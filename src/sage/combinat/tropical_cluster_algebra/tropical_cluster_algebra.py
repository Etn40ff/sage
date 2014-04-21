r"""
Tropicalized version of cluster algebras

AUTHORS:

- Salvatore Stella
"""
#*****************************************************************************
#       Copyright (C) 2013 Salvatore Stella <sstella@ncsu.edu>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from sage.combinat.root_system.cartan_type import CartanType_abstract, CartanType
from copy import copy
from sage.matrix.matrix import Matrix
from sage.combinat.cluster_algebra_quiver.quiver_mutation_type import QuiverMutationType_Irreducible, QuiverMutationType_Reducible
from sage.structure.sage_object import SageObject
from sage.sets.all import Set
from sage.combinat.root_system.cartan_matrix import CartanMatrix
from sage.all import matrix
from sage.combinat.cluster_algebra_quiver.quiver import ClusterQuiver
from sage.combinat.permutation import Permutations
from sage.misc.cachefunc import cached_method
from sage.rings.infinity import infinity
from sage.rings.rational_field import QQ
from sage.modules.free_module_element import vector
from sage.combinat.subset import Subsets
from sage.misc.flatten import flatten
from sage.calculus.var import var
from sage.symbolic.relation import solve

class TropicalClusterAlgebra(SageObject):
    r"""
    A combinatorial model for cluster algebras

    The init function should be changed in order to be more consistent with
    ClusterSeed and QuiverMutationType
    """
    def __init__(self, data, coxeter=None, mutation_type=None, depth=infinity):
        self._mutation_type=mutation_type
        if isinstance(data, Matrix):
            if not data.is_skew_symmetrizable():
                raise ValueError("The input must be a skew symmetrizable integer matrix")
            self._B=copy(data)
            self._cartan_type=None
            self._coxeter=None
            self._n=self._B.ncols()
        elif isinstance(data, CartanType_abstract):
            self._n=data.rank()
            # force labeling to be range(self._n)
            # I should fix this to allow any labeling but I still need to figure
            # out how to deal with matrices (it will require major refactoring)
            relabeling=dict(zip(data.index_set(),range(self._n)))
            self._cartan_type=data.relabel(relabeling)
            if coxeter==None:
                coxeter=list(data.index_set())
            if Set(coxeter)!=Set(data.index_set()):
                raise ValueError("The Coxeter element need to be a list"
                                 "permiting the entry of the index set of the Cartan type")
            coxeter=[ relabeling[i] for i in coxeter ]
            self._B=2-data.cartan_matrix()
            for i in range(self._n):
                for j in range(i,self._n):
                    self._B[coxeter[j],coxeter[i]]=-self._B[coxeter[j],coxeter[i]]
            self._coxeter=copy(coxeter)
        elif type(data) in [QuiverMutationType_Irreducible, QuiverMutationType_Reducible]:
            self.__init__(data.b_matrix(),mutation_type=data, depth=depth)
        elif type(data)==list:
            self.__init__(CartanType(data), coxeter=coxeter, depth=depth)
        else:
            raise ValueError("Input is not valid")
        self._A=CartanMatrix(2-matrix(self._n,map(abs,self._B.list())))
        self._quiver=None
        self._root_space=None
        self._d_vectors=[None,None]
        self._clusters=[None,None]
        self._delta=None
        self._gamma=None
        self._affine_tubes=None
        self._depth=depth

    def _repr_(self):
            r"""
            Returns the description of ``self``.
            """
            description = 'A combinatorial model for a cluster algebra of rank %d' %(self._n)
            if self._mutation_type:
                description += ' and type %s' %(self._mutation_type)
            return description

    def b_matrix(self):
        r"""
        Returns the `B` *-matrix* of ``self``.
        """
        return self._B

    def cartan_companion(self):
        r"""
        Returns the `Cartan Companion` of ``self``.
        """
        return self._A

    def quiver(self):
        r"""
        Taken from the cluster algebra package
        """
        if self._quiver is None:
            self._quiver = ClusterQuiver( self._B )
            # hack: ClusterQuiver can't determine type affine type D so if we
            # already know the mutation type we do not forget it.
            # This might create issues with forged imputs
            if self._mutation_type:
                self._quiver._mutation_type = self._mutation_type
        return self._quiver

    def show(self):
        self.quiver().show()

    def mutation_type(self):
        r"""
        Taken from the cluster algebra package
        ######
        ## WARNING: issues with
        sage: ct=CartanType(['D', 7, 1])
        sage: T=TropicalClusterAlgebra(ct,[1,7,6,5,4,3,2,0])
        Apparently D is not a recognized quiver mutation type
        #####
        """
        if self._mutation_type is None:
            if self._quiver is None:
                self.quiver()
            self._mutation_type = self._quiver.mutation_type()
        return self._mutation_type

    def is_finite(self):
        r"""
        Taken from the cluster algebra package
        """
        mt = self.mutation_type()
        if type(mt) is str:
            return False
        else:
            return mt.is_finite()

    def is_affine(self):
        r"""
        Inspiration taken from cluster algebra package
        """
        mt = self.mutation_type()
        if type(mt) is str:
            return False
        else:
            return mt.is_affine()

    def is_acyclic(self):
        r"""
        Returns True iff self is acyclic (i.e., if the underlying quiver is acyclic).
        Taken from ClusterSeed
        """
        return self.quiver()._digraph.is_directed_acyclic()

    def cartan_type(self):
        r"""
        Returns the Cartan type of the Cartan companion of self.b_matrix()

        Only crystallographic types are implemented

        Warning: this function is redundant but the corresonding method in
        CartanType does not recognize all the types
        """
        if self._cartan_type:
            return self._cartan_type
        A=self.cartan_companion()
        n=self._n
        degrees_dict=dict(zip(range(n),map(sum,2-A)))
        degrees_set=Set(degrees_dict.values())

        types_to_check=[ ["A",n] ]
        if n > 1:
            types_to_check.append(["B",n])
        if n > 2:
            types_to_check.append(["C",n])
        if n > 3:
            types_to_check.append(["D",n])
        if n >=6 and n <= 8:
            types_to_check.append(["E",n])
        if n == 4:
            types_to_check.append(["F",n])
        if n == 2:
            types_to_check.append(["G",n])
        if n >1:
            types_to_check.append(["A", n-1,1])
            types_to_check.append(["B", n-1,1])
            types_to_check.append(["BC",n-1,2])
            types_to_check.append(["A", 2*n-2,2])
            types_to_check.append(["A", 2*n-3,2])
        if n>2:
            types_to_check.append(["C", n-1,1])
            types_to_check.append(["D", n,2])
        if n>3:
            types_to_check.append(["D", n-1,1])
        if n >=7 and n <= 9:
            types_to_check.append(["E",n-1,1])
        if n == 5:
            types_to_check.append(["F",4,1])
        if n == 3:
            types_to_check.append(["G",n-1,1])
            types_to_check.append(["D",4,3])
        if n == 5:
            types_to_check.append(["E",6,2])

        for ct_name in types_to_check:
            ct=CartanType(ct_name)
            if 0 not in ct.index_set():
                ct=ct.relabel(dict(zip(range(1,n+1),range(n))))
            ct_matrix=ct.cartan_matrix()
            ct_degrees_dict=dict(zip(range(n),map(sum,2-ct_matrix)))
            if Set(ct_degrees_dict.values()) != degrees_set:
                continue
            for p in Permutations(range(n)):
                relabeling=dict(zip(range(n),p))
                ct_new=ct.relabel(relabeling)
                if ct_new.cartan_matrix()==A:
                    self._cartan_type=ct_new
                    return copy(ct_new)
        raise ValueError("Type not recognized")

    def dynkin_diagram(self):
        return self.cartan_type().dynkin_diagram()

    def root_space(self):
        if self._root_space == None:
            self._root_space = self.cartan_type().root_system().root_space(QQ)
        return copy(self._root_space)

    def initial_cluster(self):
        return [ -v for v in self.root_space().simple_roots() ]

    def coxeter(self):
        r"""
        Returns a list expressing the coxeter element corresponding to self._B
        (twisted) reflections are applied from top of the list, for example
        [2, 1, 0] correspond to s_2s_1s_0

        Sources == non positive columns == leftmost letters
        """
        if not self._coxeter:
            zero_vector=vector([0 for x in range(self._n)])
            self._coxeter=[]
            B=copy(self._B)
            columns=B.columns()
            source=None
            for j in range(self._n):
                for i in range(self._n):
                    if all(x <=0 for x in columns[i]) and columns[i] != zero_vector:
                        source=i
                        break
                if source == None:
                    if B != matrix(self._n):
                        raise ValueError("Unable to find a Coxeter element representing self._B")
                    self._coxeter+=[ x for x in range(self._n) if x not in self._coxeter]
                    break
                self._coxeter.append(source)
                columns[source]=zero_vector
                B=matrix(columns).transpose()
                B[source]=zero_vector
                columns=B.columns()
                source=None
        return copy(self._coxeter)

    def set_depth(self,depth):
        self._depth = depth

    @cached_method
    def simple_reflection(self,i):
        return self.root_space().simple_reflection(i)

    @cached_method
    def simple_reflections(self):
        return self.root_space().simple_reflections()

    @cached_method
    def c(self):
        def f(v):
            sequence=self.coxeter()
            sequence.reverse()
            for i in sequence:
                v=self.simple_reflection(i)(v)
            return v
        return f

    @cached_method
    def c_inverse(self):
        def f(v):
            sequence=self.coxeter()
            for i in sequence:
                v=self.simple_reflection(i)(v)
            return v
        return f

    @cached_method
    def twisted_reflection(self,i):
        def sigma_i(alpha):
            index_set = self.root_space().index_set()
            not_i = [ x for x in index_set if x != i]
            fixed=sum([alpha.coefficient(j)*self.root_space().simple_root(j)
                for j in not_i if alpha.coefficient(j) < 0])
            alpha=alpha-fixed
            return self.simple_reflection(i)(alpha)+fixed
        return sigma_i

    @cached_method
    def twisted_reflections(self):
        return [ self.twisted_reflection(i) for i in range(self._n) ]

    @cached_method
    def tau_c(self):
        def f(v):
            sequence=self.coxeter()
            sequence.reverse()
            for i in sequence:
                v=self.twisted_reflection(i)(v)
            return v
        return f

    @cached_method
    def tau_c_inverse(self):
        def f(v):
            sequence=self.coxeter()
            for i in sequence:
                v=self.twisted_reflection(i)(v)
            return v
        return f

    def delta(self):
        """r
        Assume roots are labeled by range(self._n)
        """
        if self._delta:
            return self._delta
        if self.is_affine():
            annihilator_basis = self.cartan_companion().transpose().integer_kernel().gens()
            self._delta = sum(
                    annihilator_basis[0][i]*self.root_space().simple_root(i)
                    for i in range(self._n) )
            return  self._delta
        else:
            raise ValueError("delta is defined only for affine types")

    def gamma(self):
        """r
        Assume roots are labeled by range(self._n)
        Return the generalized eigenvector of the cartan matrix of eigenvalue 1
        in the span of the finite root system
        """
        if self._gamma:
            return self._gamma
        if self.is_affine():
            C = map( lambda x: vector(self.c()(x)), self.root_space().simple_roots() )
            C = matrix(C).transpose()
            delta = vector(self.delta())
            gamma = (C-1).solve_right(delta)
            ct = self.cartan_type()
            i0 = [ i for i in ct.index_set() if i not in ct.classical().index_set() ][0]
            gamma = gamma-gamma[i0]/delta[i0]*delta
            self._gamma = sum( [ gamma[i]*self.root_space().simple_root(i) for
                i in range(self._n) ] )
            return self._gamma
        else:
            raise ValueError("gamma is defined only for affine types")

    def d_vectors(self,depth=None):
        if depth == None:
            depth = self._depth
        if self._d_vectors[0] == depth:
            return copy(self._d_vectors[1])

        if self.is_finite():
            if self.is_acyclic():
                self._d_vectors[0] = infinity
                self._d_vectors[1] = self.root_space().almost_positive_roots()
            else:
                raise ValueError("Not implemented yet")
        elif self.is_affine():
            if self.is_acyclic():
                if depth is infinity:
                    raise ValueError("d_vectors, for affine types, can only be "
                                     "computed up to a given depth")
                self._d_vectors[0] = depth
                self._d_vectors[1] = list( S for S in self._affine_acyclic_type_d_vectors_iter(depth=depth))
            else:
                raise ValueError("There is no theory for cyclic affine types yet")
        else:
            raise ValueError("Not implemented yet")

        return copy(self._d_vectors[1])

    def _affine_acyclic_type_d_vectors_iter(self,depth=None):
        if depth == None:
            depth = self._depth
        depth_counter=0
        d_vectors={}
        delta=self.delta()
        for v in self.root_space().simple_roots():
            d_vectors[-v]=["forward","backward"]
        for v in self._affine_acyclic_type_classical_roots_in_finite_orbits():
            d_vectors[v]=[None]
            d_vectors[delta-v]=[None]
        gets_bigger=True
        while gets_bigger and depth_counter <= depth:
            gets_bigger=False
            constructed_vectors = d_vectors.keys()
            for v in constructed_vectors:
                directions=d_vectors[v]
                while directions:
                    next_move=directions.pop()
                    if next_move == "forward":
                        next_vector =  self.tau_c()(v)
                        if next_vector not in d_vectors.keys():
                            d_vectors[next_vector]=["forward"]
                            gets_bigger=True
                    if next_move == "backward":
                        next_vector = self.tau_c_inverse()(v)
                        if next_vector not in d_vectors.keys():
                            d_vectors[next_vector]=["backward"]
                            gets_bigger=True
                    if directions:
                        continue
                    yield v
            depth_counter+=1

    def _affine_acyclic_type_classical_roots_in_finite_orbits(self):
        rs = self.root_space()
        crs = rs.classical()
        injection = crs.module_morphism(on_basis=lambda i: rs.simple_root(i),codomain=rs)
        classical_roots = [ injection(x) for x in crs.positive_roots() ]
        gammacheck = self.gamma().associated_coroot()
        return [ x for x in classical_roots if gammacheck.scalar(x) == 0 ]

    def ith_orbit(self, i, depth=None):
        if depth == None:
            depth = self._depth
        if depth is infinity and not self.is_finite():
            raise ValueError("d_vectors, for infinite types, can only be computed up to a given depth")
        depth_counter=0
        orbit={}
        orbit[0]=self.initial_cluster()[i]
        gets_bigger=True
        while gets_bigger and depth_counter < depth:
            gets_bigger=False
            forward=self.tau_c()(orbit[depth_counter])
            backward=self.tau_c_inverse()(orbit[-depth_counter])
            if forward != orbit[-depth_counter]:
                depth_counter+=1
                orbit[depth_counter]=forward
                if backward != forward:
                    orbit[-depth_counter]=backward
                    gets_bigger=True
        return orbit

    def affine_tubes(self):
        if self._affine_tubes:
            return copy(self._affine_tubes)
        if not self.is_affine():
            raise ValueError("Tubes exist only when the type of self is affine")
        finite_roots = self._affine_acyclic_type_classical_roots_in_finite_orbits()
        sums = [ x+y for (x,y) in Subsets(finite_roots,2) ]
        simple_roots=[ x for x in finite_roots if x not in sums]
        tau=self.tau_c()
        tau_inv=self.tau_c_inverse()
        initial_roots=[ x for x in simple_roots if tau_inv(x) not in simple_roots ]
        tubes=[]
        for a in initial_roots:
            layer=[a]
            h=0
            x=tau(a)
            while x != a:
                h+=1
                layer.append(x)
                x=tau(x)
            tube=[layer]
            for i in range(1,h):
                a=tube[i-1][0]+tube[0][i]
                layer=[a]
                x=tau(a)
                while x != a:
                    layer.append(x)
                    x=tau(x)
                tube.append(layer)
            tubes.append(tube)
        self._affine_tubes=tubes
        return copy(self._affine_tubes)

    @cached_method
    def compatibility_degree(self, alpha, beta):
        if alpha in self.initial_cluster():
            return max(beta[alpha.support()[0]],0)

        alphacheck = alpha.associated_coroot()

        if beta in self.initial_cluster():
            return max(alphacheck[beta.support()[0]],0)

        Ap = -matrix(self._n, map(lambda x: max(x,0), self.b_matrix().list() ) )
        Am =  matrix(self._n, map(lambda x: min(x,0), self.b_matrix().list() ) )

        a = vector(alphacheck)
        b = vector(beta)

        return max( -a*b-a*Am*b, -a*b-a*Ap*b, 0 )

    @cached_method
    def compatible(self,alpha,beta):
        if self.compatibility_degree(alpha,beta) == 0:
            return True
        return False

    @cached_method
    def exchangeable(self,alpha,beta):
        ####
        # We make the same assumptions as in cluster_expansion()
        ####
        gamma=self.gamma()
        gammacheck=gamma.associated_coroot()
        if gammacheck.scalar(alpha) == 0 and gammacheck.scalar(beta) == 0:
            rays = flatten([ t[0] for t in self.affine_tubes() ])
            system = matrix( map( vector, rays ) ).transpose()
            x = vector( var ( ['x%d'%i for i in range(len(rays))] ) )
            eqs =  [ (system*x)[i] == vector(alpha+beta)[i] for i in
                range(self._n)]
            ieqs = [ y >= 0 for y in x ]
            solutions = solve( eqs+ieqs, x, solution_dict=True )
                
            if solutions: 
                if len(solutions) > 1 or all( v > 0 for v in solutions[0].values() ):
                    return False
        if self.compatibility_degree(alpha,beta) == 1 and self.compatibility_degree(beta,alpha) == 1: 
            return True
        return False

    def clusters(self, depth=None):
        if depth == None:
            depth = self._depth
        if self._clusters[0] != depth:

            def compatible_following(l):
                out=[]
                while l:
                    x=l.pop()
                    comp_with_x=[y for y in l if self.compatibility_degree(x,y)==0]
                    if comp_with_x != []:
                        out.append((x,comp_with_x))
                    else:
                        out.append((x,))
                return out

            d_vectors = self.d_vectors(depth=depth)
            clusters = compatible_following(d_vectors)
            done = False
            while not done:
                new = []
                done = True
                for clus in clusters:
                    if type(clus[-1]) == list:
                        done = False
                        for y in compatible_following(clus[-1]):
                            new.append(clus[:-1]+y)
                    else:
                        new.append(clus)
                clusters = copy(new)
            self._clusters = [depth,[ x for x in  clusters if len(x) == self._n]]

        return copy(self._clusters[1])

    @cached_method
    def cluster_expansion(self, beta):
        if beta == 0:
            return dict()
        
        coefficients=beta.monomial_coefficients()
        if any ( x < 0 for x in coefficients.values() ):
            alpha = [ -x for x in self.initial_cluster() ]
            negative_part = dict( [(-alpha[x],-coefficients[x]) for x in
                    coefficients if coefficients[x] < 0 ] ) 
            positive_part = sum( [ coefficients[x]*alpha[x] for x in
                    coefficients if coefficients[x] > 0 ] ) 
            return dict( negative_part.items() +
                    self.cluster_expansion(positive_part).items() )
        
        if self.is_affine():
            if self.gamma().associated_coroot().scalar(beta) < 0:
                shifted_expansion = self.cluster_expansion( self.tau_c()(beta) )
                return dict( [ (self.tau_c_inverse()(x),shifted_expansion[x]) for x in
                    shifted_expansion ] )
            elif self.gamma().associated_coroot().scalar(beta) > 0:
                shifted_expansion = self.cluster_expansion( self.tau_c_inverse()(beta) )
                return dict( [ (self.tau_c()(x),shifted_expansion[x]) for x in
                    shifted_expansion ] )
            else:
                ###
                # Assumptions
                #
                # Two cases are possible for vectors in the interior of the cone
                # according to how many tubes there are:
                # 1) If there is only one tube then its extremal rays are linearly
                # independent, therefore a point is in the interior of the cone
                # if and only if it is a linear combination of all the extremal
                # rays with strictly positive coefficients. In this case solve()
                # should produce only one solution.
                # 2) If there are two or three tubes then the extreme rays are
                # linearly dependent. A vector is in the interior of the cone if
                # and only if it can be written as a strictly positive linear
                # combination of all the rays of at least one tube. In this case
                # solve() should return at least two solutions.
                #
                # If a vector is on one face of the cone than it can be written
                # uniquely as linear combination of the rays of that face (they
                # are linearly independent). solve() should return only one
                # solution no matter how many tubes there are.

                rays = flatten([ t[0] for t in self.affine_tubes() ])
                system = matrix( map( vector, rays ) ).transpose()
                x = vector( var ( ['x%d'%i for i in range(len(rays))] ) )
                eqs =  [ (system*x)[i] == vector(beta)[i] for i in
                        range(self._n)]
                ieqs = [ y >= 0 for y in x ]
                solutions = solve( eqs+ieqs, x, solution_dict=True )
                
                if not solutions: 
                    # we are outside the cone
                    shifted_expansion = self.cluster_expansion( self.tau_c()(beta) )
                    return dict( [ (self.tau_c_inverse()(v),shifted_expansion[v]) for v in
                        shifted_expansion ] )
                
                if len(solutions) > 1 or all( v > 0 for v in solutions[0].values() ):
                    # we are in the interior of the cone
                    raise ValueError("Vectors in the interior of the cone do "
                        "not have a cluster expansion")
               
                # we are on the boundary of the cone
                solution_dict=dict( [(rays[i],solutions[0][x[i]]) for i in range(len(rays)) ] )
                tube_bases = [ t[0] for t in self.affine_tubes() ]
                connected_components = []
                index = 0
                for t in tube_bases:
                    component = []
                    for a in t:
                        if solution_dict[a] == 0:
                            if component:
                                connected_components.append( component )
                                component = []
                        else: 
                            component.append( (a,solution_dict[a]) )
                    if component:
                        if connected_components:
                            connected_components[index] = ( component + 
                                    connected_components[index] )
                        else:
                            connected_components.append( component ) 
                    index = len(connected_components)
                expansion = dict()
                while connected_components:
                    component = connected_components.pop()
                    c = min( [ a[1] for a in component] )
                    expansion[sum( [a[0] for a in component])] = c
                    component = [ (a[0],a[1]-c) for a in component ]
                    new_component = []
                    for a in component:
                        if a[1] == 0:
                            if new_component:
                                connected_components.append( new_component )
                                new_component = []
                        else:
                            new_component.append( a )
                    if new_component:
                        connected_components.append( new_component )
                return expansion

        if self.is_finite():
            shifted_expansion = self.cluster_expansion( self.tau_c()(beta) )
            return dict( [ (self.tau_c_inverse()(x),shifted_expansion[x]) for x
                in shifted_expansion ] )

    def plot_cluster_fan_stereographically(self,depth=None,northsign=1,north=None,right=None):
        from sage.plot.graphics import Graphics
        from sage.plot.point import point
        from sage.misc.flatten import flatten

        if self._n !=3:
            raise ValueError("Can only stereographically project fans in 3d.")
        if depth == None:
            depth = self._depth
        if not self.is_finite() and depth==infinity:
            raise ValueError("For infinite algebras you must specify the depth.")

        if north == None:
            if self.is_affine():
                north = vector(self.delta())
            else:
                north = vector( (-1,-1,-1) )
        if right == None:
            if self.is_affine():
                right = vector(self.gamma())
            else:
                right = vector( (1,0,0) )
        colors = dict([(0,'red'),(1,'green'),(2,'blue'),(3,'cyan')])
        G = Graphics()

        roots = self.d_vectors(depth=depth)
        compatible = []
        while roots:
            x = roots.pop()
            for y in roots:
                if self.compatibility_degree(x,y) == 0:
                    compatible.append((x,y))
        for (u,v) in compatible:
            G += _stereo_arc(vector(u),vector(v),vector(u+v),north=northsign*north,right=right,thickness=0.5,color='black')

        for i in range(3):
            orbit = self.ith_orbit(i,depth=depth)
            for j in orbit:
                G += point(_stereo_coordinates(vector(orbit[j]),north=northsign*north,right=right),color=colors[i],zorder=len(G))

        if self.is_affine():
            for v in flatten(self.affine_tubes()):
                G += point(_stereo_coordinates(vector(v),north=northsign*north,right=right),color=colors[3],zorder=len(G))

        G.set_aspect_ratio(1)
        G._show_axes = False
        return G


#####
# Helper functions
#####
def _stereo_coordinates(x, north=(1,0,0), right=(0,1,0), translation=-1):
    r"""
    Project stereographically points from a sphere
    """
    from sage.misc.functional import norm
    north=_normalize(north)
    right=vector(right)
    right=_normalize(right-(right*north)*north)
    if norm(right) == 0:
        raise ValueError ("Right must not be linearly dependent from north")
    top=north.cross_product(right)
    x=_normalize(x)
    p=(translation-north*x)/(1-north*x)*(north-x)+x
    return vector((right*p, top*p ))

def _normalize(x):
    r"""
    make x of length 1
    """
    from sage.misc.functional import norm
    x=vector(x)
    if norm(x) == 0:
        return x
    return vector(x/norm(x))

def _stereo_arc(x,y, xy=None,  north=(1,0,0), right=(0,1,0), translation=-1, **kwds):
    from sage.misc.functional import norm, det, n
    from sage.plot.line import line
    from sage.plot.plot import parametric_plot
    from sage.functions.trig import arccos, cos, sin
    from sage.symbolic.constants import NaN
    from sage.calculus.var import var
    x=vector(x)
    y=vector(y)
    sx=n(_stereo_coordinates(x, north=north, right=right, translation=translation))
    sy=n(_stereo_coordinates(y, north=north, right=right, translation=translation))
    if xy == None:
        sxy=n(_stereo_coordinates(x+y, north=north, right=right, translation=translation))
    else:
        sxy=n(_stereo_coordinates(xy, north=north, right=right, translation=translation))
    m0=-matrix(3,[sx[0]**2+sx[1]**2, sx[1], 1, sy[0]**2+sy[1]**2, sy[1], 1,
                 sxy[0]**2+sxy[1]**2, sxy[1], 1])
    m1=matrix(3,[sx[0]**2+sx[1]**2, sx[0], 1, sy[0]**2+sy[1]**2, sy[0], 1,
                 sxy[0]**2+sxy[1]**2, sxy[0], 1])
    m2=matrix(3,[sx[0], sx[1], 1, sy[0], sy[1], 1, sxy[0], sxy[1], 1])
    d=det(m2)*2
    if d == 0:
        return line([sx,sy], **kwds)
    center=vector((-det(m0)/d,-det(m1)/d))
    if det(matrix(2,list(sx-center)+list(sy-center)))==0:
        return line([sx,sy], **kwds)
    radius=norm(sx-center)
    e1=_normalize(sx-center)
    v2=_normalize(sy-center)
    vxy=_normalize(sxy-center)
    e2=_normalize(vxy-(vxy*e1)*e1)
    angle=arccos(e1*vxy)+arccos(vxy*v2)
    if angle < 0.1 or angle==NaN:
        return line([sx,sy], **kwds)
    var('t')
    p=center+radius*cos(t)*e1+radius*sin(t)*e2
    return parametric_plot( p, (t, 0, angle), **kwds)
