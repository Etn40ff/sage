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

class TropicalClusterAlgebra(SageObject):
    r"""
    A combinatorial model for cluster algebras

    The init function should be changed in order to be more consistent with
    ClusterSeed and QuiverMutationType
    """
    def __init__(self, data, coxeter=None, mutation_type=None):
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
            self.__init__(data.b_matrix(),mutation_type=data)
        elif type(data)==list:
            self.__init__(CartanType(data),coxeter=coxeter)
        else:
            raise ValueError("Input is not valid")
        self._A=CartanMatrix(2-matrix(self._n,map(abs,self._B.list())))
        self._quiver=None
        self._root_space=None
        self._d_vectors=[None,None]
        self._delta=None
        self._gamma=None
        #self._symmetrizer=None
        #self._scalar_product=None
        #self._s=[None for i in range(self._n)]
        #self._sigma=[None for i in range(self._n)]
        #self._coxeter_matrix=None
        #self._coxeter_translation=None
        #self._coxeter_translation_inverse=None
        #self._finite_orbits=None
        #self._finite_cone=None
        #self._tubes=None
        #self._tubes_dict=None
        #self._clusters=None
        #self._s_w=[None for i in range(self._n)]
        #self._sigma_w=[None for i in range(self._n)]
        #self._coxeter_translation_w=None
        #self._coxeter_translation_w_inverse=None
        #self._coxeter_matrix_w=None
        #self._g_vectors=None
        #self._clusters_w=None
        ## To be removed
        #self._compatibility_degree=dict()

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

    def d_vectors(self,depth=infinity):
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

    def _affine_acyclic_type_d_vectors_iter(self,depth=infinity):
        depth_counter=0
        d_vectors={}
        for v in self.root_space().simple_roots():
            d_vectors[-v]=["forward","backward"]
        ###
        # FixMe: there is some redundancy here 
        #        it should be fixed by selecting only one root per finite orbit
        for v in self._affine_acyclic_type_classical_roots_in_finite_orbits():
            d_vectors[v]=["forward"]
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

