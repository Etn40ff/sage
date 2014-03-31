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

class TropicalClusterAlgebra(SageObject):
    r"""
    A combinatorial model for cluster algebras

    The init function should be changed in order to be more consistent with
    ClusterSeed and QuiverMutationType
    """
    def __init__(self, data, coxeter=None):
        if isinstance(data, Matrix):
            if not data.is_skew_symmetrizable():
                raise ValueError("The input must be a skew symmetrizable integer matrix")
            self._B=copy(data)
            self._cartan_type=None
            self._coxeter=None
            self._n=self._B.ncols()
        elif isinstance(data, CartanType_abstract):
            if coxeter==None:
                coxeter=range(data.rank())
            self._cartan_type=copy(data)
            self._B=2-data.cartan_matrix()
            self._n=self._B.ncols()
            if Set(coxeter)!=Set(range(self._n)):
                raise ValueError("The Coxeter element need to be a list"
                                 "permutation the  dimension of the root space"
                                 "of the Cartan type")
            for i in range(self._n):
                for j in range(i,self._n):
                    self._B[coxeter[j],coxeter[i]]=-self._B[coxeter[j],coxeter[i]]
            self._coxeter=copy(coxeter)
        elif type(data) in [QuiverMutationType_Irreducible, QuiverMutationType_Reducible]:
            raise ValueError("Not implemented yet")
        elif type(data)==list:
            self.__init__(CartanType(data),coxeter=coxeter)
        else:
            raise ValueError("Input is not valid")
        self._A=CartanMatrix(2-matrix(self._n,map(abs,self._B.list())))
        self._description = 'A combinatorial model for cluster algebra of rank %d' %(self._n)
        self._mutation_type=None
        self._quiver=None
        self._root_lattice=None
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
            return copy(self._description)

    def b_matrix(self):
        r"""
        Returns the `B` *-matrix* of ``self``.
        """
        return copy(self._B)

    def cartan_companion(self):
        r"""
        Returns the `Cartan Companion` of ``self``.
        """
        return copy(self._A)

    def quiver(self):                                                                                                                                                     
        r"""
        Taken from the cluster algebra package
        """
        if self._quiver is None:
            self._quiver = ClusterQuiver( self._B )
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

    def cartan_type(self):
        r"""
        Returns the Cartan type of the Cartan companion of self.b_matrix()

        Only chrystallographics are implemented
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

    def root_lattice(self):
        if self._root_lattice == None:
            self._root_lattice = self.cartan_type().root_system().root_lattice()
        return copy(self._root_lattice)

    def coxeter(self):
        r"""
        Returns a list expressing the coxeter element corresponding to self._B
        (twisted) reflections are applied from top of the list, for example
        [2, 1, 0] correspond to s_2s_1s_0
        
        Sources == non positive columns == leftmost letters
        """
        if not self._coxeter:
            from sage.modules.free_module_element import vector
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
        return self.root_lattice().simple_reflection(i)

    @cached_method    
    def simple_reflections(self):
        return self.root_lattice().simple_reflections()

    @cached_method    
    def twisted_reflection(self,i):
        def sigma_i(alpha):
            not_i = [ x for x in range(self._n) if x != i]
            fixed=sum([alpha.coefficient(j)*self.root_lattice().simple_root(j) 
                for j in not_i if alpha.coefficient(j) < 0])
            alpha=alpha-fixed
            return self.simple_reflection(i)(alpha)+fixed
        return sigma_i

    @cached_method    
    def twisted_reflections(self):
        return [ self.twisted_reflection(i) for i in range(self._n) ]


