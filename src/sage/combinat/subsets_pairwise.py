r"""
Subsets whose elements satisfy a predicate pairwise
"""
#*****************************************************************************
#  Copyright (C) 2011 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.sets.set import Set, Set_object_enumerated
from sage.combinat.backtrack import SearchForest
from sage.combinat.subset import Subsets

class PairwiseCompatibleSubsets(SearchForest):
    """
    The set of all subsets of ``ambient`` whose elements satisfy
    ``predicate`` pairwise

    INPUT:

    - ``ambient`` -- a set (or iterable)
    - ``predicate`` -- a binary predicate

    Assumptions: ``predicate`` is symmetric (``predicate(x,y) ==
    predicate(y,x)``) and reflexive (``predicate(x,x) == True``).

    .. note:: in fact, ``predicate(x,x)`` is never called.

    .. warning:: The current name is suboptimal and is subject to
       change. Suggestions for a good name, and a good user entry
       point are welcome. Maybe ``Subsets(..., independant = predicate)``.

    EXAMPLES:

    We construct the set of all subsets of `\{4,5,6,8,9\}` whose
    elements are pairwise relatively prime::

        sage: from sage.combinat.subsets_pairwise import PairwiseCompatibleSubsets
        sage: def predicate(x,y): return gcd(x,y) == 1
        sage: P = PairwiseCompatibleSubsets( [4,5,6,8,9], predicate); P
        An enumerated set with a forest structure
        sage: P.list()
        [{}, {4}, {4, 5}, {9, 4, 5}, {9, 4}, {5}, {5, 6}, {8, 5}, {8, 9, 5}, {9, 5}, {6}, {8}, {8, 9}, {9}]
        sage: P.cardinality()
        14
        sage: P.category()
        Category of finite enumerated sets

    Here we consider only those subsets which are maximal for
    inclusion (not yet implemented)::

        sage: P = PairwiseCompatibleSubsets( [4,5,6,8,9], predicate, maximal = True); P
        An enumerated set with a forest structure
        sage: P.list()                   # todo: not implemented
        [{9, 4, 5}, {5, 6}, {8, 9, 5}]
        sage: P.cardinality()            # todo: not implemented
        14
        sage: P.category()
        Category of finite enumerated sets

    .. rubric:: Algorithm

    In the following, we order the elements of the ambient set by
    order of apparition. The elements of ``self`` are generated by
    organizing them in a search tree. Each node of this tree is of the
    form ``(subset, rest)``, where:

     - ``subset`` represents an element of ``self``, represented
       by an increasing tuple
     - ``rest`` is the set of all `y`'s such that `y` appears
       after `x` in the ambient set and ``predicate(x,y)``
       holds, represented by a decreasing tuple

    The root of this tree is ``( (), ambient )``. All the other elements
    are generated by recursive depth first search, which gives
    lexicographic order.
    """

    #@staticmethod
    #def __classcall__(cls, ambient, predicate):
    #    ambient = Set(ambient)
    #    return super(PairwiseCompatibleSubsets, cls).__classcall__(cls, ambient, predicate)

    __len__ = None

    def __init__(self, ambient, predicate, maximal = False, element_class = Set_object_enumerated):
        """
        TESTS::

            sage: from sage.combinat.subsets_pairwise import PairwiseCompatibleSubsets
            sage: def predicate(x,y): return gcd(x,y) == 1
            sage: P = PairwiseCompatibleSubsets( [4,5,6,8,9], predicate); P
            An enumerated set with a forest structure
            sage: import __main__; __main__.predicate = predicate
            sage: TestSuite(P).run()

        """
        self._ambient = set(ambient)
        self._roots = ( ((), tuple(reversed(ambient))), )
        self._predicate = predicate
        self._maximal = maximal
        # TODO: use self.element_class for consistency
        # At this point (2011/03) TestSuite fails if we do so
        self._element_class = element_class
        SearchForest.__init__(self, algorithm = 'depth', category = FiniteEnumeratedSets())

    def __eq__(self, other):
        """
        Equality test; not really useful, but this pleases pickling ...

        TESTS::

            sage: from sage.combinat.subsets_pairwise import PairwiseCompatibleSubsets
            sage: def predicate(x,y): return gcd(x,y) == 1
            sage: P = PairwiseCompatibleSubsets( [4,5,6,8,9], predicate); P
            An enumerated set with a forest structure
            sage: P == P
            True
        """
        return self.__class__ is other.__class__ and self._ambient == other._ambient and self._predicate == other._predicate

    def __contains__(self, subset):
        """
        Membership testing

        Returns whether subset is a subset of ``self._ambient``, and
        ``predicate(x,y)`` holds for every ``x,y`` in ``self``.

        EXAMPLES::

            sage: from sage.combinat.subsets_pairwise import PairwiseCompatibleSubsets
            sage: def predicate(x,y): return gcd(x,y) == 1
            sage: P = PairwiseCompatibleSubsets( [4,5,6,8,9], predicate); P
            An enumerated set with a forest structure
            sage: Set([5,8,9]) in P
            True
            sage: Set([5,8,11]) in P
            False
            sage: Set([4,6]) in P
            False
        """
        return isinstance(subset, self._element_class ) and \
            set(subset).issubset(self._ambient) and \
            all( self._predicate(x,y) for x,y in Subsets(subset,2) )

    def post_process(self, xxx_todo_changeme ):
        """
        TESTS::

            sage: from sage.combinat.subsets_pairwise import PairwiseCompatibleSubsets
            sage: def predicate(x,y): return gcd(x,y) == 1
            sage: P = PairwiseCompatibleSubsets( [4,5,6,8,9], predicate); P
            An enumerated set with a forest structure
            sage: P.post_process( ((4,5), (9)) )
            {4, 5}
            sage: P.post_process( ((4,5), ()) )
            {4, 5}
        """
        (subset, rest) = xxx_todo_changeme
        return self._element_class(subset)

    def children(self, xxx_todo_changeme1 ):
        """
        Returns the children of a node in the tree.

        TESTS::

            sage: from sage.combinat.subsets_pairwise import PairwiseCompatibleSubsets
            sage: def predicate(x,y): return gcd(x,y) == 1
            sage: P = PairwiseCompatibleSubsets( [3,5,7,11,14], predicate); P
            An enumerated set with a forest structure
            sage: list(P.children( ((3,5), [14,11,7]) ))
            [((3, 5, 7), (11,)), ((3, 5, 11), (14,)), ((3, 5, 14), ())]

        """
        (subset, rest) = xxx_todo_changeme1
        predicate = self._predicate
        result = []
        rest = list(rest)
        while rest:
            x = rest.pop()
            result.append((subset+(x,), tuple( y for y in rest if predicate(x,y) )))
        return result
