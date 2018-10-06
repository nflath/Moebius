import collections
from factorization_possibilities import *

class State(object):
    """ Represents all the state needed to generate new factorization possibilities. """

    def __init__(self):
        # Current list of factorization possibilities
        self.all_factorizations = FactorizationPossibilities(self)

        # We keep track of all_factorizations generated at each n for
        # backtracking purposes.
        self.all_factorizations_for_n = {}

        # All the possibilities we have eliminated based on Z
        self.eliminate = collections.defaultdict(list)

        # Information about 'locked' values (that appear as the only
        # factorization for a specific n)
        self.locked = {}
        self.locked_n = {}

        # Current value of n to generate for
        self.n = 2

        # Number of backtracks
        self.i = 1

    def __eq__(self, other):
        return \
          self.n == other.n and \
          self.i == other.i and \
          self.all_factorizations == other.all_factorizations

    def compare_and_print(self, other):
        print("DIFFERENCES")
        if self.n != other.n: print("n: %d vs %d", self.n, other.n)
        if self.n != other.n: print("i n: %d vs %d", self.i, other.i)
        self.all_factorizations.compare_and_print(other.all_factorizations)

    def __str__(self):
        return "{ n: %d i: %d }" % (self.n, self.i)
