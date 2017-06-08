import math
from  util import Node

def factorize(n):
    """ Returns the factorization of n"""
    # FixMe: This is unnecessary in some cases - if we already have a duplicate
    # factor we can early return.
    # FixMe: memoize

    assert n > 1
    factors = []
    for i in xrange(2, n+1):
        while (n%i)==0:
            factors += [i]
            n = n / i
    assert n == 1
    return factors

def moebius(n):
    """Returns the moebius value of n

    This function is described as:
        moebius(n) == (-1)^m if the factorization of n is a product of m distinct primes
        moebius(n) == 0 otherswise.
    """
    # FixMe: memoize

    assert n > 0
    if n == 1:
        return 1
    f = factorize(n)
    if len(set(f)) != len(f):
        return 0
    return math.pow(-1,len(f))

def Z(n):
    """Returns the canonical value of Z for n.

    This function is described as:
        Z(n) == #{m <= n: moebius(m) == 0}
    """
    # FixMe: memoize

    z = 0
    for x in xrange(1,n+1):
        if moebius(x)==0:
            z += 1
    return z

def expand_tree_unique_prime_factorization(n, current, start_length):
    """ Expand the tree, assuming the current node is a prime factorization.

     Get all possible prime factorizations of the length start_length.  Then,
     start_length + 2, etc"""

    length = start_length
    possibilities = current.possible_new_unique_prime_factorizations(length)
    while possibilities:
       for x in possibilities:
           new = Node(n, x, current)
       length += 2
       possibilities = current.possible_new_unique_prime_factorizations(length)


def expand_tree(current, times):
    """ Expand the tree starting from the node 'current' n times."""

    if times == 0:
        # We're done expanding the tree; finish
        return
    n = current.n + 1
    m = moebius(n)

    if m == -1:
        # N is the product of an odd number of distinct primes.
        expand_tree_unique_prime_factorization(n, current, 1)
    elif m == 0:
        # The factorization of N contains a duplicated prime.
        f = current.smallest_new_factorizations_with_square()

        for x in f:
            new = Node(n, x, current)
    elif m == 1:
        # N is the product of an even number of distinct primes
        expand_tree_unique_prime_factorization(n, current, 2)
    if not current.children:
        # If we didn't find any children for this tree, then some parent
        # factorization was incorrect.

        current.dead = True
        current.dead_reason = "NO_CHILDREN"
    for child in current.children:
        # Expand all the children
        expand_tree(child, times-1)


    return current

def count(root, n):
    """Counts the # of vertices with n==n in the tree.

    Just used for informational purposes.
    """

    r = 0
    if root.n == n:
        return 1
    for c in root.children:
        r += count(c,n)
    return r

def main(max_n):
    root = Node(1,[1],None)
    r = expand_tree(root,max_n-1)
    #r.clean()
    r.pp()
    #print count(r,30)
    z = 0
    # for x in xrange(1,2*3):
    #      if moebius(x) == 0: z += 1
    #      print x "\t", z

import cProfile
cProfile.run("main(36)")
