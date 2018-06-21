from util import *
import math

@memoized
def Z(n):
    """ Returns the real Z(n)"""
    return len([moebius(x) for x in range(1,n+1) if moebius(x) == 0])

@memoized
def Z1(n):
    """ Returns the real Z(n)"""
    return len([moebius(x) for x in range(2,n+1) if moebius(x) == 1])

def ZIsPossibleBase(z,m,ZFn):
    """Return the last possible value of n z and m can occur at."""
    n = 2
    z_ = 0
    n_max = -1
    while z_ <= z:
        m_ = moebius(n)
        z_ = ZFn(n)
        if z_ == z and m_ == m:
            n_max = n
        n += 1
    return n_max

@memoized
def ZIsPossible(z, m):
    """Return the last possible value of n z and m can occur at."""
    return ZIsPossibleBase(z,m,Z)

@memoized
def Z1IsPossible(z, m):
    """Return the last possible value of n z and m can occur at."""
    return ZIsPossibleBase(z,m,Z1)


@memoized
def moebius(n):
    """Returns the moebius value of n

    This function is described as:
        moebius(n) == (-1)^m if the factorization of n is a product of m distinct primes
        moebius(n) == 0 otherswise.
    """
    def moebius_factorization(f):
        if len(set(f)) != len(f):
            return 0
        return int(math.pow(-1, len(f)))

    assert n > 0
    if n == 1:
        return 1

    return moebius_factorization(factorize(n))
