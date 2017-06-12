import math
import pdb

def factorize(n):
    """ Returns the factorization of n"""
    # FixMe: This is unnecessary in some cases - if we already have a duplicate
    # factor we can early return.
    # FixMe: memoize

    assert n > 1
    factors = []
    for i in range(2, n+1):
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

def one_unique_prime_factorization(n, length, primes, factorizations, potential, p, smallest, c, a):
    possibility = sorted(potential + [p])

    n = []
    if p == smallest:
        return n, smallest
    if possibility in n or len(set(possibility))!=len(possibility):
        # Alread found this or it has a repeated prime
        return n, smallest
    found, idx = index_recursive(c, possibility)
    if not found:
        exit = False
        for f in factorizations:
            x = sorted([p] + list(f[0]))
            if f[0] == potential:
                break
            elif x not in a:
                exit = True
                break
        if not exit:
            n += [possibility]
            smallest = p
        return n, smallest
    if found and len(c[idx]) > 1:
        # Check if there is a possibility that this is not taken:
        allfound = True
        for f in c[idx]:
            if f == possibility:
                continue
            found_, _ = index_recursive(c[idx+1:],f)
            if not found_:
                allfound = False
                break
        if not allfound:
            n += [possibility]
            smallest = p
    return n, smallest

def new_unique_prime_factorizations(n, length, primes, factorizations):
    if length == 1:
        primes += [n]
        return [[n,]]

    r = [[x for x in x if len(x) == length - 1] for x in factorizations]
    c = [[x for x in x if len(x) == length] for x in factorizations]
    r = [x for x in r if x]
    result = []
    a = [item for sublist in factorizations for item in sublist]

    smallest = None

    added = False

    for potential in r:
        added = False
        for x in potential:
            for p in primes:
                n_, smallest = one_unique_prime_factorization(n, length, primes, factorizations, potential[0], p, smallest, c, a)
                for x in n_:
                    if x not in result:
                        #if n == 26: pdb.set_trace()
                        result += [x]
                    added = True
                if added:
                    break
    return result

# FixMe: 16 produces 16 [[2, 2, 2, 2], [2, 3, 3], [2, 2, 5]] but should not generate [2, 2, 5]
# FixMe: 30 produces 30 [[30]] but should also generate [2,3,5]
# FixMe: 26 produces som bogus stuff
def new_unique_prime_factorization(n, start_length, primes, factorizations):

    length = start_length
    possibilities = new_unique_prime_factorizations(n, length, primes, factorizations)
    result = []
    while possibilities:
        result += possibilities
        length += 2
        possibilities = new_unique_prime_factorizations(n, length, primes, factorizations)
    return result

def index_recursive(lst, elt):
    # Find elt in list of lists lst
    for l in lst:
        for e in l:
            if e == elt:
                return True, lst.index(l)
    return False, 0

def one_repeated_prime_factor(n, primes, factorizations, p, f, smallest_factorization_idx, r):

    # if n == 12: pdb.set_trace()
    found = False
    possibility = sorted(f + [p])
    if len(possibility) == len(set(possibility)):
        return [], smallest_factorization_idx, False
    _, idx__ = index_recursive(factorizations, f)
    foundin, idx = index_recursive(factorizations, possibility)
    if not foundin:

        if len(set(possibility)) != len(possibility) and possibility not in r:
            return possibility, idx__, True
        elif possibility in r:
            return [], idx__, True

    if foundin and len(factorizations[idx]) > 1:
        #if n==12: pdb.set_trace()
        f_ = factorizations[idx]
        l = len(f_)
        c = 1
        my_idx = idx+1
        failed = False
        while not failed and c != l:
            try:
                my_idx += 1 + factorizations[my_idx:].index(f_)
                c += 1
            except:
                failed = True
        if c != l:
            return possibility, idx__, True
        else:
            return [], smallest_factorization_idx, False


    return [], smallest_factorization_idx, False


def new_repeated_prime_factorizations(n, primes, factorizations):
    r = []
    smallest_factorization_idx = None

    import pdb


    for p in primes:
        for f in factorizations:

            if len(f) == 1:
                if smallest_factorization_idx is not None and f == factorizations[smallest_factorization_idx]:
                    break
                f = f[0] # There was only one possibility for this space.

                r_, smallest_factorization_idx, break_ = one_repeated_prime_factor(n, primes, factorizations, p, f, smallest_factorization_idx, r)
                if r_ and r_ not in r:
                    #if n == 9: pdb.set_trace()
                    if n == 27 and len(r_) == len(set(r_)):
                            pdb.set_trace()
                    r += [r_]
                if break_:
                    break
            else:
                added = False

                if smallest_factorization_idx is not None and x in factorizations[smallest_factorization_idx]:
                    break

                for x in f:
                    r_, smallest_factorization_idx, break_ = one_repeated_prime_factor(n, primes, factorizations, p, x, smallest_factorization_idx, r)
                    if r_ and r_ not in r:
                        if n == 27 and len(r_) == len(set(r_)):
                            pdb.set_trace()
                        r += [r_]
                    if break_:
                        added = True
                        continue
                if added:
                    break

    return r



def main(max_n):

    primes = []
    factorizations = []

    for n in range(2, max_n+1):
        m = moebius(n)
        if m == -1:
            factorizations += [new_unique_prime_factorization(n,1,primes,factorizations)]
        elif m == 0:
            factorizations += [new_repeated_prime_factorizations(n,primes,factorizations)]
        elif m == 1:
            factorizations += [new_unique_prime_factorization(n,2,primes,factorizations)]
        else:
            assert False
    print(1, "[[1]]")
    for n in range(0, len(factorizations)):
        print(n+2, factorizations[n])

import sys
main(int(sys.argv[1]))
