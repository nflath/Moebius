import math
import pdb

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

def new_unique_prime_factorizations(n, length, primes, factorizations):
    if length == 1:
        primes += [n]
        return [[n,]]

    r = [[x for x in x if len(x) == length - 1] for x in factorizations]
    c = [[x for x in x if len(x) == length] for x in factorizations]


    # for a in r:
    #     if len(a) > 1:
    #         assert False
    #for a in c:
     #   if len(a) > 1:
      #      assert False


    r = [x for x in r if x]
    #c = [item for sublist in c for item in sublist]
    n = []
    a = [item for sublist in factorizations for item in sublist]

    smallest = None
    for potential in r:
        if len(potential) > 1:
            assert False
        potential = potential[0]
        for p in primes:
            possibility = sorted(potential + [p])

            if p == smallest:
                break
            if possibility in n or p in potential:
                # Alread found this or it has a repeated prime
                break
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
                break
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

    return n


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
    _, idx__ = index_recursive(factorizations, f)
    foundin, idx = index_recursive(factorizations, possibility)
    if not foundin:

        if len(set(possibility)) != len(possibility) and possibility not in r:
            return possibility, idx__, True
        elif possibility in r:
            return [], idx__, True

    if foundin and len(factorizations[idx]) > 1:

        #my_idx = idx
        #for newf in factorizations[idx]:
#            foundin_, my_idx = index_recursive(factorizations[my_idx+1:], newf)


        for newf in factorizations[idx]:

            if possibility == newf:
                continue


            # If there are newf()
            foundin_, idx_ = index_recursive(factorizations[idx+1:], newf)

            if not foundin_ and possibility not in r:
                return possibility, idx__, True
            if foundin_:
                if factorizations[idx + 1 + idx_] != factorizations[idx]:
                    assert False
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
                if r_:
                    #if n == 9: pdb.set_trace()
                    r += [r_]
                if break_:
                    break
            else:
                added = False

                for x in f:
                    if smallest_factorization_idx is not None and x in factorizations[smallest_factorization_idx]:
                        break
                    #if n == 20: pdb.set_trace()
                    r_, smallest_factorization_idx, break_ = one_repeated_prime_factor(n, primes, factorizations, p, x, smallest_factorization_idx, r)
                    if r_:


                        r += [r_]
                    if break_:
                        added = True
                        continue
                if added:
                    break
                    # FixMe: Try it with both.
                    # assert False




            # if f is smallest_factorization:
            #     break

            # found = False
            # possibility = sorted(list(f) + [p])
            # foundin, idx = index_recursive(factorizations, possibility)

            # if not foundin:
            #     if len(set(possibility)) != len(possibility) and possibility not in r:
            #         r += [possibility]
            #         found = True
            #         smallest_factorization = f
            #         break
            #     elif possibility in r:
            #         found = True
            #         smallest_factorization = f
            #         break

            # if foundin and len(factorizations[idx]) > 1:
            #     # This is a possibility if *any* path allows it; we need to figure this out
            #     # For now, only do pairs
            #     for newf in factorizations[idx]:
            #         foundin_, idx_ = index_recursive(factorizations[idx+1:], newf)
            #         if possibility == newf:
            #             continue
            #         if not foundin_ and possibility not in r:
            #             r += [possibility]
            #             found = True
            #             smallest_factorization = f
            #         else:
            #             if factorizations[idx + 1 + idx_] != factorizations[idx]:
            #                 import pdb
            #                 pdb.set_trace()
            #                 assert False
            # if found:
            #     break
    return r



def main(max_n):
    primes = []
    factorizations = []
    print 1, "[[1]]"
    for n in xrange(2, max_n+1):
        m = moebius(n)

        if m == -1:
            factorizations += [new_unique_prime_factorizations(n,1,primes,factorizations)]
        elif m == 0:
            factorizations += [new_repeated_prime_factorizations(n,primes,factorizations)]
        elif m == 1:
            factorizations += [new_unique_prime_factorizations(n,2,primes,factorizations)]
        else:
            assert False
    for n in xrange(0, len(factorizations)):
        print n+2, factorizations[n]
    #print factorizations

import sys
main(int(sys.argv[1]))
