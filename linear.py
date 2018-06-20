import math
import pickle
import collections
import pdb
import copy
import cProfile
import sys
import itertools
import logging
from functools import reduce
from util import *

# FixMe: Factorizations should always be represented as a tuple.

# Global logger
logger = None

def setupLogger():
    """Set up the global logger to be used by this module."""
    global logger
    logger = logging.getLogger('Moebius')
    logger.setLevel(logging.DEBUG)
    fh = logging.FileHandler('log.log')
    fh.setLevel(logging.DEBUG)
    ch = logging.StreamHandler()
    ch.setLevel(logging.INFO)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    fh.setFormatter(formatter)
    ch.setFormatter(formatter)
    logger.addHandler(fh)
    logger.addHandler(ch)

def calculated_Z(f, primes, factorizations):
    """Calculates Z(f).

    For each prime 'p', counts the number of factorizations 'a' where
    p*p*a <= f .  Returns the total number of cases this is true for."""

    count = 0
    max_idx = 0
    in_ = set()
    for p in primes:
        val = ord([p,p], f, factorizations)
        if val == 99:
            return -1, ([p,p],factorizations)
        if val  <= 0:
            in_.add((p,p))
        else:
            break
        for x_idx in range(0,len(factorizations)):
            x = factorizations[x_idx]
            possibility = sorted([p,p]+x)
            val = ord(possibility, f, factorizations)
            if val == 99:
                return -1, (possibility, factorizations)
            if val <= 0:
                max_idx = max(max_idx, x_idx)
                in_.add(tuple(possibility))
            else:
                break
    return len(in_), None

def calculated_Z1(f, primes, factorizations):
    """Calculates Z1(f).

    For each prime 'p', counts the number of factorizations 'a' where
    p*a <= f and moebius(p*a)==1.  Returns the total number of cases
    this is true for.
    """
    in_ = set()
    a = 5
    for p in primes:
        a = 5
        for x in factorizations:
            if p in x:
                continue
            if len(set(x)) != len(x):
                continue
            if (len(x) % 2) == 0:
                continue

            possibility = sorted([p]+x)
            val = ord(possibility, f, factorizations)
            if val == 99:
                return -1
            elif val <= 0:
                in_.add(tuple(possibility))
            else:
                break
    return len(in_)

def ord(t, o, factorizations):
    """Returns whether this < other for a specific factorization possibility.

    Check each permutation and 2-way split of this and other to try and
    find one where both parts of this are less than the parts of
    other.

    Returns -1 if t < o, 0 if t == o, 1 if t > o
    """
    t, o = simplify(t, o)

    if not t and not o or t == o:
        return 0
    if not t:
        return -1
    if not o:
        return 1

    t_index = None
    o_index = None

    try:
        t_index = factorizations.index(t)
    except:
        pass

    try:
        o_index = factorizations.index(o)
    except:
        pass

    t_found = t_index is not None
    o_found = o_index is not None

    if t_found and not o_found:
        # If t is in the list and o is not, t < o
        return -1
    if o_found and not t_found:
        return 1
    if t_found and t_index < o_index:
        # If both are found and t is earlier than o, t < o
        return -1
    if o_found and o_index < t_index:
        return 1

    return 99

@memoized
def Z(n):
    """ Returns the real Z(n)"""
    return len([moebius(x) for x in range(1,n+1) if moebius(x) == 0])

@memoized
def Z1(n):
    """ Returns the real Z(n)"""
    return len([moebius(x) for x in range(2,n+1) if moebius(x) == 1])

# FixMe: Merge ZIsPossible and Z1IsPossible
@memoized
def ZIsPossible(z, m):
    """ Given z and m, return the last possible index it could occur at (-1 if impossible)"""
    n = 2
    z_ = 0
    n_max = -1
    while z_ <= z:
        m_ = moebius(n)
        z_ = Z(n)
        if z_ == z and m_ == m:
            n_max = n
        n += 1
    return n_max

@memoized
def Z1IsPossible(z, m):
    """ Given z and m, return the last possible index it could occur at (-1 if impossible)"""
    n = 2
    z_ = 0
    n_max = -1
    while z_ <= z:
        m_ = moebius(n)
        z_ = Z1(n)
        if z_ == z and m_ == m:
            n_max = n
        n += 1
    return n_max

@memoized
def factorize(n):
    """Returns the factorization of n"""
    if n == 1: return []

    assert n > 1
    factors = []
    for i in range(2, n + 1):
        while (n % i) == 0:
            return [i] + factorize(int(n/i))
    if n != 1:
        pdb.set_trace()
    assert n == 1
    return factors

def moebius_factorization(f):
    if len(set(f)) != len(f):
        return 0
    return int(math.pow(-1, len(f)))

@memoized
def moebius(n):
    """Returns the moebius value of n

    This function is described as:
        moebius(n) == (-1)^m if the factorization of n is a product of m distinct primes
        moebius(n) == 0 otherswise.
    """

    assert n > 0
    if n == 1:
        return 1

    return moebius_factorization(factorize(n))

def one_unique_prime_factorization(n, factorizations, p, f, smallest, all_factorizations, condition):
    """Returns the possible factorizations of n with no repeated factors.

    'p' is the prime to use and 'potential' is the factorization we are
    extending, so
    """
    # FixMe: This and one_prime_factorization are similar.  Merge if
    # possible.
    possibility = sorted(f + [p])
    if not condition(possibility):
        return None, smallest, False

    if tuple(possibility) in all_factorizations.finished or possibility in factorizations:
        # Alread found this or it has a repeated prime
        return None, smallest, False

    return possibility, f, True


def one_prime_factor(n, factorizations, p, f, smallest, all_factorizations, condition):
    possibility = sorted(f+[p])
    if not condition(possibility):
        return None, smallest, False
    if tuple(possibility) in all_factorizations.finished or possibility in factorizations:
        return None, smallest, False
    return possibility, f, True

def new_unique_prime_factorizations(n, odd, primes, factorizations, all_factorizations, unique_primes_starting_cache, max_f_idx):
    """Returns all prime factorizations with no duplicated primes with either even or odd number of factors.

    Find all possibilities of size start_length, then start_length+2,
    start_length+4, ... until possibilities are no longer generated.
    """
    r = []
    if odd:
        # There is always the possibility of being prime
        r += [[n]]

    smallest = None
    max_idx = 0

    new_cache = {}

    for p in primes:

        found = False

        f_idx_start = 0
        if p in unique_primes_starting_cache:
            f_idx_start = unique_primes_starting_cache[p]

        for f_idx in range(f_idx_start, min(len(factorizations),max_f_idx+1)):

            f = factorizations[f_idx]

            #if len(set(f)) != len(f):
                #continue

            #if p in f:
                #continue

            if odd and ((len(f) % 2) == 1) or \
                not odd and len(f) % 2 == 0:
                continue

            n_, smallest, break_ = one_unique_prime_factorization(
                n, factorizations, p, f, smallest, all_factorizations,
                lambda possibility: len(possibility) == len(set(possibility)) and (odd and len(f) % 2 == 0 or len(f) % 2 == 1))
            if n_ and n_ not in r:
                r += [n_]

            if break_:
                found = True
                if p not in new_cache:
                    new_cache[p] = f_idx
                if not max_idx:
                    max_idx = max(max_idx, f_idx)
                    if [p] in factorizations:
                        max_idx = max(max_idx,factorizations.index([p]))

                break
        if not found:
            max_idx = len(factorizations)
            new_cache[p] = 0

    return r, max_idx, new_cache

#def is_possible_all_in_factorization(n, possibilities, all_factorizations):
def should_stop_search(n, possibilities, all_factorizations):
    # We should stop the search if it's not possible for all of the possibilities
    # to be in all_factorizations at the same time.
    locs = set()
    items = set()
    for possibility in possibilities:
        for idx in all_factorizations.reverse_idx[possibility]:
            locs.add(idx)
            for i in all_factorizations[idx]:
                items.add(tuple(i))
    #if tuple([2, 2, 2, 2, 2, 3]) in possibilities: pdb.set_trace()

    result =  (len(locs)+1) >= len(items)
    result2 = len(possibilities) > (len(locs))
    #if result != result2: pdb.set_trace()
    #if n == 24 and result: pdb.set_trace()
    return result2
    #return len(possibilities) > (len(locs))

o = False
def new_repeated_prime_factorizations(n, primes, factorizations, all_factorizations, repeated_primes_starting_cache, max_f_idx):
   global o
   if n == 32: o = True
   prime_location_map = {}
   prime_max_location_map = {}
   primes = []
   results = set()
   for f_idx in range(0, len(factorizations)):
       f = factorizations[f_idx]
       if len(f) == 1:
           prime_location_map[f[0]] = 0
           primes += f
       new_locs = {}
       for p in primes:
           p_start_idx = prime_location_map[p]
           for p_idx in range(p_start_idx, f_idx+1):
               possibility = sorted(factorizations[p_idx]+[p])

               stop = False
               p_loc = primes.index(p)
               for p_prime_idx in range(0, p_loc):
                  p_prime = primes[p_prime_idx]
                  p_prime_possibility = sorted([p_prime] + factorizations[new_locs[p_prime]-1])
                  if new_locs[p_prime] == 0:
                      stop = True
                      break
                  if ord(possibility, p_prime_possibility, factorizations) == 1 or \
                    ord_absolute(possibility, p_prime_possibility, all_factorizations) == 1:
                      stop = True
                      break
               if stop:
                   new_locs[p] = p_idx
                   break
               #if p_idx == 7 and p == 2 and n == 24:pdb.set_trace()
               new_locs[p] = p_idx+1
               if len(possibility) == len(set(possibility)):
                  continue
               if tuple(possibility) in all_factorizations.finished or tuple(possibility) in factorizations:
                  continue
               results.add(tuple(possibility))

       prime_location_map = new_locs
       #if len(results) > 1: pdb.set_trace()
       if results and should_stop_search(n, results, all_factorizations):
           break

   return [list(x) for x in results], f_idx

def prune_elements_lt(n, factorizations, factorization, all_factorizations):
    """Remove all elements in factorizations that are less than another element in factorizations
    """
    keep = []
    for x in range(0, len(factorizations)):

        if len(factorizations) == 1:
            keep += [factorizations[x]]
            continue

        x_greater_than_all = True

        for y in range(0, len(factorizations)):
            if x == y: continue
            if ord_absolute(factorizations[x],
                            factorizations[y],
                            all_factorizations) != 1:
                x_greater_than_all = False
                break
        if not x_greater_than_all:
            keep += [factorizations[x]]
        else:
            #if moebius(n) == 0: pdb.set_trace()
            pass
    return keep

def ord_absolute(t, o, all_factorizations):
    # Returns whether t < o given the entire list of factorizations.  99 is unknown
    t, o = simplify(t,o)
    if not t and not o:
        return 0

    if not t:
        return -1

    if not o:
        return 1

    t_found, t_first_idx = index_recursive(all_factorizations,list(t),last=False)
    t_found, t_last_idx = index_recursive(all_factorizations,list(t),last=True)
    o_found, o_first_idx = index_recursive(all_factorizations,list(o),last=False)
    o_found, o_last_idx = index_recursive(all_factorizations,list(o),last=True)

    if not t_found and not o_found:
        return 99

    if t_found and not o_found and tuple(t) in all_factorizations.finished:
        return -1

    if o_found and not t_found and tuple(o) in all_factorizations.finished:
        return 1


    if tuple(t) not in all_factorizations.finished and tuple(o) not in all_factorizations.finished:
        return 99

    elif tuple(t) not in all_factorizations.finished and o_last_idx < t_first_idx:
        return 1

    elif tuple(t) not in all_factorizations.finished:
        return 99

    elif t_last_idx < o_first_idx:
        return -1

    elif o_last_idx < t_first_idx:
        return 1

    return 99


def update_outstanding_and_finished(all_factorizations, new):
    outstanding_count = collections.defaultdict(lambda : 0)
    # For each outstanding factorization, how many trees exists where the
    # factorization either exists or is less than everything in new.

    total = 0
    # Total number of lists we generate

    new_outstanding = set()
    new_finished = set()

    outstanding = all_factorizations.outstanding

    for n in new:
        if tuple(n) not in all_factorizations.finished:
            outstanding.add(tuple(n))

    for o in all_factorizations.outstanding:



        s, i = shared(o, all_factorizations)
        lt = []
        gt = []
        equiv = []

        for n in i:
            r = ord_absolute(n, o, all_factorizations)
            if r == -1:
                lt += [n]
            elif r == 1:
                gt += [n]
            else:
                equiv += [n]
        if len(s) >= len(lt)+len(equiv):
            new_finished.add(o)
        else:
            new_outstanding.add(o)

    outstanding = copy.copy(new_outstanding)
    new_outstanding = set()
    for o in outstanding:
        all_lower = True
        for y in new:
            if ord_absolute(o,y,all_factorizations) > -1:
                all_lower = False
                break
        if all_lower:
            new_finished.add(o)
        else:
            new_outstanding.add(o)

    #LT anything that's finished
    outstanding = new_outstanding
    new_outstanding = set()
    for o in outstanding:
        for y in all_factorizations.finished:
            if ord_absolute(o,y,all_factorizations) == -1:
                new_finished.add(o)
                break
        if o not in new_finished:
            new_outstanding.add(o)


    outstanding = new_outstanding

    if len(new)==1:
        new_finished.add(tuple(new[0]))
    else:
        for x in new:
            if tuple(x) not in outstanding and \
              tuple(x) not in all_factorizations.finished:
                outstanding.add(tuple(x))
    all_factorizations.finished |= new_finished
    all_factorizations.outstanding = outstanding
    return new_finished


def generate_possibilities_for_factorization(n, m, factorizations, all_factorizations, start, end, prime_starting_cache, max_idx):
    """ Generate all possibilities for the given n and m. """
    primes = [x[0] for x in factorizations if len(x) == 1]
    if m == -1:
        r, max_idx, new_cache = new_unique_prime_factorizations(
            n,
            True,
            primes,
            factorizations,
            all_factorizations,
            prime_starting_cache[-1],
            max_idx)

        if not max_idx:
            max_idx = len(factorizations)

        max_idx += 1
        while max_idx < len(all_factorizations):
            if len(all_factorizations[max_idx]) == 1 and len(all_factorizations[max_idx][0]):
                break
            max_idx += 1

        if max_idx >= len(all_factorizations):
              end[-1] = -1
        if end[-1] != -1:
              end[-1] = max(end[-1], max_idx)

        return r, new_cache
    elif m == 0:
        r, max_idx = new_repeated_prime_factorizations(
            n,
            primes,
            factorizations,
            all_factorizations,
            prime_starting_cache[0],
            max_idx)

        if max_idx != -1:
            start[0] = min(start[0], max_idx)

        if(max_idx) != -1:

            for x in all_factorizations[max_idx]:
                max_idx = max([max_idx] + all_factorizations.reverse_idx[tuple(x)])

            max_idx += 1

            found = False
            while not found and max_idx < len(all_factorizations):
                for y in all_factorizations[max_idx]:
                    if 2 in y and tuple(y) in all_factorizations.finished:
                        found, max_idx = index_recursive(all_factorizations, y, last=True)
                        break
                max_idx = max_idx + 1


            if max_idx >= len(all_factorizations):
                end[0] = -1
            if end[0] != -1:
                end[0] = max(end[0], max_idx)

        return r, {}

    elif m == 1:
        r, max_idx, new_cache = new_unique_prime_factorizations(
            n,
            False,
            primes,
            factorizations,
            all_factorizations,
            prime_starting_cache[1],
            max_idx)

        if not max_idx:
            max_idx = -1

        while [x for x in all_factorizations[max_idx] if len(x)==1]:
            max_idx += 1

        max_idx += 1

        while max_idx < len(all_factorizations):
            if len(all_factorizations[max_idx]) == 1 and len(all_factorizations[max_idx][0]) == 1:
                break
            max_idx += 1

        if max_idx >= len(all_factorizations):
              end[1] = -1
        if end[1] != -1:
              end[1] = max(end[1], max_idx+1)
        return r, new_cache
    else:
        assert False

def all_confusions(all_factorizations, finished):
    all_confusions = set()
    for x in all_factorizations:
        if len(x) == 1:
            continue
        else:
            allfinished = True
            factors = []
            for y in x:
                if tuple(y) not in finished:
                    allfinished = False
                    break
                else:
                    factors += y
            if allfinished:
                all_confusions.add(tuple(sorted(tuple(factors))))
    return all_confusions

def all_combinations_not_calculated(all_confusions, z_calculated):
    all_potential_useful_z = set()
    for x in all_confusions:
        for y in range(1,len(x)):
            for z in itertools.combinations(x,y):
                if tuple(z) not in z_calculated:
                    all_potential_useful_z.add(z)
    return all_potential_useful_z

def all_potentially_useful_z(all_factorizations,
                             z_calculated,
                             blocked_potential_useful_z,
                             finished,
                             new_finished):
    """ Returns all n for which Z(n) may be useful """
    all_confusions_ = all_confusions(all_factorizations, finished)
    all_potential_useful_z = all_combinations_not_calculated(all_confusions_, z_calculated)
    return all_potential_useful_z | new_finished

def ranges_for_z_calculations(n, all_factorizations, it_set):
    """Calculates the range in all_factorization that each factorization is concerned with.

    This is an optimization, so we don't have to run through every full
    factorization for every Z.  The max_idx for a factorization will be
    the maximum index in all_factorization we need to show that [p*p]*a
    > factorization for all p.  Th min_idx is the lowest index that we
    are unsure whether p*p*a > factorization.  We are only really
    interested in cases where we can always calculate Z, but will
    sometimes get different results.
    """

    possible_primes = []
    for x in all_factorizations:
        for y in x:
            if len(y) == 1:
                possible_primes += y

    new_it_set = set()
    for y in it_set:
        valid = True
        for x in y:
            assert len(all_factorizations.reverse_idx[(x,)])==1
            if len(all_factorizations[all_factorizations.reverse_idx[(x,)][0]]) > 1:
                valid = False
        if valid:
            new_it_set.add(tuple(y))

    min_idx = {}
    max_idx = {}
    mask = {}

    for y in new_it_set:
        d = set()
        d.add(y)

        mask[y] = [False] * len(all_factorizations)

        for p in possible_primes:
            # For each prime, try to find some index x_idx s.t
            # [p,p]*all_factorizations[x_idx] > y.  Keep track of the maximum
            # of these.
            found_upper_bound = False
            primes = []

            for x_idx in range(0, len(all_factorizations)):

                for z in all_factorizations[x_idx]:

                    if len(z) == 1:
                        primes += z

                    v = sorted([p,p] + z)
                    val = ord_absolute(v,y,all_factorizations)

                    if val == 99:
                        # This factorization we are unsure about; possibly
                        # update our min_idx.

                        t, o = simplify(v, y)

                        t_found, t_idx = index_recursive(all_factorizations, t)
                        t_found_last, t_idx_last = index_recursive(all_factorizations, t, last=True)

                        for x in range(t_idx,t_idx_last+1):
                            mask[y][x] = True

                        o_found, o_idx = index_recursive(all_factorizations, o)
                        o_found_last, o_idx_last = index_recursive(all_factorizations, o, last=True)

                        for x in range(o_idx,o_idx_last+1):
                            if n == 51 and x == 0: pdb.set_trace()
                            mask[y][x] = True

                    v = sorted([p] + z)
                    if True or len(v) == len(set(v)) and (len(set(v)) % 2) == 1:
                        val = ord_absolute(v,y,all_factorizations)

                        if val == 99:
                            # This factorization we are unsure about; possibly
                            # update our min_idx.

                            t, o = simplify(v, y)

                            t_found, t_idx = index_recursive(all_factorizations, t)
                            t_found_last, t_idx_last = index_recursive(all_factorizations, t, last=True)

                            for x in range(t_idx,t_idx_last+1):
                                mask[y][x] = True

                            o_found, o_idx = index_recursive(all_factorizations, o)
                            o_found_last, o_idx_last = index_recursive(all_factorizations, o, last=True)

                            for x in range(o_idx,o_idx_last+1):
                                if n == 51 and x == 0: pdb.set_trace()
                                mask[y][x] = True

                    if z == list(y):
                        mask[y][x_idx] = True

                    found = False
                    for d_ in d:
                        if list(z) == sorted(list(d_)+[p]):
                          mask[y][x_idx] = True
                          found = True
                    if list(y) == sorted(z + [p]):
                        mask[y][x_idx] = True
                        found = True
                    if found:
                       for z_ in all_factorizations[x_idx]:
                           d.add(tuple(z_))
            # End for x_idx in range(0, len(all_factorizations)):
            for x in range(0, len(mask[y])):
                if mask[y][x]:
                        for z in all_factorizations[x]:
                            for zp in z:
                                mask[y][all_factorizations.reverse_idx[(zp,)][0]] = True

        for x in range(0,2):
            present = set()
            for x_idx in range(0, len(all_factorizations)):
                if mask[y][x_idx] == True:
                    for z in all_factorizations[x_idx]:
                        present.add(tuple(z))

            for x_idx in range(0, len(all_factorizations)):
                if mask[y][x_idx] == False:
                    for z in all_factorizations[x_idx]:
                        if tuple(z) in present:
                            mask[y][x_idx] = True

    return min_idx, max_idx, mask

def is_consistent(n, factorization, all_factorizations, y, mask):
    if len(y) == 1:
        return True

    yi = factorization.index(list(y))

    primes = set()

    for idx in range(0,len(y)):
        p = y[idx]

        rest = y[:idx] + y[idx+1:]

        lt = True

        i = -1
        for x in factorization:
            i = i + 1

            if not mask[i]:
                for z in all_factorizations[i]:
                    if len(z) == 1:
                        primes.add(tuple(z))

                continue

            if len(x)==1:
                primes.add(tuple(x))


            for p_ in x:
                if tuple([p_]) not in primes:
                    return False

            if x == rest:
                lt = False
                continue

            if lt:
                v = sorted([p] + x)
                if v not in factorization:
                    if tuple(v) in all_factorizations.finished and \
                      all_factorizations.reverse_idx[tuple(v)][-1] < factorization.index(y):
                        continue
                    return False
                vi = factorization.index(v)

                if vi >= yi:
                    return False

            else:
                v = sorted([p] + x)
                if v not in factorization:
                    if ((tuple(v) not in all_factorizations.finished) or
                        (tuple(v) in all_factorizations.finished and \
                        all_factorizations.reverse_idx[tuple(v)][0] > factorization.index(y)) or
                        len(all_factorizations.reverse_idx[tuple(v)])==0):
                        continue
                    return False

                vi = factorization.index(v)

                if vi <= yi:
                    return False

    return True

def analyze_z_for_factorizations_mask(n, all_factorizations, new_finished, mask):
    eliminate = []

    for y in mask:
        if len(y) == 1: continue
        logger.debug("  About to analyze masked Z for y="+str(y))
        e = copy.deepcopy(all_factorizations.all_factorizations)
        for idx in range(0, len(all_factorizations)):
            if not mask[y][idx]:
                e[idx] = []

        for x in generate_all_possible_lists_for_mask(all_factorizations, mask[y]):

            primes = [x[0] for x in x if len(x) == 1]

            moebius_of_y = 0 # FixMe: move this out into a function
            if len(set(y)) == len(y):
                moebius_of_y = int(math.pow(-1,len(y)))

            if list(y) not in x:
                continue

            y = list(y)


            if not is_consistent(n, x, all_factorizations, y, mask[tuple(y)]):
                continue

            # correct = True
            # if y == [5,17]:
            #     for idx_ in range(0,len(all_factorizations)):
            #         if mask[tuple(y)][idx_] and x[idx_] != factorize(idx_+2):
            #                 correct = False

            possible_z, idx = calculated_Z(y, primes, x)
            possible_z1 = calculated_Z1(y, primes, x)

            possible = True
            if possible_z1 == -1 or possible_z == -1 or y not in x:
                # We can't figure everything out; just go ahead and delete our work
                # FixMe: This should be impossible
                assert False
                e = {}
                break
            elif ZIsPossible(possible_z,moebius_of_y) == -1 or \
                 Z1IsPossible(possible_z1,moebius_of_y) == -1:
                # If there is no n where Z(n) == possible_z with the correct
                # moebius, this is impossible.
                possible = False
            elif (((ZIsPossible(possible_z,moebius_of_y) < (x.index(y)+2)))) or \
              (((Z1IsPossible(possible_z1,moebius_of_y) < (x.index(y)+2)))):
                    ### Z1 here
                # If the largest possible N for which Z(n) == possible_z is
                # a lower position than where y is, then this is impossible
                possible = False
            elif (possible_z != Z(x.index(y)+2)) or \
              (possible_z1 != Z1(x.index(y)+2)):
                # If the Z we calculated doesn't match Z(n) for this, just
                # exit.
                possible = False
            elif not is_consistent(n, x, all_factorizations, y, mask[tuple(y)]):
                possible = False

            if possible:
                for i in range(0, len(e)):
                    if x[i] in e[i]:
                        e[i].remove(x[i])

        for idx in range(0,len(e)):
           for z in e[idx]:
               logger.info("  Mask Eliminating [n=%d,%s] based on: %s " % (idx+2,str(z),str(y)))
               eliminate += [[idx, z]]
               if z == factorize(idx+2):
                   pdb.set_trace()
                   assert False
        logger.debug("  Done analyzing masked Z for y="+str(y))

    return eliminate


def all_eliminations(n, all_factorizations, new_finished):
    """ Returns factorizations for positions we can show are impossible. """
    global logger

    min_idx, max_idx, mask = ranges_for_z_calculations(n, all_factorizations, new_finished)

    logger.debug("  Generated upper and lower bounds for Z: "+str(min_idx)+ " " + str(max_idx))
    logger.debug("  mask: "+str(mask))
    min_idx = {}
    max_idx = {}
    for x in new_finished:
        min_idx[x] = 0
        max_idx[x] = len(all_factorizations)-1

    e_ = analyze_z_for_factorizations_mask(n, all_factorizations, new_finished, mask)

    return e_, []

def shared(f, all_factorizations):
    items = set()
    positions = set()
    expand = set()
    for p in all_factorizations.reverse_idx[tuple(f)]:
        positions.add(p)
        for i in all_factorizations[p]:
            items.add(tuple(i))

    start_positions = len(positions)

    while True:
        start_positions = len(positions)
        new_i = set()
        new_p = set()
        for f in items:
            for p in all_factorizations.reverse_idx[tuple(f)]:
                new_p.add(p)
                for i in all_factorizations[p]:
                    new_i.add(tuple(i))
        positions = positions.union(new_p)
        items = items.union(new_i)
        if len(positions) == start_positions:
            break


    return positions, items

def filter(new, all_factorizations):
    # Filter out too-high values(more than enough space for all lower values)
    new_new = []
    for f in new:
        lt = []
        gt = []
        equiv = []
        p, i = shared(f, all_factorizations)
        if len(p) == 0:
            for x in new:
                p_, i_ = shared(x, all_factorizations)
                p = p.union(p_)
                i = i.union(i_)

        for n in i:
            r = ord_absolute(n, f, all_factorizations)
            if r == -1:
                lt += [n]
            elif r == 1:
                gt += [n]
            else:
                equiv += [n]
        if len(p)+1 > (len(lt)):
            # It is possible for a lower value to be present
            new_new += [f]

    return new_new

def generate_factorization_possibilities(max_n, state):
    """ Generates the list of possible factorizations from start_n to max_n. """
    global logger, calls, ord_cache

    logger.info("Program begin")

    while state.n <= max_n:
        n = state.n
        m = moebius(n)

        pickle.dump(state, open("saves/n=%di=%d"%(state.n, state.i),"wb"))

        logger.info("Processing n=%d moebius=%d"%(n,m))

        state.possibilities_for_n[n] = copy.deepcopy(state.all_factorizations)
        state.start_for_n[n] = copy.copy(state.start)
        state.end_for_n[n] = copy.copy(state.end)

        new = []
        # The array containing all the new values we generate.

        s = state.start[m]
        e = state.end[m]
        #e = -1

        state.end[m] = 0 # FixMe: What is this for?
        # Reset end so it can be set properly each iteration
        if e == -1 or e == 0: #here
            e = len(state.all_factorizations)


        logger.debug("  possibility generation: start: %d end: %d"%(s,e))

        mask = [True]*e+[False]*len(state.all_factorizations)
        # for x in state.all_factorizations.outstanding:
        #     if moebius_factorization(x)==moebius(n):
        #         for y in state.all_factorizations.reverse_idx[tuple(x)]:
        #             mask[y] = True

        logger.debug("  primes_starting_cache used: " + str(state.primes_starting_cache))
        new_primes_starting_cache = {}
        count = 0
        for factorizations in generate_all_possible_lists_for_mask(state.all_factorizations.all_factorizations,mask):
            factorizations = factorizations#[:e]
            # Generate possibilities for each subset of the possibility tree
            # that matters
            count += 1
            new_, new_cache = generate_possibilities_for_factorization(
                n,
                m,
                factorizations[:e],
                state.all_factorizations,
                state.start,
                state.end,
                state.primes_starting_cache,
                e)

            new_ = prune_elements_lt(n, new_, factorizations, state.all_factorizations)
            # prune the ones that are more than all the other generated possibilities

            new += [x for x in new_ if x not in new and x not in state.eliminate[n-2]]
            # add all the new factorizations that remain that we have not
            # previously eliminated using z.

            for p in new_cache:
                if p not in new_primes_starting_cache:
                    new_primes_starting_cache[p] = new_cache[p]
                else:
                    new_primes_starting_cache[p] = min(new_cache[p],
                                                       new_primes_starting_cache[p])

        logger.debug("  # of options:"+str(count))
        new_new = []
        #pdb.set_trace()
        for possibility in new:
            primes_finished = set()
            found_all = True
            for i in range(0, len(possibility)):
                # Go through all factorizations before 'potential' and ensure that no
                # factorization * p is lower than potential * p but doesn't exist.
                prime = possibility[i]
                if prime in primes_finished:
                    continue
                primes_finished.add(prime)
                other = possibility[:i] + possibility[i + 1:]
                if not other:
                    break

                found, idx = index_recursive(state.all_factorizations, other)
                if not found:
                    found_all = False
                    break

                for i in range(0, idx):
                   for y in state.all_factorizations[i]:
                       x = sorted([prime] + y)
                       _, idx__ = index_recursive(state.all_factorizations, y, last=True)
                       found, _ = index_recursive(state.all_factorizations, x, last=True)
                       if idx__ < idx and not found:
                          found_all = False
                          break
                   if not found_all:
                        break
                if not found_all:
                    break

            if found_all:
                new_new += [possibility]
        new = new_new

        state.primes_starting_cache[m] = new_primes_starting_cache
        logger.debug("  Initial possibilities: %s"%(str(new)))

        if not factorize(n) in new or \
            (n == 92 and [2, 2, 2, 2, 2, 3] in new):
            print(1, "[[1]]")
            for i in range(0, len(state.all_factorizations)):
                print(i + 2, state.all_factorizations[i])
            print(new)
            pdb.set_trace()
            assert False

        new = filter(new, state.all_factorizations)

        assert factorize(n) in new
        state.all_factorizations.all_factorizations += [sorted(new)]
        state.all_factorizations.update_reverse_idx()

        # Update the outstanding and finished sets.  new_finished is the
        # outstanding factorizations that we finished at this n.
        new_finished = update_outstanding_and_finished(state.all_factorizations, new)


        logger.debug("  outstanding processing finished: outstanding=%s new_finished=%s",state.all_factorizations.outstanding,new_finished)

        all_potential_useful_z = new_finished

        if all_potential_useful_z:
            new_eliminate, new_z_calculated = all_eliminations(n, state.all_factorizations, new_finished)

            if new_eliminate:
                # For all of our new elimination candidates, update
                # all_factorizations and reset to continue calculations from
                # the lowest point we changed

                min_ = None
                for x in new_eliminate:
                    if x[1] in state.all_factorizations[x[0]]:
                        state.all_factorizations[x[0]].remove(x[1])
                        if not min_:
                            min_ = x[0]
                        min_ = min(min_,x[0])
                        if [x[1]] not in state.eliminate[x[0]]:
                            state.eliminate[x[0]] += [x[1]]
                state.n = min_+2
                state.i += 1

                state.primes_starting_cache = {-1: {}, 0 : {}, 1: {}}
                state.all_factorizations = state.possibilities_for_n[state.n]
                state.start = state.start_for_n[n]
                state.end = state.end_for_n[n]

                continue

        # End of the loop; update n
        state.n += 1

    return state.all_factorizations

if __name__ == "__main__":
    def main():
        setupLogger()
        state = State()
        if len(sys.argv) > 2:
            import pickle
            state = pickle.load(open(sys.argv[2],"rb"))
            state.n = int(state.n)
        f = generate_factorization_possibilities(int(sys.argv[1]), state)
        print(1, "[[1]]")
        for n in range(0, len(f)):
            print(n + 2, f[n])

    main()
