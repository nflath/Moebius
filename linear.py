import math
import collections
import pdb
import copy
import cProfile
import sys
import itertools
import logging
from functools import reduce
from util import *
# Naming conventions:

# Set up the logger
logger = None
def setupLogger():
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
    """Calculates Z(f)."""

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
    """Calculates Z(f).

    For each prime 'p', counts the number of factorizations 'a' where
    p*a <= f and moebius(p*a)==1.  Returns the total number of cases
    this is true for.
    """
    in_ = set()
    for p in primes:
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

def ord_no_permutation(t, o, factorizations):
    """Returns whether we can show t < o or not just based on the given factorization.

    Will simplify t and o, but not go through all comparison of factors

    Returns -1 if t < o, 0 if t == 0, 1 if o > t, 99 if unknown

    """
    # If either t or o are eliminated, one is larger than the other(or both
    # are equal).
    if not t and not o:
        return 0
    if not t:
        return -1
    if not o:
        return 1

    t_index = None
    o_index = None
    global ord_cache
    if (tuple(t), tuple(o)) in ord_cache:
        return ord_cache[tuple(t), tuple(o)]

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


calls = collections.defaultdict(lambda : 0)
ord_cache = {}
ord_cache_hits = 0
ord_calls = 0

def ord(this, other, factorizations):
    """Returns whether this < other in a more complicated way.

    Check each permutation and 2-way split of this and other to try and
    find one where both parts of this are less than the parts of
    other.

    Returns -1 if t < 0, 0 if t == 0, 1 if t > o, 99 if unknown
    """
    global ord_cache, ord_cache_hits, ord_calls, calls

    ord_calls += 1
    if (tuple(this),tuple(other),) in ord_cache:
        ord_cache_hits += 1
        return ord_cache[(tuple(this),tuple(other),)]

    t, o = simplify(this, other)

    if not t and o:
        return -1
    elif not o and t:
        return 1
    if not t and not o:
        return 0

    if (tuple(t),tuple(o),) in ord_cache:
        ord_cache_hits += 1
        return ord_cache[(tuple(t),tuple(o),)]

    calls[(tuple(t),tuple(o),)] += 1

    for t_begin_len in range(0, len(t)):
        for o_begin_len in range(0, int(len(o))):
            for t_tmp_begin in itertools.combinations(t, t_begin_len):
                for o_tmp_begin in itertools.combinations(o, o_begin_len):

                    t_tmp_begin = sorted(list(t_tmp_begin))
                    o_tmp_begin = sorted(list(o_tmp_begin))
                    t_tmp_end = copy.copy(t)
                    o_tmp_end = copy.copy(o)

                    for x in t_tmp_begin:
                        t_tmp_end.remove(x)

                    for x in o_tmp_begin:
                        o_tmp_end.remove(x)

                    if t_tmp_end and o_tmp_end and not t_tmp_begin and not o_tmp_begin:
                        val = ord_no_permutation(t_tmp_end, o_tmp_end, factorizations)
                        if val == -1:
                            return -1
                        elif val == 1:
                            return 1
                    elif t_tmp_begin and t_tmp_end and o_tmp_begin and o_tmp_end:
                        begin_val = ord_no_permutation(t_tmp_begin, o_tmp_begin, factorizations)
                        end_val = ord_no_permutation(t_tmp_end, o_tmp_end, factorizations)
                        if (begin_val == -1 and end_val == -1) or \
                          (begin_val == -1 and end_val == 0) or \
                          (begin_val == 0 and end_val == -1):
                            return -1
                        elif begin_val == 1 and end_val == 1:
                            return 1
                    elif t_tmp_begin and o_tmp_begin and not t_tmp_end and not o_tmp_end:
                        val = ord_no_permutation(t_tmp_begin, o_tmp_begin, factorizations)
                        if val == -1:
                            return -1
                        elif val == 1:
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
def factorize(n):
    """Returns the factorization of n"""

    assert n > 1
    factors = []
    for i in range(2, n + 1):
        while (n % i) == 0:
            factors += [i]
            n = n / i
    assert n == 1
    return factors

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

    f = factorize(n)
    if len(set(f)) != len(f):
        return 0
    return int(math.pow(-1, len(f)))


def one_unique_prime_factorization(n, factorizations, potential, p, smallest, finished, all_factorizations):
    """Returns the possible factorizations of n with no repeated factors.

    'p' is the prime to use and 'potential' is the factorization we are
    extending, so
    """
    # FixMe: This and one_repeated_prime_factorization are similar.  Merge if
    # possible.
    possibility = sorted(potential + [p])

    result = []
    if p == smallest:
        # FixMe: Move this out of this function into the containing one
        return [], smallest, True
    if possibility in factorizations or tuple(possibility) in finished:
        # Alread found this or it has a repeated prime
        return [], smallest, False
    if len(set(possibility)) != len(possibility):
        return [], smallest, False


    primes_finished = set()
    for i in range(0, len(possibility)):
        # Go through all factorizations before 'potential' and ensure that no
        # factorization * p is lower than potential * p but doesn't exist.
        prime = possibility[i]
        if prime in primes_finished:
            continue
        primes_finished.add(prime)
        other = possibility[:i] + possibility[i + 1:]

        found, idx = index_recursive(all_factorizations, other)
        if not found:
            return [], smallest, True

        for i in range(0, idx):
           for y in all_factorizations[i]:
               x = sorted([prime] + y)
               _, idx__ = index_recursive(all_factorizations, y, last=True)
               found, _ = index_recursive(all_factorizations, x, last=True)
               if idx__ < idx and not found:
                  return [], smallest,  True


        for i in factorizations:
            if ord(possibility,i,factorizations) == -1:
                return [], smallest, True

    return [possibility], potential, True


def new_unique_prime_factorizations(n, odd, primes, factorizations, finished, all_factorizations):
    """Returns all prime factorizations with no duplicated primes with either even or odd number of factors.

    Find all possibilities of size start_length, then start_length+2,
    start_length+4, ... until possibilities are no longer generated.
    """
    r = []
    if odd:
        r += [[n]]
        # Always a possibility of being prime
    smallest = None
    max_idx = None

    #if n == 47: pdb.set_trace()

    for p in primes:

        for f_idx in range(0, len(factorizations)):

            f = factorizations[f_idx]


            if len(set(f)) != len(f):
                continue

            if p in f:
                continue

            if odd and ((len(f) % 2) == 1) or \
                not odd and len(f) % 2 == 0:
                continue

            n_, smallest, break_ = one_unique_prime_factorization(
                n, factorizations, f, p, smallest, finished, all_factorizations)
            for x in n_:
                if x not in r:
                    r += [x]

            if break_:
                if not max_idx:
                    max_idx = f_idx
                    if [p] in factorizations:
                        max_idx = max(f_idx,factorizations.index([p]))
                break

    return r, max_idx


def one_repeated_prime_factor(n, factorizations, p, f, smallest, finished, all_factorizations):
    """ Returns the possible factorization using the given prime and intermediate factorization.

    """
    # The possibility we are examining; add the prime to the intermediate
    # factorization
    possibility = sorted(f + [p])

    if len(possibility) == len(set(possibility)):
        # The possibility does not have a repeated prime; just return

        # FixMe: If this is not in the results list, we should update
        # smallest_factorization_idx and return, right?
        return None, smallest, False

    # Just find what index f is in the factorizations list

    if possibility in factorizations or tuple(possibility) in finished:
        # We've already found this.  Keep searching.
        return None, smallest, False

    primes_finished = set()

    for i in range(0, len(possibility)):
        # Go through all factorizations before 'potential' and ensure that no
        # factorization * p is lower than potential * p but doesn't exist.
        prime = possibility[i]
        if prime in primes_finished:
            continue
        primes_finished.add(prime)
        other = possibility[:i] + possibility[i + 1:]


        found, idx = index_recursive(all_factorizations, other)
        if not found:
            return None, f, True


        for i in range(0, idx):
           for y in all_factorizations[i]:
               x = sorted([prime] + y)
               found, _ = index_recursive(all_factorizations, x)
               _, idx__ = index_recursive(all_factorizations, y, last=True)
               if idx__ < idx and not found:
                  return None, f,  True

        for i in factorizations:
            if ord(possibility,i,factorizations) == -1:
                return None, f, True

    return possibility, f, True


new_repeated_prime_factorizations_cache = {}
def new_repeated_prime_factorizations(n, primes, factorizations, finished, all_factorizations):
    """Return the possibilities for factorizaiton of n whose factorizations contain a repeated prime number.

    For each prime, loop through the factorizations of each n, and see
    if we can get a possibility for that pair.  Once you find a
    possibility for one factorization, you don't need to go further than
    that factorization for the later primes.
    """
    r = []
    smallest = None

    max_idx = None

    cached_starts = {}
    tpl = tupletized(factorizations)
    # for x in range(1,len(tpl)):
    #     if (n, tpl[:-x]) in new_repeated_prime_factorizations_cache:
    #         cached_starts = new_repeated_prime_factorizations_cache[(n, tpl[:-x])]
    #         break
    new_cached_starts = {}
    #if n == 4: pdb.set_trace()
    for p in primes:

        start = 0
        if p in cached_starts:
            start = cached_starts[p]

        for f_idx in range(start, len(factorizations)):
            f = factorizations[f_idx]
            break_ = False

            if smallest is not None and f == smallest:
                if max_idx is None: max_idx = f_idx
                new_cached_starts[p] = f_idx
                break

            r_, smallest, break_ = one_repeated_prime_factor(
                n, factorizations, p, f, smallest, finished, all_factorizations)


            if r_ and r_ not in r:
                r += [r_]
            break_ |= break_

            if break_:
                if max_idx is None:
                    max_idx = f_idx
                new_cached_starts[p] = f_idx
                break
        if max_idx is None:
            #pdb.set_trace()
            max_idx = -1
    new_repeated_prime_factorizations_cache[(n, tpl)] = new_cached_starts
    return r, max_idx

def prune_elements_lt(factorizations, factorization, all_factorizations,finished):
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
                            all_factorizations,
                            finished) != 1:
                x_greater_than_all = False
                break
        if not x_greater_than_all:
            keep += [factorizations[x]]
        else:
            pass
    return keep

def ord_absolute(t, o, all_factorizations, finished):
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

    if t_found and not o_found and tuple(t) in finished:
        return -1

    if o_found and not t_found and tuple(o) in finished:
        return 1


    if tuple(t) not in finished and tuple(o) not in finished:
        return 99

    elif tuple(t) not in finished and o_last_idx < t_first_idx:
        return 1

    elif tuple(t) not in finished:
        return 99

    elif t_last_idx < o_first_idx:
        return -1

    elif o_last_idx < t_first_idx:
        return 1

    return 99



def update_outstanding_and_finished(all_factorizations, new, outstanding, finished):
    outstanding_count = collections.defaultdict(lambda : 0)
    # For each outstanding factorization, how many trees exists where the
    # factorization either exists or is less than everything in new.

    total = 0
    # Total number of lists we generate

    new_outstanding = set()
    new_finished = set()

    for n in new:
        if tuple(n) not in finished:
            outstanding.add(tuple(n))

    for o in outstanding:
        in_all = True
        applicable = [x for x in all_factorizations if list(o) in x]
        for x in applicable:
            for y in x:
                applicable += [x for x in all_factorizations if y in x and x not in applicable]

        if applicable:
            for factorizations in generate_all_possible_lists(applicable,0,0):
                if list(o) not in factorizations:
                    in_all = False
                    break
            if in_all:
                new_finished.add(o)
            else:
                new_outstanding.add(o)
        else:
            new_finished.add(o)


    outstanding = copy.copy(new_outstanding)
    new_outstanding = set()

    for o in outstanding:
        all_lower = True
        for y in new:
            if ord_absolute(o,y,all_factorizations,finished) > -1:
                all_lower = False
                break
        if all_lower:
            new_finished.add(o)
        else:
            new_outstanding.add(o)

    outstanding = new_outstanding
    new_outstanding = set()
    for o in outstanding:
        for y in finished:
            if ord_absolute(o,y,all_factorizations,finished) == -1:
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
              tuple(x) not in finished:
                outstanding.add(tuple(x))
    finished |= new_finished
    return outstanding, finished, new_finished


def generate_possibilities_for_factorization(n, m, factorizations, finished, all_factorizations, start, end):
    """ Generate all possibilities for the given n and m. """
    primes = [x[0] for x in factorizations if len(x) == 1]
    if m == -1:
        r, max_idx = new_unique_prime_factorizations(
            n, True, primes, factorizations, finished, all_factorizations)

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

        return r
    elif m == 0:
        r, max_idx = new_repeated_prime_factorizations(
            n,
            primes,
            factorizations,
            finished,
            all_factorizations)

        if max_idx != -1:
            start[0] = min(start[0], max_idx)

        if(max_idx) == -1:
            max_idx = len(factorizations)

        if(max_idx) != -1:
            max_idx += 1

            found = False
            while not found and max_idx < len(all_factorizations):
                for y in all_factorizations[max_idx]:
                    if 2 in y and tuple(y) in finished and [2] + y not in r:
                        found, max_idx = index_recursive(all_factorizations, y, last=True)
                        break
                max_idx = max_idx + 1


            if max_idx >= len(all_factorizations):
                # Just go to the end next time
                end[0] = -1
            if end[0] != -1:
                end[0] = max(end[0], max_idx)

        return r

    elif m == 1:
        r, max_idx = new_unique_prime_factorizations(
            n, False, primes, factorizations, finished, all_factorizations)

        if not max_idx:
            max_idx = -1

        max_idx += 1

        while max_idx < len(all_factorizations):
            if len(all_factorizations[max_idx]) == 1 and len(all_factorizations[max_idx][0]) == 1:
                break
            max_idx += 1

        if max_idx >= len(all_factorizations):
              end[1] = -1
        if end[1] != -1:
              end[1] = max(end[1], max_idx+1)
        return r
    else:
        assert False

def update_ord_cache(ord_cache, all_factorizations, finished, old_calls):
    """ Updates the ord_cache ord() uses. """
    for x in finished:
        for y in finished:
            if (tuple(x),tuple(y)) in ord_cache:
                continue
            x_found, x_first_idx = index_recursive(all_factorizations,list(x),last=False)
            x_found, x_last_idx = index_recursive(all_factorizations,list(x),last=True)
            y_found, y_first_idx = index_recursive(all_factorizations,list(y),last=False)
            y_found, y_last_idx = index_recursive(all_factorizations,list(y),last=True)

            if x == y:
                ord_cache[tuple(x),tuple(y)] = 0

            if x_last_idx < y_first_idx:
                ord_cache[tuple(x),tuple(y)] = -1

            if y_last_idx < x_first_idx:
                ord_cache[tuple(x),tuple(y)] = 1

    for x, y in old_calls.keys():
        if (tuple(x),tuple(y)) in ord_cache:
            continue
        x_found, x_first_idx = index_recursive(all_factorizations,list(x),last=False)
        x_found, x_last_idx = index_recursive(all_factorizations,list(x),last=True)
        y_found, y_first_idx = index_recursive(all_factorizations,list(y),last=False)
        y_found, y_last_idx = index_recursive(all_factorizations,list(y),last=True)

        if not x_found and not y_found:
            break
        elif x == y:
            ord_cache[tuple(x),tuple(y)] = 0

        elif x_found and not y_found and x in finished:
            ord_cache[tuple(x),tuple(y)] = -1

        elif y_found and not x_found and y in finished:
            ord_cache[tuple(x),tuple(y)] = 1

        elif x_last_idx < y_first_idx and x in finished:
            ord_cache[tuple(x),tuple(y)] = -1

        elif y_last_idx < x_first_idx and y in finished:
            ord_cache[tuple(x),tuple(y)] = 1

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

def ranges_for_z_calculations(n, all_factorizations, finished, it_set):
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

    max_idx = collections.defaultdict(lambda: 0)
    min_idx = collections.defaultdict(lambda: 0)

    for y in it_set:
        for p in possible_primes:
            # For each prime, try to find some index x_idx s.t
            # [p,p]*all_factorizations[x_idx] > y.  Keep track of the maximum
            # of these.
            found_upper_bound = False

            for x_idx in range(0, len(all_factorizations)):
                all_lower = True
                for z in all_factorizations[x_idx]:
                    v = sorted([p,p] + z)
                    val = ord_absolute(v,y,all_factorizations,finished)

                    if val == 99:
                        # This factorization we are unsure about; possibly
                        # update our min_idx.
                        all_lower = False
                        t, o = simplify(y, sorted([p,p]+z))

                        t_found, t_idx = index_recursive(all_factorizations, t)
                        if not t_found or len(all_factorizations[t_idx])==1:
                            # t is not yet generated; so there isn't an index
                            # we can go into.  Just break here.  FixMe - Is
                            # this correct?
                            break

                        min_idx[y] = min(min_idx[y],t_idx)

                    elif val != 1:
                        all_lower = False
                        break
                if all_lower:
                    # There was at least one element in this index that was
                    # higher than y; record this index as a possible max

                    found_upper_bound = True
                    t, o = simplify(y, sorted([p,p]+z))
                    t_found, t_idx = index_recursive(all_factorizations, t, last=True)

                    # FixMe: Are these the correct indexes?  Why up to x_idx if
                    # we can't find t?  Or why t_idx if we can?
                    if y in max_idx:
                        if t_found:
                            max_idx[y] = max(max_idx[y],t_idx)
                        else:
                            max_idx[y] = max(max_idx[y],x_idx)

                    else:
                        if t_found:
                            max_idx[y] = max(max_idx[y],t_idx)
                        else:
                            max_idx[y] = max(max_idx[y],x_idx)
                    break

            if not found_upper_bound:
                # We couldn't find an a where [p*p*a] > y.  So we can't compute
                # Z - delete the record from max_idx.
                if y in max_idx:
                    del max_idx[y]
                if y in min_idx:
                    del min_idx[y]
                break

    return min_idx, max_idx

def analyze_z_for_factorizations(n, all_factorizations, finished, new_finished, min_idx, max_idx):
    """ Finds what factorizations we can eliminate at which places, based on analyzing Z(f). """

    eliminate = []
    # list of [index, factorization] pairs that we can get rid of

    calculated_keys = set()

    for y in max_idx:
        # Iterate through everything we found we could find a 1 value for.

        if y not in min_idx:
            # Doesn't give us anything.
            calculated_keys.add(y)
            continue

        # Populate e with every possibility in the range we're going through.
        # When we hit a possibility that works, we'll remove it from e.  The
        # ones that remain are what we can eliminate
        e = {}
        for x in range(min_idx[y],max_idx[y]+1):
            e[x] = copy.copy(all_factorizations[x])

        for x in generate_all_possible_lists(all_factorizations,
                                             min_idx[y],
                                             max_idx[y]+1):
            # For each possibility that we need to check, check a variety of
            # conditions for possibility.
            primes = [x[0] for x in x if len(x) == 1]

            moebius_of_y = 0 # FixMe: move this out into a function
            if len(set(y)) == len(y):
                moebius_of_y = int(math.pow(-1,len(y)))

            y = list(y)
            possible_z, idx = calculated_Z(y, primes, x)
            possible = True
            if possible_z == -1:
                # We can't figure everything out; just go ahead and delete our work
                # FixMe: This should be impossible
                e = {}
                break

            if ZIsPossible(possible_z,moebius_of_y) == -1:
                # If there is no n where Z(n) == possible_z with the correct
                # moebius, this is impossible.
                possible = False
            elif y in x and ZIsPossible(
                    possible_z,
                    moebius_of_y) < (x.index(y)+2):
                # If the largest possible N for which Z(n) == possible_z is
                # a lower position than where y is, then this is impossible
                possible = False
            elif y in x and possible_z != Z(x.index(y)+2):
                # If the Z we calculated doesn't match Z(n) for this, just
                # exit.
                possible = False
            if possible:
                # We couldn't rule out this possibility; update e
                for i in range(min_idx[tuple(y)],max_idx[tuple(y)]+1):
                    if x[i] in e[i]:
                        e[i].remove(x[i])
            if possible_z != -1:
                calculated_keys.add(tuple(y))

        #convert e to the idx, factorization pair
        for x in e:
           for z in e[x]:
               logger.info("  Eliminating [n=%d,%s] based on: %s " % (x+2,str(z),str(y)))
               eliminate += [[x, z]]
               assert z != factorize(x+2)
    logger.debug("  Elimination possibilities completed")

    return eliminate, calculated_keys



def all_eliminations(n, all_factorizations, finished, new_finished):
    """ Returns factorizations for positions we can show are impossible. """
    global logger

    min_idx, max_idx = ranges_for_z_calculations(n, all_factorizations, finished, new_finished)
    logger.debug("  Generated upper and lower bounds for Z")

    return analyze_z_for_factorizations(n, all_factorizations, finished, new_finished, min_idx, max_idx)


def generate_factorization_possibilities(max_n, start_n = 2, all_factorizations=[]):
    """ Generates the list of possible factorizations from start_n to max_n. """
    global logger, calls, ord_cache

    finished = set()
    # Set of factorizations that are 'finished', IE they will not be generated
    # as possibilities in any future iterations.  This can occur for two reasons:
    #
    #   1) Any arrangement of possible factorizations will have this factor.
    #      For example, both n=8 and n=9 generate (2,2,2) and (3,3) as their
    #      possibilities - so at this point, they will always be generated in
    #      some arrangement.
    #
    #   2) A larger number has been finished.  For example, (2,3,5) is finished
    #      once we isolate 36=(2,2,3,3).

    outstanding = set()
    # All the factorizations we have generated that are not finished.


    start = {0: 0, -1: 0, 1: 0}
    end = {0: 0, 1: 0, -1: 0}
    # For each moebius value, which parts of the possibilities list we need to
    # iterate over to generate all possible values.  This is a performance
    # enhancement.  For example, at n=6, we start with the array: [ [2], [3],
    # [2, 2], [5], [2,3]].  We know that next time we generate possibilities
    # for a moebius value of 1, we don't have to go past [2,5] - start will be
    # 0 and end will be 3.  Then, when we get to n=10 (the next n with a
    # moebius value of 0), we don't need to generate possibilities twice, even
    # though there are two possible factorization arrays.

    # FixMe: Start is not updated, so it's always 0.

    finished_for_n = {}
    outstanding_for_n = {}
    start_for_n = {}
    end_for_n = {}
    # Historical data - contans the values of finished/outstanding/start/end at the
    # beginning of processing each n.  Used to go backwards after eliminating
    # possiblities
    # FixMe - probably should create a class for all of these.

    z_calculated = set()
    # Set of factorizations where we have already analyzed Z(factorization) -
    # we don't have to do this again.

    eliminate = collections.defaultdict(list)
    # All the possibilities we have eliminated based on analyzing Z.

    blocked_potential_useful_z = {}
    # Contains information about factorizations we are interested in, but can't
    # always figure out - contains what comparison they are blocked on, so that
    # we can proceed once unblocked without recalculating the entire thing.

    logger.info("Program begin")

    n = start_n
    while n <= max_n:
        m = moebius(n)
        logger.info("Processing n=%d moebius=%d"%(n,m))

        finished_for_n[n] = copy.deepcopy(finished)
        outstanding_for_n[n] = copy.deepcopy(outstanding)
        start_for_n[n] = copy.copy(start)
        end_for_n[n] = copy.copy(end)

        new = []
        # The array containing all the new values we generate.

        s = start[m]
        e = end[m]

        end[m] = 0

        if e == -1:
            e = 0
        # Reset end so it can be set properly each iteration
        logger.debug("  possibility generation: start: %d end: %d"%(s,e))
        for factorizations in generate_all_possible_lists(all_factorizations,s,e):
            # Generate possibilities for each subset of the possibility tree
            # that matters
            new_ = generate_possibilities_for_factorization(
                n,
                m,
                factorizations,
                finished,
                all_factorizations,
                start,
                end)

            new_ = prune_elements_lt(new_, factorizations, all_factorizations,finished)
            # prune the ones that are more than all the other generated possibilities

            new += [x for x in new_ if x not in new and x not in eliminate[n-2]]
            # add all the new factorizations that remain that we have not
            # previously eliminated using z.


        logger.debug("  Initial possibilities: %s"%(str(new)))
        assert factorize(n) in new

        all_factorizations += [sorted(new)]

        # Update the outstanding and finished sets.  new_finished is the
        # outstanding factorizations that we finished at this n.
        outstanding, finished, new_finished = \
          update_outstanding_and_finished(all_factorizations, new, outstanding, finished)
        logger.debug("  outstanding processing finished: outstanding=%s new_finished=%s",outstanding,new_finished)

        # update the ord_cache used for the 'ord' function.
        old_calls = copy.copy(calls)
        calls.clear()
        update_ord_cache(ord_cache, all_factorizations, finished, old_calls)
        logger.debug("  Ord_cache updated")

        # Find all the Z that we can analyze now to prune branches.
        all_potential_useful_z = new_finished
        # all_potentially_useful_z(all_factorizations,
        #                                                   z_calculated,
        #                                                   blocked_potential_useful_z,
        #                                                   finished,
        #                                                   new_finished)

        logger.debug("  all_potentially_useful_z: %s"%all_potential_useful_z)

        if all_potential_useful_z:
            new_eliminate, new_z_calculated = all_eliminations(n, all_factorizations, finished, new_finished)
            z_calculated |= set(tupletized(new_z_calculated))

            if new_eliminate:
                # For all of our new elimination candidates, update
                # all_factorizations and reset to continue calculations from
                # the lowest point we changed

                min_ = None
                for x in new_eliminate:
                    if x[1] in all_factorizations[x[0]]:
                        all_factorizations[x[0]].remove(x[1])
                        if not min_:
                            min_ = x[0]
                        min_ = min(min_,x[0])
                        if [x[1]] not in eliminate[x[0]]:
                            eliminate[x[0]] += [x[1]]

                n = min_+2


                all_factorizations = all_factorizations[:min_]
                start = start_for_n[n]
                end = end_for_n[n]
                finished = finished_for_n[n]
                outstanding = outstanding_for_n[n]

                continue

        # End of the loop; update n
        n = n + 1

    return all_factorizations

if __name__ == "__main__":
    def main():
        setupLogger()
        f = generate_factorization_possibilities(int(sys.argv[1]))
        print(1, "[[1]]")
        for n in range(0, len(f)):
            print(n + 2, f[n])

    main()

# FixMe: Convert to using tuples everywhere
