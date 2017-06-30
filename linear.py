import math
import collections
import pdb
import copy
import cProfile
import sys
import itertools
from functools import reduce

# Naming conventions:
# all_factorizations is the list where all_factorizations[n] contains all possibilities
# factorizations is one set of factorizations where factorizations[n] contains one possibility
# f is a single factorization

import logging
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

def tupletized(l):
    return tuple([tuple(x) for x in l])

def calculated_Z(f, primes, factorizations):
    """Calculates Z(f).

    For each prime 'p', counts the number of factorizations 'a' where
    p*p*a <= f.  Returns the total number of cases this is true for.
    """
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


def generate_all_possible_lists(lst, finished, idx=0, retn=[]):
    """ Yields each possible list, where each index in lst is a list of possibilities.

    The same possibility cannot be chose more than once."""
    if lst == []:
        yield lst
    elif not retn:
        retn = copy.deepcopy(lst)
        for y in generate_all_possible_lists(lst, finished, 0, retn):
            yield y
    elif idx == len(lst):
        for x in finished:
            if list(x) not in retn:
                real = [[2], [3], [2, 2], [5], [2, 3], [7], [2, 2, 2], [3, 3], [2, 5], [11], [2, 2, 3], [13], [2, 7], [3, 5], [2, 2, 2, 2], [17], [2, 3, 3], [19], [2, 2, 5], [3, 7], [2, 11], [23], [2, 2, 2, 3], [5, 5], [2, 13], [3, 3, 3], [2, 2, 7], [29], [2, 3, 5], [31], [2, 2, 2, 2, 2], [3, 11], [2, 17], [5, 7], [2, 2, 3, 3], [37], [2, 19], [3, 13], [2, 2, 2, 5], [41], [2, 3, 7], [43], [2, 2, 11], [3, 3, 5], [2, 23], [47], [2, 2, 2, 2, 3], [7, 7]]
                if retn == real: pdb.set_trace()
                return

        yield retn
    else:
        for x in lst[idx]:
            if x in retn[:idx]:
                continue
            retn[idx] = x
            for y in generate_all_possible_lists(lst, finished, idx + 1, retn):
                yield y


def simplify(this, other):
    """ Remove all common factors in this and other.

    For example, (2,2,2,2) and (2,2,5) simplifies to (2,2) and (5)."""
    t_i = 0
    o_i = 0
    t = []
    o = []
    while(t_i < len(this) and o_i < len(other)):
        if this[t_i] < other[o_i]:
            t.append(this[t_i])
            t_i += 1
        elif this[t_i] > other[o_i]:
            o.append(other[o_i])
            o_i += 1
        elif(this[t_i] == other[o_i]):
            t_i += 1
            o_i += 1
    if t_i < len(this):
        t += this[t_i:]
    if o_i < len(other):
        o += other[o_i:]
    return t, o


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
    global cache
    if (tuple(t), tuple(o)) in cache:
        return cache[tuple(t), tuple(o)]

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
cache = {}
cache_hits = 0
ord_calls = 0

def ord(this, other, factorizations):
    """Returns whether this < other in a more complicated way.

    Check each permutation and 2-way split of this and other to try and
    find one where both parts of this are less than the parts of
    other.

    Returns -1 if t < 0, 0 if t == 0, 1 if t > o, 99 if unknown
    """
    global cache, cache_hits, ord_calls, calls

    ord_calls += 1
    if (tuple(this),tuple(other),) in cache:
        cache_hits += 1
        return cache[(tuple(this),tuple(other),)]

    t, o = simplify(this, other)

    if not t and o:
        return -1
    elif not o and t:
        return 1
    if not t and not o:
        return 0

    if (tuple(t),tuple(o),) in cache:
        cache_hits += 1
        return cache[(tuple(t),tuple(o),)]

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


class memoized(object):
   '''Decorator. Caches a function's return value each time it is called.
   If called later with the same arguments, the cached value is returned
   (not reevaluated).
   '''
   def __init__(self, func):
      self.func = func
      self.cache = {}
   def __call__(self, *args):
      if args in self.cache:
         return self.cache[args]
      else:
         value = self.func(*args)
         self.cache[args] = value
         return value
   def __repr__(self):
      '''Return the function's docstring.'''
      return self.func.__doc__
   def __get__(self, obj, objtype):
      '''Support instance methods.'''
      return functools.partial(self.__call__, obj)

@memoized
def Z(n):
    return len([moebius(x) for x in range(1,n+1) if moebius(x) == 0])

@memoized
def ZIsPossible(z, m):
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
    return math.pow(-1, len(f))


def one_unique_prime_factorization(n, factorizations, potential, p, smallest):
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
    if possibility in factorizations:
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


        if other not in factorizations:
            return [], smallest, True

        for i in range(0, factorizations.index(other)):
            if sorted([prime] + factorizations[i]) not in factorizations:
                return [], smallest, True

    for i in factorizations:
        if ord(possibility,i,factorizations) == -1:
            return [], smallest, False

    return [possibility], smallest, True

new_unique_prime_factorizations_for_length_cache = {}
def new_unique_prime_factorizations_for_length(n, length, primes, factorizations):
    """Return all potential prime factorizations for n of the given length.

    Find all current factorizations of length l-1.  For each of them,
    find the lowest prime that when multiplied by the factorization is
    not in the list.  Once you find one possibility, you do not need to
    go past that prime for future cases.
    """

    if length == 1:
        # If the length is 1, the only possibility is that n is a prime.
        return [[n]]

    result = []

    # r is the list of all factorizations that have length one less that our
    # search.
    r = [x for x in factorizations if len(x) == length - 1]
    # FixMe: Do we need to just walk though all factorizations period -
    # otherwise we may add too much - IE, if we are searching for a
    # factorization of length 4, and we have a*b < c*d*e, and a*b is not in our
    # current list of factorizations, we don't want to skip it - we want to
    # stop the search.  But this will at worst add more than we need, so a
    # performance issue.

    smallest = None
    added = False

    for potential in r:
        x = potential
        added = False
        for p in primes:
            # FixMe: Early-exit using smallest in this function.

            n_, smallest, break_ = one_unique_prime_factorization(
                n, factorizations, potential, p, smallest)
            for x in n_:
                if x not in result:
                    result += [x]
            if break_:
                break
    return result


def new_unique_prime_factorizations(n, start_length, primes, factorizations):
    """Returns all prime factorizations with no duplicated primes with either even or odd number of factors.

    Find all possibilities of size start_length, then start_length+2,
    start_length+4, ... until possibilities are no longer generated.
    """
    length = start_length
    possibilities = new_unique_prime_factorizations_for_length(
        n, length, primes, factorizations)
    result = []
    while possibilities:
        result += possibilities
        length += 2
        possibilities = new_unique_prime_factorizations_for_length(
            n, length, primes, factorizations)
    return result


def one_repeated_prime_factor(n, factorizations, p, f, smallest):
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
    #idx__ = factorizations.index(f)

    if possibility in factorizations:
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


        if other not in factorizations:
            return None, f, True

        for i in range(0, factorizations.index(other)):
            if sorted([prime] + factorizations[i]) not in factorizations:
                return None, f,  True

        for i in factorizations:
            if ord(possibility,i,factorizations) == -1:
                return None, f, True

    return possibility, f, True


new_repeated_prime_factorizations_cache = {}
def new_repeated_prime_factorizations(n, primes, factorizations):
    """Return the possibilities for factorizaiton of n whose factorizations contain a repeated prime number.

    For each prime, loop through the factorizations of each n, and see
    if we can get a possibility for that pair.  Once you find a
    possibility for one factorization, you don't need to go further than
    that factorization for the later primes.
    """
    r = []
    smallest = None
    cached_starts = {}
    tpl = tupletized(factorizations)
    if tpl[:-1] in new_repeated_prime_factorizations_cache:
        cached_starts = new_repeated_prime_factorizations_cache[tpl[:-1]]
    new_cached_starts = {}
    for p in primes:

        start = 0
        if p in cached_starts:
            start = cached_starts[p]

        for f_idx in range(start, len(factorizations)):
            f = factorizations[f_idx]
            break_ = False

            if smallest is not None and f == smallest:
                new_cached_starts[p] = f_idx
                break

            r_, smallest, break_ = one_repeated_prime_factor(
                n, factorizations, p, f, smallest)

            if r_ and r_ not in r:
                r += [r_]
            break_ |= break_

            if break_:
                new_cached_starts[p] = f_idx
                break
    new_repeated_prime_factorizations_cache[tpl] = new_cached_starts
    return r

def prune_elements_lt(factorizations, factorization):
    keep = []
    for x in range(0, len(factorizations)):
        found_lt = false
        for y in range(x+1, len(factorizations)):
            if ord(factorizations[x],
                   factorizations[y],
                   factorizations) == 1:
                found_lt = true
                break
        if not found_lt:
            keep += [factorizations[x]]
    return keep

def generate_possibilities_for_factorization(n, m, primes, factorizations):
    if m == -1:
        return new_unique_prime_factorizations(
            n, 1, primes, factorizations)
    elif m == 0:
        return new_repeated_prime_factorizations(
            n,
            primes,
            factorizations)
    elif m == 1:
        return new_unique_prime_factorizations(
            n, 2, primes, factorizations)
    else:
        assert false

def index_recursive(lst, elt, last=false):
    """find elt in list of lists lst

    returns whether or not the element was found, and the index of the
    list it was found in.  if last is set, returns the last index of the
    list it was found in.
    """
    for l in lst:
        for e in l:
            if e == elt:
                if not last:
                    return true, lst.index(l)
                f, i = index_recursive(lst[lst.index(l)+1:],elt,last)
                if f:
                    return true, i + lst.index(l) + 1
                return true, lst.index(l)

    return false, 0

def update_cache(cache, all_factorizations, finished, old_calls):
    for x in finished:
        for y in finished:
            if (tuple(x),tuple(y)) in cache:
                continue
            x_found, x_first_idx = index_recursive(all_factorizations,list(x),last=false)
            x_found, x_last_idx = index_recursive(all_factorizations,list(x),last=true)
            y_found, y_first_idx = index_recursive(all_factorizations,list(y),last=false)
            y_found, y_last_idx = index_recursive(all_factorizations,list(y),last=true)

            if x == y:
                cache[tuple(x),tuple(y)] = 0

            if x_last_idx < y_first_idx:
                cache[tuple(x),tuple(y)] = -1

            if y_last_idx < x_first_idx:
                cache[tuple(x),tuple(y)] = 1

    for x, y in old_calls.keys():
        if (tuple(x),tuple(y)) in cache:
            continue
        x_found, x_first_idx = index_recursive(all_factorizations,list(x),last=false)
        x_found, x_last_idx = index_recursive(all_factorizations,list(x),last=true)
        y_found, y_first_idx = index_recursive(all_factorizations,list(y),last=false)
        y_found, y_last_idx = index_recursive(all_factorizations,list(y),last=true)

        if not x_found and not y_found:
            break
        elif x == y:
            cache[tuple(x),tuple(y)] = 0

        elif x_found and not y_found and x in finished:
            cache[tuple(x),tuple(y)] = -1

        elif y_found and not x_found and y in finished:
            cache[tuple(x),tuple(y)] = 1

        elif x_last_idx < y_first_idx and x in finished:
            cache[tuple(x),tuple(y)] = -1

        elif y_last_idx < x_first_idx and y in finished:
            cache[tuple(x),tuple(y)] = 1

def all_potentially_useful_z(all_factorizations, z_calculated, blocked_potential_useful_z,finished):
    all_confusions = set()
    for x in all_factorizations:
        if len(x) == 1:
            continue
        else:
            allfinished = true
            factors = []
            for y in x:
                if tuple(y) not in finished:
                    allfinished = false
                    break
                else:
                    factors += y
            if allfinished:
                all_confusions.add(tuple(sorted(tuple(factors))))

    all_potential_useful_z = set()
    for x in all_confusions:
        for y in range(1,len(x)):
            for z in itertools.combinations(x,y):
                if z not in z_calculated:
                    all_potential_useful_z.add(z)


    for x in generate_all_possible_lists(all_factorizations,finished):
        primes = [x[0] for x in x if len(x) == 1]
        all_potential_useful_z2 = copy.copy(all_potential_useful_z)
        for y in all_potential_useful_z2:

            if y in blocked_potential_useful_z:
              if ord(y, blocked_potential_useful_z[y][0], blocked_potential_useful_z[y][1]) == 99:
                    break
              del blocked_potential_useful_z[y]

            possible_z, possibility = calculated_z(list(y), primes, x)
            if possible_z == -1:
                all_potential_useful_z.remove(y)
                blocked_potential_useful_z[y] = possibility

    return all_potential_useful_z

def all_eliminations(all_factorizations, finished, it_set, new_finished):
    e = copy.deepcopy(all_factorizations)
    for x in generate_all_possible_lists(all_factorizations,finished):
        # for every possible list of factorizations, calculated
        # z(finished) and ensure that the z value matches what we
        # expect.
        possible = true
        primes = [x[0] for x in x if len(x) == 1]
        keep = []

        for y in it_set:
            moebius_of_y = 0
            if len(set(y)) == len(y):
                moebius_of_y = math.pow(-1,len(y))
            y = list(y)
            possible_z, idx = calculated_z(y, primes, x)
            if possible_z == -1:
                continue
                # this may not be good; don't use this information
            else:
                keep += [y]

            if tuple(y) in new_finished and y not in x:
                assert false
            if tuple(y) not in new_finished and zispossible(
                    possible_z,
                    moebius_of_y) < len(x):
                possible = false
                break
            if y in x and possible_z != z(x.index(y)+2):
                possible = false
                break

        it_set = keep
        if possible:
            # this is a possible factorization; make sure we're not
            # eliminating anything in it.
            for y in range(0,len(x)):
                if x[y] in e[y]:
                    e[y].remove(x[y])
    return e


def generate_factorization_possibilities(max_n, start_n = 2, all_factorizations=[]):
    """ generates the list of factorization possibilities up to max_n """
    global logger, calls
    finished = set()
    finished_for_n = {}
    outstanding = set()
    z_calculated = set()
    eliminate = collections.defaultdict(list)
    blocked_potential_useful_z = {}
    logger.info("start")
    all_factorizations_master = []

    n = start_n
    while n <= max_n:
        finished_for_n[n] = copy.deepcopy(finished)
        logger.info("processing n=%d"%n)
        new = []
        real_z = z(n)
        possible = []
        outstanding_count = collections.defaultdict(lambda : 0)
        total = 0
        failed = 0
        m = moebius(n)
        for factorizations in generate_all_possible_lists(all_factorizations,finished):
            # attempt every possible factorization and generate all possibilities
            total += 1
            primes = [x[0] for x in factorizations if len(x) == 1]

            new_ = generate_possibilities_for_factorization(n,m,primes,factorizations)
            new_ = prune_elements_lt(new_, factorizations)

            for f in outstanding:
                # check if the factorization 'f' is finished.  see if 'f' is in
                # this factorization possibility; keep a count for each
                # outstanding possibility.

                # fixme: really, we just have to add outstanding elements to a
                # set if they are not in factorizations.
                if list(f) in factorizations:
                    outstanding_count[f] += 1
                else:
                    if not new_:
                        # invalid generation - can we figure out how to skip it next time?
                        failed += 1
                        outstanding_count[f] += 1
                    for y in new_:
                        lt_all = True
                        if ord(list(f),y,factorizations) >= 0:
                            lt_all = False
                            break
                        if lt_all:
                            outstanding_count[f] += 1

            for x in new_:
                # add all the new factorizations that remain that we have not
                # previously eliminated using z.
                if x not in new and x not in eliminate[n-2]:
                    new += [x]
        logger.debug("initial possibilities: %s"%(str(new)))
        logger.debug("total: %d failed: %d"%(total,failed))

        # update the finished and outstanding sets.
        new_outstanding = set()
        new_finished = set()
        for x in outstanding:
            if outstanding_count[x] == total:
                new_finished.add(x)
            else:
                new_outstanding.add(x)
        outstanding = new_outstanding

        if len(new)==1:
            new_finished |= set((tuple(new[0]),))
        else:
            for x in new:
                if tuple(x) not in outstanding and \
                  tuple(x) not in finished:
                    outstanding |= set(((tuple(x)),))

        all_factorizations += [sorted(new)]
        finished |= new_finished

        old_calls = copy.copy(calls)
        calls.clear()

        global cache
        update_cache(cache, all_factorizations, finished, old_calls)
        all_potential_useful_z = all_potentially_useful_z(all_factorizations,
                                                          z_calculated,
                                                          blocked_potential_useful_z,
                                                          finished)

        logger.debug("new_finished: %s"%new_finished)
        logger.debug("all_potentially_useful_z: %s"%all_potential_useful_z)

        it_set = new_finished | all_potential_useful_z
        e = all_eliminations(all_factorizations, finished, it_set, new_finished)

        z_calculated |= new_finished
        z_calculated |= all_potential_useful_z
        new_eliminate = []

        for x in range(0,len(e)):
            for y in e[x]:
                new_eliminate += [[x, y]]
                if y == factorize(x+2):
                    pdb.set_trace()

        if new_eliminate:
            # for all of our new elimination, update all_factorizations and
            # reset to calculate from the lowert point.

            min_ = none
            for x in new_eliminate:
                all_factorizations[x[0]].remove(x[1])
                if not min_:
                    min_ = x[0]
                min_ = min(min_,x[0])
                if [x[1]] not in eliminate[x[0]]:
                    eliminate[x[0]] += [x[1]]
            logger.log
            print('n=',n,'eliminating: ',new_eliminate,'resetting to:',min_+2)
            n = min_+2
            all_factorizations = all_factorizations[:min_]
            # new_repeated_prime_factorizations_cache = {}
            finished = finished_for_n[n]
            outstanding = set()

            continue
        n = n + 1

    return all_factorizations

if __name__ == "__main__":
    def main():
        f = generate_factorization_possibilities(int(sys.argv[1]))
        print(1, "[[1]]")
        for n in range(0, len(f)):
            print(n + 2, f[n])

        global cache_hits, ord_calls
        print(cache_hits, ord_calls)
        print(Z(56))

    main()

all_factorizations = [[[2]], [[3]], [[2, 2]], [[5]], [[2, 3]], [[7]], [[2, 2, 2]], [[3, 3]], [[2, 5]], [[11]], [[2, 2, 3]], [[13]], [[2, 7]], [[3, 5]], [[2, 2, 2, 2]], [[17]], [[2, 3, 3]], [[19]], [[2, 2, 5]], [[3, 7]], [[2, 11]], [[23]], [[5, 5]], [[2, 2, 2, 3]], [[2, 13]], [[3, 3, 3]], [[2, 2, 7]], [[29]], [[2, 3, 5], [30]], [[2, 3, 5], [31]], [[2, 2, 2, 2, 2]], [[2, 17], [3, 11], [5, 7]], [[2, 17], [3, 11], [5, 7]], [[2, 17], [3, 11], [5, 7]], [[2, 2, 3, 3]], [[37]], [[2, 19], [3, 13]], [[2, 19], [3, 13]], [[2, 2, 2, 5]], [[2, 3, 7], [41]], [[2, 3, 7], [42]], [[2, 3, 7], [43]], [[2, 2, 11], [3, 3, 5], [7, 7]], [[2, 2, 11], [3, 3, 5], [7, 7]], [[2, 23]], [[47]], [[2, 5, 5], [3, 3, 5], [7, 7]], [[2, 5, 5], [7, 7]], [[2, 2, 13]], [[3, 17]]]
finished = {(2, 2, 5), (23,), (11,), (3, 7), (2, 5), (13,), (3, 3), (2, 2, 2, 2), (2, 3, 3), (3,), (5,), (2, 2), (7,), (2, 3), (2, 2, 3), (3, 5), (2, 7), (2, 2, 2), (2,), (2, 11), (17,), (19,)}
outstanding = ()

n = 24
