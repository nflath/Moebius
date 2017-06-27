import math
import collections
import pdb
import copy
import cProfile
import sys
import itertools
from functools import reduce

def Z(n):
    return len([moebius(x) for x in range(1,n+1) if moebius(x) == 0])

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


# Question: Given 'finished', what Z-values can we calculate?

# First step:  Find the largest prime 'p' for which we know p*p > factors.
#  If we can't prove any, we can't solve it yet.

#  E.G. for 2 * 3 * 5, we need to be able to show 7 * 7 > 2 * 3 * 5.  As long
#  as we've factored up to 7, we're good here.

# For each prime lower than that, we need to be able to show some p * p * a > f.
# So we need to know [5 * 5] * a > 2 * 3 * 5,
#                    [3 * 3] * b > 2 * 3 * 5
#                    [2 * 2] * c > 2 * 3 * 5

# g = simplify(f)
#                    5 * a > 2 * 3
#                    3 * b > 2 * 5
#                    2 * c > 3 * 5

# For each p < max_p : we need to be able to show 'a' s.t
#          simplify[p*p*a] > simplify[f]

# So we are good as long as we have 'finished' max(simplify([p,p],f)) for all p
# < max_p (and we can find some max_p).

# So: Given 'finished', 'already_evaluated', 'primes' (where we've isolated all the primes... :()
# How do we determine what we can do?
#   - Anything in finished not in already_evaluated
#
# For each prime, keep track when we 'finish' a possibility for a * p * p.


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
            return -1, -1
        if [p,p] == f or val  <= 0:
            in_.add((p,p))
        else:
            break
        for x_idx in range(0,len(factorizations)):
            x = factorizations[x_idx]
            val = ord(sorted([p,p]+x), f, factorizations)
            if val == 99:
                return -1, -1
            if sorted([p,p]+x) == f or val <= 0:
                max_idx = max(max_idx, x_idx)
                in_.add(tuple(sorted([p,p]+x)))
            else:
                break
    return len(in_), max_idx


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
                return
        yield retn
    else:
        for x in lst[idx]:
            if x in retn[:idx]:
                continue
            retn[idx] = x
            for y in generate_all_possible_lists(lst, finished, idx + 1, retn):

                yield y


def partition(s, factorizations):
    """Partitions the set of factorizations 's' into  equal groupings.

    For example, [2,2,2,3] and [3,3,3] will be grouped together while
    [2,2,2] and [3,3] have not been disambiguated.  An 'equal group' is
    one where no element is less than another element.
    """

    r = []
    for x in s:
        if x in r:
            continue
        r_ = [x]
        for y in s:
            if x == y:
                continue

            if y in r:
                continue

            if ord(x, y, factorizations) != -1 and \
              ord(y, x, factorizations) != -1:
                r_ += [y]
        r += [r_]
    return r



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

    # t, o = simplify(t, o)

    # IF either t or o are eliminated, one is larger than the other(or both
    # are equal).
    if not t and not o:
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


def lt(this, other, factorizations):
    """Returns if we can show this < every element in other (aside itself).

    This is a set of possible factorizations, and other is a set of
    sets.  We need to make sure that, for each set in other, at least
    one factorization of this is less than one of the factorizations in
    other.
    """

    # FixMe: Is this correct? Or should *all* elements be < all elements in other?

    for other_set in other:

        if other_set is this:
            continue

        lt_ = False
        for other_element in other_set:
            if lt_:
                break;
            for this_element in this:
                if lt_:
                    break
                if ord(this_element, other_element, factorizations) == -1:
                    lt_ = True
                    break
        if not lt_:
            return False

    return True


def ord(this, other, factorizations):
    """Returns whether this < other in a more complicated way.

    Check each permutation and 2-way split of this and other to try and
    find one where both parts of this are less than the parts of
    other.

    Returns -1 if t < 0, 0 if t == 0, 1 if t > o, 99 if unknown
    """
    t, o = simplify(this, other)
    if not t and o:
        return -1
    elif not o and t:
        return 1
    if not t and not o:
        return 0

    # FixMe: We only need sorted combinations.  So this duplicates work.
    # FixMe: Can we potentially not call simplify() in the ordno_permutation?
    # They should already be simplified.
    # FixMe: This is going to have to change to return lt, gt, eq, or unknown

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

                    if t_tmp_begin and t_tmp_end and o_tmp_begin and o_tmp_end:
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
                    elif t_tmp_end and o_tmp_end and not t_tmp_begin and not o_tmp_begin:
                        val = ord_no_permutation(t_tmp_end, o_tmp_end, factorizations)
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
      if not isinstance(args, collections.Hashable):
         # uncacheable. a list, for instance.
         # better to not cache than blow up.
         return self.func(*args)
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
        return [], smallest, False

    # Just find what index f is in the factorizations list
    #idx__ = factorizations.index(f)

    if possibility in factorizations:
        # We've already found this.  Keep searching.
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
                return [], smallest,  True

        for i in factorizations:
            if ord(possibility,i,factorizations) == -1:
                return [], smallest, False

    return possibility, f, True


def new_repeated_prime_factorizations(n, primes, factorizations):
    """Return the possibilities for factorizaiton of n whose factorizations contain a repeated prime number.

    For each prime, loop through the factorizations of each n, and see
    if we can get a possibility for that pair.  Once you find a
    possibility for one factorization, you don't need to go further than
    that factorization for the later primes.
    """

    r = []
    smallest = None

    for p in primes:
        for f in factorizations:
            break_ = False

            if smallest is not None and f == smallest:
                break

            r_, smallest, break_ = one_repeated_prime_factor(
                n, factorizations, p, f, smallest)

            if r_ and r_ not in r:
                r += [r_]
            break_ |= break_

            if break_:
                break

    return r

def generate_factorization_possibilities(max_n, start_n = 2, all_factorizations=[]):
    """ Generates the list of factorization possibilities up to max_n """
    finished = set()
    outstanding = set()
    z_calculated = set()
    eliminate = collections.defaultdict(list)

    n = start_n
    while n <= max_n:
        new = []
        real_z = Z(n)
        possible = []
        outstanding_count = collections.defaultdict(lambda : 0)
        total = 0
        for factorizations in generate_all_possible_lists(all_factorizations,finished):
            # Attempt every possible factorization and generate all possibilities
            total += 1

            primes = [x[0] for x in factorizations if len(x) == 1]
            m = moebius(n)
            new_ = []
            if m == -1:
                new_ = new_unique_prime_factorizations(
                    n, 1, primes, factorizations)
            elif m == 0:
                new_ = new_repeated_prime_factorizations(
                    n, primes, factorizations)
            elif m == 1:
                new_ = new_unique_prime_factorizations(
                    n, 2, primes, factorizations)
            else:
                assert False

            if len(new_) > 1:
                # Do some pruning.  Check if any of the possibilities are less
                # than all the other possibilities in the list; if so, only
                # keep it.
                save = new_
                x = partition(new_, factorizations)
                for p in x:
                    if lt(p, x, factorizations):
                        save = p
                        lt(p, x, factorizations)
                new_ = save

            for f in outstanding:
                # Check if the factorization 'f' is finished.  See if 'f' is in
                # this factorization possibility; keep a count for each
                # outstanding possibility.

                # FixMe: Really, we just have to add outstanding elements to a
                # set if they are not in factorizations.
                if list(f) in factorizations:
                    outstanding_count[f] += 1
                else:
                    if not new_:
                        outstanding_count[f] += 1
                    for y in new_:
                        if ord(list(f),y,factorizations) == -1:
                            outstanding_count[x] += 1

            for x in new_:
                # Add all the new factorizations that remain that we have not
                # previously eliminated using Z.
                if x not in new and x not in eliminate[n-2]:
                    new += [x]

        # Update the finished and outstanding sets.
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


        # Working
        all_confusions = set()
        for x in all_factorizations:
            if len(x) == 1:
                continue
            else:
                allFinished = True
                factors = []
                for y in x:
                    if tuple(y) not in finished:
                        allFinished = False
                        break
                    else:
                        factors += y
                if allFinished:
                    all_confusions.add(tuple(sorted(tuple(factors))))

        all_potential_useful_Z = set()
        for x in all_confusions:
            for y in range(1,len(x)):
                for z in itertools.combinations(x,y):
                    if z not in z_calculated:
                        all_potential_useful_Z.add(z)

        for x in generate_all_possible_lists(all_factorizations,finished):
            primes = [x[0] for x in factorizations if len(x) == 1]
            all_potential_useful_Z2 = copy.copy(all_potential_useful_Z)
            for y in all_potential_useful_Z2:
                possible_z, idx = calculated_Z(list(y), primes, x)
                if possible_z == -1:
                    #if n == 22 and list(y)==[2,3,7]: pdb.set_trace()
                    possible_z, idx = calculated_Z(list(y), primes, x)
                    all_potential_useful_Z.remove(y)

        if new_finished or all_potential_useful_Z:
            # If we've finished anything new, go ahead and try to eliminate
            # possibilities based on Z.

            e = copy.deepcopy(all_factorizations)
            # List of impossible possibilities

            for x in generate_all_possible_lists(all_factorizations,finished):
                # For every possible list of factorizations, calculated
                # Z(finished) and ensure that the Z value matches what we
                # expect.
                possible = True
                primes = [x[0] for x in x if len(x) == 1]

#                if x == [[2], [3], [2, 2], [5], [2, 3], [7], [2, 2, 2], [3, 3], [2, 5], [11], [2, 2, 3], [13], [2, 7], [3, 5], [2, 2, 2, 2], [17], [2, 3, 3], [19], [2, 2, 5], [3, 7], [2, 11], [23]]:
                    #pdb.set_trace()

                for y in new_finished | all_potential_useful_Z:
                    moebius_of_y = 0
                    if len(set(y)) == len(y):
                        moebius_of_y = math.pow(-1,len(y))
                    y = list(y)
                    possible_z, idx = calculated_Z(y, primes, x)
                    if possible_z == -1:
                        continue
                        # This may not be good; don't use this information
                        assert tuple(y) not in new_finished
                    if tuple(y) not in new_finished and ZIsPossible(
                            possible_z,
                            moebius_of_y) < len(x):
                        ZIsPossible(
                            possible_z,
                            moebius_of_y)
                        possible = False
                        break
                    if tuple(y) in new_finished and y not in x:
                        possible = False
                        break
                    if y in x and possible_z != Z(x.index(y)+2):
                        possible = False
                        break
                if possible:
                    # This is a possible factorization; make sure we're not
                    # eliminating anything in it.
                    #if n == 23: pdb.set_trace()
                    for y in range(0,len(x)):
                        if x[y] in e[y]:
                            e[y].remove(x[y])

            z_calculated |= new_finished
            z_calculated |= all_potential_useful_Z
            new_eliminate = []

            for x in range(0,len(e)):
                for y in e[x]:
                    new_eliminate += [[x, y]]

            if new_eliminate:
                # For all of our new elimination, update all_factorizations and
                # reset to calculate from the lowert point.

                min_ = None
                for x in new_eliminate:
                    all_factorizations[x[0]].remove(x[1])
                    if not min_:
                        min_ = x[0]
                    min_ = min(min_,x[0])
                    if [x[1]] not in eliminate[x[0]]:
                        eliminate[x[0]] += [x[1]]
                print('n=',n,'eliminating: ',new_eliminate,'resetting to:',min_+3)
                n = min_+3
                all_factorizations = all_factorizations[:min_+1]


                finished = set()
                outstanding = set()

                continue
        n = n + 1

    return all_factorizations

if __name__ == "__main__":
    def main():
        # FixMe: Add tests

        f = generate_factorization_possibilities(int(sys.argv[1]))
        print(1, "[[1]]")
        for n in range(0, len(f)):
            print(n + 2, f[n])

    cProfile.run('main()',sort='tottime')
    #main()
