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

def calculated_Z(f, primes, factorizations):
    # Z = 2*3*5
    #print(factorizations)
    count = 0
    max_idx = 0
    in_ = set()
    #if f == [2,2]: pdb.set_trace()
    for p in primes:
        #2 * 2 * a

        if [p,p] == f or lt_one_([p,p], f, factorizations):
            in_.add((p,p))
        for x in factorizations:
            if sorted([p,p]+x) == f or lt_one_(sorted([p,p]+x), f, factorizations):
                max_idx = max(max_idx, factorizations.index(x))
                in_.add(tuple(sorted([p,p]+x)))
            else:
                break
    return len(in_), max_idx


def generate_all_possible_lists(lst, idx=0, retn=[]):
    """ Yields each possible list, where each index in lst is a list of possibilities.

    The same possibility cannot be chose more than once."""

    if not lst:
        yield lst
    elif not retn:
        retn = copy.deepcopy(lst)
        for y in generate_all_possible_lists(lst, 0, retn):
            yield y
    elif idx == len(lst):
        yield retn
    else:
        for x in lst[idx]:
            if x in retn[:idx]:
                continue
            retn[idx] = x
            for y in generate_all_possible_lists(lst, idx + 1, retn):
                yield y#copy.deepcopy(y)


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

            if not lt_one_(x, y, factorizations) and \
                    not lt_one_(y, x, factorizations):
                r_ += [y]
        r += [r_]
    return r


def simplify(this, other):
    """ Remove all common factors in this and other.

    For example, (2,2,2,2) and (2,2,5) simplifies to (2,2) and (5)."""
    i = 0
    while i < len(this):
        changed = False
        while i < len(this) and this[i] in other:
            changed = True
            index = other.index(this[i])
            this = this[:i] + this[i + 1:]
            other = other[:index] + other[index + 1:]
        if not changed:
            i = i + 1
    return this, other


def lt_one(t_, o_, factorizations):
    """Returns whether we can show t < o or not just based on the given factorization.

    Returns 0 if t < o, -1 if o > t, 1 if we don't know.
    """

    # FixMe: Change to just return True/False

    t, o = simplify(t_, o_)

    # IF either t or o are eliminated, one is larger than the other(or both
    # are equal).
    if not t and not o:
        return 1
    if not t:
        return 0
    if not o:
        return -1

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
        return 0
    if o_found and not t_found:
        return 1
    if t_found and t_index < o_index:
        # If both are found and t is earlier than o, t < o
        return 0
    if o_found and o_index < t_index:
        return 1

    return -1


def lt(this, other, factorizations):
    """Returns if we can show this < every element in other (aside itself).

    This is a set of possible factorizations, and other is a set of
    sets.  We need to make sure that, for each set in other, at least
    one factorization of this is less than one of the factorizations in
    other.
    """

    # FixMe: Is this correct? Or should *all* elements be < all other elements?

    for other_set in other:

        if other_set is this:
            continue
        lt_ = False
        for other_element in other_set:
            if lt_:
                continue
            for this_element in this:
                if lt_:
                    continue
                if lt_one_(this_element, other_element, factorizations):
                    lt_ = True
        if not lt_:
            return False

    return True


def lt_one_(this, other, factorizations):
    """Returns whether this < other in a more complicated way.

    Check each permutation and 2-way split of this and other to try and find one where both parts of this are less than the parts of other.
    """

    # FixMe: Does duplicated work, and additionally I'm not sure this is
    # exactly the way?  We may need to traverse down the list of
    t, o = simplify(this, other)
    if not t and o:
        return True
    elif not o and t:
        return False

    for t_begin_len in range(0, len(t)):
        for o_begin_len in range(0, len(o)):
            for t_tmp_begin in itertools.combinations(t, t_begin_len):
                for o_tmp_begin in itertools.combinations(o, o_begin_len):

                    t_tmp_begin = sorted(list(t_tmp_begin))
                    o_tmp_begin = sorted(list(o_tmp_begin))

                    o_tmp_end = copy.copy(o)
                    t_tmp_end = copy.copy(t)

                    for x in t_tmp_begin:
                        t_tmp_end.remove(x)

                    for x in o_tmp_begin:
                        o_tmp_end.remove(x)

                    if t_tmp_begin and t_tmp_end and o_tmp_begin and o_tmp_end:
                        begin_val = lt_one(t_tmp_begin, o_tmp_begin, factorizations)
                        end_val = lt_one(t_tmp_end, o_tmp_end, factorizations)
                        if begin_val == 0 and end_val == 0:
                            return True
                        #elif begin_val ==1 and end_val == 1:
                            #return False
                        #return False

                    elif t_tmp_begin and o_tmp_begin and not t_tmp_end and not o_tmp_end:
                        if lt_one(t_tmp_begin, o_tmp_begin, factorizations) == 0:
                            return True
                    elif t_tmp_end and o_tmp_end and not t_tmp_begin and not o_tmp_begin:
                        if lt_one(t_tmp_end, o_tmp_end, factorizations) == 0:
                            return True

    return False


def factorize(n):
    """Returns the factorization of n"""
    # FixMe: This is unnecessary in some cases - if we already have a duplicate
    #  factor we can early return, we dn't need to actually keep track of the
    #  factors
    # FixMe: memoize

    assert n > 1
    factors = []
    for i in range(2, n + 1):
        while (n % i) == 0:
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
    return math.pow(-1, len(f))


def one_unique_prime_factorization(n, primes, factorizations, potential, p, smallest):
    """ Returns the possible factorizations of n with no repeated factors.

    'p' is the prime to use and 'potential' is the factorization we are extending, so
    """
    # FixMe: This and one_repeated_prime_factorization are similar.  Merge if possible.
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


    # Go through all factorizations before 'potential' and ensure that no
    # factorization * p is lower than potential * p but doesn't exist.

    #if possibility == [2,3,7] and [2,3,5] in factorizations: pdb.set_trace()
    for i in range(0, len(possibility)):
        other = possibility[:i] + possibility[i + 1:]
        prime = possibility[i]

        if other not in factorizations:
            return [], smallest, True

        for i in range(0, factorizations.index(other)):
            if sorted([prime] + factorizations[i]) not in factorizations:
                return [], smallest, True

    for i in factorizations:
        if lt_one_(possibility,i,factorizations):
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
    # stop the search.  But this will at worst add more than we need

    smallest = None
    added = False

    for potential in r:
        x = potential
        added = False
        for p in primes:
            # FixMe: Early-exit using smallest in this function.  This
            # prevents updates to smallest from occuring in the middle of
            # iterating throught two 'equal' primes.

            n_, smallest, break_ = one_unique_prime_factorization(
                n, primes, factorizations, potential, p, smallest)
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


def one_repeated_prime_factor(n, factorizations, p, f, smallest_factorization_idx):
    """ Returns the possible factorization using the given prime and intermediate factorization.

    """
    # The possibility we are examining; add the prime to the intermediate
    # factorization
    possibility = sorted(f + [p])

    if len(possibility) == len(set(possibility)):
        # The possibility does not have a repeated prime; just return

        # FixMe: If this is not in the results list, we should update
        # smallest_factorization_idx and return, right?
        return [], smallest_factorization_idx, False

    # Just find what index f is in the factorizations list
    idx__ = factorizations.index(f)

    if possibility in factorizations:
        return [], smallest_factorization_idx, False

    for i in range(0, len(possibility)):
        other = possibility[:i] + possibility[i + 1:]
        prime = possibility[i]

        if other not in factorizations:
            return [], idx__, True

        for i in range(0, factorizations.index(other)):
            if sorted([prime] + factorizations[i]) not in factorizations:
                return [], idx__, True

    return possibility, idx__, True


def new_repeated_prime_factorizations(n, primes, factorizations):
    """Return the possibilities for factorizaiton of n whose factorizations contain a repeated prime number.

    For each prime, loop through the factorizations of each n, and see
    if we can get a possibility for that pair.  Once you find a
    possibility for one factorization, you don't need to go further than
    that factorization for the later primes.
    """

    r = []
    smallest_factorization_idx = None

    for p in primes:
        for f in factorizations:
            break_ = False

            if smallest_factorization_idx is not None and f == factorizations[smallest_factorization_idx]:
                break

            r_, smallest_factorization_idx, break_ = one_repeated_prime_factor(
                n, factorizations, p, f, smallest_factorization_idx)

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
    eliminate = collections.defaultdict(list)

    n = start_n
    while n <= max_n:
        new = []
        real_z = Z(n)
        possible = []
        outstanding_count = collections.defaultdict(lambda : 0)
        total = 0
        for factorizations in generate_all_possible_lists(all_factorizations):
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
                # More pruning.  Check if any of the possibilities are less than
                # all the other possibilities in the list; if so, only keep it.
                save = new_
                x = partition(new_, factorizations)
                for p in x:
                    if lt(p, x, factorizations):
                        save = p
                        lt(p, x, factorizations)
                new_ = save

            for x in outstanding:
                if list(x) in factorizations:
                    outstanding_count[x] += 1
                else:
                    if not new_:
                        outstanding_count[x] += 1
                    for y in new_:
                        #if x == [2,3,5] and y == [2,2,3,3]: pdb.set_trace()
                        if lt_one_(list(x),y,factorizations):
                            outstanding_count[x] += 1


            for x in new_:
                if x not in new and x not in eliminate[n-2]:
                    new += [x]
        #if n == 4: pdb.set_trace()
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
                if tuple(x) not in outstanding:
                    outstanding |= set(((tuple(x)),))

        all_factorizations += [sorted(new)]
        finished |= new_finished

        if new_finished:
            for x in generate_all_possible_lists(all_factorizations):
                all_possible = True
                for y in new_finished:
                    y = list(y)

                    possible_z, idx = calculated_Z(y, primes, x)
                    if y not in x:
                        all_possible = False
                        break
                    if possible_z != Z(x.index(y)+2):
                        all_possible = False
                        break
                if all_possible:
                    possible += [copy.copy(x)]

            new_eliminate = []
            for x in range(0, len(all_factorizations)):
                 for i in range(0, len(all_factorizations[x])):
                     found = False
                     for y in possible:
                         if all_factorizations[x][i] == y[x]:
                             found = True
                     if not found:
                         new_eliminate += [[x, all_factorizations[x][i]]]


            if new_eliminate:
                min_ = None
                for x in new_eliminate:
                    all_factorizations[x[0]].remove(x[1])
                    if not min_:
                        min_ = x[0]
                    min_ = min(min_,x[0])
                    if [x[1]] not in eliminate[x[0]]:
                        eliminate[x[0]] += [x[1]]
                #print('resetting to:',min_+2,'from:',n)
                n = min_+3
                #pdb.set_trace()
                all_factorizations = all_factorizations[:min_+1]
                continue
        n = n + 1


    print(finished)
    print(outstanding)
    return all_factorizations

if __name__ == "__main__":
    def main():
        # Run the test first so we know if anything is broken
        f_upto_37 = [[[2]], [[3]], [[2, 2]], [[5]], [[2, 3]], [[7]], [[2, 2, 2], [3, 3]], [[2, 2, 2], [3, 3]], [[2, 5]], [[11]], [[2, 2, 3]], [[13]], [[2, 7], [3, 5]], [[2, 7], [3, 5]], [[2, 2, 2, 2], [2, 3, 3]], [[17]], [[2, 2, 2, 2], [2, 3, 3]], [[19]], [[2, 2, 5]], [[2, 11], [3, 7]], [[2, 11], [3, 7]], [[23]], [[2, 2, 2, 3], [3, 3, 3], [5, 5]], [[2, 2, 2, 3], [3, 3, 3], [5, 5]], [[2, 13]], [[2, 2, 2, 3], [2, 2, 7], [3, 3, 3], [5, 5]], [[2, 2, 2, 3], [2, 2, 7], [3, 3, 3], [5, 5]], [[2, 3, 5], [29]], [[2, 3, 5], [30]], [[2, 3, 5], [31]], [[2, 2, 2, 2, 2]], [[2, 17], [3, 11], [5, 7]], [[2, 17], [3, 11], [5, 7]], [[2, 17], [3, 11], [5, 7]], [[2, 2, 3, 3]], [[2, 3, 5], [37]]]
        # Generate + print out factorization possibilities

        f = generate_factorization_possibilities(int(sys.argv[1]))#,f_upto_37[:-1])
        print(1, "[[1]]")
        for n in range(0, len(f)):
            print(n + 2, f[n])
        print(f)
        #print(Z(30))

        real_z = Z(30)

        possible = []
        impossible = []
    cProfile.run('main()')
    #main()
