import math
import pdb
import copy
import sys
import itertools


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
            try:
                retn[idx] = x
            except:
                pdb.set_trace()
            retn[idx] = x
            for y in generate_all_possible_lists(lst, idx + 1, retn):
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

    Returns 0 if t < o, 1 if o > t, -1 if we don't know.
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
    if t_found and t_index < o_index:
        # If both are found and t is earlier than o, t < o
        return 0

    return 1


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

    for t_perm in itertools.permutations(t):
        for t_split_idx in range(0, len(t)):
            for o_perm in itertools.permutations(o):
                for o_split_idx in range(0, len(o)):

                    t_tmp_begin = sorted(list(t_perm[:t_split_idx]))
                    t_tmp_end = sorted(list(t_perm[t_split_idx:]))
                    o_tmp_begin = sorted(list(o_perm[:o_split_idx]))
                    o_tmp_end = sorted(list(o_perm[o_split_idx:]))
                    if t_tmp_begin and t_tmp_end and o_tmp_begin and o_tmp_end:
                        if lt_one(t_tmp_begin, o_tmp_begin, factorizations) == 0 and \
                                lt_one(t_tmp_end, o_tmp_end, factorizations) == 0:
                            return True
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

    for i in range(0, len(possibility)):
        other = possibility[:i] + possibility[i + 1:]
        prime = possibility[i]

        if other not in factorizations:
            return [], smallest, True

        for i in range(0, factorizations.index(other)):
            if sorted([prime] + factorizations[i]) not in factorizations:
                return [], smallest, True

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
    # It is not; return the possibility as a real one, as well as the
    # updated smallest_factorization_idx.

    # FixMe: We need to check to make sure this possibility is not higher
    # than all others.  For example, at n=16, this generates [[2, 2, 2, 2],
    # [2, 3, 3], [2, 2, 5]], but 2,2,5 can be shown to be higher than both.
    # Currently, we deal with this by pruning later, but it would be
    # preferable to not generate it as an option in the first place.

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


def generate_factorization_possibilities(max_n):
    """ Generates the list of factorization possibilities up to max_n """

    all_factorizations = []

    for n in range(2, max_n + 1):
        new = []
        for factorizations in generate_all_possible_lists(all_factorizations):
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

            for x in new_:
                if x not in new:
                    new += [x]

        all_factorizations += [sorted(new)]

    return all_factorizations

if __name__ == "__main__":
    # Run the test first so we know if anything is broken

    # Generate + print out factorization possibilities
    f = generate_factorization_possibilities(int(sys.argv[1]))
    print(1, "[[1]]")
    for n in range(0, len(f)):
        print(n + 2, f[n])
    # print len(f)
    print(f)
