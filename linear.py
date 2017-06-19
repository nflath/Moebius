import math
import pdb
import sys
import itertools

def partition(s, factorizations):
    """Partitions the set of factorizations 's' into  equal groupings.

    For example, [2,2,2,3] and [3,3,3] will be grouped together while
    [2,2,2] and [3,3] have not been disambiguated.
    """

    r = []
    for x in s:
        f, _ = index_recursive(r,x)
        if f:
            continue
        r_ = [x]
        for y in s:
            if x == y:
                continue
            f, _ = index_recursive(r,y)
            if f:
                continue

            if not lt_one_(x,y,factorizations) and \
                not lt_one_(x,y,factorizations):
                r_ += [y]
        r += [r_]
    return r

def finished_nolt(f, factorizations):
    count = 0
    found, idx = index_recursive(factorizations, f)
    if not found:
        return False
    all_fact = factorizations[idx]


    while found:
        if factorizations[idx] == all_fact:
            count += 1
            found, idx_ = index_recursive(factorizations[idx+1:], f)
            idx = idx_ + idx + 1
        else:
            return True
    return count==len(all_fact)

def finished(f, factorizations):
    # Returns whether we know all potential locations of f in factorizations

    count = 0
    found, idx = index_recursive(factorizations, f)
    if not found:
        return False
    all_fact = factorizations[idx]


    while found:
        if factorizations[idx] == all_fact:
            count += 1
            found, idx_ = index_recursive(factorizations[idx+1:], f)
            idx = idx_ + idx + 1
        else:
            break

    if count == len(all_fact):
        return True

    for i in range(idx, len(factorizations)):
        lt_all = True
        #pdb.set_trace()
        for x in factorizations[i]:

            if lt_one(x, f, factorizations) != 0:
                lt_all = False
        if lt_all:
            #pdb.set_trace()
            return True

    return count == len(all_fact)

def filter_possibility(f, factorizations):
    # Returns whether this can be a possibility

    for f_ in factorizations:
        for x in f_:
            #if f == [2,3,5] and x == [2,2,3,3]: pdb.set_trace()
            #if x == [2,2,7] and finished(x, factorizations): pdb.set_trace()
            if finished(x, factorizations) and \
              lt_one(f, x, factorizations)==0:
              #pdb.set_trace()
              lt_one(f, x, factorizations)
              return False
    return True


def index_recursive(lst, elt, last=False):
    """Find elt in list of lists lst

    Returns whether or not the element was found, and the index of the
    list it was found in.  If last is set, returns the last index of the
    list it was found in.
    """
    for l in lst:
        for e in l:
            if e == elt:
                if not last:
                    return True, lst.index(l)
                f, i = index_recursive(lst[lst.index(l)+1:],elt,last)
                if f:
                    return True, i + lst.index(l) + 1
                return True, lst.index(l)

    return False, 0


def simplify(this, other):
    """ Remove all factors in both this and other from both.

    For example, (2,2,2,2) and (2,2,5) simplifies to (2,2) and (5)."""
    i = 0
    while i < len(this):
        changed = False
        while i < len(this) and this[i] in other:
            changed = True
            index = other.index(this[i])
            this = this[:i] + this[i+1:]
            other = other[:index] + other[index+1:]
        if not changed:
            i = i + 1
    return this, other

def lt_one(t_, o_, factorizations):
    """ Returns whether we can show t < o or not.

    Returns 0 if t < o, 1 if o > t, -1 if we don't know
    This is a set of possible factorizations, and other is a set of
    sets.  We need to make sure that, for each set in other, at least
    one factorization of this is less than one of the factorizations in
    other.
     """


    t, o = simplify(t_,o_)

    if t == [2,2,2,3] and o == [2,2,7]: pdb.set_trace()

    if not t and not o:
        return 1
    if not t:
        return 0
    if not o:
        return -1




    t_found, t_index = index_recursive(factorizations,t,True)
    o_found, o_index = index_recursive(factorizations,o)

    if t_found and not o_found:
        if not finished_nolt(t_,factorizations) or not \
        finished_nolt(o_, factorizations):
            return -1
        return 0
    if t_found and t_index < o_index:
        if not finished_nolt(t_,factorizations) or not \
          finished_nolt(o_, factorizations):
            return -1
        return 0
    if t_index == o_index:
        return -1
    return 1


def lt_one__(this, other, factorization):
    """ Returns True if this < other given the factorizations, false otherwise.

    False does not mean unabiguously greater than; we could just not know (or be equal)
    """

    t, o = simplify(this, other)

    # If t completely eliminates o, then t > o (and vice versa)
    if not t and not o:
        return False
    if not t:
        return True
    if not o:
        return False

    # FixMe: Does this rely on t being finished?
    t_found, t_index = index_recursive(factorizations,t,True)
    o_found, o_index = index_recursive(factorizations,o)

    if t_found and o_found and t_index < o_index:
        return True
    if t_found and not o_found:
        # We managed to find t, but have not generated o yet - so O must be larger.
        return False
    if o_found and not t_found:
        return False

def lt(this, other, factorizations):
    """Returns if we can show this < every element in other (aside itself).

    This is a set of possible factorizations, and other is a set of
    sets.  We need to make sure that, for each set in other, at least
    one factorization of this is less than one of the factorizations in
    other.
    """

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
                if lt_one_(this_element,other_element,factorizations):
                    lt_ = True
        if not lt_:
            return False

    return True

def lt_one_(this, other, factorizations):

    t, o = simplify(this, other)

    for t_perm in itertools.permutations(t):
        for t_split_idx in range(0,len(t)):
            for o_perm in itertools.permutations(o):
                for o_split_idx in range(0,len(o)):

                    t_tmp_begin = sorted(list(t_perm[:t_split_idx]))
                    t_tmp_end   = sorted(list(t_perm[t_split_idx:]))
                    o_tmp_begin = sorted(list(o_perm[:o_split_idx]))
                    o_tmp_end   = sorted(list(o_perm[o_split_idx:]))
                    if t_tmp_begin and t_tmp_end and o_tmp_begin and o_tmp_end:
                        if lt_one(t_tmp_begin, o_tmp_begin, factorizations)==0 and \
                          lt_one(t_tmp_end, o_tmp_end, factorizations)==0:
                          return True
                    elif t_tmp_begin and o_tmp_begin and not t_tmp_end and not o_tmp_end:
                        if lt_one(t_tmp_begin, o_tmp_begin, factorizations)==0:
                            return True
                    elif t_tmp_end and o_tmp_end and not t_tmp_begin and not o_tmp_begin:
                        if lt_one(t_tmp_end, o_tmp_end, factorizations)==0:
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

def one_unique_prime_factorization(n, length, primes, factorizations, potential, p, smallest, a):
    """Returns the possible factorizations of n using the given p and potential with no repeated factors
    """
    possibility = sorted(potential + [p])

    result = []
    if p == smallest:
        # FixMe: Move this out of this function into the containing one
        return [], smallest, False
    if possibility in factorizations:
        # Alread found this or it has a repeated prime
        return [], smallest, False
    if len(set(possibility))!=len(possibility):
        return [], smallest, False

    # Is the possibility already in the list of factorizations
    found, idx = index_recursive(factorizations, possibility)
    if not found:
        # The possibility is not already in the list of factorizations.  Go
        # through all factorizations before 'potential' and ensure that no
        # factorization * p is lower than potential * p but doesn't exist.

        # FixMe: Do we also need to check those factorizations * a, where a is
        # a prime and a < p for all p?

        # FixMe: Why is this not needed in the repeated primes case?  Or is it, but we
        # haven't hit the case yet?

        found, last_idx = index_recursive(factorizations,potential,True)

        allExist = True
        for i in range(0,last_idx):
            for x in factorizations[i]:
                if sorted([p] + x) not in a:
                    allExist = False
                    break

        if len(potential) == 1:
            # If both p and potential are primes, consider the reverse case as
            # well (walk factorizations up to p, adding potential to them)
            found, last_idx = index_recursive(factorizations,[p],True)
            for i in range(0,last_idx):
                for x in factorizations[i]:
                    if sorted(potential + x) not in a:
                        allExist = False
                        break

        if allExist:
            # This is a valid possibility
            result += [possibility]
            smallest = p
            return result, smallest, True
        else:
            return [], smallest, False
    if found:
        # We found the possibility in the list of factorizations - check if it
        # can be a possibility anyway, due to there being the chance of it
        # being unused.

        f_ = factorizations[idx]
        l = len(f_) - 1
        my_idx = idx+1
        failed = False
        while not failed and l:
            try:
                my_idx += 1 + factorizations[my_idx:].index(f_)
                l -= 1
            except:
                failed = True
        # FixMe: Is this correct?  I'm not sure it is in the case of multiple
        # factors for the possibility...For example if we have a possibility of
        # [[2,2,2],[3,3]] and then [[3,3],[3,5]] and then [[3,5],[2,2,2]].  But
        # I'm not sure this can arise either.

        if l:
            # There is the possibility this option is unused.
            hasPrime = False
            for x in f_:
                if len(x) == 1:
                    hasPrime = True
            result += [possibility]
            smallest = p
            if hasPrime:
                # If our possibility could have been a prime, continue going to
                # generate the next possibility in our list anyway.  This is
                # the case for n = 30 - We don't know if 29 factors to [29] or
                # [2*3*5], so 30 can factor to [30], [2*3*5], or [2*3*7]
                return result, smallest, False
            else:
                return result, smallest, True
    return [], smallest, False

def new_unique_prime_factorizations_for_length(n, length, primes, factorizations):
    """Return all potential prime factorizations for n of the given length.

    Find all current factorizations of length l-1.  For each of them,
    find the lowest prime that when multiplied by the factorization is
    not in the list.  Once you find one possibility, you do not need to
    go past that prime for future cases.
    """

    if length == 1:
        # If the length is 1, the only possibility is that n is a prime.
        primes += [n]
        return [[n,]]

    result = []

    # r is the list of all factorizations that have length one less that our
    # search.
    r = [[x for x in x if len(x) == length - 1] for x in factorizations]
    r = [x for x in r if x]
    # FixMe: Do we need to just walk though all factorizations period -
    # otherwise we may add too much - IE, if we are searching for a
    # factorization of length 4, and we have a*b < c*d*e, and a*b is not in our
    # current list of factorizations, we don't want to skip it - we want to
    # stop the search.

    a = [item for sublist in factorizations for item in sublist]
    # Every factorization.  I think we can get rid of this.

    smallest = None
    added = False

    for potential in r:
        added = False
        for x in potential:
            for p in primes:
                # FixMe: Early-exit using smallest in this function.  This
                # prevents updates to smallest from occuring in the middle of
                # iterating throught two 'equal' primes.
                n_, smallest, break_ = one_unique_prime_factorization(n, length, primes, factorizations, potential[0], p, smallest, a)
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
    possibilities = new_unique_prime_factorizations_for_length(n, length, primes, factorizations)
    result = []
    while possibilities:
        result += possibilities
        length += 2
        possibilities = new_unique_prime_factorizations_for_length(n, length, primes, factorizations)
    return result


def one_repeated_prime_factor(n, factorizations, p, f, smallest_factorization_idx):
    """ Returns the possible factorization using the given prime and intermediate factorization.

    """
    # The possibility we are examining; add the prime to the intermediate factorization
    possibility = sorted(f + [p])

    if len(possibility) == len(set(possibility)):
        # The possibility does not have a repeated prime; just return

        # FixMe: If this is not in the results list, we should update
        # smallest_factorization_idx and return, right?
        return [], smallest_factorization_idx, False

    # Just find what index f is in the factorizations list
    _, idx__ = index_recursive(factorizations, f, last = True)

    # Is the possibility anywhere in factorizations?
    foundin, idx = index_recursive(factorizations, possibility)

    if not foundin:
        # It is not; return the possibility as a real one, as well as the
        # updated smallest_factorization_idx.

        # FixMe: We need to check to make sure this possibility is not higher
        # than all others.  For example, at n=16, this generates [[2, 2, 2, 2],
        # [2, 3, 3], [2, 2, 5]], but 2,2,5 can be shown to be higher than both.
        # Currently, we deal with this by pruning later, but it would be
        # preferable to not generate it as an option in the first place.
        return possibility, idx__, True

    if foundin:
        # We found the possibility in the list of factorizations, but the
        # number it is factorizing has alternative possibilities.  Check if all
        # the possibilities are exhausted later in the factorization list; if
        # so it is not a possibility, otherwise it is.

        # For example: 8 factors into possibilities [[2, 2, 2], [3, 3]]
        # We examine p=2, n= [2,2].  We enter this block.  We do not find two entries of
        # [[2, 2, 2], [3, 3]], [2,2,2] is still a possibility for 9.

        # On the other hand, if n=12, once we check possibility=[2,2,2], we find that
        # both n=8 and n=9 are [[2, 2, 2], [3, 3]], so [2,2,2] is not an option for n=12.


        # f_ = factorizations[idx]
        # l = len(f_) - 1
        # my_idx = idx+1
        # failed = False
        # while not failed and l:
        #     try:
        #         my_idx += 1 + factorizations[my_idx:].index(f_)
        #         l -= 1
        #     except:
        #         failed = True
        # if l:
        if not finished(possibility, factorizations):
            return possibility, idx__, True
        else:
            return [], smallest_factorization_idx, False


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

            for x in f:
                #if n == 32 and x == [2,2,2,2]: pd.bset_trace()
                r_, smallest_factorization_idx, break_ = one_repeated_prime_factor(n, factorizations, p, x, smallest_factorization_idx)

                if r_ and r_ not in r:
                    r += [r_]
                break_ |= break_

            if break_:
                break

    return r


def generate_factorization_possibilities(max_n):
    """ Generates the list of factorization possibilities up to max_n """

    primes = []
    factorizations = []

    for n in range(2, max_n+1):
        m = moebius(n)
        if m == -1:
            factorizations += [new_unique_prime_factorizations(n,1,primes,factorizations)]
        elif m == 0:
            factorizations += [new_repeated_prime_factorizations(n,primes,factorizations)]
        elif m == 1:
            factorizations += [new_unique_prime_factorizations(n,2,primes,factorizations)]
        else:
            assert False

        if len(factorizations[-1]) > 1:
            # More pruning.  Check if any of the possibilities are less than
            # all the other possibilities in the list; if so, only keep it.

            save = factorizations[-1]
            x = partition(factorizations[-1],factorizations)
            for p in x:
                if lt(p, x, factorizations):
                    save = p
                    lt(p, x, factorizations)
            factorizations[-1] = save

        remainder = []
        for x in factorizations[-1]:
            #if n == 37 and x == [2, 3, 5]: pdb.set_trace()
            if filter_possibility(x, factorizations[:-1]):
                remainder += [x]

        factorizations[-1] = remainder


        if len(factorizations[-1]) == 1:
            # Go backwards in order to elimiate possibilities that are greater than this.

            for i in range(0, len(factorizations)-1):
                if n == 46 and i == 43:
                    pdb.set_trace()
                r = []
                for x in factorizations[i]:

                    if not(lt_one(factorizations[-1][0],x,factorizations[:-1]) == 0):
                        r += [x]
                    else:
                        print("foo")
                factorizations[i] = r


        if factorize(n) not in factorizations[-1]:
            print('ERROR: true factorization:', factorize(n), 'not in factorization list for n:',n,factorizations[-1])

    return factorizations

def test():
    # FixMe: Add more tests, possibly unit ones for the various utilities

    # Basic test: Have a known good list, check generated results against it
    # and print a error if different.

    f = [[[2]], [[3]], [[2, 2]], [[5]], [[2, 3]], [[7]], [[2, 2, 2], [3, 3]], [[2, 2, 2], [3, 3]], [[2, 5]], [[11]], [[2, 2, 3]], [[13]], [[2, 7], [3, 5]], [[2, 7], [3, 5]], [[2, 2, 2, 2], [2, 3, 3]], [[17]], [[2, 2, 2, 2], [2, 3, 3]], [[19]], [[2, 2, 5]], [[2, 11], [3, 7]], [[2, 11], [3, 7]], [[23]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[2, 13]]]
    print(finished([2,2,2,3],f))


    expected = [[[2]], [[3]], [[2, 2]], [[5]], [[2, 3]], [[7]], [[2, 2, 2], [3, 3]], [[2, 2, 2], [3, 3]], [[2, 5]], [[11]], [[2, 2, 3]], [[13]], [[2, 7], [3, 5]], [[2, 7], [3, 5]], [[2, 2, 2, 2], [2, 3, 3]], [[17]], [[2, 2, 2, 2], [2, 3, 3]], [[19]], [[2, 2, 5]], [[2, 11], [3, 7]], [[2, 11], [3, 7]], [[23]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[2, 13]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[29], [2, 3, 5]], [[30], [2, 3, 5]]]
    actual = generate_factorization_possibilities(min(int(sys.argv[1]),
                                                      len(expected)+1))

    for i in range(0,len(actual)):
        if expected[i]  != actual[i]:
            print("ERROR: at n:",i+2,"expected",expected[i],"but was",actual[i])




if __name__ == "__main__":
    # Run the test first so we know if anything is broken
    test()

    # Generate + print out factorization possibilities
    f = generate_factorization_possibilities(int(sys.argv[1]))
    print(1, "[[1]]")
    for n in range(0, len(f)):
        print(n+2, f[n])
    print(f)
