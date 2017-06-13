import math
import pdb
import sys

def index_recursive(lst, elt, last=False):
    """Find elt in list of lists lst

    Returns whether or not the element was found, and the index of the
    list it was found in.
    """
    for l in lst:
        for e in l:
            if e == elt:
                #return True, lst.index(l)
                if not last:
                    return True, lst.index(l)
                f, i = index_recursive(lst[lst.index(l)+1:],elt,last)
                if f:
                    #pdb.set_trace()
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

def lt_one(t, o, factorizations):
    t_found, t_index = index_recursive(factorizations,t,True)
    o_found, o_index = index_recursive(factorizations,o)

    if t_found and not o_found:
        return 0
    if t_index < o_index:
        return 0
    if t_index == o_index:
        return -1
    return 1

def lt(this, other, factorizations):


    if len(other) == 1:
        return False

    for x in other:
       if this == x:
           continue

       t, o = simplify(this, x)

       if lt_one(t,o,factorizations) == 0:
           continue
       elif lt_one(t,o,factorizations) == 1:
           return False
       else:
           # Try some tricky shit here
           begin = x[:-1]
           if not begin:
               return False
           end = x[-1:]
           o_found_, o_index_ = index_recursive(factorizations, begin, True)
           assert o_found_

           if len(factorizations[o_index_]) == 1:
               return False

           for x in factorizations[o_index_]:
               if x == begin:
                   continue
               new = x + end
               t, o = simplify(this, new)
               if lt_one(t,o,factorizations) == 0:
                   continue
               elif lt_one(t,o,factorizations) == 1:
                   return False
               else:
                   # Still couldnt find it
                   return False


    return True



def gt(this, other, factorizations):
    """Returns whether this > every other factorization in other, given the factorization orders defined in factorizations."""
    if len(other) == 1:
        return False
    for x in other:
        if this == x:
            # Don't compare to ourselves
            continue
        t, o = simplify(this, x)

        # If other is in the list but not this or the last index of other is
        # before the first index of this, this > other.
        t_found, t_index = index_recursive(factorizations,t)
        o_found, o_index = index_recursive(factorizations,o,True)

        if o_found and not t_found:
            pass #return True
        elif o_index < t_index:
            pass #return True
        else:
            return False

    return True


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
        # FixMe: Move this out of the function
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

        exit = False
        # FixMe: Do we also need to check those factorizations * a, where a is
        # a prime and a < p for all p?

        # FixMe: Why is this not needed in the repeated primes case?  Or is it, but we
        # haven't hit the case

        found, last_idx = index_recursive(factorizations,potential,True)

        #if possibility == [2,3,5] and n == 17: pdb.set_trace()

        allExist = True
        for i in range(0,last_idx):
            for x in factorizations[i]:
                if sorted([p] + x) not in a:
                    allExist = False
                    break
        if allExist:
            # Didn't find all of those - this is a valid possibility
            result += [possibility]
            smallest = p
            return result, smallest, True
        else:
            return [], smallest, False
    if found:
        # We found the possibility in the list of factorizations - check if it
        # can be a possibility anyway, due to
        #if n == 30: pdb.set_trace()

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
        if l:
            result += [possibility]
            smallest = p
            return result, smallest, True


            # FixMe: Is this correct?  I'm not sure it is in the case of
            # multiple factors for the possibility...
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
    # FixMe: I think we need to just walk though all factorizations period -
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
                n_, smallest, break_ = one_unique_prime_factorization(n, length, primes, factorizations, potential[0], p, smallest, a)
                # FixMe: Return whether to break from the search from here -
                # don't just rely on whether we find a possibility

                # FixMe: Early-exit using smallest in this function.  This
                # prevents updates to smallest from occuring in the middle of
                # iterating throught two 'equal' primes.
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
        if l:
            return possibility, idx__, True
        else:
            return [], smallest_factorization_idx, False


def new_repeated_prime_factorizations(n, primes, factorizations):
    """Return the possibilities for factorizaiton of n whose factorizations contain a repeated prime number.

    For each prime, loop through the factorizations of each n, and see
    if we can get a possibility for that pair.  Once you find a
    possibility for one factorization, you don't need to go further than
    that for the next primes.
    """

    r = []
    smallest_factorization_idx = None


    for p in primes:
        for f in factorizations:
            break_ = False

            if smallest_factorization_idx is not None and f == factorizations[smallest_factorization_idx]:
                break

            for x in f:
                #if n == 20 and p == 5 and x == [2, 2]: pdb.set_trace()

                #if n == 9: pdb.set_trace()

                r_, smallest_factorization_idx_, break_ = one_repeated_prime_factor(n, factorizations, p, x, smallest_factorization_idx)


                #if r_ and r_ in r:
                    #if n == 20: pdb.set_trace()
                    #break_  = False
                    #continue

                smallest_factorization_idx = smallest_factorization_idx_
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
        #if n == 30: pdb.set_trace()
        if len(factorizations[-1]) > 1:
           # Prune the possibilities.  Check if any of the possibilities we
           # just added are greater than one of the others in the list; if so,
           # remove it.
           changed = True

           while changed and len(factorizations[-1]) > 1:
               changed = False
               remove = []
               for x in factorizations[-1]:
                   if gt(x,factorizations[-1],factorizations):
                       changed = True
                       remove = x
                       break
               if remove:
                   #print('pruning from n:',n,'possibility:',remove)
                   i = factorizations[-1].index(remove)
                   factorizations[-1] = factorizations[-1][:i] + factorizations[-1][i+1:]
        if len(factorizations[-1]) > 1:
            save = None
            for x in factorizations[-1]:
                #if n == 20: pdb.set_trace()
                if lt(x,factorizations[-1], factorizations):
                    save = x
                    break
            if save:
                factorizations[-1] = [save]


    return factorizations

def test():
    expected = [[[2]], [[3]], [[2, 2]], [[5]], [[2, 3]], [[7]], [[2, 2, 2], [3, 3]], [[2, 2, 2], [3, 3]], [[2, 5]], [[11]], [[2, 2, 3]], [[13]], [[2, 7], [3, 5]], [[2, 7], [3, 5]], [[2, 2, 2, 2], [2, 3, 3]], [[17]], [[2, 2, 2, 2], [2, 3, 3]], [[19]], [[2, 2, 5]], [[2, 11], [3, 7]], [[2, 11], [3, 7]], [[23]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[2, 13], [3, 11], [5, 7]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[2, 2, 2, 3], [3, 3, 3], [5, 5], [2, 2, 7]], [[29], [2, 3, 5]], [[30], [2, 3, 5]]]

    actual = generate_factorization_possibilities(min(int(sys.argv[1]),len(expected)))
    #print(actual)
    print(len(actual))
    for i in range(0,len(actual)):
        if expected[i]  != actual[i]:
            print("ERROR: at n:",i+2,"expected",expected[i],"but was",actual[i])
    #print(actual)
    #assert(generate_factorization_possibilities(30)==f)

if __name__ == "__main__":
    test()
    f = generate_factorization_possibilities(int(sys.argv[1]))
    #print(lt([2,2,5], [[2, 2, 5], [2, 2, 2, 3], [3, 3, 3]], f))
    #print(lt([2,2,2], [[2, 2, 2], [3,3]], f[:7]))
    print(1, "[[1]]")
    for n in range(0, len(f)):
        print(n+2, f[n])
    print(f)


# FixMe: 20 produces [[2, 2, 5], [2, 2, 2, 3], [3, 3, 3]]- should additionally produce [5,5]
