from util import *

@memoized
def Z(n):
    """ Returns the real Z(n)"""
    return len([moebius(x) for x in range(1,n+1) if moebius(x) == 0])

@memoized
def Z1(n):
    """ Returns the real Z(n)"""
    return len([moebius(x) for x in range(2,n+1) if moebius(x) == 1])

def in_range(val, min, max):
    return val <= max and val >= min

def ZIsPossibleBase(z_min,z_max,m,ZFn):
    """Return the last possible value of n z and m can occur at."""
    n = 2
    z_ = 0
    n_max = -1
    while z_ <= z_max:
        m_ = moebius(n)
        z_ = ZFn(n)
        if in_range(z_,z_min,z_max) and m_ == m:
            n_max = n
        n += 1
    return n_max

@memoized
def ZIsPossible(z_min,z_max, m):
    """Return the last possible value of n z and m can occur at."""
    return ZIsPossibleBase(z_min,z_max,m,Z)

@memoized
def Z1IsPossible(z_min,z_max, m):
    """Return the last possible value of n z and m can occur at."""
    return ZIsPossibleBase(z_min,z_max,m,Z1)

def ord(t, o, factorizations):
    """Returns whether this < other for a specific factorization possibility.

    Check each permutation and 2-way split of this and other to try and
    find one where both parts of this are less than the parts of
    other.

    Returns -1 if t < o, 0 if t == o, 1 if t > o.
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


    if t in factorizations:
        t_index = factorizations.index(t)

    if o in factorizations:
        o_index = factorizations.index(o)

    t_found = t_index is not None
    o_found = o_index is not None

    if t_found and not o_found:
        # If t is in the list and o is not, t < o
        return -1
    if o_found and not t_found:
        # If o is in the list and t is not, t < o
        return 1
    if t_found and t_index < o_index:
        # If both are found and t is earlier than o, t < o
        return -1
    if o_found and o_index < t_index:
        # If both are found and t is later than o, t > o
        return 1

    # Neither are found; return unknown
    return 99

def calculated_Z(f, primes, factorizations, all_factorizations, y_idx):
    """Calculates Z(f).

    For each prime 'p', counts the number of factorizations 'a' where
    p*p*a <= f .  Returns the total number of cases this is true for."""

    count = 0
    max_idx = 0
    in_ = set()
    for p in primes:
        val = ord([p,p], f, factorizations)
        if val == 99:
            break
        if val  <= 0:
            in_.add((p,p))
        else:
            break
        for x_idx in range(0,len(factorizations)):
            x = factorizations[x_idx]
            possibility = sorted([p,p]+x)
            val = ord(possibility, f, factorizations)
            if val == 99:
                break
            if val <= 0:
                max_idx = max(max_idx, x_idx)
                in_.add(tuple(possibility))
            else:
                break

    pos = set()
    in_y = set()
    in_both = set()
    for idx in all_factorizations.reverse_idx[tuple(f)]:
        if idx == y_idx:
            if tuple(f) not in in_ and len(set(f)) != len(f):
                pos.add(idx)
                in_y.add(tuple(f))
            break
        for z in all_factorizations[idx]:
            if len(set(z)) != len(z):
                pos.add(idx)
                if tuple(z) not in in_:
                    in_y.add(tuple(z))
                else:
                    in_both.add(tuple(z))


    return len(in_) + min(len(pos),len(in_y))-min(len(pos),len(in_both)), \
      len(in_) + min(len(pos),len(in_y))

def calculated_Z1(f, primes, factorizations, all_factorizations, y_idx):
    """Calculates Z1(f).

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
                break
            elif val <= 0:
                in_.add(tuple(possibility))
            else:
                break

    pos = set()
    in_y = set()
    in_both = set()
    for idx in range(all_factorizations.reverse_idx[tuple(f)][0],len(all_factorizations)):
        if idx == y_idx:
            if tuple(f) not in in_ and len(set(f)) == len(f) and len(f) % 2 == 0:
                pos.add(idx)
                in_y.add(tuple(f))
            break
        for z in all_factorizations[idx]:
            if len(set(z)) == len(z) and len(z) % 2 == 0:
                pos.add(idx)
                if tuple(z) not in in_:
                    in_y.add(tuple(z))
                else:
                    in_both.add(tuple(z))


    return len(in_) + min(len(pos),len(in_y))-min(len(pos),len(in_both)), \
      len(in_) + min(len(pos),len(in_y))

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

    # Don't analyze for primes that are potentially not prime.
    new_it_set = set()
    for y in it_set:
        valid = True
        for x in y:
            assert len(all_factorizations.reverse_idx[(x,)])==1
            if len(all_factorizations[all_factorizations.reverse_idx[(x,)][0]]) > 1:
                valid = False
        if valid:
            new_it_set.add(tuple(y))

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

            for x_idx in range(0, len(all_factorizations)):

                for z in all_factorizations[x_idx]:
                    t, o = simplify(z, y)
                    if not t:
                        mask[y][x_idx] = True
                    tup = (sorted([p,p] + z), sorted([p]+z))
                    for v in tup:

                        val = all_factorizations.ord_absolute(v,y)

                        if tuple(v) == y:
                            #pdb.set_trace()
                            mask[y][x_idx] = True
                        if tuple(v) not in all_factorizations.outstanding and \
                          tuple(v) not in all_factorizations.finished:
                            continue

                        if val == 99:
                            #if x_idx == 53: pdb.set_trace()
                            t, o = simplify(v, y)

                            #for idx in all_factorizations.reverse_idx[tuple(v)]:
                                #if idx == 53: pdb.set_trace()
                                #mask[y][idx] = True

                            if tuple(o) != y:
                                for idx in all_factorizations.reverse_idx[tuple(t)]:
                                    #if idx == 53: pdb.set_trace()
                                    mask[y][idx] = True
                                for idx in all_factorizations.reverse_idx[tuple(o)]:
                                    #if idx == 53: pdb.set_trace()
                                    mask[y][idx] = True
        # End for x_idx in range(0, len(all_factorizations)):
        #pdb.set_trace()
        for x in range(0, len(mask[y])):
            if mask[y][x]:
                    for z in all_factorizations[x]:
                        for zp in z:
                            if len(all_factorizations.reverse_idx[(zp,)]) > 1:
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

        present = set()
        for y_idx in all_factorizations.reverse_idx[y]:
            mask[y][y_idx] = False
            for z in all_factorizations[y_idx]:
                present.add(tuple(z))

        for x_idx in range(0,len(all_factorizations)):
            for z in all_factorizations[x_idx]:
                if tuple(z) in present:
                    mask[y][x_idx] = False;
    return mask

def analyze_z_for_factorizations_mask(state, new_finished, mask):
    n = state.n
    all_factorizations = state.all_factorizations
    eliminate = []
    for y in mask:
        if len(y) == 1: continue
        state.logger.debug("  About to analyze masked Z for y="+str(y)+" "+str(mask[y]))

        cnt = 0
        for x in generate_all_possible_lists_for_mask(all_factorizations, mask[y]):
            cnt += 1
        state.logger.debug("  Count = "+str(cnt))

        e = copy.deepcopy(all_factorizations.all_factorizations)
        for idx in range(0, len(all_factorizations)):
            if not mask[y][idx]:
                e[idx] = []


        for y_idx in all_factorizations.reverse_idx[tuple(y)]:
            #if n == 28 and y == (3,3,3): pdb.set_trace()
            #if n == 46 and y == (2,3,7): pdb.set_trace()
            #if n == 60: pdb.set_trace()
            for x in generate_all_possible_lists_for_mask(all_factorizations[:y_idx+1], mask[y][:y_idx+1]):
                if n == 56 and y == (2,2,2,7) and y_idx == 54:
                    correct = True
                    for x_idx in range(0, len(x)):
                         if mask[y][x_idx] and x[x_idx] != factorize(x_idx+2):
                             correct = False
                    #if correct: pdb.set_trace()

                y_start_idx = all_factorizations.reverse_idx[tuple(y)][0]
                x[y_idx] = list(y)
                primes = [x[0] for x in x if len(x) == 1]

                moebius_of_y = 0 # FixMe: move this out into a function
                if len(set(y)) == len(y):
                    moebius_of_y = int(math.pow(-1,len(y)))

                if list(y) not in x:
                    continue

                #if n == 32 and y == (2,2,2,2,2)  and x[12] == [2,7]: pdb.set_trace()
                possible_z_min, possible_z_max = calculated_Z(list(y), primes, x[:y_start_idx], all_factorizations, y_idx)

                z_is_possible = ZIsPossible(possible_z_min,possible_z_max,moebius_of_y)

                possible = True
                if (z_is_possible < (y_idx+2)):
                    continue
                if (not in_range(Z(y_idx+2),possible_z_min,possible_z_max)):
                    continue

                possible_z1_min, possible_z1_max = calculated_Z1(list(y), primes, x[:y_start_idx], all_factorizations, y_idx)
                z1_is_possible = Z1IsPossible(possible_z1_min,possible_z1_max,moebius_of_y)
                if (z1_is_possible < (y_idx+2)):
                    continue
                if (not in_range(Z1(y_idx+2),possible_z1_min,possible_z1_max)):
                    continue


                if possible:
                    for i in range(0, len(e)):

                        if i < len(x):

                            if x[i] in e[i]:
                                e[i].remove(x[i])
                        else:
                            e[i] = []

        for idx in range(0,len(e)):
           for z in e[idx]:
               state.logger.info("  Mask Eliminating [n=%d,%s] based on: %s " % (idx+2,str(z),str(y)))
               eliminate += [[idx, z]]
               if z == factorize(idx+2):
                   pdb.set_trace()
                   assert False
        state.logger.debug("  Done analyzing masked Z for y="+str(y))

    return eliminate


def all_eliminations(state, new_finished):
    """ Returns factorizations for positions we can show are impossible. """
    global logger

    mask = ranges_for_z_calculations(state.n, state.all_factorizations, new_finished)
    e_ = analyze_z_for_factorizations_mask(state, new_finished, mask)

    return e_, []
