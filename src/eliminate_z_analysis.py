from util import *
from functools import reduce

# Here is the most complicated piece of analysis in the program; definitely
# need to make sure it's corect, and right now it isn't (due to optimizations).

# Basic idea:
# Save the current mapping of n->all possible factorizations for n in 'e'
# For each possible fullset of n->factorization possibilities 'f'
#     For each newly finished factorization 'y'
#         1.  Calculate Z(y) and Z1(y) based on 'f'.
#         2.  Check if there any n' for which moebius(n') matches moebius(n)
#             and Z(n') == Z(y,f) (and Z1(n') == Z1(y,f)
#         3.  If there is, f is potentially valid.  if f[n''] = y', then
#             we can't eliminate y' as a factorization for n''
#    If there is some f(n'')=y' pair that was never in a valid f, we can eliminate
#    y' as a possibility for n''.

# Complexities beyond this simple description:

# Selection of n->all possible factorizations to use:
#
# For each 'y', we need to identify the values of n where choosing different
# factorizations could affect the value of either Z or Z1.  This is
# accomplished in the ranges_for_z_calculations function.  Indexes we are care
# about are:
#   1.  factorizations that are a subset of 'y'
#   2.  For each p, if p*p*z < y or p*z < y is unknown, then take the non-common factors
#   t, o.  Each 'n' where t or o can occur is an index we are interested in.
#   3.  Each 'n' that may be prime is interesting
#   4.  Factorizations that aare transitively share a location with a
#   factorization meeting the above criteria.
#
#   After we determine, these, all values of 'n' that contain 'y' as a
#   possibility are marked as non-interesting; instead, we will fix 'y' to each
#   location (as we don't care about the ordering of everything before y, but
#   merely where y is located in it's possibilities.

# Calculation of Z/Z1(y, f):
#
# We now here have a set of factorizations [2->[2], 3->[3], .... [y_idx]=y] f
# and we want to find the possible values of Z(y) assuming the factorization f
# is correct.
#
# There are a few complexities: transitively shared factorizations with y,
# outstanding factorizations, and ... .
# Note: Can we just get rid of outstanding factorizations by waiting longer?
#
# TODO


@memoized
def Z(n):
    """ Returns the real Z(n)"""
    return len([x for x in range(1,n+1) if moebius(x) == 0])

@memoized
def Z1(n):
    """ Returns the real Z(n)"""
    return len([x for x in range(2,n+1) if moebius(x) == 1])

def InRange(val, min, max):
    """ Is val between max and min, inclusive."""
    return val <= max and val >= min

def ZIsPossibleBase(z_min,z_max,m,ZFn):
    """Return the last value of n with moebius m and Zfn(n) in range."""
    n = 2
    z_ = 0
    n_max = -1
    while z_ <= z_max:
        m_ = moebius(n)
        z_ = ZFn(n)
        if InRange(z_,z_min,z_max) and m_ == m:
            n_max = n
        n += 1
    return n_max

@memoized
def ZIsPossible(z_min,z_max, m):
    """Return the last value of n with moebius m and Z(n) in range."""
    return ZIsPossibleBase(z_min,z_max,m,Z)

@memoized
def Z1IsPossible(z_min,z_max, m):
    """Return the last value of n with moebius m and Z1(n) in range."""
    return ZIsPossibleBase(z_min,z_max,m,Z1)

def ord(t, o, factorizations):
    """Returns whether this < other for a specific factorization possibility.

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

# FixMe: Unify calculated_Z and calculated_Z1 somehow.
def calculated_Z(f, primes, factorizations, all_factorizations, y_idx, real):
    """Calculates Z(f).

    For each prime 'p', counts the number of factorizations 'a' where
    p*p*a <= f.  Returns the total number of cases this is true for."""

    count = 0
    max_idx = 0
    in_ = set()

    # Go through p*p*f in factorizations and add all that match
    for p in primes:
        val = ord([p,p], f, factorizations)
        if val == 99:
            break
        if val <= 0:
            in_.add((p,p))
        else:
            break
        for x_idx in range(0,len(factorizations)):
            x = factorizations[x_idx]
            possibility = sorted([p,p]+x)
            val = ord(possibility, f, factorizations)
            if val <= 0:
                max_idx = max(max_idx, x_idx)
                in_.add(tuple(possibility))
            else:
                break
    # Now, we need to handle the cases that are past the point we stopped
    # generating every possibility.
    pos = set()
    in_y = set()
    in_both = set()
    # FixMe: Is this fully correct?  Why only reverse_idx
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

def calculated_Z1(f, primes, factorizations, all_factorizations, y_idx, real):
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
    #if real:
        #pdb.set_trace()
# Real on also has 5 * 11

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
    factorization for every Z.
    """

    possible_primes = []
    for x in all_factorizations:
        for y in x:
            if len(y) == 1:
                possible_primes += y

    # Don't analyze for positions that are multiples of potential nonprimes.
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
        # Mask[y] will be set to True for each index we care about
        mask[y] = [False] * len(all_factorizations)
        for p in possible_primes:
            for x_idx in range(0, len(all_factorizations)):
                for z in all_factorizations[x_idx]:
                    t, o = simplify(z, y)
                    if not t:
                        # y is a multiple of z; we're interested in this
                        # FixMe: Why?
                        mask[y][x_idx] = True
                    tup = (sorted([p,p] + z), sorted([p]+z))
                    for v in tup:

                        val = all_factorizations.ord_absolute(v,y)

                        if tuple(v) == y:
                            # FixMe: Why?
                            mask[y][x_idx] = True
                        if tuple(v) not in all_factorizations.outstanding and \
                          tuple(v) not in all_factorizations.finished:
                            # We haven't generated v yet at all, can't do anything here
                            continue

                        if val == 99:
                            t, o = simplify(v, y)

                            # We don't know p*p*z <> y; cancle out common factors and
                            # for the remainder iterate through all possibilities
                            # FixMe: Explain why we care about these
                            if tuple(o) != y:
                                for idx in all_factorizations.reverse_idx[tuple(t)]:
                                    mask[y][idx] = True
                                for idx in all_factorizations.reverse_idx[tuple(o)]:
                                    mask[y][idx] = True
                    # End for v in tup
                # End for z in all_factorizations[x_idx]:
            # End for x_idx in range(0, len(all_factorizations)):
        # End for p in possible_primes:


        for x in range(0, len(mask[y])):
            if mask[y][x]:
                for z in all_factorizations[x]:
                    for zp in z:
                        if len(all_factorizations.reverse_idx[(zp,)]) > 1:
                            mask[y][all_factorizations.reverse_idx[(zp,)][0]] = True

        # For every factorization where mask[y][x]==True, set everywhere it could be to true
        # FixMe: Use shared here
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

        # mask[y][y_idx] and everything shared should always be false.
        # FixMe: Explain why
        # FixMe: Use shared
        present = set()
        for y_idx in all_factorizations.reverse_idx[y]:
            mask[y][y_idx] = False
            for z in all_factorizations[y_idx]:
                present.add(tuple(z))

        for x_idx in range(0,len(all_factorizations)):
            for z in all_factorizations[x_idx]:
                if tuple(z) in present:
                    mask[y][x_idx] = False;

        # For clarity, if there is only one option don't have the mask set to true
        for x_idx in range(0,len(all_factorizations)):
            if len(all_factorizations[x_idx]) == 1:
                mask[y][x_idx] = False;
    return mask

def analyze_z_for_factorizations_mask(state, mask):
    """For each factorization we've generated a mask for, analyze the Z-values.

    Specifically, generate each possible factorization list given the
    mask and, for each possible position of y, see if they are valid
    based on Z-values.  Find if there are any factorizations for n that are never valid.
    """

    n = state.n
    all_factorizations = state.all_factorizations
    eliminate = []
    for y in mask:
        # Ignore primes:
        # FixMe: filter them out when generating mask
        if len(y) == 1:
            continue

        state.logger.debug("  About to analyze masked Z for y="+str(y)+" "+str(mask[y]))

        # Debug information: number of lists we have to generate
        cnt = 0
        for x in generate_all_possible_lists_for_mask(all_factorizations, mask[y]):
            cnt += 1
        state.logger.debug("  Count = "+str(cnt))

        # e is the possibilities we can eliminate
        e = copy.deepcopy(all_factorizations.all_factorizations)
        for idx in range(0, len(all_factorizations)):
            if not mask[y][idx]:
                e[idx] = []


        for y_idx in all_factorizations.reverse_idx[tuple(y)]:
            for x in generate_all_possible_lists_for_mask(all_factorizations[:y_idx+1], mask[y][:y_idx+1]):

                y_start_idx = all_factorizations.reverse_idx[tuple(y)][0]
                x[y_idx] = list(y)
                primes = [x[0] for x in x if len(x) == 1]

                moebius_of_y = 0 # FixMe: move this out into a function
                if len(set(y)) == len(y):
                    moebius_of_y = int(math.pow(-1,len(y)))

                real = True
                if reduce(lambda x,y: x * y, y) != y_idx+2:
                    real = False
                for a in range(0,len(mask[y])):
                    if mask[y][a] and x[a] != factorize(a+2):
                        real = False

                possible_z_min, possible_z_max = calculated_Z(list(y), primes, x[:y_start_idx+1], all_factorizations, y_idx, real)
                z_is_possible = ZIsPossible(possible_z_min,possible_z_max,moebius_of_y)

                if (z_is_possible < (y_idx+2)):
                    continue
                if (not InRange(Z(y_idx+2),possible_z_min,possible_z_max)):
                    continue

                possible_z1_min, possible_z1_max = calculated_Z1(list(y), primes, x[:y_start_idx+1], all_factorizations, y_idx, real)
                z1_is_possible = Z1IsPossible(possible_z1_min,possible_z1_max,moebius_of_y)

                if (z1_is_possible < (y_idx+2)):
                    continue
                if (not InRange(Z1(y_idx+2),possible_z1_min,possible_z1_max)):
                    continue

                for i in range(0, len(e)):
                    if i < len(x):
                        if x[i] in e[i]:
                            e[i].remove(x[i])
                    else:
                        e[i] = []

        for idx in range(0,len(e)):
           # FixMe: We can just update state here.
           for z in e[idx]:
               state.logger.info("  Mask Eliminating [n=%d,%s] based on: %s " % (idx+2,str(z),str(y)))
               eliminate += [[idx, z]]
               if z == factorize(idx+2):
                   # Oops, we eliminated the right value
                   pdb.set_trace()
                   assert False

    return eliminate


def all_eliminations(state, new_finished):
    """Eliminates factorizations based on analyzing their z-values.

    Returns lowest n-value affected.
    """
    mask = ranges_for_z_calculations(state.n, state.all_factorizations, new_finished)
    e_ = analyze_z_for_factorizations_mask(state, mask)
    min_ = state.n - 2
    for x in e_:
        if x[1] in state.all_factorizations[x[0]]:
            min_ = min(min_,x[0])
            if [x[1]] not in state.eliminate[x[0]]:
                state.eliminate[x[0]] += [x[1]]

    return min_

    return e_, []
