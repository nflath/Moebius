# Functions to filter out values generated as possible factorizations for a
# specific n.

# More factorizations than are possible for a given n are generated, and then
# these are used to cut down ones generated algorithmically to ones that are
# actually possible.

def IsLowerThanFinished(state, possible_factorization):
    """Is possible_factorization lower than a finished factorization."""
    for f in state.all_factorizations.finished:
        if state.all_factorizations.ord_absolute(possible_factorization, f) == -1:
            return True
    return False

def IsOtherLockedForN(state, possible_factorization):
    """ Is some other factorization locked to this location. """

    return state.n in state.locked_n and \
      tuple(state.locked_n[state.n]) != tuple(possible_factorization)

def IsLockedElsewhere(state, possible_factorization):
    """Has possible_factorization been locked to a different position.

    A factorization is 'locked' to a position when it is the last
    factorization available for a given n; at that point it cannot
    appear anywhere else.
    """
    return tuple(possible_factorization) in state.locked and \
      state.locked[tuple(possible_factorization)] != state.n

def IsEliminated(state, possible_factorization):
    """Has possible_factorization been eliminated from this position."""
    return possible_factorization in state.eliminate[state.n-2]

def SkipsLowerFactorization(state, possible_factorization):
    """Does possible_factorization have a factorization less than it not in state."""

    # Primes do not need this check.
    if len(possible_factorization) == 1:
        return False

    primes_finished = set()
    for i in range(0, len(possible_factorization)):
        # For each prime, rest where p * rest = possible:
        #   Verify that for all y < rest, p * y exists in state.

        # Only check each prime once(performance enhancement)
        p = possible_factorization[i]
        if p in primes_finished:
            continue
        primes_finished.add(p)

        rest = possible_factorization[:i] + possible_factorization[i + 1:]

        if tuple(rest) not in state.all_factorizations.reverse_idx or \
          len(state.all_factorizations.reverse_idx[tuple(rest)]) == 0:
            return True
        rest_idx = state.all_factorizations.reverse_idx[tuple(rest)][0]

        for i in range(0, rest_idx):
           for y in state.all_factorizations[i]:
               # y will be a possibility where y < rest
               # x is p * y

               x = tuple(sorted([p] + y))
               y_idx = state.all_factorizations.reverse_idx[tuple(y)][-1]
               found = x in state.all_factorizations.reverse_idx and \
                 len(state.all_factorizations.reverse_idx[x]) > 0

               if y_idx < rest_idx and not found:
                 # y < rest but p * y > rest * y.  So p * y has been skipped and
                 # must occur before possible_factorization is generated.
                 return True

    # No skipped factorizations found
    return False

def IsTooHigh(state, new_factorizations, possible_factorization):
   """Is new_factorization greater than too many others."""
   # Factorizations that are transitively a possible factorization for some 'n'
   # that new_factorizations is.

   lt = []
   gt = []
   equiv = []
   # return all positions and factorizations 'transitively shared' by
   # possibe_factorizations (IE, all factorizations that share a 'n' as a
   # possible factorization, and all factorizations for them, etc.)

   p, i = state.all_factorizations.shared(possible_factorization)
   if len(p) == 0:
       # This is a new factorization; add everything shared for the new n
       # FixMe: Should we just always do this?

       for x in new_factorizations:
           p_, i_ = state.all_factorizations.shared(x)
           p = p.union(p_)
           i = i.union(i_)
           i.add(tuple(x))

   # Populate lt, gt, equiv
   for n in i:
       r = state.all_factorizations.ord_absolute(n, possible_factorization)
       if r == -1:
           lt += [n]
       elif r == 1:
           gt += [n]
       else:
           equiv += [n]

   # If the number of positions (including the current 'n') transitively shared
   # is more than the number of factorizations in lt, this could be a possible
   # factorization for n.
   if len(p)+1 > (len(lt)):
       return False
   return True
