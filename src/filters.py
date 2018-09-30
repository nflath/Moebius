def IsLowerThanFinished(state, possible_new_value):
    for f in state.all_factorizations.finished:
        if state.all_factorizations.ord(possible_new_value, f) == -1:
            return True
    return False

def IsLockedElsewhere(state, possible_new_value):
    return tuple(possible_new_value) in state.locked and \
      state.locked[tuple(possible_new_value)] != state.n

def index_recursive(lst, elt, last=False):
    """find elt in list of lists lst

    returns whether or not the element was found, and the index of the
    list it was found in.  if last is set, returns the last index of the
    list it was found in.
    """
    if tuple(elt) not in lst.reverse_idx:
        return False, 0

    if last:
        if len(lst.reverse_idx[tuple(elt)])==0:
            return False, -1
        return True, lst.reverse_idx[tuple(elt)][-1]
    if len(lst.reverse_idx[tuple(elt)])==0:
        return False, -1
    return True, lst.reverse_idx[tuple(elt)][0]

def IsEliminated(state, possible_new_value):
    return possible_new_value in state.eliminate[state.n-2]

def SkipsLowerPossibility(state, possible_new_value):
    primes_finished = set()
    found_all = True
    for i in range(0, len(possible_new_value)):
        # Go through all factorizations before 'potential' and ensure that no
        # factorization * p is lower than potential * p but doesn't exist.
        prime = possible_new_value[i]
        if prime in primes_finished:
            continue
        primes_finished.add(prime)
        other = possible_new_value[:i] + possible_new_value[i + 1:]
        if not other:
            break

        found, idx = index_recursive(state.all_factorizations, other)
        if not found:
            found_all = False
            break

        for i in range(0, idx):
           for y in state.all_factorizations[i]:
               x = sorted([prime] + y)
               _, idx__ = index_recursive(state.all_factorizations, y, last=True)
               found, _ = index_recursive(state.all_factorizations, x, last=True)
               if idx__ < idx and not found:
                  found_all = False
                  break
           if not found_all:
                break
        if not found_all:
            break

    if found_all:
        return False
    return True
