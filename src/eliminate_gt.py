from util import *

def EliminateBasedOnGt(state, new_finished):
    """Finds cases where we know a < b but not f*a < f*b or vice versa.

    Registers these cases and returns the lowest affected n (so we can
    redo work from there with this new knowledge).
    """
    lowest = state.n - 2
    for f in new_finished:
        for x in range(0, len(state.all_factorizations)):
            for z in state.all_factorizations[x]:
                # t * a = f
                # o * a = z
                t, o = simplify(f, z)

                # Don't deal with possible primes
                if len(t) == 1 and len(state.all_factorizations[state.all_factorizations.reverse_idx[tuple(t)][0]]) > 1:
                    continue
                if len(o) == 1 and len(state.all_factorizations[state.all_factorizations.reverse_idx[tuple(o)][0]]) > 1:
                    continue

                # If, based on just the factorization possibility list, t < o
                # is known but not f < z, or vice versa, register the other one
                # as known.
                if (state.all_factorizations.ord(list(f), list(z)) == 1 and state.all_factorizations.ord(t,o) == 99):
                    state.logger.info(" %s < %s " % (str(o),str(t)))
                    state.all_factorizations.register_lt(o,t)
                    lowest = min(lowest, state.all_factorizations.reverse_idx[tuple(o)][0])
                if state.all_factorizations.ord(list(z), list(f)) == 1 and state.all_factorizations.ord(t,o) == 99:
                    state.logger.info(" %s < %s " % (str(t),str(o)))
                    state.all_factorizations.register_lt(t,o)
                    lowest = min(lowest, state.all_factorizations.reverse_idx[tuple(t)][0])
                if (state.all_factorizations.ord(list(t), list(o)) == 1 and state.all_factorizations.ord(list(f),list(z)) == 99):
                    state.logger.info(" %s < %s " % (str(z),str(f)))
                    state.all_factorizations.register_lt(z,f)
                    lowest = min(lowest, state.all_factorizations.reverse_idx[tuple(z)][0])
                if state.all_factorizations.ord(list(o), list(t)) == 1 and state.all_factorizations.ord(list(z),list(f)) == 99:
                    state.logger.info(" %s < %s " % (str(f),str(z)))
                    state.all_factorizations.register_lt(f,z)
                    lowest = min(lowest, state.all_factorizations.reverse_idx[tuple(f)][0])

    for f in new_finished:
        for x in range(0, len(state.all_factorizations)):
            if len(state.all_factorizations[x]) > 1:
                for z in state.all_factorizations[x]:
                    t, o = simplify(f, z)
                    # f = z * t
                    if tuple(z) != f and tuple(t) != f and not o:
                        for z2 in state.all_factorizations[x]:
                            # z and z2 were both generated as possibilities for
                            # n=x, so we don't know z < z2.

                            # Check if there we know z * t < z2 * t for some t
                            # or vice versa.
                            if state.all_factorizations.ord(list(f), sorted(z2+t)) == 1 and \
                                state.all_factorizations.ord(z, z2) == 99 and len(z2) != 1 and len(z) != 1:
                                state.logger.info(" %s < %s " % (str(z2),str(z)))
                                state.all_factorizations.register_lt(z2, z)
                                lowest = min(lowest, state.all_factorizations.reverse_idx[tuple(z2)][0])
                            if state.all_factorizations.ord(list(f), sorted(z2+t)) == -1 and \
                                state.all_factorizations.ord(z, z2) == 99 and len(z2) != 1 and len(z) != 1:
                                state.logger.info(" %s < %s " % (str(z),str(z2)))
                                state.all_factorizations.register_lt(z, z2)
                                lowest = min(lowest, state.all_factorizations.reverse_idx[tuple(z)][0])
    return lowest
