from util import *

def eliminate_based_on_gt(state, new_finished):
    n = state.n
    all_factorizations = state.all_factorizations
    lowest = n - 2
    for f in new_finished:
        for x in range(0, len(all_factorizations)):
            for z in all_factorizations[x]:
                t, o = simplify(f, z)
                if len(t) == 1 and len(all_factorizations[all_factorizations.reverse_idx[tuple(t)][0]]) > 1:
                    continue
                if len(o) == 1 and len(all_factorizations[all_factorizations.reverse_idx[tuple(o)][0]]) > 1:
                    continue

                if (all_factorizations.ord(list(f), list(z)) == 1 and all_factorizations.ord(t,o) == 99):
                    all_factorizations.register_lt(o,t)
                    state.logger.info("   %s < %s based on %s",o,t,f)
                    lowest = min(lowest, all_factorizations.reverse_idx[tuple(o)][0])
                if all_factorizations.ord(list(z), list(f)) == 1 and all_factorizations.ord(t,o) == 99:
                    all_factorizations.register_lt(t,o)
                    state.logger.info("   %s < %s based on %s",t,o,f)
                    lowest = min(lowest, all_factorizations.reverse_idx[tuple(t)][0])
                if (all_factorizations.ord(list(t), list(o)) == 1 and all_factorizations.ord(list(f),list(z)) == 99):
                    all_factorizations.register_lt(z,f)
                    state.logger.info("   %s < %s based on %s",z,f,f)
                    lowest = min(lowest, all_factorizations.reverse_idx[tuple(z)][0])
                if all_factorizations.ord(list(o), list(t)) == 1 and all_factorizations.ord(list(z),list(f)) == 99:
                    all_factorizations.register_lt(f,z)
                    state.logger.info("   %s < %s based on %s",f,z,f)
                    lowest = min(lowest, all_factorizations.reverse_idx[tuple(f)][0])

    for f in new_finished:
        for x in range(0, len(all_factorizations)):
            if len(all_factorizations[x]) > 1:
                for z in all_factorizations[x]:
                    t, o = simplify(f, z)
                    if tuple(z) != f and tuple(t) != f and not o:
                        for z2 in all_factorizations[x]:
                            if all_factorizations.ord(list(f), sorted(z2+t)) == 1 and \
                                all_factorizations.ord(z, z2) == 99 and len(z2) != 1 and len(z) != 1:
                                all_factorizations.register_lt(z2, z)
                                state.logger.info("   %s < %s based on %s",z2,z,f)
                                lowest = min(lowest, all_factorizations.reverse_idx[tuple(z2)][0])
                            if all_factorizations.ord(list(f), sorted(z2+t)) == -1 and \
                                all_factorizations.ord(z, z2) == 99 and len(z2) != 1 and len(z) != 1:
                                all_factorizations.register_lt(z, z2)
                                state.logger.info("   %s < %s based on %s",z,z2,f)
                                lowest = min(lowest, all_factorizations.reverse_idx[tuple(z)][0])
    return lowest
