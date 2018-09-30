import math
import pickle
import collections
import pdb
import copy
import cProfile
import sys
import itertools
import logging
from functools import reduce
from util import *
from filters import *
from eliminate_z_analysis import all_eliminations
from eliminate_gt import EliminateBasedOnGt
from eliminate_locked import EliminateLocked
from generate_new_factorizations import GenerateNewFactorizations

ENABLE_TESTS = True
# FixMe: Factorizations should always be represented as a tuple.

def CreateLogger():
    """Set up the global logger to be used by this module."""
    logger = logging.getLogger('Moebius')
    logger.setLevel(logging.DEBUG)
    fh = logging.FileHandler('log.log')
    fh.setLevel(logging.DEBUG)
    ch = logging.StreamHandler()
    ch.setLevel(logging.INFO)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    fh.setFormatter(formatter)
    ch.setFormatter(formatter)
    logger.addHandler(fh)
    logger.addHandler(ch)
    return logger

def VerifySameAsTestdataIfCheckEnabled(state):
    if not ENABLE_TESTS:
        return
    try:
        test_state = pickle.load(open("testdata/n=%di=%d"%(state.n, state.i), "rb"))
        test_state.n = int(test_state.n)
        if test_state != state:
            state.compare_and_print(test_state)
        assert test_state == state
    except FileNotFoundError as e:
        pass

def VerifyRealFactorizationGenerated(state, new):
    if factorize(state.n) in new:
        return

    print(1, "[[1]]")
    for i in range(0, len(state.all_factorizations)):
        print(i + 2, state.all_factorizations[i])
    print(new)
    pdb.set_trace()
    assert factorize(n) in new # Will always fail

def generate_factorization_possibilities(max_n, state):
    """Generates possible factorizations from state.n to max_n."""
    state.logger.info("Program begin")

    while state.n <= max_n:
        state.logger.info("Processing n=%d i=%d moebius=%d"%(state.n,state.i,moebius(state.n)))

        pickle.dump(state, open("saves/n=%di=%d"%(state.n, state.i),"wb"))

        VerifySameAsTestdataIfCheckEnabled(state)

        state.possibilities_for_n[state.n] = copy.deepcopy(state.all_factorizations)

        new = GenerateNewFactorizations(state.n, state.all_factorizations)

        new = [p for p in new if not IsEliminated(state, p)]
        new = [p for p in new if not IsLowerThanFinished(state, p)]
        new = [p for p in new if not IsLockedElsewhere(state, p)]
        new = [p for p in new if not SkipsLowerFactorization(state, p)]
        new = [p for p in new if not IsTooHigh(state, new, p)]

        VerifyRealFactorizationGenerated(state, new)

        state.all_factorizations.all_factorizations += [sorted(new)]
        state.all_factorizations.update_reverse_idx()
        new_finished = state.all_factorizations.update_outstanding_and_finished(new)

        lowest = EliminateBasedOnGt(state, new_finished)
        lowest = min(lowest, EliminateLocked(state))




        if lowest != state.n - 2:
            #pdb.set_trace()
            state.n = lowest+2
            state.i += 1
            lt_cache = state.all_factorizations.lt_cache
            state.all_factorizations = state.possibilities_for_n[state.n]
            state.all_factorizations.lt_cache = lt_cache
            continue

        if new_finished:
            new_eliminate, new_z_calculated = all_eliminations(state, new_finished)

            if new_eliminate:
                # For all of our new elimination candidates, update
                # all_factorizations and reset to continue calculations from
                # the lowest point we changed

                min_ = state.n-2
                for x in new_eliminate:
                    if x[1] in state.all_factorizations[x[0]]:
                        min_ = min(min_,x[0])
                        if [x[1]] not in state.eliminate[x[0]]:
                            state.eliminate[x[0]] += [x[1]]
                state.n = min_+2
                state.i += 1

                glt_cache = state.all_factorizations.lt_cache
                state.all_factorizations = state.possibilities_for_n[state.n]
                state.all_factorizations.lt_cache = lt_cache
                continue

        # End of the loop; update n
        state.n += 1

    return state.all_factorizations

if __name__ == "__main__":
    def main():
        logger = CreateLogger()
        state = State()
        if len(sys.argv) > 2:
            import pickle
            state = pickle.load(open(sys.argv[2],"rb"))
            state.n = int(state.n)
        state.logger = logger
        f = generate_factorization_possibilities(int(sys.argv[1]), state)
        print(1, "[[1]]")
        for n in range(0, len(f)):
            print(n + 2, f[n])

    main()
