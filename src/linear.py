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
from generate_new_factorizations import GenerateNewFactorizations
from factorization_possibilities import FactorizationPossibilities
from state import State

ENABLE_TESTS = False
# FixMe: Factorizations should always be represented as a tuple.
# FixMe: Use sets where appropriate
# FixMe: Have a real command-line parser


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

        # Save the current state in order to be able to reload quickly
        # FixMe: Make optional
        pickle.dump(state, open("/Users/nflath/moebius/saves/n=%di=%d"%(state.n, state.i),"wb"))

        # If enabled, ensure we generated the same data as last run
        VerifySameAsTestdataIfCheckEnabled(state)

        state.all_factorizations_for_n[state.n] = copy.deepcopy(state.all_factorizations)

        # Generate all the possible new factorizations n could have based on
        # our current factorization possibilities.
        new = GenerateNewFactorizations(state.n, state.all_factorizations)

        # Filter out the new factorizations we generated in various ways
        new = [p for p in new if not IsEliminated(state, p)]
        new = [p for p in new if not IsLowerThanFinished(state, p)]
        new = [p for p in new if not IsLockedElsewhere(state, p)]
        new = [p for p in new if not IsOtherLockedForN(state, p)]
        new = [p for p in new if not SkipsLowerFactorization(state, p)]
        new = [p for p in new if not IsTooHigh(state, new, p)]

        if len(new) == 1:
            state.locked[tuple(new[0])] = state.n
            state.locked_n[state.n] = tuple(new[0])

        # Ensure we didn't filter out the real factorization for n
        VerifyRealFactorizationGenerated(state, new)

        # Update state with the newly-generated factorization possibilities for n
        new_finished = state.all_factorizations.Update(sorted(new))

        # Analyze full factorization list in a few ways to eliminate
        # previously-generated possibilities.
        lowest = EliminateBasedOnGt(state, new_finished)
        lowest = min(lowest, all_eliminations(state, new_finished))

        if lowest != state.n - 2:
            # We eliminated some previously-generated possibilities; jump back and
            # sstart processing from where we eliminated them.

            state.n = lowest+2
            state.i += 1
            lt_cache = state.all_factorizations.lt_cache
            state.all_factorizations = state.all_factorizations_for_n[state.n]
            state.all_factorizations.lt_cache = lt_cache
            continue

        # End of the loop; update n
        state.n += 1
    # end while state.n <= max_n:

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
