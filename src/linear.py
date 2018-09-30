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
from eliminate_gt import eliminate_based_on_gt

ENABLE_TESTS = True
# FixMe: Factorizations should always be represented as a tuple.

def setupLogger():
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

def should_stop_search(n, possibilities, all_factorizations):
    # We should stop the search if it's not possible for all of the possibilities
    # to be in all_factorizations at the same time.
    locs = set()
    items = set()
    for possibility in possibilities:
        for idx in all_factorizations.reverse_idx[possibility]:
            locs.add(idx)
            for i in all_factorizations[idx]:
                items.add(tuple(i))
    return len(possibilities) > (len(locs))

def should_stop_prime(n, p, p_idx, new_locs, primes, all_factorizations, check_all = False):
    if p == 2: return False
    #if n == 4: pdb.set_trace()
    can_continue = False
    p_loc = primes.index(p)
    p_max = p_loc
    if check_all:
        p_loc = len(primes)
    for f in all_factorizations[p_idx]:
        possibility = sorted(f+[p])

        for p_prime in primes[:p_loc]:
            if new_locs[p_prime] == 0:
                return True
            for f in all_factorizations[new_locs[p_prime]-1]:
                p_prime_possibility = sorted([p_prime] + f)
                if (all_factorizations.ord_absolute(possibility, p_prime_possibility) != 1):
                  # At least one possibility is not provably >
                  can_continue = True
    if not can_continue:
        return True
    return False

def generate_possibilities_via_all_factorizations(n, all_factorizations):
   prime_location_map = {}
   prime_max_location_map = {}
   primes = []
   results = set()
   m = moebius(n)
   for z_idx in range(0, len(all_factorizations)):
       for f in all_factorizations[z_idx]:
           if len(f) == 1:
               primes += f
               prime_location_map[f[0]] = 0

       new_locs = {}
       for p in primes:
           p_start_idx = prime_location_map[p]
           for p_idx in range(p_start_idx, z_idx+1):
               stop = should_stop_prime(n,p,p_idx,new_locs,primes,all_factorizations)
               if stop:
                   new_locs[p] = p_idx
                   break
               new_locs[p] = p_idx+1
               for f in all_factorizations[p_idx]:
                   possibility = sorted(f+[p])
                   if (m == 0 and len(possibility) == len(set(possibility))) or \
                     (m == 1 and (len(possibility) != len(set(possibility)) or len(set(possibility)) % 2 == 1)) or \
                     (m == -1 and (len(possibility) != len(set(possibility)) or len(set(possibility)) % 2 == 0)):
                       continue
                   if tuple(possibility) in all_factorizations.finished:
                       continue
                   results.add(tuple(possibility))

       prime_location_map = new_locs
       if results and should_stop_search(n, results, all_factorizations):
           break

   # Expand the results for all 'unsure'
   for p in primes:
         p_start_idx = prime_location_map[p]
         #if p == 3: pdb.set_trace()
         for p_idx in range(p_start_idx, len(all_factorizations)):
             can_continue = not should_stop_prime(n, p, p_idx, prime_location_map, primes, all_factorizations, True)
             if can_continue:
                 for f in all_factorizations[p_idx]:
                     possibility = sorted(f+[p])
                     if (m == 0 and len(possibility) == len(set(possibility))) or \
                       (m == 1 and (len(possibility) != len(set(possibility)) or len(set(possibility)) % 2 == 1)) or \
                       (m == -1 and (len(possibility) != len(set(possibility)) or len(set(possibility)) % 2 == 0)):
                         continue
                     if tuple(possibility) in all_factorizations.finished:
                         continue
                     results.add(tuple(possibility))
             if not can_continue:
                 break

   if m == -1:
       results.add(tuple([n]))

   return [list(x) for x in results]

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
    """ Generates the list of possible factorizations from start_n to max_n. """
    global logger, calls, ord_cache

    state.logger.info("Program begin")

    while state.n <= max_n:
        state.logger.info("Processing n=%d i=%d moebius=%d"%(state.n,state.i,moebius(state.n)))
        n = state.n

        pickle.dump(state, open("saves/n=%di=%d"%(state.n, state.i),"wb"))

        VerifySameAsTestdataIfCheckEnabled(state)

        state.possibilities_for_n[n] = copy.deepcopy(state.all_factorizations)

        new = generate_possibilities_via_all_factorizations(n, state.all_factorizations)

        new = [p for p in new if not IsEliminated(state, p)]
        new = [p for p in new if not SkipsLowerPossibility(state, p)]
        new = [p for p in new if not IsLowerThanFinished(state, p)]
        new = [p for p in new if not IsLockedElsewhere(state, p)]
        new = [p for p in new if not IsTooHigh(state, new, p)]
        #new = filter(new, state.all_factorizations)

        VerifyRealFactorizationGenerated(state, new)

        state.all_factorizations.all_factorizations += [sorted(new)]
        state.all_factorizations.update_reverse_idx()

        # Update the outstanding and finished sets.  new_finished is the
        # outstanding factorizations that we finished at this n.
        new_finished = state.all_factorizations.update_outstanding_and_finished(new)
        lowest = eliminate_based_on_gt(state, new_finished)

        if len(state.all_factorizations[-1]) == 1:
            state.locked[tuple(state.all_factorizations[-1][0])] = n
            if len(state.all_factorizations.reverse_idx[tuple(state.all_factorizations[-1][0])]) > 1:
                lowest = min(lowest,
                            state.all_factorizations.reverse_idx[tuple(state.all_factorizations[-1][0])][0]-2)


        if lowest != n - 2:
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

                min_ = n-2
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
        logger = setupLogger()
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
