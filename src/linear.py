# TODO:
# 51 [[3, 17], [5, 11]]
# 52 [[2, 2, 13], [2, 3, 3, 3], [7, 7]]

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
from moebiusutil import *
from util import *

ENABLE_Z1 = True
# FixMe: Factorizations should always be represented as a tuple.

# Global logger
logger = None

def setupLogger():
    """Set up the global logger to be used by this module."""
    global logger
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

    try:
        t_index = factorizations.index(t)
    except:
        pass

    try:
        o_index = factorizations.index(o)
    except:
        pass

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

def ord_(t, o, factorizations):
    """Returns whether this < other for a specific factorization possibility.

    Check each permutation and 2-way split of this and other to try and
    find one where both parts of this are less than the parts of
    other.

    Returns -1 if t < o, 0 if t == o, 1 if t > o.
    """
    if not t and not o or t == o:
        return 0
    if not t:
        return -1
    if not o:
        return 1

    t_index = None
    o_index = None

    try:
        t_index = factorizations.index(t)
    except:
        pass

    try:
        o_index = factorizations.index(o)
    except:
        pass

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

def prune_elements_lt(n, factorizations, factorization, all_factorizations):
    """Remove all elements in factorizations that are less than another element in factorizations
    """
    keep = []
    for x in range(0, len(factorizations)):

        if len(factorizations) == 1:
            keep += [factorizations[x]]
            continue

        x_greater_than_all = True

        for y in range(0, len(factorizations)):
            if x == y: continue
            if all_factorizations.ord_absolute(factorizations[x],
                            factorizations[y]) != 1:
                x_greater_than_all = False
                break
        if not x_greater_than_all:
            keep += [factorizations[x]]
        else:
            #if moebius(n) == 0: pdb.set_trace()
            pass
    return keep

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
                        #if z == [2,3,5]: pdb.set_trace()
                        mask[y][x_idx] = True
                    tup = (sorted([p,p] + z),)
                    if ENABLE_Z1 or True : tup = (sorted([p,p] + z), sorted([p]+z))
                    for v in tup:

                        val = all_factorizations.ord_absolute(v,y)

                        if tuple(v) == y:
                            #pdb.set_trace()
                            if x_idx == 53: pdb.set_trace()
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

def analyze_z_for_factorizations_mask(n, all_factorizations, new_finished, mask):
    eliminate = []
    for y in mask:
        if len(y) == 1: continue
        logger.debug("  About to analyze masked Z for y="+str(y)+" "+str(mask[y]))

        cnt = 0
        for x in generate_all_possible_lists_for_mask(all_factorizations, mask[y]):
            cnt += 1
        logger.debug("  Count = "+str(cnt))

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

                if ENABLE_Z1:
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
               logger.info("  Mask Eliminating [n=%d,%s] based on: %s " % (idx+2,str(z),str(y)))
               eliminate += [[idx, z]]
               if z == factorize(idx+2):
                   pdb.set_trace()
                   assert False
        logger.debug("  Done analyzing masked Z for y="+str(y))

    return eliminate


def all_eliminations(n, all_factorizations, new_finished):
    """ Returns factorizations for positions we can show are impossible. """
    global logger

    mask = ranges_for_z_calculations(n, all_factorizations, new_finished)
    e_ = analyze_z_for_factorizations_mask(n, all_factorizations, new_finished, mask)

    return e_, []

def filter(new, all_factorizations):
    # Filter out too-high values(more than enough space for all lower values)
    new_new = []
    for f in new:
        lt = []
        gt = []
        equiv = []
        p, i = all_factorizations.shared(f)
        if len(p) == 0:
            for x in new:
                p_, i_ = all_factorizations.shared(x)
                p = p.union(p_)
                i = i.union(i_)
                #pdb.set_trace()
                i.add(tuple(x))

        for n in i:
            r = all_factorizations.ord_absolute(n, f)
            if r == -1:
                lt += [n]
            elif r == 1:
                gt += [n]
            else:
                equiv += [n]
        if len(p)+1 > (len(lt)):
            # It is possible for a lower value to be present
            new_new += [f]

    return new_new

def eliminate_based_on_gt(n, all_factorizations, new_finished):
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
                    logger.info("   %s < %s based on %s",o,t,f)
                    lowest = min(lowest, all_factorizations.reverse_idx[tuple(o)][0])
                if all_factorizations.ord(list(z), list(f)) == 1 and all_factorizations.ord(t,o) == 99:
                    all_factorizations.register_lt(t,o)
                    logger.info("   %s < %s based on %s",t,o,f)
                    lowest = min(lowest, all_factorizations.reverse_idx[tuple(t)][0])
                if (all_factorizations.ord(list(t), list(o)) == 1 and all_factorizations.ord(list(f),list(z)) == 99):
                    all_factorizations.register_lt(z,f)
                    logger.info("   %s < %s based on %s",z,f,f)
                    lowest = min(lowest, all_factorizations.reverse_idx[tuple(z)][0])
                if all_factorizations.ord(list(o), list(t)) == 1 and all_factorizations.ord(list(z),list(f)) == 99:
                    all_factorizations.register_lt(f,z)
                    logger.info("   %s < %s based on %s",f,z,f)
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
                                logger.info("   %s < %s based on %s",z2,z,f)
                                lowest = min(lowest, all_factorizations.reverse_idx[tuple(z2)][0])
                            if all_factorizations.ord(list(f), sorted(z2+t)) == -1 and \
                                all_factorizations.ord(z, z2) == 99 and len(z2) != 1 and len(z) != 1:
                                all_factorizations.register_lt(z, z2)
                                logger.info("   %s < %s based on %s",z,z2,f)
                                lowest = min(lowest, all_factorizations.reverse_idx[tuple(z)][0])
    return lowest

def generate_factorization_possibilities(max_n, state):
    """ Generates the list of possible factorizations from start_n to max_n. """
    global logger, calls, ord_cache

    logger.info("Program begin")

    while state.n <= max_n:
        n = state.n
        m = moebius(n)

        # Test
        #test_state = pickle.load(open("saves/n=%di=%d"%(state.n, state.i)))
        #test_state=n = int(test_state.n)

        logger.info("Processing n=%d i=%d moebius=%d"%(n,state.i,m))

        pickle.dump(state, open("saves/n=%di=%d"%(state.n, state.i),"wb"))

        # try:
        #    test_state = pickle.load(open("testdata/n=%di=%d"%(state.n, state.i), "rb"))
        #    test_state.n = int(test_state.n)
        #    if test_state != state:
        #        state.compare_and_print(test_state)
        #        assert False
        # except:
        #     pass
        #assert test_state == state



        state.possibilities_for_n[n] = copy.deepcopy(state.all_factorizations)
        state.start_for_n[n] = copy.copy(state.start)
        state.end_for_n[n] = copy.copy(state.end)

        new = []
        # The array containing all the new values we generate.

        s = state.start[m]
        e = state.end[m]
        #e = -1

        state.end[m] = 0 # FixMe: What is this for?
        # Reset end so it can be set properly each iteration
        if e == -1 or e == 0: #here
            e = len(state.all_factorizations)


        logger.debug("  possibility generation: start: %d end: %d"%(s,e))


        logger.debug("  primes_starting_cache used: " + str(state.primes_starting_cache))
        new_primes_starting_cache = {}
        count = 0

        new = generate_possibilities_via_all_factorizations(n, state.all_factorizations)
        new = [x for x in new if x not in state.eliminate[n-2]]

        logger.debug("  # of options:"+str(count))
        new_new = []
        #pdb.set_trace()
        logger.debug("  Initial possibilities: %s"%(str(new)))
        for possibility in new:
            primes_finished = set()
            found_all = True
            for i in range(0, len(possibility)):
                # Go through all factorizations before 'potential' and ensure that no
                # factorization * p is lower than potential * p but doesn't exist.
                prime = possibility[i]
                if prime in primes_finished:
                    continue
                primes_finished.add(prime)
                other = possibility[:i] + possibility[i + 1:]
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
                new_new += [possibility]
        new = new_new

        new_new = []
        for possibility in new:
            found_lt = False
            for f in state.all_factorizations.finished:
                if state.all_factorizations.ord(possibility, f) == -1:
                    found_lt = True
            if not found_lt:
                new_new += [possibility]
        new = new_new


        logger.debug("  After filter1: %s"%(str(new)))

        new = filter(new, state.all_factorizations)
        logger.debug("  After filter2: %s"%(str(new)))

        # Remove all locked
        new_new = []
        lowest = n-2
        for possibility in new:
            if tuple(possibility) in state.locked and state.locked[tuple(possibility)] != n:
                continue
            new_new += [possibility]
        new = new_new

        if not factorize(n) in new or \
            (n == 92 and [2, 2, 2, 2, 2, 3] in new):
            print(1, "[[1]]")
            for i in range(0, len(state.all_factorizations)):
                print(i + 2, state.all_factorizations[i])
            print(new)
            pdb.set_trace()
            assert False

        assert factorize(n) in new
        state.all_factorizations.all_factorizations += [sorted(new)]
        state.all_factorizations.update_reverse_idx()

        # Update the outstanding and finished sets.  new_finished is the
        # outstanding factorizations that we finished at this n.
        new_finished = state.all_factorizations.update_outstanding_and_finished(new)
        #if n == 60: pdb.set_trace()
        lowest = min(lowest, eliminate_based_on_gt(n, state.all_factorizations, new_finished))
        logger.debug("  new_finished: %s"%str(new_finished))

        if len(state.all_factorizations[-1]) == 1:
            state.locked[tuple(state.all_factorizations[-1][0])] = n
            if len(state.all_factorizations.reverse_idx[tuple(state.all_factorizations[-1][0])]) > 1:
                lowest = min(lowest,
                            state.all_factorizations.reverse_idx[tuple(state.all_factorizations[-1][0])][0]-2)


        if lowest != n - 2:
            #pdb.set_trace()
            state.n = lowest+2
            state.i += 1
            state.primes_starting_cache = {-1: {}, 0 : {}, 1: {}}
            lt_cache = state.all_factorizations.lt_cache
            state.all_factorizations = state.possibilities_for_n[state.n]
            state.all_factorizations.lt_cache = lt_cache
            state.start = state.start_for_n[n]
            state.end = state.end_for_n[n]
            continue

        if new_finished:
            new_eliminate, new_z_calculated = all_eliminations(n, state.all_factorizations, new_finished)

            if new_eliminate:
                # For all of our new elimination candidates, update
                # all_factorizations and reset to continue calculations from
                # the lowest point we changed

                min_ = None
                for x in new_eliminate:
                    if x[1] in state.all_factorizations[x[0]]:
                        state.all_factorizations[x[0]].remove(x[1])
                        if not min_:
                            min_ = x[0]
                        min_ = min(min_,x[0])
                        if [x[1]] not in state.eliminate[x[0]]:
                            state.eliminate[x[0]] += [x[1]]
                state.n = min_+2
                state.i += 1

                state.primes_starting_cache = {-1: {}, 0 : {}, 1: {}}
                state.all_factorizations = state.possibilities_for_n[state.n]
                state.start = state.start_for_n[n]
                state.end = state.end_for_n[n]

                continue

        # End of the loop; update n
        state.n += 1

    return state.all_factorizations

if __name__ == "__main__":
    def main():
        setupLogger()
        state = State()
        if len(sys.argv) > 2:
            import pickle
            state = pickle.load(open(sys.argv[2],"rb"))
            state.n = int(state.n)
        f = generate_factorization_possibilities(int(sys.argv[1]), state)
        print(1, "[[1]]")
        for n in range(0, len(f)):
            print(n + 2, f[n])

    main()
