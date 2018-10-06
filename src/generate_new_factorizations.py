from util import *

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
    """ Return if, for any f in p_idx, p * f <~ p' * max_idx[p'] """

    # Always continue if p == 2, this is the base case.
    if p == 2: return False

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
                # possibility is p * f, where f is some factorization for p_idx

                # p_prime_possibility is p' * f', where f' is some
                # factorization in the maximum location p' has reached. p' < p.
                # If there is any p' * f' that is not provably greater than p *
                # f, continue extending n.
                if (all_factorizations.ord_absolute(possibility, p_prime_possibility) != 1):
                  # At least one possibility is not provably >
                  can_continue = True
    if not can_continue:
        return True
    return False

def GenerateNewFactorizations(n, all_factorizations):
   """Generate all possible factorizations for n without filtering.

   For each n, finds all factorizations not generated so far < 2 * n.

   Continues until there are enough factorizations generated, meaning
   not all the possibilities can fin in all_factorizations at the same
   time(and so we would only be generating larger ones that we can't
   use).  Then, expand to all factorizations where we are unsure if
   they are > 2 * n or not.
   """

   # For each prime, what is the next index to process
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
       # For each prime, extend as far as possible without going over 2 * z_idx.
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
                # end for f in all_factorizations[p_idx]:
            # end for p_idx in range(p_start_idx, z_idx+1):
        # end for p in prime


       prime_location_map = new_locs
       if results and should_stop_search(n, results, all_factorizations):
           break
    # end for z_idx in range(0, len(all_factorizations)

   # Expand the results with all factorizations we don't know are larger than
   # any in results.
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
       # Always add self as a possible prime if moebius is here.
       results.add(tuple([n]))

   return [list(x) for x in results]
