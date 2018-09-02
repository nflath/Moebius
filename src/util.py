import pdb
import copy
import collections

class memoized(object):
   '''Decorator. Caches a function's return value each time it is called.
   If called later with the same arguments, the cached value is returned
   (not reevaluated).
   '''
   def __init__(self, func):
      self.func = func
      self.cache = {}
   def __call__(self, *args):
      if args in self.cache:
         return self.cache[args]
      else:
         value = self.func(*args)
         self.cache[args] = value
         return value
   def __repr__(self):
      '''Return the function's docstring.'''
      return self.func.__doc__
   def __get__(self, obj, objtype):
      '''Support instance methods.'''
      return functools.partial(self.__call__, obj)

@memoized
def factorize(n):
    """Returns the factorization of n"""
    if n == 1: return []

    assert n > 1
    factors = []
    for i in range(2, n + 1):
        while (n % i) == 0:
            return [i] + factorize(int(n/i))
    if n != 1:
        pdb.set_trace()
    assert n == 1
    return factors

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


def tupletized(l):
    """ Return a version of the list of lists that is entirely in tuples."""
    # FixMe: convert everything to just be tuples

    return tuple([tuple(x) for x in l])

def generate_all_possible_lists(lst, start_idx=0, end_idx=0, check_primality=True, idx=0, primes = set(), retn=[]):
    """ Yields each possible list, where each index in lst is a list of possibilities.

    The same possibility cannot be chose more than once."""
    if len(lst) == []:
        yield lst
    elif not retn:
        if not end_idx:
            end_idx = len(lst)

        retn = [x[0] for x in lst[:end_idx]]
        primes = set()

        for y in generate_all_possible_lists(lst, start_idx, end_idx, check_primality, start_idx, primes, retn):
            yield y
    elif idx == end_idx:
        if idx < len(retn):
            for x in lst[:idx]:
                retn[idx] = x
            yield retn
        else:
            yield retn
    else:
        for x in lst[idx]:
            if x in retn[:idx]:
                continue

            retn[idx] = x
            c = True
            if len(retn[idx]) == 1:
                primes.add(tuple(retn[idx]))
            elif check_primality:
                for z in x:
                    if tuple([z]) not in primes:
                        c = False
                        break
            if not c:
                continue
            for y in generate_all_possible_lists(lst, start_idx, end_idx, check_primality, idx + 1, primes, retn):
                yield y

        if len(retn[idx]) == 1:
            try:
                primes.remove(tuple(retn[idx]))
            except:
                pdb.set_trace()


def generate_all_possible_lists_for_mask(lst, mask, idx=0, retn=[]):
    """ Yields each possible list, where each index in lst is a list of possibilities.

    The same possibility cannot be chose more than once."""
    if len(lst) == 0:
        yield lst

    elif not retn:
        #retn = [x[0] for x in lst]
        retn = []
        for x in generate_all_possible_lists(lst):
            retn = x
            break
        for y in generate_all_possible_lists_for_mask(lst, mask, idx, retn):
            yield y
    elif idx == len(retn):
        yield retn
    else:
        if mask[idx]:
            for x in lst[idx]:
                if x in retn[:idx]:
                    continue
                retn[idx] = x
                for y in generate_all_possible_lists_for_mask(lst, mask, idx + 1, retn):
                    yield y
        else:
            if retn[idx] in retn[:idx]:
                for z in lst[idx]:
                    if z not in retn[:idx]:
                        retn[idx] = z
                        break
            if retn[idx] in retn[:idx]:
                return
            for y in generate_all_possible_lists_for_mask(lst, mask, idx + 1, retn):
                yield y

scache = {}
def simplify(this, other):
    """ Remove all common factors in this and other.

    For example, (2,2,2,2) and (2,2,5) simplifies to (2,2) and (5)."""

    ts = tuple(this)
    to = tuple(other)

    global scache
    try:
        if (ts, to) in scache:
            return scache[(ts, to)]
    except:
        pdb.set_trace()

    t_i = 0
    o_i = 0
    t = []
    o = []
    while(t_i < len(this) and o_i < len(other)):
        if this[t_i] < other[o_i]:
            t.append(this[t_i])
            t_i += 1
        elif this[t_i] > other[o_i]:
            o.append(other[o_i])
            o_i += 1
        elif(this[t_i] == other[o_i]):
            t_i += 1
            o_i += 1
    if t_i < len(this):
        t += this[t_i:]
    if o_i < len(other):
        o += other[o_i:]
    scache[(ts, to)] = (t, o)
    return t, o

class State(object):

    def __init__(self):
        self.start = {0: 0, -1: 0, 1: 0}
        # Currently unused

        self.end = {0: 0, 1: 0, -1: 0}
        # For each moebius value, which parts of the possibilities list we need to
        # iterate over to generate all possible values.  This is a performance
        # enhancement.  For example, at n=6, we start with the array: [ [2], [3],
        # [2, 2], [5], [2,3]].  We know that next time we generate possibilities
        # for a moebius value of 1, we don't have to go past [2,5] - start will be
        # 0 and end will be 3.  Then, when we get to n=10 (the next n with a
        # moebius value of 0), we don't need to generate possibilities twice, even
        # though there are two possible factorization arrays.

        self.eliminate = collections.defaultdict(list)
        # All the possibilities we have eliminated based on various analzsis

        self.start_for_n = {}
        self.end_for_n = {}
        self.possibilities_for_n = {}
        # Used for resetting when backtracking

        self.primes_starting_cache = {-1: {}, 0 : {}, 1: {}}
        self.all_factorizations = FactorizationPossibilities()
        self.n = 2
        self.i = 1

    def __eq__(self, other):
        return \
          self.n == other.n and \
          self.i == other.i and \
          self.all_factorizations == other.all_factorizations# and \
          #self.start == other.start and \
          #self.end == other.end and \
          #self.eliminate == other.eliminate and \
          #self.start_for_n == other.start_for_n and \
          #self.end_for_n == other.end_for_n and \
          #self.possibilities_for_n == other.possibilities_for_n and \
          #self.primes_starting_cache == other.primes_starting_cache

    def compare_and_print(self, other):
        print("DIFFERENCES")
        if self.n != other.n: print("n: %d vs %d", self.n, other.n)
        if self.n != other.n: print("i n: %d vs %d", self.i, other.i)
        self.all_factorizations.compare_and_print(other.all_factorizations)

    def __str__(self):
        return "{ n: %d i: %d }" % (self.n, self.i)

class FactorizationPossibilities(object):
    # Represents the 'tree' of factorization possibilities.  Not represented as
    # a tree for performance reasons; instead, a list-of-lists, where
    # all_factorizations[i] is a list of all possible factorizations of i.
    #
    # Fields: all_factorizations - the master list of lists
    # reverse_idx: Maps from a factorization to each index it is located in.
    # Finished - All factorizations that will not appear as a possibility in a future
    #   index
    # Outstanding - All factorizations that are in the list that may appear
    # in a future index

    # FixMe: Move more functionality into this class:
    #   - (index_recursive)
    #   - Updating finished/outstanding/reverse_idx

    def __init__(self):
        self.all_factorizations = []
        self.reverse_idx = collections.defaultdict(list)
        self.finished = set()
        # Set of factorizations that are 'finished', IE they will not be generated
        # as possibilities in any future iterations.  This can occur for two reasons:
        #
        #   1) Any arrangement of possible factorizations will have this factor.
        #      For example, both n=8 and n=9 generate (2,2,2) and (3,3) as their
        #      possibilities - so at this point, they will always be generated in
        #      some arrangement.
        #
        #   2) A larger number has been finished.  For example, (2,3,5) is finished
        #      once we isolate 36=(2,2,3,3).

        self.outstanding = set()
        # All the factorizations we have generated that are not finished.

        self.lt_cache = {}

    def __eq__(self, other):
        return \
          self.all_factorizations == other.all_factorizations and \
          self.finished == other.finished and \
          self.outstanding == other.outstanding
          #self.reverse_idx == other.reverse_idx and \

    def compare_and_print(self, other):
        for x in range(0, len(self.all_factorizations)):
            if self.all_factorizations[x] != other.all_factorizations[x]:
                print("  %d: %s\t\t%s" % (x+2,str(self.all_factorizations[x]), str(other.all_factorizations[x])))

    def update_reverse_idx(self):
        # Should be called after updating self.all_factorizations FixMe: Should
        # not be exposed externally, there should be some function that
        # updates all_factorizations, finsihed, outstanding, reverse_idx atomically

        n = len(self.all_factorizations) - 1
        for z in self.all_factorizations[n]:
            self.reverse_idx[tuple(z)].append(n)

    def update_outstanding_and_finished(self, new):
        outstanding_count = collections.defaultdict(lambda : 0)
        # For each outstanding factorization, how many trees exists where the
        # factorization either exists or is less than everything in new.

        total = 0
        # Total number of lists we generate

        new_outstanding = set()
        new_finished = set()

        outstanding = self.outstanding

        for n in new:
            if tuple(n) not in self.finished:
                outstanding.add(tuple(n))

        for o in self.outstanding:
            s, i = self.shared(o)
            lt = []
            gt = []
            equiv = []

            for n in i:
                r = self.ord_absolute(n, o)
                if r == -1:
                    lt += [n]
                elif r == 1:
                    gt += [n]
                else:
                    equiv += [n]
            if len(s) >= len(lt)+len(equiv):
                new_finished.add(o)
            else:
                new_outstanding.add(o)

        outstanding = copy.copy(new_outstanding)
        new_outstanding = set()
        for o in outstanding:
            all_lower = True
            for y in new:
                if self.ord_absolute(o,y) > -1:
                    all_lower = False
                    break
            if all_lower:
                new_finished.add(o)
            else:
                new_outstanding.add(o)


        #LT anything that's finished
        outstanding = new_outstanding
        new_outstanding = set()
        for o in outstanding:
            for y in self.finished:
                if self.ord_absolute(o,y) == -1:
                    new_finished.add(o)
                    break
            if o not in new_finished:
                new_outstanding.add(o)
        outstanding = new_outstanding

        if len(new)==1:
            new_finished.add(tuple(new[0]))
        else:
            for x in new:
                if tuple(x) not in outstanding and \
                  tuple(x) not in self.finished and \
                  tuple(x) not in new_finished:
                    outstanding.add(tuple(x))
        self.finished |= new_finished
        self.outstanding = outstanding

        for f in self.finished:
            assert f not in self.outstanding

        return new_finished

    def shared(self, f):
        items = set()
        positions = set()
        expand = set()
        for p in self.reverse_idx[tuple(f)]:
            positions.add(p)
            for i in self.all_factorizations[p]:
                items.add(tuple(i))

        start_positions = len(positions)

        while True:
            start_positions = len(positions)
            new_i = set()
            new_p = set()
            for f in items:
                for p in self.reverse_idx[tuple(f)]:
                    new_p.add(p)
                    for i in self.all_factorizations[p]:
                        new_i.add(tuple(i))
            positions = positions.union(new_p)
            items = items.union(new_i)
            if len(positions) == start_positions:
                break

        return positions, items

    def register_lt(self, t, o):
        #pdb.set_trace()
        self.lt_cache[(tuple(t),tuple(o))] = -1
        self.lt_cache[(tuple(o),tuple(t))] = 1

    def ord_absolute(self, t, o):
        t, o = simplify(t,o)
        return self.ord(t, o)

    def ord(self, t, o):
        """ Returns whether t < o given the entire list of factorizations.  """

        if not t and not o:
            return 0

        if not t:
            return -1

        if not o:
            return 1

        t = tuple(t)
        o = tuple(o)

        if (t,o) in self.lt_cache:
            return self.lt_cache[(t,o)]

        if t == o: return 0
        t_found = self.reverse_idx[t]
        o_found = self.reverse_idx[o]
        t_first_idx = None
        t_last_idx = None
        o_first_idx = None
        o_last_idx = None
        if t_found:
            t_first_idx = self.reverse_idx[t][0]
            t_last_idx = self.reverse_idx[t][-1]
        if o_found:
            o_first_idx = self.reverse_idx[o][0]
            o_last_idx = self.reverse_idx[o][-1]



        if not t_found and not o_found:
            return 99

        if t_found and not o_found and tuple(t) in self.finished:
            return -1

        if o_found and not t_found and tuple(o) in self.finished:
            return 1


        if tuple(t) not in self.finished and tuple(o) not in self.finished:
            return 99

        elif tuple(t) not in self.finished and o_last_idx < t_first_idx:
            return 1

        elif tuple(t) not in self.finished:
            return 99

        elif t_last_idx < o_first_idx:
            return -1

        elif o_last_idx < t_first_idx:
            return 1

        return 99

    def __getitem__(self, key):
        return self.all_factorizations[key]

    def __len__(self):
        return len(self.all_factorizations)
