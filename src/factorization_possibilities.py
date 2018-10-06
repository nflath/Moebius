import collections
from util import *

class FactorizationPossibilities(object):
    # Represents the 'tree' of factorization possibilities.  Not represented as
    # a tree for performance reasons; instead, a list-of-lists, where
    # all_factorizations[i] is a list of all possible factorizations of i.

    def __init__(self, logger):
        # List of lists; each index is all possibilities for that n (starts at n=2).
        self.all_factorizations = []

        # Which indexes a factorization possibily can be in
        self.reverse_idx = collections.defaultdict(list)

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
        self.finished = set()

        # All the factorizations we have generated that are not finished.
        self.outstanding = set()

        # Outside-provided information about lt.
        self.lt_cache = {}

    def __eq__(self, other):
        return self.all_factorizations == other.all_factorizations

    def compare_and_print(self, other):
        for x in range(0, len(self.all_factorizations)):
            if self.all_factorizations[x] != other.all_factorizations[x]:
                print("  %d: %s\t\t%s" % (x+2,str(self.all_factorizations[x]), str(other.all_factorizations[x])))

    def Update(self, new_factorizations):
        """Add factorizations for the next n and update internal state.

        Returns all the factorizations that are now 'finished'."""

        self.all_factorizations += [sorted(new_factorizations)]

        n = len(self.all_factorizations) - 1
        for z in self.all_factorizations[n]:
            self.reverse_idx[tuple(z)].append(n)

        return self.update_outstanding_and_finished(new_factorizations)

    def update_outstanding_and_finished(self, new):
        """Updates which factorizations are finished vs outstanding."""

        new_outstanding = set()
        new_finished = set()

        outstanding = self.outstanding

        # Every new item starts as outstanding
        for n in new:
            outstanding.add(tuple(n))

        # If there are enough smaller and equivalent items transitively sharing
        # space with an item that it must be added, transition to finished.
        # FixMe: Do I need all of these new_outstandings? or new_finished?
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

        # If an item in outstanding is less than every newly-generated
        # possibility, transition it to finished.
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


        # If an item in outstanding is less than any item in finished, the
        # outstanding item transitions to finished.
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
            # If there is only one new item, it is finished.
            #FixMe: Is this necessary or does one of the above checks always hit it?
            new_finished.add(tuple(new[0]))
        else:
            for x in new:
                if tuple(x) not in outstanding and \
                  tuple(x) not in self.finished and \
                  tuple(x) not in new_finished:
                    outstanding.add(tuple(x))
        self.finished |= new_finished
        self.outstanding = outstanding

        # Sanity check
        for f in self.finished:
            assert f not in self.outstanding

        return new_finished

    def shared(self, f):
        """Return factorizations transitively sharing a 'n' with f.

        Returns the factorizations that transitively share 'n' with f.
        IE, if f,y,z are possibilities for n, and y,z,a are
        possibilitieis for n', will return ((n,n'),(y,z,a)).
        """

        items = set()
        positions = set()

        # Add all positions/items that directly share with f
        for p in self.reverse_idx[tuple(f)]:
            positions.add(p)
            for i in self.all_factorizations[p]:
                items.add(tuple(i))

        start_positions = len(positions)

        # Continue iterating until no changes
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
        # FixMe: Extract to state
        self.lt_cache[(tuple(t),tuple(o))] = -1
        self.lt_cache[(tuple(o),tuple(t))] = 1

    def ord_absolute(self, t, o):
        """Is t < o, with simplification (usually use this)."""
        t, o = simplify(t,o)
        return self.ord(t, o)

    def ord(self, t, o):
        """ Returns whether t < o (no simplification)."""

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
