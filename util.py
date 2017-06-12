
debug_n = 7

import collections
import functools

class Node():
    """ Represents one node of the factorization tree.

    Contains one possible factorization of 'n'. """
    def __init__(self, n, factors, parent):
        self.n = n
        self.dead = False
        self.dead_reason = None
        self.factors = factors
        self.children = []
        self.parent = parent

        # Memoizations
        self._flatten = None
        self._primes = None
        self._prime_factorizations = [None] * self.n
        self.Z = self.calculated_Z()

        # On construction, add self to parent
        if self.parent:
            self.parent.children += [self]

    def clean(self):
        """ Cleans the tree by marking nodes as dead if all their children are dead."""

        for c in self.children:
            c.clean()
        all_children_dead = True
        if not self.children:
            return
        for c in self.children:
            if not c.dead:
                all_children_dead = False
        if all_children_dead:
            self.dead = True
            self.dead_reason = "ALL_CHILDREN_DEAD"

    def pp_clean(self, depth=0):
        """ Prints the tree, omitting nodes that are dead. """

        if depth==0:
            self.clean()
        if self.dead:
            return
        print "  " * depth,
        print self.n, ": ", str(self.factors), self.Z
        for c in self.children:
            c.pp_clean(depth + 1)


    def pp(self, depth=0):
        """ Prints the tree, including dead nodes."""
        print "  " * depth,

        print self.n, ":", str(self.factors), self.Z,
        if self.dead:
            print self.dead_reason
        else:
            print
        for c in self.children:
            c.pp(depth+1)

    def calculated_Z(self):
        """ Calculate Z based on this tree. """
        # FixMe: Slow.  Optimize

        r = 0
        f = self.flatten()
        x = []

        # FixMe: actually do this
        return


        for p in self.primes():
            # How many p^2 * A < self.factors for each p? Sum them up.

            if p in self.factors:
                 i = self.factors.index(p)
                 remaining_factors = self.factors[:i]+self.factors[i+1:]

                 # If we have p^2 * A < p * remaining_factors,
                 # then calculate p * A < remaining_factors

                 if not remaining_factors:
                     return len(x)

                 # All factors < remaining__factors
                 all_remaining = f[:f.index(remaining_factors)]

                 if [p] in all_remaining:
                     x += [[p]]
                 else:
                     continue

                 for a in all_remaining:
                     tmp = sorted([p] + a)
                     if tmp not in all_remaining:
                         break
                     x += [tmp]

            else:
                if [p,p] in f:
                    x += [[p,p]]
                else:
                    continue

                for a in f:
                    tmp = sorted([p,p]+a)
                    if tmp in f:
                        x += [tmp]
                    else:
                        break
        return len(x)


    def possible_new_unique_prime_factorizations(self, length):
        """Returns all possible new factorizations of given length as a list.

        The factorizations will not contain duplicates.
        """
        if length == 1:
            # Just return the next number as a prime
            return [[self.n+1]]

        n = []
        primes = self.primes()
        r = self.prime_factorizations(length-1)
        c = self.prime_factorizations(length)
        smallest = None
        a = self.flatten()



        for potential in r:
            for p in primes:
                # Iterate through all factorizations of length-1.  Find the
                # lowest prime which multiplying by is not already in the list
                # of factorizations.
                possibility = sorted(potential + [p])

                if p == smallest:
                    break
                if possibility in n or len(possibility) != len(set(possibility)):
                    # Alread found this.
                    break
                if possibility not in c:
                    exit = False
                    for f in a:
                        x = sorted([p] + f)
                        if f == potential:
                            break
                        elif x not in a:
                            exit = True
                            break
                    if not exit:
                        n += [possibility]
                        smallest = p
                    break

        return n

    def flatten(self):
        """Return all factorizations in order as a list."""
        if self._flatten is None:
            if self.parent and self.parent._flatten:
                self._flatten = self.parent._flatten + [self.factors]
            else:
                r = []
                curr = self
                while curr and curr.factors:
                    r += [curr.factors]
                    curr = curr.parent
                r.reverse()
                self._flatten = r[1:]
        return self._flatten


    def prime_factorizations(self, length):
        """ Return all possible prime factorizations in this tree of the given 'length'. """
        r = []
        current = self
        while current:
            if len(current.factors)==length:
                r += [current.factors]
            current = current.parent
        r.reverse()
        if length == 1:
            return r[1:]
        else:
            return r

    def primes(self):
        """ Return all primes in this tree. """
        if self._primes is None:
            self._primes = [x[0] for x in self.prime_factorizations(1)]
        return self._primes

    # 27
    def smallest_new_factorizations_with_square(self):
        """Return the smallest possible new factorization that contains a replicated prime.
        """

        factorizations = self.flatten()
        r = []

        smallest_factorization = None
        for p in self.primes():
            for f in factorizations:
                if f is smallest_factorization:
                    # We've already found a smaller factorization; no need to go farther
                    break
                found = False
                tmp = sorted(f + [p])
                if p in f:
                    if tmp not in factorizations:
                        # Multiplying the lowest factorization by p is a possibility.
                        r += [tmp]
                        found = True
                        smallest_factorization = f
                        break
                elif tmp not in factorizations:
                    if len(set(f)) != len(f) and p not in f:
                        # The current factorization already has a duplicate;
                        # just multiply it by p.
                         r += [tmp]
                         found = True
                         smallest_factorization = f
                    break
                if found:
                    break
        return r
