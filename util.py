
debug_n = 7

import collections
import functools

class Node():

    def __init__(self, n, factors, parent):
        self.n = n
        self.dead = False
        self.dead_reason = None
        self.factors = factors
        self.children = []
        self.parent = parent
        self._flatten = None
        self._primes = None
        self._prime_factorizations = [None] * self.n
        self.Z = self.calculated_Z()


        if self.parent:
            self.parent.children += [self]


    def clean(self):
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
        if depth==0:
            self.clean()
        if self.dead:
            return
        print "  " * depth,
        print self.n, ": ", str(self.factors), self.Z
        for c in self.children:
            c.pp_clean(depth + 1)


    def pp(self, depth=0):
        print "  " * depth,

        print self.n, ":", str(self.factors), self.Z,
        if self.dead:
            print self.dead_reason
        else:
            print
        for c in self.children:
            c.pp(depth+1)

    def calculated_Z(self):
        r = 0
        f = self.flatten()
        x = []

        if self.n < 36:
            return

        for p in self.primes():
            # How many p^2 * A < self.factors

            if p in self.factors:
                 i = self.factors.index(p)
                 remaining_factors = self.factors[:i]+self.factors[i+1:]
                 if not remaining_factors:
                     return len(x)
                 #print f.index(remaining_factors)
                 all_remaining = f[:f.index(remaining_factors)]

                 if [p] in all_remaining:
                     x += [p]

                 for a in all_remaining:
                     tmp = sorted([p] + a)
                     if tmp not in all_remaining:
                         break
                     #if sorted([p] + a) not in x: FixMe: Is this necessary?
                     x += tmp

            else:
                # pass, for now
                # FixMe: We need this.
                if [p,p] in f:
                    x += [[p,p]]

                for a in f:
                    tmp = sorted([p,p]+a)
                    if tmp in f:
                        x += tmp
        return len(x)



    def possible_new_unique_prime_factorizations(self, length):
        assert length > 1
        n = []
        primes = self.primes()
        r = self.prime_factorizations(length-1)
        c = self.prime_factorizations(length)
        smallest = None
        a = self.flatten()

        #for factorization in a:
            # [2]
            # [3] ([2 * 2])
            # [2 * 2] (2 * 3, 3 * 3)


        for potential in r:
            for p in primes:
                possibility = sorted(potential + [p])
                if p == smallest:
                    break
                if possibility in n or len(possibility) != len(set(possibility)):
                    break
                if possibility not in c:
                    exit = False
                    #if self.n == 14:
                        #import pdb
                        #pdb.set_trace()
                    for f in a:
                        if f == potential:
                            break
                        elif sorted([p] + f) not in a:
                            exit = True
                            break
                    if not exit:
                        n += [possibility]
                        smallest = p
                    break

        return n

    def flatten(self):
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
        if self._primes is None:
            self._primes = [x[0] for x in self.prime_factorizations(1)]
        return self._primes

    def smallest_new_factorizations_with_square(self):
        factorizations = self.flatten()
        r = []

        smallest_factorization = None
        for p in self.primes():
            for f in factorizations:
                if f is smallest_factorization:
                    break
                tmp = sorted(f + [p])
                found = False
                if p in f:
                    if tmp not in factorizations:
                        r += [tmp]
                        found = True
                        smallest_factorization = f
                        break
                elif tmp not in factorizations:
                    if len(set(f)) != len(f) and p not in f:
                         r += [tmp]
                         found = True
                         smallest_factorization = f
                    break
                if found:
                    break
        return r
