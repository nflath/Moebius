import pdb
import copy
import collections
import math

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

@memoized
def moebius(n):
    """Returns the moebius value of n

    This function is described as:
        moebius(n) == (-1)^m if the factorization of n is a product of m distinct primes
        moebius(n) == 0 otherswise.
    """
    def moebius_factorization(f):
        if len(set(f)) != len(f):
            return 0
        return int(math.pow(-1, len(f)))

    assert n > 0
    if n == 1:
        return 1

    return moebius_factorization(factorize(n))

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
            primes.remove(tuple(retn[idx]))

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
    if (ts, to) in scache:
        return scache[(ts, to)]

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
