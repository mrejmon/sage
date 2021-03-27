def is_endomorphism_alternative(self):
    return set(self.domain().alphabet()).issuperset(self.codomain().alphabet())

def periodic_points_fixed(self):
    from sage.misc.callable_dict import CallableDict
    from sage.combinat.words.morphism import PeriodicPointIterator, get_cycles

    assert self.is_endomorphism(), "f should be an endomorphism"

    if self.is_erasing():
        raise NotImplementedError("f should be non erasing")

    A = self.domain().alphabet()
    d = dict((letter,self(letter)[0]) for letter in A)
    G = set(self.growing_letters()) # <--

    res = []
    parent = self.codomain().shift()
    for cycle in get_cycles(CallableDict(d),A):
        if cycle[0] in G: # <--
            P = PeriodicPointIterator(self, cycle)
            res.append([parent(P._cache[i]) for i in range(len(cycle))])

    return res

def growing_letters_alternative(self):
    assert(self.is_endomorphism())

    bounded = set()
    unbounded = dict(self._morph)
    undecided = dict()

    # Need a letter not in the alphabet.
    terminal = '#'
    while terminal in self.codomain().alphabet():
        terminal += '#'

    # Split letters into bounded, unbounded and undecided.
    while True:
        for letter1, image1 in unbounded.items():
            if not image1:
                bounded.add(letter1)
                del unbounded[letter1]
                for letter2, image2 in unbounded.items():
                    unbounded[letter2] = [x for x in image2 if x != letter1]
                break
            elif all(x == terminal for x in image1) or (len(image1) == 1 and image1[0] == letter1):
                bounded.add(letter1)
                del unbounded[letter1]
                for letter2, image2 in unbounded.items():
                    unbounded[letter2] = [x if x != letter1 else terminal for x in image2]
                break
            elif len(image1) == 1:
                undecided[letter1] = image1
                del unbounded[letter1]
                for letter2, image2 in unbounded.items():
                    unbounded[letter2] = [x if x != letter1 else image1[0] for x in image2]
                break
        else: # no break
            break

    # Decide undecided letters.
    while True:
        for letter, image in undecided.items():
            if image[0] in bounded:
                bounded.add(letter)
                del undecided[letter]
                break
            elif image[0] in unbounded:
                unbounded[letter] = image
                del undecided[letter]
                break
        if not undecided:
            break

    return sorted(unbounded, key=self.domain().sortkey_letters)

def is_injective_v2(self, certificate=False):
    """
    Return whether this morphism is injective.

    ALGORITHM:

    Slightly modified version of :wikipedia:`Sardinas–Patterson_algorithm`.
    Time complexity is `O(L^2)`, where `L` is the sum of lengths of images
    of this morphism.

    EXAMPLES::

        sage: WordMorphism('a->0,b->10,c->110,d->111').is_injective()
        True
        sage: WordMorphism('a->00,b->01,c->012,d->20001').is_injective()
        False

    One pair of preimages mapped to the same word can be obtained by
    setting the ``certificate`` parameter to ``True``::

        sage: m = WordMorphism('a->00,b->01,c->012,d->20001')
        sage: answer, u, v = m.is_injective(certificate=True); answer, u, v
        (False, word: bd, word: cab)
        sage: m(u) == m(v)
        True

    If the morphism is injective, ``None`` is returned instead::

        sage: WordMorphism('a->0,b->10,c->110,d->111').is_injective(True)
        True, None, None
    """
    domain = self.domain()
    for letter, image in self._morph.items():
        if not image:
            return False if not certificate else (False, domain([letter]), domain([letter, letter]))

    todo = []
    tails = {}

    for letter1, image1 in self._morph.items():
        for letter2, image2 in self._morph.items():
            if letter1 == letter2:
                continue
            elif image1.is_prefix(image2):
                tail = image2[image1.length():]
                if tail not in tails:
                    todo.append(tail)
                    tails[tail] = ([letter1], [letter2])

    while todo:
        tail = todo.pop()
        for letter, image in self._morph.items():
            if tail == image:
                preimage1, preimage2 = tails[tail]
                return False if not certificate else (False, domain(preimage2), domain(preimage1 + [letter]))
            elif tail.is_prefix(image):
                new_tail = image[tail.length():]
                if new_tail not in tails:
                    todo.append(new_tail)
                    preimage1, preimage2 = tails[tail]
                    tails[new_tail] = (preimage2, preimage1 + [letter])
            elif image.is_prefix(tail):
                new_tail = tail[image.length():]
                if new_tail not in tails:
                    todo.append(new_tail)
                    preimage1, preimage2 = tails[tail]
                    tails[new_tail] = (preimage1 + [letter], preimage2)

    return True if not certificate else (True, None, None)

from itertools import count
from collections import Counter

from sage.rings.all import ZZ
from sage.combinat.words.words import FiniteWords
from sage.combinat.words.morphism import get_cycles

def smallest_cyclic_shift(self):
    s = self + self
    n = len(s)
    i = 0
    ans = 0
    while i < n // 2:
        ans = i
        j = i + 1
        k = i
        while j < n and s[k] <= s[j]:
            if s[k] < s[j]:
                k = i
            else:
                k += 1
            j += 1
        while i <= k:
            i += j - k
    return s[ans:n//2+ans]

def infinite_repetitions_nogrowing_v2(self):
    def impl():
        U = {}
        for x in unbounded:
            hx = g.image(x)
            for i, y in enumerate(hx):
                if y in unbounded:
                    break
            U[x] = y, hx[:i]
        for cycle in get_cycles(lambda x: U[x][0], domain=unbounded):
            if all(not U[x][1] for x in cycle):
                continue
            for cycle in g.domain()(cycle).conjugates_iterator():
                u = g.domain()()
                for x in cycle:
                    u = g(u)
                    u = u + U[x][1]
                history = dict({u : 0})
                for i in count(1):
                    u = g(u)
                    if u in history:
                        s = ZZ(history[u])
                        t = ZZ(i - history[u])
                        break
                    history[u] = i
                q = len(cycle)
                l0 = (s / q).ceil() * q
                l1 = l0 + (t.lcm(q) / q)
                gq = g.restrict_domain(bounded) ** q
                uql = gq(u, l0)
                res = g.domain()()
                for _ in range(l0+1, l1+1):
                    uql = gq(uql)
                    res = uql + res
                yield k(res.primitive()).primitive()

    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')
    try:
        g, _, k, _ = self.simplify_injective()
    except ValueError:
        g, k = self, self.domain().identity_morphism()
    unbounded = set(g.growing_letters())
    bounded = set(g.domain().alphabet()) - unbounded

    result = set()
    for x in impl():
        result.add(smallest_cyclic_shift(x))
    g, k = g.reversal(), k.reversal()
    for x in impl():
        result.add(smallest_cyclic_shift(self.domain()(reversed(x))))

    return result

def infinite_repetitions_growing_v2(self):
    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')
    try:
        g, _, k, _ = self.simplify_injective()
    except ValueError:
        g, k = self, self.domain().identity_morphism()
    unbounded = set(g.growing_letters())

    result = set()
    for equivalence_class in g.periodic_points():
        q = len(equivalence_class)
        gq = g**q
        for periodic_point in equivalence_class:
            # Check if this periodic point is a periodic infinite word.
            periodic_point = periodic_point[:1]
            letter_cnts = Counter(periodic_point)
            for _ in g.domain().alphabet():
                previous_length = periodic_point.length()
                periodic_point = gq(periodic_point)
                letter_cnts.update(periodic_point[previous_length:])
                if any(letter_cnts[letter] >= 2 for letter in unbounded):
                    break
            else: # nobreak
                continue
            if letter_cnts[periodic_point[0]] < 2:
                continue
            v = periodic_point[:periodic_point.find(periodic_point[0], start=1)]
            vq = gq(v)
            m = 0
            while vq[m*v.length():(m+1)*v.length()] == v:
                m += 1
            if m >= 2 and m*v.length() == vq.length():
                result.add(smallest_cyclic_shift(k(v).primitive()))

    return result

def mortal_letters(self):
    """
    Return the set of mortal letters.

    Requires this morphism to be an endomorphism.

    Let `m` be this morphism. A letter `a` is mortal iff there exists a positive
    integer `k` such that `m^k(a) = \varepsilon`.

    EXAMPLES::

        sorted(sage: WordMorphism('a->abc,b->cc,c->').mortal_letters())
        ['b', 'c']
    """
    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')

    domainA = self.domain().alphabet()
    codomainA = self.codomain().alphabet()
    matrix = self.incidence_matrix()
    lens = [len(self._morph[x]) for x in domainA]

    mortal = set()
    todo = [j for j, e in enumerate(lens) if e == 0]
    while todo:
        j = todo.pop()
        letter = domainA.unrank(j)
        mortal.add(letter)
        i = codomainA.rank(letter)
        row = matrix.row(i)
        for j, e in enumerate(row):
            if e != 0: # this check is necessary to prevent repeated inclusion in todo
                lens[j] -= e
                if lens[j] == 0:
                    todo.append(j)
    return mortal
