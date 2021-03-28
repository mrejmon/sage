from itertools import count
from collections import Counter

from sage.rings.all import ZZ
from sage.combinat.words.words import FiniteWords
from sage.combinat.words.morphism import get_cycles

# finite_word.py
def smallest_cyclic_shift(self, w):
    """
    """
    start, end = 0, 0
    s2 = self**2
    for s in s2.lyndon_factorization():
        start = end
        end += s.length()
        if start < self.length() and end > self.length():
            break
    return s2[start:end]

# morphism.py
def reach(self, w):
    r"""
    Return the set of letters which occur in words of `\{m^n(w) | n \ge 0}`,
    where `m` is this morphism and `w` is a word (finite iterable is enough)
    inputted as a parameter.

    Requires this morphism to be an endomorphism.

    EXAMPLES::

        sage: sorted(WordMorphism('a->abc,b->bb,c->bd,d->dd').reach('c'))
        sage: ['b', 'c', 'd']
    """
    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')

    visited = set(w)
    todo = list(visited)
    while todo:
        a = todo.pop()
        for b in self.image(a):
            if b not in visited:
                visited.add(b)
                todo.append(b)
    return visited

def is_injective(self):
    """
    Return whether this morphism is injective.

    ALGORITHM:

    Slightly modified version of :wikipedia:`Sardinas–Patterson_algorithm`.
    Time complexity is on average quadratic with regards to the size of the
    morphism.

    EXAMPLES::

        sage: WordMorphism('a->0,b->10,c->110,d->111').is_injective()
        True
        sage: WordMorphism('a->00,b->01,c->012,d->20001').is_injective()
        False
    """
    def check(u, v):
        if u.is_prefix(v):
            tail = v[u.length():]
            if tail not in tails:
                tails.add(tail)
                todo.append(tail)

    images = self._morph.values()
    if any(not x for x in images):
        return False
    tails = set()
    todo = []

    for i, u in enumerate(images):
        for j, v in enumerate(images):
            if i == j:
                continue
            check(u, v)

    while todo:
        u = todo.pop()
        for v in images:
            if u == v:
                return False
            check(u, v)
            check(v, u)

    return True

def infinite_repetitions(self, w=None):
    r"""
    Return (except for conjugation) the set of primitive infinite repetitions
    from the language `\{m^n(w) | n \ge 0}`, where `m` is this morphism and
    `w` is a word inputted as a parameter.

    Requires this morphism to be an endomorphism.

    A non-empty word `v` is an infinite repetition (also known as an infinite
    periodic factor) of a language iff for each positive integer `k` the word
    `v^k` is a factor of some word from the language.

    If `v` is an infinite repetition, then all its powers are also infinite
    repetitions, therefore this method returns only the primitive ones. It turns
    out that a language created by iteration of a morphism has a finite number
    of primitive infinite repetitions.

    Similarly, if `v` is an infinite repetition, then all its conjugates are
    also infinite repetitions, therefore this method returns only the
    lexicographically smallest one from each conjugacy class.

    INPUT:

    - ``w`` -- finite iterable representing a word in the domain of this
      morphism used as a *seed*, default is ``self.domain().alphabet()``

    ALGORITHM:

    The algorithm used is described in detail in [KS2015]_.

    EXAMPLES::

        sage: m = WordMorphism('a->aba,b->aba,c->cd,d->e,e->d')
        sage: inf_reps = m.infinite_repetitions()
        sage: sorted(inf_reps)
        [word: aab, word: aba, word: baa, word: de, word: ed]

    Incomplete check that these words are indeed infinite repetitions::

        sage: SL = m._language_naive(10, Word('abcde'))
        sage: all(x in SL for x in inf_reps)
        True
        sage: all(x^2 in SL for x in inf_reps)
        True
        sage: all(x^3 in SL for x in inf_reps)
        True
    """
    return self.infinite_repetitions_bounded(w) | self.infinite_repetitions_growing(w)

def infinite_repetitions_bounded(self, w=None):
    r"""
    Return (except for conjugation) the set of primitive infinite repetitions,
    which contain no growing letters,
    from the language `\{m^n(w) | n \ge 0}`, where `m` is this morphism and
    `w` is a word inputted as a parameter.

    Requires this morphism to be an endomorphism.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

    INPUT:

    - ``w`` -- finite iterable representing a word in the domain of this
      morphism used as a *seed*, default is ``self.domain().alphabet()``

    EXAMPLES::

        sage: m = WordMorphism('a->aba,b->aba,c->cd,d->e,e->d')
        sage: sorted(m.infinite_repetitions_bounded())
        [word: de, word: ed]

        sage: m = WordMorphism('c->d,d->c,e->fc,f->ed')
        sage: sorted(m.infinite_repetitions_bounded())
        [word: c, word: d]
    """
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

    if not w:
        w = self._morph
    f = self.restrict_domain(self.reach(w))
    g, _, k, _ = f.simplify_injective()
    unbounded = set(g.growing_letters())
    bounded = set(g._morph) - unbounded

    result = set()
    for x in impl():
        result.add(x.smallest_cyclic_shift())
    g, k = g.reversal(), k.reversal()
    for x in impl():
        result.add(self.domain()(reversed(x)).smallest_cyclic_shift())

    return result

def infinite_repetitions_growing(self, w=None):
    """
    Return (except for conjugation) the set of primitive infinite repetitions,
    which contain at least one growing letter,
    from the language `\{m^n(w) | n \ge 0}`, where `m` is this morphism and
    `w` is a word inputted as a parameter.

    Requires this morphism to be an endomorphism.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

    INPUT:

    - ``w`` -- finite iterable representing a word in the domain of this
      morphism used as a *seed*, default is ``self.domain().alphabet()``

    EXAMPLES::

        sage: m = WordMorphism('a->aba,b->aba,c->cd,d->e,e->d')
        sage: sorted(m.infinite_repetitions_growing())
        [word: aab, word: aba, word: baa]

        sage: m = WordMorphism('a->bcb,b->ada,c->d,d->c')
        sage: sorted(m.infinite_repetitions_growing())
        [word: ad, word: bc, word: cb, word: da]

        sage: m = WordMorphism('b->c,c->bcb')
        sage: sorted(m.infinite_repetitions_growing())
        [word: bc, word: cb]
    """
    if not w:
        w = self._morph
    f = self.restrict_domain(self.reach(w))
    g, _, k, _ = f.simplify_injective()
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
                result.add(k(v).primitive().smallest_cyclic_shift())

    return result

def is_repetitive(self, w=None):
    """
    Return whether the language `\{m^n(w) | n \ge 0}` is repetitive,
    where `m` is this morphism and `w` is a word inputted as a parameter.

    Requires this morphism to be an endomorphism.

    A language is repetitive iff for each positive integer `k` there exists a
    word `u` such that `u^k` is a factor of some word of the language.

    It turns that for languages created by iteration of a morphism this is
    equivalent to having at least one infinite repetition (this property is
    also known as strong repetitiveness).

    See :meth:`infinite_repetitions`.

    INPUT:

    - ``w`` -- finite iterable representing a word in the domain of this
      morphism used as a *seed*, default is ``self.domain().alphabet()``

    EXAMPLES:

    This can be used for checking whether an infinite word created by
    iteration of a morphism is NOT k-power free for all positive integers k::

        sage: WordMorphism('a->ab,b->ab').is_repetitive()
        True
        sage: WordMorphism('a->ab,b->ba').is_repetitive()
        False
    """
    return self.is_pushy(w) or self.is_unboundedly_repetitive(w)

def is_pushy(self, w=None):
    """
    Return whether the language `\{m^n(w) | n \ge 0}` is pushy,
    where `m` is this morphism and `w` is a word inputted as a parameter.

    Requires this morphism to be an endomorphism.

    A language created by an iteration of a morphism is pushy iff its words
    contain an infinite number of factors containing no growing letters. It
    turns out that this is equivalent to having at least one infinite repetition
    containing no growing letters.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

    INPUT:

    - ``w`` -- finite iterable representing a word in the domain of this
      morphism used as a *seed*, default is ``self.domain().alphabet()``

    EXAMPLES::

        sage: WordMorphism('a->abca,b->bc,c->').is_pushy()
        False
        sage: WordMorphism('a->abc,b->,c->bcb').is_pushy()
        True
    """
    return bool(self.infinite_repetitions_bounded(w))

def is_unboundedly_repetitive(self, w=None):
    """
    Return whether the language `\{m^n(w) | n \ge 0}` is unboundedly repetitive,
    where `m` is this morphism and `w` is a word inputted as a parameter.

    Requires this morphism to be an endomorphism.

    A language created by an iteration of a morphism is unboundedly repetitive
    iff it has at least one infinite repetition containing at least one growing
    letter.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

    INPUT:

    - ``w`` -- finite iterable representing a word in the domain of this
      morphism used as a *seed*, default is ``self.domain().alphabet()``

    EXAMPLES::

        sage: WordMorphism('a->abca,b->bc,c->').is_unboundedly_repetitive()
        True
        sage: WordMorphism('a->abc,b->,c->bcb').is_unboundedly_repetitive()
        False
    """
    return bool(self.infinite_repetitions_growing(w))

def simplify(self, Z=None):
    r"""
    Return morphisms `h` and `k` such that this morphism is simplifiable with
    respect to `h` and `k`.

    If this morphism is non-injective, this function always succeeds, but can
    fail (raise ``ValueError``) if it is injective, even it if is simplifiable.

    Let `f: X^* \rightarrow Y^*` be a morphism. Then `f` is simplifiable with
    respect to morphisms `h: X^* \rightarrow Z^*` and `k: Z^* \rightarrow Y^*`,
    if `f = k \circ h` and `|Z| < |X|`. If also `Y \subseteq X`, then morphism
    `g: Z^* \rightarrow Z^* = h \circ k` is a simplification of `f`
    (with respect to `h` and `k`).

    Therefore a morphism is simplifiable if it contains "more letters than is
    needed". Simplification preserves some properties of the original morphism
    (e.g. repetitiveness).

    Time complexity is on average quadratic with regards to the size of the
    morphism.

    For more information see Section 3 in [KO2000]_.

    INPUT:

    - ``Z`` -- iterable, whose elements are used as an alphabet for the
      simplification, default is ``self.domain().alphabet()``

    EXAMPLES:

    Example of a simplifiable morphism::

        sage: f = WordMorphism('a->bca,b->bcaa,c->bcaaa')
        sage: h, k = f.simplify('xy')
        sage: h
        WordMorphism: a->xy, b->xyy, c->xyyy
        sage: k
        WordMorphism: x->bc, y->a
        sage: g = h * k; g
        WordMorphism: x->xyyxyyy, y->xy
        sage: k * h == f
        True
        sage: g('x')
        word: xyyxyyy
        sage: f(k('x'))
        word: bcaabcaaa

    Example of a non-simplifiable morphism::

        sage: WordMorphism('a->aa').simplify()
        Traceback (most recent call last):
        ...
        ValueError: failed to simplify a->aa

    Example of a simplifiable morphism that the function fails on::

        sage: f = WordMorphism('a->abcc,b->abcd,c->abdc,d->abdd')
        sage: f.simplify('xyz')
        Traceback (most recent call last):
        ...
        ValueError: failed to simplify a->abcc, b->abcd, c->abdc, d->abdd

    Proof that the above morphism is simplifiable::

        sage: k = WordMorphism('x->ab,y->c,z->d')
        sage: h = WordMorphism('a->xyy,b->xyz,c->xzy,d->xzz')
        sage: k * h == f
        True
        sage: g = h * k; g
        WordMorphism: x->xyyxyz, y->xzy, z->xzz
    """
    X = self.domain().alphabet()
    Y = self.codomain().alphabet()
    f = self._morph

    if self.is_erasing(): # Trivial case #1.
        k = {letter : image for letter, image in f.items() if image}
        h = {letter : [letter] if image else [] for letter, image in f.items()}
    elif len(Y) < len(X): # Trivial case #2.
        k = {x : [y] for x, y in zip(X, Y)}
        k_inverse = {y : [x] for x, y in zip(X, Y)}
        h = {x : [k_inverse[y] for y in image] for x, image in f.items()}
    else: # Non-trivial case.
        k = dict(f)
        to_do = set(k)
        to_remove = []
        while to_do:
            # min() and remove() instead of pop() to have deterministic output.
            letter1 = min(to_do)
            to_do.remove(letter1)
            image1 = k[letter1]
            for letter2, image2 in k.items():
                if letter1 == letter2:
                    continue
                if image1 == image2:
                    to_remove.append(letter2)
                    to_do.discard(letter2)
                elif image1.is_prefix(image2):
                    k[letter2] = image2[image1.length():]
                    to_do.add(letter2)
                elif image1.is_suffix(image2):
                    k[letter2] = image2[:-image1.length()]
                    to_do.add(letter2)
                elif image2.is_prefix(image1):
                    k[letter1] = image1[image2.length():]
                    to_do.add(letter1)
                    break
                elif image2.is_suffix(image1):
                    k[letter1] = image1[:-image2.length()]
                    to_do.add(letter1)
                    break
            for letter in to_remove:
                del k[letter]
            to_remove = []

        if len(k) == len(f):
            raise ValueError(f'failed to simplify {self}')

        h = {}
        for letter1, image1 in f.items():
            image3 = []
            while image1:
                for letter2, image2 in k.items():
                    if image2.is_prefix(image1):
                        image1 = image1[image2.length():]
                        image3.append(letter2)
                        break
            h[letter1] = image3

    k = type(self)(k, codomain=self.codomain())
    h = type(self)(h, domain=self.domain(), codomain=k.domain())

    if Z: # Custom alphabet.
        old_Z_star = k.domain()
        old_Z = old_Z_star.alphabet()
        Z = [z for z, _ in zip(Z, old_Z)]
        if len(Z) < len(old_Z):
            raise ValueError(f'Z should have length at least {len(old_Z)}, is {len(Z)}')
        Z_star = FiniteWords(Z)
        h_new = {old : [new] for old, new in zip(old_Z, Z)}
        k_new = {new : [old] for new, old in zip(Z, old_Z)}
        h_new = type(self)(h_new, domain=old_Z_star, codomain=Z_star)
        k_new = type(self)(k_new, domain=Z_star, codomain=old_Z_star)
        h = h_new * h
        k = k * k_new

    return h, k

def simplify_injective(self):
    r"""
    Return a quadruplet `(g, h, k, i)`, where `g` is an injective simplification
    of this morphism with respect to `h`, `k` and `i`.

    Requires this morphism to be an endomorphism.

    Basically calls :meth:`simplify` until the result is injective. If this
    morphism is already injective, instead of raising an exception a quadruplet
    `(g, h, k, i)` is still returned, where `g` and `h` are equal to this
    morphism, `k` is the identity morphism and `i` is 0.

    Let `f: X^* \rightarrow Y^*` be a morphism and `Y \subseteq X`. Then
    `g: Z^* \rightarrow Z^*` is an injective simplification of `f` with respect
    to morphisms `h: X^* \rightarrow Z^*` and `k: Z^* \rightarrow Y^*` and a
    positive integer `i`, if `g` is injective and `|Z| < |X|` and
    `g^i = h \circ k` and `f^i = k \circ h`.

    For more information see Section 4 in [KO2000]_.

    EXAMPLES::

        sage: f = WordMorphism('a->abc,b->a,c->bc')
        sage: g, h, k, i = f.simplify_injective(); g, h, k, i
        (WordMorphism: a->aa, WordMorphism: a->aa, b->a, c->a, WordMorphism: a->abc, 2)
        sage: sage: g.is_injective()
        True
        sage: sage: g ** i == h * k
        True
        sage: sage: f ** i == k * h
        True
    """
    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')

    try:
        h, k = simplify(self)
    except ValueError:
        return self, self, self.domain().identity_morphism(), 0
    g = h * k

    for i in count(start=1):
        try:
            h_new, k_new = simplify(g)
            g, h, k = h_new * k_new, h_new * h, k * k_new
        except ValueError:
            return g, h, k, i
