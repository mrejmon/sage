from itertools import count
from collections import Counter

from sage.rings.all import ZZ
from sage.combinat.words.words import FiniteWords
from sage.combinat.words.morphism import get_cycles

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

def infinite_repetitions(self):
    r"""
    Return the set of all primitive infinite repetitions of the D0L system made
    from this morphism and an arbitrary axiom, from which all letters are
    accessible.

    Requires this morphism to be an endomorphism.

    A D0L system is a triplet `(A, \varphi, w)`, where `A` is an alphabet,
    `\varphi` a morphism on `A^*` and `w` a non-empty word (called axiom).
    The language of a D0L system is the set `\{\varphi^k(w) | k \in \NN\}`.

    An infinite repetition (aka an infinite periodic factor) of a D0L system is
    a non-empty word `w` such that `w^k` is a factor of a word of the language
    of the system for all positive integers `k`.

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
    return self.infinite_repetitions_bounded() | self.infinite_repetitions_growing()

def infinite_repetitions_bounded(self):
    """
    Return the set of all primitive infinite repetitions, which contain no
    growing letters, of the D0L system made from this morphism and an arbitrary
    axiom, from which all letters are accessible.

    Requires this morphism to be an endomorphism.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

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

    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')

    g, _, k, _ = self.simplify_injective()
    unbounded = set(g.growing_letters())
    bounded = set(g.domain().alphabet()) - unbounded

    result = set()
    for x in impl():
        result.update(x.conjugates_iterator())
    g, k = g.reversal(), k.reversal()
    for x in impl():
        result.update(self.domain()(reversed(x)).conjugates_iterator())

    return result

def infinite_repetitions_growing(self):
    """
    Return the set of all primitive infinite repetitions, which contain at least
    one growing letter, of the D0L system made from this morphism and an
    arbitrary axiom, from which all letters are accessible.

    Requires this morphism to be an endomorphism.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

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
    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')

    g, _, k, _ = self.simplify_injective()
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
                result.update(k(v).primitive().conjugates_iterator())

    return result

def is_repetitive(self):
    """
    Return whether the D0L system made from this morphism and an arbitrary
    axiom, from which all letters are accessible, is repetitive.

    Requires this morphism to be an endomorphism.

    A D0L system is repetitive iff for all positive integers `k` there is a
    non-empty word `w` such that `w^k` is a factor of a word of the language of
    the system. Therefore if a D0L system is not repetitive it must be k-power
    free for some `k`. It turns out that for D0L systems repetitiveness is
    equivalent to having at least one infinite repetition (aka strong
    repetitiveness).

    See :meth:`infinite_repetitions`.

    EXAMPLES::

        sage: WordMorphism('a->ab,b->ab').is_repetitive()
        True
        sage: WordMorphism('a->ab,b->ba').is_repetitive()
        False
    """
    return self.is_pushy() or self.is_unboundedly_repetitive()

def is_pushy(self):
    """
    Return whether the D0L system made from this morphism and an arbitrary
    axiom, from which all letters are accessible, is pushy.

    Requires this morphism to be an endomorphism.

    A D0L system is pushy iff it has an infinite amount of factors (of words
    of the language of the system) containing no growing letters. It turns out
    that this is equivalent to having at least one infinite repetition
    containing no growing letters.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

    EXAMPLES::

        sage: WordMorphism('a->abca,b->bc,c->').is_pushy()
        False
        sage: WordMorphism('a->abc,b->,c->bcb').is_pushy()
        True
    """
    return bool(self.infinite_repetitions_bounded())

def is_unboundedly_repetitive(self):
    """
    Return whether the D0L system made from this morphism and an arbitrary
    axiom, from which all letters are accessible, is unboundedly repetitive.

    Requires this morphism to be an endomorphism.

    A D0L system is unboundedly repetitive iff it has at least one infinite
    repetition containing at least one growing letter.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

    EXAMPLES::

        sage: WordMorphism('a->abca,b->bc,c->').is_unboundedly_repetitive()
        True
        sage: WordMorphism('a->abc,b->,c->bcb').is_unboundedly_repetitive()
        False
    """
    return bool(self.infinite_repetitions_growing())

def simplify(self, Z=None):
    r"""
    Return morphisms `h` and `k` such that this morphism is simplifiable with
    respect to `h` and `k`.

    If this morphism is non-injective, this function always succeeds, but can
    fail (raise ``ValueError``) if it is injective, even it if is simplifiable.

    Let `f: X^* \rightarrow Y^*` be a morphism. Then `f` is simplifiable with
    respect to morphisms `h: X^* \rightarrow Z^*` and `k: Z^* \rightarrow Y^*`,
    if `f = k \circ h` and `|Z| < |X|`. If also `X = Y`, then morphism
    `g: Z^* \rightarrow Z^* = h \circ k` is a simplification of `f`
    (with respect to `h` and `k`).

    Therefore a morphism is simplifiable if it contains "more letters than is
    needed". Simplification preserves some properties of the original morphism
    (e.g. repetitiveness).

    Time complexity is on average quadratic with regards to the size of the
    morphism.

    For more information see Section 3 in [KO2000]_.

    INPUT:

    - ``Z`` -- sequence used (or its subsequence) as a domain for the
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
        sage: h = WordMorphism('a->xyy,b->xyz,c->xzy,d->xzz')
        sage: k = WordMorphism('x->ab,y->c,z->d')
        sage: k * h == f
        True
        sage: g = h * k; g
        WordMorphism: x->xyyxyz, y->xzy, z->xzz
    """
    X = self.domain().alphabet()
    Y = self.codomain().alphabet()
    if not Z:
        Z = X
    if len(Z) < len(X) - 1:
        raise ValueError(f'alphabet should have length at least {len(X) - 1}, is {len(Z)}')

    f = self._morph
    if len(Y) < len(X):
        k = {letter1 : self.codomain()([letter2]) for letter1, letter2 in zip(Z, Y)}
    else:
        k_wip = dict(f)
        for letter, image in f.items():
            if not image:
                del k_wip[letter]

        to_do = set(k_wip)
        to_remove = []
        while to_do:
            # min() and remove() instead of pop() to have deterministic output.
            letter1 = min(to_do)
            to_do.remove(letter1)
            image1 = k_wip[letter1]
            for letter2, image2 in k_wip.items():
                if letter1 == letter2:
                    continue
                if image1 == image2:
                    to_remove.append(letter2)
                    to_do.discard(letter2)
                elif image1.is_prefix(image2):
                    k_wip[letter2] = image2[image1.length():]
                    to_do.add(letter2)
                elif image1.is_suffix(image2):
                    k_wip[letter2] = image2[:-image1.length()]
                    to_do.add(letter2)
                elif image2.is_prefix(image1):
                    k_wip[letter1] = image1[image2.length():]
                    to_do.add(letter1)
                    break
                elif image2.is_suffix(image1):
                    k_wip[letter1] = image1[:-image2.length()]
                    to_do.add(letter1)
                    break
            for letter in to_remove:
                del k_wip[letter]
            to_remove = []

        if len(k_wip) == len(f):
            raise ValueError(f'failed to simplify {self}')

        k = {letter : image for letter, image in zip(Z, k_wip.values())}

    # Find h by using k on f "in reverse".
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

    Z_star = FiniteWords(Z[:len(k)])
    h = type(self)(h, domain=self.domain(), codomain=Z_star)
    k = type(self)(k, domain=Z_star, codomain=self.codomain())
    return h, k

def simplify_injective(self, Z=None):
    r"""
    Return a quadruplet `(g, h, k, i)`, where `g` is an injective simplification
    of this morphism with respect to `h`, `k` and `i`.

    Requires this morphism to be an endomorphism.

    Basically calls :meth:`simplify` until the result is injective. If this
    morphism is already injective, instead of raising an exception a quadruplet
    `(g, h, k, i)` is still returned, where `g` and `h` are equal to this
    morphism, `k` is the identity morphism and `i` is 1.

    Let `f: X^* \rightarrow X^*` be a morphism. Then `g: Z^* \rightarrow Z^*` is
    an injective simplification of `f` with respect to morphisms
    `h: X^* \rightarrow Z^*` and `k: Z^* \rightarrow X^*` and a positive integer
    `i`, if `g` is injective and `|Z| < |X|` and `g^i = h \circ k` and
    `f^i = k \circ h`.

    For more information see Section 4 in [KO2000]_.

    INPUT:

    - ``Z`` -- sequence used (or its subsequence) as a domain for the
      simplification, default is ``self.domain().alphabet()``

    EXAMPLES::

        sage: f = WordMorphism('a->abc,b->a,c->bc')
        sage: g, h, k, i = f.simplify_injective('xy'); g, h, k, i
        (WordMorphism: x->xx, WordMorphism: a->xx, b->x, c->x, WordMorphism: x->abc, 2)
        sage: g.is_injective()
        True
        sage: g ** i == h * k
        True
        sage: f ** i == k * h
        True
    """
    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')

    if self.is_injective():
        # Without optional argument Z this code could be just
        # return self, self, self.domain().identity_morphism(), 1
        X = self.domain().alphabet()
        if not Z:
            Z = X
        if len(Z) < len(X):
            raise ValueError(f'alphabet should have length at least {len(X)}, is {len(Z)}')
        Z_star = FiniteWords(Z[:len(X)])
        k = type(self)({z : x for x, z in zip(X, Z)}, domain=Z_star, codomain=self.domain())
        k_inverse = type(self)({x : z for x, z in zip(X, Z)}, domain=self.domain(), codomain=Z_star)
        h = k_inverse * f
        return h * k, h, k, 1

    i = 1
    h, k = simplify(self, Z)
    g = h * k

    while not g.is_injective():
        h_new, k_new = simplify(g, Z)
        g, h, k, i = h_new * k_new, h_new * h, k * k_new, i + 1

    return g, h, k, i
