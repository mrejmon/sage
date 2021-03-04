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
    Time complexity is `O(L^2)`, where `L` is the sum of lengths of images
    of this morphism.

    EXAMPLES::

        sage: WordMorphism('a->0,b->10,c->110,d->111').is_injective()
        True
        sage: WordMorphism('a->0,b->010,c->01,d->10').is_injective()
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
    Return a sorted list of all infinite repetitions of the D0L system made from
    this morphism and an arbitrary axiom, from which all letters are accessible.

    Requires this morphism to be an endomorphism.

    D0L system is a triplet `(A, \varphi, w)`, where `A` is an alphabet,
    `\varphi` a morphism on `A^*` and `w` a non-empty word (called axiom).
    The language of a D0L system is the set `\{\varphi^k(w) | k \in \NN\}`.

    Infinite repetition (aka infinite periodic factor) of a D0L system is a
    non-empty word `w` such that `w^k` is a factor of the language of the system
    for all positive integers `k`.

    ALGORITHM:

    The algorithm used is described in detail in [KS2015]_.

    EXAMPLES::

        sage: morph = WordMorphism('a->aba,b->aba,c->cd,d->e,e->d')
        sage: inf_reps = morph.infinite_repetitions(); inf_reps
        [word: aab, word: aba, word: baa, word: de, word: ed]

    Incomplete check that these words are indeed infinite repetitions::

        sage: SL = morph._language_naive(10, Word('abcde'))
        sage: all(x in SL for x in inf_reps)
        True
        sage: all(x^2 in SL for x in inf_reps)
        True
        sage: all(x^3 in SL for x in inf_reps)
        True
    """
    bounded = self.infinite_repetitions_nongrowing()
    unbounded = self.infinite_repetitions_growing()

    sortkey = self.domain().sortkey_letters
    return sorted(bounded + unbounded, key=lambda x: [sortkey(y) for y in x])

def infinite_repetitions_nongrowing(self):
    """
    Return a sorted list of all infinite repetitions, which contain only
    non-growing letters, of the D0L system made from this morphism and an
    arbitrary axiom, from which all letters are accessible.

    Requires this morphism to be an endomorphism.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

    EXAMPLES::

        sage: WordMorphism('a->aba,b->aba,c->cd,d->e,e->d').infinite_repetitions_nongrowing()
        [word: de, word: ed]
        sage: WordMorphism('c->d,d->c,e->fc,f->ed').infinite_repetitions_nongrowing()
        [word: c, word: d]
    """
    def impl(reversed):
        nonlocal g
        if reversed:
            g_saved = g
            g = g.reversal()
        U = dict()
        for x in unbounded:
            hx = g.image(x)
            for i, y in enumerate(hx):
                if y in unbounded:
                    break
            U[x] = y, hx[:i]
        for cycle in get_cycles(lambda x: U[x][0], domain=unbounded):
            if all(not U[x][1] for x in cycle):
                continue
            for _ in range(len(cycle)):
                cycle = cycle[1:] + cycle[:1]
                u = g.domain()()
                for x in cycle:
                    u = g(u)
                    u = u + U[x][1]
                if reversed:
                    g = g_saved
                    u = u.reversal()
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
                gq = g ** q
                uql = gq(u, l0)
                res = g.domain()()
                for _ in range(l0+1, l1+1):
                    uql = gq(uql)
                    res += uql
                res = k(res.primitive()).primitive()
                for x in res.conjugates_iterator():
                    result.add(x)

    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')
    try:
        g, _, k, _ = self.simplify_injective()
    except ValueError:
        g, k = self, self.domain().identity_morphism()
    unbounded = set(g.growing_letters())

    result = set()
    impl(False) # UL.
    impl(True) # UR.

    sortkey = self.domain().sortkey_letters
    return sorted(result, key=lambda x: [sortkey(y) for y in x])

def infinite_repetitions_growing(self):
    """
    Return a sorted list of all infinite repetitions, which contain at least
    one growing letter, of the D0L system made from this morphism and an
    arbitrary axiom, from which all letters are accessible.

    Requires this morphism to be an endomorphism.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

    EXAMPLES::

        sage: WordMorphism('a->aba,b->aba,c->cd,d->e,e->d').infinite_repetitions_growing()
        [word: aab, word: aba, word: baa]
        sage: WordMorphism('a->bcb,b->ada,c->d,d->c').infinite_repetitions_growing()
        [word: ad, word: bc, word: cb, word: da]
        sage: WordMorphism('b->c,c->bcb').infinite_repetitions_growing()
        [word: bc, word: cb]
    """
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
                res = k(v).primitive()
                for x in res.conjugates_iterator():
                    result.add(x)

    sortkey = self.domain().sortkey_letters
    return sorted(result, key=lambda x: [sortkey(y) for y in x])

def is_repetitive(self):
    """
    Return whether the D0L system made from this morphism and an arbitrary
    axiom, from which all letters are accessible, is repetitive.

    Requires this morphism to be an endomorphism.

    D0L system is repetitive iff for all positive integers `k` there is a
    non-empty word `w` such that `w^k` is a factor of the language of the
    system. It turns out that this is equivalent to having at least one infinite
    repetition (aka strong repetitiveness).

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

    D0L system is pushy iff it has at least one infinite repetition containing
    only non-growing letters.

    See :meth:`infinite_repetitions` and :meth:`is_growing`.

    EXAMPLES::

        sage: WordMorphism('a->abca,b->bc,c->').is_pushy()
        False
        sage: WordMorphism('a->abc,b->,c->bcb').is_pushy()
        True
    """
    return bool(self.infinite_repetitions_nongrowing())

def is_unboundedly_repetitive(self):
    """
    Return whether the D0L system made from this morphism and an arbitrary
    axiom, from which all letters are accessible, is unboundedly repetitive.

    Requires this morphism to be an endomorphism.

    D0L system is unboundedly repetitive iff it has at least one infinite
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

    Time complexity is `O(L^2)`, where `L` is the sum of lengths of images
    of this morphism.

    Let `f: X^* \rightarrow Y^*` be a morphism. Then `f` is simplifiable with
    respect to morphisms `h: X^* \rightarrow Z^*` and `k: Z^* \rightarrow Y^*`,
    if `f = k \cdot h` and `\#Z < \#X`. If also `X = Y`, then morphism
    `g: Z^* \rightarrow Z^* = h \cdot k` is a simplification of `f`
    (with respect to `h` and `k`). Simplification preserves some properties of
    the original morphism (e.g. infinite repetitions).

    For more information see Section 3 in [KO2000]_.

    INPUT:

    - ``Z`` -- iterable used (or its subset) as a domain for the simplification,
      default is ``self.domain().alphabet()``

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
    Y = self.domain().alphabet()
    if not Z:
        Z = X
    if len(Z) < len(X) - 1:
        raise ValueError(f'alphabet should have length at least {len(X) - 1}, is {len(Z)}')

    f = self._morph
    if len(Y) < len(X):
        k = {letter1 : [letter2] for letter1, letter2 in zip(Z, Y)}
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

    If this morphism is non-injective, this function always succeeds, but can
    fail (raise ``ValueError``) if it is injective, even it if is simplifiable.

    Requires this morphism to be an endomorphism.

    Let `f: X^* \rightarrow X^*` be a morphism. Then `g: Z^* \rightarrow Z^*` is
    an injective simplification of `f` with respect to morphisms
    `h: X^* \rightarrow Z^*` and `k: Z^* \rightarrow X^*` and a positive integer
    `i`, if `g` is injective and `\#Z < \#X` and `g^i = h \cdot k` and
    `f^i = k \cdot h`.

    For more information see Section 4 in [KO2000]_.

    INPUT:

    - ``Z`` -- iterable used (or its subset) as a domain for the simplification,
      default is ``self.domain().alphabet()``

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
    h, k = simplify(self, Z)
    g = h * k
    for i in count(start=1):
        try:
            h_new, k_new = simplify(g, Z)
            g, h, k = h_new * k_new, h_new * h, k * k_new
        except:
            return g, h, k, i
