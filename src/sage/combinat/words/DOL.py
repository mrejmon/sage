from itertools import count
from collections import Counter

from sage.rings.all import ZZ
from sage.combinat.words.words import FiniteWords
from sage.combinat.words.morphism import get_cycles

def infinite_factors(self):
    """
    TODO
    """
    bounded = self.infinite_factors_bounded()
    unbounded = self.infinite_factors_unbounded()

    sortkey = self.domain().sortkey_letters
    return sorted(bounded + unbounded, key=lambda x: [sortkey(y) for y in x])

def is_repetitive(self):
    """
    TODO
    """
    return self.is_pushy() or self.is_unboundedly_repetitive()

def is_pushy(self):
    """
    TODO
    """
    return bool(self.infinite_factors_bounded())

def is_unboundedly_rep(self):
    """
    TODO
    """
    return bool(self.infinite_factors_unbounded())

def simplify_attempt(self, Z=None):
    r"""
    Let ``self`` be a morphism `f: X^* \rightarrow Y^*`. Attempt to return
    morphisms `h: X^* \rightarrow Z^*` and `k: Z^* \rightarrow Y^*`, such that
    `f = k \cdot h` and `\#Z < \#X` and if `X = Y`, then morphism
    `g: Z^* \rightarrow Z^* = h \cdot k` is a simplification of `f`
    (with respect to (`h`, `k`)). Simplification preserves some properties of
    the original morphism (e.g. infinite factors).

    This function always succeeds if ``self`` is not injective, but can fail
    (raise ``ValueError``) if ``self`` is injective, even if self is simplifiable.

    INPUT:

    - ``Z`` -- iterable used (or its subset) as a domain for the simplification,
      default is ``self.domain().alphabet()``

    EXAMPLES:

    Example of a simplifiable morphism::

        sage: f = WordMorphism('a->bca,b->bcaa,c->bcaa)
        sage: h, k = f.simplify_attempt('xy')
        sage: h
        WordMorphism: a->xy, b->xyy, c->xyyy
        sage: k
        WordMorphism: x->bc, y->a
        sage: g = h * k; g
        WordMorphism: x->xyyxyyy, y->xy
        sage: k * h == f
        True

    Example of a non-simplifiable morphism::

        sage: WordMorphism('a->aa').simplify_attempt()
        Traceback (most recent call last):
        ...
        ValueError: failed to simplify a->aa

    Example of a simplifiable morphism that the function fails on::

        sage: f = WordMorphism('a->abcc,b->abcd,c->abdc,d->abdd')
        sage: f.simplify_attempt('xyz')
        Traceback (most recent call last):
        ...
        ValueError: failed to simplify a->abcc, b->abcd, c->abdc, d->abdd
        sage: h = WordMorphism('a->xyy,b->xyz,c->xzy,d->xzz')
        sage: k = WordMorphism('x->ab,y->c,z->d')
        sage: k * h == f
        True
        sage: g = h * k; g
        WordMorphism: x->xyyxyz, y->xzy, z->xzz

    .. NOTE::

        Time complexity is `O(L^2)`, where `L` is the sum of the lengths of all images of ``self``.
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

        to_do = set(f)
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
    Let ``self`` be a non-injective morphism `f: X^* \rightarrow X^*`. Return a
    quadruplet `(g, h, k, i)`, where `g: Z^* \rightarrow Z^*`,
    `h: X^* \rightarrow Z^*` and `k: Z^* \rightarrow X^*` are morphisms
    and `i` is an integer, such that `g` is an injective simplification of `f`
    with respect to `(h, k, i)`, that is `g` is injective and `\#Z < \#Y` and
    `g^i = h \cdot k` and `f^i = k \cdot h`.

    INPUT:

    - ``Z`` -- iterable used (or its subset) as a domain for the simplification,
      default is ``self.domain().alphabet()``

    EXAMPLES::

        sage: f = WordMorphism('a->abc,b->a,c->bc')
        sage: g, h, k, i = f.simplify_injective('xy'); g, h, k, i
        (WordMorphism: x->xx, WordMorphism: a->xx, b->x, c->x, WordMorphism: x->abc, 2)
        sage: g.is_injective()
        True
        sage: g ** i = h * k
        True
        sage: f ** i = k * h
        True
    """
    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')
    h, k = simplify_attempt(self, Z)
    g = h * k
    for i in count(start=1):
        try:
            h_new, k_new = simplify_attempt(g, Z)
            g, h, k = h_new * k_new, h_new * h, k * k_new
        except:
            return g, h, k, i

def infinite_factors_bounded(self):
    """
    TODO
    """
    def impl(reversed):
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

def infinite_factors_unbounded(self):
    """
    TODO
    """
    if not self.is_endomorphism():
        raise TypeError(f'self ({self}) is not an endomorphism')
    try:
        g, _, k, _ = self.simplify_injective()
    except ValueError:
        g, k = self, self.domain().identity_morphism()
    unbounded = set(g.growing_letters())

    result = []
    for equivalence_class in g.periodic_points():
        q = len(equivalence_class)
        gq = g**q
        a = equivalence_class[0][:1]
        # Check if ((g^q)^Inf)(a) is a periodic infinite word.
        periodic_point = a
        letter_cnts = Counter(periodic_point)
        for _ in g.domain().alphabet():
            previous_length = periodic_point.length()
            periodic_point = gq(periodic_point)
            letter_cnts.update(periodic_point[previous_length:])
            if any(letter_cnts[letter] >= 2 for letter in unbounded):
                break
        else: # nobreak
            continue
        if letter_cnts[a[0]] < 2:
            continue
        v = periodic_point[:periodic_point.find(a, start=1)]
        vq = gq(v)
        m = 0
        while vq[m*v.length():(m+1)*v.length()] == v:
            m += 1
        if m >= 2 and m*v.length() == vq.length():
            res = k(v).primitive()
            for x in res.conjugates_iterator():
                result.append(x)

    sortkey = self.domain().sortkey_letters
    return sorted(result, key=lambda x: [sortkey(y) for y in x])

def is_injective(self):
    """
    TODO
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
