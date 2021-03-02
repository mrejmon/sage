from itertools import islice, count
from collections import Counter

from sage.rings.all import IntegerRing
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

def simplify(self, alphabet=None):
    """
    TODO
    """
    # Remove erasing letters.
    g_wip = dict(self._morph)
    for letter, image in self._morph.items():
        if not image:
            del g_wip[letter]

    # Simplify (find morphism g).
    to_do = set(g_wip)
    to_remove = []
    while to_do:
        # min() and remove() instead of pop() to have deterministic output.
        letter1 = min(to_do)
        to_do.remove(letter1)
        image1 = g_wip[letter1]
        for letter2, image2 in g_wip.items():
            if letter1 == letter2:
                continue
            if image1.length() == image2.length():
                if image1 == image2:
                    to_remove.append(letter2)
                    to_do.discard(letter2)
            elif image1.length() < image2.length():
                if image1.is_prefix(image2):
                    g_wip[letter2] = image2[image1.length():]
                    to_do.add(letter2)
                elif image1.is_suffix(image2):
                    g_wip[letter2] = image2[:-image1.length()]
                    to_do.add(letter2)
            else:
                if image2.is_prefix(image1):
                    g_wip[letter1] = image1[image2.length():]
                    to_do.add(letter1)
                    break
                elif image2.is_suffix(image1):
                    g_wip[letter1] = image1[:-image2.length()]
                    to_do.add(letter1)
                    break
        for letter in to_remove:
            del g_wip[letter]
        to_remove = []

    if len(g_wip) == len(self._morph):
        raise ValueError(f'failed to simplify {self}')

    Z = alphabet[:len(g_wip)] if alphabet else self._domain.alphabet()[:len(g_wip)]
    g = {letter : image for letter, image in zip(Z, g_wip.values())}

    # Find f by using g on self "in reverse".
    f = {}
    for letter1, image1 in self._morph.items():
        image3 = []
        while True:
            for letter2, image2 in g.items():
                if image2.is_prefix(image1):
                    image1 = image1[image2.length():]
                    image3.append(letter2)
                    break
            if not image1:
                break
        f[letter1] = image3

    FW_Z = FiniteWords(Z)
    f = type(self)(f, domain=self._domain, codomain=FW_Z)
    g = type(self)(g, domain=FW_Z, codomain=self._codomain)
    return f, g

def simplify_injective(self, alphabet=None):
    """
    TODO

    If self is not injective, return a triplet (k, f, g), where k is a injective
    simplification of self with respect to (f, g).

    Let h be a morphism X^*->X^*. If h is not injective, then there exist morphisms
    f: X^*->Z^* and g: Z^*->X^* such that h = g o f, k = f o g is injective and #Z < #X.
    The morphism k is then called the injective simplification of h with respect to (f, g).

    # RE 83
    # if self is injective
    # mention that f has to be ^k
    # rename h, f, g, k to f, h, k, g

    EXAMPLES::

        sage: a = WordMorphism('a->bca,b->bcaa,c->bcaaa'); a.simplify_injective('xy')
        (WordMorphism: a->xy, b->xyy, c->xyyy, WordMorphism: x->bc, y->a)
        sage: b = WordMorphism('a->abc,b->bc,c->a'); b.simplify_injective('xy')
        (WordMorphism: a->xy, b->y, c->x, WordMorphism: x->a, y->bc)
        sage: c = WordMorphism('a->aca,b->badc,c->acab,d->adc'); c.simplify_injective('xyz')
        (WordMorphism: a->x, b->zy, c->xz, d->y, WordMorphism: x->aca, y->adc, z->b)
        sage: d = WordMorphism('a->1,b->011,c->01110,d->1110'); d.simplify_injective('xyz')
        (WordMorphism: a->y, b->xyy, c->xyyyx, d->yyyx, WordMorphism: x->0, y->1) # nope
        sage: e = WordMorphism('a->abc,b->bc,c->a,f->'); e.simplify_injective('xy')
        (WordMorphism: a->xy, b->y, c->x, f->, WordMorphism: x->a, y->bc)
        sage: f = WordMorphism('a->a,b->,c->c'); f.simplify_injective('xy')
        (WordMorphism: a->x, b->, c->y, WordMorphism: x->a, y->c)

        WordMorphism('a->abc,b->a,c->bc')
    """
    assert(self.is_endomorphism())
    f, g = simplify(self, alphabet)
    k = f * g
    for i in count(start=1):
        try:
            f_new, g_new = simplify(k, alphabet)
            k, f, g = f_new * g_new, f_new * f, g * g_new
        except:
            return k, f, g, i

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
                    s = IntegerRing()(history[u])
                    t = IntegerRing()(i - history[u])
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

    assert(self.is_endomorphism())
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
    assert(self.is_endomorphism())
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

    EXAMPLES::

        sage: WordMorphism('a->0,b->10,c->110,d->111').is_injective()
        True
        sage: WordMorphism('a->0,b->010,c->01,d->10').is_injective()
        False

    TESTS::

        sage: WordMorphism('a->10,b->00,c->11,d->110').is_injective()
        True
        sage: WordMorphism('a->0,b->0,c->1,d->1').is_injective()
        False
        sage: WordMorphism('a->1,b->011,c->01110,d->1110,e->10011').is_injective()
        False
        sage: WordMorphism('').is_injective()
        True
        sage: WordMorphism('a->').is_injective()
        False
        sage: WordMorphism('a->b').is_injective()
        True
        sage: WordMorphism('a->,b->').is_injective()
        False
        sage: WordMorphism('a->a,b->').is_injective()
        False
        sage: WordMorphism('a->,b->b').is_injective()
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

# ================================================
# OTHER
# ================================================

def unbounded_letters(self):
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

def periodic_points_fixed(self):
    from sage.misc.callable_dict import CallableDict
    from sage.combinat.words.morphism import PeriodicPointIterator

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
