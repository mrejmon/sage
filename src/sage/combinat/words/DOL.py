from itertools import islice, count
from collections import Counter

from sage.rings.all import IntegerRing
from sage.combinat.words.words import FiniteWords
from sage.combinat.words.morphism import get_cycles


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
    def _check_if_equal_and_add_new_tail_if_possible(w1, w2, tails_stack, tails_set):
        if len(w1) == len(w2) and w1 == w2:
            return False
        elif len(w1) < len(w2) and w1.is_prefix(w2):
            tail = w2[len(w1):]
            if tail not in tails_set:
                tails_set.add(tail)
                tails_stack.append(tail)
        elif len(w1) > len(w2) and w1.has_prefix(w2):
            tail = w1[len(w2):]
            if tail not in tails_set:
                tails_set.add(tail)
                tails_stack.append(tail)
        return True

    values = self._morph.values()
    # Edge case.
    if len(values) == 1 and next(iter(values)).is_empty(): return False
    # Tail 't' is a word such that a = bt or b = at, where either both 'a' and 'b' are "code words",
    # or 'a' is a code word and 'b' is another tail.
    # Morphism is injective iff no tail is equal to a code word.

    # A stack is used for keeping track of tails we still have to check.
    tails_stack = []
    # A set is used to quickly check whether we saw this tail already.
    tails_set = set()
    # In the first part of the algorithm we check the case where both 'a' and 'b' are code words.
    for i, v1 in enumerate(values):
        for v2 in islice(values, i + 1, None):
                if not _check_if_equal_and_add_new_tail_if_possible(v1, v2, tails_stack, tails_set):
                    return False
    # In the second part of the algorithm we check the case where 'a' is a code word and 'b' is another tail.
    while len(tails_stack) != 0:
        tail = tails_stack.pop()
        for v in values:
            if not _check_if_equal_and_add_new_tail_if_possible(tail, v, tails_stack, tails_set):
                return False
    # No tail was equal to a codeword, morphism is injective.
    return True

def _simplify_injective_once(self, alphabet=None):
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
    """
    assert(self.is_endomorphism())
    f, g = _simplify_injective_once(self, alphabet)
    k = f * g
    for i in count(start=1):
        try:
            f_new, g_new = _simplify_injective_once(k, alphabet)
            k, f, g = f_new * g_new, f_new * f, g * g_new
        except:
            return k, f, g, i

def unbounded_letters(self):
    """
    TODO

    EXAMPLES::

        sage: sorted(WordMorphism('a->ab,b->ba').unbounded_letters())
        ['a', 'b']
        sage: sorted(WordMorphism('a->abc,b->b,c->,d->dd').unbounded_letters())
        ['a']
        sage: sorted(WordMorphism('a->ab,b->a,c->b').unbounded_letters())
        ['a', 'b', 'c']
        sage: sorted(WordMorphism('a->b,b->a').unbounded_letters())
        []
        sage: sorted(WordMorphism('a->b,b->c,c->a').unbounded_letters())
        []
    """
    assert(self.is_endomorphism())

    bounded = set()
    unbounded = dict(self._morph)
    undecided = dict()

    # Need a letter not in the alphabet.
    terminal = '#'
    while terminal in self._codomain.alphabet():
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

    return set(unbounded)

# g = {0 : (6, '0'), 1 : (6, '1'), 2 : (0, '2'), 3 : (1, '3'), 4 : (4, '4'), 5 : (3, '5'), 6 : (3, '6'), 7 : (4, '7'), 8 : (0, '8')}
# for x in functional_graph_cycle_iter(g): print(x)
def _functional_graph_cycle_iter(graph):
    visited, removed = set(), set()
    for u in graph:
        if u in removed:
            continue
        visited.add(u)
        history_vertices = [u]
        history_labels = []
        while True:
            v, label = graph[u]
            history_labels.append(label)
            if v in visited:
                if v not in removed:
                    i = history_vertices.index(v)
                    yield history_labels[i:]
                removed.update(history_vertices)
                break
            history_vertices.append(v)
            visited.add(v)
            u = v

def iter_inf_factors_without_growing_letters(self, conjugates=True):
    """
    """
    def impl(g, unbounded, reversed):
        if reversed: # <--
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
            if reversed: # <--
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
            yield res.primitive()

    assert(self.is_endomorphism())
    try:
        g, _, k, _ = self.simplify_injective()
    except ValueError:
        g, k = self, self.domain().identity_morphism()
    unbounded = g.unbounded_letters()

    for x in impl(g, unbounded, False): # UL.
        yield k(x).primitive()
    for x in impl(g, unbounded, True): # UR.
        yield k(x).primitive()

def iter_inf_factors_without_growing_letters_OLD(self, conjugates=True):
    """
    """
    def to_period(u, q, g):
        history = dict({u : 0})
        for i in count(1):
            u = g(u)
            if u in history:
                s = IntegerRing()(history[u])
                t = IntegerRing()(i - history[u])
                break
            history[u] = i
        l0 = (s / q).ceil() * q
        l1 = l0 + (t.lcm(q) / q)
        gq = g ** q
        uql = gq(u, l0)
        res = g.domain()()
        for _ in range(l0+1, l1+1):
            uql = gq(uql)
            res += uql
        return res.primitive()

    assert(self.is_endomorphism())
    try:
        g, _, k, _ = self.simplify_injective()
    except ValueError:
        g, k = self, self.domain().identity_morphism()
    unbounded = g.unbounded_letters()

    # Construct UL and UR.
    UL, UR = dict(), dict()
    for x in unbounded:
        hx = g.image(x)
        for i, y in enumerate(hx):
            if y in unbounded:
                break
        UL[x] = y, hx[:i]
        for i, y in enumerate(reversed(hx)):
            if y in unbounded:
                break
        UR[x] = y, hx[hx.length()-i:]

    # Find inf. factors in UL.
    for cycle in get_cycles(lambda x: UL[x][0], domain=unbounded):
        if all(not UL[x][1] for x in cycle):
            continue
        u = g.domain()()
        for x in cycle:
            u = g(u)
            u = u + UL[x][1]
        yield k(to_period(u, len(cycle), g)).primitive()

    # Find inf. factors in UR.
    for cycle in get_cycles(lambda x: UR[x][0], domain=unbounded):
        if all(not UR[x][1] for x in cycle):
            continue
        u = g.domain()()
        for x in cycle:
            u = g(u)
            u = UR[x][1] + u
        yield k(to_period(u, len(cycle), g)).primitive()

def iter_inf_factors_with_growing_letter(self, conjugates=True):
    """
    """
    assert(self.is_endomorphism())
    try:
        g, _, k, _ = self.simplify_injective()
    except ValueError:
        g, k = self, self.domain().identity_morphism()
    unbounded = g.unbounded_letters()

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
            yield k(v).primitive()

def iter_inf_factors(self, conjugates=True):
    for x in self.iter_inf_factors_without_growing_letters(conjugates):
        yield x
    for x in self.iter_inf_factors_with_growing_letter(conjugates):
        yield x

def is_pushy(self):
    try:
        next(self.iter_inf_factors_without_growing_letters(False))
    except StopIteration:
        return False
    return True

def is_unboundedly_rep(self):
    try:
        next(self.iter_inf_factors_with_growing_letter(False))
    except StopIteration:
        return False
    return True

def is_repetitive(self):
    return self.is_pushy() or self.is_unboundedly_repetitive()
