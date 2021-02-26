from itertools import islice
from sage.combinat.words.words import FiniteWords

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

def is_simplifiable(self, return_fg=False, alphabet=None):
    """

    EXAMPLES::

        sage: a = WordMorphism('a->bca,b->bcaa,c->bcaaa'); a.is_simplifiable(True, 'xy')
        (True, WordMorphism: a->xy, b->xyy, c->xyyy, WordMorphism: x->bc, y->a)
        sage: b = WordMorphism('a->abc,b->bc,c->a'); b.is_simplifiable(True, 'xy')
        (True, WordMorphism: a->xy, b->y, c->x, WordMorphism: x->a, y->bc)
        sage: c = WordMorphism('a->aca,b->badc,c->acab,d->adc'); c.is_simplifiable(True, 'xyz')
        (True,
         WordMorphism: a->x, b->zy, c->xz, d->y,
         WordMorphism: x->aca, y->adc, z->b)
        sage: d = WordMorphism('a->1,b->011,c->01110,d->1110'); d.is_simplifiable(True, 'xyz')
        (True, WordMorphism: a->y, b->xyy, c->xyyyx, d->yyyx, WordMorphism: x->0, y->1)
        sage: e = WordMorphism('a->abc,b->bc,c->a,f->'); e.is_simplifiable(True, 'xy')
        (True, WordMorphism: a->xy, b->y, c->x, f->, WordMorphism: x->a, y->bc)
        sage: f = WordMorphism('a->a,b->,c->c'); f.is_simplifiable(True, 'xy')
        (True, WordMorphism: a->x, b->, c->y, WordMorphism: x->a, y->c)

        # add example which is still simplifiable after simplification
    """
    # Remove erasing letters.
    g_wip = dict(self._morph)
    for letter, image in self._morph.items():
        if not image:
            del g_wip[letter]

    if not return_fg and len(g_wip) < len(self._morph):
        return True

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

    if not return_fg:
        return len(g_wip) < len(self._morph)
    elif len(g_wip) == len(self._morph):
        return False, None, None

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
    return True, f, g

def bounded_letters(self):
    """

    EXAMPLES::

        sage: WordMorphism('a->ab,b->ba').bounded_letters()
        []
        sage: WordMorphism('a->abc,b->b,c->,d->dd').bounded_letters()
        ['b', 'c']
        sage: WordMorphism('a->ab,b->a,c->b').bounded_letters()
        []
        sage: WordMorphism('a->b,b->a').bounded_letters()
        ['a', 'b']
        sage: WordMorphism('a->b,b->c,c->a').bounded_letters()
        ['a', 'b', 'c']
    """
    assert(all(x in self._domain.alphabet() for x in self._codomain.alphabet()))

    bounded = set()
    unbounded = dict()
    undecided = dict()

    # Change alphabet into integers 0 ... n-1 so that we can add a letter
    # for sure not in the alphabet.
    alphabet = self._domain.alphabet()
    to_integer = {e : i for i, e in enumerate(alphabet)}
    for letter, image in self._morph.items():
        unbounded[to_integer[letter]] = [to_integer[x] for x in image]
    terminal = -1

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

    return [alphabet[x] for x in sorted(bounded)]
