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

    TEST::

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

def is_simplifiable(self, alphabet, *, bool_only=False):
    """

    EXAMPLES::

        sage: a = WordMorphism('a->bca,b->bcaa,c->bcaaa'); a.is_simplifiable('xy')
        (True, WordMorphism: a->xy, b->xyy, c->xyyy, WordMorphism: x->bc, y->a)
        sage: b = WordMorphism('a->abc,b->bc,c->a'); b.is_simplifiable('xy')
        (True, WordMorphism: a->xy, b->y, c->x, WordMorphism: x->a, y->bc)
        sage: c = WordMorphism('a->aca,b->badc,c->acab,d->adc'); c.is_simplifiable('xyz')
        (True,
         WordMorphism: a->x, b->zy, c->xz, d->y,
         WordMorphism: x->aca, y->adc, z->b)
        sage: d = WordMorphism('a->1,b->011,c->01110,d->1110'); d.is_simplifiable('xyz')
        (True, WordMorphism: a->y, b->xyy, c->xyyyx, d->yyyx, WordMorphism: x->0, y->1)
        sage: e = WordMorphism('a->abc,b->bc,c->a,f->'); e.is_simplifiable('xy')
        (True, WordMorphism: a->xy, b->y, c->x, f->, WordMorphism: x->a, y->bc)
    """
    # Remove erasing letters.
    to_remove = []
    for letter, image in self._morph.items():
        if not image:
            to_remove.append(letter)
    g_wip = dict(self._morph)
    if to_remove:
        if bool_only:
            return False
        for letter in to_remove:
            del g_wip[letter]
        for letter, image in g_wip.items():
            new_image = [x for x in image if x not in to_remove]
            g_wip[letter] = self._codomain(new_image, datatype='list', check=False)
        to_remove = []

    # Simplify (find morphism g).
    to_do = set(g_wip)
    while to_do:
        key1 = min(to_do)
        to_do.remove(key1)
        val1 = g_wip[key1]
        for key2, val2 in g_wip.items():
            if key1 == key2:
                continue
            if len(val1) == len(val2):
                if val1 == val2:
                    to_remove.append(key2)
                    to_do.discard(key2)
            elif len(val1) < len(val2):
                if val1.is_prefix(val2):
                    g_wip[key2] = val2[len(val1):]
                    to_do.add(key2)
                elif val1.is_suffix(val2):
                    g_wip[key2] = val2[:-len(val1)]
                    to_do.add(key2)
            else:
                if val2.is_prefix(val1):
                    g_wip[key1] = val1[len(val2):]
                    to_do.add(key1)
                    break
                elif val2.is_suffix(val1):
                    g_wip[key1] = val1[:-len(val2)]
                    to_do.add(key1)
                    break
        for key in to_remove:
            del g_wip[key]
        to_remove = []

    if len(g_wip) == len(self._domain.alphabet()):
        return False if bool_only else (False, None, None)
    elif bool_only:
        return True

    Z = alphabet[:len(g_wip)] if alphabet else self._domain.alphabet()[:len(g_wip)]
    g = {letter : image for letter, image in zip(Z, g_wip.values())}

    # Find f by using g on self "in reverse".
    f = {}
    for letter1, image1 in self._morph.items():
        image3 = []
        while True:
            for letter2, image2 in g.items():
                if image1[:image2.length()] == image2:
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
