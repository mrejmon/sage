from itertools import islice

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

def simplify(self):
    """

    EXAMPLES::

        a = WordMorphism('a->bca,b->bcaa,c->bcaaa'); a.simplify()
        b = WordMorphism('a->abc,b->bc,c->a'); b.simplify()
        c = WordMorphism('a->aca,b->badc,c->acab,d->adc'); c.simplify()
        d = WordMorphism('a->1,b->011,c->01110,d->1110'); d.simplify()

    """
    # Helper function, invariant: val1.empty() == False.
    def _helper(val1, val2):
        # Remove prefixes.
        if val1.length() > val2.length():
            return val2
        a, b = 0, 0
        while True:
            if val1[a] != val2[b]:
                break
            a += 1
            b += 1
            if a == val1.length():
                a = 0
            if b == val2.length():
                break
        # Remove suffixes.
        if val1.length() > val2.length()-(b-a):
            return val2[b-a:]
        c, d = val1.length()-1, val2.length()-1
        while True:
            if val1[c] != val2[d]:
                break
            c -= 1
            d -= 1
            if c == -1:
                c = val1.length()-1
            if d == (b-a)-1:
                break
        return val2[b-a:d+val1.length()-c]

    # Setup.
    g = dict(self._morph)
    to_do = set(self._morph)
    to_remove = []

    while to_do:
        key1 = to_do.pop()
        val1 = g[key1]
        for key2, val2 in g.items():
            if key1 == key2:
                continue
            res = _helper(val1, val2)
            if len(res) == 0:
                to_remove.append(key2)
                to_do.discard(key2)
            elif len(res) != len(val2):
                assert(len(res) < len(val2))
                g[key2] = res
                to_do.add(key2)
        for key in to_remove:
            del g[key]
        to_remove = []

    return g
