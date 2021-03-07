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
