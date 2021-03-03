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
