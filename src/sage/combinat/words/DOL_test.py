import random
import string
from functools import wraps
from sage.combinat.words.morphism import WordMorphism
from sage.combinat.words.words import FiniteWords
from itertools import product

def geometric_sample(EX, start, end):
    p = 1/EX
    i = start
    while i < end and random.random() < (1-p):
        i += 1
    return i

def create_random_morphism(a1=3, a2=4, a3=5, i1=0, i2=5, i3=10):
    h = dict()
    X_size = geometric_sample(a2, a1, a3)
    X = string.ascii_lowercase[:X_size]
    for letter in X:
        image_size = geometric_sample(i2, i1, i3)
        h[letter] = random.choices(X, k=image_size)
    return WordMorphism(h)

def _test(logger=None):
    def decorator(f):
        @wraps(f)
        def wrapper(a1=3, a2=4, a3=5, i1=0, i2=5, i3=10, cnt=10000, rndom=True, e1=3, e2=8, seed=18, debug=False, **kwargs):
            if rndom:
                random.seed(seed)
                for i in range(cnt):
                    print(f'\r{i}                    ', end='')
                    h = WordMorphism(create_random_morphism(a1, a2, a3, i1, i2, i3))
                    if debug: print(f'\n{h}')
                    f(h, debug, logger, **kwargs)
                print(f'\r{cnt}')
            else:
                F = FiniteWords(string.ascii_lowercase[:e1])
                for i, h in enumerate(F.iter_morphisms((e1, e2+1))):
                    print(f'\r{i}                    ', end='')
                    if debug: print(f'\n{h}')
                    f(h, debug, logger, **kwargs)
                print(f'\r{i+1}')
            return logger
        return wrapper
    return decorator

@_test([0])
def test_is_injective(h, debug, logger):
    """
    sage: test_is_injective(i1=1, debug=False, cnt=10000)
    10000
    [8743]
    """
    is_injective1 = h.is_injective()
    if debug: print(is_injective1)
    is_injective2 = _IsUniquelyDecodable(list(str(x) for x in h._morph.values()))
    if debug: print(is_injective2)
    assert(is_injective1 == is_injective2)
    if is_injective1: logger[0] += 1

@_test()
def test_unbounded_letters(h, debug, logger):
    unbounded1 = set(h.unbounded_letters())
    if debug: print(sorted(unbounded1))
    h._codomain = h._domain
    unbounded2 = set(h.growing_letters())
    if debug: print(sorted(unbounded2))
    assert(unbounded1 == unbounded2)

def _necessary_condition_for_elementary(self):
    alph = [set(image) for image in self._morph.values()]
    for x in product(*alph):
        if len(set(x)) == len(x):
            return True
    return False

@_test()
def test_simplify_injective(h, debug, logger):
    try:
        k, f, g = h.simplify_injective(string.ascii_uppercase)
    except ValueError:
        if debug: print('failed to simplify')
        assert(h.is_injective())
    if debug: print(f'G: {g}\nF: {f}\nK: {k}')
    assert(len(k._domain.alphabet()) < len(h._domain.alphabet()))
    assert(k.is_injective())
    h2 = g * f
    if debug: print(f'H?: {h2}')
    assert(h == h2)

@_test()
def find_counter_examples(h, debug, logger):
    if len(h._morph) == len(set().union(*h._morph.values())):
        try:
            _ = h._simplify_injective_once(string.ascii_uppercase)
        except ValueError:
            ncfe = _necessary_condition_for_elementary(h)
            if not ncfe:
                print(h)
                assert(h.is_injective())

@_test([0])
def tmp(h, debug, logger):
    try:
        f, g = h._simplify_injective_once()
        k = f * g
    except ValueError:
        return
    try:
        f2, g2 = k._simplify_injective_once()
        k2 = f2 * g2
    except ValueError:
        return
    logger[0] += 1
    if debug: print(f'k: {k}\nf: {f}\ng: {g}\nk2: {k2}\nf2: {f2}\ng2: {g2}')
    F = f2 * f
    G = g * g2
    if debug: print(f'F = f2 * f: {F}\nG = g * g2: {G}\nF * G: {F * G}\nG * F: {G * F}')
    assert(h**2 == G * F)
    assert(k2**2 == F * G)

@_test()
def tmp2(h, debug, logger):
    h._codomain = h._domain
    gen = h.iter_inf_factors_with_growing_letter()
    lst = list(gen)
    if not lst:
        return
    print(h)
    for x in lst:
        print(x)

# ------------------------------------------------------------------------------
# https://goo.gl/kkF5SY
# https://gist.github.com/lcpz/fc02cbf6f0108259302ee4b7d9924dbe

def _LeftQuotientOfWord(ps, w):
  """Yields the suffixes of w after removing any prefix in ps."""
  for p in ps:
    if w.startswith(p):
      yield w[len(p):]
  return

def _LeftQuotient(ps, ws):
  """Returns the set of suffixes of any word in ws after removing any prefix
  in ps. This is the quotient set which results from dividing ws on the
  left by ps."""
  qs = set()
  for w in ws:
    for q in _LeftQuotientOfWord(ps, w):
      qs.add(q)
  return qs

def _IsUniquelyDecodable(cs_list):
  """Checks if the set of codewords cs is uniquely decodable via the
  Sardinas-Patterson algorithm."""
  cs = set(cs_list)
  if len(cs) < len(cs_list):
    return False
  s = _LeftQuotient(cs, cs)
  s.discard('')
  if len(s) == 0:
    return True
  NL, i = sum(len(x) for x in cs), 0
  while '' not in s and len(s & cs) == 0:
    t = _LeftQuotient(cs, s) | _LeftQuotient(s, cs)
    if t == s or i > NL: # wrong, equality with all previous sets should be checked, NL is a bandaid
      return True
    s = t
    i += 1
  return False
