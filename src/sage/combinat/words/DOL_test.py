import random
import string
from functools import wraps
from sage.combinat.words.morphism import WordMorphism

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
        def wrapper(a1=3, a2=4, a3=5, i1=0, i2=5, i3=10, cnt=10, seed=18, debug=True, **kwargs):
            random.seed(seed)
            for i in range(cnt):
                print(f'\r{i}                    ', end='')
                h = WordMorphism(create_random_morphism(a1, a2, a3, i1, i2, i3))
                if debug: print(f'\n{h}')
                f(h, debug, logger, **kwargs)
            print(f'\r{cnt}')
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
def test_bounded_letters(h, debug, logger):
    bounded1 = set(h.bounded_letters())
    if debug: print(sorted(bounded1))
    h._codomain = h._domain
    bounded2 = set(h.domain().alphabet()) - set(h.growing_letters())
    if debug: print(sorted(bounded2))
    assert(bounded1 == bounded2)

@_test()
def test_is_simplifiable(h, debug, logger):
    is_injective = h.is_injective()
    if debug: print(f'is_injective: {is_injective}')
    is_simplifiable, f, g = h.is_simplifiable(True, string.ascii_uppercase)
    if debug: print(f'is_simplifiable: {is_simplifiable}')
    if not is_simplifiable:
        assert(is_injective) # At least a partial test.
    else:
        if debug: print(f'G: {g}\nF: {f}')
        k = f * g
        if debug: print(f'K: {k}')
        h2 = g * f
        if debug: print(f'H?: {g * f}')
        assert(h == g * f)

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
  Sardinas-Patterson algorithm. Prints diagnostic output to err."""
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
