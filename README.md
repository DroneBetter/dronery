this library consists of a 'core' (things i use frequently and don't want to reimplement on-the-fly in my projects/ephemeral shell experiments), and various offshoots (ideas i find cool, but are narrow or impractical and used little)

it is intended as complementary in functionality to computer algebra systems, so doesn't grow much in directions that are easy to do with them; growth/fixes in the core usually occur when i need to do a new task, or an existing task in a different way

some things can already be done with SymPy but are reimplemented here because i want them to be more hackable/closer to Python primitives (ie. polynomials as lists)

a few pieces have a little bit of documentation/canonically associated writing; these are few on account of the code is its own documentation that is always up-to-date!
* matrix.py has [matrix.html](https://dronebetter.github.io/matrix.html) (although that is currently about ideas that it can be bent into doing rather than its functionality directly)
* linRecur.py's `nthTerm` function (and the eigenbasis of a companion matrix) is explained by [linear recurrence](https://oeis.org/wiki/User:Natalia_L._Skirrow/linear_recurrence)
* perms.py is explained by [Stirling factoradics](https://oeis.org/wiki/User:Natalia_L._Skirrow/Stirling_factoradics)

## disclaimers
* it is made for my own use with no regard for anyone else
* the code is generally quite terse and onelinerful because i like it that way
  * some new things are more idio(/s/syncr/m)atic and pleasant but i am operating mostly on the philosophy "if it ain't broke, don't fix it"
    * yes i know that elaborate Y-combinatude has a reasonableish amount of overhead which can be considered broke perhaps
* i will change functionality and input/output formats of existing functions whenever i want if i think the new way is more sensical, or on a stylistic whim
  * i decided long ago (mostly by virtue of this being the default option) that automated tests aren't worth the overhead of implementing and maintaining alongside the library's functionality, so sometimes this causes uncaught oversights in the interdependency web to make it into releases; sorry

### 'this sounds horrible'
a little bit yeah
### 'can any good come of this?'
well i am a big proponent of one's tools also being their objects of study; while dronery is generally not to come into direct contact with the OEIS or sympy or the outside world in general, developments in one do often precipitate the other!

it is a toy environment in which to make things from the ground up with no care for wherever else they already exist, and sometimes (ie. the [sympy `_bell_poly` module](https://github.com/sympy/sympy/pull/30372)) these transpire to be improvements

i also have some very strong Opinions on python design philosophy (like that [PEP 3113](https://peps.python.org/pep-3113) is stupid and `map(lambda i,(j,k): ...,enumerate(zip(a,b)))` should be valid to maintain parity with its listcomp counterpart) that would get me incinerated at any python conference, so to some extent this library may serve as a rectification of some of the decisions that i disagree with; for instance, [my thread "Making `combinations`, `combinations_with_replacement` and `permutations` indexable"](https://discuss.python.org/t/making-combinations-combinations-with-replacement-and-permutations-indexable/107834) was given little attention / deemed out-of-scope (~~doubtless due to [little-minded hobgoblins](https://peps.python.org/pep-0008/#a-foolish-consistency-is-the-hobgoblin-of-little-minds)~~) but those classes all have `.index` and `__getitem__` methods if you import them from dronery!

## considerations for pieces
### poly
* the `factorise` function is slow because I've only implemented Kronecker's algorithm (together with the trick where `gcd(p,p')` has all `p`'s factors with multiplicity decremented (proof: product rule), allowing the factors to be stratified by multiplicity first); if it stalls for longer than your patience, put the polynomial into SymPy or Mathematica or something instead.

## future plans
* some kinda power series streaming submodule (probably with separate o.g.f. and e.g.f. classes); for a lot of functions it's faster (ie. generally linear-time) to compute `output[n]` in terms of both `input[:n+1]` and `output[:n]` than `input[:n+1]` alone. (Cf. the essay [*Power Serious*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/19863F4EAACC33E1E01DE2A2114EC7DF/S0956796899003299a.pdf/power_series_power_serious.pdf))
