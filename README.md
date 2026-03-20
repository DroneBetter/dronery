this library consists of a 'core' (things i use frequently and don't want to reimplement on-the-fly in my projects/ephemeral shell experiments), and various offshoots (ideas i find cool, but are narrow or impractical and used little)

it is intended as complementary in functionality to computer algebra systems, so doesn't grow much in directions that are easy to do with them; growth/fixes in the core usually occur when i need to do a new task, or an existing task in a different way

some things can already be done with SymPy but are reimplemented here because i want them to be more hackable/closer to Python primitives (ie. polynomials as lists)

a few pieces have a little bit of documentation/canonically associated writing; these are few on account of the code is its own documentation that is always up-to-date!
*matrix.py has [matrix.html](https://dronebetter.github.io/matrix.html) (although that is currently about ideas that it can be bent into doing rather than its functionality directly)
*linRecur.py's `nthTerm` function (and the eigenbasis of a companion matrix) is explained by [linear recurrence](https://oeis.org/wiki/User:Natalia_L._Skirrow/linear_recurrence)
*perms.py is explained by [Stirling factoradic](https://oeis.org/wiki/User:Natalia_L._Skirrow/Stirling_factoradics)

##disclaimers
*it is made for my own use with no regard for anyone else
*the code is generally quite terse and onelinerful because i like it that way
*i will change functionality and input/output formats of existing functions whenever i want if i think the new way is more sensical, or on a stylistic whim

##considerations for pieces
###poly
*the `factorise` function is slow because I've only implemented Kronecker's algorithm (together with the trick where `gcd(p,p')` has all `p`'s factors with multiplicity decremented (proof: product rule), allowing the factors to be stratified by multiplicity first); if it stalls for longer than your patience, put the polynomial into SymPy or Mathematica or something instead.

[readme incomplete]
