# Opposite shifts do not repair the cross-normalized `A + B` argument

## Result

Let `A` and `B` be two equally large sets of positive integers.  Replacing
them by

\[
  A+c,\qquad B-c
\]

preserves every cross-sum.  Nevertheless, there need not be any
positivity-preserving integer `c` for which the pairwise cross-normalized
matching slack is nonnegative at all support primes.  In fact, the
construction below has one odd support prime `p` whose slack is strictly
negative for **every** admissible `c`, even after:

1. equality pairs are discarded;
2. the best possible matching of numerator edges is used.

Thus an opposite shift alone does not extend the normalized `A+A`
square-root proof to balanced `A+B`.  This is an obstruction to that proof
mechanism, not a counterexample to a polynomial lower bound for `A+B`.

## The local quantity that a cross-normalized proof needs

Fix an odd prime `p` and a positive shift

\[
  X=A+c,\qquad Y=B-c.
\]

For a cross-pair `(x,y)`, divide `x+y` and `|x-y|` by their common
pairwise normalizer.  If neither endpoint is divisible by `p`, the normalizer
is a `p`-adic unit, so it does not affect the following valuation count.

In one nonzero residue orbit `{r,-r}`, put

\[
 x=|X_r|,\quad x'=|X_{-r}|,
 \qquad y=|Y_r|,\quad y'=|Y_{-r}|.
\]

At the first `p`-adic threshold, cross-differences contribute
`xy+x'y'`, cross-sums contribute `xy'+x'y`, and a maximum numerator
matching contributes

\[
  \min(x,y')+\min(x',y).
\]

Consequently the local cross-normalized slack is

\[
 xy+x'y'-xy'-x'y+\min(x,y')+\min(x',y).       \tag{1}
\]

For `(x,x';y,y')=(m,0;0,m)`, (1) equals

\[
  -m^2+m<0\qquad(m\ge2).                       \tag{2}
\]

This is exactly where the one-set identity fails: in the `A+A` case the two
copies have identical residue counts, and the corresponding expression
becomes a nonnegative binomial coefficient.

## A construction defeating every admissible shift

Choose integers `s >= 3`, `m >= 4`, an odd prime `p > 2m`, and a set

\[
  U=\{u_1,\ldots,u_s\}\subset\{1,\ldots,p-1\}
\]

such that all sums `u+v` with distinct `u,v in U` are different modulo `p`.
For example, take powers of two and then take `p` larger than every relevant
integer sum.  Define

\[
 A=\{u+p\ell:u\in U,\ 0\le\ell<m\},
 \qquad
 B=\{p-u+p\ell:u\in U,\ 0\le\ell<m\}.         \tag{3}
\]

Both sets have size `sm`.  Write `u_- = min U` and `u_+ = max U`.
Positivity of both shifted sets is equivalent to

\[
  1-u_-\le c\le p-u_+-1.                       \tag{4}
\]

For every `c` in (4) and every `u in U`,

\[
  1\le u+c\le p-1.                             \tag{5}
\]

Thus no shifted endpoint in these residue classes is divisible by `p`, and
the pairwise normalizers are all `p`-adic units.

The shifted residues belonging to label `u` are

\[
  A+c:\ u+c,
  \qquad B-c:\ -(u+c).                         \tag{6}
\]

For equal labels, every cross-sum is

\[
 (u+p\ell)+(p-u+p\ell')=p(1+\ell+\ell').       \tag{7}
\]

Since `1+ell+ell' < p`, its `p`-adic order is exactly one.  Cross-sums
with unequal labels are not divisible by `p`.  Hence the total normalized
numerator `p`-mass is `s m^2`, while any matching captures at most `sm` of
that mass.

A cross-difference between labels `u` and `v` can be divisible by `p` only
if

\[
  u+v+2c\equiv0\pmod p.                        \tag{8}
\]

The Sidon condition on the two-element sums says that, for a fixed `c`, at
most one unordered pair `{u,v}` satisfies (8).  There is no fixed label:
`u=v` in (8) would give `u+c=0 mod p`, contrary to (5).  Let `q` be the
number of reflected label pairs; then `q <= 1`.

Discard any cross-pairs for which the shifted endpoints are equal.  Such
pairs form a matching, and a logarithmic normalized-distance argument has to
discard them anyway because their distance is zero.  All remaining shifted
endpoints lie in `[1,pm-1]`.  Therefore every nonzero cross-difference
divisible by `p` has order exactly one.  Only the two ordered rectangles
belonging to each reflected label pair can contribute, so the denominator
`p`-mass is at most `2q m^2`.

It follows that even the optimal matched slack is at most

\[
  2q m^2-sm^2+sm
   =-(s-2q)m^2+sm.                              \tag{9}
\]

Since `s >= 3`, `q <= 1`, and `m >= 4`, (9) is negative.  In the worst case
`s=3,q=1`, it is `-m^2+3m < 0`.  This proves the claimed obstruction for
every positivity-preserving shift.

The prime `p` is genuinely a support prime by (7), but it is not a common
divisor of `A+B`: sums with unequal labels are nonzero modulo `p`.  Moreover,
the `p`-divisible numerator edges comprise `s` disjoint copies of `K_{m,m}`.
Deleting all of them costs `sm^2`, not the `O(sm)` cost of deleting a
matching.  Thus this is not the removable case where one globally divides a
common prime or deletes a few exceptional edges.

An explicit instance is

\[
 U=\{1,2,4\},\qquad m=4,\qquad p=11.
\]

Here the admissible shifts are `0 <= c <= 6`, and (9) is always at most
`-4`.

## What survives for `A+B`

This obstruction concerns **cross normalization**, where `|x-y|` is paired
edgewise with `x+y` in order to retain the positive logarithmic gap

\[
  \log\frac{x+y}{|x-y|}.
\]

The raw bipartite Cauchy/Vandermonde lemma is different.  Its denominator is
made from differences internal to `A` and internal to `B`.  At a sum
component of sizes `x,y`, deleting a maximum matching gives

\[
  \binom{x}{2}+\binom{y}{2}-xy+\min(x,y)
  =\binom{|x-y|}{2}\ge0.
\]

So the raw local bipartite matching lemma and the bipartite metric estimate
remain valid.  Opposite shifts preserve all cross-sums and both internal
Vandermondes, hence they do not change that raw quotient at all.  The missing
ingredient there is global: cross numerator edges and the two families of
within-part denominator edges do not admit the edgewise nonnegative
potential used by the biased `A+A` sampling proof.

Accordingly, the rigorous conclusion is:

* **No** shift-only reduction proves a polynomial `A+B` bound by reusing the
  cross-normalized `A+A` slack.
* The example does **not** rule out a polynomial balanced-`A+B` theorem by a
  new correlated two-part sampling argument based on the raw bipartite
  Cauchy lemma.

