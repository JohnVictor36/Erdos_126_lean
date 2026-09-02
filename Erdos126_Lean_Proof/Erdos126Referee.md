# Referee report on `proof.md`

## Verdict

I tried to break the argument at the normalization, nested-matching,
conditioning, support, and ordered/unordered-pair interfaces.  I did not find
a counterexample or a false inequality.  Subject to the clarifications below,
the paper proof does establish

\[
  |P(A)| \gg \sqrt{|A|}.
\]

This would be a substantial improvement on the bound normally quoted for
Erdős Problem 126, so this report should not be treated as a substitute for an
independent expert referee and a literature/priority check.  My mathematical
recommendation is **accept after revision**, not rejection.

The most important issue is expositional rather than mathematical: the object
called \(S_p(T)\) must be tied to a *simultaneously saturating* matching.  It is
not true for an arbitrary matching that its slack is the displayed sum of
\(\binom{|x-y|}{2}\)'s.  Once the saturating choice is made, all subsequent
uses are valid.

## 1. Normalization and support

For an edge \(e=\{i,j\}\), put

\[
 g_e=(a_i,a_j),\qquad
 h_e=2^{\mathbf 1_{v_2(a_i)=v_2(a_j)}}g_e,
 \qquad U_e=(a_i+a_j)/h_e,\quad D_e=|a_i-a_j|/h_e.
\]

I checked the following points.

1.  Both quotients are integers.  In the equal-\(2\)-valuation case,
    \(a_i/g_e\) and \(a_j/g_e\) are coprime odd integers, so both their sum
    and difference are even.

2.  \(D_e\ge1\), since the elements of \(A\) are distinct.

3.  \(U_e\ge2\).  The only possible equality \((x+y)/2=1\) with positive
    odd \(x,y\) is \(x=y=1\), which would give \(a_i=a_j\).

4.  Every prime divisor of \(U_e\) divides the original sum \(a_i+a_j\).
    Thus the normalized numerator support is contained in \(P(A)\); equality
    is neither asserted nor needed.

5.  The edgewise ratio is unchanged:
    \(U_e/D_e=(a_i+a_j)/|a_i-a_j|>1\).  Consequently
    \(\mathcal A(T)-\mathcal B(T)\) is a sum of strictly positive edge
    weights whenever \(|T|\ge2\).

No factor of two or support reversal occurs here.

**Required clarification.**  Add the one-line argument for \(U_e\ge2\),
since it is used later to absorb the additive \(\log2\) cost of a matching.

## 2. The normalized \(p\)-adic matching lemma

The local reduction is correct.  If \(v_p(a_i)\ne v_p(a_j)\), division by
the pairwise gcd leaves one \(p\)-adic unit and one multiple of \(p\), so both
normalized sum and difference have valuation zero.  In a common exact
valuation stratum, their valuations are read from the unit parts.

For odd \(p\), at threshold \(t\ge1\), denominator edges lie within a unit
class modulo \(p^t\) and numerator edges run between \(u\) and \(-u\).
Negation has no fixed unit class.  The complementary components over all
thresholds form a laminar family.  A bottom-up matching saturates each
component simultaneously.  If the paired children have side sizes
\((x_s,y_s)\), then

\[
 \sum_s\min(x_s,y_s)
 +\min\!\left(\sum_s(x_s-y_s)_+,\sum_s(y_s-x_s)_+\right)
 =\min\!\left(\sum_sx_s,\sum_sy_s\right).
\]

This establishes the simultaneous-saturation claim, including the case of
empty sides.

For \(p=2\), the indexing should be made explicit.  With odd unit parts
\(u_i,u_j\), for normalized threshold \(t\ge1\),

\[
 2^t\mid D_{ij}\iff u_i\equiv u_j\pmod {2^{t+1}},\qquad
 2^t\mid U_{ij}\iff u_i\equiv -u_j\pmod {2^{t+1}}.
\]

Thus the first classes are modulo \(4\), and odd negation has no fixed point
at any relevant level.  This is exactly the same laminar matching problem.

For one paired component with side sizes \(x,y\), simultaneous saturation
gives

\[
 \binom{x}{2}+\binom{y}{2}-xy+\min(x,y)
 =\binom{|x-y|}{2}.
\]

Summing over thresholds is legitimate because valuations are finite and each
valuation is its number of satisfied thresholds.

**Required correction.**  Define \(M_p(T)\) from this saturation construction
and define \(S_p(T)\) using that matching, or instead define \(S_p(T)\) by the
component sum and then state that it is realized by a matching.  As currently
written, “there is a matching” followed by “define the logged slack” leaves
the choice implicit.  Later Lemma 3 uses the stronger component formula, not
merely nonnegativity.

The following bound, used in the conditioning step, should also be stated and
proved immediately:

\[
 0\le S_p(T)
 =\log p\sum_C\binom{|x_C-y_C|}{2}
 \le \mathcal B_p(T)\le\mathcal B_p(V).
\]

The middle inequality follows componentwise from
\(\binom{|x-y|}{2}\le\binom x2+\binom y2\).

## 3. Exact identity and prime support

For the saturating choice,

\[
 S_p(T)/\log p
 =\sum_{e\subset T}v_p(D_e)-\sum_{e\subset T}v_p(U_e)
   +\sum_{e\in M_p(T)}v_p(U_e).
\]

Summing over \(p\in P(A)\) gives

\[
 \mathcal A(T)-\mathcal B_P(T)+\sum_{p\in P(A)}S_p(T)
 =\sum_{p\in P(A)}\sum_{e\in M_p(T)}v_p(U_e)\log p.
\]

This is exact because every prime factor of every \(U_e\) belongs to
\(P(A)\).  Primes of the original sums that disappear under normalization
cause no problem: they may contribute to \(\mathcal B_P\), but then their
slack term cancels that contribution when they do not divide a normalized
numerator.

There is no ordered/unordered factor of two.  Every quantity in the paper is
summed over unordered edges; the official ordered off-diagonal product has
the same prime support because it merely squares the unordered product.

## 4. Biased sampling lemma

The sampling computation is correct.  A leading complementary pair is given
one random orientation.  Conditional on it, vertices are independent with
probabilities \(3/4\) on the favored side and \(1/4\) on the other.  Every
descendant complementary pair has its two sides contained in the two opposite
leading sides, so the same orientation controls all its levels.

For a descendant component with original side sizes \(c,d\) and selected
side sizes \(X,Y\), orientation averaging gives

\[
 \mathbb E\!\left[\binom X2+\binom Y2\right]
 =\frac5{16}\left(\binom c2+\binom d2\right),
 \qquad \mathbb E[XY]=\frac3{16}cd.
\]

Fix any injection pairing \(\min(c,d)\) vertices across the two sides.  Its
retained edges are a matching, hence their count is at most \(\min(X,Y)\),
and each is retained with probability \(3/16\).  Therefore

\[
 \mathbb E\min(X,Y)\ge\frac3{16}\min(c,d).
\]

Substitution yields exactly

\[
 \mathbb E\binom{|X-Y|}{2}
 \ge \frac18\left(\binom c2+\binom d2\right)
      +\frac3{16}\binom{|c-d|}{2}.
\]

After summation over all levels this is
\(\mathbb E S_p(T)\ge\mathcal B_p(V)/8\).

The pair-retention probabilities are also correct:

- opposite leading sides: \(3/16\);
- the same leading side, after orientation averaging: \(5/16\);
- independently oriented roots: \(1/4\).

Thus every edge is retained with probability at least \(3/16\).

Conditional on orientations, the vertex indicators are independent and have
means at least \(1/4\).  If \(\mu\ge k/4\), then
\(|T|<k/8\) implies \(|T|<\mu/2\), so the standard multiplicative Chernoff
bound gives \(\Pr(G^c)\le e^{-\mu/8}\le e^{-k/32}\).

**Required clarification.**  The truncation of the slack expectation uses
the unstated inequality \(S_p(T)\le\mathcal B_p(V)\) from Section 2 of this
report.  Add it before invoking the Chernoff estimate.

## 5. The metric matching estimate

The metric argument is correct.  With
\(x=a_i/g_{ij}\), \(y=a_j/g_{ij}\), one has

\[
 \rho_{ij}=\log(xy),\qquad
 \tfrac12\rho_{ij}\le\log U_{ij}\le\rho_{ij}+\log2.
\]

The lower bound follows from AM–GM, including in the equal-\(2\)-valuation
case where \(U=(x+y)/2\).  The upper bound follows from
\(x+y\le2xy\); it is deliberately non-sharp but sufficient.

For each matched edge and each third vertex, the valuation-vector triangle
inequality applies.  On summing, any unordered pair occurs at most twice on
the right: zero times if it is itself a matched edge, once if exactly one
endpoint is matched, and twice if the endpoints belong to two different
matched edges.  Hence

\[
 (N-2)\sum_{e\in M}\rho_e\le2\sum_{e\subset T}\rho_e
 \le4\mathcal A(T).
\]

Also \(|M|\log2\le N\log2/2\le\mathcal A(T)/(N-1)\), since every
\(U_e\ge2\).  For \(N\ge4\),

\[
 \frac4{N-2}+\frac1{N-1}\le\frac{10}{N}.
\]

No hidden dependence on the heights of the \(a_i\) occurs.

## 6. The final expectation comparison with explicit constants

The final use of \(\gg\) can and should be replaced by a short exact
calculation.  First note that \(r\ge1\), since \(k\ge2\) supplies at least one
sum greater than one.  Choose \(p_*\in P(A)\) with

\[
 \mathcal B_{p_*}(V)\ge Z/r,
 \qquad Z=\mathcal B_P(V).
\]

Let \(\delta=e^{-k/32}\), and put

\[
 X=\mathcal A(V)-\mathcal B(V),\quad
 Y=\mathcal B(V)-\mathcal B_P(V),\quad
 Z=\mathcal B_P(V).
\]

All three are nonnegative and \(X+Y+Z=\mathcal A(V)>0\).  Edge retention and
slack truncation give

\[
 \mathbb E[\mathbf1_G\mathcal L(T)]
 \ge(3/16-\delta)(X+Y)+(1/8-\delta)\mathcal B_{p_*}(V).
\]

The other prime slacks are nonnegative.  If \(\delta\le1/16\), then

\[
 \mathbb E[\mathbf1_G\mathcal L(T)]
 \ge\frac18(X+Y)+\frac1{16}\frac Zr
 \ge\frac1{16r}(X+Y+Z)
 =\frac{\mathcal A(V)}{16r}.
\]

For every outcome in \(G\), \(|T|\ge k/8\).  Once \(k\ge32\), Lemma 4 is
applicable and the exact identity gives

\[
 0\le\mathcal L(T)
 \le\frac{80r}{k}\mathcal A(T)
 \le\frac{80r}{k}\mathcal A(V).
\]

Therefore

\[
 \frac{\mathcal A(V)}{16r}
 \le\frac{80r}{k}\mathcal A(V),
 \qquad\text{so}\qquad k\le1280r^2.
\]

This applies for all \(k\) above an absolute threshold satisfying
\(e^{-k/32}\le1/16\) and \(k\ge32\).  Since \(r\ge1\), decreasing the final
absolute constant handles the finite remaining values.  The draft's proposed
safe constant \(1600\) is compatible with this calculation (and leaves room
for a separate zero-removal convention if the Lean statement permits zero).

## 7. Attempts to find counterexamples

The configurations most likely to expose an error all survive:

- all numbers in one residue class modulo a large power of \(p\): the
  normalized denominator has large \(p\)-mass, while the empty complementary
  side produces positive discrepancy slack;
- equal \(2\)-adic valuation for every number: the extra division by \(2\)
  shifts the residue tree from modulo \(2\) to modulo \(4\) and removes the
  fixed class;
- extremely lacunary numbers: the raw sum/difference quotient can have almost
  no archimedean slack, but the valuation metric still bounds the total cost
  of every matching;
- normalized numerators losing many primes of the original sums: the proof
  needs only support containment, and the \(-\mathcal B_P+S_p\) identity
  accounts for the lost primes exactly;
- components with one side empty or with highly unequal sizes: the bottom-up
  matching and the biased moment inequality both include these cases.

I therefore found no mathematical obstruction to the claimed square-root
bound.

## 8. Requested revisions before circulation

1. Define the saturating matching and the slack canonically enough that Lemma
   3 is visibly about the same \(S_p(T)\) as Lemma 2.
2. State and prove \(0\le S_p(T)\le\mathcal B_p(T)\le\mathcal B_p(V)\).
3. Write the \(p=2\) threshold congruences with the \(t+1\) shift explicitly.
4. Add the short proof that \(U_{ij}\ge2\).
5. Replace the final \(\gg\) paragraph with the explicit expectation
   inequalities above, including \(r\ge1\), \(\mathcal A(V)>0\), and the
   threshold needed for Lemma 4.
6. Keep the current warning that this major improvement requires external
   mathematical and literature review.

