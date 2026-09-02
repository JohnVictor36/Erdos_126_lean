# Computational audit of the Erdős 126 square-root argument

## Verdict

The independent executable model in `Erdos126StressTest.py` found **no
counterexample** to any of the four tested interfaces.  The full deterministic
run completed with status `PASS` on 2 September 2026.

This is a stress test, not a proof.  Its useful role is narrower: it checks the
normalization conventions, ordered-pair factors of two, the simultaneous
threshold matching, and the exact constants in the biased expectation against
many concrete instances.  These are precisely the places where a silent
factor, parity correction, or quantifier error would be easy to introduce.

Run the full audit from the repository root with

```bash
python3 Erdos126StressTest.py
```

The smaller CI-style run is `python3 Erdos126StressTest.py --quick`.  The
script uses only the Python standard library and a fixed seed
`12620260902`.

## What was tested

### 1. Normalization

For positive integers $a,b$, the script independently defines

\[
g=(a,b),\qquad
q=g\begin{cases}
2,&a/g\text{ and }b/g\text{ both odd},\\
1,&\text{otherwise},
\end{cases}
\]

and

\[
U(a,b)=\frac{a+b}{q},\qquad D(a,b)=\frac{|a-b|}{q}.
\]

It checks

\[
qU=a+b,\qquad qD=|a-b|,\qquad (U,D)=1.
\]

It also checks, for $p=2,3,5,7,11$, that the valuation computed from the
normalized integer agrees with subtracting

\[
\min(v_p(a),v_p(b))+
  1_{p=2}1_{v_2(a)=v_2(b)}
\]

from the valuation of the raw sum or difference.

The exhaustive range was $1\le a,b\le350$: 122,500 pairs and 612,500
valuation comparisons.  All passed.

### 2. One involution working at every $p$-adic threshold

For each finite set $T$ and prime $p$, all edge weights

\[
u_{ij}=v_p(U(a_i,a_j)),\qquad d_{ij}=v_p(D(a_i,a_j))
\]

were computed.  A maximum-base-4 involution was found by an exact dynamic
program over all partial matchings.  For every positive level $t$ occurring
among the $u_{ij}$, the script checked the ordered-pair inequality

\[
\#\{(i,j):i\ne j, u_{ij}\ge t\}
\le
\#\{(i,j):i\ne j, d_{ij}\ge t\}
+\#\{i:\tau(i)\ne i, u_{i,\tau(i)}\ge t\}.
\]

It separately checked the summed inequality

\[
\sum_{i\ne j}u_{ij}\le
\sum_{i\ne j}d_{ij}+
\sum_{\tau(i)\ne i}u_{i,\tau(i)}.
\]

The search covered all 1,804 subsets of $\{1,\ldots,11\}$ having cardinality
2 through 7, at each of $p=2,3,5,7$, plus 450 random sets of cardinality up
to 13 and height below $10^{12}$, using all primes through 31.  In total:

- 7,666 set-prime instances;
- 9,797 positive threshold levels;
- no threshold or weighted failure.

Some instances attained equality, so the test also exercised the boundary of
the inequality rather than only cases with large slack.

### 3. Heavy-prime biased expectation

For the same maximum-score involution, let

\[
U_p=\sum_{i\ne j}u_{ij},\qquad
D_p=\sum_{i\ne j}d_{ij},\qquad
M_p=\sum_{\tau(i)\ne i}u_{i,\tau(i)}.
\]

The exact same-side, opposite-side, and matching-edge retention probabilities
give

\[
\mathbb E[\text{selected slack}]
=\frac{5D_p+3M_p-3U_p}{16}.
\]

The script checked both this formula and

\[
\mathbb E[\text{selected slack}]\ge \frac18D_p
\]

in all 7,666 set-prime instances above.  For 42 representative instances of
every cardinality 2 through 7, it did not merely use the marginal formula: it
enumerated all $2\cdot4^{|T|}$ points of the full finite probability space,
289,344 sample points in total.  The direct average agreed exactly, as a
rational number, with the displayed formula.

No counterexample was found.  More significantly, the $1/8$ lower bound is
**sharp for this local expectation deduction**.  For

\[
T=\{1,2,4\},\qquad p=3,
\]

the selected maximum-score involution has

\[
(U_p,D_p,M_p)=(4,2,2).
\]

Thus $D_p+M_p-U_p=0$, and

\[
\mathbb E[\text{selected slack}]
=\frac{5\cdot2+3\cdot2-3\cdot4}{16}
=\frac14=\frac18D_p.
\]

Consequently no constant larger than $1/8$ follows solely from the three
retention probabilities $5/16,3/16,3/16$ and the matching inequality
$U_p\le D_p+M_p$.

### 4. Metric permutation constant

For

\[
w_{ij}=\begin{cases}
0,&i=j,\\
\log U(a_i,a_j),&i\ne j,
\end{cases}
\]

and every tested permutation $\sigma$, the script checked the Lean theorem's
dimensionless form

\[
R:=\frac{N\sum_iw_{i,\sigma(i)}}{\sum_{i,j}w_{ij}}\le6.
\]

It also checked the underlying reduced-product triangle inequality exactly in
integer arithmetic for every ordered triple.

All permutations were enumerated for all subsets of
$\{1,\ldots,10\}$ of cardinality 2 through 7.  Another 250 random sets of
cardinality up to 14 and height below $10^{12}$ were tested against 100
random permutations each.  Totals:

- 1,207 sets;
- 817,090 permutations;
- 369,528 ordered triangle checks.

The largest observed ratio was $R=2$, attained already by a two-point set
and its transposition.  Among four-point sets the search came very close:

\[
T=\{3,5,6,10\},\quad
\sigma=(1\ 4)(2\ 3),\quad
R\approx1.9985968168.
\]

Thus the proved constant 6 has substantial empirical room.  The data are
compatible with a possible constant 2 for this special normalized-sum metric,
but the audit does not prove such an improvement.

## Reproducibility summary

The full run reported:

| Check | Count | Result |
|---|---:|---|
| Normalization pairs | 122,500 | PASS |
| Normalization valuation comparisons | 612,500 | PASS |
| Set-prime matching instances | 7,666 | PASS |
| Positive $p$-adic threshold levels | 9,797 | PASS |
| Heavy-expectation instances | 7,666 | PASS |
| Explicit full-system sample points | 289,344 | PASS |
| Metric permutations | 817,090 | PASS |
| Exact metric triangle checks | 369,528 | PASS |

The script aborts at the first failure and prints the complete set, prime,
involution or permutation, threshold, and both sides of the failed inequality.
This makes any future regression directly reproducible.
