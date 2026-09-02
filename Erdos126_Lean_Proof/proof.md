---
title: "A Square-Root Lower Bound for Prime Divisors of Pairwise Sums"
subtitle: "A gcd-normalized p-adic matching argument"
date: "Working draft — September 2026"
---

**Status.** This is a self-contained working draft accompanied by a complete
Lean formalization of the stated finite and asymptotic bounds. Independent
mathematical and computational audits found no error, but no claim of priority
is made, and the result should be externally refereed before being cited as
established.

# 1. Statement of the result

Let $A=\{a_1,\ldots,a_k\}$ be a set of distinct positive integers, and put

$$
P(A)=\{p\text{ prime}:p\mid a_i+a_j\text{ for some }1\le i<j\le k\},
\qquad r(A)=|P(A)|.
$$

We prove the following unconditional estimate.

**Theorem 1.** There is an absolute constant $c>0$ such that every set $A$ of $k\ge2$ distinct positive integers satisfies

$$
r(A)\ge c\sqrt{k}.
$$

Equivalently,

$$
\omega\!\left(\prod_{1\le i<j\le k}(a_i+a_j)\right)\gg\sqrt{k}.
$$

The argument does not require a bound on the sizes of the $a_i$. Its central device is to divide each pair $a_i,a_j$ by its own greatest common divisor before applying the $p$-adic matching method. This removes the self-paired $p$-adic chains that obstruct a direct Vandermonde argument.

All logarithms below are natural.

# 2. Pairwise normalization

For $i<j$, define

$$
g_{ij}=\gcd(a_i,a_j),
\qquad
\varepsilon_{ij}=\mathbf 1_{v_2(a_i)=v_2(a_j)},
\qquad
h_{ij}=2^{\varepsilon_{ij}}g_{ij},
$$

and set

$$
U_{ij}=\frac{a_i+a_j}{h_{ij}},
\qquad
D_{ij}=\frac{|a_i-a_j|}{h_{ij}}.
$$

These are positive integers. Indeed, if $v_2(a_i)=v_2(a_j)$, then after division by $g_{ij}$ the two resulting coprime integers are odd, so their sum and difference are both even.

The normalization has three immediate properties:

$$
\frac{U_{ij}}{D_{ij}}
=\frac{a_i+a_j}{|a_i-a_j|}>1,
$$

every prime divisor of $U_{ij}$ lies in $P(A)$, and $U_{ij}\ge2$. For the
last assertion, first divide $a_i,a_j$ by their gcd. If the two reduced
coprime numbers have different parity, their sum is at least $3$; if both are
odd, they are distinct and their sum divided by $2$ is at least $2$. The
extra factor $2^{\varepsilon_{ij}}$ removes the single forced
self-complementary $2$-adic layer.

For a vertex set $T\subseteq\{1,\ldots,k\}$, write

$$
\mathcal A(T)=\sum_{\{i,j\}\subset T}\log U_{ij},
\qquad
\mathcal B(T)=\sum_{\{i,j\}\subset T}\log D_{ij}.
$$

For a prime $p$, also write

$$
\mathcal B_p(T)
=\log p\sum_{\{i,j\}\subset T}v_p(D_{ij}),
\qquad
\mathcal B_P(T)=\sum_{p\in P(A)}\mathcal B_p(T).
$$

By the ratio identity above,

$$
\mathcal A(T)-\mathcal B(T)
=\sum_{\{i,j\}\subset T}\log\frac{a_i+a_j}{|a_i-a_j|}>0
$$

whenever $|T|\ge2$. Moreover, $\mathcal B(T)-\mathcal B_P(T)\ge0$.

# 3. The normalized p-adic matching lemma

We first isolate the local arithmetic statement.

**Lemma 2 (normalized matching).** Fix a prime $p$ and a set of vertices $T$. There is a matching $M_p(T)$ on $T$ such that

$$
\sigma_p(T):=
\sum_{\{i,j\}\subset T}v_p(D_{ij})
-\sum_{\{i,j\}\subset T}v_p(U_{ij})
+\sum_{\{i,j\}\in M_p(T)}v_p(U_{ij})
\ge0.
$$

More precisely, $\sigma_p(T)$ is a sum of terms $\binom{|x-y|}{2}$, one for every complementary pair of $p$-adic residue classes at every relevant level.

**Proof.** First suppose that $p$ is odd. Split $T$ into the exact valuation strata

$$
T_\alpha=\{i\in T:v_p(a_i)=\alpha\}.
$$

If $i,j$ lie in different strata, then

$$
v_p(U_{ij})=v_p(D_{ij})=0.
$$

Thus only pairs within one $T_\alpha$ matter. For $i\in T_\alpha$, write $a_i=p^\alpha u_i$ with $u_i$ a $p$-adic unit. For $t\ge1$ and a unit class $u\pmod {p^t}$, let

$$
C_{\alpha,t,u}
=\{i\in T_\alpha:u_i\equiv u\pmod {p^t}\},
\qquad
n_{\alpha,t,u}=|C_{\alpha,t,u}|.
$$

At level $t$, numerator edges with $p^t\mid U_{ij}$ join $C_{\alpha,t,u}$ to $C_{\alpha,t,-u}$, whereas denominator edges with $p^t\mid D_{ij}$ lie inside the individual classes. Negation has no fixed point among unit classes modulo an odd prime power.

There is one matching that simultaneously realizes

$$
\min(n_{\alpha,t,u},n_{\alpha,t,-u})
$$

matched numerator edges in every complementary pair at every level. To construct it, work upward from the deepest nonempty residue level. Match as much as possible in each paired child. The unmatched vertices of a paired child remain entirely on one side. At its parent, match opposing leftovers coming from different children. If the paired children have sizes $x_s,y_s$, then the number of edges obtained at the parent is

$$
\sum_s\min(x_s,y_s)
+\min\!\left(\sum_s(x_s-y_s)_+,\sum_s(y_s-x_s)_+\right)
=\min\!\left(\sum_sx_s,\sum_sy_s\right).
$$

This proves the simultaneous matching formula inductively. The roots and the
valuation strata are disjoint, so the union is a matching. Fix this
simultaneously saturating matching for the rest of the proof and call it
$M_p(T)$.

At a fixed level, a complementary pair of selected class sizes $x,y$ contributes $xy$ numerator edges, $\binom{x}{2}+\binom{y}{2}$ denominator edges, and $\min(x,y)$ matched numerator edges. Hence its contribution to the normalized slack is

$$
\binom{x}{2}+\binom{y}{2}-xy+\min(x,y)
=\binom{|x-y|}{2}.
$$

Summing this identity over all levels proves the lemma for odd $p$.

For $p=2$, pairs from unequal exact $2$-adic valuation strata again contribute zero. Inside one equal-valuation stratum, write the normalized parts as odd integers $u_i$. By the extra factor $2$ in $h_{ij}$,

$$
v_2(U_{ij})=v_2(u_i+u_j)-1,
\qquad
v_2(D_{ij})=v_2(u_i-u_j)-1.
$$

Thus the threshold $v_2(U_{ij})\ge t$ is the congruence
$u_i\equiv-u_j\pmod {2^{t+1}}$, and the analogous difference threshold is
$u_i\equiv u_j\pmod {2^{t+1}}$. The residue tree therefore begins modulo
$4$, with the complementary odd classes $1$ and $3$. At every later level,
negation has no fixed odd residue. The same construction and calculation
apply. $\square$

Multiplying the normalized matching inequality by $\log p$, define the logged slack

$$
S_p(T)=\sigma_p(T)\log p\ge0.
$$

The component formula also gives the pointwise upper bound

$$
0\le S_p(T)\le \mathcal B_p(T),
$$

because $\binom{|x-y|}{2}\le\binom x2+\binom y2$ in every residue
component. In particular, $S_p(T)\le\mathcal B_p(V)$ whenever $T\subseteq V$.

Because every $U_{ij}$ is supported on $P(A)$, Lemma 2 gives the exact identity

$$
\mathcal A(T)-\mathcal B_P(T)+\sum_{p\in P(A)}S_p(T)
=\sum_{p\in P(A)}\log p
  \sum_{\{i,j\}\in M_p(T)}v_p(U_{ij}).
$$

# 4. A biased selection for one prime

We next show that, for one chosen prime, a random subset produces a fixed positive fraction of the normalized denominator mass as slack.

**Lemma 3 (biased class selection).** Fix $p\in P(A)$. There is a random subset $T\subseteq\{1,\ldots,k\}$ such that every edge is retained with probability at least $3/16$, and

$$
\mathbb E S_p(T)\ge\frac18\mathcal B_p(\{1,\ldots,k\}).
$$

Conditional on auxiliary orientations, the vertex indicators are independent and each has inclusion probability either $1/4$ or $3/4$.

**Proof.** In each exact $v_p(a_i)$-stratum, pair the leading unit classes $u,-u\pmod p$ when $p$ is odd. When $p=2$, pair the classes $1,3\pmod4$. Orient each pair independently and uniformly. Vertices on the favored side are retained independently with probability $3/4$, and vertices on the other side with probability $1/4$.

One leading orientation controls every descendant complementary pair. Fix such a pair with original sizes $c,d$, and let $X,Y$ be its selected sizes. Average over the two orientations. Then

$$
\mathbb E\!\left[\binom X2+\binom Y2\right]
=\frac5{16}\left(\binom c2+\binom d2\right),
\qquad
\mathbb E[XY]=\frac3{16}cd.
$$

Pair arbitrarily $\min(c,d)$ original vertices across the two classes. The number of these pairs for which both endpoints are retained is at most $\min(X,Y)$ and has expectation $3\min(c,d)/16$. Hence

$$
\mathbb E\min(X,Y)\ge\frac3{16}\min(c,d).
$$

Using

$$
\binom{|X-Y|}{2}
=\binom X2+\binom Y2-XY+\min(X,Y),
$$

we obtain, after simplifying,

$$
\mathbb E\binom{|X-Y|}{2}
\ge
\frac18\left(\binom c2+\binom d2\right)
+\frac3{16}\binom{|c-d|}{2}
\ge
\frac18\left(\binom c2+\binom d2\right).
$$

Summing the preceding estimate over all residue levels and using Lemma 2 proves the claimed slack bound. Two vertices on opposite sides of the same oriented pair are jointly retained with probability $3/16$; vertices on the same side have averaged joint probability $5/16$; and vertices controlled by independent orientations have joint probability $1/4$. Thus every edge is retained with probability at least $3/16$. $\square$

We will also need $T$ to be large. Conditional on all orientations, every inclusion probability is at least $1/4$. Therefore the Chernoff bound gives

$$
\Pr(|T|<k/8)\le e^{-k/32}.
$$

Let $G=\{|T|\ge k/8\}$. Since $0\le S_p(T)\le\mathcal B_p(\{1,\ldots,k\})$, restricting the expected slack bound to $G$ loses at most $e^{-k/32}\mathcal B_p(\{1,\ldots,k\})$. Likewise, for any fixed nonnegative edge weights, the expected weight retained on $G$ is at least $3/16-e^{-k/32}$ times the total weight.

# 5. The valuation metric and matching costs

The next lemma prevents the matching edges from carrying an excessive fraction of the normalized numerator.

For $i<j$, define

$$
\rho_{ij}
=\log\frac{a_i a_j}{g_{ij}^2}
=\sum_q|v_q(a_i)-v_q(a_j)|\log q,
$$

where the sum is over all primes. Thus $\rho$ is the $\ell^1$ distance between the prime-valuation vectors of the $a_i$.

**Lemma 4 (metric matching bound).** If $T$ has $N\ge4$ vertices and $M$ is any matching on $T$, then

$$
\sum_{\{i,j\}\in M}\log U_{ij}
\le\frac{10}{N}\mathcal A(T).
$$

**Proof.** Put $x=a_i/g_{ij}$ and $y=a_j/g_{ij}$. These are coprime and $\rho_{ij}=\log(xy)$. If $v_2(a_i)\ne v_2(a_j)$, then $U_{ij}=x+y$; if the valuations are equal, then $x,y$ are odd and $U_{ij}=(x+y)/2$. The arithmetic-geometric mean inequality gives

$$
\frac12\rho_{ij}\le\log U_{ij}\le\rho_{ij}+\log2.
$$

For a matched edge $\{i,j\}$ and every third vertex $\ell$, the triangle inequality gives

$$
\rho_{ij}\le\rho_{i\ell}+\rho_{j\ell}.
$$

Sum this over all $\ell\ne i,j$ and then over the matching. Since any unordered pair occurs at most twice on the right,

$$
(N-2)\sum_{\{i,j\}\in M}\rho_{ij}
\le2\sum_{\{i,j\}\subset T}\rho_{ij}.
$$

By the lower metric comparison above,

$$
\sum_{\{i,j\}\subset T}\rho_{ij}\le2\mathcal A(T).
$$

Also $U_{ij}\ge2$, so $\mathcal A(T)\ge\binom N2\log2$. Combining these estimates with the upper metric comparison,

$$
\sum_{\{i,j\}\in M}\log U_{ij}
\le\frac{4}{N-2}\mathcal A(T)
+\frac{1}{N-1}\mathcal A(T)
\le\frac{10}{N}\mathcal A(T).
$$

This proves the lemma. $\square$

# 6. Proof of Theorem 1

Let $P=P(A)$, $r=|P|$, and let $V=\{1,\ldots,k\}$. Choose $p_*\in P$ for which $\mathcal B_p(V)$ is maximal. Then

$$
\mathcal B_{p_*}(V)\ge\frac1r\mathcal B_P(V).
$$

Generate the random subset $T$ using Lemma 3 for the prime $p_*$, and retain only the event $G=\{|T|\ge k/8\}$.

Define

$$
\mathcal L(T)=
\mathcal A(T)-\mathcal B_P(T)+\sum_{p\in P}S_p(T).
$$

For every outcome in $G$, the exact identity following Lemma 2 gives

$$
\mathcal L(T)\le
\sum_{p\in P}\sum_{e\in M_p(T)}\log U_e.
$$

Lemma 4 and $|T|\ge k/8$ then give

$$
\mathcal L(T)\le\frac{80r}{k}\mathcal A(T).
$$

We now average the left side. Decompose

$$
\mathcal A(T)-\mathcal B_P(T)
=\bigl(\mathcal A(T)-\mathcal B(T)\bigr)
+\bigl(\mathcal B(T)-\mathcal B_P(T)\bigr).
$$

Both terms on the right are sums of nonnegative edge weights, by the ratio
identity in Section 2. Choose $k$ large enough that $e^{-k/32}\le1/16$.
Lemma 3, the pointwise upper bound on $S_{p_*}$, and the Chernoff estimate then
give the explicit inequality

$$
\mathbb E\,\mathbf1_G\mathcal L(T)\ge
\frac18\bigl(\mathcal A(V)-\mathcal B(V)\bigr)
+\frac18\bigl(\mathcal B(V)-\mathcal B_P(V)\bigr)
+\frac1{16}\mathcal B_{p_*}(V).
$$

Set

$$
X=\mathcal A(V)-\mathcal B(V),
\qquad
Y=\mathcal B(V)-\mathcal B_P(V),
\qquad
Z=\mathcal B_P(V).
$$

These quantities are nonnegative and $X+Y+Z=\mathcal A(V)$. By the maximal
choice of $p_*$, the preceding lower bound is at least

$$
\frac1{16}\left(X+Y+\frac Zr\right)
\ge\frac{\mathcal A(V)}{16r}.
$$

On the other hand, $\mathcal A(T)\le\mathcal A(V)$, so the expected matching upper bound, restricted to $G$, is at most

$$
\frac{80r}{k}\mathcal A(V).
$$

Comparing the last two bounds and cancelling the positive quantity $\mathcal A(V)$ yields

$$
\frac1{16r}\le\frac{80r}{k},
$$

and therefore

$$
k\le1280r^2.
$$

This proves Theorem 1 for all sufficiently large $k$. Reducing the absolute
constant handles the remaining finite set of values of $k$. $\square$

# 7. Remarks on the mechanism

1. The direct disturbance fails in a self-paired class $0\pmod {p^t}$. Pairwise gcd normalization removes the common valuation $\min(v_p(a_i),v_p(a_j))$ from both sum and difference, leaving equal-valuation unit strata whose complementary classes are non-self.

2. The proof disturbs only one prime, namely a prime carrying at least $1/r$ of the $P$-part of the normalized denominator. The other primes require only their nonnegative matching inequalities.

3. The metric estimate globalizes the normalization: although one $U_{ij}$ may be huge, the total valuation distance of a matching is at most $O(1/k)$ of the total pairwise distance.

4. The argument is height-free; no multiplicatively short-interval reduction is used.

5. The proof is self-contained, but because the conclusion appears stronger than the bound commonly associated with this problem, independent external verification and a literature-priority check are essential before formal circulation.

# 8. Lean formalization status

The formalization is a standalone continuation of the official statement
`FormalConjectures.ErdosProblems.126`; the official source file itself is not
modified. Lean 4.33.1 now checks the complete dependency chain, including:

- the pairwise gcd and $2$-adic normalization;
- the simultaneous nested $p$-adic matching for every prime;
- the exact finite biased sample and its $1/8$, $3/16$, and good-event
  estimates;
- restriction and re-optimization of matchings after sampling;
- the ambient-prime logarithmic identity and all factorization bookkeeping;
- the concrete $6/N$ valuation-metric matching bound;
- the global expectation sandwich and the numerical cancellation
  $$
  k\le1536r^2
  $$
  for positive sets;
- removal of a possible zero, yielding
  $$
  k\le1600r^2
  $$
  for finsets of natural numbers with $k>2$;
- the transfer to the asymptotic conclusion in the official conjecture.

The imported $A+A$ proof contains no `sorry`, `admit`, `native_decide`, or
custom axiom.  Lean's `#print axioms` command reports only the standard
foundational principles `propext`, `Classical.choice`, and `Quot.sound` for
both the finite bound and the final asymptotic theorem.  A separate exploratory
$A+B$ file, not imported by this proof, remains unfinished.

Because the conclusion appears stronger than the bound usually associated
with this problem, the mathematical argument and the formalization should
still receive independent expert review before a claim of priority or
publication.

# References

1. Formal Conjectures, *Erdos Problem 126*, official Lean statement,
   <https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/126.lean>.
