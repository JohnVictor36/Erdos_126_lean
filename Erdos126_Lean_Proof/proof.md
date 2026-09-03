---
title: "A Square-Root Lower Bound for Prime Divisors of Pairwise Sums"
subtitle: "A gcd-normalized p-adic matching argument"
date: "Working draft — September 2026"
---

**Status.** Self-contained working draft with a Lean formalization. No claim
of priority is made; external refereeing is still needed.

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

# 4. The valuation metric and matching costs

The next lemma prevents the matching edges from carrying an excessive fraction of the normalized numerator.

For $i<j$, define

$$
\rho_{ij}
=\log\frac{a_i a_j}{g_{ij}^2}
=\sum_q|v_q(a_i)-v_q(a_j)|\log q,
$$

where the sum is over all primes. Thus $\rho$ is the $\ell^1$ distance between the prime-valuation vectors of the $a_i$.

**Lemma 3 (metric matching bound).** If $T$ has $N\ge2$ vertices and $M$ is any matching on $T$, then

$$
\sum_{\{i,j\}\in M}\log U_{ij}
\le\frac{6}{N}\mathcal A(T).
$$

**Proof.** Put $w_{ij}=\log U_{ij}$ off the diagonal and $w_{ii}=0$. If $g=g_{ij}$, $x=a_i/g$, and $y=a_j/g$, then $\rho_{ij}=\log(xy)$. According as $x,y$ have different parity or are both odd, $U_{ij}=x+y$ or $(x+y)/2$. Hence

$$
\rho_{ij}\le2w_{ij},
\qquad
w_{ij}\le\rho_{ij}+\log2.
$$

Extend $M$ to an involution $\sigma$ by fixing the unmatched vertices. Summing the triangle inequality through every intermediate vertex gives

$$
N\sum_i\rho_{i,\sigma(i)}
\le2\sum_{i,j}\rho_{ij}
\le4\sum_{i,j}w_{ij}.
$$

Also $U_{ij}\ge2$ for $i\ne j$, so

$$
N^2\log2\le2\sum_{i,j}w_{ij}.
$$

Combining the last two estimates with $w_{i,\sigma(i)}\le\rho_{i,\sigma(i)}+\log2$ gives

$$
N\sum_iw_{i,\sigma(i)}\le6\sum_{i,j}w_{ij}.
$$

Both sums count unordered edges twice, proving the lemma. $\square$

# 5. Deterministic separation at one prime

Fix $p\in P(A)$. Write $a_i=p^{v_p(a_i)}u_i$ with $p\nmid u_i$. For odd $p$, partition the vertices according as the least positive residue of $u_i$ lies in

$$
H_0=\{1,\ldots,(p-1)/2\},
\qquad H_1=-H_0.
$$

For $p=2$, use instead the odd unit classes $1,3\pmod4$. Denote the two vertex sets by $V_0,V_1$.

Unequal exact $p$-adic valuation strata contribute zero to both normalized valuations. Within an equal stratum, positive normalized difference valuation means $u_i\equiv u_j$, while positive normalized sum valuation means $u_i\equiv-u_j$. Consequently,

$$
\mathcal B_p(V)=\mathcal B_p(V_0)+\mathcal B_p(V_1),
\tag{5.1}
$$

and every normalized $p$-adic numerator valuation inside either $V_\nu$ is zero. The statement includes all powers $p^t$ simultaneously; only the leading unit class is needed to choose the side. The extra factor $2$ in $h_{ij}$ is exactly what makes the same assertion true modulo $4$ for $p=2$.

For each $q\in P(A)$ and each $\nu\in\{0,1\}$, apply Lemma 2 on $V_\nu$, obtaining a matching $M_{q,\nu}$. Since

$$
\mathcal A(V_\nu)-\mathcal B_P(V_\nu)\ge0
$$

and every matching slack is nonnegative, while the $p$-numerator mass inside $V_\nu$ vanishes, the exact identity implies

$$
\mathcal B_p(V_\nu)
\le\sum_{q\in P}\sum_{e\in M_{q,\nu}}\log U_e.
\tag{5.2}
$$

For fixed $q$, the union

$$
M_q=M_{q,0}\cup M_{q,1}
$$

is a matching on the original $k$ vertices. Add (5.2) for the two sides, use (5.1), and apply Lemma 3 directly to $M_q$ on the original set. This gives

$$
\boxed{
\mathcal B_p(V)\le\frac{6r}{k}\mathcal A(V)
}
\qquad(p\in P(A)).
\tag{5.3}
$$

It is important that $M_q$ need not be the normalized matching supplied by Lemma 2 on all of $V$. We use the matching identities only on the two sides, where their slacks are nonnegative; the union is used solely in the metric upper bound.

# 6. Proof of Theorem 1

Apply Lemma 2 directly on $V$ for every $q\in P$. Its exact identity, nonnegative slacks, and Lemma 3 yield

$$
\mathcal A(V)-\mathcal B_P(V)
\le\frac{6r}{k}\mathcal A(V).
\tag{6.1}
$$

Summing (5.3) over $p\in P$ gives

$$
\mathcal B_P(V)
\le\frac{6r^2}{k}\mathcal A(V).
\tag{6.2}
$$

Adding (6.1) and (6.2),

$$
\mathcal A(V)
\le\frac{6r(r+1)}{k}\mathcal A(V).
$$

Since $\mathcal A(V)>0$ for $k\ge2$, cancellation gives

$$
\boxed{k\le6r(r+1)\le12r^2}.
$$

In particular,

$$
r(A)\ge\sqrt{k/12}.
$$

# 7. What makes the proof work

The pairwise gcd normalization removes self-paired residue chains.  The two
$p$-unit sides then place all normalized $p$-difference mass inside the sides
and all normalized $p$-sum mass across them.  The side matchings are used only
where their slack is nonnegative; after that they may be joined and charged to
the metric energy of the full $k$-vertex set.  Thus the proof is deterministic,
height-free, and loses no factor from a small side.

For finsets of natural numbers, erasing a possible zero and applying the same
argument gives $k\le13r^2$ when $k>2$.  The accompanying Lean modules formalize
this version and its transfer to the official asymptotic statement.

# References

1. Formal Conjectures, *Erdos Problem 126*, official Lean statement,
   <https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/126.lean>.
