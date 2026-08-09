## Recommendation: (D), but first as a finite weighted-jet theorem

By the stated tide criteria, the best next programme is **(D): inductive recovery of the coefficients of a one-dimensional degenerate potential**.

The right initial scope is not an unrestricted analytic potential. Prove a theorem for a fixed finite jet
\[
L(x)=a x^{2k}+\sum_{r=1}^{R} c_r x^{2k+r}
\]
under an explicit global integrability/coercivity hypothesis, or with the higher-order terms localized by a cutoff. Then package the result for arbitrary finite \(R\).

### Why (D) wins

- **Small infrastructure delta:** generalized-Gaussian moments and single-perturbation expansions already exist. The main new component is a weighted, multiparameter expansion and quotient recurrence.
- **Closed result at every tide:** moments, weighted coefficients, normalized coefficients, the triangular lemma, one recovery rung, then finite induction.
- **Substantive outward progress:** it turns the Section 7.4 examples into a genuine recovery theorem rather than adding one more isolated coefficient.
- **Reusable structure:** the weighted-series and triangular-normalization machinery should inform a later proof of (B).

### Ranking of the alternatives

1. **(D)** — best balance of novelty, existing machinery, and tide-sized closure.
2. **(A)** — safest fallback. It is highly predictable but mostly repeats the \(\gamma\)-rung with larger cumulant algebra.
3. **(C)** — strategically valuable, especially because it serves two papers, but not the smallest infrastructure delta. Multivariate change of variables, Gaussian normalization/moments, matrix positivity, and tail transfer can easily become a foundations programme.
4. **(B)** — defer. It risks combining all-order asymptotics, global domination, normalized-series algebra, and jet induction in one scope. The work from (D) should substantially de-risk it.

A short exploratory spike on Mathlib’s multivariate Gaussian API is still worthwhile, but I would not make (C) the next committed multi-tide programme.

---

## Proposed stages

Write
\[
q=t^{-1/(2k)},\qquad
\mu_{a,k}(du)=Z_{a,k}^{-1}e^{-a u^{2k}}\,du.
\]
After \(x=qu\),
\[
tL(qu)=a u^{2k}+\sum_{r=1}^{R}c_r q^r u^{2k+r}.
\]

The coefficient \(c_r\) is therefore expected to first appear at weighted order \(q^r\).

### Tide 1: Reference generalized-Gaussian moment API

Prove a consolidated family of results for \(\mu_{a,k}\):

\[
Z_{a,k}
 =\int_{\mathbb R}e^{-a u^{2k}}\,du
 =\frac1k\,a^{-1/(2k)}
   \Gamma\!\left(\frac1{2k}\right),
\]
and
\[
M_n:=\mathbb E_{\mu_{a,k}}[u^n]
=
\begin{cases}
0,&n\text{ odd},\\[1mm]
a^{-n/(2k)}
\dfrac{\Gamma((n+1)/(2k))}
      {\Gamma(1/(2k))},&n\text{ even}.
\end{cases}
\]

Also establish integrability of polynomially weighted reference densities and
\[
\operatorname{Var}_{\mu_{a,k}}(u^j)>0
\qquad (j\ge 1).
\]

**Closed-form target:** Gamma formulas for all moments and an explicit formula for
\[
V_j=M_{2j}-M_j^2>0.
\]

---

### Tide 2: Exact scaling and observable interface

Formalize the scaled Gibbs identity for finite jets:
\[
t^{s/(2k)}\langle x^s\rangle_t
=
\frac{
 \int u^s e^{-a u^{2k}}
 \exp\!\left(-\sum_{r=1}^{R}c_r q^r u^{2k+r}\right)\,du
}{
 \int e^{-a u^{2k}}
 \exp\!\left(-\sum_{r=1}^{R}c_r q^r u^{2k+r}\right)\,du
}.
\]

If the note’s observable class is compactly supported, include the cutoff-monomial version here and isolate the tail-transfer obligation.

**Closed-form target:** an exact equality reducing every required physical moment to a normalized perturbation of \(\mu_{a,k}\).

---

### Tide 3: Weighted exponential polynomial

Define the coefficient polynomials \(P_n(u)\) by
\[
\exp\!\left(-\sum_{r=1}^{R}c_rq^r u^{2k+r}\right)
=
\sum_{n=0}^{R}q^nP_n(u)+\operatorname{Rem}_{R+1}(q,u),
\]
where
\[
P_n(u)=
\sum_{\substack{\ell_1,\ldots,\ell_n\ge0\\
                 \sum_{r=1}^n r\ell_r=n}}
\prod_{r=1}^{n}
\frac{\bigl(-c_r u^{2k+r}\bigr)^{\ell_r}}{\ell_r!}.
\]

Prove the key triangular decomposition
\[
P_n(u)=-c_nu^{2k+n}+\widetilde P_n(u;c_1,\ldots,c_{n-1}).
\]

**Closed-form target:** a finite multi-index formula and the statement that the new coefficient \(c_n\) occurs exactly once and linearly at weight \(n\).

---

### Tide 4: Integrated remainder theorem

Upgrade the formal weighted expansion to an asymptotic expansion after integration:
\[
J_s(q):=
\int u^s e^{-a u^{2k}}
 \exp\!\left(-\sum c_rq^r u^{2k+r}\right)\,du
=
\sum_{n=0}^{R}J_{s,n}q^n+o(q^R),
\]
with
\[
J_{s,n}=\int u^sP_n(u)e^{-a u^{2k}}\,du.
\]

Using Tide 1, reduce each \(J_{s,n}\) to a finite combination of Gamma moments.

**Closed-form target:** an all-observable, finite-order unnormalized expansion with explicit coefficients and a proved \(o(q^R)\) remainder.

---

### Tide 5: Normalized quotient recurrence

For
\[
F_s(q)=\frac{J_s(q)}{J_0(q)}
      =\sum_{n=0}^{R}C_{s,n}q^n+o(q^R),
\]
prove the recurrence
\[
C_{s,0}=\frac{J_{s,0}}{J_{0,0}},
\qquad
C_{s,n}
=
\frac{1}{J_{0,0}}
\left(
J_{s,n}-\sum_{h=1}^{n}J_{0,h}C_{s,n-h}
\right).
\]

Alternatively, normalize the \(J\)'s by \(Z_{a,k}\) first so the recurrence has denominator \(1\).

**Closed-form target:** a reusable normalized-series theorem in which every \(C_{s,n}\) is an explicit polynomial in \(c_1,\ldots,c_n\) and reference moments.

---

### Tide 6: Triangular covariance lemma

Combine Tides 3–5 to prove
\[
C_{s,r}
=
K_{s,r}(c_1,\ldots,c_{r-1})
-c_r\,\operatorname{Cov}_{\mu_{a,k}}
       \bigl(u^s,u^{2k+r}\bigr),
\]
where \(K_{s,r}\) is independent of \(c_r,c_{r+1},\ldots\).

Choose
\[
s=2k+r.
\]
Then
\[
C_{2k+r,r}
=
K_{2k+r,r}(c_1,\ldots,c_{r-1})
-c_r\,\operatorname{Var}_{\mu_{a,k}}(u^{2k+r}).
\]

**Closed-form target:** the exact one-new-parameter-at-one-new-order identity with a strictly nonzero coefficient.

This is the conceptual heart of the programme.

---

### Tide 7: One-rung recovery theorem

Define the observable asymptotic coefficient by the iterated limit
\[
C_{j,r}
=
\lim_{q\to0}q^{-r}
\left(
F_j(q)-\sum_{n<r}C_{j,n}q^n
\right),
\qquad j=2k+r.
\]

Assuming \(c_1,\ldots,c_{r-1}\) are known, prove
\[
c_r
=
\frac{
K_{2k+r,r}(c_1,\ldots,c_{r-1})
-C_{2k+r,r}
}{
\operatorname{Var}_{\mu_{a,k}}(u^{2k+r})
}.
\]

Give the denominator explicitly using Gamma functions.

**Closed-form target:** a turnkey theorem recovering \(c_r\) from one rescaled expectation coefficient and the previously recovered jet.

---

### Tide 8: Finite-jet induction and local-potential packaging

Induct on \(r\le R\) to recover
\[
(c_1,\ldots,c_R)
\]
from the corresponding expectation asymptotics, assuming \((k,a)\) have already been recovered by the existing leading-order theorem.

Then transfer from the globally controlled model to the desired local germ using cutoff observables and a tail-negligibility theorem.

**Closed-form target:** a sorry-free finite-order Section 7.4 recovery theorem:
equality of the relevant expectation asymptotics through weighted order \(R\) implies equality of the potential jets through degree \(2k+R\).

Only after this theorem is stable should an unrestricted analytic/all-order corollary be considered.

---

## Main scope trap

The most likely trap is **treating the weighted exponential expansion as uniformly integrable for an arbitrary finite jet**.

For example,
\[
a x^{2k}+\sum_{r=1}^{R}c_r x^{2k+r}
\]
need not define a Gibbs measure at all: the highest term may be odd, or an even highest coefficient may be negative. Even when the full potential is globally coercive, a naive Taylor remainder after scaling may not admit a \(q\)-independent integrable majorant on all of \(\mathbb R\).

Therefore the programme should choose its analytic envelope before building the combinatorics:

- localized higher-order jet terms;
- or a globally coercive remainder with a uniform lower bound;
- or a core/tail split with the tail shown negligible.

Do not silently use the bare finite polynomial as the global potential unless its coercivity is explicit.

## Numerical check before Tide 1

Use a CAS or high-precision quadrature for several small cases, for example \(k=1,2,3\), with two or three mixed coefficients. For each \(r\):

1. Numerically compute
   \[
   F_{2k+r}(q)=
   \mathbb E_q[u^{2k+r}]
   \]
   for decreasing \(q\).
2. Subtract the fitted lower-order terms.
3. Verify that the \(q^r\) coefficient changes with \(c_r\) by
   \[
   -\operatorname{Var}_{\mu_{a,k}}(u^{2k+r}),
   \]
   independently of the lower coefficients.
4. Include both odd and even \(2k+r\) to catch parity errors.
5. Check that every test potential is actually normalizable and that the tail does not dominate at the sampled \(q\).

This small experiment is especially important because using partition data alone would make odd perturbations vanish at linear order by symmetry; the choice of the matching moment observable \(u^{2k+r}\) is what converts the linear response into a strictly positive variance.