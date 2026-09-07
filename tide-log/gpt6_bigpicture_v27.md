## Recommendation

Yes: **Stage 3 should certify the full spectral-cutoff theorem for polynomial data, with the entire phase-order sum inside each spectral coefficient.** Do not truncate the Taylor series first.

Two changes to the proposed design are important:

1. Prove a **uniform weighted ℓ¹ bound for the density representation**, not just a bound on each coefficient. This also controls the number/sum of terms that enter the high-spectrum remainder.
2. For the phase-order sum, **apply Tonelli before estimating the tail**. The Stage 2 tail estimate with \(m=\lceil\nu\rceil+i+p\) is useful termwise, but its constants need not be summable in \(p\) for arbitrary polynomial data.

Below, declaration names are proposed interfaces, not claims about existing Mathlib or project declarations.

---

# 1. Precise Stage 3 target

## 1.1 Recommended initial hypotheses

For the first implementation, use:

- \(d\ge1\);
- \(k:\operatorname{Fin}d\to\mathbb N\), with every \(k_i>0\);
- \(h:\operatorname{Fin}d\to\mathbb N\);
- \(\beta>0\);
- \(\xi,\eta\) real polynomials in \(d\) variables;
- \(N>0\).

Write
\[
u^k=\prod_i u_i^{k_i},\qquad
u^{2k}=(u^k)^2,\qquad
u^h=\prod_i u_i^{h_i},
\]
and define
\[
Z(N)=\int_{(0,1]^d}
 \eta(u)u^h
 e^{-\beta N u^{2k}+\beta\sqrt N\,u^k\xi(u)}\,du.
\]

The restriction \(h_i\in\mathbb N\) is useful, not cosmetic: it makes the proposed lattice and the coefficient constant depending only on \(d,k\) valid.

For arbitrary real \(h_i>-1\), a version remains possible, but the common rational-lattice claim need not hold and the spacing constant generally depends on \(h\).

Set
\[
a=\xi(0),\qquad J=\xi-a,\qquad P_p=\eta J^p,
\qquad b_{p,\gamma}=[u^\gamma]P_p.
\]

For a monomial \(\gamma\), the Stage 1 weights are
\[
w_i(\gamma)=\frac{h_i+\gamma_i+1}{2k_i}-1.
\]
Let \(c_\gamma(\mu,q)\) denote the **aggregated** density coefficient, obtained using `coeffAt`, not the coefficient of an arbitrarily chosen list entry.

Finally,
\[
K_k=\prod_i\frac1{2k_i}.
\]

## 1.2 Spectral support

A convenient admissible support is
\[
\Lambda_{h,k}
=
\bigcup_{i<d}
\left\{\frac{h_i+r+1}{2k_i}:r\in\mathbb N\right\}.
\]

Every density exponent belongs to this set. If
\[
Q=2\prod_i k_i,
\]
then \(\Lambda_{h,k}\subseteq Q^{-1}\mathbb N_{>0}\). The lcm choice is sharper, but the product choice is likely easier initially.

A more data-sensitive support is
\[
\Lambda^*
=
\left\{
\frac{h_i+\gamma_i+1}{2k_i}:
\exists p,\ b_{p,\gamma}\ne0,\ i<d
\right\}.
\]
Either support works. The theorem should allow zero coefficients at admissible exponents.

**Implementation recommendation:** index spectral exponents by positive natural lattice indices, with
\[
\mu_r=(r+1)/Q.
\]
This makes every cutoff sum an ordinary finite sum with a finite bound/filter. Prove membership in \(\Lambda_{h,k}\) separately. It avoids developing a general locally finite subset of `ℝ` just to state this theorem.

## 1.3 Coefficient formula

For \(0\le j<d\), define
\[
\boxed{
A_{\mu,j}
=
K_k
\sum_{p=0}^{\infty}\frac{\beta^p}{p!}
\sum_{\gamma\in\operatorname{supp}P_p}
 b_{p,\gamma}
 \sum_{q=j}^{d-1}
 c_\gamma(\mu,q)\binom qj\,
 \operatorname{fluctMoment}_{\beta,a,p}(\mu,q-j).
}
\]

The indexing follows directly from Stage 2: the power \((\log N)^j\) comes from \(i=q-j\).

There is **no additional \(p/2\) in the spectral exponent**: that factor is already incorporated in `phaseKernel β a p`.

The main theorem is
\[
\boxed{
Z(N)
-
\sum_{\substack{\mu\in\Lambda_{h,k}\\\mu<L}}
N^{-\mu}\sum_{j=0}^{d-1}A_{\mu,j}(\log N)^j
=
O\!\left(N^{-L}(1+\log N)^{d-1}\right)
}
\]
as \(N\to+\infty\), for every \(L>0\).

Using \(1+\log N\) gives a convenient estimate for all \(N\ge1\). The paper can replace it by \((\log N)^{d-1}\) in the asymptotic statement.

### Three public deliverables

I would expose:

1. **Coefficient absolute summability**, preferably at the expanded finite-sum level:
   \[
   \sum_p\frac{\beta^p}{p!}
   \sum_\gamma |b_{p,\gamma}|
   \sum_{q=j}^{d-1}
   |c_\gamma(\mu,q)|\binom qj
   \left|\operatorname{fluctMoment}(\mu,q-j,p)\right|
   <\infty.
   \]

2. **A quantitative cutoff bound:** an existential constant \(C\), independent of \(N\), such that the displayed error bound holds for every \(N\ge1\).

3. **The `IsBigO` corollary** at `atTop`.

Define coefficients using `tsum`; prove `Summable` before using the definition substantively. Expose a `HasSum` lemma as a convenience for integral interchanges, rather than making `HasSum` the representation of a coefficient.

---

# 2. Uniform density bounds: use a weighted budget

Your proposed bound is plausible, and there is a particularly clean invariant behind it.

Assume all exponents belong to \(Q^{-1}\mathbb Z\), with \(Q\ge1\). Distinct exponents then satisfy
\[
|\alpha|\ge Q^{-1}.
\]

For an \(r\)-coordinate density representation \(v\), define
\[
\mathcal B_Q(v)
=
\sum_{(\mu,j,c)\in v}|c|\,j!\,Q^j.
\]

The recommended theorem is
\[
\boxed{
\mathcal B_Q(v_r)\le r!\,Q^{r-1}
\qquad(r\ge1).
}
\]

This implies both
\[
\sum_{(\mu,j,c)\in v_d}|c|\le d!Q^{d-1}
\]
and
\[
|c_\gamma(\mu,j)|
\le \frac{d!Q^{d-1-j}}{j!}.
\]

In particular, \(d!Q^d\) is a safe looser bound.

## Why the induction works

The one-coordinate representation has one coefficient \(1\), degree \(0\), so its budget is \(1\).

Suppose an existing term has degree \(j\le r-1\).

### Resonant step

The new term has coefficient \(c/(j+1)\) and degree \(j+1\). Its weighted contribution is
\[
\frac{|c|}{j+1}(j+1)!Q^{j+1}
=
Q\,|c|j!Q^j.
\]

### Nonresonant step

The usual convolution formula produces degrees \(i=0,\ldots,j\), with coefficient magnitudes
\[
|c|\frac{j!}{i!}|\alpha|^{-(j-i+1)},
\]
and one endpoint term of degree \(0\), with magnitude
\[
|c|j!|\alpha|^{-(j+1)}.
\]

Each output term contributes at most
\[
Q\,|c|j!Q^j
\]
to the weighted budget. There are \(j+2\le r+1\) outputs. Thus
\[
\mathcal B_Q(v_{r+1})
\le(r+1)Q\,\mathcal B_Q(v_r).
\]

This gives the claimed factorial bound.

### Formal consequences

Prove, in this order:

- a budget bound for one convolution of one basis term;
- a budget bound for one convolution of a representation;
- the induction for `stateDensityRep`;
- unweighted list ℓ¹ control;
- aggregated `coeffAt` control.

This avoids any need to canonicalize the representation. Repeated entries and cancellation are harmless.

**Gate:** first check that the actual `gRep` output has exactly the basis coefficients used above, possibly with zero entries. If its syntactic decomposition differs, prove the local budget estimate against that implementation; do not force a representation refactor.

---

# 3. The high-spectrum remainder

Yes: the \(\tau\)-side is the recommended route.

A crucial correction is that the signed moments from expanding the logarithm are not themselves the quantities to estimate. Introduce **absolute moments** or a single positive log-weighted integral.

For \(b\ge0\), define
\[
M_{\nu,r}(b)
=
\int_0^\infty
t^{\nu-1}(1+|\log t|)^r
e^{-\beta t+\beta b\sqrt t}\,dt.
\]
For \(\nu>0\), this is finite.

For \(N\ge1\), \(\mu\ge L>0\), and \(q\le d-1\),
\[
\begin{aligned}
&\int_0^1
\tau^{\mu-1}(-\log\tau)^q
(\sqrt{N\tau})^p
e^{-\beta N\tau+\beta a\sqrt{N\tau}}\,d\tau\\
&\quad\le
N^{-L}(1+\log N)^q
\int_0^\infty
t^{L-1}(1+|\log t|)^q
(\sqrt t)^p
e^{-\beta t+\beta|a|\sqrt t}\,dt.
\end{aligned}
\]

The proof is exactly:

1. \(\tau^{\mu-1}\le\tau^{L-1}\) on \(0<\tau\le1\);
2. substitute \(t=N\tau\);
3. use
   \[
   |\log N-\log t|
   \le(1+\log N)(1+|\log t|);
   \]
4. enlarge \((0,N]\) to \((0,\infty)\).

Suppose
\[
\|P_p\|_1\le A B^p.
\]
Summing over \(p,\gamma\) and the high-spectrum density entries gives
\[
\boxed{
|R_{\mathrm{high}}(N)|
\le
K_k A\,d!Q^{d-1}
M_{L,d-1}(|a|+B)\,
N^{-L}(1+\log N)^{d-1}.
}
\]

This is the main Stage 3 estimate. It controls all high exponents without ever estimating moments at a large \(\mu\).

## Low-spectrum tail replacement

There is a second remainder:
\[
R_{\mathrm{low\,tail}}
=
\text{low-spectrum truncated moments}
-
\text{low-spectrum full moments}.
\]

Here the low spectral set is finite. Sum over phase orders under the absolute integral first, obtaining the kernel
\[
e^{-\beta t+\beta(|a|+B)\sqrt t}.
\]
Then estimate its tail. For example,
\[
-\beta t+\beta b\sqrt t
\le-\beta t/2+\beta b^2/2,
\]
and the finitely many power/log factors can be absorbed into further exponential decay. A bound of the form
\[
|R_{\mathrm{low\,tail}}(N)|\le C_L e^{-\beta N/8}
\]
is ample.

**Do not sum the existing factorial-in-\(p\) tail constants.** Prove a summed-majorant tail lemma instead.

---

# 4. Phase expansion and integration

## Polynomial coefficient infrastructure

Use the existing polynomial representation if one is already established. Otherwise `MvPolynomial (Fin d) ℝ` is a natural public type, with coefficient extraction to the finite monomial representation used downstream.

Define
\[
\|P\|_1=\sum_{\gamma\in\operatorname{supp}P}|[u^\gamma]P|.
\]
Prove:
\[
\|PQ\|_1\le\|P\|_1\|Q\|_1,\qquad
\|P^p\|_1\le\|P\|_1^p,
\]
and on the unit box,
\[
|P(u)|\le\|P\|_1.
\]

Then take
\[
A=\|\eta\|_1,\qquad B=\|J\|_1.
\]
No separate \(B=0\) case should be needed; keep the natural \(B^0=1\) convention.

## Integration strategy

For fixed \(N\), define the phase-order integrand
\[
F_p(u)=
u^h P_p(u)\frac{\beta^p}{p!}
(\sqrt N\,u^k)^p
e^{-\beta N u^{2k}+\beta a\sqrt N\,u^k}.
\]

The most reusable interface is:

- every \(F_p\) is integrable;
- \(\sum_p\int |F_p|<\infty\);
- pointwise on the box, \(\sum_pF_p\) equals the original integrand.

Then invoke the applicable Bochner integral/sum interchange theorem and conclude
\[
Z(N)=\sum_p\int F_p.
\]

This “summable integral norms” interface is preferable to making dominated convergence of partial sums the central abstraction. The latter is a valid fallback, but it introduces partial-sum bounds that the rest of Stage 3 does not need.

Check the exact `integral_tsum` signature in the pinned Mathlib version before committing the wrapper. In particular, **pointwise summability alone is not enough**.

## Tonelli wrapper

Build one project-level nonnegative series-integral lemma, using `lintegral_tsum`, that yields
\[
\begin{aligned}
&\sum_p\frac{(\beta B)^p}{p!}
\int_0^\infty
t^{\nu-1}(1+|\log t|)^r(\sqrt t)^p
e^{-\beta t+\beta b\sqrt t}\,dt\\
&\qquad =
M_{\nu,r}(b+B).
\end{aligned}
\]

Prove the ENNReal equality first; establish finiteness of the right side; then export real `Summable` and equality statements.

Use the same wrapper with domain:

- \((0,\infty)\);
- \((N,\infty)\);
- optionally \((0,N]\).

This one abstraction supplies coefficient summability, high-spectrum control, and low-tail control.

---

# 5. Suggested unit sequence and gates

A realistic estimate is **9–12 review-sized units**, depending on available polynomial and integral infrastructure.

| Proposed unit | Deliverable | Estimate |
|---|---|---:|
| u230 | Integer spectral indexing, positivity, spacing, finite cutoff set | 1 |
| u231 | Weighted budget for one basis convolution | 1–2 |
| u232 | Uniform representation ℓ¹ and `coeffAt` bounds | 1 |
| u233 | Polynomial coefficient ℓ¹ algebra and box evaluation bound | 1 |
| u234 | Positive log moments; integrability; Tonelli phase-majorant wrappers | 1–2 |
| u235 | Integrated phase Taylor identity; finite monomial expansion | 1 |
| u236 | Single-basis and summed high-spectrum estimates | 1 |
| u237 | Coefficient definition, absolute summability, regrouping | 1 |
| u238 | Summed low-spectrum tail; quantitative cutoff theorem | 1–2 |
| u239 | `IsBigO` corollary and paper-facing specialization | 1 |

The spectral/budget branch and the polynomial/Tonelli branch can proceed largely independently.

## Go/no-go gates

**Gate A — after u232:**  
A uniform **list ℓ¹** bound is proved with no \(\gamma\)-dependence. A bound only on `coeffAt` is not yet enough unless the number of possible \((\mu,j)\) per monomial is separately bounded.

**Gate B — after u234:**  
The majorant moment is finite for arbitrary finite \(B\), with **no smallness assumption** on \(\|J\|_1\).

**Gate C — after u236:**  
The high-spectrum bound has constants independent of \(\gamma\), and its \(p\)-dependence is controlled by the Tonelli majorant.

**Gate D — before final assembly:**  
The coefficient \(A_{\mu,j}\) is defined independently of \(L\), and expanded absolute summability is available. Regrouping should then be routine rather than a new analytic argument.

## What belongs to Stage 4

Stage 4 replaces finite polynomial supports by infinite coefficient families. It must supply:

- a coefficient space with a submultiplicative weighted ℓ¹ norm;
- convergence/evaluation on the integration box;
- compatibility of coefficient multiplication with function multiplication;
- absolute summability over monomials as well as phase orders;
- justification that the represented functions are the intended analytic functions.

“Analytic near the origin” alone is not a substitute for a coefficient majorant valid on the integration region. If only local analyticity is assumed, localization and control of the complementary region are additional work.

None of that is necessary for the polynomial Stage 3 theorem.

---

# 6. Paper-facing statement

Stage 3 alone can certify the following polynomial version of `thm:TaylorTree` / `cor:standardintegralexp`:

> **Polynomial Taylor-tree asymptotics.**  
> Let \(d\ge1\), \(k_i\) be positive integers, \(h_i\) nonnegative integers, \(\beta>0\), and \(\xi,\eta\) real polynomials. There is a locally finite set
> \[
> \Lambda^*\subseteq
> \bigcup_i\{(h_i+r+1)/(2k_i):r\in\mathbb N\}
> \]
> and a family of polynomials \(P_\mu\), each of degree at most \(d-1\), such that for every \(L>0\),
> \[
> Z(N)=
> \sum_{\substack{\mu\in\Lambda^*\\\mu<L}}
> N^{-\mu}P_\mu(\log N)
> +
> O\!\left(N^{-L}(\log N)^{d-1}\right).
> \]
> Every coefficient of every \(P_\mu\) is given by an absolutely convergent series over phase orders and polynomial monomials, with terms expressed through the fluctuation moments. The family \(P_\mu\) is independent of the cutoff \(L\).

Call this an **asymptotic family** or **spectrally truncated asymptotic expansion**. Absolute convergence of each coefficient series does **not** assert convergence of the full sum over spectral exponents.

The decisive formal architecture is therefore:

\[
\boxed{
\text{uniform density budget}
+\text{coefficient }\ell^1\text{ algebra}
+\text{Tonelli majorant}
\ \Longrightarrow\
\text{spectral cutoff theorem}.
}
\]

That architecture handles polynomial data of arbitrary size and leaves a clean coefficient-space extension point for Stage 4.
