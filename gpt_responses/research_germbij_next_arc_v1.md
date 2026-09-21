**My ranking is A → C → B.** I would make **ambient curved Morse–Bott recovery** the main next arc, take the singular power normal form as a short companion, and defer quantitative recovery until its regularity assumptions and observation model are explicit. I would fold D into the other arcs rather than develop it separately.

The reason for choosing A is structural: it removes the most conspicuous coordinate dependence from the note’s main claim. But there is an important distinction between **transporting the asymptotics to a graph** and **proving identification using only the original ambient monomial family**. The latter is the substantive unfinished step.

## 1. A — Curved Morse–Bott in ambient coordinates

### First theorem: graph-supported limit and covariance-measure limit

Write ambient coordinates as \((x,y)\in\mathbb R^r\times\mathbb R^p\), and put
\[
z=x-\phi(y),\qquad \iota(y)=(\phi(y),y).
\]

A clean first statement uses a cutoff adapted to the graph:
\[
dP_t(x,y)=Z_t^{-1}\chi(y)\eta(z)e^{-tL(x,y)}\,dx\,dy,
\]
where:

- \(\chi\ge 0\) is continuous, compactly supported, and not identically zero;
- \(\eta\ge0\) is compactly supported in a sufficiently small transverse window and equals \(1\) near \(0\);
- \(H(y)\) is continuous and uniformly positive definite on the tangential support;
- on that window,
  \[
  L(\phi(y)+z,y)=\tfrac12z^\top H(y)z+R(z,y),
  \qquad |R(z,y)|\le C|z|^3.
  \]

Define
\[
A=(2\pi)^{r/2}\int\chi(y)\det H(y)^{-1/2}\,dy,
\qquad
d\mu(y)=
\frac{\chi(y)\det H(y)^{-1/2}\,dy}
{\int\chi\det H^{-1/2}}.
\]

Then prove, in one theorem package,
\[
t^{r/2}Z_t\longrightarrow A,
\]
\[
E_t[F(x,y)]\longrightarrow
\int F(\phi(y),y)\,d\mu(y),
\]
and
\[
tE_t[z_i z_jg(y)]
\longrightarrow
\int g(y)(H(y)^{-1})_{ij}\,d\mu(y).
\]

Here continuous tests on the relevant compact sets suffice.

**Why this is a good Lean target:** the map
\[
(z,y)\mapsto(z+\phi(y),y)
\]
is a fibrewise translation. You can transport integration using Fubini and translation invariance, rather than first building a general manifold change-of-variables theorem. The first result needs remarkably little differential geometry.

### What it identifies

The leading ambient monomial limits determine
\[
\bar\mu=\iota_\#\mu.
\]
Its support determines the graph over \(\operatorname{supp}\chi\), under the stated positivity and continuity assumptions.

The scaled centred moments determine the matrix-valued measure
\[
d\nu=H^{-1}\,d\mu.
\]
Equality of \(\mu\) and \(\nu\), together with continuity, identifies \(H\) on the visible support.

Two clarifications belong in the theorem’s interpretation:

1. **This \(H\) is the transverse Hessian in the graph coordinates**, not automatically the matrix of the Euclidean normal Hessian.
2. For a smooth graph, the invariant expression is
   \[
   \det(H_{\mathrm{normal}})^{-1/2}\,d\operatorname{vol}_W
   =
   \det(H)^{-1/2}\,dy.
   \]
   Thus the apparent absence of a graph-area factor is correct: it is compensated by the change in the normal Hessian.

### Main technical risk: the original observable family

The centred observable
\[
(x_i-\phi_i(y))(x_j-\phi_j(y))g(y)
\]
is generally **not an ambient polynomial**. Consequently, the graph theorem above does not by itself close the original fixed-monomial identification claim.

Ordinary Stone–Weierstrass approximation does not directly fix this: the factor \(t\) magnifies approximation error.

I would make the next milestone explicit:

> **Ambient-polynomial bridge:** under sufficient smoothness for a first-order Laplace expansion, equality of the ambient polynomial expansion coefficients determines the principal transverse covariance measure.

A plausible route is to regard the \(t^{-1}\) coefficient as a distribution supported on \(W\). Its principal transverse second-order part encodes \(H^{-1}\mu\). Polynomial density in a suitable \(C^k\) topology can then replace mere uniform density. This requires stronger smoothness and more expansion machinery than the current cubic-bound leading-order theorem.

**Recommendation:** land the graph transport theorem first, but reserve the headline “ambient monomials recover curved Morse–Bott geometry” for this bridge.

---

## 2. C — Singular non-isolated power normal forms

This is the best low-risk companion arc: it adds genuinely singular geometry while keeping the proof mechanism transparent.

### First theorem: exact joint recovery of singular order and coefficient

Let
\[
L(x,y)=a(y)x^{2k},\qquad k\ge1,
\]
with \(a>0\) continuous on the compact support of \(\chi\). Integrate over the full transverse line, with weight \(\chi(y)\).

Put \(p=1/(2k)\). Then
\[
Z_t=
\frac{\Gamma(p)}{k}\,t^{-p}
\int\chi(y)a(y)^{-p}\,dy.
\]

The tangential marginal is exactly
\[
d\mu_k(y)=
\frac{\chi(y)a(y)^{-1/(2k)}\,dy}
{\int\chi a^{-1/(2k)}}.
\]

Moreover, for nonnegative integers \(q\),
\[
t^{q/k}E_t[x^{2q}g(y)]
=
\frac{\Gamma((2q+1)/(2k))}
{\Gamma(1/(2k))}
\int g(y)a(y)^{-q/k}\,d\mu_k(y).
\]

This yields three clean identification statements:

- the decay exponent of \(E_t[x^2]\) identifies \(k\);
- tangential moments identify \(\mu_k\);
- taking \(q=k\),
  \[
  tE_t[x^{2k}g(y)]
  =\frac1{2k}\int g(y)a(y)^{-1}\,d\mu_k(y),
  \]
  so the corresponding mixed moments identify \(a\) on the visible support.

Adding a transverse cutoff changes “exact” to “asymptotic,” with the same limits.

### Fold D into this theorem

The especially clean observable identity is
\[
\boxed{tE_t[L]=\frac1{2k}=\lambda.}
\]

For Morse–Bott, the analogous limit is
\[
tE_t[L]\longrightarrow r/2.
\]

This is a better “observable definition of \(\lambda\)” than a generic squared-distance exponent. For example, for
\[
L=\sum_i x_i^{2k_i},
\]
the RLCT is \(\sum_i1/(2k_i)\), whereas \(E_t[|x|^2]\) is dominated by the slowest-decaying coordinate. Its exponent alone does not generally determine the RLCT.

Also, prove the energy limit directly by moment scaling or dominated convergence. Do not infer it merely by differentiating an asymptotic equivalent for \(Z_t\).

### Main technical risk

Mostly library engineering: integrability and scaling of generalized Gaussian moments, Gamma identities, and uniform domination when passing to cutoffs or remainders.

The conceptual risk is overclaiming: this is a **singular transverse normal-form theorem**, not yet a general theorem about singular non-isolated zero sets.

---

## 3. B — Quantitative recovery via localized covariance ratios

I would avoid starting with quantitative Stone–Weierstrass. It introduces a potentially ill-conditioned polynomial inversion problem before deciding what topology of recovery is wanted.

### First theorem: deterministic local reconstruction stability

Let
\[
B(y)=H(y)^{-1},\qquad d\nu=B\,d\mu.
\]
Assume, near a target point \(y_0\),

- \(B\) is \(\alpha\)-Hölder with constant \(M\);
- \(\|B\|\le K\);
- \(\mu(B(y_0,h))\ge c h^p\).

Choose \(0\le b_{y_0,h}\le1\), equal to \(1\) on the radius-\(h\) ball and supported in the radius-\(2h\) ball. Suppose estimates satisfy
\[
|\widehat m-\mu(b)|\le\varepsilon_m,\qquad
\left\|\widehat S-\int bB\,d\mu\right\|\le\varepsilon_S.
\]

For \(\varepsilon_m\le ch^p/2\), define
\[
\widehat B(y_0)=\widehat S/\widehat m.
\]
Then
\[
\|\widehat B(y_0)-B(y_0)\|
\le
M(2h)^\alpha+
\frac{2(\varepsilon_S+K\varepsilon_m)}{ch^p}.
\]

With both errors of size \(\varepsilon\), balancing gives
\[
\|\widehat B-B\|
=O\!\left(\varepsilon^{\alpha/(\alpha+p)}\right).
\]
Uniform positive definiteness then converts this into an \(H\)-error bound.

This gives a concrete empirical target without quantitative polynomial approximation.

### Main technical risk

There are two unavoidable inputs:

- **Regularity and local mass:** finite noisy moments cannot give uniform pointwise recovery of an unrestricted continuous \(H\). Hölder control and a lower mass bound are substantive assumptions.
- **Scaled covariance control:** the relevant finite-temperature observable is \(tzz^\top b(y)\). A bounded-test estimate applied naively has a supremum growing with \(t\). To connect to item 4, use posterior moment/variance bounds, or carefully truncated rescaled tests—not just the existing bounded-test statement verbatim.

That second step is where the empirical theorem becomes more than deterministic approximation theory.

---

## What LLC and WBIC actually see

There is a clean statement here, but I would **not** say that LLC/free-energy estimators directly see the Morse–Bott density. Three distinct objects should be separated:

| Quantity | Leading Morse–Bott information |
|---|---|
| Tangential posterior expectations | Normalized measure \(\mu\) |
| Free energy \(-\log Z_t\) | \(\lambda=r/2\), and constant \(-\log A\) |
| Energy-based LLC statistic \(tE_t[L]\) | \(\lambda=r/2\) |

The free-energy constant sees the **total weighted Morse–Bott volume**, not its spatial distribution. The leading LLC statistic does not even see that total volume: in the exact quadratic normal form, it is \(r/2\), independently of \(H(y)\).

There is also a temperature convention worth correcting:

- ordinary posterior: \(t=n\), when \(L_n\) is average loss;
- standard WBIC: inverse temperature \(\beta=1/\log n\), hence effective \(t=n/\log n\).

In the exact normal form,
\[
E_{\beta}[nL_n]-nL_{n,\min}
=\lambda/\beta.
\]
The amplitude \(A\) cancels from this normalized energy expectation.

### The clean empirical theorem from 2 + 4

For bounded tangential \(g\), if \(t_n\to\infty\) and the empirical comparison gives
\[
|E_{n,t_n}[g(y)]-E_{t_n}[g(y)]|
\le e_n\|g\|_\infty,\qquad e_n\to0,
\]
then
\[
E_{n,t_n}[g(y)]\longrightarrow\int g\,d\mu.
\]

This is immediate and useful. But its hypotheses must control the **whole tangential support**, not merely transverse Hessian fluctuations.

An empirical residual restricted to \(W\) can reweight the limiting measure by
\[
e^{-t_nR_n|_W(y)}.
\]
Even a small residual can therefore destroy the population Morse–Bott density at large temperature. A sufficient condition is
\[
t_n\,\operatorname{osc}_W(R_n)\to0,
\]
alongside the required transverse controls; exact preservation of the zero manifold is another clean setting. Score correction alone does not automatically eliminate tangential reweighting.

**Bottom line:** make A the main arc, use C to establish a compact singular/RLCT extension, and present B as a localized statistical inverse problem. For the empirical reading, the strongest accurate slogan is:

> **Posterior observables recover the normalized Morse–Bott measure; free energy records its total mass; the leading LLC records the transverse scaling exponent.**