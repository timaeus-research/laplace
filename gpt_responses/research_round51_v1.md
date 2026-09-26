The remaining gap is no longer another decomposition of KL. It is connecting the decompositions to three things:

1. **operational meaning**: which responses occur, and at what probability cost;
2. **differential meaning**: how the reconstructed distribution itself moves;
3. **resolution dependence**: what changes when the observer acquires more statistics.

The large-deviation interpretation is indeed a beautiful endpoint. But I would build it as **two small theorems**, not begin with a general LDP framework.

Two qualifications apply throughout:

- “Interior” should mean **relative interior in the effective affine response space**.
- I cannot certify a 400-line budget or exact Mathlib API availability without your checkout. The estimates below are realistic *marginal* targets given the infrastructure you describe, not claims about verified implementations.

## 1. Ranked shortlist

I would rank the following seven modules. The first two together give the large-deviation interpretation.

| Rank | Module | Main contribution |
|---|---|---|
| 1 | Compact-set Chernoff upper bound | Turns directional tail bounds into response-space geometry |
| 2 | Tilted-measure lower bound | Shows that the geometric cost is sharp |
| 3 | Separate quadratic expansions of \(L\) and \(R\) | Completes the local three-way response decomposition |
| 4 | \(L^1\)-valued reconstruction derivative | Makes the atlas a differentiable map of distributions |
| 5 | Conditional variational formula | Gives the invisible term an operational dual meaning |
| 6 | Coarse-graining tower | Describes how the map changes with observational resolution |
| 7 | Full-simplex mixture-path Fisher identities | Places the data bridge alongside the two already understood paths |

I would defer the **unconditional mixed Fréchet Hessian theorem** until the chart regularity needed for item 4 is exposed cleanly. Its formula is excellent; its main cost is analytic infrastructure, not the formula.

---

## 2. Exact statements and proof routes

### 1. Compact Chernoff upper bound

For this item and the next, assume \(S\) is essentially bounded and takes values in a finite-dimensional affine response space. Write
\[
\Lambda(\lambda)=\log E_\nu e^{\langle\lambda,S\rangle},
\qquad
J(m)=\sup_{\lambda\in\mathbb V}
       \{\langle\lambda,m\rangle-\Lambda(\lambda)\}.
\]
Affine offsets can instead be removed by working with \(S-m_0\).

On the atlas,
\[
J(m)=\mathcal I(m),
\qquad
\lambda(m)=-\theta(m).
\]

**Theorem.** For every compact \(F\) and every real
\[
a<\inf_{m\in F}J(m),
\]
there is an integer \(k\ge1\) such that, for every \(n\ge1\),
\[
\Pr_\nu(\widehat M_n\in F)\le k e^{-na}.
\]

Consequently,
\[
\limsup_{n\to\infty}\frac1n\log\Pr_\nu(\widehat M_n\in F)
\le-\inf_FJ,
\]
with the extended-log convention \(\log0=-\infty\).

**Proof.** For every \(m\in F\), select \(\lambda_m\) with
\[
\langle\lambda_m,m\rangle-\Lambda(\lambda_m)>a.
\]
The open halfspaces
\[
U_m=\{x:\langle\lambda_m,x\rangle-\Lambda(\lambda_m)>a\}
\]
cover \(F\). Extract a finite subcover and apply the union bound and Chernoff to each halfspace.

**Answer to your specific question:** yes, your halfspace bound suffices for compact sets **if it supplies**
\[
\Pr(\langle\lambda,\widehat M_n\rangle\ge b)
 \le e^{-n(b-\Lambda(\lambda))}
\]
for every required \(\lambda,b\). A bound only for a restricted collection of directions or thresholds needs a separate check.

For bounded \(S\), let
\[
K=\overline{\operatorname{conv}}(\operatorname{ess\,range}_\nu S).
\]
Then \(K\) is compact and \(\widehat M_n\in K\) almost surely. Apply the compact theorem to \(F\cap K\) to get the upper bound for every closed \(F\). No separate exponential-tightness theorem is needed.

**Likely marginal size:** 150–300 lines once the rate-function supremum and halfspace API are available.

**Important:** use \(J\), not an interior-only \(\mathcal I\), in the closed-set statement. Boundary points can have finite rate.

---

### 2. Open-set lower bound by a change of measure

**Theorem, local form.** Let \(m\) be an atlas response, \(G\) an open neighborhood of \(m\), and \(\varepsilon>0\). Then eventually in \(n\),
\[
\Pr_\nu(\widehat M_n\in G)
\ge \frac12e^{-n(\mathcal I(m)+\varepsilon)}.
\]

Hence
\[
\liminf_{n\to\infty}\frac1n
 \log\Pr_\nu(\widehat M_n\in G)
\ge-\inf_{m\in G\cap\Omega}\mathcal I(m),
\]
where \(\Omega\) is the atlas domain.

**Proof.** Put \(P=\Pi(m)=P_\theta\). On \(n\) samples,
\[
\frac{d\nu^{\otimes n}}{dP^{\otimes n}}
=
\exp\left(
n\langle\theta,\widehat M_n\rangle+n\Lambda(-\theta)
\right)
=
\exp\left(
-n\mathcal I(m)+n\langle\theta,\widehat M_n-m\rangle
\right).
\]
Choose a neighborhood \(U\subseteq G\) of \(m\) on which
\[
|\langle\theta,x-m\rangle|<\varepsilon.
\]
Therefore
\[
\Pr_\nu(\widehat M_n\in G)
\ge e^{-n(\mathcal I(m)+\varepsilon)}
   \Pr_P(\widehat M_n\in U).
\]
Your SLLN under \(P\) makes the final factor tend to one.

#### When does this become the full lower bound?

If your atlas covers \(\operatorname{ri}K\), then boundedness gives a particularly cheap completion.

For \(x\in K\) with \(J(x)<\infty\), let
\[
x_t=(1-t)x+tm_0,\qquad 0<t<1.
\]
Then \(x_t\in\operatorname{ri}K\), and convexity gives
\[
J(x_t)\le(1-t)J(x)+tJ(m_0)=(1-t)J(x).
\]
For an open \(G\ni x\), eventually \(x_t\in G\). Thus
\[
\inf_{G\cap\operatorname{ri}K}J=\inf_GJ.
\]
This upgrades the atlas lower bound to the full open-set lower bound.

Together with item 1, this is the bounded finite-dimensional Cramér theorem:
\[
-\inf_{G}J
\le \liminf_n n^{-1}\log\Pr(\widehat M_n\in G),
\]
\[
\limsup_n n^{-1}\log\Pr(\widehat M_n\in F)
\le-\inf_FJ.
\]

**Likely marginal size:** 250–400 lines **if finite-product change of measure is already convenient**. Otherwise, make that tensorization lemma a separate prerequisite; it can consume the budget.

This is the right “beautiful endpoint”: the atlas information is not merely a projection cost—it is the empirical rarity cost of producing that response from \(\nu\).

---

### 3. Separate quadratic expansions of \(L\) and \(R\)

Let \(\mathcal G=\sigma(S)\), \(C=E_\nu[\cdot\mid\mathcal G]\), and \(B=B_0\). For
\[
p_t=\frac{e^{tf}}{E_\nu e^{tf}},\qquad h=f-E_\nu f,
\]
put \(c_t=Cp_t\), so the lifted law has density \(c_t\) relative to \(\nu\).

**Theorem.** For bounded \(f\),
\[
\frac{L(t)}{t^2}\longrightarrow
\frac12\|h-Ch\|_2^2,
\]
\[
\frac{R(t)}{t^2}\longrightarrow
\frac12\|Ch-Bh\|_2^2.
\]

Together with your existing result,
\[
\frac{\mathcal I(M_t)}{t^2}\longrightarrow
\frac12\|Bh\|_2^2,
\]
this is exactly the nonlinear information split linearized into your three orthogonal subspaces.

**Cheapest proof.**

1. Prove the uniform expansion
   \[
   p_t=1+th+O_{L^\infty}(t^2).
   \]
2. Conditional expectation preserves the order bound on the remainder:
   \[
   c_t=1+tCh+O_{L^\infty}(t^2).
   \]
   You need not develop a general Banach-space conditional-expectation API.
3. Use the reusable density lemma
   \[
   p_t=1+tg+O_{L^\infty}(t^2),\quad E p_t=1
   \quad\Longrightarrow\quad
   \frac{\mathrm{KL}(p_t\nu\|\nu)}{t^2}
   \to\frac12\|g\|_2^2.
   \]
   Its proof is Taylor expansion of \(x\log x-x+1\) near \(1\).
4. Subtract exact identities:
   \[
   L(t)=\mathrm{KL}(\nu_t\|\nu)-\mathrm{KL}(c_t\nu\|\nu),
   \]
   \[
   R(t)=\mathrm{KL}(c_t\nu\|\nu)-\mathcal I(M_t).
   \]

This avoids separately differentiating either residual KL.

**Likely marginal size:** 250–400 lines, especially if the existing bounded-tilt estimates are reusable.

---

### 4. The reconstruction map is differentiable in \(L^1\)

Let
\[
q_m=\frac{d\Pi(m)}{d\nu},
\qquad
C_m=\operatorname{Cov}_{\Pi(m)}(S,S)|_{\mathbb V}.
\]
Assume bounded \(S\), and work on the nondegenerate relative response space. Define
\[
\ell_{m,u}(x)
=\left\langle C_m^{-1}u,S(x)-m\right\rangle.
\]

**Theorem.** The reconstruction map
\[
q:\Omega\longrightarrow L^1(\nu)
\]
is Fréchet differentiable, with
\[
Dq(m)[u]=q_m\,\ell_{m,u}.
\]

Consequently, for every bounded measurable observable \(\varphi\),
\[
D\!\left(E_{\Pi(m)}\varphi\right)[u]
=E_{\Pi(m)}[\varphi\,\ell_{m,u}]
=\left\langle C_m^{-1}u,
       \operatorname{Cov}_{\Pi(m)}(S,\varphi)\right\rangle.
\]

**Proof.**

- Prove the parameterized density map \(\theta\mapsto q_\theta\) differentiable into \(L^1\), using a locally uniform exponential remainder.
- The forward moment Jacobian is \(-C_m\).
- Obtain \(D\theta(m)=-C_m^{-1}\) from differentiability of the local inverse.
- Apply the chain rule.

A useful inexpensive way to obtain inverse differentiability is to combine the forward first-order expansion with your existing local Lipschitz inverse: the Lipschitz estimate transfers the forward \(o(\|\delta\theta\|)\) remainder to \(o(\|\delta m\|)\).

**Why this outranks the mixed Hessian:** one theorem simultaneously controls every bounded observable and the distribution itself.

**Budget qualification:** 200–350 lines after chart differentiability is exposed; the whole result may exceed 400 if that prerequisite is buried.

#### The mixed Hessian then has the expected form

Once the required second-order regularity is available, define
\[
a_\varphi=C_m^{-1}\operatorname{Cov}_{\Pi(m)}(S,\varphi),
\]
\[
r_\varphi
=\varphi-E_{\Pi(m)}\varphi
 -\langle a_\varphi,S-m\rangle.
\]
Then
\[
D^2\!\left(E_{\Pi(m)}\varphi\right)[u,z]
=E_{\Pi(m)}[r_\varphi\,\ell_{m,u}\ell_{m,z}].
\]

This is a particularly good **second theorem after item 4**, rather than the first theorem in the module.

---

### 5. Conditional variational characterization of \(L\)

Write \(d=dD/d\nu\), \(c=E_\nu[d\mid\mathcal G]\), and \(\bar D=c\nu\). Assume the relevant KL terms are finite.

**Theorem.**
\[
L=\mathrm{KL}(D\|\bar D)
=
\sup_{g\in\mathcal B_b}
\left\{
E_Dg-
E_D\log E_\nu[e^g\mid\mathcal G]
\right\}.
\]

This requires no regular conditional probability kernel. Everything can be phrased using conditional expectations.

**Interpretation:** \(L\) is the optimal conditional log-score improvement available to an observer who can see beyond \(S\).

**Proof sketch.**

For bounded \(g\), set
\[
Z_g=E_\nu[e^g\mid\mathcal G].
\]
The density \(c e^g/Z_g\) defines a probability measure. KL nonnegativity gives
\[
E_Dg-E_D\log Z_g\le L.
\]

For sharpness, let \(r=d/c\) on \(\{c>0\}\), and use
\[
g_k=\operatorname{clip}_{[-k,k]}(\log r).
\]
On the relevant set,
\[
E_\nu[r\mid\mathcal G]=1,
\qquad
E_\nu[e^{g_k}\mid\mathcal G]\le1+e^{-k}.
\]
Hence the normalizer contributes at most \(e^{-k}\), while
\[
E_Dg_k\to E_D\log r=L.
\]

The truncation argument is cheaper than constructing a conditional Gibbs variational theorem with kernels.

**Likely marginal size:** 250–400 lines if you already have KL comparison for bounded density tilts.

---

### 6. Coarse-graining tower—with the right nesting hypothesis

Here there is an important correction:

> \(\sigma(S)\subseteq\sigma(S')\) alone does **not** imply nesting of the exponential atlases.

For information monotonicity, require affine feature inclusion, for example
\[
S=TS'+b,
\]
or equivalently the relevant inclusion of affine feature spans.

Let \(P_c,P_f\) be the coarse and fine reconstructions of the same \(D\).

**Theorem: atlas refinement.**
\[
\mathcal I_f-\mathcal I_c
=\mathrm{KL}(P_f\|P_c)\ge0,
\]
\[
\mathrm{KL}(D\|P_c)
=\mathrm{KL}(D\|P_f)+\mathrm{KL}(P_f\|P_c).
\]

This is mostly your arbitrary-target Pythagoras, instantiated with the coarse reconstruction as a member of the fine exponential family.

Separately, for \(\mathcal G\subseteq\mathcal H\), define
\[
D^{\mathcal G}
=E_\nu[d\mid\mathcal G]\,\nu,\qquad
D^{\mathcal H}
=E_\nu[d\mid\mathcal H]\,\nu.
\]

**Theorem: observational refinement.**
\[
L_{\mathcal G}
=L_{\mathcal H}
+\mathrm{KL}(D^{\mathcal H}\|D^{\mathcal G}).
\]

Thus invisible information decreases with observation, and total reconstruction error decreases with feature-family refinement.

**But \(R\) is not generally monotone.** In fact,
\[
R_c-R_f
=
\mathrm{KL}(P_f\|P_c)
-\mathrm{KL}(D^{\mathcal H}\|D^{\mathcal G}).
\]
This difference has no fixed sign in general.

This distinction is valuable: **observational resolution** and **expressive capacity of the exponential family** are different axes.

**Likely marginal size:** 150–300 lines per tower identity, mostly reuse.

---

### 7. Full-simplex mixture-path Fisher identities

Let
\[
r=\frac{dD}{d\nu},\qquad
q_s=1+s(r-1),\qquad D_s=q_s\nu.
\]
The mixture-path score is
\[
\partial_s\log q_s=\frac{r-1}{q_s},
\]
whose \(D_s\)-mean is zero. Thus its Fisher speed squared is
\[
k_D(s)
=E_{D_s}\left[\left(\frac{r-1}{q_s}\right)^2\right]
=\int\frac{(r-1)^2}{q_s}\,d\nu.
\]

**Theorem.**
\[
\mathrm{KL}(D\|\nu)=\int_0^1(1-s)k_D(s)\,ds,
\]
\[
\mathrm{KL}(\nu\|D)=\int_0^1s\,k_D(s)\,ds,
\]
\[
\int_0^1k_D(s)\,ds
=\mathrm{KL}(D\|\nu)+\mathrm{KL}(\nu\|D).
\]

These hold in the extended nonnegative sense. For the cheapest first formalization, assume
\[
0<c\le r\le C<\infty.
\]

**Proof.** Integrate the scalar identities
\[
\int_0^1(1-s)\frac{(r-1)^2}{1+s(r-1)}\,ds
=r\log r-r+1,
\]
\[
\int_0^1s\frac{(r-1)^2}{1+s(r-1)}\,ds
=r-1-\log r,
\]
then use \(E_\nu r=1\).

So yes: the full-simplex m-geodesic has precisely the weighted identities you hoped for. The denominator belongs **inside the squared score**, or equivalently as one power in the \(\nu\)-integral above.

**Likely marginal size:** 150–300 lines under two-sided density bounds; extended-valued endpoints deserve a separate extension.

Do not infer pointwise domination of atlas Fisher speed by this speed without another argument: they use different base laws.

---

## 3. Top-ranked item: Lean-facing formulation

I would formalize the finite-\(n\) compact bound first. It avoids extended logarithms entirely.

Below is deliberately schematic rather than pretending to know your namespaces.

```lean
/-- Λ λ = log ∫ exp (⟪λ, S x⟫) ∂ν. -/
def logMGF (λ : V) : ℝ := ...

/-- Extended-valued convex conjugate, on the effective response space. -/
def rate (m : V) : EReal :=
  ⨆ λ : V, ((inner λ m - logMGF λ : ℝ) : EReal)

/-- Mean of the first n+1 iid feature observations. -/
def empiricalMean (n : ℕ) (ω : Ω) : V := ...

theorem compact_chernoff_bound
    (hF : IsCompact F)
    (ha : ∀ m ∈ F, (a : EReal) < rate m) :
    ∃ k : ℕ, 1 ≤ k ∧
      ∀ n : ℕ,
        ℙ {ω | empiricalMean n ω ∈ F}
          ≤ ENNReal.ofReal
              ((k : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ) * a)) := ...
```

For this theorem, the only probabilistic input needs to be:

```lean
hChernoff :
  ∀ (λ : V) (b : ℝ) (n : ℕ),
    ℙ {ω | b ≤ inner λ (empiricalMean n ω)}
      ≤ ENNReal.ofReal
          (Real.exp
            (-((n + 1 : ℕ) : ℝ) * (b - logMGF λ)))
```

An even cheaper intermediate theorem replaces `rate` by explicit witnesses:

```lean
hWitness :
  ∀ m ∈ F, ∃ λ : V, a < inner λ m - logMGF λ
```

Prove compactness plus Chernoff from this hypothesis; discharge `hWitness` from the supremum definition afterward.

### Library ingredients

The top theorem does **not** need to touch `IdentDistrib`, independence, or the SLLN. Those belong inside your existing Chernoff theorem.

Its ingredients are:

- continuity of a linear functional;
- openness of strict superlevel sets;
- finite-subcover extraction, notably `IsCompact.elim_finite_subcover` or its convenient variant in your checkout;
- finite subadditivity of a measure;
- elementary `ENNReal.ofReal` and exponential algebra;
- the complete-lattice characterization of a supremum to extract a witness.

For the lower bound, the relevant infrastructure is:

- your `ae_tendsto_sampleResponse`;
- finite-product density/change-of-measure identities;
- dominated convergence for neighborhood indicators, or an existing “a.s. convergence implies convergence in probability” route;
- logarithmic/exponential limit algebra only at the final wrapper.

I cannot reliably certify whether your 2026 Mathlib revision contains a packaged Cramér theorem. I do not know of one I can safely cite here. In any event, **this self-contained route is likely cheaper to integrate than a general LDP abstraction**.

### Main pitfalls

1. **`Real.log 0` is not \(-\infty\).**  
   Do not write the asymptotic probability statement with an unguarded real logarithm. Either define an extended log-probability or retain the finite exponential bounds as the primary results.

2. **The fixed prefactor matters.**  
   Compactness gives \(k e^{-na}\), not generally \(e^{-na}\). Its logarithm vanishes after division by \(n\).

3. **Use a strict rate threshold.**  
   Start with \(a<\inf_FJ\); do not try to choose maximizers of the conjugate at every point. Boundary maximizers need not exist.

4. **Empty sets and infinite rates should require no special mathematics.**  
   Taking \(k=\max(1,\#\text{subcover})\) handles the empty cover. Arbitrarily large real thresholds handle \(\inf_FJ=\infty\).

5. **Stay in the effective affine space.**  
   Ambient interior may be empty because of affine relations among statistics.

6. **Tilt only finite products.**  
   The infinite iid product measures under \(\nu\) and \(P_\theta\) are generally singular. There is no infinite-product likelihood ratio to use here.

7. **A local atlas only gives a local lower bound.**  
   The radial completion requires atlas coverage of \(\operatorname{ri}K\), not merely existence of a chart around \(m_0\).

---

## 4. What to defer or drop

### Defer: a general unbounded-statistic LDP

It introduces exponential tightness, restricted mgf domains, and boundary/domain issues that do not improve the bounded-statistic response story. First finish the bounded theorem above.

### Defer: deriving a Fréchet Hessian by polarization alone

Polarization identifies a bilinear form **once second Fréchet differentiability is known**. Existence of directional second derivatives—even formulas for all directions—does not by itself establish that regularity.

The cheapest sound route is:

1. \(L^1\) reconstruction derivative;
2. covariance and inverse-covariance differentiability;
3. differentiate the response Jacobian;
4. identify the residual formula.

If `C²` regularity is already packaged, then polarization is indeed an inexpensive final identification step.

### Defer: Fisher geometry as a global `InnerProductSpace` instance

For each \(m\),
\[
g_m(u,z)=\langle u,C_m^{-1}z\rangle
\]
is a positive-definite inner product. But it varies with \(m\). A global typeclass instance on the same `V` is usually the wrong interface.

First package a smoothly varying positive-definite bilinear form, or the isometry
\[
u\longmapsto \ell_{m,u}\in L^2_0(\Pi(m)).
\]
A `RCLike` abstraction adds little to this real statistical geometry.

### Drop: unrestricted monotonicity of \(R\)

It is false in general. Keep the exact difference identity instead.

### Defer: singular endpoint generality for the full bridge

The identities are true with infinite reverse KL, but the boundary bookkeeping is disproportionate to the conceptual gain. Prove the bounded-positive-density version, then extend by Tonelli and scalar endpoint identities.

---

## Recommendation

My implementation order would be:

1. **Compact Chernoff cover lemma.**
2. **Tilted lower bound and radial completion.**
3. **Separate \(L/R\) quadratic limits.**
4. **\(L^1\) reconstruction derivative.**
5. **Conditional variational formula and the two refinement towers.**

The resulting picture has a particularly clean interpretation:

- \(\mathcal I\): the cost of making a response occur;
- \(Dq\): how that response changes the reconstructed law;
- \(R\): response-visible structure beyond the chosen affine features;
- \(L\): structure unavailable to the statistic;
- refinement identities: how those categories move when the observer becomes more capable.

That completes the **map of responses** more directly than another isolated curvature or metric theorem.