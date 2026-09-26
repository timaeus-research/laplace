## 1. Recommended ranking

The programme now has the decomposition and most of its infinitesimal shadow. I would organise the next work around two goals:

1. **Explain how the atlas bends**, rather than merely how much energy it has.
2. **Make the global domain of the atlas precise**, including the distinction between interior responses and boundary laws.

My ranking by **depth × feasibility**, given the stated seabed, is:

| Rank | Target | Why now |
|---|---|---|
| **1** | **Skewness controls curvature variation and KL asymmetry** | A short conceptual completion of several landed results; turns asymmetry into an accumulated third-order statistic. |
| **2** | **Mixed response Hessian, then observable-defect second order as a corollary** | Identifies the atlas’s extrinsic bending and packages the remaining local second-order phenomena into one theorem. |
| **3** | **Global response-chart theorem, modulo parameter gauge** | The deepest structural target: identifies exactly which response manifold has been constructed. Higher cost, but central rather than peripheral. |
| **4** | **Remove bounded-density assumptions from the bridge curvature split** | Makes the bridge genuinely reach the finite-information data laws already covered by the global decomposition. |
| **5** | **Conditional variational formula for general densities** | Completes the operational meaning of fibre information; a supremum, generally not a bounded maximiser. |
| **6** | **Four-path comparison package** | Beautiful and relatively inexpensive if restricted to valid comparisons: equal endpoint energies, conditional contraction, and common length lower bounds. |
| **7** | Further intrinsic/extrinsic curvature tensors | Worth doing after the mixed Hessian and global chart, not before. |

I would not start another round of isolated identities. The best next package is **“third-order geometry and the second fundamental form,”** followed by **“global atlas and its boundary.”**

---

## 2. What the main targets should say

### A. Skewness: the best immediate target

Use the **positive response score** convention
\[
\ell_{M,v}(x)
  :=\left\langle\Sigma_M^{-1}v,S(x)-M\right\rangle,
\]
where covariance is inverted only on the effective direction space \(\mathbb V\).

Along a straight response path \(M_s=M_0+sv\),
\[
\frac{d}{ds}\log q_{M_s}=\ell_{M_s,v},
\qquad
\kappa(s)=E_{Q_s}\ell_{M_s,v}^{\,2}.
\]

Then the desired statement is
\[
\boxed{\kappa'(s)=-E_{Q_s}\ell_{M_s,v}^{\,3}.}
\]

For \(M_0=m_\nu\), \(Q_0=\nu\), integration by parts gives
\[
\boxed{
KL(Q_1\Vert\nu)-KL(\nu\Vert Q_1)
=\int_0^1s(1-s)E_{Q_s}\ell_{M_s,v}^{\,3}\,ds.
}
\]

This is more than another cumulant formula:

> The direction of KL asymmetry is the weighted accumulated skewness of the response score along the atlas.

The score convention matters. Using \(\langle D\theta\,v,S-M\rangle\) instead reverses the score’s sign.

#### Envelope theorem or inverse differentiation?

**Conceptually, the envelope theorem is cleaner. In Lean, a finite covariance identity is probably cleaner still.**

Write \(\beta_s=\Sigma_s^{-1}v\). Then
\[
\kappa(s)
=\max_b\{2\langle v,b\rangle-\langle b,\Sigma_s b\rangle\}.
\]
The stationary-point calculation immediately suggests
\[
\kappa'(s)=-\langle\beta_s,\Sigma_s'\beta_s\rangle.
\]

But a generic envelope theorem introduces unnecessary machinery. Instead use the exact identity
\[
\boxed{
\kappa(t)-\kappa(s)
=-\langle\beta_t,(\Sigma_t-\Sigma_s)\beta_s\rangle.
}
\]
It needs only continuity of \(\beta\) and differentiability of covariance—not differentiability of the inverse or of \(\beta\).

Your covariance-path derivative then supplies
\[
\langle\beta_s,\Sigma_s'\beta_s\rangle
=E_{Q_s}\ell_s^3.
\]

If smooth inverse covariance is already easy to invoke, ordinary differentiation followed by cancellation may have fewer Lean lines. I would not build a general envelope API just for this theorem.

---

### B. Mixed Hessian: the local geometric heart

Let \(P_0f=E_Qf\) denote the constant projection, and let \(B_M\) be the centred feature-regression projection in \(L^2(Q)\). For \(u,z\in\mathbb V\),
\[
\boxed{
D^2q_M[u,z]
=q_M(I-P_0-B_M)(\ell_{M,u}\ell_{M,z}).
}
\]

**Notation warning:** if your \(C\) denotes conditional expectation onto \(\sigma(S)\), do not state this as \(I-C-B\). The projection subtracted here is the **constant projection**, not conditional expectation. Indeed, the product of the scores is already \(\sigma(S)\)-measurable.

This Hessian has zero mass and zero feature moments:
\[
\int D^2q_M[u,z]\,d\nu=0,\qquad
\int S\,D^2q_M[u,z]\,d\nu=0.
\]

That is the structural content:

> In affine response coordinates, all second-order bending of the atlas lies in directions invisible to the response map.

After identifying a density variation with its score, the normal component is precisely the residualised product of two tangent scores. This is the natural precursor to a second-fundamental-form theorem; one should distinguish it from the Levi-Civita second fundamental form for the ambient Fisher metric.

For any bounded observable \(f\), define
\[
r_{f,M}=f-E_Qf-B_Mf.
\]
Then
\[
\boxed{
D^2\big(E_{\Pi(M)}f\big)[u,z]
=E_Q[r_{f,M}\ell_{M,u}\ell_{M,z}].
}
\]

This packages—and polarises—the existing diagonal observable-transport theorem.

---

### C. Observable-defect second order: make it a corollary

There are several possible meanings of “observable defect.” A particularly useful data-to-atlas version is the following.

At \(Q=\Pi(M)\), let
\[
D_t=\frac{e^{th}Q}{E_Qe^{th}},\qquad M_t=E_{D_t}S,
\]
with bounded \(h,f\). Put
\[
\bar h=h-E_Qh,\qquad b=E_Q[(S-M)\bar h],
\qquad \ell_b=\ell_{M,b}=B_Mh,
\]
and
\[
\Delta_f(t)=E_{D_t}f-E_{\Pi(M_t)}f.
\]
Then
\[
\Delta_f(0)=0,\qquad
\Delta_f'(0)=E_Q[r_{f,M}\bar h],
\]
and
\[
\boxed{
\Delta_f''(0)
=E_Q\!\left[r_{f,M}\big(\bar h^2-\ell_b^2\big)\right].
}
\]

Thus
\[
\Delta_f(t)
=tE_Q[r_f\bar h]
+\frac{t^2}{2}E_Q[r_f(\bar h^2-(B_Mh)^2)]
+o(t^2).
\]

This cleanly separates nonlinear change in the data law from nonlinear change along the reconstructed atlas.

I would prove the mixed Hessian first and derive this by the chain rule. A separate bespoke second-order density expansion would duplicate effort.

---

### D. Global structure: a chart and a variational section, not yet a fibration

Let
\[
K=\overline{\operatorname{conv}}\big(\operatorname{ess\,range}_\nu S\big),
\qquad
\mathbb V=\operatorname{span}(K-K).
\]
Because the features are bounded and the index set is finite, \(K\) is compact.

The clean theorem is:

> **The gauge-fixed mean map is a smooth diffeomorphism**
> \[
> m:\mathbb V\longrightarrow \operatorname{ri}K,
> \]
> for the family \(e^{-\langle\theta,S\rangle}\nu/Z(\theta)\), with
> \[
> Dm(\theta)=-\Sigma_\theta,\qquad
> D\theta(M)=-\Sigma_M^{-1}.
> \]

Relative interior should ideally be represented as an ordinary open subset of the affine space \(m_\nu+\mathbb V\).

The gauge is essential: on the original parameter space, directions whose feature pairing is almost surely constant do not change the law.

Then add a separate theorem:

> For each \(M\in\operatorname{ri}K\), \(\Pi(M)\) is the unique minimiser of \(KL(D\Vert\nu)\) among probability laws with response \(M\), and, for finite-information competitors,
> \[
> KL(D\Vert\nu)
> =KL(D\Vert\Pi(M))+KL(\Pi(M)\Vert\nu).
> \]

This gives an exact section of the response map and a canonical point in every interior fibre.

I would **not call the general construction a fibration** yet:

- “Full simplex” is problematic for a general measurable \(X\).
- Laws not dominated by \(\nu\) may see feature values outside the essential moment body.
- Boundary responses need not be attainable by dominated laws.
- Even in a finite simplex, fibres change dimension at the boundary; global local triviality is not automatic.

In Lean, the best first global statement is therefore:

1. a gauge-fixed smooth chart;
2. a response map on probability densities;
3. a section on interior responses;
4. a unique fibrewise KL minimiser.

Also, “maximum entropy” here means relative to the chosen reference measure, unless \(\nu\) has separately been identified with an absolute maximum-entropy law.

**Likely hard lemma:** coercivity of
\[
\theta\longmapsto\log Z(\theta)+\langle\theta,M\rangle
\]
on \(\mathbb V\), for \(M\in\operatorname{ri}K\). A compact-direction/finite-cover argument is a plausible direct route if the relevant convex-duality theorem is not already available.

---

### E. A canonical fourth path

For bounded positive \(d=dD/d\nu\), the full exponential path is canonical:
\[
E_s=\frac{d^s\nu}{\int d^s\,d\nu}.
\]

It has the same endpoints as the mixture bridge, but generally **not** the same response schedule \(M_s\).

The clean comparison is an equal-energy theorem:
\[
\boxed{
\int_0^1 k_d(s)\,ds
=
\int_0^1\operatorname{Var}_{E_s}(\log d)\,ds
=
KL(D\Vert\nu)+KL(\nu\Vert D).
}
\]

For the exponential path, this is simply integration of
\[
\frac{d}{ds}E_{E_s}\log d=\operatorname{Var}_{E_s}(\log d).
\]

Together with existing results, this gives parallel equal-energy pairs:

- mixture and exponential paths between \(\nu,D\);
- response-straight and exponential paths between \(\nu,\Pi(M)\);
- mixture and exponential paths between \(\nu,D^\uparrow\).

The lift bridge satisfies pointwise Fisher contraction relative to the data bridge. There is **no corresponding general pointwise contraction to the atlas**.

A further canonical path is the Fisher–Rao great-circle path. Under the convention \(\int h^2\,dP\), its endpoint distance is
\[
2\arccos\!\int\sqrt d\,d\nu.
\]
This gives a common lower bound for lengths of paths joining \(\nu\) to \(D\), but introduces a new geometric API. I would defer it.

---

### F. Unbounded densities: split the work

#### Bridge curvature first

For \(d\ge0\), \(\int d\,d\nu=1\), the bridge density
\[
d_w=1-w+wd
\]
is bounded below for \(w<1\), even when \(d\) is unbounded or vanishes.

For \(0<w<1\),
\[
k_d(w)=\int\frac{(d-1)^2}{d_w}\,d\nu
\]
is finite under mere integrability of \(d\). At \(w=0\), it may be infinite.

Thus the natural extension uses:

- interior-time curvature identities;
- nonnegative integral representations;
- endpoint limits;
- finite KL where finite-valued endpoint statements are desired.

This need not be organised entirely around clipping. The nonnegative kernel representation and Tonelli/monotone arguments may be more natural.

For \(R\), use the difference of already-controlled representations. Do not apply monotone convergence directly to the possibly signed integrand \(k_a-\kappa\).

#### Conditional variational formula second

The general target is
\[
\boxed{
L=\sup_{g\ \mathrm{bounded,\ measurable}}
\left\{E_Dg-E_D\log E_\nu[e^g\mid\sigma(S)]\right\}.
}
\]

Replace `IsGreatest` by a supremum statement. The formal optimiser \(\log(d/a)\) is generally unbounded and may be \(-\infty\).

Clipping that log-ratio is the correct recovery construction, with explicit conventions on \(\{a=0\}\). The delicate part is convergence of the conditional log-normalisation term, not merely convergence of the linear term.

---

## 3. Precise top-ranked theorem and Lean proof plan

### Hypotheses

Assume:

- \(J\) finite;
- \((X,\mathcal A,\nu)\) a probability space;
- \(S:X\to\mathbb R^J\) measurable and bounded;
- \(K\) and \(\mathbb V\) as above;
- the existing interior response chart \(M\mapsto\theta(M)\), with its first-derivative formula;
- \(M_0,M_1\in\operatorname{ri}K\).

Set
\[
v=M_1-M_0,\quad M_s=M_0+sv,\quad Q_s=\Pi(M_s),
\]
\[
\beta_s=\Sigma_{M_s}^{-1}v,\quad
\ell_s=\langle\beta_s,S-M_s\rangle,\quad
\kappa(s)=\langle v,\beta_s\rangle.
\]

### Statements

For every \(s\in[0,1]\), using the chart on a neighbourhood of the segment,
\[
\operatorname{HasDerivAt}\ \kappa\
\left(-\int\ell_s^3\,dQ_s\right)\ s.
\]

Moreover, the third-moment function is continuous on \([0,1]\).

When \(M_0=E_\nu S\),
\[
KL(Q_1\Vert\nu)-KL(\nu\Vert Q_1)
=\int_0^1s(1-s)\int\ell_s^3\,dQ_s\,ds.
\]

No separate bounded-positive data density is needed here: the path consists entirely of interior atlas laws.

### Proof in lemma-sized pieces

1. **Effective covariance invertibility.**  
   Reuse or package positive definiteness on \(\mathbb V\), and continuity of the covariance solution \(\beta_s\).

2. **Identify the path score.**
   \[
   \theta'(s)=-\beta_s,\qquad
   \partial_s\log q_s=\ell_s.
   \]

3. **Differentiate covariance with frozen arguments.**  
   For fixed \(b,c\in\mathbb V\),
   \[
   \frac{d}{ds}\operatorname{Cov}_{Q_s}
      (\langle b,S\rangle,\langle c,S\rangle)
   =
   E_{Q_s}\!\left[
   \langle b,S-M_s\rangle
   \langle c,S-M_s\rangle\ell_s
   \right].
   \]
   This should specialise `hasDerivAt_lawCov_familyMeasure_path`.

4. **Prove the finite-difference stationary-value identity.**
   \[
   \kappa(t)-\kappa(s)
   =-\langle\beta_t,(\Sigma_t-\Sigma_s)\beta_s\rangle.
   \]
   This is finite-dimensional linear algebra using
   \(\Sigma_t\beta_t=\Sigma_s\beta_s=v\).

5. **Take the difference-quotient limit.**  
   Continuity of \(\beta_t\) and step 3 give
   \[
   \kappa'(s)=-\langle\beta_s,\Sigma_s'\beta_s\rangle
   =-E_{Q_s}\ell_s^3.
   \]
   A small reusable lemma for a continuous factor multiplying a vanishing differentiable increment may help.

6. **Continuity and integrability.**  
   On the compact parameter path, bounded features and continuous coefficients provide domination. Reuse existing family-integral continuity machinery.

7. **Integrate by parts.**  
   Starting from the landed asymmetry formula,
   \[
   \int_0^1(1-2s)\kappa(s)\,ds
   =-\int_0^1s(1-s)\kappa'(s)\,ds,
   \]
   since \(s(1-s)\) vanishes at both endpoints.

### Estimated size

Without inspecting the files, I would budget:

| Component | Lines |
|---|---:|
| Score/covariance specialisation | 70–130 |
| Stationary-value derivative helper and skewness theorem | 100–180 |
| Continuity/integrability packaging | 40–90 |
| Integration-by-parts corollary | 50–100 |
| **Total** | **260–500** |

This assumes the effective-space covariance inverse and its continuity are already packaged. If not, add roughly 100–200 lines. A generic envelope theorem would likely cost more than it saves.

---

## 4. What to drop from round 52?

**Drop none mathematically. Change their packaging.**

- **Item 10, skewness:** do next. Highest payoff per likely Lean line.
- **Item 7, mixed Hessian:** keep. This is the missing local geometric heart.
- **Item 6, observable defect:** stop treating it as an independent major development. Derive it from item 7 and the exponential-tilt chain rule.

If one item must leave the active queue, remove **6 as a standalone implementation**, not as a desired theorem.

The coherent next narrative is:

> **The response map has a canonical first-order regression, its atlas bends only in response-invisible directions, and its third-order skewness governs information asymmetry.**

The global chart theorem then tells you exactly where that geometry lives.