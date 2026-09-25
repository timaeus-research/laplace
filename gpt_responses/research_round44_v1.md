I would prioritise **endpoint continuity, intrinsic Legendre geometry, and the differential of the actual data→response map**, in that order. The cubic tensor comes after those—not before them.

Two qualifications are essential:

- For the statements below, assume **`[IsProbabilityMeasure ν]`**. With a merely finite reference measure, normalise it first; the zero-level and KL formulas require mass-dependent corrections.
- An arbitrary data e-geodesic does **not** project to a straight line in natural coordinates. That is true for an e-geodesic **inside the sufficient-statistic exponential family**.

I cannot inspect your Mathlib checkout, so I distinguish theorem names I recognise from APIs whose exact names I cannot certify.

## Common setup

Let
\[
E=\mathbb R^J,\qquad V=\operatorname{dirSpan}(K),\qquad
m_0=\mathbb E_\nu S,
\]
using the **Euclidean** inner product on \(E\), not the default sup norm on a function space. In Lean, `EuclideanSpace ℝ J` is the natural choice.

Assume:

- `J` finite;
- `ν` a probability measure;
- `S` measurable and ν-a.e. bounded;
- your existing hypotheses identifying the moment body and intrinsic chart.

Write
\[
P_\theta=\nu.\mathrm{tilted}\,\langle\theta,S\rangle,\quad
A(\theta)=\log\int e^{\langle\theta,S\rangle}\,d\nu,\quad
I(M)=\operatorname{genRate}_\nu(S,M),
\]
with \(\theta\in V\). Write \(Q_M=\Pi_\nu(M)\) when \(I(M)<\infty\).

Below, expressions involving differences of rates mean their finite real values.

---

## 1. Endpoint convergence of canonical representatives — including a KL certificate

This is the most valuable immediate completion of `MixtureBridge`.

### Main statement

For \(M\) with \(I(M)<\infty\), put
\[
M_s=(1-s)m_0+sM,\qquad Q_s=\Pi_\nu(M_s),\qquad Q=\Pi_\nu(M).
\]

Then, for \(0\le s<1\),
\[
\boxed{
0\le \operatorname{KL}(Q\|Q_s)
\le I(M)-I(M_s).
}
\]

Consequently,
\[
\boxed{
\operatorname{KL}(Q\|Q_s)\longrightarrow0
\quad\text{and}\quad
d_{\rm TV}(Q_s,Q)\longrightarrow0
\qquad(s\uparrow1).
}
\]

With \(d_{\rm TV}(P,Q)=\sup_B|P(B)-Q(B)|\), the quantitative conclusion is
\[
\boxed{
d_{\rm TV}(Q_s,Q)^2
\le \frac12\bigl(I(M)-I(M_s)\bigr).
}
\]

This covers **finite-information boundary endpoints**, not merely interior data.

### Why it follows from your landed layer

For \(s<1\), write \(Q_s=P_{\theta_s}\). The bounded-tilt KL identity gives
\[
\operatorname{KL}(Q\|P_{\theta_s})
=I(M)-I(M_s)-\langle\theta_s,M-M_s\rangle.
\]

The last pairing is nonnegative. For \(s>0\),
\[
M-M_s=\frac{1-s}{s}(M_s-m_0),
\]
and
\[
\langle\theta_s,M_s-m_0\rangle
=I(M_s)+\operatorname{KL}(\nu\|P_{\theta_s})\ge0.
\]
At \(s=0\), \(\theta_0=0\).

Thus the **KL endpoint theorem needs neither Pinsker nor differentiability**. Your landed rate convergence finishes it.

### Pinsker dependency

I would add a probability-specialised theorem:
```lean
-- Schematic; TV convention must be fixed.
theorem totalVariation_sq_le_half_klDiv
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (tv μ ν ^ 2) ≤ (1 / 2) * klDiv μ ν
```

Do not let sharp Pinsker block progress: a nonsharp universal bound
\[
d_{\rm TV}^2\le C\,\operatorname{KL}
\]
already proves the endpoint theorem.

**Mathlib names:** `InformationTheory.klDiv`; an existing Pinsker theorem, KL/f-divergence conversion theorem, and the precise total-variation API: **unsure**. A route through binary coarse-graining is mathematically clean, but depends on whether the needed f-divergence data-processing theorem is available.

**Important asymmetry:** do not claim
\(\operatorname{KL}(Q_s\|Q)\to0\). It can be infinite for every \(s<1\) when \(Q\) is supported on a proper face.

---

## 2. The intrinsic chart is a smooth Legendre equivalence

This is the central structural theorem. It turns your bijection into a response geometry.

### Precise intrinsic formulation

Translate the moment body into \(V\):
\[
\Omega=\{v\in V:m_0+v\in\operatorname{intrinsicInterior}K\},
\]
an open subset of \(V\), and define
\[
F(\theta)=\mathbb E_{P_\theta}S-m_0.
\]

Define the covariance operator \(C_\theta:V\to V\) by
\[
\langle u,C_\theta v\rangle
=\operatorname{Cov}_{P_\theta}
  (\langle u,S\rangle,\langle v,S\rangle).
\]

Prove:

1. \(A|_V\) and \(F\) are smooth.
2. \(DF(\theta)=C_\theta\).
3. \(C_\theta\) is positive definite on \(V\), hence a continuous linear equivalence.
4. The existing inverse \(G:\Omega\to V\) is smooth, with
   \[
   DG(v)=C_{G(v)}^{-1}.
   \]

The natural Lean derivative statement is schematically:
```lean
HasFDerivAt F (covarianceCLM θ) θ
```
and, for a locally defined or totalised inverse on the open set `Ω`,
```lean
HasFDerivAt G (covarianceEquiv (G v)).symm v
```

Then obtain the dual identities:
\[
\boxed{
DI(M)[u]=\langle\theta(M),u\rangle,\qquad
D^2I(M)[u,v]=\langle u,C_{\theta(M)}^{-1}v\rangle.
}
\]

Here all derivatives of \(I\) are **intrinsic**, along \(V\).

### Hypotheses

No nondegeneracy assumption beyond restricting to \(V\). Indeed,
\[
\operatorname{Var}_{P_\theta}(\langle v,S\rangle)=0
\]
means that \(\langle v,S\rangle\) is ν-a.e. constant, hence \(v\perp V\); for \(v\in V\), this forces \(v=0\).

### Formalisation advice

Land **C¹ first**, then smoothness. Reuse the existing global bijection: the inverse function theorem supplies local regularity, not another global-surjectivity proof.

**Mathlib names:** `HasStrictFDerivAt.toPartialHomeomorph`, `HasFDerivAt.comp`, `ContDiff`, `ContDiffOn`. The exact derivative-under-the-integral and smooth-inverse lemma names are **unsure**.

---

## 3. Differential of the data→response map, with explained-information curvature

This is the theorem most directly answering the standing direction.

### General local response formula

Let \(D\) be a probability law, \(h\) bounded and measurable, and
\[
D_s=D.\mathrm{tilted}(s h),\qquad M(s)=\mathbb E_{D_s}S.
\]
Assume \(D\ll\nu\) and \(M(0)\in\operatorname{intrinsicInterior}K\). Then locally,
\[
M'(s)=\operatorname{Cov}_{D_s}(S,h),
\]
and
\[
\boxed{
\theta'(s)
=C_{\theta(M(s))}^{-1}\operatorname{Cov}_{D_s}(S,h).
}
\]

Consequently,
\[
\boxed{
\frac{d}{ds}I(M(s))
=\left\langle\theta(M(s)),
                 \operatorname{Cov}_{D_s}(S,h)\right\rangle.
}
\]

This cleanly separates:

- **data-side forcing:** \(\operatorname{Cov}_{D_s}(S,h)\);
- **response-side susceptibility:** \(C_{\theta(M(s))}^{-1}\).

### Especially beautiful basepoint theorem

Take \(D=\nu\), and let
\[
b=\operatorname{Cov}_\nu(S,h)\in V.
\]
Then
\[
\left.\frac{d}{ds}I(M(s))\right|_{s=0}=0,
\]
and
\[
\boxed{
\left.\frac{d^2}{ds^2}I(M(s))\right|_{s=0}
=\langle b,C_0^{-1}b\rangle
\le \operatorname{Var}_\nu(h).
}
\]

The gap is exactly a residual variance:
\[
\operatorname{Var}_\nu(h)-\langle b,C_0^{-1}b\rangle
=
\operatorname{Var}_\nu\!\left(
h-\langle C_0^{-1}b,S\rangle
\right).
\]

Thus infinitesimal information entering the data decomposes into **information visible in the chosen responses** and **invisible residual information**.

Your information decomposition then identifies this gap with the second derivative, at zero, of
\[
\operatorname{KL}(D_s\|\Pi_\nu(M(s))).
\]

### Hypotheses and feasibility

For the basepoint theorem, bounded measurable \(h\) and your usual bounded statistics suffice. Finite-information assumptions on general \(D\) are needed only when also asserting its information decomposition.

**Mathlib names:** `HasFDerivAt.comp`; your `ThermalTransport` derivative theorems do most of the work. Exact covariance/regression API names: **unsure**. The residual-variance identity can be proved directly by expanding the square.

---

## 4. Quantitative susceptibility: global response control, local inverse stability

This should address open item 2b, while also supplying the proposed response-information bound.

### Global covariance upper bound ⇒ global quadratic information bound

Assume \(L>0\) and
\[
\langle u,C_\theta u\rangle\le L\|u\|^2
\qquad\text{for every }\theta,u\in V.
\]

Then
\[
\boxed{
\|F(\theta)-F(\eta)\|\le L\|\theta-\eta\|
}
\]
and, for \(M\in m_0+V\),
\[
\boxed{
I(M)\ge\frac{\|M-m_0\|^2}{2L}.
}
\]

The latter is an extended-real statement, so it also covers \(I(M)=\infty\).

A simple sufficient hypothesis is
\[
\|S(x)-m_0\|\le B\quad \nu\text{-a.e.},
\]
which gives \(L=B^2\), taking \(B>0\).

**Proof route:** integrate the covariance bound to obtain
\[
A(\theta)-\langle\theta,m_0\rangle
\le \frac L2\|\theta\|^2,
\]
then evaluate the Cramér supremum at
\(\theta=(M-m_0)/L\). No Chernoff tail theorem is required.

### Local inverse stability

For every finite radius \(r\), there is \(\kappa_r>0\) such that, for \(\|\theta\|,\|\eta\|\le r\),
\[
\boxed{
\kappa_r\|\theta-\eta\|
\le \|F(\theta)-F(\eta)\|
\le L\|\theta-\eta\|.
}
\]

Use continuity and positive definiteness of \(C_\theta\), compactness of the parameter ball and unit sphere, and strong monotonicity along segments. Handle \(V=\{0\}\) separately or vacuously.

### Mixture-path consequence

For \(v=M-m_0\), \(M_s=m_0+sv\), and \(s<1\),
\[
I'(M_s\text{ along }s)=\langle\theta_s,v\rangle,\qquad
\frac{d^2}{ds^2}I(M_s)=\langle v,C_{\theta_s}^{-1}v\rangle.
\]
In particular, the **right derivative at zero is zero**.

**Mathlib names:** compactness/continuous-extremum and derivative-to-Lipschitz APIs should supply this, but their exact names are **unsure**. The Chernoff lemma mentioned in the question is not the right dependency.

**Caution:** a covariance bound only at \(\nu\) is insufficient for the global quadratic lower bound. You need a bound along all relevant tilts. A global inverse-Lipschitz bound generally fails near the boundary.

---

## 5. The correct geodesic/Bregman theorem — with an explicit limit on what projection preserves

This is worth packaging, but only in its correct form.

### Mixture-geodesic preservation: arbitrary finite-information data

For \(D\) a probability law with \(\operatorname{KL}(D\|\nu)<\infty\),
\[
D_s=(1-s)\nu+sD
\]
satisfies
\[
\boxed{
\mathbb E_{\Pi_\nu(\mathbb E_{D_s}S)}S
=(1-s)m_0+s\mathbb E_D S.
}
\]

Thus the representative path is an **m-geodesic in expectation coordinates**, although its measures need not themselves form a mixture.

### Exponential-geodesic preservation: within the family

For \(\theta_0,\theta_1\in V\),
\[
\theta_s=(1-s)\theta_0+s\theta_1
\]
gives
\[
P_{\theta_s}\propto
\left(\frac{dP_{\theta_0}}{d\nu}\right)^{1-s}
\left(\frac{dP_{\theta_1}}{d\nu}\right)^s\nu,
\]
and projection fixes this path.

The elegant unifying identity is
\[
\boxed{
\operatorname{KL}(P_\theta\|P_\eta)
=
A(\eta)-A(\theta)-\langle\nabla A(\theta),\eta-\theta\rangle
=
B_I(M_\theta,M_\eta).
}
\]

Notice the reversed natural-coordinate order:
\[
\operatorname{KL}(P_\theta\|P_\eta)=B_A(\eta,\theta).
\]

This establishes the operative content of dual flatness before introducing connection objects.

### Why the arbitrary-data version is false

Take uniform \(\nu\) on \(\{-1,0,1\}\), statistic \(S(x)=x\), and \(h(x)=1_{\{1\}}(x)\). For \(D_s=\nu.\mathrm{tilted}(sh)\),
\[
M(s)=\frac{e^s-1}{e^s+2}.
\]
Its representing natural parameter satisfies
\[
\theta'(0)=\frac12,\qquad \theta''(0)=\frac16.
\]
It is therefore **not a straight natural-coordinate path**.

**Mathlib names:** your `familyMeasure_eq_tilted`, `mean_mixture`, and existing bounded-tilt KL identities. A generic Bregman-divergence API: **unsure**; an explicit scalar identity is sufficient.

---

## 6. Cubic response tensor and dual third derivatives

After ranks 2–4, this becomes a natural and comparatively focused next layer.

For \(u,v,w\in V\), define
\[
T_\theta(u,v,w)
=
\mathbb E_{P_\theta}
\!\left[
\langle u,S-M_\theta\rangle
\langle v,S-M_\theta\rangle
\langle w,S-M_\theta\rangle
\right].
\]

Prove
\[
\boxed{
D^3A(\theta)[u,v,w]=T_\theta(u,v,w)
}
\]
and
\[
\boxed{
D^3I(M)[u,v,w]
=
-T_{\theta(M)}
\bigl(C_{\theta(M)}^{-1}u,
      C_{\theta(M)}^{-1}v,
      C_{\theta(M)}^{-1}w\bigr).
}
\]

Interpretation: covariance gives susceptibility; the cubic tensor gives **how susceptibility changes as the data move**.

These formulas are a better first target than a full differential-geometric connection API. Afterwards, in natural coordinates, the e-connection has zero coefficients, the m-connection has coefficients obtained by raising an index of \(T\) with \(C^{-1}\), and the Levi–Civita connection has half those coefficients.

**Hypotheses:** the common bounded-statistic setup suffices for all finite derivatives.

**Mathlib names:** `ContinuousMultilinearMap`, `ContDiff`; exact iterated-derivative and inverse-operator differentiation lemmas: **unsure**.

---

## Stress-test of (v) and (vi)

### (v) Zero rate iff the featureless response

Under probability normalisation, this is correct:
\[
\boxed{I(M)=0\iff M=m_0.}
\]

Your completion theorem makes the forward implication immediate:
\[
I(M)=0
\Rightarrow \operatorname{KL}(\Pi_\nu M\|\nu)=0
\Rightarrow \Pi_\nu M=\nu
\Rightarrow M=m_0.
\]

The reverse implication follows by using \(\nu\) itself.

**Known name:** `InformationTheory.klDiv_eq_zero_iff`, subject to its probability hypotheses.

I would land this immediately as a small prerequisite, rather than spend a major milestone on it. Call it **zero-information characterisation**. Calling it “maximum entropy” is justified only when \(\nu\) is uniform relative to the chosen finite reference measure; an arbitrary prior is not intrinsically featureless.

### (vi) Information gained per unit response

- **Mixture path:** derivative at \(s=0\) is zero—correct, interpreted intrinsically/right-sided.
- **Statistical e-path \(P_{sh}\):**
  \[
  \frac d{ds}I(M(sh))
  =s\,\operatorname{Var}_{P_{sh}}(\langle h,S\rangle),
  \]
  not just `Var`.
- **Arbitrary data e-path \(\nu.\mathrm{tilted}(sf)\):**
  \[
  \frac d{ds}\operatorname{KL}(D_s\|\nu)
  =s\,\operatorname{Var}_{D_s}(f),
  \]
  but the derivative of the **response rate** is generally different; rank 3 gives the correct formula.
- The global quadratic bound is correct with a **uniform tilted covariance bound**, not merely the covariance at the base law. It is better described as a response-information lower bound than as reverse Pinsker.

**Recommended implementation order:** zero-rate corollary → endpoint KL convergence → Pinsker/TV → C¹ intrinsic Legendre chart → differential data response → quantitative stability → Bregman packaging → cubic tensor.