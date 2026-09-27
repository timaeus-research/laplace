## Recommendation

Start **programme D: the curved response quotient**.

Its two main components should be:

1. **D1: Fisher geometry downstairs**, expressed entirely through multilinear operators and derivatives of paths.
2. **D4: topology upstairs**, using normalized densities in \(L^1\), rather than choosing a topology on representatives of log-densities.

Together they say something substantially stronger than “the response is a smooth submersion”: **the response space is a topological quotient with contractible fibres, equipped with an explicitly computable, generally curved Fisher geometry.**

C6 remains worth finishing, but there is a correction to its proposed formula unless the slice directions are invisible. I would not make the new programme depend on its bump-function implementation.

---

# Q1. Ranking D1–D7

### 1. D1 — Fisher geometry in natural coordinates

**Highest depth × reachability.** The existing \(A,T\), inverse-chart machinery, and mean-affine journeys already contain the e-/m-/Levi-Civita connections. No manifold API is required: define a smooth symmetric-bilinear Christoffel operator on \(W\), define path acceleration and curvature in coordinates, and prove the identities directly. The particularly valuable theorem is curvature: all derivatives of the third cumulant cancel, leaving a quadratic expression in \(A^{-1}T\). This also gives the entire \(\alpha\)-connection family almost for free. Be meticulous about the sign: with \(A=D\mu=-G^\sharp\), the mixture Christoffel operator is **\(A^{-1}T\)** and the Levi-Civita operator is **\(\tfrac12A^{-1}T\)**.

### 2. D4 — Topological response quotient and fibre contraction

**Very high reachability once the topology is chosen correctly.** Work with the image of admissible bounded tilts as normalized densities in \(L^1\), thereby identifying additive constants and almost-everywhere changes automatically. Boundedness of \(S\) makes the mean map continuous; local continuity of the inverse mean chart makes the response continuous. The already-proved mixture identities then give a **fibre-preserving strong deformation retraction** onto the model family. A continuous model section proves that the response is a quotient map, hence that the moment-equivalence quotient is homeomorphic to \(W\). This does **not** require a bundle theorem or properness.

### 3. D3 — Fibre second jet

**Close the gap, but correct the general statement.** Write \(K\xi=\sum_i\xi_i k_i\), \(D=D\Phi_g\), and let \(h=\mathrm{hor}_g\). For the fixed-response graph,
\[
D\sigma_0(0)\xi=-DK\xi,\qquad
J\xi:=K\xi-hDK\xi.
\]
The general formula is
\[
D^2\sigma_0(0)[\xi,\eta]
   =-H_g(J\xi,J\eta)
   =-A_g^{-1}B_g(J\xi,J\eta).
\]
Your proposed formula with \(K\xi\) is correct **when the slice directions are invisible**. I would first try twice differentiating the finite-dimensional augmented-slice identity, or localizing the coefficient-journey lemmas; a global bump is a fallback, not the mathematical centre. Also refine the caveat: there is no intrinsic *Riemannian* second fundamental form without extra structure, but a fixed affine ambient structure does support a canonical **normal-quotient-valued second jet**.

### 4. D7 — A better lifting theorem: exponential leaves through arbitrary laws

The deeper alternative to the Banach-space ODE is to fix \(g_0\) and use the offset exponential family
\[
\lambda\longmapsto \rho_{\,g_0-\langle\lambda,S\rangle}.
\]
If its mean map is a diffeomorphism onto the same mean domain, every prescribed response path has a unique lift in this finite-dimensional leaf through \(\rho_{g_0}\). This is genuinely nontrivial and avoids infinite-dimensional ODE theory. Under bounded \(g_0\), the base measures have the same null sets and comparable densities, making reuse of the global mean-chart theorem plausible. **The missing item is a checked base-change theorem:** I would not promise global lifting before verifying that all hypotheses of the existing mean-range theorem survive this change of reference measure.

### 5. D2 — First variation of response length

Useful and reachable, but currently more analysis than new geometry. After D1, the invariant formulation becomes cleaner: first variation of energy, then length under positive speed, with the Levi-Civita acceleration appearing after integration by parts. Start with **energy**, which has no square-root singularity, and then derive length. Compact-interval differentiation under the integral and uniform positivity are genuine obligations. This belongs immediately after programme D, rather than preceding the connection machinery.

### 6. D6 — Prescribed-response journeys by a horizontal ODE

Local lifting is realistic; global existence on \([0,1]\) is not automatic. Smoothness of \(\mathrm{hor}\) does not prevent its norm from becoming large along a lift, and compactness of the prescribed response path alone does not control the upstairs law. Moreover, if the existing horizontal vectors are feature-linear tilts, the ODE stays in the finite-dimensional exponential leaf through its starting law. In that case D7 is the better theorem and proof route. Do not spend the next programme building Banach-space Picard–Lindelöf infrastructure unless the desired horizontal distribution genuinely leaves those leaves.

### 7. D5 — Finite-range compactified topology

Potentially deep, but least ready from the information supplied. A continuous bijection from compact \(\widehat W\) to the Hausdorff polytope is a homeomorphism; the work lies in defining the topology and proving compactness and continuity across strata. Facewise homeomorphisms and compatible embeddings do not by themselves establish the required cross-face convergence. This deserves a separate compactification programme, not an opportunistic extension of the current response calculus.

---

# Q2. Six modules for the top two

Below, names not already listed in the question are **proposed declarations**, not claims about existing identifiers.

Use these mathematical aliases:

\[
\begin{aligned}
\mu(\theta)&=\operatorname{meanMap}(\theta),\\
A_\theta&=D\mu_\theta,\\
T_\theta(u,v)&=D^2\mu_\theta[u,v],\\
G_\theta(u,v)&=-\langle A_\theta u,v\rangle,\\
C_\theta(u,v)&=A_\theta^{-1}T_\theta(u,v).
\end{aligned}
\]

Thus \(A_g=A_{\Phi(g)}\). In Lean, package \(G,T,C\) as continuous bilinear maps where practical.

## D01. `ResponseFisherJets`

**Deliverable:** The Fisher metric is positive definite, its derivative is minus the third cumulant, and \(C=A^{-1}T\) satisfies the metric-compatibility algebra.

### Target statements

```lean
theorem fisher_eq_neg_inner_meanDeriv :
  fisher θ u v = - inner (A θ u) v

theorem fisher_pos (hu : u ≠ 0) :
  0 < fisher θ u u

theorem hasDerivAt_fisher_line :
  HasDerivAt
    (fun t : ℝ => fisher (θ + t • u) v w)
    (- inner (T θ u v) w) 0

theorem fisher_mChristoffel :
  fisher θ (mChristoffel θ u v) w =
    - inner (T θ u v) w
```

Here:

```lean
mChristoffel θ u v := (A θ).symm (T θ u v)
```

with the inverse notation adapted to the existing equivalence packaging.

Also export total symmetry of

```lean
fun u v w => inner (T θ u v) w
```

and symmetry of `mChristoffel θ`.

### Proof route

Specialize the existing tilted covariance/cumulant differentiation to `modelTilt θ`. The negative sign in the tilt makes \(D G=-T\). Positive definiteness follows from the existing nondegeneracy/minimality hypotheses behind invertibility of the mean derivative.

**Important:** invertibility alone is not the positivity proof; use that covariance is positive semidefinite and nondegenerate.

### Existing declarations to reuse

- `modelTilt`
- `responseOf_modelTilt`
- Existing covariance and third-cumulant derivative lemmas
- Existing identification of chart derivative with minus covariance
- Existing mean-chart inverse/equivalence machinery

---

## D02. `ResponseDualConnections`

**Deliverable:** Construct the e-/m-/Levi-Civita and \(\alpha\)-connections as coordinate operators, prove duality, and identify mixture geodesics.

Define

```lean
alphaChristoffel α θ u v :=
  ((1 - α) / 2) • mChristoffel θ u v
```

Thus `α = 1` is exponential, `α = -1` is mixture, and `α = 0` is Levi-Civita.

### Target statements

Writing the directional metric derivative explicitly:

```lean
theorem fisher_deriv_eq_alpha_duality :
  - inner (T θ u v) w =
    fisher θ (alphaChristoffel α θ u v) w +
    fisher θ v (alphaChristoffel (-α) θ u w)
```

```lean
theorem alphaChristoffel_symmetric :
  alphaChristoffel α θ u v =
    alphaChristoffel α θ v u
```

For a twice differentiable path \(\theta(t)\), with jets \(v,a\) at \(t\):

```lean
theorem meanPath_secondDeriv :
  meanAcceleration =
    A (θ t)
      (a + mChristoffel (θ t) v v)
```

Consequently:

```lean
theorem meanPath_accel_eq_zero_iff :
  meanAcceleration = 0 ↔
    a + mChristoffel (θ t) v v = 0
```

The actual Lean statement should take explicit `HasDerivAt` hypotheses for the path and its velocity, rather than hide regularity inside `meanAcceleration`.

### Proof route

Duality is D01 plus
\((1-\alpha)/2+(1+\alpha)/2=1\).
The path theorem is the second-order chain rule:
\[
(\mu\circ\theta)''=A_\theta\theta''+T_\theta(\theta',\theta').
\]

Specialize to the already-constructed mean-affine journeys.

### Existing declarations to reuse

- `responseOf_localMixTilt_eq`
- `eventually_hasDerivAt_responseOf_localMixTilt`
- `hasDerivAt_mixResponseVel`
- D01’s metric derivative and symmetry lemmas

This module establishes the connection interpretation without asserting the existence of any Mathlib manifold connection object.

---

## D03. `ResponseFisherCurvature`

**Deliverable:** Curvature of every \(\alpha\)-connection is a quadratic third-cumulant expression; fourth derivatives cancel.

Fix the convention

\[
R(u,v)w=
D_u\Gamma(v,w)-D_v\Gamma(u,w)
+\Gamma(u,\Gamma(v,w))-\Gamma(v,\Gamma(u,w)).
\]

Define this directly using `fderiv` on \(W\).

### Target statement

```lean
theorem alphaCurvature_eq :
  alphaCurvature α θ u v w =
    - ((1 - α ^ 2) / 4) •
      (mChristoffel θ u (mChristoffel θ v w) -
       mChristoffel θ v (mChristoffel θ u w))
```

Corollaries:

```lean
theorem eCurvature_eq_zero :
  alphaCurvature 1 θ u v w = 0

theorem mCurvature_eq_zero :
  alphaCurvature (-1) θ u v w = 0
```

and the covariant Levi-Civita formula:

```lean
theorem fisher_lcCurvature :
  fisher θ (alphaCurvature 0 θ u v w) z =
    (1 / 4 : ℝ) *
      (fisher θ (mChristoffel θ u w) (mChristoffel θ v z) -
       fisher θ (mChristoffel θ v w) (mChristoffel θ u z))
```

### Proof route

First prove the antisymmetrized derivative identity
\[
D_uC(v,w)-D_vC(u,w)
=-C(u,C(v,w))+C(v,C(u,w)).
\]

Differentiating \(A^{-1}T\) produces:

- the displayed quadratic terms from \(D(A^{-1})\);
- an \(A^{-1}D^3\mu\) term, which cancels by symmetry.

Then substitute \(\Gamma^{(\alpha)}=\frac{1-\alpha}{2}C\).

### Existing declarations to reuse

- D01–D02
- Smoothness of the model mean map
- Existing derivative-of-inverse machinery underlying response velocity
- Symmetry of higher derivatives

**Do not claim a universal sign for sectional curvature.** The quadratic formula does not supply one for a general exponential family.

---

## D04. `ResponseDensityTopology`

**Deliverable:** Put a representative-independent \(L^1\) topology on admissible data laws, and prove continuity of response and model section.

Let \(\mu_0=\nu.\mathrm{tilted}(0)\). Define

\[
p_g=\frac{e^g}{\int e^g\,d\mu_0}\in L^1(\mu_0).
\]

Use the **range of this map on existing admissible tilts**:

```lean
def DataLaw :=
  {p : Lp ℝ 1 μ₀ // p ∈ Set.range densityOf}
```

This avoids silently enlarging `bddSpace` to all essentially bounded measurable log-densities.

### Target statements

```lean
def lawResponse : DataLaw → W := ...

def modelLaw : W → DataLaw := ...

theorem lawResponse_densityOf :
  lawResponse (lawOf g) = responseOf g

theorem continuous_lawResponse :
  Continuous lawResponse

theorem continuous_modelLaw :
  Continuous modelLaw

theorem lawResponse_modelLaw :
  lawResponse (modelLaw θ) = θ
```

### Proof route

The mean-density map is bounded linear:
\[
\left\|\int S(p-q)\,d\mu_0\right\|
\leq \|S\|_\infty\|p-q\|_1.
\]

Compose with the inverse mean chart, using continuity on its actual mean domain. Prove continuity of `modelLaw` locally in \(\theta\), using bounded \(S\), uniform bounds for the exponential on parameter neighbourhoods, and continuity of normalization.

### Existing declarations to reuse

- `responseOf_eq_iff`
- `responseOf_eq_iff_tiltedMean_eq_meanMap`
- `responseOf_modelTilt`
- Existing local smoothness/continuity of the inverse mean chart

**Assumption check:** this route uses bounded \(S\). If boundedness is not already standing, state it explicitly; \(L^1\)-continuity of the mean fails in this form for unbounded statistics.

---

## D05. `ResponseFibreDeformation`

**Deliverable:** A continuous fibre-preserving strong deformation retraction onto the model laws.

Define, for \(t\in[0,1]\),

```lean
def responseDeform (t : Set.Icc (0 : ℝ) 1) (p : DataLaw) : DataLaw :=
  -- density (1 - t) • p + t • modelLaw (lawResponse p)
```

### Target statements

```lean
theorem continuous_responseDeform :
  Continuous
    (fun q : Set.Icc (0 : ℝ) 1 × DataLaw =>
      responseDeform q.1 q.2)

theorem responseDeform_zero :
  responseDeform 0 p = p

theorem responseDeform_one :
  responseDeform 1 p = modelLaw (lawResponse p)

theorem lawResponse_responseDeform :
  lawResponse (responseDeform t p) = lawResponse p

theorem responseDeform_modelLaw :
  responseDeform t (modelLaw θ) = modelLaw θ
```

Endpoint numerals above abbreviate the corresponding interval subtype elements.

### Proof route

The underlying density expression is continuous by normed-space algebra and D04. Membership in `DataLaw` follows from `mixTilt`; response preservation follows from its exact mean identity.

This separates topology from integration: prove the density equality once, then let continuity be linear algebra in \(L^1\).

### Existing declarations to reuse

- `integral_mixTilt`, plus the corresponding density/law equality
- `responseOf_mixTilt_of_eq`
- `responseOf_mix_model`
- `integral_mix_model`
- D04

---

## D06. `ResponseTopologicalQuotient`

**Deliverable:** The response quotient is homeomorphic to \(W\), every fibre is contractible, and the entire data-law space is homotopy equivalent to the model family.

Define:

```lean
def responseSetoid : Setoid DataLaw :=
  Setoid.ker lawResponse
```

### Target statements

```lean
theorem lawResponse_isQuotientMap :
  IsQuotientMap lawResponse

def responseQuotientHomeomorph :
  Quotient responseSetoid ≃ₜ W
```

For each \(\theta\), export an explicit continuous contraction

```lean
fibreContract θ :
  Set.Icc (0 : ℝ) 1 × {p : DataLaw // lawResponse p = θ} →
    {p : DataLaw // lawResponse p = θ}
```

with identity at zero, constant value `modelLaw θ` at one, and that point fixed throughout.

### Proof route

A continuous surjection with a continuous right inverse is a quotient map: if the inverse image of a set is open, pull it back along the section. Construct the quotient homeomorphism from this and the kernel equivalence relation. Restrict D05 to each fibre for its contraction.

### Existing declarations to reuse

- D04’s continuous section
- D05’s deformation identities
- `responseOf_eq_iff`

**Scope boundary:** contractible fibres and a fibrewise deformation retraction do not establish local triviality, a product decomposition, or a Serre fibration.

---

# Q3. Headline theorem and the continuing story

The geometric headline is:

\[
\boxed{\displaystyle
R^{(\alpha)}_\theta(u,v)w
=-\frac{1-\alpha^2}{4}
\bigl(C_\theta(u,C_\theta(v,w))
      -C_\theta(v,C_\theta(u,w))\bigr),
\qquad C_\theta=A_\theta^{-1}T_\theta .
}
\]

This is the next-order synthesis:

- **First order:** Fisher form and submersion identify observable directions.
- **Second order:** the Hessian and e-/m-acceleration gap separate data curvature from inverse-chart curvature.
- **Fibres:** fixed-moment convex sets become, now topologically, **contractible fibres of a quotient map**.
- **Downstairs geometry:** e- and m-connections are flat, but their Levi-Civita midpoint is generally curved; its curvature is precisely a commutator built from the third cumulant.

The “featureless law to actual data” story also becomes global: every admissible data law is continuously joined to its fitted model **without changing response**, while response journeys live in a space whose Fisher curvature is explicitly known.

## Ranked implementation queue

1. **`ResponseFisherJets`** — metric derivative and the \(A^{-1}T\) operator.
2. **`ResponseDualConnections`** — e-/m-/LC duality and mean-affine geodesics.
3. **`ResponseFisherCurvature`** — quadratic curvature and the \(\alpha\)-family.
4. **`ResponseDensityTopology`** — continuous response on normalized \(L^1\) densities.
5. **`ResponseFibreDeformation`** — fibre-preserving strong deformation retraction.
6. **`ResponseTopologicalQuotient`** — quotient homeomorphism and contractible fibres.