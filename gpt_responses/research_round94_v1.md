## Recommendation

**Do not begin by building a general Riemannian-distance API or proving a fibration theorem.** The next programme should make three things precise:

1. **What the curvature measures:** an exact third-cumulant inequality defect, with no universal sign.
2. **What the response forgets:** an exact relative-entropy decomposition along its fibres.
3. **When sampling loses the response:** quantitative noise bounds, and exact finite-sample probabilities of reaching a boundary face.

Close C6 as part of this programme. It is now a short, important bridge between the local submersion theory and the global fibre picture.

Two corrections should govern the programme:

- Proper faces of the moment polytope are **boundary strata, not walls inside \(W\)**. Their inverse images belong at infinity or in a completion. They do not, by themselves, partition \(W\) into several open chambers.
- \(\sqrt{d_{\rm eff}/n}\) is an **RMS size of linearised sampling noise**, not a confidence radius and not automatically an intrinsic Fisher–Rao radius.

Below, Lean-flavoured statements are proposed interfaces, not claims about exact current argument order. I suppress the standing boundedness, nondegeneracy, and measure hypotheses.

---

# Q1. Ranking E1–E7

### 1. E3 — Curvature as a third-cumulant inequality defect

Highest immediate depth × reachability. D01–D03 contain essentially the entire proof. The exact numerator is
\[
G_\theta(R^0(u,v)v,u)
=\frac14\left(
G_\theta(C(u,v),C(u,v))
-G_\theta(C(u,u),C(v,v))
\right).
\]
Thus nonpositive curvature is a **specific reverse Gram inequality**, not a general property of exponential families. The full categorical family has Fisher sectional curvature \(+1/4\), so any blanket “exponential families are nonpositively curved” claim is false. This module should also expose the lowered curvature tensor and its algebraic symmetries.

### 2. E7 — The response as an information projection, globally over the law space

My choice for E7 is the **relative-entropy Pythagorean theorem**, together with entropy dissipation along D05’s deformation. This makes the response more than a topological quotient: it is the unique information projection onto the model, and the discarded information is a nonnegative fibre coordinate. It also gives a clean interpretation of the featureless-to-data story without choosing a path. This is reachable directly from the exponential density formula and moment matching; no Riemannian infrastructure is needed.

### 3. E1 — The second jet of the fibre section

Finish it now. The corrected formula is the right one: the Hessian must be evaluated on the **actual vertical tangent vectors** \(J\xi\), not on the raw slice vectors \(K\xi\). This identifies the quadratic bending of a fixed-response fibre inside log-density space. Its distinction from D05’s convexity is illuminating: fibres are affine/convex in density coordinates, but generally curved in log-density coordinates.

### 4. E4 — Sampling resolution, with boundary and tangent statements separated

Very high value, but it must become two different statements. First, Fisher-normalised linear sampling noise gives an exact second-moment identity and a nonasymptotic probability bound. Second, for an exposed face \(F\), the empirical mean lies in \(F\) **iff every observation lies in \(F\)**, giving the exact probability \(P_D(F)^n\). The latter directly addresses existence of the finite empirical structural coordinate. A deterministic “ball meets wall iff RMS exceeds margin” statement is not justified.

### 5. E2 — Fisher path geometry: first variation and face separation, not path-order conjectures

The clean differential theorem is the **first variation of energy**, which avoids the zero-speed singularities of length and produces the already-defined LC equation. The clean boundary theorem is a sharp ambient Fisher–Rao lower bound in terms of face mass. I would not conjecture a universal ordering between e-geodesic and m-geodesic lengths. LC geodesics minimise only under additional local/global hypotheses. Also, the ambient statistical distance \(2\arccos\rho\leq\pi\) must not be silently identified with the intrinsic distance of a constrained exponential family.

### 6. E5 — Journey lifting and a possible global trivialisation

A section and a fibre-preserving strong deformation retraction **do not imply a Hurewicz fibration**. The promising additional structure is exponential tilting of *each* input law. For each \(p\), solve the tilted moment equation relative to \(p\), not relative to \(\nu\). This suggests a global homeomorphism
\[
\mathrm{DataLaw}\;\cong\;\mathrm{responseFibre}(0)\times W
\]
over \(W\). Such a result would supply a continuous lifting function immediately. I believe this route is plausible here, but its missing theorem is joint continuity of the relative moment inverse in the **\(L^1\) law variable**. Do not claim fibration before proving that theorem.

### 7. E6 — Normal-score interpretation of the defect jets

There is a clean identity, but it is not a curvature theorem. At the featureless model, for the path \(g_t=th\), put \(v=\mathrm{responseVel}(h)\), \(L_v=\langle v,S\rangle\), and let
\[
r=h-\mathbb E h+L_v-\mathbb E L_v.
\]
Then \(r\) is the residual score after Fisher-orthogonal projection onto the model scores. Under the defect conventions in the question,
\[
\Delta''(0)=\operatorname{Var}(r),\qquad
\Delta'''(0)=2\kappa(r,r,r)-3\kappa(r,r,L_v).
\]
The second identity is exactly your displayed cubic formula after substituting \(h=r-L_v\), modulo constants. Its mixed term contains fibre information absent from \(C\). Moreover, a third derivative with nonzero second derivative is parameterisation-dependent. It should not be presented as a quotient-curvature invariant.

---

# Q2. Six modules

## 1. `ResponseFisherCurvatureSign`

**Deliverable:** sectional curvature is exactly a third-cumulant inverse-Fisher inequality defect.

Write
\[
G_\theta^*(x,y):=-\langle x,A_\theta^{-1}y\rangle.
\]
This is the inverse Fisher form on Euclidean representatives of covectors, since the Fisher operator is \(-A_\theta\).

### Proposed statements

```lean
def inverseFisherInner (θ x y : W) : ℝ :=
  -dotJ x ((CDE θ).symm y)

theorem fisherInner_mChristoffel_mChristoffel
    (θ u v x y : W) :
    fisherInner S ν θ
        (mChristoffel θ u v) (mChristoffel θ x y)
      =
    inverseFisherInner θ
        (thirdOp θ u v) (thirdOp θ x y)
```

```lean
theorem fisherCurvature_numerator (θ u v : W) :
    fisherInner S ν θ (alphaCurvature 0 θ u v v) u
      =
    (1 / 4 : ℝ) *
      (fisherInner S ν θ
          (mChristoffel θ u v) (mChristoffel θ u v)
       -
       fisherInner S ν θ
          (mChristoffel θ u u) (mChristoffel θ v v))
```

Consequently, for linearly independent \(u,v\),
\[
K_\theta(u,v)=
\frac{
G_\theta^*(T(u,v),T(u,v))
-G_\theta^*(T(u,u),T(v,v))
}{
4\bigl(G_\theta(u,u)G_\theta(v,v)-G_\theta(u,v)^2\bigr)
}.
\]

Prove the sign interface without introducing division first:

```lean
theorem fisherCurvature_numerator_nonpos_iff (θ u v : W) :
    fisherInner S ν θ (alphaCurvature 0 θ u v v) u ≤ 0
      ↔
    inverseFisherInner θ (thirdOp θ u v) (thirdOp θ u v)
      ≤
    inverseFisherInner θ (thirdOp θ u u) (thirdOp θ v v)
```

### Sign meaning

Nonpositive sectional curvature at \(\theta\) means precisely that this inequality holds on every two-plane. Ordinary Cauchy–Schwarz does **not** establish it: its right-hand side can even be negative.

A useful further corollary is:

> If the endomorphisms \(C_\theta(u,-)\) commute for all \(u\), every \(\alpha\)-curvature vanishes at \(\theta\).

### Proof route and reuse

Expand `alphaCurvature_zero`; use the symmetry of the trilinear form
\[
(u,v,w)\longmapsto G_\theta(C(u,v),w)
\]
to move the outer \(C\) to the other argument. Then use \(C=A^{-1}T\).

Reuse:

- `alphaCurvature_eq`, `alphaCurvature_zero`
- `fisherInner_mChristoffel`
- `dotJ_thirdOp_symm₁₂/₂₃`
- Fisher positivity and symmetry
- `chartDeriv_mChristoffel`

No further differentiation is required.

---

## 2. `ResponseInformationPythagoras`

**Deliverable:** response is the unique KL projection, and the canonical fibre deformation dissipates precisely the discarded information.

Let `lawKL p q` mean \(D_{\mathrm{KL}}(p\,d\nu\|q\,d\nu)\). On `DataLaw`, bounded log-density representatives make this finite and well-defined.

### Proposed statements

```lean
theorem lawKL_response_pythagoras
    (p : DataLaw ν) (θ : W) :
    lawKL p (modelLaw θ)
      =
    lawKL p (modelLaw (lawResponse hS ν p))
      +
    lawKL (modelLaw (lawResponse hS ν p)) (modelLaw θ)
```

```lean
theorem lawResponse_unique_KL_minimizer
    (p : DataLaw ν) (θ : W) :
    lawKL p (modelLaw θ)
        = lawKL p (modelLaw (lawResponse hS ν p))
      ↔
    θ = lawResponse hS ν p
```

Define the vertical information:

```lean
def responseInformationDefect (p : DataLaw ν) : ℝ :=
  lawKL p (modelLaw (lawResponse hS ν p))
```

Then:

```lean
theorem responseInformationDefect_deform_le
    (t : unitInterval) (p : DataLaw ν) :
    responseInformationDefect (deform t p)
      ≤
    (1 - (t : ℝ)) * responseInformationDefect p
```

An important differential companion is
\[
D_\theta^2\,D_{\mathrm{KL}}(p\|P_\theta)[u,v]
=G_\theta(u,v).
\]
Thus the curvature programme’s metric is exactly the Hessian of the model-fitting objective. At \(\theta=\Phi(p)\), its first derivative vanishes.

### Proof route

The log ratio of two model densities is affine in \(S\):
\[
\log\frac{p_\phi}{p_\theta}
=\langle\theta-\phi,S\rangle+\psi(\theta)-\psi(\phi).
\]
Its expectation under \(p\) equals its expectation under \(P_{\Phi(p)}\). That proves Pythagoras.

For deformation, its response stays fixed, so convexity of \(x\mapsto x\log x\) gives
\[
D((1-t)p+tq\|q)\leq(1-t)D(p\|q).
\]

### Reuse

- Existing normalized-density and log-density identities
- Moment matching for `responseOf` / `lawResponse`
- `lawResponse_modelLaw`
- `lawResponse_deform`, `lawDens_mixTilt`
- `fisherInner` and the derivative of `chartV`

**Convention warning:** \(P_0\) is the normalized reference law. Call it “maximal entropy” only relative to the specified reference measure, or when the reference is genuinely uniform.

---

## 3. `ResponseFibreSecondJet`

**Deliverable:** the second jet of the local fixed-response graph is the negative response Hessian restricted to its true vertical tangent.

Use the affine augmented slice underlying the existing construction:
\[
\Psi(z,s)=\Phi(g+Kz+\operatorname{hor}_g s),\qquad
\sigma_0(z)=\sigma(z,\Phi(g)).
\]
Here \(D\Phi_g\operatorname{hor}_g=\mathrm{id}\), and set
\[
J\xi=K\xi-\operatorname{hor}_g(D\Phi_gK\xi).
\]

### Proposed statements

```lean
theorem hasFDerivAt_fibreSection_fixed_response_zero :
    HasFDerivAt σ₀ (-(DΦg.comp K)) 0
```

```lean
theorem responseDeriv_fibreTangent (ξ : Z) :
    DΦg (J ξ) = 0
```

```lean
theorem fibreSection_secondJet (ξ η : Z) :
    (fderiv ℝ (fun z => fderiv ℝ σ₀ z) 0 ξ) η
      =
    -((fderiv ℝ (fun x => fderiv ℝ Φ x) g (J ξ)) (J η))
```

For the actual fibre parametrisation
\[
F(z)=g+Kz+\operatorname{hor}_g\sigma_0(z),
\]
record the equivalent ambient statement:
\[
D^2F_0[\xi,\eta]
=-\operatorname{hor}_g\!\left(D^2\Phi_g[J\xi,J\eta]\right).
\]

### Proof route

Differentiate \(\Phi(F(z))=\Phi(g)\) twice:
\[
0=D^2\Phi_g[J\xi,J\eta]+D\Phi_g(D^2F_0[\xi,\eta]).
\]
The slice is affine in \((z,s)\), and the horizontal map is fixed at \(g\); hence the second term is exactly \(D^2\sigma_0[\xi,\eta]\).

### Reuse

- Smoothness and defining identities of `augSlice`, `fibreSection`
- The horizontal right-inverse theorem
- Existing response Fréchet derivative and Hessian
- `responseHess_eq_sub_mChristoffel`, for subsequent interpretations

Do not replace \(J\) by \(K\), and do not let `hor` vary with \(z\) in this calculation.

---

## 4. `ResponseFaceFisherSeparation`

**Deliverable:** face mass gives a sharp ambient statistical distance to a boundary face, hence a rigorous lower bound on intrinsic journey length.

For an exposed face \(F\), let
\[
a_F(\theta)=P_\theta(S\in F),\qquad
b_F(\theta)=2\arccos\sqrt{a_F(\theta)}.
\]
For nonempty proper faces of a full-support finite-range model, \(0<a_F(\theta)<1\).

Define the ambient spherical statistical distance on normalized nonnegative densities by
\[
d_{\rm sph}(p,q)=2\arccos\int\sqrt{pq}\,d\nu.
\]

### Proposed statements

```lean
theorem sphericalDist_ge_faceMargin
    (θ : W) (q : ProbabilityDensity ν)
    (hq : SupportedOnFeatureFace S q F) :
    2 * Real.arccos (Real.sqrt (faceMass θ F))
      ≤
    sphericalDist (modelDens θ) q
```

Equality is attained by the conditional density
\[
q_F=\frac{\mathbf 1_{\{S\in F\}}p_\theta}{a_F(\theta)}.
\]

```lean
theorem sphericalDist_conditionedOnFace (θ : W) :
    sphericalDist (modelDens θ) (conditionedOnFace θ F)
      =
    2 * Real.arccos (Real.sqrt (faceMass θ F))
```

The path bridge is:

```lean
theorem sphericalDist_le_fisherLength
    (γ : ℝ → W) (hγ : ContDiffOn ℝ 1 γ (Set.Icc 0 1)) :
    sphericalDist (modelDens (γ 0)) (modelDens (γ 1))
      ≤
    fisherLength γ
```

Then formulate a boundary-limit version: if model laws along a journey converge to a law supported on \(F\), every uniform upper bound on its truncated Fisher lengths is at least \(b_F(\theta_0)\).

### Proof route

For the face estimate, Cauchy–Schwarz on \(F\) gives
\[
\int\sqrt{p_\theta q}\,d\nu\leq\sqrt{a_F(\theta)}.
\]
For paths, the square-root-density map has speed
\[
\left\|\frac d{dt}\sqrt{p_{\theta(t)}}\right\|_{L^2}
=\frac12\sqrt{G_{\theta(t)}(\theta',\theta')}.
\]
Apply the sphere angle-versus-length inequality.

### Reuse

- Finite-range exposed-face and support declarations
- `meanExt` for identifying the limiting moment face
- `fisherNorm_rayPath`, `integrableOn_fisherNorm_rayPath`
- Existing affinity/angle lower bounds
- `dist_rayEndpoint_le_tail` for upper approximation certificates, **in the metric that declaration actually controls**

The intrinsic distance to the face is generally only **bounded below** by \(b_F\). Equality needs an additional argument; a two-level exposed statistic is a particularly clean sharp case.

---

## 5. `ResponseSamplingResolution`

**Deliverable:** separate an RMS noise theorem, a confidence theorem, and an exact boundary-hit theorem.

### A. Exact linearised noise identity

Let \(U_i\) be independent copies of the centered feature vector under the truth \(D\), expressed in \(W\), and let
\[
Z_n=A_\theta^{-1}\frac1n\sum_{i=1}^n U_i,
\qquad \theta=\Phi(D).
\]

```lean
theorem integral_fisherNorm_sq_linearResponseNoise
    (hn : 0 < n) :
    ∫ ω, (fisherNorm θ (Z n ω)) ^ 2 ∂μ
      =
    d_eff / (n : ℝ)
```

```lean
theorem prob_linearResponseNoise_ge
    (hn : 0 < n) (hr : 0 < r) :
    μ.real {ω | r ≤ fisherNorm θ (Z n ω)}
      ≤
    d_eff / ((n : ℝ) * r^2)
```

Hence \(n\geq d_{\rm eff}/(\varepsilon r^2)\) gives a \(1-\varepsilon\) **linearised** confidence ball.

### B. Exact affine-wall margin

For a mean-coordinate wall \(\langle a,m\rangle=b\), assume the truth is on the side with gap
\[
\delta=\langle a,m_\theta\rangle-b>0.
\]
Its corresponding affine hyperplane in linearised response space is
\[
G_\theta(a,z)=\delta,
\]
and its Fisher distance from \(0\) is exactly
\[
r_{\rm tan}=\frac{\delta}{\sqrt{G_\theta(a,a)}}.
\]

This follows from \(A_\theta Z_n=\bar S_n-m_\theta\) and
\[
\langle a,A_\theta z\rangle=-G_\theta(a,z).
\]

The probability of reaching the wrong side is therefore at most
\[
\frac{d_{\rm eff}}{n\,r_{\rm tan}^2}.
\]
A sharper directional bound uses
\(\operatorname{Var}_D\langle a,S\rangle/(n\delta^2)\).

For a finite collection of affine decision walls, the smallest tangent margin gives a single norm-based bound, without a union-bound factor. These are prescribed decision walls; do not invent them from the proper faces of the moment polytope.

### C. Exact finite-range boundary event

For \(n>0\) and an exposed face \(F\):

```lean
theorem empiricalMean_mem_face_iff
    (hn : 0 < n) :
    empiricalMean S samples ∈ F
      ↔
    ∀ i : Fin n, S (samples i) ∈ F
```

Under iid sampling:

```lean
theorem prob_empiricalMean_mem_face
    (hn : 0 < n) :
    sampleLaw.real {xs | empiricalMean S xs ∈ F}
      =
    (truth.real {x | S x ∈ F}) ^ n
```

Consequently, summing over facets bounds the probability that the empirical mean fails to lie in the relative interior—and therefore fails to have a finite structural coordinate.

### Proof route and reuse

- `FisherNormalisedSampling`
- `effDim_eq_sum_lawCov`, the existing \(d_{\rm eff}\) trace identity
- Independence: cross terms in the squared norm vanish
- Markov applied to the squared Fisher norm
- Finite-range supporting-hyperplane descriptions

For the face event, each supporting-functional gap is nonnegative. Their average is zero iff every gap is zero. Independence then gives the \(n\)-th power.

This last theorem concerns the **actual empirical moment**, not a delta-method approximation. The empirical law need not belong to `DataLaw`; keep that distinction explicit.

---

## 6. `ResponseFisherEnergyVariation`

**Deliverable:** the LC equation is exactly the Euler–Lagrange equation for Fisher energy.

Define
\[
E(\theta)=\frac12\int_0^1G_{\theta(t)}(\theta'(t),\theta'(t))\,dt.
\]
For a sufficiently smooth two-parameter family \(\Theta(s,t)\), put
\[
\theta(t)=\Theta(0,t),\quad
V=\partial_t\Theta(0,t),\quad
U=\partial_s\Theta(0,t).
\]

### Proposed statement

```lean
theorem hasDerivAt_fisherEnergy_variation
    (hΘ : SmoothVariationOnCompactRectangle Θ) :
    HasDerivAt
      (fun s => fisherEnergy (Θ s))
      (fisherInner S ν (θ 1) (U 1) (V 1)
       - fisherInner S ν (θ 0) (U 0) (V 0)
       - ∫ t in (0 : ℝ)..1,
           fisherInner S ν (θ t) (U t)
             (accel t
               + (1 / 2 : ℝ) • mChristoffel (θ t) (V t) (V t)))
      0
```

Here `SmoothVariationOnCompactRectangle` should be an explicit local regularity package, not an axiom; \(C^2\) on a neighbourhood of a compact rectangle is ample.

For fixed endpoints, deduce stationarity of every LC geodesic. Prove the converse using compactly supported variations if the requisite fundamental-lemma infrastructure is inexpensive.

### Proof route

Differentiate the energy integrand:
\[
\partial_s\frac12G(V,V)
=G(\partial_tU,V)+\frac12G(C(U,V),V).
\]
Integrate by parts and use total symmetry of the lowered \(C\). The surviving acceleration is
\[
\theta''+\frac12C(\theta',\theta').
\]

### Reuse

- `hasDerivAt_fisherInner_line_mChristoffel`
- `hasDerivAt_fisherInner_line_dual`
- `koszul_alphaChristoffel_zero`
- `alphaChristoffel` at \(0\)
- `hasDerivAt_deriv_chartV_path`

This is a better first variational target than length: no division by speed and no regular-curve hypothesis.

---

# Q3. Headline theorem and continuation of the story

The headline should be the global information decomposition:

\[
\boxed{
\underbrace{D_{\mathrm{KL}}(P_D\|P_0)}_{\text{total information relative to the featureless law}}
=
\underbrace{D_{\mathrm{KL}}(P_D\|P_{\Phi(D)})}_{\text{information invisible to the response}}
+
\underbrace{D_{\mathrm{KL}}(P_{\Phi(D)}\|P_0)}_{\text{information retained by the structural coordinate}} .
}
\]

This extends programme D in a concrete way:

- **First order:** the response is a submersion; model fitting has Fisher Hessian.
- **Second order:** the response Hessian separates forcing from the e/m connection gap; C6 identifies the bending of the fixed-response fibre.
- **Curvature:** the quotient’s sectional curvature is the inverse-Fisher inequality defect of third cumulants.
- **Fibres:** they are contractible fixed-moment sets, and the canonical contraction decreases their discarded information.
- **Journeys:** Fisher energy selects the LC equation; face mass supplies a rigorous cost of approaching a boundary stratum.
- **Sampling:** \(d_{\rm eff}/n\) controls linearised uncertainty, while \(P_D(F)^n\) gives the exact probability of landing on a particular boundary face.

The resolution story thereby becomes a pair of honest statements: **noise relative to a specified margin controls confidence**, and **finite-sample boundary loss has an exact combinatorial probability**. Neither needs an unjustified identification of RMS noise with intrinsic distance.

## Ranked list of six modules to formalise next

1. **`ResponseFisherCurvatureSign`** — curvature as the third-cumulant inequality defect.
2. **`ResponseInformationPythagoras`** — global information projection and entropy-dissipating fibre contraction.
3. **`ResponseFibreSecondJet`** — close C6 with the correctly verticalised Hessian.
4. **`ResponseFaceFisherSeparation`** — sharp ambient face margin and intrinsic journey lower bounds.
5. **`ResponseSamplingResolution`** — confidence bounds and exact empirical boundary-hit probabilities.
6. **`ResponseFisherEnergyVariation`** — Fisher energy’s first variation and the LC Euler–Lagrange equation.