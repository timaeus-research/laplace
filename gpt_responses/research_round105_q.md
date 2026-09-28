# Research round 105 — germbij response-map programme: N1–N4 landed; audit, N5/N6 feasibility, and the next programme

You are GPT-6 Astra, research advisor to a Lean 4 (Mathlib) formalisation of the note *germbij* (the response map `q ↦ Φ(q) ∈ W` of a bounded feature family `S : J → X → ℝ` over data laws `q ≪ ν`; `W = dirSpan` (`𝕍`); `P_θ = ν.tilted(−⟨θ,S⟩)` (`Pfam`); mean map `m`; inverse chart `θr`; Fisher form `G`; `regressionDir F θ = u_F`; `responseProjection hS ν M = R_M` the entropy projection; `dataBilin D = Σ_D`; `dataKer` its kernel `N`; `dataDualSing he = e*` the covariance dual of a displacement `e` annihilated by `N` (M6); `qStarVec M = (R_M{x})_x` on a finite configuration; `hull = conv S(X)`; `Ω = relint`; `regressor hS D hh` = the regression of a score `h` on `S` under `D`; `Refines S T ν`; `sampleResponse S Xs n ω = M̂_n`; `lawCov`; `dotJ`; `Bdd`). Everything below is sorry-free, warning-free Lean in laplace `Laplace/Multi/Response*` (≈95 modules).

The user's standing direction: *"make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to map the space of responses across the data manifold (ideally all the way from the featureless distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?"* plus the resolution story (truth shifts vs sampling shifts; chambers below the sampling scale are unresolvable). New mathematics, not packaging.

## What landed since round 104 (your programme N, ranks 1–4, in full)

* **N1 (three modules + capstone)** — `ResponseFaceSupportConstancy` (support constant on the relative interior of each face; one base law `ν_A` per open stratum), `ResponseFaceCalculus` (`momentBody ν_A = conv S(A) = carriedResponses S A`, `𝕍^{ν_A} = W_A = vectorSpan(S(A))`, relint(face) = `Ω^{ν_A}`; the FACEWISE DERIVATIVE `d/dt E_{R_{M'+te}}F|₀ = ⟨u_F^{A}(M'), e⟩` for `e ∈ W_A`), and the capstone `ResponseStratifiedTransport`: the tangential field `u_F(M) = u_F^{supp q*(M)}(M)` is defined on the whole closed polytope; every polytope point is a relative-interior point of its minimal face (`mem_intrinsicInterior_carriedResponses_supportSet`, via the supporting-functional criterion); a Lipschitz map composed with a differentiable path is differentiable wherever it is differentiable along the tangent line (`hasDerivAt_comp_of_lipschitzOnWith_line`); velocities are tangent to the current face wherever the support is locally constant; **`stratified_transport`: `E_{R_{M(1)}}F − E_{R_{M(0)}}F = ∫₀¹⟨u_F(M t), V t⟩dt`** for every `C¹` journey `M : [0,1] → conv S(X)` with bounded velocity `V` tangent to the current face off a countable set of times (FTC off a countable set, `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`), and the corollary for journeys with locally constant support.
* **N2 `ResponseHessianResidual`** — `r_F = F − E_θF − ⟨u_F(θ), S − m_θ⟩` (mean zero, orthogonal to every score); **`secondResponse F θ u v = E_θ[r_F ℓ_u ℓ_v]`** (the residual third moment); affine feature observables have zero response curvature; `d²/dt² E_{θ_t}F|₀ = E[r_F ℓ_V²]`, `V = A_{θ₀}⁻¹e`; the facewise second derivative on each open stratum. (Your `ℓ_e` normalisation differs from the seabed's `modelScore`: the seabed pairs with the velocity `V = A⁻¹e` of the response line; same content.)
* **N3 `ResponseFaceCarried` + `ResponseAsymptoticLinearity`** — `D{x} = 0` off `A = supp q*(m_D)` (Csiszár via the seabed's `support_absorb`), face restriction on the WHOLE face polytope (`supp q*(N) ⊆ A ⇒ Π^{ν_A}(N) = Π^ν(N)`); quadratic remainder on the face polytope `|f_F(N) − f_F(m_D) − ⟨u_F, N − m_D⟩| ≤ C‖N − m_D‖²` (cubic expansion of the face law near `m_D`, global Lipschitz far); face influence `ψ_F(x) = ⟨u_F, S(x) − m_D⟩`; **`Ψ̂_F − Ψ_F(D) = (1/n)Σψ_F(Xᵢ) + ℛ_n`, `E ℛ_n² ≤ 3C²|J|⁴(2B)⁴/n²`** (samples lie in `A` a.s.); bias `|EΨ̂ − Ψ| ≤ C|J|²(2B)²/n`; **sharp risk `|E(Ψ̂ − Ψ)² − Var_D ψ_F/n| ≤ (Var_D ψ_F + 2C₄)/n^{3/2}`** (pointwise `(L+R)² ≶ (1 ± n^{-1/2})L² ± (1+√n)R²`; no CLT). Every data law, boundary means included. NOT done: the refined bias `(1/2n)tr(Cov_D(S) D²_A f_F) + O(n^{-3/2})` in unlocalised form (the localised form exists in the seabed as `iid_obsBias_hessian`).
* **N4 `ResponseJointResolution`** — `|E[δᵢδⱼ] − V_ij/n| ≤ ½(V_ii + V_jj + 2C₄ᵢ + 2C₄ⱼ)/n^{3/2}`; null directions: `Var_D(Σwᵢψᵢ) = 0 ⇒ E(Σwᵢδᵢ)² ≤ |ι|Σwᵢ²C₄ᵢ/n²`; **resolution ellipsoid**: for every nonnegative quadratic form `A` on the observables, `P(n δᵀAδ ≥ r²) ≤ (tr(AV) + Σ_{ij}|A_ij|c_ij/√n)/r²` (Markov). Your `(V + λI)⁻¹` instance is prose.

All sorry-free, warning-free, on `main` (laplace ≈ 105 `Response*` modules).

## Key statements (verbatim Lean, docstrings included; proofs elided)

### `ResponseFaceSupportConstancy.lean`
# The support of the response is constant on the relative interior of a face

The entropy response `R_M` charges exactly the atoms whose feature vectors lie on the minimal face
of the polytope containing `M` (Csiszár's support theorem, `FiniteMinimalFace`). Along the polytope
the support can only shrink towards the boundary: the support of every point of the face of `M`
is contained in the support of `M` (`supportSet_subset_of_mem_carriedResponses`), while the
supports of the endpoints of a segment through `M` are contained in the support of `M`
(`supportSet_subset_of_mem_openSegment`). Since every point of the relative interior of a face is
the midpoint-like interior point of a segment through any other point of the face
(`exists_mem_openSegment_of_mem_intrinsicInterior`), the support is **constant on the relative
interior of each face** (`supportSet_eq_of_mem_intrinsicInterior`). Combined with the exact face
restriction of `ResponseFaceRestriction`, the entropy response is, on the whole relative interior of
the face of `M`, the entropy response of the fixed conditioned law `ν_A`, `A = supp q*(M)`
(`responseProjection_eq_faceMeasure_of_mem_intrinsicInterior`): each open face stratum is one
interior problem for one base law, which is what lets the interior response calculus run facewise.

```lean
theorem exists_mem_openSegment_of_mem_intrinsicInterior {K : Set (J → ℝ)} {x y : J → ℝ}
    (hx : x ∈ intrinsicInterior ℝ K) (hy : y ∈ K) : ∃ z ∈ K, x ∈ openSegment ℝ y z

theorem convex_carriedResponses (A : Set X) : Convex ℝ (carriedResponses S A)

theorem supportSet_subset_of_mem_openSegment {M M' z : J → ℝ} (hM' : M' ∈ hull) (hz : z ∈ hull)
    (hseg : M ∈ openSegment ℝ M' z) : supportSet hS ν M' ⊆ supportSet hS ν M

theorem supportSet_subset_of_mem_carriedResponses {M M' : J → ℝ} (hM : M ∈ hull)
    (hM' : M' ∈ carriedResponses S (supportSet hS ν M)) :
    supportSet hS ν M' ⊆ supportSet hS ν M

theorem supportSet_eq_of_mem_intrinsicInterior {M M' : J → ℝ} (hM : M ∈ hull)
    (hM' : M' ∈ intrinsicInterior ℝ (carriedResponses S (supportSet hS ν M))) :
    supportSet hS ν M' = supportSet hS ν M

theorem responseProjection_eq_faceMeasure_of_mem_intrinsicInterior {M M' : J → ℝ} (hM : M ∈ hull)
    (hM' : M' ∈ intrinsicInterior ℝ (carriedResponses S (supportSet hS ν M))) :
    responseProjection hS (faceMeasure ν (supportSet hS ν M)) M' = responseProjection hS ν M'

```

### `ResponseFaceCalculus.lean`
# The facewise interior calculus of the response map

The conditioned law `ν_A` of a set of atoms `A` sees exactly the feature vectors of `A`
(`essRange_faceMeasure_eq_image`), so its moment body is the face polytope `conv S(A)`, which is the
set of responses carried by `A` (`carriedResponses_eq_convexHull_image`,
`momentBody_faceMeasure_eq_carriedResponses`); in particular the direction space of `ν_A` is the
direction space `W_A = span (S(A) − S(A))` of the face (`dirSpan_faceMeasure_eq_vectorSpan_image`).
Hence the relative interior of the face of `M` is the interior response domain `Ω^{ν_A}` of the base
law `ν_A`, `A = supp q*(M)`, on which the whole interior response calculus is available; combined
with the constancy of the support on the relative interior of the face
(`ResponseFaceSupportConstancy`), this gives the **facewise derivative of the response map**
(`hasDerivAt_responseObs_face`): for `M'` in the relative interior of the face of `M` and a face
direction `e ∈ W_A`,
`d/dt E_{R_{M' + t e}} F |_{t=0} = ⟨u_F^{A}(M'), e⟩`,
where `u_F^{A}(M')` is the regression direction of `F` relative to the conditioned law `ν_A` at the
chart point of `M'`. Every open face stratum of the polytope therefore carries its own smooth
response calculus, with the face law as base law and the face directions as tangent directions.

```lean
theorem faceMeasure_singleton (A : Set X) (x : X) :
    faceMeasure ν A {x} = if x ∈ A then (ν A)⁻¹ * ν {x} else 0

theorem faceMeasure_compl_self (A : Set X) : faceMeasure ν A Aᶜ = 0

theorem essRange_faceMeasure_eq_image (A : Set X) :
    essRange (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S = statPoint S '' A

theorem carriedResponses_eq_convexHull_image (A : Set X) :
    carriedResponses S A = convexHull ℝ (statPoint S '' A)

theorem momentBody_faceMeasure_eq_carriedResponses (A : Set X) :
    momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S = carriedResponses S A

theorem dirSpan_faceMeasure_eq_vectorSpan_image (A : Set X) :
    dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S = vectorSpan ℝ (statPoint S '' A)

theorem intrinsicInterior_momentBody_faceMeasure (A : Set X) :
    intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) =
      intrinsicInterior ℝ (carriedResponses S A)

theorem measure_supportSet_ne_zero {M : J → ℝ} (hM : M ∈ hull) : ν (supportSet hS ν M) ≠ 0

theorem eventuallyEq_responseObs_face {A : Set X} [IsProbabilityMeasure (faceMeasure ν A)]
    {M M' : J → ℝ} (hM : M ∈ hull) (hA : A = supportSet hS ν M)
    (hM' : M' ∈ intrinsicInterior ℝ (carriedResponses S A)) (F : X → ℝ)
    (e : dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) :
    (fun t : ℝ ↦ ∫ x, F x ∂responseProjection hS ν (M' + t • (e : J → ℝ))) =ᶠ[𝓝 0]
      lineObservable hS (faceMeasure ν A) F
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos (faceMeasure ν A)) hS M') e

theorem hasDerivAt_responseObs_face {A : Set X} [IsProbabilityMeasure (faceMeasure ν A)]
    {M M' : J → ℝ} (hM : M ∈ hull) (hA : A = supportSet hS ν M)
    (hM' : M' ∈ intrinsicInterior ℝ (carriedResponses S A)) {F : X → ℝ} (hF : Bdd F)
    (e : dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, F x ∂responseProjection hS ν (M' + t • (e : J → ℝ)))
      (dotJ (regressionDir hS (faceMeasure ν A) F
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos (faceMeasure ν A)) hS M') : J → ℝ) (e : J → ℝ)) 0

```

### `ResponseStratifiedTransport.lean`
# Stratified transport of posterior expectations across the moment polytope

The **tangential response field** `u_F(M) := u_F^{A}(M)`, `A = supp q*(M)`, is the regression
direction of the observable `F` relative to the conditioned law `ν_A` at the chart point of `M`
(`tangentField`): a vector of the direction space `W_A` of the minimal face of `M`, defined at every
point of the closed polytope. Every point of the polytope lies in the relative interior of its
minimal face (`mem_intrinsicInterior_carriedResponses_supportSet`), so the facewise interior
calculus applies at every point, and the global Lipschitz bound turns the facewise line derivative
into a derivative along every differentiable path whose velocity is tangent to the current face
(`hasDerivAt_responseObs_path`):
`d/ds E_{R_{M(s)}}[F] = ⟨u_F(M(s)), Ṁ(s)⟩`.
Velocities are automatically tangent wherever the support is locally constant
(`hasDerivAt_mem_vectorSpan_of_supportSet_eventually_eq`). Integrating along a `C¹` journey
`M : [0,1] → conv S(X)` whose velocity is tangent off a countable set of times — for instance a
journey with finitely many face crossings — gives the **stratified transport theorem**
(`stratified_transport`, `stratified_transport_of_locally_constant_support`):
`E_{R_{M(1)}}[F] − E_{R_{M(0)}}[F] = ∫₀¹ ⟨u_F(M(t)), Ṁ(t)⟩ dt`,
the change of a posterior expectation along any journey through the data manifold, from any
starting law to any ending law, is the line integral of the tangential response field, which
switches base law and tangent space at each face crossing.

```lean
theorem hasDerivAt_comp_of_lipschitzOnWith_line {g : E → ℝ} {K : Set E} {C : NNReal}
    (hg : LipschitzOnWith C g K) {M : ℝ → E} {v : E} {t : ℝ} (hM : HasDerivAt M v t)
    (hK : ∀ᶠ s in 𝓝 t, M s ∈ K) (hline : ∀ᶠ s in 𝓝 t, M t + (s - t) • v ∈ K) {d : ℝ}
    (hd : HasDerivAt (fun r : ℝ ↦ g (M t + r • v)) d 0) : HasDerivAt (fun s ↦ g (M s)) d t

noncomputable def faceField (A : Set X) (F : X → ℝ) (M : J → ℝ) : J → ℝ

theorem faceField_eq (A : Set X) [h : IsProbabilityMeasure (faceMeasure ν A)] (F : X → ℝ)
    (M : J → ℝ) :
    faceField hS ν A F M = (regressionDir hS (faceMeasure ν A) F
      (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos (faceMeasure ν A)) hS M) : J → ℝ)

noncomputable def tangentField (F : X → ℝ) (M : J → ℝ) : J → ℝ

theorem dotJ_sum_smul (e : J → ℝ) (p : X → ℝ) (f : X → J → ℝ) :
    dotJ e (∑ x, p x • f x) = ∑ x, p x * dotJ e (f x)

theorem mem_intrinsicInterior_carriedResponses_supportSet {M : J → ℝ} (hM : M ∈ hull) :
    M ∈ intrinsicInterior ℝ (carriedResponses S (supportSet hS ν M))

theorem vectorSpan_carriedResponses (A : Set X) :
    vectorSpan ℝ (carriedResponses S A) = vectorSpan ℝ (statPoint S '' A)

theorem hasDerivAt_mem_vectorSpan_of_supportSet_eventually_eq {M : ℝ → J → ℝ} {v : J → ℝ} {t : ℝ}
    (hM : HasDerivAt M v t) (hhull : ∀ᶠ s in 𝓝 t, M s ∈ hull)
    (hconst : ∀ᶠ s in 𝓝 t, supportSet hS ν (M s) = supportSet hS ν (M t)) :
    v ∈ vectorSpan ℝ (statPoint S '' supportSet hS ν (M t))

theorem hasDerivAt_responseObs_path {F : X → ℝ} (hF : Bdd F) {M : ℝ → J → ℝ} {v : J → ℝ}
    {t : ℝ} (hM : HasDerivAt M v t) (hhull : ∀ᶠ s in 𝓝 t, M s ∈ hull)
    (hv : v ∈ vectorSpan ℝ (statPoint S '' supportSet hS ν (M t))) :
    HasDerivAt (fun s ↦ ∫ x, F x ∂responseProjection hS ν (M s))
      (dotJ (tangentField hS ν F (M t)) v) t

theorem stratified_transport {F : X → ℝ} (hF : Bdd F) {M V : ℝ → J → ℝ} {B : ℝ}
    (hhull : ∀ t ∈ Icc (0 : ℝ) 1, M t ∈ hull) (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt M (V t) t)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖V t‖ ≤ B) {s : Set ℝ} (hs : s.Countable)
    (htan : ∀ t ∈ Ioo (0 : ℝ) 1 \ s,
      V t ∈ vectorSpan ℝ (statPoint S '' supportSet hS ν (M t))) :
    (∫ x, F x ∂responseProjection hS ν (M 1)) - ∫ x, F x ∂responseProjection hS ν (M 0) =
      ∫ t in (0 : ℝ)..1, dotJ (tangentField hS ν F (M t)) (V t)

theorem stratified_transport_of_locally_constant_support {F : X → ℝ} (hF : Bdd F)
    {M V : ℝ → J → ℝ} {B : ℝ} (hhull : ∀ t ∈ Icc (0 : ℝ) 1, M t ∈ hull)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt M (V t) t) (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖V t‖ ≤ B)
    {s : Set ℝ} (hs : s.Countable)
    (hconst : ∀ t ∈ Ioo (0 : ℝ) 1 \ s, ∀ᶠ u in 𝓝 t, supportSet hS ν (M u) = supportSet hS ν (M t)) :
    (∫ x, F x ∂responseProjection hS ν (M 1)) - ∫ x, F x ∂responseProjection hS ν (M 0) =
      ∫ t in (0 : ℝ)..1, dotJ (tangentField hS ν F (M t)) (V t)

```

### `ResponseHessianResidual.lean`
# The response Hessian is a residual third moment

The first response of an observable `F` along a mean displacement is its regression on the
features, `⟨u_F, e⟩`. The second response is the interaction of two scores with the part of the
observable that the regression does **not** explain: with the centred regression residual
`r_F = F − E_θF − ⟨u_F(θ), S − m_θ⟩` (`regResidual`, mean zero and orthogonal to every score,
`integral_regResidual`, `integral_regResidual_mul_modelScore`), the second response of
`ResponseObservableHessian` is
`secondResponse F θ u v = E_θ[r_F · ℓ_u ℓ_v]` (`secondResponse_eq_integral_regResidual`),
the third moment of the residual against the centred scores `ℓ_u = ⟨u, S − m_θ⟩`. In particular
affine feature observables `⟨a, S⟩ + c` have zero response curvature
(`secondResponse_dirLoss_add_const`), the second derivative of `t ↦ E_{θ_t}F` along a response line
at `t = 0` is `E_{θ₀}[r_F ℓ_V²]` with `V = A_{θ₀}⁻¹ e` the velocity of the line
(`hasDerivAt_deriv_lineObservable_zero_residual`), and the same holds facewise on every open face
stratum with the conditioned law as base law (`hasDerivAt_deriv_responseObs_face`).

```lean
noncomputable def regResidual (F : X → ℝ) (θ : 𝕍) : X → ℝ

theorem bdd_regResidual {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) : Bdd (regResidual hS ν F θ)

theorem integral_regResidual {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) :
    ∫ x, regResidual hS ν F θ x ∂Pfam (θ : J → ℝ) = 0

theorem integral_regResidual_mul_modelScore {F : X → ℝ} (hF : Bdd F) (θ v : 𝕍) :
    ∫ x, regResidual hS ν F θ x * f θ v x ∂Pfam (θ : J → ℝ) = 0

theorem secondResponse_eq_integral_regResidual {F : X → ℝ} (hF : Bdd F) (θ u v : 𝕍) :
    secondResponse hS ν F θ u v =
      ∫ x, regResidual hS ν F θ x * (f θ u x * f θ v x) ∂Pfam (θ : J → ℝ)

theorem secondResponse_dirLoss_add_const (a : 𝕍) (c : ℝ) (θ u v : 𝕍) :
    secondResponse hS ν (fun x ↦ dirLoss S (a : J → ℝ) x + c) θ u v = 0

theorem deriv_lineObservable_eventuallyEq {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) :
    deriv (lineObservable hS ν F θ₀ e) =ᶠ[𝓝 0] fun s ↦
      -lawCov (Pfam (responseLine hS ν θ₀ e s : J → ℝ)) F
        (dirLoss S (responseLineVel hS ν θ₀ e s : J → ℝ))

theorem hasDerivAt_deriv_lineObservable_zero_residual {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) :
    HasDerivAt (deriv (lineObservable hS ν F θ₀ e))
      (∫ x, regResidual hS ν F θ₀ x *
        (f θ₀ ((CDE θ₀).symm e) x * f θ₀ ((CDE θ₀).symm e) x) ∂Pfam (θ₀ : J → ℝ)) 0

theorem hasDerivAt_deriv_responseObs_face {A : Set X} [IsProbabilityMeasure (faceMeasure ν A)]
    {M M' : J → ℝ} (hM : M ∈ hull) (hA : A = supportSet hS ν M)
    (hM' : M' ∈ intrinsicInterior ℝ (carriedResponses S A)) {F : X → ℝ} (hF : Bdd F)
    (e : dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) :
    HasDerivAt (deriv (fun t : ℝ ↦ ∫ x, F x ∂responseProjection hS ν (M' + t • (e : J → ℝ))))
      (∫ x, regResidual hS (faceMeasure ν A) F
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos (faceMeasure ν A)) hS M') x *
        (modelScore S (faceMeasure ν A)
          (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS M')
          ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS
            (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
              (one_integral_pos (faceMeasure ν A)) hS M')).symm e) x *
         modelScore S (faceMeasure ν A)
          (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS M')
          ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS
            (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
              (one_integral_pos (faceMeasure ν A)) hS M')).symm e) x)
        ∂familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          ((responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS M' : J → ℝ))) 0

```

### `ResponseFaceCarried.lean`
# Data laws are carried by the minimal face of their mean

Csiszár's support theorem says that the support of the entropy response `q*(M)` is the largest
support among all probability vectors with mean `M`. Consequently **every data law `D` is carried by
the atoms `A = supp q*(m_D)` of the minimal face of its mean**
(`measure_singleton_eq_zero_of_notMem_supportSet`, `measure_compl_supportSet_dataMean`): a law
whose mean lies on a face of the polytope never charges an atom outside that face. Samples from `D`
therefore lie in `A`, and every empirical mean lies in the face polytope `conv S(A)`.

The exact face restriction of `ResponseFaceRestriction` extends from the point `M` to the whole
face polytope: for every mean `N` of the face `conv S(A)`, `A = supp q*(M)`, the entropy response
relative to the conditioned law `ν_A` is the entropy response relative to `ν`
(`responseProjection_faceMeasure_of_supportSet_subset`,
`responseProjection_faceMeasure_of_mem_carriedResponses`). Together: the statistics of the plug-in
estimator at any data law are the statistics of the plug-in estimator of the face law `ν_A`, for
which the data mean is an interior point.

```lean
theorem responseProjection_faceMeasure_of_supportSet_subset {N : J → ℝ} (hN : N ∈ hull)
    {A : Set X} (hsub : supportSet hS ν N ⊆ A) :
    responseProjection hS (faceMeasure ν A) N = responseProjection hS ν N

theorem responseProjection_faceMeasure_of_mem_carriedResponses {M N : J → ℝ} (hM : M ∈ hull)
    (hN : N ∈ carriedResponses S (supportSet hS ν M)) :
    responseProjection hS (faceMeasure ν (supportSet hS ν M)) N = responseProjection hS ν N

theorem atomVec_mem_stdSimplex : (fun x ↦ D.real {x}) ∈ stdSimplex ℝ X

theorem dataMean_eq_vecMoment_atomVec : mD = vecMoment S (fun x ↦ D.real {x})

theorem measure_singleton_eq_zero_of_notMem_supportSet {x : X} (hx : x ∉ supportSet hS ν mD) :
    D {x} = 0

theorem measure_compl_supportSet_dataMean : D (supportSet hS ν mD)ᶜ = 0

theorem absolutelyContinuous_faceMeasure_dataMean : D ≪ faceMeasure ν (supportSet hS ν mD)

```

### `ResponseAsymptoticLinearity.lean`
# Face-adaptive asymptotic linearity of the plug-in estimator

Let `D` be any data law on the finite configuration, `m_D` its mean, `A = supp q*(m_D)` the atoms
of the minimal face of `m_D`, and `u_F = u_F^{A}(m_D)` the tangential response field of a bounded
observable `F` at `m_D`. The **face influence function** of `F` is
`ψ_F(x) = ⟨u_F, S(x) − m_D⟩` (`faceInfluence`).

* **The quadratic remainder on the face polytope** (`exists_face_quadratic_remainder`): for every
  mean `N` of the face polytope `conv S(A)`,
  `|E_{R_N}F − E_{R_{m_D}}F − ⟨u_F, N − m_D⟩| ≤ C ‖N − m_D‖²`,
  from the cubic expansion of the interior calculus of the face law `ν_A` near `m_D` and the global
  Lipschitz bound far from it.
* **Asymptotic linearity** (`empiricalObs_sub_eq_sum_faceInfluence_add`,
  `integral_sq_linearityRemainder_le`): since the samples lie in `A` almost surely, the plug-in
  estimator `Ψ̂_F = E_{R_{M̂_n}}F` of `n` i.i.d. samples satisfies
  `Ψ̂_F − Ψ_F(D) = (1/n) ∑ᵢ ψ_F(Xᵢ) + ℛ_n`, `E_D ℛ_n² ≤ 3 C² |J|⁴ (2B)⁴ / n²`.
* **First-order unbiasedness and the sharp risk** (`abs_integral_empiricalObs_sub_le`,
  `abs_integral_sq_empiricalObs_sub_sub_le`): `|E_D Ψ̂_F − Ψ_F(D)| ≤ C |J|² (2B)² / n` and
  `|E_D (Ψ̂_F − Ψ_F(D))² − Var_D(ψ_F)/n| ≤ (Var_D ψ_F + 2 C₄) / n^{3/2}`.

The theorem holds at **every** data law, boundary means included: the estimator only explores the
face on which the data mean is relatively interior, and its statistics are those of the interior
problem of the face law. No central limit theorem enters; the constants depend on the face.

```lean
theorem dotJ_finset_sum {ι : Type*} (e : J → ℝ) (s : Finset ι) (g : ι → J → ℝ) :
    dotJ e (∑ i ∈ s, g i) = ∑ i ∈ s, dotJ e (g i)

theorem dotJ_sub_right (e a b : J → ℝ) : dotJ e (a - b) = dotJ e a - dotJ e b

theorem exists_face_quadratic_remainder {F : X → ℝ} (hF : Bdd F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2

noncomputable def faceInfluence (F : X → ℝ) (x : X) : ℝ

noncomputable def linearityRemainder (F : X → ℝ) (n : ℕ) (ω : Ω) : ℝ

theorem ae_sampleResponse_mem_carriedResponses {n : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂P, sampleResponse S Xs n ω ∈ carriedResponses S (supportSet hS ν mD)

theorem dotJ_tangentField_sampleResponse_sub (F : X → ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    dotJ (tangentField hS ν F mD) ((raw n) ω) =
      (∑ i ∈ Finset.range n, faceInfluence hS ν D F (Xs i ω)) / n

theorem empiricalObs_sub_eq_sum_faceInfluence_add (F : X → ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD =
      (∑ i ∈ Finset.range n, faceInfluence hS ν D F (Xs i ω)) / n +
        linearityRemainder hS ν D Xs F n ω

theorem ae_abs_linearityRemainder_le {F : X → ℝ} {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂P, |linearityRemainder hS ν D Xs F n ω| ≤ C * ‖(raw n) ω‖ ^ 2

theorem measurable_linearityRemainder (F : X → ℝ) {n : ℕ} (hn : 0 < n) :
    Measurable (linearityRemainder hS ν D Xs F n)

theorem integral_sq_linearityRemainder_le {F : X → ℝ} {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    ∫ ω, linearityRemainder hS ν D Xs F n ω ^ 2 ∂P ≤
      C ^ 2 * (3 * Fintype.card J ^ 4 * (2 * B) ^ 4 / n ^ 2)

theorem integral_dotJ_tangentField_sampleResponse_sub (F : X → ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ ω, dotJ (tangentField hS ν F mD) ((raw n) ω) ∂P = 0

theorem integrable_dotJ_tangentField_sampleResponse_sub (F : X → ℝ) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ dotJ (tangentField hS ν F mD) ((raw n) ω)) P

theorem integrable_linearityRemainder {F : X → ℝ} {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    Integrable (linearityRemainder hS ν D Xs F n) P

theorem abs_integral_empiricalObs_sub_le {F : X → ℝ} (hF : Bdd F) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    |(∫ ω, empiricalObs hS ν Xs F n ω ∂P) - ∫ x, F x ∂responseProjection hS ν mD| ≤
      C * (Fintype.card J ^ 2 * (2 * B) ^ 2 / n)

theorem integrable_sq_linearityRemainder {F : X → ℝ} {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ linearityRemainder hS ν D Xs F n ω ^ 2) P

theorem abs_integral_sq_empiricalObs_sub_sub_le {F : X → ℝ} (hF : Bdd F) {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    |(∫ ω, (empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD) ^ 2 ∂P) -
        lawCov D (dirLoss S (tangentField hS ν F mD)) (dirLoss S (tangentField hS ν F mD)) / n| ≤
      (lawCov D (dirLoss S (tangentField hS ν F mD)) (dirLoss S (tangentField hS ν F mD)) +
        2 * (C ^ 2 * (3 * Fintype.card J ^ 4 * (2 * B) ^ 4))) / (n * Real.sqrt n)

```

### `ResponseJointResolution.lean`
# Joint resolution of finitely many posterior expectations

For finitely many bounded observables `F i` with plug-in errors `δ_n(i) = Ψ̂_{F i} − Ψ_{F i}(D)`
(`jointError`) and face influence functions `ψ_i`, the asymptotic linearity of
`ResponseAsymptoticLinearity` gives the joint second moments:

* **the sampling covariance matrix** (`abs_integral_jointError_mul_sub_le`):
  `|E_D[δ_n(i) δ_n(j)] − Cov_D(ψ_i, ψ_j)/n| ≤ ½ (V_ii + V_jj + 2 C₄ᵢ + 2 C₄ⱼ) / n^{3/2}`;
* **null directions carry no first-order fluctuation** (`integral_sq_sum_smul_jointError_le`):
  for a weight vector `w` with `Var_D(∑ wᵢ ψᵢ) = 0`, `E_D (∑ wᵢ δ_n(i))² ≤ (∑|wᵢ|)(∑|wᵢ| C₄ᵢ)/n²` —
  the linear term vanishes almost surely and only the quadratic response error remains;
* **the resolution ellipsoid** (`measureReal_quadForm_jointError_ge_le`): for every nonnegative
  quadratic form `A` on the observables and `r > 0`,
  `P_D(n δ_nᵀ A δ_n ≥ r²) ≤ (tr(A V) + ∑_{ij} |A_ij| c_ij / √n) / r²`, the Markov bound of the
  joint second moments; with `A = (V + λI)⁻¹` this is the oracle coverage of the sampling
  ellipsoid of the observables.

```lean
theorem abs_integral_mul_le_of_sq {f g : Ω → ℝ} (hf : Integrable (fun ω ↦ f ω ^ 2) P)
    (hg : Integrable (fun ω ↦ g ω ^ 2) P) (hfg : Integrable (fun ω ↦ f ω * g ω) P) {ε : ℝ}
    (hε : 0 < ε) :
    |∫ ω, f ω * g ω ∂P| ≤ (1 / 2 : ℝ) * (ε * ∫ ω, f ω ^ 2 ∂P + (1 / ε) * ∫ ω, g ω ^ 2 ∂P)

def QuadRem (F : X → ℝ) (C : ℝ) : Prop

noncomputable def jointError (n : ℕ) (ω : Ω) (i : ι) : ℝ

noncomputable def linTerm (n : ℕ) (ω : Ω) (i : ι) : ℝ

noncomputable def fourthConst (C : ℝ) : ℝ := C ^ 2 * (3 * Fintype.card J ^ 4 * (2 * B) ^ 4)

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] hS hν hXm hid hlaw hind hB in
theorem fourthConst_nonneg (C : ℝ) : 0 ≤ fourthConst (J := J) (B := B) C

theorem jointError_eq (i : ι) {n : ℕ} (ω : Ω) :
    jointError hS ν D Xs F n ω i =
      linTerm hS ν D Xs F n ω i + linearityRemainder hS ν D Xs (F i) n ω

theorem integral_linTerm_mul_linTerm (i j : ι) {n : ℕ} (hn : 0 < n) :
    ∫ ω, linTerm hS ν D Xs F n ω i * linTerm hS ν D Xs F n ω j ∂P =
      lawCov D (dirLoss S (tangentField hS ν (F i) mD)) (dirLoss S (tangentField hS ν (F j) mD)) /
        n

noncomputable def influenceCov (i j : ι) : ℝ

theorem bdd_linTerm (i : ι) {n : ℕ} (hn : 0 < n) : Bdd fun ω ↦ linTerm hS ν D Xs F n ω i

theorem bdd_jointError (i : ι) {n : ℕ} (hn : 0 < n) :
    Bdd fun ω ↦ jointError hS ν D Xs F n ω i

theorem integrable_sq_remainder (i : ι) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ linearityRemainder hS ν D Xs (F i) n ω ^ 2) P

theorem integrable_remainder (i : ι) {n : ℕ} (hn : 0 < n) :
    Integrable (linearityRemainder hS ν D Xs (F i) n) P

theorem integrable_remainder_mul_remainder (i j : ι) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ linearityRemainder hS ν D Xs (F i) n ω *
      linearityRemainder hS ν D Xs (F j) n ω) P

theorem abs_integral_jointError_mul_sub_le (i j : ι) {n : ℕ} (hn : 0 < n) :
    |(∫ ω, jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j ∂P) -
        influenceCov hS ν D F i j / n| ≤
      (1 / 2 : ℝ) * (influenceCov hS ν D F i i + influenceCov hS ν D F j j +
        2 * fourthConst (J := J) (B := B) (C i) + 2 * fourthConst (J := J) (B := B) (C j)) /
        (n * Real.sqrt n)

theorem dotJ_finset_sum_smul_left {κ : Type*} (s : Finset κ) (w : κ → ℝ) (u : κ → J → ℝ)
    (v : J → ℝ) : dotJ (∑ i ∈ s, w i • u i) v = ∑ i ∈ s, w i * dotJ (u i) v

theorem integral_sq_sum_smul_jointError_le (w : ι → ℝ)
    (hw : lawCov D (dirLoss S (∑ i, w i • tangentField hS ν (F i) mD))
      (dirLoss S (∑ i, w i • tangentField hS ν (F i) mD)) = 0) {n : ℕ} (hn : 0 < n) :
    ∫ ω, (∑ i, w i * jointError hS ν D Xs F n ω i) ^ 2 ∂P ≤
      Fintype.card ι * (∑ i, w i ^ 2 * fourthConst (J := J) (B := B) (C i)) / n ^ 2

theorem measureReal_quadForm_jointError_ge_le (A : ι → ι → ℝ)
    (hA : ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, A i j * (v i * v j)) {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 0 < r) :
    P.real {ω | r ^ 2 ≤ n * ∑ i, ∑ j, A i j *
        (jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j)} ≤
      ((∑ i, ∑ j, A i j * influenceCov hS ν D F i j) +
        (∑ i, ∑ j, |A i j| * ((1 / 2 : ℝ) * (influenceCov hS ν D F i i +
          influenceCov hS ν D F j j + 2 * fourthConst (J := J) (B := B) (C i) +
          2 * fourthConst (J := J) (B := B) (C j)))) / Real.sqrt n) / r ^ 2

```



## Where N5 and N6 stand

* **N5 (Cauchy–Binet barycentric regression).** Mathlib has NO Cauchy–Binet formula (only `det_mul` for square matrices). Proving `det(AᵀWA) = Σ_I det(A_I)²∏_{x∈I}w_x` from scratch and then the barycentric representation `β_p = Σ_I ω_I(p) β_I` is a large detour. QUESTION: is there a determinant-free route to `u_F(p) ∈ conv{b_I}` (e.g. via the extreme points of the feasible set of the normal equations, or a Carathéodory/Jacobi-type argument on the weighted least-squares functional), or a weaker configuration-only stability constant that is still new and natural? Or should N5 be skipped?
* **N6 (local price of refinement).** The seabed's sharp risk has constants `C(D)` that depend on the law; the local-alternatives limit `D_n ∝ e^{τh/√n}D` needs uniformity of `C(D_n)` in `n`. The deterministic half is cheap: along the data tilt `D_t ∝ e^{th}D` with `D` a level-`k` model law, `d/dt[E_{D_t}F − Ψ_{k,F}(D_t)]|₀ = Cov_D(F − P_kF, h)` (the first-order defect of a level), and `Var_D(P_{k+1}F) − Var_D(P_kF) = Var_D(P_{k+1}F − P_kF)`. QUESTION: what is the cleanest formal statement of N6 that avoids uniformity in `n`? E.g. a fixed-law bias–variance decomposition `E(Ψ̂ − E_DF)² = Var_D ψ_F/n + (Ψ_F(D) − E_DF)² + O(n^{-3/2} + |Ψ_F(D) − E_DF|/n)` plus the first-order defect identity, which together give the boxed limit as a corollary in prose?

## Questions

1. **Audit** the statements above for mathematical errors, mis-scoped hypotheses, or vacuous cases (e.g. the `[IsProbabilityMeasure (faceMeasure ν A)]` + `hA : A = supportSet hS ν M` pattern; the `hB` feature bound; the sup norm on `J → ℝ` everywhere; the tangency hypothesis of `stratified_transport`; the `QuadRem` constants).
2. Answer the N5 and N6 questions above.
3. **The next programme.** With the response map now understood as a stratified gradient-like system with a facewise calculus, transport theorem, residual Hessian, and face-adaptive sampling theory, what are the next 6 targets of maximum beauty and depth for the user's direction (mapping the space of responses across the data manifold from the featureless law to the data law, and the resolution story)? Candidates I see: (a) the second-order stratified transport (journey Hessian `d²/dt² E_{R_{M(t)}}F = E[r_F ℓ_V²] + ⟨u_F, M̈⟩` along tangent paths, with the face-switching structure); (b) an intrinsic geometric statement: the entropy response `M ↦ R_M` as a gradient flow / the transport field `u_F` as the gradient of `f_F` for the face-Fisher metric, `df_F = G_A(u_F, ·)` on each stratum, so `stratified_transport` is Stokes for a stratified 1-form; (c) the boundary behaviour of the tangential field at a face crossing (does `u_F^{A}(M')` converge to the projection of the ambient field as `M' → ∂`? the seabed has `tendsto_faceProj_regressionDir`); (d) chamber/resolution refinements using the joint ellipsoid (a decision-theoretic minimax over finitely many chambers); (e) the unlocalised refined bias `(1/2n)tr(Cov_D(S)D²f_F) + O(n^{-3/2})` from N3's pieces; (f) N6. Rank, state each target precisely, give proof routes on the seabed, and name what to skip.
