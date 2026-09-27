# Research round 104 — germbij response-map programme: programme M and the post-M ranks all landed; audit + next programme

You are GPT-6 Astra, research advisor to a Lean 4 (Mathlib) formalisation of the note *germbij* (the response map `q ↦ Φ(q) ∈ W` of a bounded feature family `S : J → X → ℝ` over data laws `q ≪ ν`; `W = dirSpan` (`𝕍`); `P_θ = ν.tilted(−⟨θ,S⟩)` (`Pfam`); mean map `m`; inverse chart `θr`; Fisher form `G`; `regressionDir F θ = u_F`; `responseProjection hS ν M = R_M` the entropy projection; `dataBilin D = Σ_D`; `dataKer` its kernel `N`; `dataDualSing he = e*` the covariance dual of a displacement `e` annihilated by `N` (M6); `qStarVec M = (R_M{x})_x` on a finite configuration; `hull = conv S(X)`; `Ω = relint`; `regressor hS D hh` = the regression of a score `h` on `S` under `D`; `Refines S T ν`; `sampleResponse S Xs n ω = M̂_n`; `lawCov`; `dotJ`; `Bdd`). Everything below is sorry-free, warning-free Lean in laplace `Laplace/Multi/Response*` (≈95 modules).

The user's standing direction: *"make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to map the space of responses across the data manifold (ideally all the way from the featureless distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?"* plus the resolution story (truth shifts vs sampling shifts; chambers below the sampling scale are unresolvable). New mathematics, not packaging.

## What landed since round 103 (everything you ranked)

* **M3 `ResponseRegressionUniformBound`** — vertex-free sign-cell argument, exactly your §2.2 cheaper version but with the direct termwise bound instead of a normalised sequence: `Σ_x p_x r_x s_x = E` termwise nonneg ⇒ `|s_x| ≤ E/(p_x|r_x|)` (and `s_x = 0` where `r_x = 0`); injective design map ⇒ bounded cell; finite max over realised patterns. `‖u_F(θ)‖ ≤ L_F` for all `θ`.
* **M3b `ResponseGlobalLipschitz`** — `|E_{R_N}F − E_{R_M}F| ≤ L‖N − M‖` on the CLOSED polytope (interior mean value along response lines; closed polytope by segment approximation + continuity of `q*`), `LipschitzOnWith` packaging, and the law-valued `Σ_x|R_N{x} − R_M{x}| ≤ L‖N − M‖`.
* **M4 `ResponseFacewiseRegression`** — finite-configuration `L¹` covariance stability; face covariance form `Σ_q` as a `BilinForm`, positive definite on the face direction space `W_A = vectorSpan(S(supp q*(M)))`; `faceReg` (Riesz), `faceProj` (the `Σ_{R_M}`-projection onto `W_A`); coercivity; quantitative `‖π_A u − u_H^A‖ ≤ (3B(LB + K_H)/λ_A)Σ|p − q|`; **`tendsto_faceProj_regressionDir`** (`π_A(u_H(θr M_k)) → u_H^A` for `M_k → M ∈ hull`). NOT formalised: the identification of `faceProj` with the Euclidean orthogonal projection (it is one, since the discarded component has a face-constant feature).
* **M7a `ResponseModelBaseDefect`** — BASE CHANGE `Π^{P_θ₀}(M) = Π^ν(M)` (your relative-base Pythagoras made unnecessary: the seabed's ν-based defect theory transfers verbatim to base `D = P_θ₀`); defect theorem at the featureless law by L'Hôpital on the seabed's `ℰ''(0)`; **DEFECT THEOREM** `KL(D_t‖R_{m(D_t)})/t² → ½Var_D(h − g_h)` at every model base.
* **M7b `ResponseInfinitesimalLadder`** — coarse model laws are fine model laws; **`KL(R^T_t‖R^S_t)/t² → ½(Var_D g_T − Var_D g_S) = ½Var_D(g_T − g_S)`** (nested Pythagoras).
* **Post-M 2 `ResponseJourneyIntegral`** — **`E_{R_{m_D}}F − E_νF = ∫₀¹⟨u_F(θ(M_t)), m_D − m_ν⟩dt`**, endpoint on the boundary included (FTC on `[0,T]`, `T<1`, + uniform bound + boundary journey).
* **Post-M 3+4 `ResponseEmpiricalRisk`** — plug-in `Ψ̂_F = E_{R_{M̂_n}}F` defined for every sample (`M̂_n ∈ hull`); `E(Ψ̂ − Ψ)² ≤ L²tr Cov_D(S)/n`, `E|Ψ̂ − Ψ| ≤ L√(tr/n)` (no measurability needed for the second-moment form; `(E|Z|)² ≤ EZ²` from `Var|Z| ≥ 0`); Chebyshev; **MARGIN CHAMBER THEOREM** `ball(m_D,r) ⊆ C ⇒ P(M̂ ∉ C) ≤ tr/(nr²)`.
* **Post-M 6 `ResponseResolutionEllipsoid`** — `u_{Σc_iF_i} = Σc_iu_{F_i}`; `Σ_D(u_{F_c},u_{F_c}) = cᵀVc`; Le Cam for every contrast with `cᵀVc > 0`.
* **Post-M 5 `ResponseRefinementBudget`** — chain `S : (k : ℕ) → J k → X → ℝ` with dependent index types; `KL(D‖R_0) = KL(D‖R_K) + Σ_{k<K}KL(R_{k+1}‖R_k)`; saturated form; Pinsker stopping criterion `(E_DF − E_{R_K}F)²/(2L²) + Σ ≤ KL(D‖R_0)`.
* **Post-M 4 lower `ResponseAttainableChamber`** — along `D_s ∝ e^{s⟨e*,S⟩}D`: mean speed `e`, cost `⟨e,Σ_D⁺e⟩/2`; at `s_n = a/√n` means `ae/√n` apart, every `[0,1]`-test has error `≥ L_n → (1 − √(a²⟨e,Σ_D⁺e⟩/2))/2`.

## Key statements (verbatim Lean; `…` elides proofs)

```lean

-- Laplace/Multi/ResponseRegressionUniformBound.lean
/-- **THE UNIFORM REGRESSION BOUND**: on a finite configuration the regression directions of a
bounded observable are uniformly bounded over the whole model, `‖u_F(θ)‖ ≤ L_F` for every `θ`,
although the weights and the Fisher form degenerate at the boundary of the polytope. -/
theorem exists_uniform_regressionDir_bound (hν : ∀ x, ν {x} ≠ 0) {F : X → ℝ} (hF : Bdd F) :
    ∃ L : ℝ, ∀ θ : 𝕍, ‖(uF F θ : J → ℝ)‖ ≤ L := …


-- Laplace/Multi/ResponseGlobalLipschitz.lean
/-- **THE GLOBAL LIPSCHITZ RESPONSE**: on the closed moment polytope, with `L` a uniform bound on
`Σ_j |u_F(θ)_j|`, `|E_{R_N}F − E_{R_M}F| ≤ L ‖N − M‖` for all `M, N ∈ conv S(X)`. -/
theorem abs_responseObs_sub_le {F : X → ℝ} (hF : Bdd F) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ θ : 𝕍, ∑ j, |(uF F θ : J → ℝ) j| ≤ L) {M N : J → ℝ} (hM : M ∈ hull) (hN : N ∈ hull) :
    |(∫ x, F x ∂responseProjection hS ν N) - ∫ x, F x ∂responseProjection hS ν M| ≤
      L * ‖N - M‖ := …

/-- **The entropy projection is Lipschitz on the closed polytope**: there is `L` with
`Σ_x |R_N{x} − R_M{x}| ≤ L ‖N − M‖` for all `M, N ∈ conv S(X)`. -/
theorem sum_abs_qStarVec_sub_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ M ∈ hull, ∀ N ∈ hull,
      ∑ x, |qStarVec hS ν N x - qStarVec hS ν M x| ≤ L * ‖N - M‖ := …


-- Laplace/Multi/ResponseFacewiseRegression.lean
/-- **THE LAW-LEVEL FACE STABILITY ESTIMATE**: if `u` solves the regression normal equations of
`H` on `V` under a law `p`, `‖u‖ ≤ L`, and `λ` is a coercivity constant of `Σ_q` on `V`, then
`‖π_V u − u_H^V‖ ≤ (3B(LB + K_H)/λ) Σ_x |p_x − q_x|` with `B = Σ_j Σ_x |S_j(x)|`. -/
theorem norm_faceProj_sub_faceReg_le (hpd : PosDefOn S hq V) {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ w ∈ V, lam * ‖w‖ ^ 2 ≤ covForm S hq w w) {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X)
    {H : X → ℝ} {KH : ℝ} (hKH : 0 ≤ KH) (hH : ∀ x, |H x| ≤ KH) {u : J → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hu : ‖u‖ ≤ L)
    (hreg : ∀ w ∈ V, lawCov (vecMeasure p) (dirLoss S u) (dirLoss S w) =
      lawCov (vecMeasure p) H (dirLoss S w)) :
    ‖(faceProj hq hpd u : J → ℝ) - (faceReg hq hpd H : J → ℝ)‖ ≤
      3 * (∑ j, ∑ y, |S j y|) * (L * (∑ j, ∑ y, |S j y|) + KH) / lam * ∑ x, |p x - q x| := …

/-- **FACEWISE CONVERGENCE OF THE REGRESSION DIRECTIONS**: for interior means `M_k → M ∈ conv S(X)`
and a bounded observable `H`, the tangential projections of the regression directions converge to
the regression direction of the face law, `π_A(u_H(θ(M_k))) → u_H^A`. -/
theorem tendsto_faceProj_regressionDir {M : J → ℝ} (hM : M ∈ hull) {ι : Type*} {l : Filter ι}
    {Mk : ι → J → ℝ} (hMk : ∀ k, Mk k ∈ Ω) (hlim : Tendsto Mk l (𝓝 M)) {H : X → ℝ}
    (hH : Bdd H) :
    Tendsto (fun k ↦ (faceProj (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM)
        (posDefOn_faceSpan hS ν hν hM) (uF H (θr (Mk k)) : J → ℝ) : J → ℝ)) l
      (𝓝 (faceReg (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM)
        (posDefOn_faceSpan hS ν hν hM) H : J → ℝ)) := …


-- Laplace/Multi/ResponseModelBaseDefect.lean
/-- **BASE CHANGE OF THE ENTROPY PROJECTION**: the entropy projection of a mean does not depend
on the base point chosen within the family, `Π^{P_{θ₀}}(M) = Π^ν(M)`. -/
theorem responseProjection_familyMeasure_base (θ₀ : J → ℝ) {M : J → ℝ}
    (hfin : genRate ν S M ≠ ⊤) :
    responseProjection hS (Pfam θ₀) M = responseProjection hS ν M := …

/-- **THE DEFECT THEOREM AT A MODEL BASE POINT**: along `D_t ∝ e^{t h} P_{θ₀}`, the information
invisible to the response is, to second order, the residual variance of the score after regression
on the features under `D = P_{θ₀}`:
`KL(D_t ‖ R_{m(D_t)}) / t² → ½ Var_D(h − g_h)`. -/
theorem tendsto_klDiv_tilted_familyMeasure_responseProjection_div_sq (θ₀ : J → ℝ)
    (D : Measure X) [IsProbabilityMeasure D] (hD : D = Pfam θ₀) :
    Tendsto (fun t ↦ (klDiv (D.tilted fun x ↦ t * h x)
        (responseProjection hS ν fun i ↦ ∫ x, S i x ∂D.tilted fun x ↦ t * h x)).toReal /
      t ^ 2) (𝓝[≠] 0)
      (𝓝 (lawCov D (fun x ↦ h x - regressor hS D hh x)
        (fun x ↦ h x - regressor hS D hh x) / 2)) := …


-- Laplace/Multi/ResponseInfinitesimalLadder.lean
/-- **A model law of the coarse family is a model law of the fine family.** -/
theorem exists_familyMeasure_eq_of_refines (hST : Refines S T ν) (θ₀ : J → ℝ) :
    ∃ η₀ : K → ℝ, PT η₀ = PS θ₀ := …

/-- The infinitesimal ladder in Pythagorean form:
`KL(R^T_t ‖ R^S_t) / t² → ½ Var_D(g_T − g_S)`. -/
theorem tendsto_klDiv_responseProjection_refine_div_sq' (hST : Refines S T ν) {θ₀ : J → ℝ}
    {η₀ : K → ℝ} (hbase : PT η₀ = PS θ₀) [IsProbabilityMeasure (PS θ₀)] :
    Tendsto (fun t ↦ (klDiv
        (responseProjection hT ν fun k ↦ ∫ x, T k x ∂(PS θ₀).tilted fun x ↦ t * h x)
        (responseProjection hS ν fun j ↦ ∫ x, S j x ∂(PS θ₀).tilted fun x ↦ t * h x)).toReal /
      t ^ 2) (𝓝[≠] 0)
      (𝓝 (lawCov (PS θ₀) (fun x ↦ regressor hT (PS θ₀) hh x - regressor hS (PS θ₀) hh x)
        (fun x ↦ regressor hT (PS θ₀) hh x - regressor hS (PS θ₀) hh x) / 2)) := …


-- Laplace/Multi/ResponseJourneyIntegral.lean
/-- **THE CANONICAL JOURNEY INTEGRAL**: the change of a posterior expectation from the featureless
law to the entropy response of the data is the integral of the response field along the canonical
journey, endpoint included:
`E_{R_{m_D}}F − E_ν F = ∫₀¹ ⟨u_F(θ(M_t)), m_D − m_ν⟩ dt`. -/
theorem integral_responseProjection_sub_eq_journey {F : X → ℝ} (hF : Bdd F) :
    (∫ x, F x ∂responseProjection hS ν mD) - ∫ x, F x ∂ν =
      ∫ t in (0 : ℝ)..1, journeyField hS ν D F t := …


-- Laplace/Multi/ResponseEmpiricalRisk.lean
/-- **THE UNIFORM RISK BOUND**: `E_D |Ψ̂_F − Ψ_F(D)| ≤ L_F √(tr Cov_D(S) / n)`, uniformly over all
data laws on the configuration and with no localisation. -/
theorem integral_abs_empiricalObs_sub_le {F : X → ℝ} (hF : Bdd F) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S, ∑ j, |(regressionDir hS ν F θ : J → ℝ) j| ≤ L)
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, |empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD| ∂P ≤
      L * √(traceCov S D / n) := …

/-- **THE MARGIN CHAMBER THEOREM**: if the chamber `C` assigned to the data law contains the
Euclidean `r`-ball about `m_D`, then the probability of assigning the empirical mean to another
chamber is at most `tr Cov_D(S) / (n r²)`. The margin `r`, the distance from `m_D` to the boundary
of its chamber, controls the resolution, not the width of the chamber. -/
theorem measureReal_sampleResponse_notMem_chamber_le {C : Set (J → ℝ)} {r : ℝ} (hr : 0 < r)
    (hball : ∀ M', ‖M' - mD‖ < r → M' ∈ C) {n : ℕ} (hn : 0 < n) :
    P.real {ω | sampleResponse S Xs n ω ∉ C} ≤ traceCov S D / n / r ^ 2 := …


-- Laplace/Multi/ResponseResolutionEllipsoid.lean
/-- **The influence variance of a contrast is its resolution form**:
`σ²_{F_c} = Σ_D(u_{F_c}, u_{F_c}) = cᵀ V c`. -/
theorem dataBilin_regressionDir_sum {ι : Type*} [Fintype ι] (c : ι → ℝ) {F : ι → X → ℝ}
    (hF : ∀ i, Bdd (F i)) :
    dataBilin hS ν D (uF fun x ↦ ∑ i, c i * F i x) (uF fun x ↦ ∑ i, c i * F i x) =
      ∑ i, ∑ i', c i * c i' * resolutionMat hS ν D F i i' := …

/-- **THE RESOLUTION ELLIPSOID**: every scalar contrast `F_c = Σ_i c_i F_i` of finitely many
posterior expectations with `cᵀ V c > 0` carries the two-point minimax obstruction at the scale
`√(cᵀ V c / n)`: along the alternatives tilted by the influence function of `F_c` at scale
`a/√n`, `√n L_n → (a cᵀVc/2)(1 − √(a² cᵀVc/2))` and every integrable estimator has two-point risk
at least `L_n` for `n` large. -/
theorem minimax_two_point_contrast {ι : Type*} [Fintype ι] {F : ι → X → ℝ} (hF : ∀ i, Bdd (F i))
    (c : ι → ℝ) (hpos : 0 < ∑ i, ∑ i', c i * c i' * resolutionMat hS ν D F i i') {a : ℝ}
    (ha : 0 < a) :
    ∃ L : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ Real.sqrt n * L n) atTop
        (𝓝 (a * (∑ i, ∑ i', c i * c i' * resolutionMat hS ν D F i i') / 2 *
          (1 - √(a ^ 2 * (∑ i, ∑ i', c i * c i' * resolutionMat hS ν D F i i') / 2)))) ∧
      ∀ᶠ n : ℕ in atTop, ∀ T : (Fin n → X) → ℝ, Measurable T →
        Integrable T (Measure.pi fun _ : Fin n ↦ D) →
        Integrable T (Measure.pi fun _ : Fin n ↦
          D.tilted fun x ↦ (a / Real.sqrt n) * dataInfluence hS ν D (fun x ↦ ∑ i, c i * F i x) x) →
        L n ≤ max (∫ z, |T z - dataObs hS ν (fun x ↦ ∑ i, c i * F i x) D|
            ∂(Measure.pi fun _ : Fin n ↦ D))
          (∫ z, |T z - dataObs hS ν (fun x ↦ ∑ i, c i * F i x) (D.tilted fun x ↦ (a / Real.sqrt n) *
            dataInfluence hS ν D (fun x ↦ ∑ i, c i * F i x) x)| ∂(Measure.pi fun _ : Fin n ↦
              D.tilted fun x ↦ (a / Real.sqrt n) *
                dataInfluence hS ν D (fun x ↦ ∑ i, c i * F i x) x)) := …


-- Laplace/Multi/ResponseRefinementBudget.lean
/-- **THE GLOBAL REFINEMENT BUDGET**: along a chain of refinements,
`KL(D ‖ R_0) = KL(D ‖ R_K) + Σ_{k<K} KL(R_{k+1} ‖ R_k)`. -/
theorem klDiv_levelResponse_telescope {K : ℕ}
    (hK : genRate ν (S K) (fun j ↦ ∫ x, S K j x ∂D) ≠ ⊤) :
    klDiv D (levelResponse hS ν D 0) =
      klDiv D (levelResponse hS ν D K) +
        ∑ k ∈ Finset.range K, klDiv (levelResponse hS ν D (k + 1)) (levelResponse hS ν D k) := …

/-- **THE BUDGET AS A STOPPING CRITERION**: the observable error of the level-`K` response plus the
information already resolved by the refinements is at most the total information beyond the
coarsest level, `(E_D F − E_{R_K} F)²/(2L²) + Σ_{k<K} KL(R_{k+1} ‖ R_k) ≤ KL(D ‖ R_0)`. -/
theorem pinsker_budget {K : ℕ} (hK : genRate ν (S K) (fun j ↦ ∫ x, S K j x ∂D) ≠ ⊤)
    {F : X → ℝ} (hF : Bdd F) {c L : ℝ} (hL : 0 < L) (hFc : ∀ x, |F x - c| ≤ L) :
    ENNReal.ofReal (((∫ x, F x ∂D) - ∫ x, F x ∂levelResponse hS ν D K) ^ 2 / (2 * L ^ 2)) +
        ∑ k ∈ Finset.range K, klDiv (levelResponse hS ν D (k + 1)) (levelResponse hS ν D k) ≤
      klDiv D (levelResponse hS ν D 0) := …


-- Laplace/Multi/ResponseAttainableChamber.lean
/-- **THE RESOLUTION FLOOR ALONG AN ATTAINABLE DIRECTION**: for the alternatives `D_{a/√n}` tilted
by the least-information score of an annihilated displacement `e`, the two-point testing bound
`L_n = (1 − √(n KL(D_{a/√n} ‖ D)))/2` converges to `(1 − √(a² ⟨e, Σ_D⁺ e⟩/2))/2`, and every test
`φ` between `n` samples of `D` and of `D_{a/√n}` has error at least `L_n`. -/
theorem chamber_resolution_floor {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) {a : ℝ} (ha : 0 < a) :
    ∃ L : ℕ → ℝ,
      Tendsto L atTop (𝓝 ((1 - √(a ^ 2 *
        dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he) / 2)) / 2)) ∧
      ∀ n : ℕ, ∀ φ : (Fin n → X) → ℝ, Measurable φ → (∀ z, 0 ≤ φ z) → (∀ z, φ z ≤ 1) →
        L n ≤ ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ D.tilted fun x ↦ (a / Real.sqrt n) *
            (hE he) x)) + ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ D)) / 2 := …

```

## Questions

1. **Audit** the statements above. Anything false, vacuous, or with accidental hypothesis strength? In particular: (a) M3b's `L` is any uniform bound on `Σ_j|u_F(θ)_j|` (sup-norm pairing) — is the Euclidean-Lipschitz constant `L_F` we get (a finite max over sign cells, not explicit) the right object, or should the note carry an explicit constant (e.g. via the determinant/Cauchy–Binet route `max_I‖b_I‖`)? (b) M4: `faceProj` is defined as the `Σ_{R_M}`-Riesz projection; is stating the theorem with it (rather than the Euclidean projection) acceptable, and is there a cheap proof that they coincide? (c) M7a's base change `Π^{P_θ₀}(M) = Π^ν(M)` — any subtlety at boundary `M` (finite `ν`-rate assumed)? (d) The journey integral's integrand at the endpoint `t = 1` is `⟨u_F(θr m_D), e⟩` with `θr` junk on the boundary — harmless for the integral, but should the note define the response field on the closed polytope via the tangential (M4) limit instead? (e) `chamber_resolution_floor` quantifies over tests `φ` of the two laws; is this the right formal shape of "no procedure resolves the chamber", or should it be phrased for chamber classifiers `c : (Fin n → X) → Bool` with `P_D(c ≠ C_D) + P_{D_s}(c ≠ C_{D_s})`?

2. **Next programme.** With K, L, M and the post-M ranks all landed, what are the 5–7 most valuable NEW theorems now, ranked, with proof routes sized against this seabed? Candidates from my side: (i) the Euclidean identification of `faceProj` + a facewise version of the journey integral (the response field on the closed polytope is the tangential regression direction, and the journey integral holds with it); (ii) `Ψ̂_F` is also `E_D`-unbiased to first order / its bias `= (1/2n)tr(Σ_D D²f_F)` on the closed polytope (extending L2 to boundary means via M4?); (iii) a Berry–Esseen-free CLT substitute: the exact law of `√n(M̂ − m_D)` is not available, but Chebyshev + M2's covariance give a two-sided interval for `Ψ̂` — is there a cleaner "confidence ellipsoid" theorem combining M2, post-M 6 and Chebyshev (`P(|Ψ̂_{F_c} − Ψ_{F_c}| ≥ r) ≤ (cᵀVc/n + O(n^{-3/2}))/r²`)? (iv) the response map on the FULL simplex of laws (general `X`, not finite): Lipschitz of `M ↦ E_{R_M}F` on the closed moment body via the atlas tail bounds (round 102 said Pinsker only gives ½-Hölder; is Lipschitz true in general? counterexample?); (v) the "journey through the data manifold" for data laws NOT of finite rate (infinite `KL(D‖ν)`): the polytope journey still makes sense (means), does the journey integral hold?; (vi) second-order facewise calculus (Hessians at boundary means); (vii) anything about maximum-entropy interpretation of `R_0 = ν` in the budget chain (the coarsest family should be the trivial one; we did not formalise `R^{S_0}_M = ν` for a constant family — is it worth a lemma?). Rank against your own, say what to skip, give sharp statements.

3. **The note.** Given ~95 modules, which 6–8 theorems should be the spine of the germbij response-map section (in order), so that the story "featureless law → data, resolution by sampling" reads as one argument? One sentence each.
