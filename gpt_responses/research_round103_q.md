# Research round 103 — germbij response-map programme: programme M (M1, M2, M5, companions, M6) landed; the Lean route for M3/M4 and the M7 design

You are GPT-6 Astra, research advisor to a Lean 4 (Mathlib) formalisation of the note *germbij* (the response map `q ↦ Φ(q) ∈ W` of a bounded feature family `S : J → X → ℝ` over data laws `q ≪ ν`; `W = dirSpan` (a submodule of `J → ℝ`, notation `𝕍`); `P_θ = ν.tilted(−⟨θ,S⟩)` (`Pfam`); mean map `m`; inverse chart `θr`; Fisher form `G`; chart derivative `A = CD θ`, inverse `(CDE θ).symm`; `regressionDir F θ = u_F` the Fisher–Riesz representative of `v ↦ Cov_θ(F,⟨v,S⟩)`; `responseProjection hS ν M = R_M` the entropy projection (`R_M` is the unique law with mean `M` minimising `KL(·‖ν)`; `Pythagoras: KL(ρ‖ν) = KL(ρ‖R_M) + KL(R_M‖ν)` for every `ρ` with mean `M`); `dataBilin D = Σ_D` the data covariance form on `W`; `dotJ` the Euclidean pairing on `J → ℝ`; `lawCov ρ f g` the covariance; `Bdd` = bounded; `SpansAffine S ν` = every bounded function is ν-a.e. affine in `S`). Everything below is sorry-free, warning-free Lean in laplace `Laplace/Multi/Response*` (≈83 modules, rounds 84–102).

The user's standing direction: *"make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to map the space of responses across the data manifold (ideally all the way from the featureless distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?"* plus the resolution story (truth shifts vs sampling shifts; chambers below the sampling scale are unresolvable). New mathematics, not packaging.

## What landed since round 102 (your programme M)

* **M1 `ResponseDataInfluence`** — `Ψ_F(D) = E_{R_{m_D}}F`; along `D_t ∝ e^{th}D`, `d/dt Ψ_F(D_t)|₀ = Cov_D(⟨u_F,S⟩,h)` (mean path via a retraction `W`-valued `meanPath`, chain rule through the response chart); influence function `IF_{F,D} = ⟨u_F, S − m_D⟩` with `Var_D(IF) = Σ_D(u_F,u_F)`; minimum-information lift `⟨e,Σ_D⁻¹e⟩` under positive definiteness.
* **M2 `ResponseObservableJointCovariance`** — reset-localised increments `A_F(z) = 1_{‖z‖≤δ}(f_F(m₀+z) − f_F(m₀))`; law-level `|Cov(A_F,A_H) − E[⟨u_F,ξ⟩⟨u_H,ξ⟩]| ≤ (c_F d_H + a_F c_H)M₃ + c_F c_H M₂²`; i.i.d. `Cov(f̂_{F,loc}, f̂_{H,loc}) = Σ_D(u_F,u_H)/n + O(n^{-3/2})` and the cross term `E[⟨u,ξ_n⟩ f̂_{F,loc}] = Σ_D(u,u_F)/n + O(n^{-3/2})`, explicit constants, no fourth moments.
* **M5 `ResponseMinimaxTwoPoint`** — Le Cam two-point bound from L7's testing obstruction via the clipped test; along `D_t ∝ e^{t IF}D` at `t_n = a/√n`: `√n L_n → (aσ_F²/2)(1 − √(a²σ_F²/2))`, every integrable estimator has two-point risk `≥ L_n` eventually.
* **Companions `ResponseRefinementCompanions`** — `Refines_trans`; idempotence `R_{m(R_M)} = R_M`; two laws agreeing on the affine span agree on all bounded observables; **`R_D = D` for `SpansAffine` families** (every `D ≪ ν` with finite rate).
* **M6 `ResponseSingularCovariance`** — `N = ker Σ_D` (`D`-a.s. constant features); the descended form on `W ⧸ N` is nondegenerate; covariance dual `e*` for `e` annihilated by `N` with `Σ_D(e*,u) = ⟨u,e⟩`; `sup_{Σ_D(u,u) ≤ 1}⟨u,e⟩² = Σ_D(e*,e*) = ⟨e,Σ_D⁺e⟩` attained; unbounded SNR off the annihilator; a bounded lift `h` with `Cov_D(⟨u,S⟩,h) = ⟨u,e⟩ ∀u` forces annihilation, and on the annihilator the least lift variance is `Σ_D(e*,e*)`.
* Not done: M3 (uniform regression bound), M4 (facewise convergence), M7 (infinitesimal ladder), global ladder telescoping, product-KL additivity.

## Key statements (verbatim Lean; `…` elides proofs; local notations as above)

```lean

-- Laplace/Multi/ResponseDataInfluence.lean
/-- **The posterior expectation as a function of the data law**: `Ψ_F(D) = E_{R_{m_D}} F`. -/
noncomputable def dataObs (F : X → ℝ) (D : Measure X) : ℝ := …

/-- The influence function `IF_{F,D}(x) = ⟨u_F, S(x) − m_D⟩` at a law with interior response. -/
noncomputable def dataInfluence (F : X → ℝ) (x : X) : ℝ := …

/-- **The data-law influence of a posterior expectation**: along the tilted perturbations
`D_t ∝ e^{t h} D` of a data law with interior response,
`d/dt E_{R_{m(D_t)}} F |_{t=0} = Cov_D(⟨u_F, S⟩, h)`. -/
theorem hasDerivAt_dataObs_tilted {F : X → ℝ} (hF : Bdd F) {h : X → ℝ} (hh : Bdd h) :
    HasDerivAt (fun t ↦ dataObs hS ν F (D.tilted fun x ↦ t * h x))
      (lawCov D (dirLoss S (regressionDir hS ν F (θr mD) : J → ℝ)) h) 0 := …

/-- The influence function has the covariances of the regression feature `⟨u_F, S⟩`. -/
theorem lawCov_dataInfluence (F : X → ℝ) {h : X → ℝ} (hh : Bdd h) :
    lawCov D (dataInfluence hS ν D F) h =
      lawCov D (dirLoss S (regressionDir hS ν F (θr mD) : J → ℝ)) h := …

/-- **The minimum-information lift**: among the bounded scores `h` producing the response velocity
`Cov_D(⟨u,S⟩, h) = ⟨u, e⟩` for every `u ∈ W`, the least variance is `⟨e, Σ_D⁻¹ e⟩`, attained by
the covariance-dual feature `h_e = ⟨Σ_D⁻¹ e, S⟩`. -/
theorem isLeast_information_lift (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (e : 𝕍) :
    IsLeast {v | ∃ h : X → ℝ, Bdd h ∧
        (∀ u : 𝕍, lawCov D (dirLoss S (u : J → ℝ)) h = dotJ (u : J → ℝ) (e : J → ℝ)) ∧
        v = lawCov D h h}
      (dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e)) := …


-- Laplace/Multi/ResponseObservableJointCovariance.lean
/-- **The reset-localised increment** of the posterior expectation:
`A_F(z) = 1_{‖z‖≤δ} (f_F(m₀+z) − f_F(m₀))`. -/
noncomputable def locInc (F : X → ℝ) (θ₀ : 𝕍) (δ : ℝ) (z : 𝕍) : ℝ := …

/-- **THE i.i.d. JOINT COVARIANCE OF LOCALISED POSTERIOR EXPECTATIONS**: for `n` i.i.d. samples
from a data law `D` (with `m_D = m(θ₀)` this is the covariance of the reset-localised empirical
posterior expectations),
`|Cov(f̂_{F,loc}, f̂_{H,loc}) − Σ_D(u_F, u_H)/n| ≤
  ((c_F d_H + a_F c_H) √3 |J|³ (2B)³ + c_F c_H (|J|² (2B)²)²) / n^{3/2}`. -/
theorem iid_lawCov_locInc_sub_le (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w)
    {F H : X → ℝ} (hF : Bdd F) (hH : Bdd H) (θ₀ : 𝕍) {KF KH : ℝ} (hδ : 0 < δ) (hKF : 0 ≤ KF)
    (hKH : 0 ≤ KH) (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hremF : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ KF * ‖z‖ ^ 3)
    (hremH : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν H θ₀ z - obsChart hS ν H θ₀ 0 -
        dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν H θ₀ z| ≤ KH * ‖z‖ ^ 3) :
    |lawCov P (fun ω ↦ locInc hS ν F θ₀ δ (p ((raw n) ω)))
        (fun ω ↦ locInc hS ν H θ₀ δ (p ((raw n) ω))) -
      lawCov D (dirLoss S (regressionDir hS ν F θ₀ : J → ℝ))
        (dirLoss S (regressionDir hS ν H θ₀ : J → ℝ)) / n| ≤
      ((globQuad hS ν hF θ₀ KF δ * globLin hS ν hH θ₀ KH δ +
          linSize hS ν F θ₀ * globQuad hS ν hH θ₀ KH δ) *
          (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3) +
        globQuad hS ν hF θ₀ KF δ * globQuad hS ν hH θ₀ KH δ *
          (Fintype.card J ^ 2 * (2 * B) ^ 2) ^ 2) / (n * Real.sqrt n) := …

/-- **THE i.i.d. COORDINATE–OBSERVABLE CROSS TERM**:
`|E[⟨u, ξ_n⟩ f̂_{F,loc}] − Σ_D(u, u_F)/n| ≤ (∑_j|u_j|) c_F √3 |J|³ (2B)³ / n^{3/2}`. -/
theorem iid_integral_dotJ_mul_locInc_sub_le (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) (u : J → ℝ) {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {K : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3) :
    |(∫ ω, dotJ u ((raw n) ω) * locInc hS ν F θ₀ δ (p ((raw n) ω)) ∂P) -
        lawCov D (dirLoss S u) (dirLoss S (regressionDir hS ν F θ₀ : J → ℝ)) / n| ≤
      (∑ j, |u j|) * globQuad hS ν hF θ₀ K δ *
        (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n)) := …


-- Laplace/Multi/ResponseMinimaxTwoPoint.lean
/-- **Le Cam's two-point bound**: for `μ ≪ η` with finite information and a functional taking the
values `ψ₀ < ψ₁` at `μ` and `η`, every integrable estimator of `n` i.i.d. samples satisfies
`max(E_{μⁿ}|T − ψ₀|, E_{ηⁿ}|T − ψ₁|) ≥ ((ψ₁ − ψ₀)/2)(1 − √(n KL(μ‖η)))`. -/
theorem lecam_two_point (hμη : μ ≪ η) (hkl : klDiv μ η ≠ ⊤) {ψ₀ ψ₁ : ℝ} (h : ψ₀ < ψ₁) (n : ℕ)
    {T : (Fin n → Ω) → ℝ} (hTm : Measurable T)
    (hT₀ : Integrable T (Measure.pi fun _ : Fin n ↦ μ))
    (hT₁ : Integrable T (Measure.pi fun _ : Fin n ↦ η)) :
    (ψ₁ - ψ₀) / 2 * (1 - √(n * (klDiv μ η).toReal)) ≤
      max (∫ z, |T z - ψ₀| ∂(Measure.pi fun _ : Fin n ↦ μ))
        (∫ z, |T z - ψ₁| ∂(Measure.pi fun _ : Fin n ↦ η)) := …

/-- **The minimax scale of a posterior expectation**: along the alternatives
`D_t ∝ e^{t IF_{F,D}} D` at scale `t_n = a/√n`, the Le Cam two-point lower bound `L_n` for
estimating `Ψ_F` satisfies `√n · L_n → (a σ_F²/2)(1 − √(a² σ_F²/2))` with `σ_F² = Σ_D(u_F,u_F)`,
and for `n` large every integrable estimator has
`max(E_{Dⁿ}|T − Ψ_F(D)|, E_{D_{t_n}ⁿ}|T − Ψ_F(D_{t_n})|) ≥ L_n`. -/
theorem minimax_two_point_tilted {F : X → ℝ} (hF : Bdd F)
    (hpos : 0 < dataBilin hS ν D (uF F) (uF F)) {a : ℝ} (ha : 0 < a) :
    ∃ L : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ Real.sqrt n * L n) atTop
        (𝓝 (a * dataBilin hS ν D (uF F) (uF F) / 2 *
          (1 - √(a ^ 2 * dataBilin hS ν D (uF F) (uF F) / 2)))) ∧
      ∀ᶠ n : ℕ in atTop, ∀ T : (Fin n → X) → ℝ, Measurable T →
        Integrable T (Measure.pi fun _ : Fin n ↦ D) →
        Integrable T (Measure.pi fun _ : Fin n ↦
          D.tilted fun x ↦ (a / Real.sqrt n) * dataInfluence hS ν D F x) →
        L n ≤ max (∫ z, |T z - dataObs hS ν F D| ∂(Measure.pi fun _ : Fin n ↦ D))
          (∫ z, |T z - dataObs hS ν F (D.tilted fun x ↦ (a / Real.sqrt n) *
            dataInfluence hS ν D F x)| ∂(Measure.pi fun _ : Fin n ↦
              D.tilted fun x ↦ (a / Real.sqrt n) * dataInfluence hS ν D F x)) := …


-- Laplace/Multi/ResponseRefinementCompanions.lean
/-- **The entropy projection is idempotent**: the response of the mean of a response is that
response. -/
theorem responseProjection_mean_self {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    responseProjection hS ν (fun i ↦ ∫ x, S i x ∂responseProjection hS ν M) =
      responseProjection hS ν M := …

/-- **Saturation reaches the data**: for a saturated family every data law `D ≪ ν` of finite rate
is its own entropy response, `R_D = D`. -/
theorem responseProjection_eq_self_of_spansAffine (hspan : SpansAffine S ν) (D : Measure X)
    [IsProbabilityMeasure D] (hDν : D ≪ ν)
    (hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤) :
    responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D) = D := …


-- Laplace/Multi/ResponseSingularCovariance.lean
/-- **The covariance kernel**: the directions with `D`-a.s. constant feature, `Σ_D(u, ·) = 0`. -/
noncomputable def dataKer : Submodule ℝ 𝕍 := …

/-- **The descended covariance form** on `W/N`. -/
noncomputable def quotBilin : LinearMap.BilinForm ℝ Q := …

/-- The descended form is nondegenerate. -/
theorem quotBilin_nondegenerate : (quotBilin hS ν D).Nondegenerate := …

/-- **The covariance dual of an annihilated displacement**: a representative in `W` of the
Riesz representative of `⟨·, e⟩` on `W/N`, so `Σ_D(e*, u) = ⟨u, e⟩` for every `u`. -/
noncomputable def dataDualSing {e : J → ℝ} (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) :
    𝕍 := …

/-- The defining property of the singular covariance dual. -/
theorem dataBilin_dataDualSing {e : J → ℝ} (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0)
    (u : 𝕍) : dataBilin hS ν D (dataDualSing hS ν D he) u = dotJ (u : J → ℝ) e := …

/-- **Finite optimal signal-to-noise on the annihilator**:
`sup_{Σ_D(u,u) ≤ 1} ⟨u, e⟩² = Σ_D(e*, e*)`, attained. -/
theorem isGreatest_snr_sing {e : J → ℝ} (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) :
    IsGreatest {r | ∃ u : 𝕍, dataBilin hS ν D u u ≤ 1 ∧ r = dotJ (u : J → ℝ) e ^ 2}
      (dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he)) := …

/-- **Noiseless witnesses**: a displacement not annihilated by the covariance kernel has unbounded
signal-to-noise ratios. -/
theorem not_bddAbove_snr_of_not_annihilator {e : J → ℝ} {u₀ : 𝕍} (hu₀ : u₀ ∈ dataKer hS ν D)
    (hne : dotJ (u₀ : J → ℝ) e ≠ 0) :
    ¬ BddAbove {r | ∃ u : 𝕍, dataBilin hS ν D u u ≤ 1 ∧ r = dotJ (u : J → ℝ) e ^ 2} := …

/-- A score realising a response velocity annihilates the covariance kernel: kernel directions have
`D`-a.s. constant features, hence zero covariance with every bounded score. -/
theorem annihilator_of_lift {e : J → ℝ} {h : X → ℝ} (hh : Bdd h)
    (hcov : ∀ u : 𝕍, lawCov D (dirLoss S (u : J → ℝ)) h = dotJ (u : J → ℝ) e) :
    ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0 := …

/-- **The minimum-information lift on the annihilator**: the least variance of a bounded score
realising the response velocity `⟨·, e⟩` is `Σ_D(e*, e*)`, attained at `⟨e*, S⟩`. -/
theorem isLeast_information_lift_sing {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) :
    IsLeast {v | ∃ h : X → ℝ, Bdd h ∧
        (∀ u : 𝕍, lawCov D (dirLoss S (u : J → ℝ)) h = dotJ (u : J → ℝ) e) ∧
        v = lawCov D h h}
      (dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he)) := …


-- Laplace/Multi/ResponseObservableSamplingGeometry.lean
/-- **The regression direction** `u_F ∈ W`: the Fisher–Riesz representative of the covariance
functional, `G_θ(u_F, v) = Cov_{P_θ}(F, ⟨v, S⟩)` for every `v ∈ W`. -/
noncomputable def regressionDir (F : X → ℝ) (θ : 𝕍) : 𝕍 := …

/-- The defining property of the regression direction. -/
theorem fisherInner_regressionDir {F : X → ℝ} (hF : Bdd F) (θ v : 𝕍) :
    G θ (regressionDir hS ν F θ) v = lawCov (Pfam (θ : J → ℝ)) F (dirLoss S (v : J → ℝ)) := …


-- Laplace/Multi/ResponseFeatureRefinement.lean
/-- `T` refines `S`: every `S`-feature is `ν`-a.e. an affine function of the `T`-features. -/
def Refines (S : J → X → ℝ) (T : K → X → ℝ) (ν : Measure X) : Prop := …

/-- **THE REFINEMENT LADDER**: `KL(D‖R_S) = KL(D‖R_T) + KL(R_T‖R_S)` — the information newly
resolved by the richer features is exactly the reduction of the information invisible to the coarse
ones. -/
theorem klDiv_data_responseProjection_refine (hST : Refines S T ν) :
    klDiv D (responseProjection hS ν mS) =
      klDiv D (responseProjection hT ν mT) +
        klDiv (responseProjection hT ν mT) (responseProjection hS ν mS) := …

```

## The proposed Lean route for M3 (please audit)

Mathlib has no polyhedral vertex theory (no "bounded polyhedron = convex hull of vertices", no "vertex ⇔ d+1 tight independent constraints"). It has Krein–Milman `closure_convexHull_extremePoints` and `extremePoints_convexHull_subset`, and compactness of closed bounded sets in finite dimension. Your round-102 M3 route (bounded sign cell ⇒ convex hull of interpolating fits) needs the vertex identification. I propose the following **vertex-free** route that gives the uniform bound (not the convex-hull membership):

Setting: `X` finite (the finite configuration), `ν` with full support on `X`, every model law `P_θ` has full support and positive weights `p_x(θ)`. The affine least-squares fit at `θ` is `β(θ) = (c, u_F(θ)) ∈ ℝ × W`, the unique minimiser of `Q_p(b) = Σ_x p_x (c + ⟨u,S(x)⟩ − F(x))²`, characterised by the normal equations `Σ_x p_x r_x(θ) a_x = 0` with `a_x = (1, S(x))` and residual `r_x = c + ⟨u,S(x)⟩ − F(x)`. (`a_x·b = 0 ∀x ⇒ b = 0` because `W` is the span of differences of feature values and `⟨u,S⟩` constant on `X` forces `u = 0` in `W`.)

1. For a sign pattern `σ : X → SignType`, the closed cell `C_σ = {b | ∀ x, 0 ≤ σ_x·(a_x·b − F(x)) ∧ (σ_x = 0 → a_x·b = F(x))}`. `β(θ) ∈ C_{σ(θ)}` with `σ(θ)_x = sign r_x(θ)`. Finitely many patterns.
2. **Cell boundedness** (your recession argument, one witness per pattern): if `p > 0` and `β(p) ∈ C_σ` with `σ = σ(p)`, then `C_σ` is bounded. Proof: if unbounded, a recession direction `v ≠ 0` exists at `β` (closed convex set in finite dimension: unit vectors `(b_k − β)/‖b_k − β‖` have a convergent subsequence on the compact sphere, convexity + closedness give `β + tv ∈ C_σ ∀ t ≥ 0`), so `r_x(a_x·v) ≥ 0 ∀x` and `a_x·v = 0` where `r_x = 0`; pairing the normal equations with `v` gives `Σ p_x r_x (a_x·v) = 0`, a sum of nonnegatives, so `r_x(a_x·v) = 0 ∀x`; hence `a_x·v = 0` for all `x` (both cases), so `v = 0`. Contradiction.
3. **Uniform bound**: `‖β(θ)‖ ≤ max over the finitely many realised patterns σ of sup_{C_σ}‖·‖ < ∞`. So `∃ L_F, ∀ θ, ‖u_F(θ)‖ ≤ L_F` (any norm on `W`; hence also `√G_θ(u_F,u_F) ≤ L_F √Λ` if the Fisher form is uniformly bounded above, which it is on a finite configuration).
4. Then `|f_F(M) − f_F(N)| ≤ L_F ‖M − N‖` on `Ω` by integrating `Df_F(M)[e] = ⟨u_F(θr M), e⟩` along segments (Ω is convex: the relative interior of the polytope), and the Lipschitz extension to the closed polytope is identified with `E_{R_M}F` by K1's boundary journey (`P_t → R_D` in law along the polytope journey, so `E_{P_t}F → E_{R_D}F`).

Questions on this route: (a) is step 2 airtight as stated (in particular the cell definition with both weak inequalities and equalities, and the "both cases" step)? (b) is there an even cheaper route to the uniform bound for a finite configuration — e.g. `‖u_F(θ)‖_{G_θ}² = Var_θ(proj F) ≤ Var_θ F ≤ ‖F‖²_∞` is FREE (Bessel), so `√G_θ(u_F,u_F) ≤ 2‖F‖_∞` uniformly; the problem is only that `G_θ` degenerates at the boundary. Is the Fisher-normalised bound enough for the Lipschitz statement in some other metric (Fisher distance `d_F` instead of Euclidean, i.e. `|f_F(M) − f_F(N)| ≤ 2‖F‖_∞ d_F(M,N)`, which follows from `|Df_F[θ̇]| = |G(u_F,θ̇)| ≤ √G(u_F,u_F)√G(θ̇,θ̇)` and is ALREADY a one-liner in the seabed's Fisher-length language)? Does the Euclidean Lipschitz statement carry mathematical content the Fisher one lacks (I believe yes: Fisher length blows up at the boundary while the polytope journey has finite Euclidean length, and M4 needs the Euclidean-bounded regression directions), please confirm or refute. (c) Is the sign-cell argument the right foundation for M4 too, or does M4 need the convex-hull form?

## M4 (facewise convergence) — please give the precise seabed statement

The seabed has: faces of the moment polytope `conv S(X)`, the face family `P^A_v` (entropy family on a face `A` of the support: `ν` conditioned to the atoms in the face, tilted), face embeddings, `meanExt`, `faceChart`, the boundary journey `P_t → R_M` for `M` on the boundary (finite `X`: every `M ∈ conv S(X)` is reached, `R_M` is the face family law). Give the statement of M4 in these terms (which convergence of `u_H(M_k)`, which projection, which limit object), and the proof route sized against: the M3 uniform bound, `Cov_{P_θ}(F,⟨v,S⟩)` continuous in the law (we have `L¹` continuity of covariances of bounded functions: `|ΔCov| ≤ 3‖f‖‖g‖‖q₁−q₂‖₁`), positive definiteness of the face covariance on the face's direction space.

## M7 (infinitesimal ladder) — please give the seabed statement

Seabed facts: `Refines S T ν`; `R^S_M`, `R^T_M`; the ladder `KL(D‖R_S) = KL(D‖R_T) + KL(R_T‖R_S)`; tilt second-order expansion `KL(D_s‖D)/s² → Var_D(h)/2` for `D_s ∝ e^{sh}D` (L7 has the Σ_D-dual instance; the general bounded-`h` version is `tendsto_klDiv_tilted_div_sq`-style, present); `regressionDir`; M1's influence derivative. Your round-102 statement: at a common interior base point `D` (a model law of the coarsest family, hence of all), `KL(R_{k+1}(t)‖R_k(t))/t² → ½‖(P_{k+1} − P_k)(h − E_D h)‖²_{L²(D)}`. In the seabed the natural objects are `u^S_h := regressionDir^S h` and `u^T_h` (the regression directions of the SCORE `h` itself in the two families) and `Var_D(⟨u^T_h,T⟩) − Var_D(⟨u^S_h,S⟩) = ‖(P_T − P_S)h₀‖²` (Pythagoras of nested projections). Please write the precise statement in these terms, the hypotheses (`D = P^S_θ` a model law of `S`, hence `= P^T_{θ'}`? or just `D` interior for both), and the proof route: is it `KL(R^T(t)‖R^S(t)) = KL(R^T(t)‖D) − KL(R^S(t)‖D) + (cross term)`? Note `R^T(t)` is the `T`-projection of `D_t`, `R^S(t)` the `S`-projection of `D_t`, and `KL(D_t‖R^S(t)) = KL(D_t‖R^T(t)) + KL(R^T(t)‖R^S(t))` (ladder at `D_t`), so `KL(R^T(t)‖R^S(t)) = KL(D_t‖R^S(t)) − KL(D_t‖R^T(t))` and each term is a "defect" `KL(D_t‖R(t))`; is `KL(D_t‖R^S(t))/t² → ½ Var_D(h − P_S h)` the right lemma (defect of a tilt = residual variance)? That would make M7: **defect second-order expansion** `KL(D_t‖R^S_{m(D_t)})/t² → ½‖h₀ − P_S h₀‖²` — is this known/true, and what is the cleanest route in the seabed (the response projection of `D_t` is `P_{θr(m(D_t))}`; expand `KL(D_t‖P_{θ(t)}) = E_{D_t}[log(dD_t/dν)] + ⟨θ(t), m(D_t)⟩ + log Z(θ(t))`, all smooth in `t` with `θ(0) = θ₀`, `θ'(0) = A⁻¹Cov_D(S,h)`)?

## Questions

1. **Audit M1, M2, M5, companions, M6** as stated above (statements verbatim). Anything false, vacuous, or with accidental hypothesis strength? In particular M5's `hpos : 0 < Σ_D(u_F,u_F)` (needed for `ψ₀ ≠ ψ₁`), M6's annihilation hypothesis `he` on `dataDualSing`, the companions' `hfin : genRate ≠ ⊤` in `R_D = D`.
2. **M3 route** — (a), (b), (c) above.
3. **M4 and M7 precise statements** as requested, with sizes against this seabed.
4. **After M**: with M3/M4/M7 done, what are the next 4–6 theorems of highest value for the user's direction (map the space of responses across the data manifold, from the featureless law to the data)? Candidates from my side: (i) the global Lipschitz response `M ↦ E_{R_M}F` on the closed polytope and its consequence "the response map `q ↦ Φ(q)` is a Lipschitz retraction of the closed simplex of data laws (in `L¹` or in mean coordinates) onto the polytope, with fibres the KL-fibres"; (ii) a **uniform** (in `M` over the closed polytope) i.i.d. resolution statement: `E|f̂_F − Ψ_F(D)| ≤ C/√n` with `C` independent of `D` (M3 gives the Lipschitz constant; Hoeffding gives `E‖M̂−m_D‖ ≤ C/√n`); (iii) the second-order M7 with the Hessian (the infinitesimal ladder to order `t³`?); (iv) the "chambers vs sampling" theorem in its final form: for a partition of the polytope into chambers of Euclidean width `r`, the probability of misclassifying the chamber of `m_D` from `n` samples is `≤ tr Σ_D/(n r²)` uniformly, and the two-point bound shows chambers of width `≪ 1/√n` cannot be resolved by ANY procedure (Le Cam along a mean displacement `e` with `n⟨e,Σ_D⁺e⟩ ≲ 1`). Rank, add your own, say what to skip.
