# Research round 102 — germbij response-map programme: programme L (L2, L4, L5, L7) landed; audit + programme M

You are GPT-6 Astra, research advisor to a Lean 4 (Mathlib) formalisation of the note *germbij* (the response map `q ↦ Φ(q) ∈ W` of a bounded feature family `S : J → X → ℝ` over data laws `q ≪ ν`; `W = dirSpan`; `P_θ = ν.tilted(−⟨θ,S⟩)`; mean map `m`; inverse chart `θr`; Fisher form `G`; chart derivative `A = CD θ`, inverse `(CDE θ).symm`; `regressionDir F θ = u_F` the Fisher–Riesz representative of `v ↦ Cov_θ(F,⟨v,S⟩)` (round 100/101, K5); `responseProjection hS ν M = R_M` the entropy projection; `secondResponse F θ u v = E_θ[(F − EF) r_{uv}]` with `r` the score residual; `scoreResidual`; `sampleResponse S Xs n ω = M̂_n`; `dotJ` = Euclidean pairing on `J → ℝ`; `lawCov ρ f g` = covariance). Everything below is sorry-free, warning-free Lean in laplace `Laplace/Multi/Response*` (≈76 modules, rounds 84–101).

The user's standing direction: *"make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to map the space of responses across the data manifold (ideally all the way from the featureless distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?"* plus the resolution story (truth shifts vs sampling shifts; chambers below the sampling scale are unresolvable). The user wants new mathematics, not packaging.

## What landed since round 101 (your programme L)

* **L2 `ResponseObservableIIDExpansion`** — the observable delta method: `obsChart F θ₀ z = E_{θr(m₀+z)}F`; **Hessian = second response** `D²f_F(m₀)[e,e] = E_{θ₀}[(F−EF) r_{A⁻¹e,A⁻¹e}]`; cubic remainder on a ball (δ, K exist); law-level bias `|E[f̂_loc − f(m₀)] − ½E_μ H_F| ≤ ((Σ|u_{F,j}|)/δ² + K + ½‖H_F‖/δ)M₃`; i.i.d. bias `E[f̂_{F,loc}] − f_F(m_D) = (1/2n)·tr(Σ_D D²f_F) + O(n^{-3/2})` with explicit constant `√3|J|³(2B)³/n^{3/2}`. (Covariance formula NOT done yet — the linear part `E[⟨u_F,ξ⟩⟨u_H,ξ⟩] = Cov_D/n` is K5.)
* **L4 `ResponseMismatchResolution`** — `dataBilin D = Σ_D` on `W`; under positive definiteness the covariance dual `e* = Σ_D⁻¹e` (`dataDual`), `⟨u,e⟩² ≤ Σ_D(u,u)⟨e,Σ_D⁻¹e⟩`, **`isGreatest_snr`: `max_{u≠0} ⟨u,e⟩²/Σ_D(u,u) = ⟨e,Σ_D⁻¹e⟩`**; `E[⟨u,ξ_n⟩²] = Σ_D(u,u)/n`; off-model floor `1 ≤ n⟨e,Σ_D⁻¹e⟩`; **local nonlinear chamber certificate** (margin γ, radius r with `(Σ|u_{F,j}|)r + ½‖H_F‖r² + Kr³ < γ`) and its Hoeffding probability `≥ 1 − 2|J|exp(−nr²/(8B²))`.
* **L5 `ResponseFeatureRefinement`** — `Refines S T ν` (every `S`-feature ν-a.e. affine in `T`); `R_T` has the `S`-mean of `D`; coarse rate finite from fine rate; **ladder `KL(D‖R_S) = KL(D‖R_T) + KL(R_T‖R_S)`** and `KL(R_T‖ν) = KL(R_S‖ν) + KL(R_T‖R_S)` (in ℝ≥0∞, boundary cases included); Pinsker certificate with affine predictors subtracted: `ofReal((E_{R_T}F − E_{R_S}F)²/(2L²)) ≤ KL(R_T‖R_S)` for `|F − ⟨a,S⟩ − c| ≤ L`.
* **L7 `ResponseTestingData`** — for ANY `μ ≪ η`: root density `√(dμ/dη) ∈ L²(η)` with root law μ, constant root for η, **affinity testing bound `error ≥ (1 − √(1 − ρ^{2n}))/2`** (ρ = Hellinger affinity), **Hellinger ≤ KL: `2(1−ρ) ≤ KL(μ‖η)`** (pointwise `2r − 2√r ≤ r log r`, Jensen-free), Bernoulli ⇒ **`error ≥ (1 − √(n KL(μ‖η)))/2`**; local alternatives `D_s ∝ e^{s⟨e*,S⟩}D` along the covariance dual: `KL(D_s‖D)/s² → ⟨e,Σ_D⁻¹e⟩/2` and `d/ds⟨u,m(D_s)⟩|₀ = ⟨u,e⟩` for `u ∈ W`.
* **L3** — NOT a new module: the remaining-information identities already exist in the seabed in "atlas" language (`klDiv_data_atlas_eq_integral`: `KL(D‖Q_s) = KL(D‖R_M) + ∫_s^1 (1−t) atlasCurv`, `toReal_klDiv_responseProjection_atlas_eq_integral`, and the observable tail bound `sq_integral_sub_responseProjection_atlas_le`), where `atlasPath S ν M s = (1−s)m₀ + sM` and `Q_s = R_{atlasPath s}` — i.e. exactly the polytope journey of K1/K4 with `atlasCurv = journeyEnergy` up to identification. Only the derivative `d/dt KL(D‖P_t) = −(1−t)g` and the affine-predictor Pinsker along the journey would be new. Worth a translation module, or skip?
* **L1** — deferred: Mathlib has NO Cauchy–Binet, so the volume-sampling identity `u_F(p) = Σ_B λ_B(p) u_B` is a substantial detour. Is there a Cauchy–Binet-free proof of the uniform bound `‖u_F(p)‖ ≤ L_F` over positive laws for a fixed finite configuration (e.g. via the normal equations and a compactness/closed-graph argument on the closed simplex, or via the fact that `Σ_p u = γ_p` with both sides affine in `p` and a Perron-type argument)? Or a weaker but sufficient statement (Lipschitz of `M ↦ E_{R_M}F` on the closed polytope) reachable another way — e.g. from the atlas tail bound `(E_{R_M}F − E_{Q_s}F)² ≤ 2L²∫_s^1(1−u)κ_u du` plus `∫_s^1(1−u)κ_u du ≤ C(1−s)`?
* **L6** — not started.

## Key statements (verbatim Lean; `…` elides proofs)

```lean
-- Laplace/Multi/ResponseObservableIIDExpansion.lean
/-- **The posterior expectation in mean coordinates**: `f_F(m₀ + z) = E_{θ(m(θ₀)+z)} F`. -/
noncomputable def obsChart (F : X → ℝ) (θ₀ : 𝕍) (z : 𝕍) : ℝ :=
  ∫ x, F x ∂Pfam (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) : J → ℝ)

-- Laplace/Multi/ResponseObservableIIDExpansion.lean
/-- **The Hessian quadratic form of the posterior expectation**:
`H_F(z) = secondResponse F θ₀ (A⁻¹z) (A⁻¹z) = E_{θ₀}[(F − E F) r_{A⁻¹z, A⁻¹z}]`. -/
noncomputable def obsHessForm (F : X → ℝ) (θ₀ : 𝕍) (z : 𝕍) : ℝ :=
  secondResponse hS ν F θ₀ ((CDE θ₀).symm z) ((CDE θ₀).symm z)

-- Laplace/Multi/ResponseObservableIIDExpansion.lean
/-- **The Hessian of the posterior expectation is the second response**:
`D²f_F(m₀)[e, e] = E_{θ₀}[(F − E F) r_{A⁻¹e, A⁻¹e}]`. -/
theorem fderiv_fderiv_obsChart_zero {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) :
    fderiv ℝ (fderiv ℝ (obsChart hS ν F θ₀)) 0 e e = obsHessForm hS ν F θ₀ e := by …

-- Laplace/Multi/ResponseObservableIIDExpansion.lean
/-- **The cubic expansion of the posterior expectation in a mean displacement**: on a ball inside
the chart domain, `|f_F(m₀+z) − f_F(m₀) − ⟨u_F, z⟩ − ½ H_F(z)| ≤ K ‖z‖³`. -/
theorem exists_obsChart_cubic_remainder {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) :
    ∃ δ > 0, (∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω) ∧
      ∃ K, 0 ≤ K ∧ ∀ z : 𝕍, ‖z‖ ≤ δ →
        |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
          dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
          (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3 := by …

-- Laplace/Multi/ResponseObservableIIDExpansion.lean
/-- **THE LOCALISED OBSERVABLE BIAS IS THE HESSIAN TERM**: for a centred law `μ` of the sampling
displacement with third absolute moment `M₃`,
`| E[f̂_{F,loc} − f_F(m₀)] − ½ E_μ[H_F(Z)] | ≤ ((∑_j |u_{F,j}|)/δ² + K + ½ ‖H_F‖/δ) M₃`,
where `f̂_{F,loc} = f_F(m₀) + 1_{‖ξ‖≤δ}(f_F(m₀+ξ) − f_F(m₀))` is the reset-localised posterior
expectation. -/
theorem obsBias_hessian (μ : Measure 𝕍) [IsFiniteMeasure μ] {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍)
    {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (hcent : ∫ z, z ∂μ = 0) (hint : Integrable (fun z : 𝕍 ↦ z) μ)
    (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    |(∫ z in cball, (obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0) ∂μ) -
        (1 / 2 : ℝ) * ∫ z, obsHessForm hS ν F θ₀ z ∂μ| ≤
      ((∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) / δ ^ 2 + K +
        (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ / δ) * ∫ z, ‖z‖ ^ 3 ∂μ := by …

-- Laplace/Multi/ResponseObservableIIDExpansion.lean
/-- **The Hessian contracted with the data covariance**:
`∑_{a,b} Cov_D(S_a,S_b) H_F(A⁻¹ p e_a, A⁻¹ p e_b) = tr(Σ_D D²f_F(m₀))`. -/
noncomputable def hessContraction {F : X → ℝ} (hF : Bdd F) (p : (J → ℝ) →ₗ[ℝ] 𝕍) (θ₀ : 𝕍) :
    ℝ :=
  ∑ a, ∑ b, (∫ x, (S a x - ∫ y, S a y ∂D) * (S b x - ∫ y, S b y ∂D) ∂D) *

-- Laplace/Multi/ResponseObservableIIDExpansion.lean
/-- **THE i.i.d. SAMPLING BIAS OF A LOCALISED POSTERIOR EXPECTATION**: for the reset-localised
posterior expectation of `n` i.i.d. samples from a data law `D` with mean `m(θ₀)`,
`| E[f̂_{F,loc}] − f_F(m₀) − (1/(2n)) ∑_{a,b} Cov_D(S_a,S_b) H_F(A⁻¹p e_a, A⁻¹p e_b) |
  ≤ ((∑_j |u_{F,j}|)/δ² + K + ½‖H_F‖/δ) · √3 |J|³ (2B)³ / n^{3/2}`. -/
theorem iid_obsBias_hessian (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w)
    {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3) :
    |(∫ z in cball, (obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0)
          ∂(P.map fun ω ↦ p ((raw n) ω))) -
        (1 / 2 : ℝ) * ((1 / n : ℝ) * hessContraction hS ν D hF p θ₀)| ≤
      ((∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) / δ ^ 2 + K +
        (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ / δ) *
        (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n)) := by …

-- Laplace/Multi/ResponseFeatureRefinement.lean
/-- `T` refines `S`: every `S`-feature is `ν`-a.e. an affine function of the `T`-features. -/
def Refines (S : J → X → ℝ) (T : K → X → ℝ) (ν : Measure X) : Prop :=
  ∀ j, ∃ (b : K → ℝ) (c : ℝ), S j =ᵐ[ν] fun x ↦ dirLoss T b x + c

-- Laplace/Multi/ResponseFeatureRefinement.lean
/-- **The `T`-response has the `S`-mean of the data** when `T` refines `S`. -/
theorem mean_S_responseProjection_T (hST : Refines S T ν) :
    (fun j : J ↦ ∫ x, S j x ∂responseProjection hT ν mT) = mS := by …

-- Laplace/Multi/ResponseFeatureRefinement.lean
/-- **The coarse rate is finite when the fine rate is**: `𝓘_S(m_S D) ≤ KL(R_T‖ν) = 𝓘_T(m_T D)`. -/
theorem genRate_ne_top_of_refines (hST : Refines S T ν) : genRate ν S mS ≠ ⊤ := by …

-- Laplace/Multi/ResponseFeatureRefinement.lean
/-- **The acquired information along a refinement**: `KL(R_T‖ν) = KL(R_S‖ν) + KL(R_T‖R_S)`. -/
theorem klDiv_responseProjection_refine (hST : Refines S T ν) :
    klDiv (responseProjection hT ν mT) ν =
      klDiv (responseProjection hS ν mS) ν +
        klDiv (responseProjection hT ν mT) (responseProjection hS ν mS) := by …

-- Laplace/Multi/ResponseFeatureRefinement.lean
/-- **THE REFINEMENT LADDER**: `KL(D‖R_S) = KL(D‖R_T) + KL(R_T‖R_S)` — the information newly
resolved by the richer features is exactly the reduction of the information invisible to the coarse
ones. -/
theorem klDiv_data_responseProjection_refine (hST : Refines S T ν) :
    klDiv D (responseProjection hS ν mS) =
      klDiv D (responseProjection hT ν mT) +
        klDiv (responseProjection hT ν mT) (responseProjection hS ν mS) := by …

-- Laplace/Multi/ResponseFeatureRefinement.lean
/-- **The observable certificate of a refinement**: for a bounded observable and an affine feature
predictor `⟨a, S⟩ + c` with `|F − ⟨a,S⟩ − c| ≤ L`,
`(E_{R_T}F − E_{R_S}F)² / (2L²) ≤ KL(R_T‖R_S)`. -/
theorem sq_integral_sub_responseProjection_refine_le (hST : Refines S T ν) {F : X → ℝ}
    (hF : Bdd F) (a : J → ℝ) {c L : ℝ} (hL : 0 < L)
    (hFc : ∀ x, |F x - dirLoss S a x - c| ≤ L) :
    ENNReal.ofReal (((∫ x, F x ∂responseProjection hT ν mT) -
        ∫ x, F x ∂responseProjection hS ν mS) ^ 2 / (2 * L ^ 2)) ≤
      klDiv (responseProjection hT ν mT) (responseProjection hS ν mS) := by …

-- Laplace/Multi/ResponseMismatchResolution.lean
/-- **The data covariance form** on the direction space: `Σ_D(u, v) = Cov_D(⟨u,S⟩, ⟨v,S⟩)`. -/
noncomputable def dataBilin : LinearMap.BilinForm ℝ 𝕍 :=
  LinearMap.mk₂ ℝ (fun u v : 𝕍 ↦ lawCov D (dirLoss S (u : J → ℝ)) (dirLoss S (v : J → ℝ)))

-- Laplace/Multi/ResponseMismatchResolution.lean
/-- **The covariance dual** of a displacement `e ∈ W`: the direction `e* ∈ W` with
`Σ_D(e*, u) = ⟨u, e⟩` for every `u ∈ W`, i.e. `e* = Σ_D⁻¹ e`. -/
noncomputable def dataDual (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (e : 𝕍) :
    𝕍 :=
  ((dataBilin hS ν D).toDual (dataBilin_nondegenerate hS ν D hpd)).symm

-- Laplace/Multi/ResponseMismatchResolution.lean
/-- The defining property of the covariance dual. -/
theorem dataBilin_dataDual (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (e u : 𝕍) :
    dataBilin hS ν D (dataDual hS ν D hpd e) u = dotJ (u : J → ℝ) (e : J → ℝ) := by …

-- Laplace/Multi/ResponseMismatchResolution.lean
/-- **The optimal linearised signal-to-noise ratio**: `⟨e, Σ_D⁻¹ e⟩` is the greatest value of
`⟨u, e⟩² / Σ_D(u, u)` over nonzero directions, attained at the covariance dual. -/
theorem isGreatest_snr (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) {e : 𝕍} (he : e ≠ 0) :
    IsGreatest {r | ∃ u : 𝕍, u ≠ 0 ∧ r = dotJ (u : J → ℝ) (e : J → ℝ) ^ 2 / dataBilin hS ν D u u}
      (dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e)) := by …

-- Laplace/Multi/ResponseMismatchResolution.lean
/-- **The local nonlinear chamber certificate**: if the posterior expectation exceeds `c` by the
margin `γ` at the mean `m₀`, then it still exceeds `c` at every mean displacement `z` with
`‖z‖ ≤ r`, provided `(∑_j |u_{F,j}|) r + ½‖H_F‖ r² + K r³ < γ`. -/
theorem obsChart_gt_of_norm_le {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {δ K : ℝ}
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (hK : 0 ≤ K) {c γ r : ℝ} (hγ : c + γ ≤ obsChart hS ν F θ₀ 0) (hrδ : r ≤ δ)
    (hcert : (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * r +
      (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ * r ^ 2 + K * r ^ 3 < γ)
    (z : 𝕍) (hz : ‖z‖ ≤ r) :
    c < obsChart hS ν F θ₀ z := by …

-- Laplace/Multi/ResponseMismatchResolution.lean
/-- **The exact noise of a linear statistic off the model**: `E[⟨u, ξ_n⟩²] = Σ_D(u,u)/n`. -/
theorem integral_sq_dotJ_sampleResponse_sub_eq (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) (u : 𝕍) :
    ∫ ω, dotJ (u : J → ℝ) ((raw n) ω) ^ 2 ∂P = dataBilin hS ν D u u / n := by …

-- Laplace/Multi/ResponseMismatchResolution.lean
/-- **THE OFF-MODEL RESOLUTION FLOOR**: if `Σ_D` is positive definite on `W` and the observable
with regression direction `u_F` resolves the truth displacement `e` above its own sampling noise,
`E[⟨u_F, ξ_n⟩²] ≤ ⟨u_F, e⟩²`, then `n ⟨e, Σ_D⁻¹ e⟩ ≥ 1`. -/
theorem mismatch_resolution_floor (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P) {n : ℕ}
    (hn : 0 < n) (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (F : X → ℝ) (θ₀ e : 𝕍)
    (hu : regressionDir hS ν F θ₀ ≠ 0)
    (hres : ∫ ω, dotJ (regressionDir hS ν F θ₀ : J → ℝ) ((raw n) ω) ^ 2 ∂P ≤
      dotJ (regressionDir hS ν F θ₀ : J → ℝ) (e : J → ℝ) ^ 2) :
    1 ≤ n * dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e) := by …

-- Laplace/Multi/ResponseMismatchResolution.lean
/-- **The probabilistic chamber certificate**: under the margin certificate of
`obsChart_gt_of_norm_le`, the empirical posterior expectation exceeds the threshold with probability
at least `1 − 2|J| exp(−n r²/(8B²))`. -/
theorem measureReal_obsChart_gt_ge (hind : iIndepFun Xs P) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j x, |S j x| ≤ B) {n : ℕ} (hn : 0 < n) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) (hDν : D ≪ ν) {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍)
    {δ K : ℝ}
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (hK : 0 ≤ K) {c γ r : ℝ} (hγ : c + γ ≤ obsChart hS ν F θ₀ 0) (hr0 : 0 < r) (hrδ : r ≤ δ)
    (hcert : (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * r +
      (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ * r ^ 2 + K * r ^ 3 < γ) :
    1 - 2 * Fintype.card J * Real.exp (-((n : ℝ) * r ^ 2) / (8 * B ^ 2)) ≤
      P.real {ω | c < obsChart hS ν F θ₀ (p ((raw n) ω))} := by …

-- Laplace/Multi/ResponseTestingData.lean
/-- The root density `√(dμ/dη)`. -/
noncomputable def rootFun (x : Ω) : ℝ := √((μ.rnDeriv η x).toReal)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure η] in

-- Laplace/Multi/ResponseTestingData.lean
/-- **The Hellinger affinity** `ρ(μ, η) = ∫ √(dμ/dη) dη`. -/
noncomputable def dataAffinity : ℝ := ∫ x, rootFun μ η x ∂η

theorem integral_dataRoot_mul_oneRoot :

-- Laplace/Multi/ResponseTestingData.lean
/-- **The affinity testing bound for data laws**: every equal-prior test of `μ` against `η` on
`n` i.i.d. samples has error at least `(1 − √(1 − ρ^{2n}))/2`. -/
theorem testing_error_data_ge (n : ℕ) {φ : (Fin n → Ω) → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(1 - (dataAffinity μ η ^ n) ^ 2)) / 2 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ μ)) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ η)) / 2 := by …

-- Laplace/Multi/ResponseTestingData.lean
/-- **Hellinger is below Kullback–Leibler**: `2(1 − ρ(μ,η)) ≤ KL(μ‖η)`. -/
theorem two_sub_two_mul_dataAffinity_le (hkl : klDiv μ η ≠ ⊤) :
    2 - 2 * dataAffinity μ η ≤ (klDiv μ η).toReal := by …

-- Laplace/Multi/ResponseTestingData.lean
/-- `1 − ρ^{2n} ≤ n · KL(μ‖η)`. -/
theorem one_sub_dataAffinity_pow_le (hkl : klDiv μ η ≠ ⊤) (n : ℕ) :
    1 - (dataAffinity μ η ^ n) ^ 2 ≤ n * (klDiv μ η).toReal := by …

-- Laplace/Multi/ResponseTestingData.lean
/-- **THE TESTING OBSTRUCTION IN INFORMATION FORM**: every equal-prior test of `μ` against `η` on
`n` i.i.d. samples has error at least `(1 − √(n KL(μ‖η)))/2`. -/
theorem testing_error_data_ge_of_klDiv (hkl : klDiv μ η ≠ ⊤) (n : ℕ) {φ : (Fin n → Ω) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(n * (klDiv μ η).toReal)) / 2 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ μ)) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ η)) / 2 := by …

-- Laplace/Multi/ResponseTestingData.lean
/-- **The testing obstruction for the local alternatives**: every test of `D_s` against `D` on
`n` samples has error at least `(1 − √(n KL(D_s‖D)))/2`. -/
theorem testing_error_tilted_ge {f : X → ℝ} (hf : Bdd f) (s : ℝ) (n : ℕ)
    {φ : (Fin n → X) → ℝ} (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(n * (klDiv (D.tilted fun x ↦ s * f x) D).toReal)) / 2 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ D.tilted fun x ↦ s * f x)) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ D)) / 2 := by …

-- Laplace/Multi/ResponseTestingData.lean
/-- **The information of the local alternatives along the covariance dual** is
`s² ⟨e, Σ_D⁻¹ e⟩ / 2 + o(s²)`. -/
theorem tendsto_klDiv_tilted_dataDual_div_sq (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u)
    (e : 𝕍) :
    Tendsto (fun s ↦ (klDiv (D.tilted fun x ↦
        s * dirLoss S (dataDual hS ν D hpd e : J → ℝ) x) D).toReal / s ^ 2)
      (𝓝[≠] 0) (𝓝 (dotJ (dataDual hS ν D hpd e : J → ℝ) (e : J → ℝ) / 2)) := by …

-- Laplace/Multi/ResponseTestingData.lean
/-- **The local alternatives along the covariance dual move the mean in the direction `e`**:
`d/ds ⟨u, m(D_s)⟩|_{s=0} = ⟨u, e⟩` for every `u ∈ W`. -/
theorem hasDerivAt_dotJ_mean_tilted_dataDual (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u)
    (e u : 𝕍) :
    HasDerivAt (fun s ↦ dotJ (u : J → ℝ)
        (fun i ↦ ∫ x, S i x ∂(D.tilted fun x ↦ s * dirLoss S (dataDual hS ν D hpd e : J → ℝ) x)))
      (dotJ (u : J → ℝ) (e : J → ℝ)) 0 := by …

-- Laplace/Multi/InformationAlongAtlas.lean
/-- **Information along the atlas**: for a data law `D` with response `M` and finite information,
`KL(D‖Q_s) = KL(D‖Π(M)) + ∫_s^1 (1−t) κ(t) dt`. -/
theorem klDiv_data_atlas_eq_integral (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) (hD : (fun j ↦ ∫ x, S j x ∂D) = M) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    (klDiv D (responseProjection hS ν (atlasPath S ν M s))).toReal =
      (klDiv D (responseProjection hS ν M)).toReal +
        ∫ t in s..1, (1 - t) * atlasCurv hS ν hfin t := by …

-- Laplace/Multi/EndpointTail.lean
/-- **The exact endpoint tail**: `KL(Π(M) ‖ Π(M_s)) = ∫_s^1 (1 − u) κ(u) du`. -/
theorem toReal_klDiv_responseProjection_atlas_eq_integral {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (klDiv (responseProjection hS ν M) (responseProjection hS ν (atlasPath S ν M s))).toReal =
      ∫ u in s..1, (1 - u) * atlasCurv hS ν hfin u := by …

-- Laplace/Multi/BoundaryCompletion.lean
/-- **Pinsker at the endpoint**: the endpoint defect of every bounded observable is controlled by
the tail of the weighted Fisher energy, `(E_{Q_*}F − E_{Q_s}F)² ≤ 2 L² ∫_s^1 (1 − u) κ_u du` for
`|F − c| ≤ L`. -/
theorem sq_integral_sub_responseProjection_atlas_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {F : X → ℝ} (hF : Bdd F) {c L : ℝ} (hL : 0 < L) (hFc : ∀ x, |F x - c| ≤ L) :
    ((∫ x, F x ∂responseProjection hS ν M) - ∫ x, F x ∂(Qat s)) ^ 2 ≤
      2 * L ^ 2 * ∫ u in s..1, (1 - u) * atlasCurv hS ν hfin u := by …
```

## Questions

1. **Audit L2, L4, L5, L7.** Correct and the right statements? In particular: (a) L2's sign and the constant `(Σ_j|u_{F,j}|)/δ²` (a sup-norm pairing bound; is there a cleaner Fisher-normalised constant?); (b) L4: `dataDual` is defined only under positive definiteness — should I add the singular case (covariance inverse on the range, infinite SNR in noiseless directions) or is it a corner? (c) L5: hypotheses `D ≪ ν`, `genRate_T ≠ ⊤` — anything missing for the ladder, and is the `Refines` notion (ν-a.e. affine) the right one? (d) L7: the constant in `error ≥ (1 − √(nKL))/2` vs Pinsker's `1 − √(nKL/2)` — is there an equally cheap route to `nKL/2` (e.g. `1 − ρ² ≤ KL/2`?), and is `2(1−ρ) ≤ KL` sharp enough for the chamber story?

2. **Programme M.** With K and L landed, what are the 5–7 most valuable *new* theorems now, ranked, with proof routes sized against this seabed? Our candidates: (i) L2's nonlinear covariance `Cov(f̂_F, f̂_H) = Cov_D(⟨u_F,S⟩,⟨u_H,S⟩)/n + O(n^{-3/2})`; (ii) the nested-feature LADDER as a sequence (finitely many refinements, telescoping `KL(D‖ν) = Σ KL(R_{k+1}‖R_k)` when the last family is saturated: needs `R_D = D` for saturated finite families — do we have it? J2's `SpansAffine` gives every bounded function affine in S, hence `KL(D‖R_D) = 0`); (iii) L6 facewise response calculus (tangential regression directions converge at boundary means); (iv) the L1 uniform bound by a non-Cauchy–Binet route; (v) a "response map is a retraction of the data manifold" theorem tying K3 (fibres) + L5 (ladders) + L7 (obstruction): the fibre of the response over `M` is exactly the set of data laws no S-based procedure can distinguish at rate — i.e. testing lower bounds *within a fibre* need KL between fibre members, not between projections; (vi) the joint law of (structural coordinate, observable) fluctuations — a CLT-free second-moment statement `E[⟨u,ξ⟩ (f̂_F − f_F)] = Cov_D(⟨u,S⟩,⟨u_F,S⟩)/n + O(n^{-3/2})`; (vii) minimax: combine L4's `isGreatest_snr` with L7 to a two-point minimax lower bound for estimating `⟨e, m_D⟩`-type functionals: `inf_estimators sup_{D'} E|T − ⟨w,m_{D'}⟩| ≥ c/√(n⟨w,Σ_D w⟩)` hmm (needs Le Cam two-point). Rank against your own, say what to skip, give sharp statements.

3. **Anything false or vacuous in L2/L4/L5/L7?** Check hypothesis lists for accidental strength (e.g. `hpd` positive definiteness; `hK : 0 ≤ K`; `Refines` a.e.; `hDν : D ≪ ν`).
