/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiltedFisherCompactConvergence
import Laplace.Multi.FisherNormalisedSampling
import Laplace.Multi.ExtremeMeanSupport
import Laplace.Multi.ReconstructionBias
import Laplace.Multi.ResponseFormContinuity

/-!
# `L¹` continuity of the response geometry in the data law

The covariance-quotient geometry of a data law `D = q ν` — its mean, its forcings
`b_D(k) = Cov_D(S, k)`, its response `Φ(D) = θ(E_D S)`, the response velocities
`DΦ_D[k] = (Dm(Φ(D))|_W)⁻¹ b_D(k)`, the bilinear response form `G_D(k, ℓ)` and the effective
dimension `d_eff(D) = tr(R_{Φ(D)} C_D)` — is a function of the density `q ∈ L¹(ν)`. With bounded
sufficient statistics and bounded score directions:

* **Means, forcings and covariances are `L¹`-Lipschitz** (`norm_densMean_sub_le`,
  `norm_densForcing_sub_le`, `abs_densCov_stat_sub_le`): `‖m(q₁) − m(q₂)‖ ≤ B ‖q₁ − q₂‖₁`,
  `‖b_{q₁}(k) − b_{q₂}(k)‖ ≤ 3 B K ‖q₁ − q₂‖₁`.
* **On regular chambers the response, the velocities, the response form and the effective
  dimension are `L¹`-continuous** (`tendsto_densResponse`, `tendsto_densVel`, `tendsto_densBilin`,
  `tendsto_densEffDim`): if `q_n → q` in `L¹` and `E_q S` is an interior mean, all of them converge.
  The inverse Fisher matrix is controlled through the continuity of the susceptibility
  `θ ↦ (Dm(θ)|_W)⁻¹` in the natural coordinates; nothing is claimed across singular boundary
  limits.

The response geometry is therefore robust to perturbations of the data law, not merely smooth
along selected coefficient paths.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Law

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The law with density `q`. -/
local notation "law" q => ν.withDensity fun x ↦ ENNReal.ofReal (q x)

variable (S) in
/-- The mean of the data law `q ν`. -/
noncomputable def densMean (q : X → ℝ) : J → ℝ := fun i ↦ ∫ x, S i x ∂(law q)

variable (S) in
/-- The forcing of the data law `q ν` by the score direction `k`: `b_q(k) = Cov_{qν}(S, k)`. -/
noncomputable def densForcing (q k : X → ℝ) : J → ℝ := fun i ↦ lawCov (law q) (S i) k

/-- The response of the data law `q ν`: `Φ(q) = θ(E_{qν} S)`. -/
noncomputable def densResponse (q : X → ℝ) : 𝕍 := θr (densMean S ν q)

/-- The response velocity of the data law `q ν` in the direction `k`, through the retraction
`p` onto `W`: `DΦ_q[k] = (Dm(Φ(q))|_W)⁻¹ b_q(k)`. -/
noncomputable def densVel (q : X → ℝ) (p : (J → ℝ) →ₗ[ℝ] 𝕍) (k : X → ℝ) : 𝕍 :=
  ((CDE (densResponse hS ν q)).symm : 𝕍 →L[ℝ] 𝕍) (p (densForcing S ν q k))

/-- The bilinear response form of the data law `q ν`: `G_q(k, ℓ) = −⟨DΦ_q[k], b_q(ℓ)⟩`. -/
noncomputable def densBilin (q : X → ℝ) (p : (J → ℝ) →ₗ[ℝ] 𝕍) (k ℓ : X → ℝ) : ℝ :=
  -dotJ (densVel hS ν q p k : J → ℝ) (densForcing S ν q ℓ)

/-- The effective dimension of the data law `q ν`: `d_eff(q) = tr(R_{Φ(q)} C_q)`. -/
noncomputable def densEffDim [DecidableEq J] (q : X → ℝ) (p : (J → ℝ) →ₗ[ℝ] 𝕍) : ℝ :=
  -(∑ a, ∑ b, samplingOp hS ν (densResponse hS ν q) p (Pi.single b 1) a *
    lawCov (law q) (S a) (S b))

/-- The joint map `(θ, b) ↦ (Dm(θ)|_W)⁻¹ (p b)` is continuous. -/
theorem continuous_susceptibility_apply (p : (J → ℝ) →ₗ[ℝ] 𝕍) :
    Continuous fun x : 𝕍 × (J → ℝ) ↦ ((((CDE x.1).symm : 𝕍 →L[ℝ] 𝕍) (p x.2) : 𝕍) : J → ℝ) := by
  refine continuous_subtype_val.comp (Continuous.clm_apply ?_ ?_)
  · exact (continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).comp continuous_fst
  · exact p.continuous_of_finiteDimensional.comp continuous_snd

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- The mean of an admissible density lies in the moment body. -/
theorem densMean_mem_momentBody {r : X → ℝ} (hr0 : ∀ x, 0 ≤ r x) (hri : Integrable r ν)
    (hr1 : ∫ x, r x ∂ν = 1) : densMean S ν r ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
  have := isProbabilityMeasure_withDensity_ofReal ν hr0 hri hr1
  exact mean_mem_momentBody_of_ac hS ν _ (withDensity_absolutelyContinuous _ _)

section Lipschitz

variable {q₁ q₂ : X → ℝ} (hq₁m : AEMeasurable q₁ ν) (hq₁0 : ∀ x, 0 ≤ q₁ x)
  (hq₁i : Integrable q₁ ν) (hq₁1 : ∫ x, q₁ x ∂ν = 1) (hq₂m : AEMeasurable q₂ ν)
  (hq₂0 : ∀ x, 0 ≤ q₂ x) (hq₂i : Integrable q₂ ν) (hq₂1 : ∫ x, q₂ x ∂ν = 1)
  {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i x, |S i x| ≤ B)
include hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i hB0 hB

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] hB0 in
/-- **Means are `L¹`-Lipschitz**: `|m(q₁)_i − m(q₂)_i| ≤ B ‖q₁ − q₂‖₁`. -/
theorem abs_densMean_sub_le (i : J) :
    |densMean S ν q₁ i - densMean S ν q₂ i| ≤ B * ∫ x, |q₁ x - q₂ x| ∂ν :=
  abs_integral_withDensity_sub_le ν hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i (hS i).1 (hB i)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem norm_densMean_sub_le :
    ‖densMean S ν q₁ - densMean S ν q₂‖ ≤ B * ∫ x, |q₁ x - q₂ x| ∂ν := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_densMean_sub_le hS ν hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i hB i

include hq₁1 hq₂1

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **Forcings are `L¹`-Lipschitz**: `|b_{q₁}(k)_i − b_{q₂}(k)_i| ≤ 3 B K ‖q₁ − q₂‖₁`. -/
theorem abs_densForcing_sub_le {k : X → ℝ} (hkm : Measurable k) {K : ℝ} (hK : ∀ x, |k x| ≤ K)
    (i : J) :
    |densForcing S ν q₁ k i - densForcing S ν q₂ k i| ≤ 3 * B * K * ∫ x, |q₁ x - q₂ x| ∂ν :=
  abs_lawCov_withDensity_sub_le ν hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i hq₁1 hq₂1 (hS i).1 hkm hB0
    (hB i) hK

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem norm_densForcing_sub_le {k : X → ℝ} (hkm : Measurable k) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |k x| ≤ K) :
    ‖densForcing S ν q₁ k - densForcing S ν q₂ k‖ ≤ 3 * B * K * ∫ x, |q₁ x - q₂ x| ∂ν := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_densForcing_sub_le hS ν hq₁m hq₁0 hq₁i hq₁1 hq₂m hq₂0 hq₂i hq₂1 hB0 hB hkm hK i

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **Data covariances of the statistics are `L¹`-Lipschitz.** -/
theorem abs_densCov_stat_sub_le (a b : J) :
    |lawCov (law q₁) (S a) (S b) - lawCov (law q₂) (S a) (S b)| ≤
      3 * B * B * ∫ x, |q₁ x - q₂ x| ∂ν :=
  abs_lawCov_withDensity_sub_le ν hq₁m hq₁0 hq₁i hq₂m hq₂0 hq₂i hq₁1 hq₂1 (hS a).1 (hS b).1 hB0
    (hB a) (hB b)

end Lipschitz

section Convergence

variable {α : Type*} {l : Filter α} {q : α → X → ℝ} {q₀ : X → ℝ}
  (hqm : ∀ n, AEMeasurable (q n) ν) (hq0 : ∀ n x, 0 ≤ q n x) (hqi : ∀ n, Integrable (q n) ν)
  (hq1 : ∀ n, ∫ x, q n x ∂ν = 1) (hq₀m : AEMeasurable q₀ ν) (hq₀0 : ∀ x, 0 ≤ q₀ x)
  (hq₀i : Integrable q₀ ν) (hq₀1 : ∫ x, q₀ x ∂ν = 1)
  (hL1 : Tendsto (fun n ↦ ∫ x, |q n x - q₀ x| ∂ν) l (𝓝 0))
include hqm hq0 hqi hq₀m hq₀0 hq₀i hL1

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **`L¹` convergence of densities gives convergence of means.** -/
theorem tendsto_densMean : Tendsto (fun n ↦ densMean S ν (q n)) l (𝓝 (densMean S ν q₀)) := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (by simpa using hL1.const_mul B)
  exact norm_densMean_sub_le hS ν (hqm n) (hq0 n) (hqi n) hq₀m hq₀0 hq₀i hB0 hB

include hq1 hq₀1

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **`L¹` convergence of densities gives convergence of forcings.** -/
theorem tendsto_densForcing {k : X → ℝ} (hk : Bdd k) :
    Tendsto (fun n ↦ densForcing S ν (q n) k) l (𝓝 (densForcing S ν q₀ k)) := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  obtain ⟨K, hK⟩ := hk.2
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK (Classical.arbitrary X))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa using hL1.const_mul (3 * B * K))
  exact norm_densForcing_sub_le hS ν (hqm n) (hq0 n) (hqi n) (hq1 n) hq₀m hq₀0 hq₀i hq₀1 hB0 hB
    hk.1 hK0 hK

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **`L¹` convergence of densities gives convergence of the data covariances.** -/
theorem tendsto_densCov_stat (a b : J) :
    Tendsto (fun n ↦ lawCov (law (q n)) (S a) (S b)) l (𝓝 (lawCov (law q₀) (S a) (S b))) := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa using hL1.const_mul (3 * B * B))
  rw [Real.norm_eq_abs]
  exact abs_densCov_stat_sub_le hS ν (hqm n) (hq0 n) (hqi n) (hq1 n) hq₀m hq₀0 hq₀i hq₀1 hB0 hB a b

variable (hrel : densMean S ν q₀ ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **`L¹` convergence of densities gives convergence of the responses** at interior means. -/
theorem tendsto_densResponse :
    Tendsto (fun n ↦ densResponse hS ν (q n)) l (𝓝 (densResponse hS ν q₀)) := by
  have hM₀ := densMean_mem_momentBody hS ν hq₀0 hq₀i hq₀1
  have hz : ∀ n, densMean S ν (q n) - densMean S ν q₀ ∈ 𝕍 := fun n ↦
    sub_mem_dirSpan_of_mem_momentBody' hS ν hM₀ (densMean_mem_momentBody hS ν (hq0 n) (hqi n)
      (hq1 n))
  have hzt : Tendsto (fun n ↦ (⟨densMean S ν (q n) - densMean S ν q₀, hz n⟩ : 𝕍)) l (𝓝 0) := by
    rw [tendsto_subtype_rng]
    simpa using (tendsto_densMean hS ν hqm hq0 hqi hq₀m hq₀0 hq₀i hL1).sub_const (densMean S ν q₀)
  have hcont := (hasStrictFDerivAt_responseTheta_add hS ν hrel).continuousAt.tendsto.comp hzt
  simp only [Function.comp_def, Submodule.coe_zero, add_zero] at hcont
  exact hcont.congr fun n ↦ by simp only [densResponse, add_sub_cancel]

/-- **`L¹` convergence of densities gives convergence of the response velocities.** -/
theorem tendsto_densVel (p : (J → ℝ) →ₗ[ℝ] 𝕍) {k : X → ℝ} (hk : Bdd k) :
    Tendsto (fun n ↦ (densVel hS ν (q n) p k : J → ℝ)) l (𝓝 (densVel hS ν q₀ p k : J → ℝ)) := by
  have h := ((continuous_susceptibility_apply hS ν p).tendsto
    (densResponse hS ν q₀, densForcing S ν q₀ k)).comp
    ((tendsto_densResponse hS ν hqm hq0 hqi hq1 hq₀m hq₀0 hq₀i hq₀1 hL1 hrel).prodMk_nhds
      (tendsto_densForcing hS ν hqm hq0 hqi hq1 hq₀m hq₀0 hq₀i hq₀1 hL1 hk))
  exact h.congr fun n ↦ rfl

/-- **`L¹` convergence of densities gives convergence of the bilinear response form.** -/
theorem tendsto_densBilin (p : (J → ℝ) →ₗ[ℝ] 𝕍) {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    Tendsto (fun n ↦ densBilin hS ν (q n) p k ℓ) l (𝓝 (densBilin hS ν q₀ p k ℓ)) := by
  have hd : Continuous fun x : (J → ℝ) × (J → ℝ) ↦ dotJ x.1 x.2 :=
    continuous_dotJ_comp continuous_fst continuous_snd
  have h := ((hd.tendsto ((densVel hS ν q₀ p k : J → ℝ), densForcing S ν q₀ ℓ)).comp
    ((tendsto_densVel hS ν hqm hq0 hqi hq1 hq₀m hq₀0 hq₀i hq₀1 hL1 hrel p hk).prodMk_nhds
      (tendsto_densForcing hS ν hqm hq0 hqi hq1 hq₀m hq₀0 hq₀i hq₀1 hL1 hℓ))).neg
  exact h.congr fun n ↦ rfl

/-- **`L¹` convergence of densities gives convergence of the effective dimension.** -/
theorem tendsto_densEffDim [DecidableEq J] (p : (J → ℝ) →ₗ[ℝ] 𝕍) :
    Tendsto (fun n ↦ densEffDim hS ν (q n) p) l (𝓝 (densEffDim hS ν q₀ p)) := by
  refine (tendsto_finsetSum _ fun a _ ↦ tendsto_finsetSum _ fun b _ ↦ Tendsto.mul ?_
    (tendsto_densCov_stat hS ν hqm hq0 hqi hq1 hq₀m hq₀0 hq₀i hq₀1 hL1 a b)).neg
  have e : ∀ r : X → ℝ, samplingOp hS ν (densResponse hS ν r) p (Pi.single b 1) a =
      ((CDE (densResponse hS ν r)).symm (p (Pi.single b 1)) : J → ℝ) a := fun _ ↦ rfl
  simp only [e]
  have h := (((continuous_apply a).comp (continuous_susceptibility_apply hS ν p)).tendsto
    (densResponse hS ν q₀, Pi.single b 1)).comp
    ((tendsto_densResponse hS ν hqm hq0 hqi hq1 hq₀m hq₀0 hq₀i hq₀1 hL1 hrel).prodMk_nhds
      tendsto_const_nhds)
  exact h.congr fun n ↦ rfl

end Convergence

end Law

end Laplace.Multi
