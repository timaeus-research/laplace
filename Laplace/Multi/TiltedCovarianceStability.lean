/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiltedFisherCompactConvergence
import Laplace.Multi.BoundedTiltCompletionAction
import Laplace.Multi.NormalTiltFisherComparison

/-!
# Covariance stability along the completion action

Measure-level form of the `L¹` stability of covariance forms: tilting a law with density `q` by a
bounded `g` is the law with density `tiltedDens ν g q` (`tilted_withDensity_ofReal`), so covariances
of tilted laws are `L¹`-stable uniformly over bounded common tilts
(`abs_lawCov_tilted_withDensity_sub_le`). The density of a family law is `L¹`-close to the density
of a completion law at Fisher-close points, `‖p_θ − ρ_x‖₁ ≤ 2 ‖√p_θ − √ρ_x‖₂`
(`integral_abs_famDens_sub_le`), and along the completion action

`|Cov_{P_{θ+a}}(f,f') − Cov_{Q_{tiltExt a x}}(f,f')| ≤ 6 ‖f‖_∞ ‖f'‖_∞ e^{2K} ‖p_θ − ρ_x‖₁`

(`abs_lawCov_family_add_sub_completion_tiltExt_le`), uniformly over `|⟨a,S⟩| ≤ K`. This is the
analytic input for the nonexpansion of face embeddings: the Fisher forms of ambient paths near an
accessible boundary point converge to the Fisher forms of the corresponding face-family paths.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section TiltedLaw

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
  {q : X → ℝ} (hqm : AEMeasurable q ν) (hq0 : ∀ x, 0 ≤ q x) (hqi : Integrable q ν)
  {g : X → ℝ} (hg : Bdd g)
include hqm hq0 hqi hg

omit [IsProbabilityMeasure ν] hqi in
/-- **Tilting a law with density `q` by `g` is the law with density `tiltedDens ν g q`.** -/
theorem tilted_withDensity_ofReal :
    (ν.withDensity fun x ↦ ENNReal.ofReal (q x)).tilted g =
      ν.withDensity fun x ↦ ENNReal.ofReal (tiltedDens ν g q x) := by
  rw [Measure.tilted, integral_withDensity_ofReal_ae ν hqm hq0]
  have hf : AEMeasurable (fun x ↦ ENNReal.ofReal (q x)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable hqm
  have hg' : AEMeasurable (fun x ↦ ENNReal.ofReal (Real.exp (g x) / ∫ y, q y * Real.exp (g y) ∂ν))
      ν := (ENNReal.measurable_ofReal.comp (hg.1.exp.div_const _)).aemeasurable
  rw [← withDensity_mul₀ hf hg']
  congr 1
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (hq0 x), tiltedDens, mul_div_assoc]

omit [IsProbabilityMeasure ν] hq0 hqi in
theorem aemeasurable_tiltedDens : AEMeasurable (tiltedDens ν g q) ν :=
  (hqm.mul hg.1.exp.aemeasurable).div_const _

omit [IsProbabilityMeasure ν] hqm hqi hg in
theorem tiltedDens_nonneg (x : X) : 0 ≤ tiltedDens ν g q x := by
  unfold tiltedDens
  have hZ : 0 ≤ ∫ y, q y * Real.exp (g y) ∂ν :=
    integral_nonneg fun y ↦ mul_nonneg (hq0 y) (Real.exp_pos _).le
  exact div_nonneg (mul_nonneg (hq0 x) (Real.exp_pos _).le) hZ

omit [IsProbabilityMeasure ν] hqm hq0 in
theorem integrable_tiltedDens {K : ℝ} (hK : ∀ x, |g x| ≤ K) :
    Integrable (tiltedDens ν g q) ν :=
  (integrable_mul_exp ν hg hK hqi).div_const _

omit [IsProbabilityMeasure ν] hqm in
theorem integral_tiltedDens (hq1 : ∫ x, q x ∂ν = 1) {K : ℝ} (hK : ∀ x, |g x| ≤ K) :
    ∫ x, tiltedDens ν g q x ∂ν = 1 := by
  have hZ : 0 < ∫ y, q y * Real.exp (g y) ∂ν :=
    (Real.exp_pos _).trans_le (exp_neg_le_integral_mul_exp ν hq0 hqi hq1 hg hK)
  unfold tiltedDens
  rw [integral_div, div_self hZ.ne']

end TiltedLaw

section TiltedStability

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
  {q₁ q₂ : X → ℝ} (hq₁m : AEMeasurable q₁ ν) (hq₁0 : ∀ x, 0 ≤ q₁ x) (hq₁i : Integrable q₁ ν)
  (hq₁1 : ∫ x, q₁ x ∂ν = 1) (hq₂m : AEMeasurable q₂ ν) (hq₂0 : ∀ x, 0 ≤ q₂ x)
  (hq₂i : Integrable q₂ ν) (hq₂1 : ∫ x, q₂ x ∂ν = 1) {g : X → ℝ} (hg : Bdd g) {K : ℝ}
  (hK : ∀ x, |g x| ≤ K)
include hq₁m hq₁0 hq₁i hq₁1 hq₂m hq₂0 hq₂i hq₂1 hg hK

omit [IsProbabilityMeasure ν] in
/-- **Covariances of tilted laws are `L¹`-stable, uniformly over bounded common tilts**:
`|Cov_{Q₁^g}(f,f') − Cov_{Q₂^g}(f,f')| ≤ 3 ‖f‖_∞ ‖f'‖_∞ · 2 e^{2K} ‖q₁ − q₂‖₁`. -/
theorem abs_lawCov_tilted_withDensity_sub_le {f f' : X → ℝ} (hf : Measurable f)
    (hf' : Measurable f') {L L' : ℝ} (hL0 : 0 ≤ L) (hL'0 : 0 ≤ L') (hL : ∀ x, |f x| ≤ L)
    (hL' : ∀ x, |f' x| ≤ L') :
    |lawCov ((ν.withDensity fun x ↦ ENNReal.ofReal (q₁ x)).tilted g) f f' -
        lawCov ((ν.withDensity fun x ↦ ENNReal.ofReal (q₂ x)).tilted g) f f'| ≤
      3 * L * L' * (2 * Real.exp (2 * K) * ∫ x, |q₁ x - q₂ x| ∂ν) := by
  rw [tilted_withDensity_ofReal ν hq₁m hq₁0 hg, tilted_withDensity_ofReal ν hq₂m hq₂0 hg]
  have h := abs_lawCov_withDensity_sub_le ν (aemeasurable_tiltedDens ν hq₁m hg)
    (tiltedDens_nonneg ν hq₁0) (integrable_tiltedDens ν hq₁i hg hK)
    (aemeasurable_tiltedDens ν hq₂m hg) (tiltedDens_nonneg ν hq₂0)
    (integrable_tiltedDens ν hq₂i hg hK) (integral_tiltedDens ν hq₁0 hq₁i hg hq₁1 hK)
    (integral_tiltedDens ν hq₂0 hq₂i hg hq₂1 hK) hf hf' hL0 hL hL'
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (by norm_num) hL0) hL'0))
  exact integral_abs_tiltedDens_sub_le ν hq₁0 hq₁i hq₁1 hq₂0 hq₂i hq₂1 hg hK

end TiltedStability

section Completion

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The density of a completion law. -/
local notation "ρ" x => fun y ↦ rootDensExt hS ν x y * rootDensExt hS ν x y

/-- **The family density is `L¹`-close to the completion density at Fisher-close points**:
`‖p_θ − ρ_x‖₁ ≤ 2 ‖√p_θ − √ρ_x‖₂`. -/
theorem integral_abs_famDens_sub_le (θ : J → ℝ) (x : FisherCompletion hS ν) :
    ∫ y, |famDens S ν θ y - rootDensExt hS ν x y * rootDensExt hS ν x y| ∂ν ≤
      2 * ‖rootDensLp hS ν θ - rootDensExt hS ν x‖ := by
  have hcs := integral_abs_sub_mul_abs_add_le ν (rootDensLp hS ν θ) (rootDensExt hS ν x)
  have e : ∫ y, |famDens S ν θ y - rootDensExt hS ν x y * rootDensExt hS ν x y| ∂ν =
      ∫ y, |rootDensLp hS ν θ y - rootDensExt hS ν x y| *
        |rootDensLp hS ν θ y + rootDensExt hS ν x y| ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_rootDens hS ν θ).coeFn_toLp] with y hy
    rw [rootDensLp, hy, ← rootDens_sq hS ν, ← abs_mul]
    congr 1
    ring
  rw [e]
  refine hcs.trans ?_
  have hn : ‖rootDensLp hS ν θ + rootDensExt hS ν x‖ ≤ 2 := by
    calc ‖rootDensLp hS ν θ + rootDensExt hS ν x‖ ≤
          ‖rootDensLp hS ν θ‖ + ‖rootDensExt hS ν x‖ := norm_add_le _ _
      _ = 2 := by rw [norm_rootDensLp, norm_rootDensExt]; norm_num
  calc ‖rootDensLp hS ν θ - rootDensExt hS ν x‖ * ‖rootDensLp hS ν θ + rootDensExt hS ν x‖ ≤
        ‖rootDensLp hS ν θ - rootDensExt hS ν x‖ * 2 :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = 2 * ‖rootDensLp hS ν θ - rootDensExt hS ν x‖ := mul_comm _ _

/-- The `L¹` distance between family densities and the completion density tends to zero along
a sequence converging in the completion. -/
theorem tendsto_integral_abs_famDens_sub_completionDens {u : ℕ → FisherPoint hS ν}
    {x : FisherCompletion hS ν} (hu : Tendsto (fun n ↦ (u n : FisherCompletion hS ν)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ ∫ y, |famDens S ν ((u n).param : J → ℝ) y -
      rootDensExt hS ν x y * rootDensExt hS ν x y| ∂ν) atTop (𝓝 0) := by
  have h := ((continuous_rootDensExt hS ν).tendsto x).comp hu
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  have h2 : Tendsto (fun n ↦ 2 * ‖rootDensLp hS ν ((u n).param : J → ℝ) - rootDensExt hS ν x‖)
      atTop (𝓝 0) := by
    have := h.const_mul 2
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    simp only [Function.comp, rootDensExt_coe]
  refine squeeze_zero (fun n ↦ integral_nonneg fun y ↦ abs_nonneg _)
    (fun n ↦ integral_abs_famDens_sub_le hS ν _ x) h2

theorem aemeasurable_completionDens (x : FisherCompletion hS ν) :
    AEMeasurable (fun y ↦ rootDensExt hS ν x y * rootDensExt hS ν x y) ν :=
  aemeasurable_rootDensExt_mul_self hS ν x

/-- **Covariance stability along the completion action**: for `|⟨a,S⟩| ≤ K`,
`|Cov_{P_{θ+a}}(f,f') − Cov_{Q_{tiltExt a x}}(f,f')| ≤ 6 ‖f‖_∞ ‖f'‖_∞ e^{2K} ‖p_θ − ρ_x‖₁`. -/
theorem abs_lawCov_family_add_sub_completion_tiltExt_le (θ : J → ℝ) (x : FisherCompletion hS ν)
    (a : 𝕍) {K : ℝ} (hK : ∀ y, |dirLoss S (a : J → ℝ) y| ≤ K) {f f' : X → ℝ}
    (hf : Measurable f) (hf' : Measurable f') {L L' : ℝ} (hL0 : 0 ≤ L) (hL'0 : 0 ≤ L')
    (hL : ∀ y, |f y| ≤ L) (hL' : ∀ y, |f' y| ≤ L') :
    |lawCov (Pfam (θ + a)) f f' - lawCov (completionLaw hS ν (tiltExt hS ν a x)) f f'| ≤
      3 * L * L' * (2 * Real.exp (2 * K) *
        ∫ y, |famDens S ν θ y - rootDensExt hS ν x y * rootDensExt hS ν x y| ∂ν) := by
  have e1 : Pfam (θ + a) = (Pfam θ).tilted fun y ↦ -dirLoss S (a : J → ℝ) y := by
    rw [familyMeasure_add_eq_tilted hS ν θ a 0]
    congr 1
    funext y
    rw [sub_zero]
  rw [e1, completionLaw_tiltExt hS ν a x, familyMeasure_eq_withDensity_famDens, completionLaw]
  exact abs_lawCov_tilted_withDensity_sub_le ν (measurable_famDens hS ν θ).aemeasurable
    (famDens_nonneg hS ν θ) (integrable_famDens hS ν θ) (integral_famDens hS ν θ)
    (aemeasurable_completionDens hS ν x) (fun y ↦ mul_self_nonneg _)
    (integrable_rootDensExt_mul_self hS ν x) (integral_rootDensExt_sq hS ν x)
    (bdd_neg (bdd_dirLoss hS _)) (fun y ↦ by rw [abs_neg]; exact hK y) hf hf' hL0 hL'0 hL hL'

end Completion

end Laplace.Multi
