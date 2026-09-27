/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherCompletionLaws
import Laplace.Multi.FacetFisherAccess

/-!
# The Hellinger limit of a normal ray is the face-conditioned law

Along the ray `θ_r = v − r u` towards the exposed face `A = {⟨u,S⟩ = β}` (`⟨u,S⟩ ≤ β` a.e.,
`ν(A) > 0`), the square-root densities converge in `L²(ν)` to the **face root density**
`q_F = 1_A e^{−⟨v,S⟩/2}/√Z_F(v)`, where `Z_F(v) = ∫_A e^{−⟨v,S⟩} dν`. The proof uses only the
exact affinity `∫ q_{θ_r} q_F = √(Z_F(v)/A_r)` with
`A_r = e^{−rβ} Z(θ_r) = ∫ e^{−⟨v,S⟩} e^{r(⟨u,S⟩−β)}`,
which tends to `Z_F(v)` by dominated convergence, and the norm identity
`‖q_{θ_r} − q_F‖² = 2 − 2∫ q_{θ_r} q_F`. No accessibility of the ray is needed.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Defs

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (S : J → X → ℝ) (ν : Measure X)
  (u : J → ℝ) (β : ℝ)

/-- The face partition function `Z_F(v) = ∫_A e^{−⟨v,S⟩} dν`. -/
noncomputable def faceZ (v : J → ℝ) : ℝ := ∫ x in {x | dirLoss S u x = β}, famWeight S v x ∂ν

/-- The face root density `q_F = 1_A e^{−⟨v,S⟩/2}/√Z_F(v)`. -/
noncomputable def faceRootDens (v : J → ℝ) (x : X) : ℝ :=
  {x | dirLoss S u x = β}.indicator (fun x ↦ Real.exp (-dirLoss S v x / 2)) x / √(faceZ S ν u β v)

/-- The normalised ray partition function `A_r = ∫ e^{−⟨v,S⟩} e^{r(⟨u,S⟩ − β)} dν`. -/
noncomputable def rayNorm (v : J → ℝ) (r : ℝ) : ℝ :=
  ∫ x, famWeight S v x * Real.exp (r * (dirLoss S u x - β)) ∂ν

end Defs

section Limit

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (u : J → ℝ) (β : ℝ)
include hS

theorem faceZ_pos (hp : 0 < ν.real {x | dirLoss S u x = β}) (v : J → ℝ) :
    0 < faceZ S ν u β v := by
  obtain ⟨-, K, hK⟩ := bdd_dirLoss hS v
  have hA := measurableSet_faceFibre hS u β
  have h1 := setIntegral_ge_of_const_le hA (measure_ne_top ν _)
    (fun x _ ↦ (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hK x)).2]) :
      Real.exp (-K) ≤ famWeight S v x)) (integrable_famWeight hS ν v).integrableOn
  rw [smul_eq_mul] at h1
  exact lt_of_lt_of_le (by positivity) h1

omit hS [IsProbabilityMeasure ν] in
theorem rayNorm_eq (v : J → ℝ) (r : ℝ) :
    rayNorm S ν u β v r = Real.exp (-(r * β)) * famZ S ν (v - r • u) := by
  rw [rayNorm, famZ, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [famWeight, dirLoss_sub', dirLoss_smul]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem rayNorm_pos (v : J → ℝ) (r : ℝ) : 0 < rayNorm S ν u β v r := by
  rw [rayNorm_eq ν u β]
  exact mul_pos (Real.exp_pos _) (famZ_pos hS ν _)

omit hS [IsProbabilityMeasure ν] in
theorem famZ_eq_rayNorm (v : J → ℝ) (r : ℝ) :
    famZ S ν (v - r • u) = Real.exp (r * β) * rayNorm S ν u β v r := by
  rw [rayNorm_eq ν u β, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- **`A_r → Z_F(v)`** by dominated convergence. -/
theorem tendsto_rayNorm (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) (v : J → ℝ) :
    Tendsto (fun n : ℕ ↦ rayNorm S ν u β v n) atTop (𝓝 (faceZ S ν u β v)) := by
  have hA := measurableSet_faceFibre hS u β
  rw [faceZ, ← integral_indicator hA]
  refine tendsto_integral_of_dominated_convergence (famWeight S v) (fun n ↦ ?_)
    (integrable_famWeight hS ν v) (fun n ↦ ?_) ?_
  · exact ((bdd_famWeight hS v).1.mul
      ((((bdd_dirLoss hS u).1.sub_const β).const_mul (n : ℝ)).exp)).aestronglyMeasurable
  · filter_upwards [hβ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_pos (famWeight_pos v x) (Real.exp_pos _)).le]
    calc famWeight S v x * Real.exp (n * (dirLoss S u x - β))
        ≤ famWeight S v x * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith [hx]))
            (famWeight_pos v x).le
      _ = famWeight S v x := mul_one _
  · filter_upwards [hβ] with x hx
    rcases eq_or_lt_of_le hx with h | h
    · have hmem : x ∈ {x | dirLoss S u x = β} := h
      simp only [Set.indicator_of_mem hmem, h, sub_self, mul_zero, Real.exp_zero, mul_one]
      exact tendsto_const_nhds
    · have hnot : x ∉ {x | dirLoss S u x = β} := h.ne
      rw [Set.indicator_of_notMem hnot]
      have h1 : Tendsto (fun n : ℕ ↦ Real.exp (n * (dirLoss S u x - β))) atTop (𝓝 0) := by
        refine Real.tendsto_exp_atBot.comp ?_
        exact tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg (by linarith)
      simpa using h1.const_mul (famWeight S v x)

omit [IsProbabilityMeasure ν] in
theorem measurable_faceRootDens (v : J → ℝ) : Measurable (faceRootDens S ν u β v) :=
  (Measurable.indicator ((bdd_dirLoss hS v).1.neg.div_const 2).exp
    (measurableSet_faceFibre hS u β)).div_const _

omit hS [IsProbabilityMeasure ν] in
theorem faceRootDens_nonneg (v : J → ℝ) (x : X) : 0 ≤ faceRootDens S ν u β v x := by
  unfold faceRootDens
  refine div_nonneg ?_ (Real.sqrt_nonneg _)
  exact Set.indicator_nonneg (fun x _ ↦ (Real.exp_pos _).le) x

omit [IsProbabilityMeasure ν] in
theorem bdd_faceRootDens (v : J → ℝ) : Bdd (faceRootDens S ν u β v) := by
  obtain ⟨-, K, hK⟩ := bdd_dirLoss hS v
  refine ⟨measurable_faceRootDens hS ν u β v, Real.exp (K / 2) / √(faceZ S ν u β v), fun x ↦ ?_⟩
  rw [abs_of_nonneg (faceRootDens_nonneg ν u β v x), faceRootDens]
  refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  by_cases hx : x ∈ {x | dirLoss S u x = β}
  · rw [Set.indicator_of_mem hx]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hK x)).1])
  · rw [Set.indicator_of_notMem hx]
    positivity

theorem memLp_faceRootDens (v : J → ℝ) : MemLp (faceRootDens S ν u β v) 2 ν := by
  obtain ⟨hm, C, hC⟩ := bdd_faceRootDens hS ν u β v
  exact MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs]
    exact hC x)

/-- The product `q_{θ_r} q_F` is the indicator of the face times `e^{−⟨v,S⟩}/(√A_r √Z_F)`. -/
theorem rootDens_mul_faceRootDens (hp : 0 < ν.real {x | dirLoss S u x = β}) (v : J → ℝ) (r : ℝ)
    (x : X) :
    rootDens S ν (v - r • u) x * faceRootDens S ν u β v x =
      {x | dirLoss S u x = β}.indicator
        (fun x ↦ famWeight S v x / (√(rayNorm S ν u β v r) * √(faceZ S ν u β v))) x := by
  by_cases hx : x ∈ {x | dirLoss S u x = β}
  · have hx' : dirLoss S u x = β := hx
    rw [Set.indicator_of_mem hx, faceRootDens, Set.indicator_of_mem hx, rootDens_eq hS ν,
      famZ_eq_rayNorm ν u β, dirLoss_sub']
    simp only [dirLoss_smul]
    rw [hx', Real.sqrt_mul (Real.exp_pos _).le, ← Real.exp_half, famWeight]
    have e1 : Real.exp (-(dirLoss S v x - r * β) / 2) =
        Real.exp (-dirLoss S v x / 2) * Real.exp (r * β / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-dirLoss S v x) =
        Real.exp (-dirLoss S v x / 2) * Real.exp (-dirLoss S v x / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e1, e2]
    have h1 := Real.exp_pos (r * β / 2)
    have h2 := Real.sqrt_pos.2 (rayNorm_pos hS ν u β v r)
    have h3 := Real.sqrt_pos.2 (faceZ_pos hS ν u β hp v)
    field_simp
  · rw [Set.indicator_of_notMem hx, faceRootDens, Set.indicator_of_notMem hx, zero_div, mul_zero]

/-- **The affinity of the ray with the face root density**: `∫ q_{θ_r} q_F = √(Z_F/A_r)`. -/
theorem integral_rootDens_mul_faceRootDens (hp : 0 < ν.real {x | dirLoss S u x = β})
    (v : J → ℝ) (r : ℝ) :
    ∫ x, rootDens S ν (v - r • u) x * faceRootDens S ν u β v x ∂ν =
      √(faceZ S ν u β v / rayNorm S ν u β v r) := by
  have hA := measurableSet_faceFibre hS u β
  have hZ := faceZ_pos hS ν u β hp v
  have hR := rayNorm_pos hS ν u β v r
  simp_rw [rootDens_mul_faceRootDens hS ν u β hp v r]
  rw [integral_indicator hA, integral_div, ← faceZ, Real.sqrt_div' _ hR.le,
    div_eq_div_iff (mul_pos (Real.sqrt_pos.2 hR) (Real.sqrt_pos.2 hZ)).ne'
      (Real.sqrt_pos.2 hR).ne',
    mul_comm (√(rayNorm S ν u β v r)) (√(faceZ S ν u β v)), ← mul_assoc,
    Real.mul_self_sqrt hZ.le]

/-- `q_F² = 1_A e^{−⟨v,S⟩}/Z_F(v)`. -/
theorem faceRootDens_mul_self (hp : 0 < ν.real {x | dirLoss S u x = β}) (v : J → ℝ) (x : X) :
    faceRootDens S ν u β v x * faceRootDens S ν u β v x =
      {x | dirLoss S u x = β}.indicator (famWeight S v) x / faceZ S ν u β v := by
  have hZ := faceZ_pos hS ν u β hp v
  by_cases hx : x ∈ {x | dirLoss S u x = β}
  · simp only [faceRootDens, Set.indicator_of_mem hx]
    rw [div_mul_div_comm, ← Real.exp_add, Real.mul_self_sqrt hZ.le, famWeight,
      show -dirLoss S v x / 2 + -dirLoss S v x / 2 = -dirLoss S v x by ring]
  · simp [faceRootDens, Set.indicator_of_notMem hx]

theorem integral_faceRootDens_mul_self (hp : 0 < ν.real {x | dirLoss S u x = β}) (v : J → ℝ) :
    ∫ x, faceRootDens S ν u β v x * faceRootDens S ν u β v x ∂ν = 1 := by
  have hA := measurableSet_faceFibre hS u β
  have hZ := faceZ_pos hS ν u β hp v
  simp_rw [faceRootDens_mul_self hS ν u β hp v]
  rw [integral_div, integral_indicator hA, ← faceZ, div_self hZ.ne']

/-- **The norm identity** `‖q_{θ_r} − q_F‖² = 2 − 2√(Z_F/A_r)`. -/
theorem integral_rootDens_sub_faceRootDens_sq (hp : 0 < ν.real {x | dirLoss S u x = β})
    (v : J → ℝ) (r : ℝ) :
    ∫ x, (rootDens S ν (v - r • u) x - faceRootDens S ν u β v x) *
        (rootDens S ν (v - r • u) x - faceRootDens S ν u β v x) ∂ν =
      2 - 2 * √(faceZ S ν u β v / rayNorm S ν u β v r) := by
  have hq := bdd_rootDens hS ν (v - r • u)
  have hf := bdd_faceRootDens hS ν u β v
  have e : ∀ x, (rootDens S ν (v - r • u) x - faceRootDens S ν u β v x) *
      (rootDens S ν (v - r • u) x - faceRootDens S ν u β v x) =
      rootDens S ν (v - r • u) x * rootDens S ν (v - r • u) x -
        2 * (rootDens S ν (v - r • u) x * faceRootDens S ν u β v x) +
        faceRootDens S ν u β v x * faceRootDens S ν u β v x := fun x ↦ by ring
  simp_rw [e]
  have i1 : Integrable (fun x ↦ rootDens S ν (v - r • u) x * rootDens S ν (v - r • u) x -
      2 * (rootDens S ν (v - r • u) x * faceRootDens S ν u β v x)) ν :=
    (integrable_of_bdd_prob ν (hq.mul hq)).sub ((integrable_of_bdd_prob ν (hq.mul hf)).const_mul _)
  have i2 : Integrable (fun x ↦ faceRootDens S ν u β v x * faceRootDens S ν u β v x) ν :=
    integrable_of_bdd_prob ν (hf.mul hf)
  have i3 : Integrable (fun x ↦ 2 * (rootDens S ν (v - r • u) x * faceRootDens S ν u β v x)) ν :=
    (integrable_of_bdd_prob ν (hq.mul hf)).const_mul _
  rw [integral_add i1 i2, integral_sub (integrable_of_bdd_prob ν (hq.mul hq)) i3,
    integral_const_mul, integral_rootDens_mul_faceRootDens hS ν u β hp,
    integral_faceRootDens_mul_self hS ν u β hp]
  have h1 := integral_rootDens_sq hS ν (v - r • u)
  simp_rw [sq] at h1
  rw [h1]
  ring

/-- **The Hellinger distance of the ray to the face root density tends to zero.** -/
theorem tendsto_integral_rootDens_sub_faceRootDens_sq (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) (v : J → ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ x, (rootDens S ν (v - (n : ℝ) • u) x - faceRootDens S ν u β v x) *
      (rootDens S ν (v - (n : ℝ) • u) x - faceRootDens S ν u β v x) ∂ν) atTop (𝓝 0) := by
  simp_rw [integral_rootDens_sub_faceRootDens_sq hS ν u β hp v]
  have hZ := faceZ_pos hS ν u β hp v
  have h1 : Tendsto (fun n : ℕ ↦ faceZ S ν u β v / rayNorm S ν u β v n) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := faceZ S ν u β v)).div (tendsto_rayNorm hS ν u β hβ v) hZ.ne'
    rwa [div_self hZ.ne'] at this
  have h2 : Tendsto (fun n : ℕ ↦ √(faceZ S ν u β v / rayNorm S ν u β v n)) atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp h1
    rwa [Real.sqrt_one] at this
  have := (tendsto_const_nhds (x := (2 : ℝ))).sub (h2.const_mul 2)
  simpa using this

/-- **The square-root densities of the normal ray converge in `L²(ν)` to the face root density.** -/
theorem tendsto_rootDensLp_ray (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) (v : J → ℝ) :
    Tendsto (fun n : ℕ ↦ rootDensLp hS ν (v - (n : ℝ) • u)) atTop
      (𝓝 ((memLp_faceRootDens hS ν u β v).toLp _)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have e : ∀ n : ℕ, dist (rootDensLp hS ν (v - (n : ℝ) • u))
      ((memLp_faceRootDens hS ν u β v).toLp _) =
      √(∫ x, (rootDens S ν (v - (n : ℝ) • u) x - faceRootDens S ν u β v x) *
        (rootDens S ν (v - (n : ℝ) • u) x - faceRootDens S ν u β v x) ∂ν) := fun n ↦ by
    rw [dist_eq_norm, rootDensLp, ← MemLp.toLp_sub, ← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq]
    rfl
  simp_rw [e]
  have := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_integral_rootDens_sub_faceRootDens_sq hS ν u β hβ hp v)
  rwa [Real.sqrt_zero] at this

end Limit

end Laplace.Multi
