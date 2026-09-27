/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.HellingerFisherControl
import Laplace.Multi.FisherTopology

/-!
# Completion points are probability laws

The square-root density `Ψ(θ) = q_θ ∈ L²(ν)` is `½`-Lipschitz for the intrinsic Fisher distance
(`H ≤ ½ d_F`), hence extends to the intrinsic Fisher completion. The extended values are nonnegative
unit vectors of `L²(ν)`, i.e. square roots of probability densities relative to `ν`, and the
extended mean is the mean of that law: `m̄(x)_i = ∫ S_i Ψ̄(x)² dν`. So every completion point is a
probability law absolutely continuous with respect to the base measure, with the prescribed mean.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section L2

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- `‖f‖² = ∫ f f` for `f ∈ L²(ν)`. -/
theorem norm_sq_eq_integral_mul_self (f : Lp ℝ 2 ν) : ‖f‖ ^ 2 = ∫ x, f x * f x ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [RCLike.inner_apply, conj_trivial]

theorem norm_toLp_sq {f : X → ℝ} (hf : MemLp f 2 ν) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x * f x ∂ν := by
  rw [norm_sq_eq_integral_mul_self]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- **Cauchy–Schwarz in `L²`**: `∫ |f − g| |f + g| ≤ ‖f − g‖ ‖f + g‖`. -/
theorem integral_abs_sub_mul_abs_add_le (f g : Lp ℝ 2 ν) :
    ∫ x, |f x - g x| * |f x + g x| ∂ν ≤ ‖f - g‖ * ‖f + g‖ := by
  have hsub : MemLp (fun x ↦ ‖(⇑f - ⇑g) x‖) 2 ν := ((Lp.memLp f).sub (Lp.memLp g)).norm
  have hadd : MemLp (fun x ↦ ‖(⇑f + ⇑g) x‖) 2 ν := ((Lp.memLp f).add (Lp.memLp g)).norm
  have h1 : ∫ x, |f x - g x| * |f x + g x| ∂ν = inner ℝ (hsub.toLp _) (hadd.toLp _) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hsub.coeFn_toLp, hadd.coeFn_toLp] with x hx hy
    rw [RCLike.inner_apply, conj_trivial, hx, hy]
    simp only [Pi.sub_apply, Pi.add_apply, Real.norm_eq_abs]
    ring
  have h2 : ‖hsub.toLp _‖ = ‖f - g‖ := by
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_norm, eLpNorm_congr_ae (Lp.coeFn_sub f g)]
  have h3 : ‖hadd.toLp _‖ = ‖f + g‖ := by
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_norm, eLpNorm_congr_ae (Lp.coeFn_add f g)]
  rw [h1, ← h2, ← h3]
  exact real_inner_le_norm _ _

/-- **A bounded weight against squares is Lipschitz on bounded sets of `L²`.** -/
theorem abs_integral_mul_sq_sub_le [Nonempty X] {φ : X → ℝ} (hφ : Bdd φ) {B : ℝ}
    (hB : ∀ x, |φ x| ≤ B) (f g : Lp ℝ 2 ν) :
    |(∫ x, φ x * (f x * f x) ∂ν) - ∫ x, φ x * (g x * g x) ∂ν| ≤ B * (‖f - g‖ * ‖f + g‖) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  have hff : Integrable (fun x ↦ φ x * (f x * f x)) ν :=
    ((Lp.memLp f).integrable_mul (Lp.memLp f)).bdd_mul hφ.1.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  have hgg : Integrable (fun x ↦ φ x * (g x * g x)) ν :=
    ((Lp.memLp g).integrable_mul (Lp.memLp g)).bdd_mul hφ.1.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  have hint : Integrable (fun x ↦ |f x - g x| * |f x + g x|) ν :=
    ((Lp.memLp f).sub (Lp.memLp g)).norm.integrable_mul ((Lp.memLp f).add (Lp.memLp g)).norm
  rw [← integral_sub hff hgg]
  calc |∫ x, φ x * (f x * f x) - φ x * (g x * g x) ∂ν|
      ≤ ∫ x, |φ x * (f x * f x) - φ x * (g x * g x)| ∂ν := by
        have := norm_integral_le_integral_norm (μ := ν)
          fun x ↦ φ x * (f x * f x) - φ x * (g x * g x)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ x, B * (|f x - g x| * |f x + g x|) ∂ν := by
        refine integral_mono (hff.sub hgg).abs (hint.const_mul B) fun x ↦ ?_
        have e : φ x * (f x * f x) - φ x * (g x * g x) = φ x * ((f x - g x) * (f x + g x)) := by
          ring
        simp only
        rw [e, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (hB x) (by positivity)
    _ = B * ∫ x, |f x - g x| * |f x + g x| ∂ν := integral_const_mul _ _
    _ ≤ B * (‖f - g‖ * ‖f + g‖) :=
        mul_le_mul_of_nonneg_left (integral_abs_sub_mul_abs_add_le ν f g) hB0

/-- **A bounded weight against squares is continuous on `L²`.** -/
theorem continuous_integral_mul_sq [Nonempty X] {φ : X → ℝ} (hφ : Bdd φ) :
    Continuous fun f : Lp ℝ 2 ν ↦ ∫ x, φ x * (f x * f x) ∂ν := by
  obtain ⟨B, hB⟩ := hφ.2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  refine Metric.continuous_iff.2 fun g ε hε ↦ ?_
  refine ⟨min 1 (ε / (B * (1 + 2 * ‖g‖) + 1)), lt_min one_pos (by positivity), fun f hf ↦ ?_⟩
  have hd1 : dist f g < 1 := lt_of_lt_of_le hf (min_le_left _ _)
  have hd2 : dist f g < ε / (B * (1 + 2 * ‖g‖) + 1) := lt_of_lt_of_le hf (min_le_right _ _)
  rw [dist_eq_norm] at hd1 hd2
  rw [Real.dist_eq]
  refine (abs_integral_mul_sq_sub_le ν hφ hB f g).trans_lt ?_
  have hfg : ‖f + g‖ ≤ ‖f - g‖ + 2 * ‖g‖ := by
    calc ‖f + g‖ = ‖(f - g) + (2 : ℝ) • g‖ := by
          congr 1
          rw [two_smul]
          abel
      _ ≤ ‖f - g‖ + ‖(2 : ℝ) • g‖ := norm_add_le _ _
      _ = ‖f - g‖ + 2 * ‖g‖ := by rw [norm_smul, Real.norm_eq_abs, abs_two]
  have h1 : ‖f - g‖ * ‖f + g‖ ≤ ‖f - g‖ * (1 + 2 * ‖g‖) :=
    mul_le_mul_of_nonneg_left (hfg.trans (by linarith)) (norm_nonneg _)
  have hpos : 0 < B * (1 + 2 * ‖g‖) + 1 := by positivity
  rw [lt_div_iff₀ hpos] at hd2
  calc B * (‖f - g‖ * ‖f + g‖) ≤ B * (‖f - g‖ * (1 + 2 * ‖g‖)) :=
        mul_le_mul_of_nonneg_left h1 hB0
    _ = ‖f - g‖ * (B * (1 + 2 * ‖g‖)) := by ring
    _ < ε := by nlinarith [norm_nonneg (f - g), hB0, norm_nonneg g]

end L2

section Laws

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] in
theorem memLp_rootDens (θ : J → ℝ) : MemLp (rootDens S ν θ) 2 ν := by
  obtain ⟨C, hC⟩ := exists_rootDens_le hS ν θ
  exact MemLp.of_bound (measurable_rootDens hS ν θ).aestronglyMeasurable C (ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (rootDens_nonneg S ν θ x)]
    exact hC x)

/-- The square-root density as an element of `L²(ν)`. -/
noncomputable def rootDensLp (θ : J → ℝ) : Lp ℝ 2 ν := (memLp_rootDens hS ν θ).toLp _

omit [Nonempty X] in
theorem norm_rootDensLp (θ : J → ℝ) : ‖rootDensLp hS ν θ‖ = 1 := by
  have h := norm_toLp_sq ν (memLp_rootDens hS ν θ)
  simp_rw [← sq] at h
  rw [integral_rootDens_sq hS ν] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

omit [Nonempty X] in
/-- The `L²` distance of square-root densities is the Hellinger distance. -/
theorem dist_rootDensLp (θ η : J → ℝ) :
    dist (rootDensLp hS ν θ) (rootDensLp hS ν η) = hellingerDist S ν θ η := by
  rw [dist_eq_norm, rootDensLp, rootDensLp, ← MemLp.toLp_sub, hellingerDist,
    ← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq]
  rfl

variable [Nonempty J]

/-- **The square-root density is `½`-Lipschitz for the intrinsic Fisher distance.** -/
theorem lipschitzWith_rootDensLp :
    LipschitzWith (Real.toNNReal (1 / 2))
      fun p : FisherPoint hS ν ↦ rootDensLp hS ν (p.param : J → ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  rw [dist_rootDensLp hS ν, Real.coe_toNNReal _ (by norm_num), FisherPoint.dist_eq,
    fisherDist_comm hS ν]
  exact hellingerDist_le_half_fisherDist hS ν q.param p.param

/-- **The extended square-root density on the intrinsic Fisher completion.** -/
noncomputable def rootDensExt : FisherCompletion hS ν → Lp ℝ 2 ν :=
  UniformSpace.Completion.extension fun p : FisherPoint hS ν ↦ rootDensLp hS ν (p.param : J → ℝ)

theorem rootDensExt_coe (p : FisherPoint hS ν) :
    rootDensExt hS ν (p : FisherCompletion hS ν) = rootDensLp hS ν (p.param : J → ℝ) :=
  UniformSpace.Completion.extension_coe (lipschitzWith_rootDensLp hS ν).uniformContinuous p

theorem lipschitzWith_rootDensExt :
    LipschitzWith (Real.toNNReal (1 / 2)) (rootDensExt hS ν) :=
  (lipschitzWith_rootDensLp hS ν).completion_extension

theorem continuous_rootDensExt : Continuous (rootDensExt hS ν) :=
  UniformSpace.Completion.continuous_extension

/-- Extended square-root densities are unit vectors. -/
theorem norm_rootDensExt (x : FisherCompletion hS ν) : ‖rootDensExt hS ν x‖ = 1 := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_norm.comp (continuous_rootDensExt hS ν)) continuous_const) fun p ↦ ?_
  rw [rootDensExt_coe, norm_rootDensLp]

/-- Extended square-root densities are nonnegative. -/
theorem rootDensExt_nonneg (x : FisherCompletion hS ν) : 0 ≤ rootDensExt hS ν x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_nonneg.preimage (continuous_rootDensExt hS ν)) fun p ↦ ?_
  rw [rootDensExt_coe, ← Lp.coeFn_nonneg]
  filter_upwards [(memLp_rootDens hS ν _).coeFn_toLp] with x hx
  rw [Pi.zero_apply, rootDensLp, hx]
  exact rootDens_nonneg S ν _ x

/-- Extended square-root densities are square roots of probability densities. -/
theorem integral_rootDensExt_sq (x : FisherCompletion hS ν) :
    ∫ y, rootDensExt hS ν x y * rootDensExt hS ν x y ∂ν = 1 := by
  rw [← norm_sq_eq_integral_mul_self, norm_rootDensExt, one_pow]

/-- **The extended mean is the mean of the extended law.** -/
theorem meanExt_eq_integral_rootDensExt (x : FisherCompletion hS ν) (i : J) :
    meanExt hS ν x i = ∫ y, S i y * (rootDensExt hS ν x y * rootDensExt hS ν x y) ∂ν := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    ((continuous_apply i).comp (continuous_meanExt hS ν))
    ((continuous_integral_mul_sq ν (hS i)).comp (continuous_rootDensExt hS ν))) fun p ↦ ?_
  rw [meanExt_coe, rootDensExt_coe, ← mean_familyMeasure_one_zero hS ν]
  beta_reduce
  rw [integral_famDens_mul hS ν]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_rootDens hS ν _).coeFn_toLp] with y hy
  rw [rootDensLp, hy, ← sq, rootDens_sq hS ν]
  ring

end Laws

end Laplace.Multi
