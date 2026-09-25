/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ExposedFace

/-!
# Null faces cost infinite information; positive faces are reached at their entry cost

Two faces of the boundary rate geometry, for a feature law `ν` with `u·R ≤ β` a.e. and the face
event `F = {u·R = β}`:

* **the rate vanishes at the mean of any law** (`genRate_mean_eq_zero`, Jensen's inequality for the
  exponential), so on a positive-mass face the conditional mean `M_F = E_{ν_F} R` lies on the face
  hyperplane and has exactly the entry cost, `𝓘(M_F) = −log p_F` (`genRate_condMean`): a
  positive-mass face supplies a boundary point of finite rate;
* **on a null face the rate is infinite** (`genRate_eq_top_of_null_face`): if `ν(F) = 0` then for
  every `M` with `u·M = β`, `𝓘(M) = ⊤`, because `Z_λ = E_ν e^{−λ(β − u·R)} → 0` by dominated
  convergence and the Chernoff score at `λu` is `−log Z_λ`.

Together with `ExposedFace` these are the pointwise halves of the boundary-barrier criterion: the
rate blows up at every boundary point exactly when every supporting face is null, and a positive
face is reached along a radial segment with rate at most `(1−ε)(−log p_F)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]

section

variable (ν : Measure X) [IsProbabilityMeasure ν] {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hR

omit hR in
theorem integrable_of_bdd_prob {f : X → ℝ} (hf : Bdd f) : Integrable f ν := by
  obtain ⟨hfm, K, hK⟩ := hf
  exact Integrable.of_bound hfm.aestronglyMeasurable K
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hK x)

/-- `q · E_ν R = E_ν (q·R)`. -/
theorem dotJ_integral_eq (q : ι → ℝ) :
    dotJ q (fun i ↦ ∫ x, R i x ∂ν) = ∫ x, dirLoss R q x ∂ν := by
  simp only [dotJ, dirLoss]
  rw [integral_finsetSum _ fun i _ ↦ (integrable_of_bdd_prob ν (hR i)).const_mul (q i)]
  exact Finset.sum_congr rfl fun i _ ↦ (integral_const_mul _ _).symm

/-- **The rate vanishes at the mean of the law** (Jensen). -/
theorem genRate_mean_eq_zero : genRate ν R (fun i ↦ ∫ x, R i x ∂ν) = 0 := by
  refine le_antisymm (iSup_le fun q ↦ ?_) zero_le
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, dotJ_integral_eq ν hR q, sub_nonpos]
  unfold featCgf
  rw [Real.le_log_iff_exp_le (integral_exp_pos (integrable_exp_dirLoss ν hR q))]
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ ↦ mem_univ _) (integrable_of_bdd_prob ν (bdd_dirLoss hR q))
    (integrable_exp_dirLoss ν hR q)

/-- The conditional mean of a face lies on the face hyperplane. -/
theorem dotJ_condMean {u : ι → ℝ} {β : ℝ} (hp : 0 < ν.real {x | dirLoss R u x = β}) :
    dotJ u (fun i ↦ ∫ x, R i x ∂faceMeasure ν {x | dirLoss R u x = β}) = β := by
  obtain ⟨hum, _, _⟩ := bdd_dirLoss hR u
  have hF0 : ν {x | dirLoss R u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  rw [dotJ_integral_eq _ hR u, integral_faceMeasure]
  have hF : MeasurableSet {x | dirLoss R u x = β} := measurableSet_eq_fun hum measurable_const
  rw [setIntegral_congr_fun hF (fun x hx ↦ hx), setIntegral_const, smul_eq_mul]
  field_simp

/-- **A positive face is reached at its entry cost**: `𝓘(M_F) = −log p_F` at the conditional mean
`M_F = E_{ν_F} R`. -/
theorem genRate_condMean {u : ι → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss R u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss R u x = β}) :
    genRate ν R (fun i ↦ ∫ x, R i x ∂faceMeasure ν {x | dirLoss R u x = β}) =
      ENNReal.ofReal (-Real.log (ν.real {x | dirLoss R u x = β})) := by
  have hF0 : ν {x | dirLoss R u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  rw [genRate_face_eq ν hR hβ hp (dotJ_condMean ν hR hp), genRate_mean_eq_zero _ hR, add_zero]

/-- **On a null face the rate is infinite.** -/
theorem genRate_eq_top_of_null_face {u : ι → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss R u x ≤ β)
    (h0 : ν {x | dirLoss R u x = β} = 0) {M : ι → ℝ} (hM : dotJ u M = β) :
    genRate ν R M = ⊤ := by
  obtain ⟨hum, _, _⟩ := bdd_dirLoss hR u
  -- the shifted normaliser `Z_λ = E e^{λ(u·R − β)}` tends to `0`
  set Z : ℝ → ℝ := fun lam ↦ ∫ x, Real.exp (lam * (dirLoss R u x - β)) ∂ν with hZ
  have hZpos : ∀ lam, 0 < Z lam := fun lam ↦
    integral_exp_pos ((integrable_exp_mul_of_bdd ν ((bdd_dirLoss hR u).add (Bdd.const (-β)))
      lam).congr (Eventually.of_forall fun x ↦ by simp [sub_eq_add_neg]))
  have hne : ∀ᵐ x ∂ν, dirLoss R u x ≠ β := by
    refine ae_iff.2 ?_
    have e : {x | ¬dirLoss R u x ≠ β} = {x | dirLoss R u x = β} := by ext; simp
    rw [e]; exact h0
  have hZlim : Tendsto Z atTop (𝓝 0) := by
    have h0' : (0 : ℝ) = ∫ _x, (0 : ℝ) ∂ν := by simp
    rw [hZ, h0']
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (Eventually.of_forall fun lam ↦ (Measurable.aestronglyMeasurable (by fun_prop))) ?_
      (integrable_const _) ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
      filter_upwards [hβ] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
      exact Real.exp_le_exp.2 (mul_nonpos_of_nonneg_of_nonpos hlam (by linarith))
    · filter_upwards [hβ, hne] with x hx hxne
      have hlt : dirLoss R u x - β < 0 := sub_neg.2 (lt_of_le_of_ne hx hxne)
      exact Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hlt)
  -- the Chernoff score at `λ u` is `−log Z_λ`
  have hscore : ∀ lam : ℝ, dotJ (lam • u) M - featCgf ν R (lam • u) = -Real.log (Z lam) := by
    intro lam
    unfold featCgf
    have e : ∫ x, Real.exp (dirLoss R (lam • u) x) ∂ν = Real.exp (lam * β) * Z lam := by
      rw [hZ, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [dirLoss_smul, ← Real.exp_add]
      congr 1; ring
    rw [e, Real.log_mul (Real.exp_pos _).ne' (hZpos lam).ne', Real.log_exp, dotJ_smul_left, hM]
    ring
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨lam, hlam⟩ := (hZlim.eventually (gt_mem_nhds (Real.exp_pos (-r)))).exists
  have hlog : (r : ℝ) ≤ -Real.log (Z lam) := by
    have := Real.log_lt_log (hZpos lam) hlam
    rw [Real.log_exp] at this
    linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (dotJ (lam • u) M - featCgf ν R (lam • u)) := by
        rw [hscore]; exact ENNReal.ofReal_le_ofReal hlog
    _ ≤ genRate ν R M := le_iSup (fun q ↦ ENNReal.ofReal (dotJ q M - featCgf ν R q)) _

end

end Laplace.Multi
