/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.E2Matrix

/-!
# eq:covK with localisation is minus the temperature derivative

The note displays eq:covK with `S = P⁻¹ = (tH + γI)⁻¹`. This file differentiates the localised
resolvent `S(s) = (sH + γ1)⁻¹` along `s` without any norm on matrices: the resolvent identity
`S(s) − S(t) = −(s − t) S(s) H S(t)` (`resolvent_identity`), continuity of `S` through
`Matrix.inv_def` (`continuousAt_locS`), and the entrywise derivative
`d/ds S(s)ᵢⱼ = −(S H S)ᵢⱼ` (`hasDerivAt_locS_apply`). The scalar identity for the displayed
formula follows in the second part.
-/

open Matrix Filter Topology

namespace Laplace.Multi

variable {d : ℕ}

/-- The localised precision `A(s) = sH + γ1`. -/
noncomputable def locPrec (γ : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  s • H + γ • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The localised resolvent `S(s) = (sH + γ1)⁻¹`. -/
noncomputable def locS (γ : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (locPrec γ H s)⁻¹

section Resolvent

variable {γ : ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

theorem locPrec_sub (γ : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (s t : ℝ) :
    locPrec γ H t - locPrec γ H s = (t - s) • H := by
  simp only [locPrec]
  rw [add_sub_add_right_eq_sub, sub_smul]

/-- **The resolvent identity** `S(s) − S(t) = −(s − t) S(s) H S(t)`. -/
theorem resolvent_identity {s t : ℝ} (hs : IsUnit (locPrec γ H s).det)
    (ht : IsUnit (locPrec γ H t).det) :
    locS γ H s - locS γ H t = -(s - t) • (locS γ H s * H * locS γ H t) := by
  have h1 : locS γ H s * locPrec γ H s = 1 := Matrix.nonsing_inv_mul _ hs
  have h2 : locPrec γ H t * locS γ H t = 1 := Matrix.mul_nonsing_inv _ ht
  calc locS γ H s - locS γ H t
      = locS γ H s * (locPrec γ H t * locS γ H t) - locS γ H s * locPrec γ H s * locS γ H t := by
        rw [h2, h1, Matrix.mul_one, Matrix.one_mul]
    _ = locS γ H s * (locPrec γ H t - locPrec γ H s) * locS γ H t := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = -(s - t) • (locS γ H s * H * locS γ H t) := by
        rw [locPrec_sub, Matrix.mul_smul, Matrix.smul_mul, neg_sub]

theorem continuous_locPrec (γ : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) : Continuous (locPrec γ H) := by
  unfold locPrec
  fun_prop

/-- `S` is continuous where `det A ≠ 0`, through `A⁻¹ = det(A)⁻¹ • adj(A)`. -/
theorem continuousAt_locS {t : ℝ} (ht : IsUnit (locPrec γ H t).det) :
    ContinuousAt (locS γ H) t := by
  have hdet : ContinuousAt (fun s => (locPrec γ H s).det) t :=
    ((continuous_locPrec γ H).matrix_det).continuousAt
  have hadj : ContinuousAt (fun s => (locPrec γ H s).adjugate) t :=
    ((continuous_locPrec γ H).matrix_adjugate).continuousAt
  have hne : (locPrec γ H t).det ≠ 0 := isUnit_iff_ne_zero.mp ht
  have h : locS γ H = fun s => ((locPrec γ H s).det)⁻¹ • (locPrec γ H s).adjugate := by
    funext s
    rw [locS, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hdet.inv₀ hne).smul hadj

theorem eventually_isUnit_det {t : ℝ} (ht : IsUnit (locPrec γ H t).det) :
    ∀ᶠ s in 𝓝 t, IsUnit (locPrec γ H s).det := by
  have hdet : ContinuousAt (fun s => (locPrec γ H s).det) t :=
    ((continuous_locPrec γ H).matrix_det).continuousAt
  have hne : (locPrec γ H t).det ≠ 0 := isUnit_iff_ne_zero.mp ht
  have := hdet.eventually_ne hne
  exact this.mono fun s hs => isUnit_iff_ne_zero.mpr hs

/-- **The entrywise derivative of the resolvent**: `d/ds S(s)ᵢⱼ = −(S(t) H S(t))ᵢⱼ` at `s = t`. -/
theorem hasDerivAt_locS_apply {t : ℝ} (ht : IsUnit (locPrec γ H t).det) (i j : Fin d) :
    HasDerivAt (fun s => locS γ H s i j) (-(locS γ H t * H * locS γ H t) i j) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : ∀ᶠ s in 𝓝[≠] t,
      -(locS γ H s * H * locS γ H t) i j = slope (fun s => locS γ H s i j) t s := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_isUnit_det ht)] with s hs
      hsu
    have hst : s - t ≠ 0 := sub_ne_zero.mpr hs
    have h := congrFun (congrFun (resolvent_identity hsu ht) i) j
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [slope_def_field, h]
    field_simp
  refine Tendsto.congr' hslope ?_
  have hcont : ContinuousAt (fun s => -(locS γ H s * H * locS γ H t) i j) t := by
    have hmul : Continuous fun M : Matrix (Fin d) (Fin d) ℝ => -(M * H * locS γ H t) i j :=
      (((continuous_apply j).comp (continuous_apply i)).comp
        ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_const)).neg
    exact hmul.continuousAt.comp (continuousAt_locS ht)
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

end Resolvent

/-! ### The displayed formula and its derivative -/

section Formula

variable {γ : ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- eq:mean's cubic term with `S = (sH + γ1)⁻¹`: `−½ S (s T:S)`. -/
noncomputable def meanShiftLoc (s γ : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) : Fin d → ℝ :=
  (-(1 / 2 : ℝ)) • (locS γ H s *ᵥ (s • contractT T (locS γ H s)))

/-- The right-hand side of eq:covK as displayed, with `S = (tH + γ1)⁻¹`. -/
noncomputable def covKFormulaLoc (t γ : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) : ℝ :=
  1 / 2 * (H * locS γ H t * B * locS γ H t).trace
    + 1 / 2 * ((locS γ H t *ᵥ b) ⬝ᵥ contractT T (locS γ H t))
    - t / 2 * (b ⬝ᵥ ((locS γ H t * H * locS γ H t) *ᵥ contractT T (locS γ H t)))
    - t / 2 * ((locS γ H t *ᵥ b) ⬝ᵥ contractT T (locS γ H t * H * locS γ H t))

theorem locS_zero (H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) : locS 0 H t = (t • H)⁻¹ := by
  simp [locS, locPrec]

theorem meanShiftLoc_zero (s : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (T : Fin d → Fin d → Fin d → ℝ) :
    meanShiftLoc s 0 H T = meanShift s H T := by
  simp [meanShiftLoc, meanShift, locS_zero]

/-- At `γ = 0` the displayed formula is `covKFormula`. -/
theorem covKFormulaLoc_zero (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (T : Fin d → Fin d → Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    covKFormulaLoc t 0 H T B b = covKFormula t H T B b := by
  simp [covKFormulaLoc, covKFormula, locS_zero]

/-- The derivative of the displayed formula in `bᵀS` form (no symmetry): the value of
`−d/ds[½ tr(B S(s)) + b⬝meanShiftLoc s]` at `s = t`. -/
noncomputable def covKFormulaLoc' (t γ : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) : ℝ :=
  1 / 2 * (B * (locS γ H t * H * locS γ H t)).trace
    + 1 / 2 * (b ⬝ᵥ (locS γ H t *ᵥ contractT T (locS γ H t)))
    - t / 2 * (b ⬝ᵥ ((locS γ H t * H * locS γ H t) *ᵥ contractT T (locS γ H t)))
    - t / 2 * (b ⬝ᵥ (locS γ H t *ᵥ contractT T (locS γ H t * H * locS γ H t)))

theorem hasDerivAt_contractT_locS {t : ℝ} (ht : IsUnit (locPrec γ H t).det)
    (T : Fin d → Fin d → Fin d → ℝ) (k : Fin d) :
    HasDerivAt (fun s => contractT T (locS γ H s) k)
      (-contractT T (locS γ H t * H * locS γ H t) k) t := by
  have h := HasDerivAt.sum (u := Finset.univ) fun m _ => HasDerivAt.sum (u := Finset.univ)
    fun n _ => (hasDerivAt_locS_apply ht m n).const_mul (T k m n)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp [contractT, Finset.sum_apply]
  · simp only [contractT, mul_neg, Finset.sum_neg_distrib]

/-- Pulling the scalar coefficients out of the mean-shift derivative sum. -/
theorem meanShift_deriv_sum (b : Fin d → ℝ) (R S : Matrix (Fin d) (Fin d) ℝ) (C Dv : Fin d → ℝ)
    (t : ℝ) :
    ∑ i, b i * ∑ k, (-R i k * (t * C k) + S i k * (1 * C k + t * -Dv k)) =
      -t * (b ⬝ᵥ (R *ᵥ C)) + b ⬝ᵥ (S *ᵥ C) - t * (b ⬝ᵥ (S *ᵥ Dv)) := by
  have inner : ∀ i, ∑ k, (-R i k * (t * C k) + S i k * (1 * C k + t * -Dv k)) =
      -t * ∑ k, R i k * C k + ∑ k, S i k * C k - t * ∑ k, S i k * Dv k := fun i => by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [inner, dotProduct, Matrix.mulVec]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The scalar identity, `bᵀS` form**: for `A(t) = tH + γ1` invertible,
`d/ds[½ tr(B S(s)) + b⬝meanShiftLoc s] = −covKFormulaLoc'` at `s = t`. -/
theorem hasDerivAt_firstOrderLoc {t : ℝ} (ht : IsUnit (locPrec γ H t).det)
    (T : Fin d → Fin d → Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    HasDerivAt (fun s => 1 / 2 * (B * locS γ H s).trace + b ⬝ᵥ meanShiftLoc s γ H T)
      (-covKFormulaLoc' t γ H T B b) t := by
  -- trace term
  have htr : HasDerivAt (fun s => 1 / 2 * (B * locS γ H s).trace)
      (1 / 2 * -(B * (locS γ H t * H * locS γ H t)).trace) t := by
    have h := HasDerivAt.sum (u := Finset.univ) fun i _ => HasDerivAt.sum (u := Finset.univ)
      fun k _ => (hasDerivAt_locS_apply ht k i).const_mul (B i k)
    refine ((h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).const_mul
      (1 / 2 : ℝ)).congr_deriv ?_
    · simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_apply]
    · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_neg,
        Finset.sum_neg_distrib]
  -- mean term
  have hmean : HasDerivAt (fun s => b ⬝ᵥ meanShiftLoc s γ H T)
      (-(1 / 2) * (-t * (b ⬝ᵥ ((locS γ H t * H * locS γ H t) *ᵥ contractT T (locS γ H t))) +
        b ⬝ᵥ (locS γ H t *ᵥ contractT T (locS γ H t)) -
        t * (b ⬝ᵥ (locS γ H t *ᵥ contractT T (locS γ H t * H * locS γ H t))))) t := by
    have h := HasDerivAt.sum (u := Finset.univ) fun i _ => HasDerivAt.const_mul (b i)
      (HasDerivAt.sum (u := Finset.univ) fun k _ => (hasDerivAt_locS_apply ht i k).mul
        ((hasDerivAt_id' (x := t)).mul (hasDerivAt_contractT_locS ht T k)))
    refine ((h.const_mul (-(1 / 2) : ℝ)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [meanShiftLoc, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul,
        Finset.sum_apply, Pi.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    · rw [← meanShift_deriv_sum b (locS γ H t * H * locS γ H t) (locS γ H t)
        (contractT T (locS γ H t)) (contractT T (locS γ H t * H * locS γ H t)) t]
      simp only [Pi.mul_apply]
  refine (htr.add hmean).congr_deriv ?_
  simp only [covKFormulaLoc']
  ring

theorem locS_transpose (hH : Hᵀ = H) (s : ℝ) : (locS γ H s)ᵀ = locS γ H s := by
  rw [locS, Matrix.transpose_nonsing_inv]
  congr 1
  simp [locPrec, Matrix.transpose_add, Matrix.transpose_smul, hH]

/-- **The displayed formula equals its `bᵀS` form when `H` is symmetric**: `tr(HSBS) = tr(BSHS)` by
cyclicity and `(Sb)ᵀv = bᵀSv` by symmetry of `S`. -/
theorem covKFormulaLoc_eq_of_symm (hH : Hᵀ = H) (t : ℝ) (T : Fin d → Fin d → Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    covKFormulaLoc t γ H T B b = covKFormulaLoc' t γ H T B b := by
  unfold covKFormulaLoc covKFormulaLoc'
  have hS := locS_transpose (γ := γ) hH t
  have htr : (H * locS γ H t * B * locS γ H t).trace =
      (B * (locS γ H t * H * locS γ H t)).trace := by
    rw [show H * locS γ H t * B * locS γ H t = (H * locS γ H t) * (B * locS γ H t) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hdot : ∀ v, (locS γ H t *ᵥ b) ⬝ᵥ v = b ⬝ᵥ (locS γ H t *ᵥ v) := fun v => by
    rw [dotProduct_mulVec_eq, hS]
  rw [htr, hdot, hdot]

/-- **The note's displayed eq:covK, with `S = (tH + γI)⁻¹`, is `−∂ₜ` of eq:cov's trace term plus
`bᵀ` eq:mean's cubic term**, for symmetric `H` and invertible `tH + γ1`. -/
theorem covKFormulaLoc_eq_neg_deriv (hH : Hᵀ = H) {t : ℝ} (ht : IsUnit (locPrec γ H t).det)
    (T : Fin d → Fin d → Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    covKFormulaLoc t γ H T B b =
      -deriv (fun s => 1 / 2 * (B * locS γ H s).trace + b ⬝ᵥ meanShiftLoc s γ H T) t := by
  rw [(hasDerivAt_firstOrderLoc ht T B b).deriv, neg_neg, covKFormulaLoc_eq_of_symm hH]

end Formula

end Laplace.Multi
