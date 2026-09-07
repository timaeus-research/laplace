/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Laplace.Grammar.CoeffLipschitz

/-!
# The weighted analytic coefficient space (grammar §4.3, Astra #11 rank 2)

The Taylor data `(x, y)` of the phase and amplitude live in the `ρ`-weighted `ℓ¹` space. We realise
the pair as a single point of Mathlib's Banach space `ℓ¹((ℕ×ℕ) ⊕ (ℕ×ℕ), ℝ)` after rescaling
`a(inl k) = x_k ρ^{|k|}`, `a(inr k) = y_k ρ^{|k|}` (`CoeffPair`, `toX`, `toY`, `ofPair`). The
norm dominates both weighted norms (`wnorm_toX_le_norm`, `wnorm_toY_le_norm`), so the canonical
coefficient maps `coeffA`, `coeffB : CoeffPair → ℝ` are continuous (locally Lipschitz, from unit
145) and Borel measurable. This is the domain on which convergence in distribution of the
coefficient data can be stated (next unit). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- The index of the pair `(x, y)` of coefficient arrays. -/
abbrev PairIdx : Type := (ℕ × ℕ) ⊕ (ℕ × ℕ)

/-- The coefficient-pair space `ℓ¹(PairIdx, ℝ)`. -/
abbrev CoeffPair : Type := lp (fun _ : PairIdx => ℝ) 1

noncomputable instance : MeasurableSpace CoeffPair := borel CoeffPair
instance : BorelSpace CoeffPair := ⟨rfl⟩

/-- The phase array `x_k = a(inl k) ρ^{-|k|}`. -/
noncomputable def toX (ρ : ℝ) (a : CoeffPair) : ℕ × ℕ → ℝ :=
  fun k => a (Sum.inl k) / ρ ^ (k.1 + k.2)

/-- The amplitude array `y_k = a(inr k) ρ^{-|k|}`. -/
noncomputable def toY (ρ : ℝ) (a : CoeffPair) : ℕ × ℕ → ℝ :=
  fun k => a (Sum.inr k) / ρ ^ (k.1 + k.2)

theorem summable_abs_coeff (a : CoeffPair) : Summable fun i => |a i| := by
  have h := (memℓp_gen_iff (p := 1) (by simp)).1 (lp.memℓp a)
  simpa using h

theorem norm_eq_tsum_abs (a : CoeffPair) : ‖a‖ = ∑' i, |a i| := by
  rw [lp.norm_eq_tsum_rpow (by simp) a]
  simp

theorem wsummable_toX (ρ : ℝ) (hρ : 0 < ρ) (a : CoeffPair) : WSummable ρ (toX ρ a) := by
  unfold WSummable toX
  refine ((summable_abs_coeff a).comp_injective Sum.inl_injective).congr fun k => ?_
  simp only [Function.comp]
  rw [abs_div, abs_of_pos (pow_pos hρ _), div_mul_cancel₀ _ (pow_pos hρ _).ne']

theorem wsummable_toY (ρ : ℝ) (hρ : 0 < ρ) (a : CoeffPair) : WSummable ρ (toY ρ a) := by
  unfold WSummable toY
  refine ((summable_abs_coeff a).comp_injective Sum.inr_injective).congr fun k => ?_
  simp only [Function.comp]
  rw [abs_div, abs_of_pos (pow_pos hρ _), div_mul_cancel₀ _ (pow_pos hρ _).ne']

/-- The weighted norm of the phase array is dominated by the `ℓ¹` norm. -/
theorem wnorm_toX_le_norm (ρ : ℝ) (hρ : 0 < ρ) (a : CoeffPair) : wnorm ρ (toX ρ a) ≤ ‖a‖ := by
  rw [norm_eq_tsum_abs]
  have hW := wsummable_toX ρ hρ a
  unfold WSummable at hW
  unfold wnorm
  refine hW.tsum_le_tsum_of_inj Sum.inl Sum.inl_injective (fun i _ => abs_nonneg _) (fun k => ?_)
    (summable_abs_coeff a)
  unfold toX
  rw [abs_div, abs_of_pos (pow_pos hρ _), div_mul_cancel₀ _ (pow_pos hρ _).ne']

theorem wnorm_toY_le_norm (ρ : ℝ) (hρ : 0 < ρ) (a : CoeffPair) : wnorm ρ (toY ρ a) ≤ ‖a‖ := by
  rw [norm_eq_tsum_abs]
  have hW := wsummable_toY ρ hρ a
  unfold WSummable at hW
  unfold wnorm
  refine hW.tsum_le_tsum_of_inj Sum.inr Sum.inr_injective (fun i _ => abs_nonneg _) (fun k => ?_)
    (summable_abs_coeff a)
  unfold toY
  rw [abs_div, abs_of_pos (pow_pos hρ _), div_mul_cancel₀ _ (pow_pos hρ _).ne']

theorem toX_sub (ρ : ℝ) (a b : CoeffPair) :
    toX ρ (a - b) = fun k => toX ρ a k - toX ρ b k := by
  funext k
  unfold toX
  rw [lp.coeFn_sub, Pi.sub_apply, sub_div]

theorem toY_sub (ρ : ℝ) (a b : CoeffPair) :
    toY ρ (a - b) = fun k => toY ρ a k - toY ρ b k := by
  funext k
  unfold toY
  rw [lp.coeFn_sub, Pi.sub_apply, sub_div]

theorem wnorm_toX_sub_le_dist (ρ : ℝ) (hρ : 0 < ρ) (a b : CoeffPair) :
    wnorm ρ (fun k => toX ρ a k - toX ρ b k) ≤ dist a b := by
  rw [dist_eq_norm, ← toX_sub]; exact wnorm_toX_le_norm ρ hρ _

theorem wnorm_toY_sub_le_dist (ρ : ℝ) (hρ : 0 < ρ) (a b : CoeffPair) :
    wnorm ρ (fun k => toY ρ a k - toY ρ b k) ≤ dist a b := by
  rw [dist_eq_norm, ← toY_sub]; exact wnorm_toY_le_norm ρ hρ _

/-- The point of `CoeffPair` representing a pair of weighted-summable arrays. -/
noncomputable def ofPair (ρ : ℝ) (hρ : 0 < ρ) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) : CoeffPair :=
  ⟨Sum.elim (fun k => x k * ρ ^ (k.1 + k.2)) (fun k => y k * ρ ^ (k.1 + k.2)), by
    change Memℓp _ 1
    rw [memℓp_gen_iff (p := 1) (by simp)]
    simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
    unfold WSummable at hx hy
    have hx' : Summable fun k : ℕ × ℕ => |x k * ρ ^ (k.1 + k.2)| :=
      hx.congr fun k => by rw [abs_mul, abs_of_pos (pow_pos hρ _)]
    have hy' : Summable fun k : ℕ × ℕ => |y k * ρ ^ (k.1 + k.2)| :=
      hy.congr fun k => by rw [abs_mul, abs_of_pos (pow_pos hρ _)]
    refine Summable.sum _ ?_ ?_
    · exact hx'.congr fun k => by simp
    · exact hy'.congr fun k => by simp⟩

/-- The norm of a represented pair is the sum of the two weighted norms. -/
theorem norm_ofPair (ρ : ℝ) (hρ : 0 < ρ) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) : ‖ofPair ρ hρ x y hx hy‖ = wnorm ρ x + wnorm ρ y := by
  rw [norm_eq_tsum_abs]
  have hs := summable_abs_coeff (ofPair ρ hρ x y hx hy)
  have h1 : Summable ((fun i => |ofPair ρ hρ x y hx hy i|) ∘ Sum.inl) :=
    hs.comp_injective Sum.inl_injective
  have h2 : Summable ((fun i => |ofPair ρ hρ x y hx hy i|) ∘ Sum.inr) :=
    hs.comp_injective Sum.inr_injective
  rw [Summable.tsum_sum h1 h2]
  unfold wnorm
  congr 1
  · refine tsum_congr fun k => ?_
    change |x k * ρ ^ (k.1 + k.2)| = _
    rw [abs_mul, abs_of_pos (pow_pos hρ _)]
  · refine tsum_congr fun k => ?_
    change |y k * ρ ^ (k.1 + k.2)| = _
    rw [abs_mul, abs_of_pos (pow_pos hρ _)]

theorem toX_ofPair (ρ : ℝ) (hρ : 0 < ρ) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) : toX ρ (ofPair ρ hρ x y hx hy) = x := by
  funext k
  change x k * ρ ^ (k.1 + k.2) / ρ ^ (k.1 + k.2) = x k
  exact mul_div_cancel_right₀ _ (pow_pos hρ _).ne'

theorem toY_ofPair (ρ : ℝ) (hρ : 0 < ρ) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) : toY ρ (ofPair ρ hρ x y hx hy) = y := by
  funext k
  change y k * ρ ^ (k.1 + k.2) / ρ ^ (k.1 + k.2) = y k
  exact mul_div_cancel_right₀ _ (pow_pos hρ _).ne'

theorem ofPair_toXY (ρ : ℝ) (hρ : 0 < ρ) (a : CoeffPair) :
    ofPair ρ hρ (toX ρ a) (toY ρ a) (wsummable_toX ρ hρ a) (wsummable_toY ρ hρ a) = a := by
  ext i
  rcases i with k | k
  · change toX ρ a k * ρ ^ (k.1 + k.2) = a (Sum.inl k)
    unfold toX
    exact div_mul_cancel₀ _ (pow_pos hρ _).ne'
  · change toY ρ a k * ρ ^ (k.1 + k.2) = a (Sum.inr k)
    unfold toY
    exact div_mul_cancel₀ _ (pow_pos hρ _).ne'

/-- The canonical log coefficient `A_α` as a function on the coefficient-pair space. -/
noncomputable def coeffA (β ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) (a : CoeffPair) : ℝ :=
  canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β (toX ρ a) (toY ρ a) (i, j) s) α

/-- The canonical constant coefficient `B_α` as a function on the coefficient-pair space. -/
noncomputable def coeffB (β b ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) (a : CoeffPair) : ℝ :=
  canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β (toX ρ a) (toY ρ a)) b)
    (anaFaceV (ampCoeff β (toX ρ a) (toY ρ a)) b)
    (fun i j s => ampCoeff β (toX ρ a) (toY ρ a) (i, j) s) α

theorem lipA_nonneg (β ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Mx α : ℝ) (hr : 0 < r) :
    0 ≤ lipA β ρ r h₁ h₂ k₁ k₂ Mx α :=
  mul_nonneg (cWeight_nonneg r hr h₁ h₂ k₁ k₂ α)
    (mul_nonneg (by positivity) (envMoment_gauss_nonneg _ _ _ _ _))

theorem lipB_nonneg (β b ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Mx α : ℝ) (hb : 0 < b) (hr : 0 < r) :
    0 ≤ lipB β b ρ r h₁ h₂ k₁ k₂ Mx α :=
  add_nonneg
    (mul_nonneg (add_nonneg (uWeight_nonneg b r hb hr h₁ h₂ k₁ k₂ α)
      (vWeight_nonneg b r hb hr h₁ h₂ k₁ k₂ α))
      (mul_nonneg (by positivity) (envMoment_gauss_nonneg _ _ _ _ _)))
    (mul_nonneg (cWeight_nonneg r hr h₁ h₂ k₁ k₂ α)
      (mul_nonneg (by positivity) (envMoment_gauss_nonneg _ _ _ _ _)))

/-- Norm bounds on the unit ball around a point. -/
theorem norm_le_of_dist_lt_one (a a₀ : CoeffPair) (h : dist a a₀ < 1) : ‖a‖ ≤ ‖a₀‖ + 1 := by
  have := norm_sub_norm_le a a₀
  rw [← dist_eq_norm] at this
  linarith

/-- **Continuity of `A_α` on the coefficient-pair space.** -/
theorem continuous_coeffA (β ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hρ : 0 < ρ) (hr0 : 0 < r)
    (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α : ℝ) (hα : 0 < α) :
    Continuous (coeffA β ρ h₁ h₂ k₁ k₂ α) := by
  refine continuous_iff_continuousAt.2 fun a₀ => ?_
  set M := ‖a₀‖ + 1 with hM
  have hM0 : 0 < M := by have := norm_nonneg a₀; linarith
  refine continuousAt_of_locally_lipschitz one_pos
    (lipA β ρ r h₁ h₂ k₁ k₂ M α * (1 + 2 * β * M)) fun a ha => ?_
  have hna : ‖a‖ ≤ M := norm_le_of_dist_lt_one a a₀ ha
  have hna₀ : ‖a₀‖ ≤ M := by linarith
  have hL := abs_canonA_ampCoeff_sub_le β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂
    (toX ρ a) (toX ρ a₀) (toY ρ a) (toY ρ a₀) (wsummable_toX ρ hρ a) (wsummable_toX ρ hρ a₀)
    (wsummable_toY ρ hρ a) (wsummable_toY ρ hρ a₀) M M
    ((wnorm_toX_le_norm ρ hρ a).trans hna) ((wnorm_toX_le_norm ρ hρ a₀).trans hna₀)
    ((wnorm_toY_le_norm ρ hρ a).trans hna) ((wnorm_toY_le_norm ρ hρ a₀).trans hna₀) α hα
  rw [Real.dist_eq]
  unfold coeffA
  refine hL.trans ?_
  have h1 := wnorm_toX_sub_le_dist ρ hρ a a₀
  have h2 := wnorm_toY_sub_le_dist ρ hρ a a₀
  have hlip := lipA_nonneg β ρ r h₁ h₂ k₁ k₂ M α hr0
  calc lipA β ρ r h₁ h₂ k₁ k₂ M α
        * (wnorm ρ (fun k => toY ρ a k - toY ρ a₀ k)
          + 2 * β * M * wnorm ρ (fun k => toX ρ a k - toX ρ a₀ k))
      ≤ lipA β ρ r h₁ h₂ k₁ k₂ M α * (dist a a₀ + 2 * β * M * dist a a₀) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 (mul_le_mul_of_nonneg_left h1 (by positivity)))
          hlip
    _ = lipA β ρ r h₁ h₂ k₁ k₂ M α * (1 + 2 * β * M) * dist a a₀ := by ring

/-- **Continuity of `B_α` on the coefficient-pair space.** -/
theorem continuous_coeffB (β b ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ)
    (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α : ℝ) (hα : 0 < α) :
    Continuous (coeffB β b ρ h₁ h₂ k₁ k₂ α) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  refine continuous_iff_continuousAt.2 fun a₀ => ?_
  set M := ‖a₀‖ + 1 with hM
  have hM0 : 0 < M := by have := norm_nonneg a₀; linarith
  refine continuousAt_of_locally_lipschitz one_pos
    (lipB β b ρ r h₁ h₂ k₁ k₂ M α * (1 + 2 * β * M)) fun a ha => ?_
  have hna : ‖a‖ ≤ M := norm_le_of_dist_lt_one a a₀ ha
  have hna₀ : ‖a₀‖ ≤ M := by linarith
  have hL := abs_canonB_ampCoeff_sub_le β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂
    (toX ρ a) (toX ρ a₀) (toY ρ a) (toY ρ a₀) (wsummable_toX ρ hρ a) (wsummable_toX ρ hρ a₀)
    (wsummable_toY ρ hρ a) (wsummable_toY ρ hρ a₀) M M
    ((wnorm_toX_le_norm ρ hρ a).trans hna) ((wnorm_toX_le_norm ρ hρ a₀).trans hna₀)
    ((wnorm_toY_le_norm ρ hρ a).trans hna) ((wnorm_toY_le_norm ρ hρ a₀).trans hna₀) α hα
  rw [Real.dist_eq]
  unfold coeffB
  refine hL.trans ?_
  have h1 := wnorm_toX_sub_le_dist ρ hρ a a₀
  have h2 := wnorm_toY_sub_le_dist ρ hρ a a₀
  have hlip := lipB_nonneg β b ρ r h₁ h₂ k₁ k₂ M α hb hr0
  calc lipB β b ρ r h₁ h₂ k₁ k₂ M α
        * (wnorm ρ (fun k => toY ρ a k - toY ρ a₀ k)
          + 2 * β * M * wnorm ρ (fun k => toX ρ a k - toX ρ a₀ k))
      ≤ lipB β b ρ r h₁ h₂ k₁ k₂ M α * (dist a a₀ + 2 * β * M * dist a a₀) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 (mul_le_mul_of_nonneg_left h1 (by positivity)))
          hlip
    _ = lipB β b ρ r h₁ h₂ k₁ k₂ M α * (1 + 2 * β * M) * dist a a₀ := by ring

theorem measurable_coeffA (β ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hρ : 0 < ρ) (hr0 : 0 < r)
    (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α : ℝ) (hα : 0 < α) :
    Measurable (coeffA β ρ h₁ h₂ k₁ k₂ α) :=
  (continuous_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ α hα).measurable

theorem measurable_coeffB (β b ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ)
    (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α : ℝ) (hα : 0 < α) :
    Measurable (coeffB β b ρ h₁ h₂ k₁ k₂ α) :=
  (continuous_coeffB β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α hα).measurable

end Laplace.Grammar
