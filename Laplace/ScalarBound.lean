import Mathlib

/-!
# Scalar bound on `exp(-z) - (1 - z)`

The key inequality powering the global perturbative remainder estimate in the
anharmonic 1D Laplace asymptotic (per the GPT-5.5-Pro consultation):

  For all `z : ℝ`,  `exp(-z) - (1 - z) ≤ (z²/2) · max 1 (exp(-z))`.

This is the second-order Taylor remainder bound, written in a form that stays
integrable when multiplied by the Gaussian factor `exp(-u²/2)` after the
rescaling `z = s_t(u)`.

We also provide the elementary lower bound `1 - z ≤ exp(-z)` (a restatement of
Mathlib's `Real.add_one_le_exp`).
-/

open Real Set

namespace Laplace

/-- Lower bound: `1 - z ≤ exp(-z)` for all `z : ℝ`. -/
lemma one_sub_le_exp_neg (z : ℝ) : 1 - z ≤ Real.exp (-z) := by
  have := Real.add_one_le_exp (-z); linarith

/-- Lower bound corollary: `0 ≤ exp(-z) - (1 - z)`. -/
lemma exp_neg_sub_one_add_nonneg (z : ℝ) :
    0 ≤ Real.exp (-z) - (1 - z) := by
  have := one_sub_le_exp_neg z; linarith

/-- For `z ≥ 0`, `exp(-z) - (1 - z) ≤ z² / 2`. -/
lemma exp_neg_sub_one_add_le_half_sq_of_nonneg (z : ℝ) (hz : 0 ≤ z) :
    Real.exp (-z) - (1 - z) ≤ z ^ 2 / 2 := by
  have hg_mono : Monotone (fun y : ℝ => y ^ 2 / 2 + 1 - y - Real.exp (-y)) := by
    apply monotone_of_deriv_nonneg
    · fun_prop
    · intro y
      have h : HasDerivAt (fun y : ℝ => y ^ 2 / 2 + 1 - y - Real.exp (-y))
          (y - 1 + Real.exp (-y)) y := by
        have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
          have := (hasDerivAt_id y).pow 2
          simpa using this.div_const 2
        have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
          have := (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
          simpa using this
        have h3 := ((h1.add_const 1).sub (hasDerivAt_id y)).sub h2
        convert h3 using 1; ring
      rw [h.deriv]
      have := Real.add_one_le_exp (-y); linarith
  have h0 : (fun y : ℝ => y ^ 2 / 2 + 1 - y - Real.exp (-y)) 0 ≤
            (fun y : ℝ => y ^ 2 / 2 + 1 - y - Real.exp (-y)) z := hg_mono hz
  simp at h0
  linarith

/-- For `z ≤ 0`, `exp(-z) - (1 - z) ≤ (z²/2) · exp(-z)`. -/
lemma exp_neg_sub_one_add_le_half_sq_mul_exp_neg_of_nonpos (z : ℝ) (hz : z ≤ 0) :
    Real.exp (-z) - (1 - z) ≤ (z ^ 2 / 2) * Real.exp (-z) := by
  -- Reduce to: `exp(w) - 1 - w ≤ (w²/2) · exp(w)` for `w := -z ≥ 0`.
  set w := -z with hw_def
  have hw : 0 ≤ w := by simp [hw_def]; linarith
  -- Show K(w) := (w²/2) exp(w) - exp(w) + 1 + w ≥ 0 for w ≥ 0.
  -- This needs K monotone on Ici 0, with K(0) = 0.
  -- K'(w) = exp(w)·(w²/2 + w - 1) + 1 =: Kp(w); Kp(0) = 0.
  -- Kp'(w) = exp(w)·(w²/2 + 2w) ≥ 0 on Ici 0; so Kp ≥ 0 there; so K monotone.
  have hKp_mono : MonotoneOn
      (fun y : ℝ => Real.exp y * (y ^ 2 / 2 + y - 1) + 1) (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _
      apply DifferentiableAt.differentiableWithinAt
      fun_prop
    · intro y hy
      have hy_pos : 0 ≤ y := by
        have := interior_subset hy
        exact this
      have h : HasDerivAt
          (fun y : ℝ => Real.exp y * (y ^ 2 / 2 + y - 1) + 1)
          (Real.exp y * (y ^ 2 / 2 + 2 * y)) y := by
        have hexp : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp y) y :=
          Real.hasDerivAt_exp y
        have hsq : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
          have := (hasDerivAt_id y).pow 2
          simpa using this.div_const 2
        have hpoly : HasDerivAt (fun y : ℝ => y ^ 2 / 2 + y - 1) (y + 1) y := by
          have := (hsq.add (hasDerivAt_id y)).sub_const 1
          convert this using 1
        have hmul : HasDerivAt (fun y : ℝ => Real.exp y * (y ^ 2 / 2 + y - 1))
            (Real.exp y * (y ^ 2 / 2 + y - 1) + Real.exp y * (y + 1)) y :=
          hexp.mul hpoly
        have := hmul.add_const 1
        convert this using 1; ring
      rw [h.deriv]
      have hexp_pos : 0 ≤ Real.exp y := (Real.exp_pos y).le
      have hpoly_nonneg : 0 ≤ y ^ 2 / 2 + 2 * y := by positivity
      exact mul_nonneg hexp_pos hpoly_nonneg
  -- Kp(0) = 0
  have hKp_zero : (fun y : ℝ => Real.exp y * (y ^ 2 / 2 + y - 1) + 1) 0 = 0 := by simp
  -- Kp(w) ≥ 0 for w ≥ 0
  have hKp_nonneg : 0 ≤ Real.exp w * (w ^ 2 / 2 + w - 1) + 1 := by
    have := hKp_mono (Set.self_mem_Ici) hw hw
    rw [hKp_zero] at this; exact this
  -- K monotone on Ici 0
  have hK_mono : MonotoneOn
      (fun y : ℝ => y ^ 2 / 2 * Real.exp y - Real.exp y + 1 + y) (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _
      apply DifferentiableAt.differentiableWithinAt
      fun_prop
    · intro y hy
      have hy_pos : 0 ≤ y := by
        have := interior_subset hy
        exact this
      -- deriv of K at y is Kp(y), which ≥ 0 by previous.
      have h : HasDerivAt
          (fun y : ℝ => y ^ 2 / 2 * Real.exp y - Real.exp y + 1 + y)
          (Real.exp y * (y ^ 2 / 2 + y - 1) + 1) y := by
        have hexp : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp y) y :=
          Real.hasDerivAt_exp y
        have hsq : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
          have := (hasDerivAt_id y).pow 2
          simpa using this.div_const 2
        have hmul : HasDerivAt (fun y : ℝ => y ^ 2 / 2 * Real.exp y)
            (y * Real.exp y + y ^ 2 / 2 * Real.exp y) y := hsq.mul hexp
        have h1 := (hmul.sub hexp).add_const 1
        have h2 := h1.add (hasDerivAt_id y)
        convert h2 using 1; ring
      rw [h.deriv]
      -- 0 ≤ Kp(y) by hKp_mono
      have := hKp_mono (Set.self_mem_Ici) hy_pos hy_pos
      rw [hKp_zero] at this; exact this
  -- K(0) = 0
  have hK_zero : (fun y : ℝ => y ^ 2 / 2 * Real.exp y - Real.exp y + 1 + y) 0 = 0 := by simp
  -- K(w) ≥ 0
  have hK_nonneg : 0 ≤ w ^ 2 / 2 * Real.exp w - Real.exp w + 1 + w := by
    have := hK_mono (Set.self_mem_Ici) hw hw
    rw [hK_zero] at this; exact this
  -- Translate back to z: w = -z, w² = z², exp w = exp(-z), 1 + w = 1 - z.
  have hwsq : w ^ 2 = z ^ 2 := by rw [hw_def]; ring
  have hewp : Real.exp w = Real.exp (-z) := by rw [hw_def]
  rw [hwsq, hewp] at hK_nonneg
  -- hK_nonneg : 0 ≤ z²/2 · exp(-z) - exp(-z) + 1 + w
  -- want: exp(-z) - (1 - z) ≤ (z²/2) · exp(-z), i.e., 0 ≤ (z²/2) · exp(-z) - exp(-z) + 1 - z
  have hw_eq : w = -z := hw_def
  rw [hw_eq] at hK_nonneg
  linarith

/-- **Scalar Taylor-1 remainder bound for `exp(-·)`**: for all `z : ℝ`,

  `exp(-z) - (1 - z) ≤ (z²/2) · max 1 (exp(-z))`.

This is the cornerstone of the global remainder estimate for the anharmonic
Laplace expansion. -/
theorem exp_neg_sub_one_add_le (z : ℝ) :
    Real.exp (-z) - (1 - z) ≤ (z ^ 2 / 2) * max 1 (Real.exp (-z)) := by
  rcases lt_or_ge z 0 with hz | hz
  swap
  · calc Real.exp (-z) - (1 - z)
        ≤ z ^ 2 / 2 := exp_neg_sub_one_add_le_half_sq_of_nonneg z hz
      _ = (z ^ 2 / 2) * 1 := by ring
      _ ≤ (z ^ 2 / 2) * max 1 (Real.exp (-z)) := by
          apply mul_le_mul_of_nonneg_left (le_max_left _ _)
          positivity
  · have hz' : z ≤ 0 := hz.le
    calc Real.exp (-z) - (1 - z)
        ≤ (z ^ 2 / 2) * Real.exp (-z) :=
          exp_neg_sub_one_add_le_half_sq_mul_exp_neg_of_nonpos z hz'
      _ ≤ (z ^ 2 / 2) * max 1 (Real.exp (-z)) := by
          apply mul_le_mul_of_nonneg_left (le_max_right _ _)
          positivity

/-- **Two-sided bound** combining the lower and upper estimates. -/
theorem abs_exp_neg_sub_one_add_le (z : ℝ) :
    |Real.exp (-z) - (1 - z)| ≤ (z ^ 2 / 2) * max 1 (Real.exp (-z)) := by
  rw [abs_of_nonneg (exp_neg_sub_one_add_nonneg z)]
  exact exp_neg_sub_one_add_le z

end Laplace
