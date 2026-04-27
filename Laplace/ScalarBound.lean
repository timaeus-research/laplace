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

/-! ## Second-order Taylor bound

For the next-order asymptotic in the anharmonic Laplace expansion we need

  `|exp(-z) - (1 - z + z²/2)| ≤ (|z|³/6) · max 1 (exp(-z))`.

The proof has the same shape as the first-order bound: nested monotonicity
arguments establish that the difference is sign-controlled (positive for
`z ≤ 0`, negative for `z ≥ 0`) with the desired magnitude bound, on each
side. The new ingredient is one extra level of nesting since `g'''(z) =
1 - exp(-z)` only has a definite sign on each half-line. -/

/-- Sign for `z ≥ 0`: `exp(-z) ≤ 1 - z + z²/2`. -/
lemma exp_neg_le_one_sub_add_half_sq_of_nonneg (z : ℝ) (hz : 0 ≤ z) :
    Real.exp (-z) ≤ 1 - z + z ^ 2 / 2 := by
  -- Show G(z) := 1 - z + z²/2 - exp(-z) ≥ 0 via G(0) = 0 and G monotone.
  -- G'(z) = -1 + z + exp(-z), G'(0) = 0, G' monotone since G''(z) = 1 - exp(-z) ≥ 0 on [0,∞).
  have hG'_mono : MonotoneOn (fun y : ℝ => -1 + y + Real.exp (-y)) (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _
      apply DifferentiableAt.differentiableWithinAt
      fun_prop
    · intro y hy
      have hy_nn : 0 ≤ y := interior_subset hy
      have h : HasDerivAt (fun y : ℝ => -1 + y + Real.exp (-y)) (1 - Real.exp (-y)) y := by
        have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
          have := (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
          simpa using this
        have h2 := ((hasDerivAt_const y (-1 : ℝ)).add (hasDerivAt_id y)).add h1
        convert h2 using 1; ring
      rw [h.deriv]
      have : Real.exp (-y) ≤ 1 := by
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith
  -- G'(0) = 0, so G'(z) ≥ 0 on [0,∞).
  have hG'_nonneg : 0 ≤ -1 + z + Real.exp (-z) := by
    have h0 : (fun y : ℝ => -1 + y + Real.exp (-y)) 0 = 0 := by simp
    have := hG'_mono Set.self_mem_Ici hz hz
    rw [h0] at this; exact this
  -- Now G itself: G(z) = 1 - z + z²/2 - exp(-z).
  have hG_mono : MonotoneOn
      (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y)) (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _
      apply DifferentiableAt.differentiableWithinAt
      fun_prop
    · intro y hy
      have hy_nn : 0 ≤ y := interior_subset hy
      have h : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y))
          (-1 + y + Real.exp (-y)) y := by
        have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
          have := (hasDerivAt_id y).pow 2
          simpa using this.div_const 2
        have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
          have := (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
          simpa using this
        have h3 := (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add h1).sub h2
        convert h3 using 1; ring
      rw [h.deriv]
      have := hG'_mono Set.self_mem_Ici hy_nn hy_nn
      simp at this; linarith
  have hG_zero : (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y)) 0 = 0 := by simp
  have hG_nonneg : 0 ≤ 1 - z + z ^ 2 / 2 - Real.exp (-z) := by
    have := hG_mono Set.self_mem_Ici hz hz
    rw [hG_zero] at this; exact this
  linarith

/-- For `z ≥ 0`, `(1 - z + z²/2) - exp(-z) ≤ z³/6`. -/
lemma one_sub_add_half_sq_sub_exp_neg_le_sixth_cube_of_nonneg
    (z : ℝ) (hz : 0 ≤ z) :
    1 - z + z ^ 2 / 2 - Real.exp (-z) ≤ z ^ 3 / 6 := by
  -- Define G(z) := z³/6 - 1 + z - z²/2 + exp(-z) and show G(z) ≥ 0.
  -- G(0) = G'(0) = G''(0) = 0; G'''(y) = 1 - exp(-y) ≥ 0 on [0,∞).
  -- Step 1: G''(y) := -1 + y + exp(-y) — already shown nonneg on [0,∞).
  have hGpp_nonneg : ∀ {y : ℝ}, 0 ≤ y → 0 ≤ -1 + y + Real.exp (-y) := by
    intro y hy
    have hG'_mono : MonotoneOn (fun u : ℝ => -1 + u + Real.exp (-u)) (Set.Ici (0 : ℝ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · fun_prop
      · intro u _; apply DifferentiableAt.differentiableWithinAt; fun_prop
      · intro u hu
        have hu_nn : 0 ≤ u := interior_subset hu
        have h : HasDerivAt (fun u : ℝ => -1 + u + Real.exp (-u)) (1 - Real.exp (-u)) u := by
          have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) u := by
            have := (Real.hasDerivAt_exp (-u)).comp u ((hasDerivAt_id u).neg)
            simpa using this
          have h2 := ((hasDerivAt_const u (-1 : ℝ)).add (hasDerivAt_id u)).add h1
          convert h2 using 1 <;> ring
        rw [h.deriv]
        have : Real.exp (-u) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
          exact Real.exp_le_exp.mpr (by linarith)
        linarith
    have h0 : (fun u : ℝ => -1 + u + Real.exp (-u)) 0 = 0 := by simp
    have := hG'_mono Set.self_mem_Ici hy hy
    rw [h0] at this; exact this
  -- Step 2: G'(y) := y²/2 - 1 + y - Real.exp (-y) is ≥ 0 on [0,∞).
  -- (G'(0) = 0 and G' monotone since G''(y) = y + 1 - exp(-y)... wait that's different.
  -- Let me re-derive: G(z) = z³/6 - 1 + z - z²/2 + exp(-z).
  -- G'(z) = z²/2 + 1 - z - exp(-z).
  -- G''(z) = z - 1 + exp(-z).
  -- G'''(z) = 1 - exp(-z).
  -- The function `-1 + y + exp(-y)` is G'' with sign flipped: actually G''(y) = y - 1 + exp(-y) = -(1 - y - exp(-y)) = -1 + y + exp(-y). Hmm same!
  -- Wait: -1 + y + exp(-y) vs y - 1 + exp(-y). These ARE the same. ✓
  -- So G''(y) = -1 + y + exp(-y), which we've shown ≥ 0 for y ≥ 0.
  -- Step 2: G'(y) ≥ 0 on [0,∞).
  have hG'_mono : MonotoneOn (fun y : ℝ => y ^ 2 / 2 + 1 - y - Real.exp (-y)) (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _; apply DifferentiableAt.differentiableWithinAt; fun_prop
    · intro y hy
      have hy_nn : 0 ≤ y := interior_subset hy
      have h : HasDerivAt (fun y : ℝ => y ^ 2 / 2 + 1 - y - Real.exp (-y))
          (y - 1 + Real.exp (-y)) y := by
        have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
          have := (hasDerivAt_id y).pow 2; simpa using this.div_const 2
        have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
          have := (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
          simpa using this
        have h3 := ((h1.add_const 1).sub (hasDerivAt_id y)).sub h2
        convert h3 using 1; ring
      rw [h.deriv]
      have := hGpp_nonneg hy_nn
      linarith
  have hG'_zero : (fun y : ℝ => y ^ 2 / 2 + 1 - y - Real.exp (-y)) 0 = 0 := by simp
  have hG'_nonneg : 0 ≤ z ^ 2 / 2 + 1 - z - Real.exp (-z) := by
    have := hG'_mono Set.self_mem_Ici hz hz
    rw [hG'_zero] at this; exact this
  -- Step 3: G(z) ≥ 0.
  have hG_mono : MonotoneOn
      (fun y : ℝ => y ^ 3 / 6 - 1 + y - y ^ 2 / 2 + Real.exp (-y)) (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _; apply DifferentiableAt.differentiableWithinAt; fun_prop
    · intro y hy
      have hy_nn : 0 ≤ y := interior_subset hy
      have h : HasDerivAt (fun y : ℝ => y ^ 3 / 6 - 1 + y - y ^ 2 / 2 + Real.exp (-y))
          (y ^ 2 / 2 + 1 - y - Real.exp (-y)) y := by
        have h_cube : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (y ^ 2 / 2) y := by
          have hy3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * y ^ 2) y := by
            have := (hasDerivAt_id y).pow 3
            simpa [Nat.cast_succ, mul_comm] using this
          have := hy3.div_const 6
          convert this using 1 <;> ring
        have h_sq : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
          have := (hasDerivAt_id y).pow 2; simpa using this.div_const 2
        have h_exp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
          have := (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
          simpa using this
        have h3 := ((((h_cube.sub_const 1).add (hasDerivAt_id y)).sub h_sq).add h_exp)
        convert h3 using 1
      rw [h.deriv]
      have hGp := hG'_mono Set.self_mem_Ici hy_nn hy_nn
      rw [hG'_zero] at hGp; exact hGp
  have hG_zero : (fun y : ℝ => y ^ 3 / 6 - 1 + y - y ^ 2 / 2 + Real.exp (-y)) 0 = 0 := by simp
  have hG_nonneg : 0 ≤ z ^ 3 / 6 - 1 + z - z ^ 2 / 2 + Real.exp (-z) := by
    have := hG_mono Set.self_mem_Ici hz hz
    rw [hG_zero] at this; exact this
  linarith

/-- For `z ≤ 0`, `exp(-z) - (1 - z + z²/2) ≤ (-z)³/2 · exp(-z)`.

(For `z ≤ 0` we have `(-z)^3 = |z|^3`, so the right-hand side is
`|z|³/2 · exp(-z)`.) -/
lemma exp_neg_sub_one_add_sub_half_sq_le_half_cube_mul_exp_neg_of_nonpos
    (z : ℝ) (hz : z ≤ 0) :
    Real.exp (-z) - (1 - z + z ^ 2 / 2) ≤ (-z) ^ 3 / 2 * Real.exp (-z) := by
  -- Reduce to: `e^w - 1 - w - w²/2 ≤ (w³/2) · e^w` for `w := -z ≥ 0`.
  set w := -z with hw_def
  have hw : 0 ≤ w := by rw [hw_def]; linarith
  -- K(w) := (w³/2)·e^w - e^w + 1 + w + w²/2 ≥ 0 for w ≥ 0.
  -- K(0) = K'(0) = K''(0) = 0; K'''(w) = e^w·(w³/2 + 9w²/2 + 9w + 2) ≥ 2.
  -- Three nested monotonicity arguments.
  -- Level 3: Kpp(w) := e^w·(w³/2 + 3w² + 3w - 1) + 1, Kpp(0) = 0, Kpp' ≥ 0.
  have hKpp_mono : MonotoneOn
      (fun y : ℝ => Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 + 3 * y - 1) + 1)
      (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _; apply DifferentiableAt.differentiableWithinAt; fun_prop
    · intro y hy
      have hy_nn : 0 ≤ y := interior_subset hy
      have h : HasDerivAt
          (fun y : ℝ => Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 + 3 * y - 1) + 1)
          (Real.exp y * (y ^ 3 / 2 + 9 * y ^ 2 / 2 + 9 * y + 2)) y := by
        have hexp : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp y) y :=
          Real.hasDerivAt_exp y
        have hcube : HasDerivAt (fun y : ℝ => y ^ 3 / 2) (3 * y ^ 2 / 2) y := by
          have h1 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * y ^ 2) y := by
            have := (hasDerivAt_id y).pow 3
            simpa using this
          have := h1.div_const 2
          convert this using 1 <;> ring
        have hsq : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (6 * y) y := by
          have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
            have := (hasDerivAt_id y).pow 2; simpa using this
          have h2 := h1.const_mul 3
          convert h2 using 1 <;> ring
        have hpoly : HasDerivAt (fun y : ℝ => y ^ 3 / 2 + 3 * y ^ 2 + 3 * y - 1)
            (3 * y ^ 2 / 2 + 6 * y + 3) y := by
          have h1 := ((hcube.add hsq).add ((hasDerivAt_id y).const_mul 3)).sub_const 1
          convert h1 using 1 <;> ring
        have hmul : HasDerivAt
            (fun y : ℝ => Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 + 3 * y - 1))
            (Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 + 3 * y - 1) +
             Real.exp y * (3 * y ^ 2 / 2 + 6 * y + 3)) y := hexp.mul hpoly
        have h := hmul.add_const 1
        convert h using 1 <;> ring
      rw [h.deriv]
      have hexp_pos : 0 < Real.exp y := Real.exp_pos y
      have hpoly_nonneg : 0 ≤ y ^ 3 / 2 + 9 * y ^ 2 / 2 + 9 * y + 2 := by positivity
      exact mul_nonneg hexp_pos.le hpoly_nonneg
  have hKpp_zero : (fun y : ℝ =>
      Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 + 3 * y - 1) + 1) 0 = 0 := by simp
  have hKpp_nonneg : 0 ≤ Real.exp w * (w ^ 3 / 2 + 3 * w ^ 2 + 3 * w - 1) + 1 := by
    have := hKpp_mono Set.self_mem_Ici hw hw
    rw [hKpp_zero] at this; exact this
  -- Level 2: Kp(w) := e^w·(w³/2 + 3w²/2 - 1) + 1 + w, Kp(0) = 0, Kp' = Kpp ≥ 0.
  have hKp_mono : MonotoneOn
      (fun y : ℝ => Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 / 2 - 1) + 1 + y)
      (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _; apply DifferentiableAt.differentiableWithinAt; fun_prop
    · intro y hy
      have hy_nn : 0 ≤ y := interior_subset hy
      have h : HasDerivAt
          (fun y : ℝ => Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 / 2 - 1) + 1 + y)
          (Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 + 3 * y - 1) + 1) y := by
        have hexp : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp y) y :=
          Real.hasDerivAt_exp y
        have hcube : HasDerivAt (fun y : ℝ => y ^ 3 / 2) (3 * y ^ 2 / 2) y := by
          have hy3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * y ^ 2) y := by
            have := (hasDerivAt_id y).pow 3
            simpa [Nat.cast_succ, mul_comm] using this
          have := hy3.div_const 2
          convert this using 1 <;> ring
        have hsq32 : HasDerivAt (fun y : ℝ => 3 * y ^ 2 / 2) (3 * y) y := by
          have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
            have := (hasDerivAt_id y).pow 2; simpa using this
          have h2 := h1.const_mul 3
          have h3 := h2.div_const 2
          convert h3 using 1 <;> ring
        have hpoly : HasDerivAt (fun y : ℝ => y ^ 3 / 2 + 3 * y ^ 2 / 2 - 1)
            (3 * y ^ 2 / 2 + 3 * y) y := by
          have h1 := (hcube.add hsq32).sub_const 1
          convert h1 using 1 <;> ring
        have hmul : HasDerivAt
            (fun y : ℝ => Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 / 2 - 1))
            (Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 / 2 - 1) +
             Real.exp y * (3 * y ^ 2 / 2 + 3 * y)) y := hexp.mul hpoly
        have h := (hmul.add_const 1).add (hasDerivAt_id y)
        convert h using 1 <;> ring
      rw [h.deriv]
      have := hKpp_mono Set.self_mem_Ici hy_nn hy_nn
      rw [hKpp_zero] at this; exact this
  have hKp_zero : (fun y : ℝ =>
      Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 / 2 - 1) + 1 + y) 0 = 0 := by simp
  have hKp_nonneg : 0 ≤ Real.exp w * (w ^ 3 / 2 + 3 * w ^ 2 / 2 - 1) + 1 + w := by
    have := hKp_mono Set.self_mem_Ici hw hw
    rw [hKp_zero] at this; exact this
  -- Level 1: K(w) := (w³/2)·e^w - e^w + 1 + w + w²/2, K(0) = 0, K' = Kp ≥ 0.
  have hK_mono : MonotoneOn
      (fun y : ℝ => y ^ 3 / 2 * Real.exp y - Real.exp y + 1 + y + y ^ 2 / 2)
      (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _; apply DifferentiableAt.differentiableWithinAt; fun_prop
    · intro y hy
      have hy_nn : 0 ≤ y := interior_subset hy
      have h : HasDerivAt
          (fun y : ℝ => y ^ 3 / 2 * Real.exp y - Real.exp y + 1 + y + y ^ 2 / 2)
          (Real.exp y * (y ^ 3 / 2 + 3 * y ^ 2 / 2 - 1) + 1 + y) y := by
        have hexp : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp y) y :=
          Real.hasDerivAt_exp y
        have hcube : HasDerivAt (fun y : ℝ => y ^ 3 / 2) (3 * y ^ 2 / 2) y := by
          have hy3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * y ^ 2) y := by
            have := (hasDerivAt_id y).pow 3
            simpa [Nat.cast_succ, mul_comm] using this
          have := hy3.div_const 2
          convert this using 1 <;> ring
        have hcube_exp : HasDerivAt (fun y : ℝ => y ^ 3 / 2 * Real.exp y)
            (3 * y ^ 2 / 2 * Real.exp y + y ^ 3 / 2 * Real.exp y) y := hcube.mul hexp
        have hsq : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
          have := (hasDerivAt_id y).pow 2; simpa using this.div_const 2
        have h1 := (((hcube_exp.sub hexp).add_const 1).add (hasDerivAt_id y)).add hsq
        convert h1 using 1; ring
      rw [h.deriv]
      have := hKp_mono Set.self_mem_Ici hy_nn hy_nn
      rw [hKp_zero] at this; exact this
  have hK_zero : (fun y : ℝ =>
      y ^ 3 / 2 * Real.exp y - Real.exp y + 1 + y + y ^ 2 / 2) 0 = 0 := by simp
  have hK_nonneg : 0 ≤ w ^ 3 / 2 * Real.exp w - Real.exp w + 1 + w + w ^ 2 / 2 := by
    have := hK_mono Set.self_mem_Ici hw hw
    rw [hK_zero] at this; exact this
  -- Translate w back to z: w = -z, w² = z², w³ = (-z)³, exp(w) = exp(-z).
  have hwsq : w ^ 2 = z ^ 2 := by rw [hw_def]; ring
  have hwcb : w ^ 3 = (-z) ^ 3 := by rw [hw_def]
  have hexpw : Real.exp w = Real.exp (-z) := by rw [hw_def]
  rw [hwsq, hwcb, hexpw] at hK_nonneg
  -- hK_nonneg : 0 ≤ (-z)³/2 · exp(-z) - exp(-z) + 1 + w + z²/2
  have hw_eq : w = -z := hw_def
  rw [hw_eq] at hK_nonneg
  -- want: exp(-z) - (1 - z + z²/2) ≤ ((-z)³/2) · exp(-z)
  -- equivalent: 0 ≤ ((-z)³/2)·exp(-z) - exp(-z) + 1 - z + z²/2
  linarith

/-- **Scalar Taylor-2 remainder bound for `exp(-·)`** (one-sided): for all `z : ℝ`,

  `1 - z + z²/2 - exp(-z) ≤ |z|³/6 · max 1 (exp(-z))`

(equivalently the `(1-z+z²/2) - exp(-z)` direction; the reverse direction is
covered by `exp_neg_sub_one_add_sub_half_sq_le`). -/
theorem one_sub_add_half_sq_sub_exp_neg_le (z : ℝ) :
    1 - z + z ^ 2 / 2 - Real.exp (-z) ≤ |z| ^ 3 / 6 * max 1 (Real.exp (-z)) := by
  rcases lt_or_ge z 0 with hz | hz
  swap
  · -- z ≥ 0: bound by z³/6, |z|^3 = z^3, max = 1.
    have h1 := one_sub_add_half_sq_sub_exp_neg_le_sixth_cube_of_nonneg z hz
    have hz_abs : |z| = z := abs_of_nonneg hz
    have hexp : Real.exp (-z) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr (by linarith)
    have hmax : max 1 (Real.exp (-z)) = 1 := max_eq_left hexp
    rw [hz_abs, hmax]; linarith
  · -- z < 0: 1 - z + z²/2 ≥ 1 + z²/2 ≥ 1 ≥ exp(-z)? No, exp(-z) ≥ 1 here.
    -- For z < 0, the LHS = (1 - z + z²/2) - exp(-z) ≤ 0 (since exp(-z) ≥ 1+|z|+|z|²/2 in this regime).
    -- So it's automatically ≤ the RHS.
    have hz' : z ≤ 0 := hz.le
    have h_nonneg : 0 ≤ Real.exp (-z) - (1 - z + z ^ 2 / 2) := by
      have h := exp_neg_sub_one_add_sub_half_sq_le_half_cube_mul_exp_neg_of_nonpos z hz'
      -- This gives e^{-z} - (1-z+z²/2) ≤ ... but we want lower bound.
      -- Use: by convexity/Taylor, e^{-z} ≥ 1 - z + z²/2 for all z (since e^{-z} = ∑ (-z)^k/k!,
      -- but only true on certain regions).
      -- Actually: define G(z) = exp(-z) - (1-z+z²/2). G(0) = 0. G'(z) = -exp(-z) + 1 - z.
      -- G'(0) = 0. G''(z) = exp(-z) - 1 ≥ 0 for z ≤ 0.
      -- So G' monotone on (-∞, 0] (increasing), G'(0) = 0, so G'(z) ≤ 0 for z ≤ 0.
      -- So G monotone decreasing on (-∞, 0] (going right), G(0) = 0, so G(z) ≥ 0 for z ≤ 0.
      have hG'_mono : MonotoneOn (fun y : ℝ => -Real.exp (-y) + 1 - y) (Set.Iic (0 : ℝ)) := by
        apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
        · fun_prop
        · intro y _; apply DifferentiableAt.differentiableWithinAt; fun_prop
        · intro y hy
          have hy_np : y ≤ 0 := Set.mem_Iic.mp (interior_subset hy)
          have h : HasDerivAt (fun y : ℝ => -Real.exp (-y) + 1 - y) (Real.exp (-y) - 1) y := by
            have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
              have := (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
              simpa using this
            have h2 := ((h1.neg.add_const 1).sub (hasDerivAt_id y))
            convert h2 using 1 <;> ring
          rw [h.deriv]
          have : Real.exp (-y) ≥ 1 := by
            rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
            exact Real.exp_le_exp.mpr (by linarith)
          linarith
      -- G'(0) = 0
      have hG'_zero : (fun y : ℝ => -Real.exp (-y) + 1 - y) 0 = 0 := by simp
      -- For z ≤ 0: G'(z) ≤ G'(0) = 0
      have hG'_z_le : -Real.exp (-z) + 1 - z ≤ 0 := by
        have := hG'_mono hz' Set.right_mem_Iic hz'
        rw [hG'_zero] at this; exact this
      -- Now G(z) is decreasing in z on (-∞, 0] (since G' ≤ 0): so G(z) ≥ G(0) = 0 for z ≤ 0.
      have hG_anti : AntitoneOn (fun y : ℝ => Real.exp (-y) - (1 - y + y ^ 2 / 2))
          (Set.Iic (0 : ℝ)) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · fun_prop
        · intro y _; apply DifferentiableAt.differentiableWithinAt; fun_prop
        · intro y hy
          have hy_np : y ≤ 0 := Set.mem_Iic.mp (interior_subset hy)
          have h : HasDerivAt (fun y : ℝ => Real.exp (-y) - (1 - y + y ^ 2 / 2))
              (-Real.exp (-y) + 1 - y) y := by
            have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
              have := (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
              simpa using this
            have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
              have := (hasDerivAt_id y).pow 2; simpa using this.div_const 2
            have h3 : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2) (-1 + y) y := by
              have h4 := (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add h2)
              convert h4 using 1; ring
            have h5 := h1.sub h3
            convert h5 using 1; ring
          rw [h.deriv]
          -- G'(y) = -exp(-y) + 1 - y ≤ 0 for y ≤ 0 by hG'_mono.
          have hG'y_le : -Real.exp (-y) + 1 - y ≤ 0 := by
            have := hG'_mono hy_np Set.right_mem_Iic hy_np
            rw [hG'_zero] at this; exact this
          exact hG'y_le
      have hG_zero : (fun y : ℝ => Real.exp (-y) - (1 - y + y ^ 2 / 2)) 0 = 0 := by simp
      have := hG_anti hz' Set.right_mem_Iic hz'
      rw [hG_zero] at this; linarith
    -- So 1 - z + z²/2 - exp(-z) ≤ 0 ≤ |z|^3/6 · max(...)
    have hRHS_nn : 0 ≤ |z| ^ 3 / 6 * max 1 (Real.exp (-z)) := by positivity
    linarith

/-- **Two-sided Taylor-2 bound for `exp(-·)`**:
`|exp(-z) - (1 - z + z²/2)| ≤ |z|³/2 · max 1 (exp(-z))` for all `z : ℝ`.

The constant `1/2` is loose (the tight bound is `1/6`); we use the looser
form because it falls out cleanly from the existing Taylor-1 bound for the
`z ≤ 0` case via the identity `(z²/2)·|z| = |z|³/2`. -/
theorem abs_exp_neg_sub_one_add_sub_half_sq_le (z : ℝ) :
    |Real.exp (-z) - (1 - z + z ^ 2 / 2)| ≤ |z| ^ 3 / 2 * max 1 (Real.exp (-z)) := by
  rcases lt_or_ge z 0 with hz | hz
  swap
  · -- z ≥ 0: exp(-z) - (1 - z + z²/2) ≤ 0 by the sign lemma; |.| ≤ z³/6 ≤ z³/2.
    have h1 := exp_neg_le_one_sub_add_half_sq_of_nonneg z hz
    have h2 := one_sub_add_half_sq_sub_exp_neg_le_sixth_cube_of_nonneg z hz
    have hz_abs : |z| = z := abs_of_nonneg hz
    have hexp : Real.exp (-z) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr (by linarith)
    have hmax : max 1 (Real.exp (-z)) = 1 := max_eq_left hexp
    rw [hmax, hz_abs]
    rw [abs_of_nonpos (by linarith : Real.exp (-z) - (1 - z + z ^ 2 / 2) ≤ 0)]
    nlinarith [sq_nonneg z, h2]
  · -- z < 0: exp(-z) - (1 - z + z²/2) ≥ 0; bound by (-z)³/2·exp(-z) = |z|³/2·max(...).
    have hz' : z ≤ 0 := hz.le
    have h := exp_neg_sub_one_add_sub_half_sq_le_half_cube_mul_exp_neg_of_nonpos z hz'
    have hexp_ge : 1 ≤ Real.exp (-z) := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr (by linarith)
    have hmax : max 1 (Real.exp (-z)) = Real.exp (-z) := max_eq_right hexp_ge
    have hz_abs : |z| = -z := abs_of_nonpos hz'
    rw [hmax, hz_abs]
    -- Need: |exp(-z) - (1-z+z²/2)| ≤ ((-z)³/2)·exp(-z).
    -- Have: exp(-z) - (1-z+z²/2) ≤ ((-z)³/2)·exp(-z) and ≥ 0.
    have h_nn : 0 ≤ Real.exp (-z) - (1 - z + z ^ 2 / 2) := by
      -- Same argument as in `one_sub_add_half_sq_sub_exp_neg_le`: G(z) ≥ 0 for z ≤ 0.
      have hG'_mono : MonotoneOn (fun y : ℝ => -Real.exp (-y) + 1 - y) (Set.Iic (0 : ℝ)) := by
        apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
        · fun_prop
        · intro y _; apply DifferentiableAt.differentiableWithinAt; fun_prop
        · intro y hy
          have hy_np : y ≤ 0 := Set.mem_Iic.mp (interior_subset hy)
          have h : HasDerivAt (fun y : ℝ => -Real.exp (-y) + 1 - y) (Real.exp (-y) - 1) y := by
            have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
              have := (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
              simpa using this
            have h2 := ((h1.neg.add_const 1).sub (hasDerivAt_id y))
            convert h2 using 1 <;> ring
          rw [h.deriv]
          have : Real.exp (-y) ≥ 1 := by
            rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
            exact Real.exp_le_exp.mpr (by linarith)
          linarith
      have hG'_zero : (fun y : ℝ => -Real.exp (-y) + 1 - y) 0 = 0 := by simp
      have hG_anti : AntitoneOn (fun y : ℝ => Real.exp (-y) - (1 - y + y ^ 2 / 2))
          (Set.Iic (0 : ℝ)) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · fun_prop
        · intro y _; apply DifferentiableAt.differentiableWithinAt; fun_prop
        · intro y hy
          have hy_np : y ≤ 0 := Set.mem_Iic.mp (interior_subset hy)
          have h : HasDerivAt (fun y : ℝ => Real.exp (-y) - (1 - y + y ^ 2 / 2))
              (-Real.exp (-y) + 1 - y) y := by
            have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
              have := (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
              simpa using this
            have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
              have := (hasDerivAt_id y).pow 2; simpa using this.div_const 2
            have h3 : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2) (-1 + y) y := by
              have h4 := (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add h2)
              convert h4 using 1; ring
            have h5 := h1.sub h3
            convert h5 using 1; ring
          rw [h.deriv]
          have hG'y_le : -Real.exp (-y) + 1 - y ≤ 0 := by
            have := hG'_mono hy_np Set.right_mem_Iic hy_np
            rw [hG'_zero] at this; exact this
          exact hG'y_le
      have hG_zero : (fun y : ℝ => Real.exp (-y) - (1 - y + y ^ 2 / 2)) 0 = 0 := by simp
      have := hG_anti hz' Set.right_mem_Iic hz'
      rw [hG_zero] at this; linarith
    rw [abs_of_nonneg h_nn]
    -- exp(-z) - (1-z+z²/2) ≤ ((-z)³/2)·exp(-z).
    convert h using 1

end Laplace
