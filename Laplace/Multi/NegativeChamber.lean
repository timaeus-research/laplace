/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TwoMonoPotential
import Laplace.Multi.ProfileFamily

/-!
# The negative chamber: the profile variance far beyond the wall

On the negative side of the wall the profile `ρ_{-b} ∝ e^{-(y^p − b y^q)}` on `(0, ∞)` concentrates
at the interior minimiser `y_b = (qb/p)^{1/(p−q)}`. Rescaling `y = y_b z` turns the exponent into
`B ψ(z)`, `B = y_b^p`, with the fixed potential `ψ(z) = z^p − (p/q) z^q` of `TwoMonoPotential`
(`profileNum_neg_eq`), and the half-line Laplace lemma then gives the **profile matching theorem**

  `Var_{-b}(y^q) · y_b^{p − 2q} → q²/(p (p − q))`   (`tendsto_negVar_mul_rpow`),

i.e. `Var_{-b}(y^q) ~ (q²/(p(p−q))) · (qb/p)^{(2q−p)/(p−q)}` — Astra's `h(−b) ~ K_{p,q} b^{β−1}`
with `β = p/(2(p−q))` (round 26, §3). The `√t` chamber law is the far-negative asymptote of the
exact wall profile.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The interior minimiser `y_b = (qb/p)^{1/(p−q)}` of `y^p − b y^q`. -/
noncomputable def negScale (p q b : ℝ) : ℝ := (q * b / p) ^ (1 / (p - q))

/-- The large parameter `B = y_b^p`. -/
noncomputable def negB (p q b : ℝ) : ℝ := negScale p q b ^ p

/-- The rescaled numerators `I_g(B) = ∫₀^∞ g(z) e^{-B φ(z)} dz`. -/
noncomputable def zNum (p q : ℝ) (g : ℝ → ℝ) (B : ℝ) : ℝ :=
  ∫ z in Ioi (0 : ℝ), g z * Real.exp (-(B * twoMonoPhi p q z))

/-- The profile variance of `y^q` at `c = −b`. -/
noncomputable def negVar (p q b : ℝ) : ℝ :=
  profilePosterior p q (fun y ↦ y ^ q * y ^ q) (-b) - profilePosterior p q (fun y ↦ y ^ q) (-b) ^ 2

section Params

variable {p q : ℝ} (hq : 0 < q) (hqp : q < p)
include hq hqp

theorem negScale_pos {b : ℝ} (hb : 0 < b) : 0 < negScale p q b := by
  have hp : 0 < p := by linarith
  unfold negScale
  exact Real.rpow_pos_of_pos (by positivity) _

/-- `y_b^{p−q} = qb/p`. -/
theorem negScale_rpow_sub {b : ℝ} (hb : 0 < b) : negScale p q b ^ (p - q) = q * b / p := by
  have hp : 0 < p := by linarith
  have hr : p - q ≠ 0 := by linarith
  unfold negScale
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hr, Real.rpow_one]

/-- `b y_b^q = (p/q) B`. -/
theorem mul_negScale_rpow {b : ℝ} (hb : 0 < b) :
    b * negScale p q b ^ q = p / q * negB p q b := by
  have hp : 0 < p := by linarith
  have hy := negScale_pos hq hqp hb
  unfold negB
  have e : negScale p q b ^ p = negScale p q b ^ q * negScale p q b ^ (p - q) := by
    rw [← Real.rpow_add hy]; congr 1; ring
  rw [e, negScale_rpow_sub hq hqp hb]
  field_simp

/-- **The rescaling identity**: `N_g(−b) = y_b e^{-B ψ(1)} ∫₀^∞ g(y_b z) e^{-B φ(z)} dz`. -/
theorem profileNum_neg_eq {b : ℝ} (hb : 0 < b) (g : ℝ → ℝ) :
    profileNum p q g (-b) = negScale p q b * Real.exp (-(negB p q b * twoMonoPsi p q 1)) *
      zNum p q (fun z ↦ g (negScale p q b * z)) (negB p q b) := by
  have hp : 0 < p := by linarith
  have hy := negScale_pos hq hqp hb
  set y := negScale p q b with hydef
  set B := negB p q b with hBdef
  unfold profileNum zNum
  have hsub := integral_comp_mul_left_Ioi (fun v ↦ g v * Real.exp (-(v ^ p + -b * v ^ q))) 0 hy
  rw [mul_zero] at hsub
  -- `∫ F = y * ∫ F(y z)`
  have e1 : (∫ v in Ioi (0 : ℝ), g v * Real.exp (-(v ^ p + -b * v ^ q))) =
      y * ∫ z in Ioi (0 : ℝ), g (y * z) * Real.exp (-((y * z) ^ p + -b * (y * z) ^ q)) := by
    rw [hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul]
  rw [e1, mul_assoc, ← MeasureTheory.integral_const_mul (Real.exp (-(B * twoMonoPsi p q 1)))
    (fun z ↦ (fun z ↦ g (y * z)) z * Real.exp (-(B * twoMonoPhi p q z)))]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ)))
  intro z hz
  have hz : 0 < z := hz
  have hB : B = y ^ p := rfl
  dsimp only
  have hby : b * y ^ q = p / q * B := mul_negScale_rpow hq hqp hb
  rw [Real.mul_rpow hy.le hz.le, Real.mul_rpow hy.le hz.le]
  have e2 : -((y ^ p * z ^ p + -b * (y ^ q * z ^ q))) =
      -(B * twoMonoPsi p q 1) + -(B * twoMonoPhi p q z) := by
    unfold twoMonoPhi twoMonoPsi
    rw [hB]
    have : b * (y ^ q * z ^ q) = (b * y ^ q) * z ^ q := by ring
    rw [show -(y ^ p * z ^ p + -b * (y ^ q * z ^ q)) =
      -(y ^ p * z ^ p) + b * (y ^ q * z ^ q) by ring, this, hby, hB]
    ring
  rw [e2, Real.exp_add]
  ring

/-- Integrability of `z^s e^{-B φ(z)}` on `(0, ∞)` for `B > 0`, `s > −1`. -/
theorem integrableOn_rpow_mul_exp_neg_twoMonoPhi {s : ℝ} (hs : -1 < s) {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun z : ℝ ↦ z ^ s * Real.exp (-(B * twoMonoPhi p q z))) (Ioi 0) := by
  have hp : 0 < p := by linarith
  set z₁ := max 2 ((2 * p / q) ^ (1 / (p - q))) with hz₁
  have hz₁1 : 1 ≤ z₁ := le_trans (by norm_num) (le_max_left _ _)
  obtain ⟨c₁, hc₁, hquad⟩ := twoMonoPhi_quad_bound hq hqp hz₁1
  -- `φ(z) ≥ ½ z^p − ½ z₁^p` for all `z > 0`
  have hlow : ∀ z, 0 < z → 1 / 2 * z ^ p - 1 / 2 * z₁ ^ p ≤ twoMonoPhi p q z := fun z hz ↦ by
    rcases le_or_gt z z₁ with h | h
    · have h1 := hquad z hz h
      have h2 : z ^ p ≤ z₁ ^ p := Real.rpow_le_rpow hz.le h hp.le
      nlinarith [sq_nonneg (z - 1), hc₁]
    · have h1 := twoMonoPhi_coercive hq hqp (z := z) h.le
      have hα : 0 ≤ (z - 1) ^ min p 1 := Real.rpow_nonneg (by linarith [hz₁1]) _
      have hz1 : 1 ≤ z := hz₁1.trans h.le
      -- redo the coercivity computation: `z^p − (p/q) z^q ≥ ½ z^p`
      have hzc : (2 * p / q) ^ (1 / (p - q)) ≤ z := (le_max_right _ _).trans h.le
      have hr : 0 < p - q := by linarith
      have hpow : 2 * p / q ≤ z ^ (p - q) := by
        have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hzc hr.le
        rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hr.ne', Real.rpow_one] at hh
      have hqp' : p / q * z ^ q ≤ 1 / 2 * z ^ p := by
        have e : z ^ p = z ^ q * z ^ (p - q) := by
          rw [← Real.rpow_add hz]; congr 1; ring
        rw [e]
        have hzq : 0 < z ^ q := Real.rpow_pos_of_pos hz _
        calc p / q * z ^ q = z ^ q * (p / q) := by ring
          _ ≤ z ^ q * (1 / 2 * z ^ (p - q)) := by
              refine mul_le_mul_of_nonneg_left ?_ hzq.le
              have : 2 * p / q = 2 * (p / q) := by ring
              linarith
          _ = 1 / 2 * (z ^ q * z ^ (p - q)) := by ring
      have hψ1 : twoMonoPsi p q 1 = 1 - p / q := by simp [twoMonoPsi]
      have hpq1 : 1 ≤ p / q := by rw [le_div_iff₀ hq]; linarith
      have hz₁p : 0 ≤ z₁ ^ p := Real.rpow_nonneg (by linarith) _
      unfold twoMonoPhi
      rw [hψ1]
      unfold twoMonoPsi
      nlinarith
  have hint : IntegrableOn (fun z : ℝ ↦ z ^ s * Real.exp (-(B / 2) * z ^ p)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hs hp (by positivity)
  refine (hint.const_mul (Real.exp (B / 2 * z₁ ^ p))).mono' ?_ ?_
  · exact ((measurable_id.pow_const s).mul
      (((measurable_twoMonoPhi p q).const_mul B).neg.exp)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun z hz ↦ ?_)
    have hz : 0 < z := hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hz.le _), Real.abs_exp]
    have := hlow z hz
    calc z ^ s * Real.exp (-(B * twoMonoPhi p q z))
        ≤ z ^ s * Real.exp (-(B * (1 / 2 * z ^ p - 1 / 2 * z₁ ^ p))) := by
          gcongr
      _ = Real.exp (B / 2 * z₁ ^ p) * (z ^ s * Real.exp (-(B / 2) * z ^ p)) := by
          rw [show -(B * (1 / 2 * z ^ p - 1 / 2 * z₁ ^ p)) = B / 2 * z₁ ^ p + -(B / 2) * z ^ p
            by ring, Real.exp_add]
          ring

/-- The rescaled partition function is positive. -/
theorem zNum_one_pos {B : ℝ} (hB : 0 < B) : 0 < zNum p q (fun _ ↦ 1) B := by
  have hint := integrableOn_rpow_mul_exp_neg_twoMonoPhi hq hqp (s := 0) (by norm_num) hB
  unfold zNum
  have hint' : IntegrableOn (fun z : ℝ ↦ (1 : ℝ) * Real.exp (-(B * twoMonoPhi p q z))) (Ioi 0) :=
    hint.congr_fun (fun z hz ↦ by simp [Real.rpow_zero]) measurableSet_Ioi
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun z ↦ by simp [(Real.exp_pos _).le]) hint']
  have hsupp : Function.support (fun z : ℝ ↦ (1 : ℝ) * Real.exp (-(B * twoMonoPhi p q z))) =
      univ :=
    Set.eq_univ_of_forall fun z ↦ Function.mem_support.mpr (by simp [(Real.exp_pos _).ne'])
  rw [hsupp, univ_inter, Real.volume_Ioi]
  simp

/-- Positivity of the rescaled parameter `B = y_b^p`. -/
theorem negB_pos {b : ℝ} (hb : 0 < b) : 0 < negB p q b :=
  Real.rpow_pos_of_pos (negScale_pos hq hqp hb) _

/-- The profile law at `−b` is the rescaled law. -/
theorem profilePosterior_neg_eq {b : ℝ} (hb : 0 < b) (g : ℝ → ℝ) :
    profilePosterior p q g (-b) =
      zNum p q (fun z ↦ g (negScale p q b * z)) (negB p q b) /
        zNum p q (fun _ ↦ 1) (negB p q b) := by
  unfold profilePosterior
  rw [profileNum_neg_eq hq hqp hb g, profileNum_neg_eq hq hqp hb (fun _ ↦ 1)]
  exact mul_div_mul_left _ _ (mul_pos (negScale_pos hq hqp hb) (Real.exp_pos _)).ne'

omit hq hqp in
theorem zNum_rpow_scale {y : ℝ} (hy : 0 < y) (B : ℝ) :
    zNum p q (fun z ↦ (y * z) ^ q) B = y ^ q * zNum p q (fun z ↦ z ^ q) B := by
  unfold zNum
  rw [← MeasureTheory.integral_const_mul (y ^ q)
    (fun z ↦ (fun z ↦ z ^ q) z * Real.exp (-(B * twoMonoPhi p q z)))]
  apply setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ)))
  intro z hz
  have hz : 0 < z := hz
  dsimp only
  rw [Real.mul_rpow hy.le hz.le]
  ring

omit hq hqp in
theorem zNum_rpow_sq_scale {y : ℝ} (hy : 0 < y) (B : ℝ) :
    zNum p q (fun z ↦ (y * z) ^ q * (y * z) ^ q) B =
      y ^ q * y ^ q * zNum p q (fun z ↦ z ^ q * z ^ q) B := by
  unfold zNum
  rw [← MeasureTheory.integral_const_mul (y ^ q * y ^ q)
    (fun z ↦ (fun z ↦ z ^ q * z ^ q) z * Real.exp (-(B * twoMonoPhi p q z)))]
  apply setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ)))
  intro z hz
  have hz : 0 < z := hz
  dsimp only
  rw [Real.mul_rpow hy.le hz.le]
  ring

/-- The scaled variance identity: `Var_{-b}(y^q) · y_b^{p−2q} = B · Var_B(z^q)`. -/
theorem negVar_mul_eq {b : ℝ} (hb : 0 < b) :
    negVar p q b * negScale p q b ^ (p - 2 * q) =
      negB p q b * (zNum p q (fun z ↦ z ^ q * z ^ q) (negB p q b) /
          zNum p q (fun _ ↦ 1) (negB p q b) -
        (zNum p q (fun z ↦ z ^ q) (negB p q b) / zNum p q (fun _ ↦ 1) (negB p q b)) ^ 2) := by
  have hy := negScale_pos hq hqp hb
  unfold negVar
  rw [profilePosterior_neg_eq hq hqp hb, profilePosterior_neg_eq hq hqp hb,
    zNum_rpow_scale hy, zNum_rpow_sq_scale hy]
  have hB : negB p q b = negScale p q b ^ p := rfl
  have hyp : negScale p q b ^ q * negScale p q b ^ q * negScale p q b ^ (p - 2 * q) =
      negScale p q b ^ p := by
    rw [← Real.rpow_add hy, ← Real.rpow_add hy]; congr 1; ring
  rw [hB]
  set y := negScale p q b
  set N0 := zNum p q (fun _ ↦ 1) (y ^ p)
  set N1 := zNum p q (fun z ↦ z ^ q) (y ^ p)
  set N2 := zNum p q (fun z ↦ z ^ q * z ^ q) (y ^ p)
  linear_combination (N2 / N0 - (N1 / N0) ^ 2) * hyp

/-- The half-line Laplace integrals `A_j(B) = √B ∫₀^∞ (√B (z^q − 1))^j e^{-B φ(z)} dz`. -/
noncomputable def negA (p q : ℝ) (j : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt B * ∫ z in Ioi (0 : ℝ),
    (Real.sqrt B * (z ^ q - 1)) ^ j * Real.exp (-(B * twoMonoPhi p q z))

omit hq hqp in
theorem negA_eq (j : ℕ) (B : ℝ) :
    negA p q j B = Real.sqrt B * Real.sqrt B ^ j * zNum p q (fun z ↦ (z ^ q - 1) ^ j) B := by
  unfold negA zNum
  rw [mul_assoc, ← MeasureTheory.integral_const_mul (Real.sqrt B ^ j)
    (fun z ↦ (fun z ↦ (z ^ q - 1) ^ j) z * Real.exp (-(B * twoMonoPhi p q z)))]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ)))
  intro z _
  dsimp only
  rw [mul_pow]
  ring

/-- Integrability of `z^q z^q e^{-Bφ}`. -/
theorem integrableOn_rpow_sq_mul_exp_neg_twoMonoPhi {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun z : ℝ ↦ z ^ q * z ^ q * Real.exp (-(B * twoMonoPhi p q z))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_twoMonoPhi hq hqp (s := q + q) (by linarith) hB).congr_fun
    (fun z hz ↦ ?_) measurableSet_Ioi
  have hz : 0 < z := hz
  dsimp only
  rw [Real.rpow_add hz]

theorem integrableOn_exp_neg_twoMonoPhi {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun z : ℝ ↦ Real.exp (-(B * twoMonoPhi p q z))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_twoMonoPhi hq hqp (s := 0) (by norm_num) hB).congr_fun
    (fun z _ ↦ ?_) measurableSet_Ioi
  simp [Real.rpow_zero]

/-- `∫ (z^q − 1) e^{-Bφ} = N₁ − N₀`. -/
theorem zNum_sub_one {B : ℝ} (hB : 0 < B) :
    zNum p q (fun z ↦ z ^ q - 1) B = zNum p q (fun z ↦ z ^ q) B - zNum p q (fun _ ↦ 1) B := by
  unfold zNum
  have h1 : IntegrableOn (fun z : ℝ ↦ z ^ q * Real.exp (-(B * twoMonoPhi p q z))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_twoMonoPhi hq hqp (by linarith) hB
  have h0 : IntegrableOn (fun z : ℝ ↦ (1 : ℝ) * Real.exp (-(B * twoMonoPhi p q z))) (Ioi 0) :=
    (integrableOn_exp_neg_twoMonoPhi hq hqp hB).congr_fun (fun z _ ↦ by simp) measurableSet_Ioi
  rw [← MeasureTheory.integral_sub h1 h0]
  refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun z _ ↦ ?_
  dsimp only
  ring

/-- `∫ (z^q − 1)² e^{-Bφ} = N₂ − 2N₁ + N₀`. -/
theorem zNum_sub_one_sq {B : ℝ} (hB : 0 < B) :
    zNum p q (fun z ↦ (z ^ q - 1) ^ 2) B =
      zNum p q (fun z ↦ z ^ q * z ^ q) B - 2 * zNum p q (fun z ↦ z ^ q) B +
        zNum p q (fun _ ↦ 1) B := by
  unfold zNum
  have h2 := integrableOn_rpow_sq_mul_exp_neg_twoMonoPhi hq hqp hB
  have h1 : IntegrableOn (fun z : ℝ ↦ z ^ q * Real.exp (-(B * twoMonoPhi p q z))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_twoMonoPhi hq hqp (by linarith) hB
  have h0 : IntegrableOn (fun z : ℝ ↦ (1 : ℝ) * Real.exp (-(B * twoMonoPhi p q z))) (Ioi 0) :=
    (integrableOn_exp_neg_twoMonoPhi hq hqp hB).congr_fun (fun z _ ↦ by simp) measurableSet_Ioi
  have h1' : IntegrableOn (fun z : ℝ ↦ 2 * (z ^ q * Real.exp (-(B * twoMonoPhi p q z)))) (Ioi 0) :=
    h1.const_mul 2
  have h21 : IntegrableOn (fun z : ℝ ↦ z ^ q * z ^ q * Real.exp (-(B * twoMonoPhi p q z)) -
      2 * (z ^ q * Real.exp (-(B * twoMonoPhi p q z)))) (Ioi 0) := h2.sub h1'
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub h2 h1',
    ← MeasureTheory.integral_add h21 h0]
  refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun z _ ↦ ?_
  dsimp only
  ring

/-- `B · Var_B(z^q) = A₂/A₀ − (A₁/A₀)²`. -/
theorem mul_zVar_eq_negA {B : ℝ} (hB : 0 < B) :
    B * (zNum p q (fun z ↦ z ^ q * z ^ q) B / zNum p q (fun _ ↦ 1) B -
        (zNum p q (fun z ↦ z ^ q) B / zNum p q (fun _ ↦ 1) B) ^ 2) =
      negA p q 2 B / negA p q 0 B - (negA p q 1 B / negA p q 0 B) ^ 2 := by
  have hN0 := zNum_one_pos hq hqp hB
  have h0 : zNum p q (fun z ↦ (z ^ q - 1) ^ 0) B = zNum p q (fun _ ↦ 1) B := by
    simp only [pow_zero]
  have h1 : zNum p q (fun z ↦ (z ^ q - 1) ^ 1) B = zNum p q (fun z ↦ z ^ q - 1) B := by
    simp only [pow_one]
  rw [negA_eq, negA_eq, negA_eq, h0, h1, pow_zero, pow_one, mul_one, zNum_sub_one hq hqp hB,
    zNum_sub_one_sq hq hqp hB]
  set N0 := zNum p q (fun _ ↦ 1) B
  set N1 := zNum p q (fun z ↦ z ^ q) B
  set N2 := zNum p q (fun z ↦ z ^ q * z ^ q) B
  set s := Real.sqrt B with hs
  have hss : s * s = B := Real.mul_self_sqrt hB.le
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hB).ne'
  clear_value s
  subst hss
  field_simp
  ring

end Params

/-- The polynomial envelope of the rescaled observable `(√B((1 + w/√B)^q − 1))^j`. -/
theorem abs_sqrt_mul_rpow_sub_one_pow_le {q : ℝ} (hq : 0 < q) (j : ℕ) {B : ℝ} (hB : 1 ≤ B) {w : ℝ}
    (hw : -Real.sqrt B < w) :
    |(Real.sqrt B * ((1 + w / Real.sqrt B) ^ q - 1)) ^ j| ≤
      (max q 1 * 2 ^ ⌈q⌉₊) ^ j * (1 + |w|) ^ (j * (⌈q⌉₊ + 1)) := by
  set n₀ := ⌈q⌉₊
  have hsB : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
  have hsB0 : 0 < Real.sqrt B := by linarith
  set z := 1 + w / Real.sqrt B with hz
  have hwB : -1 < w / Real.sqrt B := by rw [lt_div_iff₀ hsB0]; linarith
  have hz0 : 0 < z := by rw [hz]; linarith
  have hz1 : z - 1 = w / Real.sqrt B := by rw [hz]; ring
  have hkey : |Real.sqrt B * (z ^ q - 1)| ≤ max q 1 * 2 ^ n₀ * (1 + |w|) ^ (n₀ + 1) := by
    have h1 := abs_rpow_sub_one_le hq (Nat.le_ceil q) hz0
    rw [abs_mul, abs_of_pos hsB0]
    have hw' : Real.sqrt B * |z - 1| = |w| := by
      rw [hz1, abs_div, abs_of_pos hsB0]; field_simp
    have h1z : 1 + z ≤ 2 * (1 + |w|) := by
      have : w / Real.sqrt B ≤ |w| :=
        calc w / Real.sqrt B ≤ |w| / Real.sqrt B :=
              div_le_div_of_nonneg_right (le_abs_self w) hsB0.le
          _ ≤ |w| := div_le_self (abs_nonneg w) hsB
      rw [hz]; linarith [abs_nonneg w]
    have h2 : (1 + z) ^ n₀ ≤ 2 ^ n₀ * (1 + |w|) ^ n₀ := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1z n₀
    have hm : 0 ≤ max q 1 := le_trans zero_le_one (le_max_right _ _)
    calc Real.sqrt B * |z ^ q - 1|
        ≤ Real.sqrt B * (max q 1 * |z - 1| * (1 + z) ^ n₀) :=
          mul_le_mul_of_nonneg_left h1 hsB0.le
      _ = max q 1 * (Real.sqrt B * |z - 1|) * (1 + z) ^ n₀ := by ring
      _ = max q 1 * |w| * (1 + z) ^ n₀ := by rw [hw']
      _ ≤ max q 1 * (1 + |w|) * (2 ^ n₀ * (1 + |w|) ^ n₀) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg w]) hm) h2
            (by positivity) (by positivity)
      _ = max q 1 * 2 ^ n₀ * (1 + |w|) ^ (n₀ + 1) := by ring
  rw [abs_pow, pow_mul', ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hkey j

section Limits

variable {p q : ℝ} (hq : 0 < q) (hqp : q < p)
include hq hqp

/-- **Half-line Laplace asymptotics of the moments**: `A_j(B) → ∫ (q w)^j e^{-κ w²/2} dw`,
`κ = p(p−q)`. -/
theorem tendsto_negA (j : ℕ) :
    Tendsto (fun B ↦ negA p q j B) atTop
      (𝓝 (∫ w : ℝ, (q * w) ^ j * Real.exp (-(p * (p - q) / 2 * w ^ 2)))) := by
  have hp : 0 < p := by linarith
  set z₁ := max 2 ((2 * p / q) ^ (1 / (p - q))) with hz₁
  have hz₁1 : 1 < z₁ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨c₁, hc₁, hquad⟩ := twoMonoPhi_quad_bound hq hqp (z₁ := z₁) hz₁1.le
  have h := tendsto_sqrt_mul_integral (measurable_twoMonoPhi p q) (twoMonoPhi_one p q)
    (κ := p * (p - q)) hc₁ (c₂ := 1 / 2) (by norm_num) hz₁1 hquad (α := min p 1)
    (lt_min hp one_pos) (min_le_right _ _) (fun z hz ↦ twoMonoPhi_coercive hq hqp hz)
    (twoMonoPhi_div_sq_tendsto hq)
    (G := fun B w ↦ (Real.sqrt B * ((1 + w / Real.sqrt B) ^ q - 1)) ^ j)
    (Ginf := fun w ↦ (q * w) ^ j)
    (fun B ↦ ((measurable_const.mul (((measurable_const.add
      (measurable_id.div_const _)).pow_const q).sub measurable_const)).pow_const j))
    (C := (max q 1 * 2 ^ ⌈q⌉₊) ^ j) (n := j * (⌈q⌉₊ + 1))
    (fun B hB w hw ↦ abs_sqrt_mul_rpow_sub_one_pow_le hq j hB hw)
    (fun w ↦ (tendsto_sqrt_mul_rpow_sub_one q w).pow j)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  unfold negA
  congr 1
  refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun z _ ↦ ?_
  have e : 1 + Real.sqrt B * (z - 1) / Real.sqrt B = z := by
    field_simp
    ring
  rw [e]

/-- **The rescaled variance limit**: `B · Var_B(z^q) → q²/(p(p−q))`. -/
theorem tendsto_mul_zVar :
    Tendsto (fun B ↦ B * (zNum p q (fun z ↦ z ^ q * z ^ q) B / zNum p q (fun _ ↦ 1) B -
        (zNum p q (fun z ↦ z ^ q) B / zNum p q (fun _ ↦ 1) B) ^ 2)) atTop
      (𝓝 (q ^ 2 / (p * (p - q)))) := by
  have hκ : 0 < p * (p - q) := mul_pos (by linarith) (by linarith)
  set κ := p * (p - q) with hκdef
  set L0 := ∫ w : ℝ, Real.exp (-(κ / 2 * w ^ 2)) with hL0
  have hL0pos : 0 < L0 := by
    rw [hL0, integral_exp_neg_half_mul_sq hκ]
    exact div_pos (mul_pos (Real.sqrt_pos.mpr two_pos) (Real.sqrt_pos.mpr Real.pi_pos))
      (Real.sqrt_pos.mpr hκ)
  have h0 : Tendsto (fun B ↦ negA p q 0 B) atTop (𝓝 L0) := by
    have := tendsto_negA hq hqp 0
    simpa only [pow_zero, one_mul] using this
  have h1 : Tendsto (fun B ↦ negA p q 1 B) atTop (𝓝 0) := by
    have := tendsto_negA hq hqp 1
    have e : (∫ w : ℝ, (q * w) ^ 1 * Real.exp (-(κ / 2 * w ^ 2))) = 0 := by
      simp_rw [pow_one, mul_assoc]
      rw [MeasureTheory.integral_const_mul, integral_mul_exp_neg_half_mul_sq, mul_zero]
    rwa [e] at this
  have h2 : Tendsto (fun B ↦ negA p q 2 B) atTop (𝓝 (q ^ 2 * (1 / κ) * L0)) := by
    have := tendsto_negA hq hqp 2
    have e : (∫ w : ℝ, (q * w) ^ 2 * Real.exp (-(κ / 2 * w ^ 2))) = q ^ 2 * (1 / κ) * L0 := by
      simp_rw [mul_pow, mul_assoc]
      rw [MeasureTheory.integral_const_mul, integral_sq_mul_exp_neg_half_mul_sq hκ, hL0]
    rwa [e] at this
  have hlim := (h2.div h0 hL0pos.ne').sub ((h1.div h0 hL0pos.ne').pow 2)
  have e : q ^ 2 * (1 / κ) * L0 / L0 - (0 / L0) ^ 2 = q ^ 2 / κ := by
    field_simp
    ring
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  simp only [Pi.div_apply]
  exact (mul_zVar_eq_negA hq hqp hB).symm

/-- `B = y_b^p → ∞` as `b → ∞`. -/
theorem tendsto_negB : Tendsto (fun b ↦ negB p q b) atTop atTop := by
  have hp : 0 < p := by linarith
  have h1 : Tendsto (fun b : ℝ ↦ q * b / p) atTop atTop :=
    (tendsto_id.const_mul_atTop hq).atTop_div_const hp
  have h2 := (tendsto_rpow_atTop (one_div_pos.mpr (sub_pos.mpr hqp))).comp h1
  exact (tendsto_rpow_atTop hp).comp h2

/-- **Profile matching in the negative chamber**:
`Var_{-b}(y^q) · y_b^{p−2q} → q²/(p(p−q))`, `y_b = (qb/p)^{1/(p−q)}`. -/
theorem tendsto_negVar_mul_rpow :
    Tendsto (fun b ↦ negVar p q b * negScale p q b ^ (p - 2 * q)) atTop
      (𝓝 (q ^ 2 / (p * (p - q)))) := by
  refine ((tendsto_mul_zVar hq hqp).comp (tendsto_negB hq hqp)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  simp only [Function.comp_apply]
  exact (negVar_mul_eq hq hqp hb).symm

/-- The same statement in the wall coordinate:
`Var_{-b}(y^q) · (qb/p)^{(p−2q)/(p−q)} → q²/(p(p−q))`, i.e.
`Var_{-b}(y^q) ~ (q²/(p(p−q))) (qb/p)^{(2q−p)/(p−q)}`. -/
theorem tendsto_negVar_mul_rpow' :
    Tendsto (fun b ↦ negVar p q b * (q * b / p) ^ ((p - 2 * q) / (p - q))) atTop
      (𝓝 (q ^ 2 / (p * (p - q)))) := by
  have hp : 0 < p := by linarith
  refine (tendsto_negVar_mul_rpow hq hqp).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  congr 1
  unfold negScale
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  field_simp

end Limits

end Laplace.Multi
