/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.GaussianMoments
import Laplace.OneD.MonomialPotential
import Laplace.Gibbs

/-!
# Expansion-based recovery of a subleading coefficient

The germbij note's Section 7.4 pairing mechanism in its smallest
instance. For the quartic-perturbed harmonic potential
`x²/2 + b·x⁴` with `b ≥ 0`, the partition function has the expansion
`Z_b(t) = √(2π)·t^(-1/2) - 3b·√(2π)·t^(-3/2) + E` with
`0 ≤ E ≤ 105·b²·√(2π)·t^(-5/2)`
(`quartic_partition_expansion_bounds`): the main and correction terms
come from the `k = 0` and `k = 2` Gaussian moments exactly, and the
error is the integrated second-order exponential remainder, bounded by
the `k = 4` moment through the elementary inequality
`0 ≤ e^(-s) - 1 + s ≤ s²` (`exp_neg_sub_one_add_bounds`). Consequently
the coefficient `b` is recoverable from the expansion: eventual equality
of partition functions forces equality of coefficients
(`quartic_coefficient_recovery_of_eventuallyEq`) — the correction at
order `t^(-3/2)` is the pairing that reads off `b`.
-/

open Real MeasureTheory Filter

namespace Laplace.OneD

/-- Second-order bounds for the exponential remainder: for `s ≥ 0`,
`0 ≤ e^(-s) - 1 + s ≤ s²`. -/
lemma exp_neg_sub_one_add_bounds {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ Real.exp (-s) - 1 + s ∧ Real.exp (-s) - 1 + s ≤ s ^ 2 := by
  constructor
  · have h := Real.add_one_le_exp (-s)
    linarith
  · have hmul : Real.exp (-s) * (1 + s) ≤ 1 := by
      calc Real.exp (-s) * (1 + s) = (s + 1) * Real.exp (-s) := by ring
        _ ≤ Real.exp s * Real.exp (-s) :=
            mul_le_mul_of_nonneg_right (Real.add_one_le_exp s)
              (Real.exp_pos (-s)).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hu : (0 : ℝ) < 1 + s := by linarith
    have hX1 : (Real.exp (-s) - 1 + s) * (1 + s) ≤ s ^ 2 * (1 + s) := by
      nlinarith [sq_nonneg s]
    exact le_of_mul_le_mul_right hX1 hu

/-- The quartic-perturbed partition function equals its two-term
expansion plus a nonnegative error bounded at order `t^(-5/2)`:
`0 ≤ Z_b(t) - √(2π)·t^(-1/2) + 3b·√(2π)·t^(-3/2)
   ≤ 105·b²·√(2π)·t^(-5/2)`. -/
theorem quartic_partition_expansion_bounds {b t : ℝ} (hb : 0 ≤ b)
    (ht : 0 < t) :
    0 ≤ partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t
        - Real.sqrt (2 * π) * t ^ (-(1 : ℝ) / 2)
        + 3 * b * Real.sqrt (2 * π) * t ^ (-(3 : ℝ) / 2) ∧
      partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t
        - Real.sqrt (2 * π) * t ^ (-(1 : ℝ) / 2)
        + 3 * b * Real.sqrt (2 * π) * t ^ (-(3 : ℝ) / 2)
      ≤ 105 * b ^ 2 * Real.sqrt (2 * π) * t ^ (-(5 : ℝ) / 2) := by
  set q : ℝ → ℝ := fun x ↦ Real.exp (-(t * x ^ 2) / 2) with hq_def
  set r : ℝ → ℝ := fun x ↦
    Real.exp (-(t * b * x ^ 4)) - 1 + t * b * x ^ 4 with hr_def
  -- Pointwise remainder bounds from the elementary inequality.
  have hr_bounds : ∀ x : ℝ, 0 ≤ r x ∧ r x ≤ (t * b) ^ 2 * x ^ 8 := by
    intro x
    have hs : 0 ≤ t * b * x ^ 4 := by positivity
    obtain ⟨h0, h1⟩ := exp_neg_sub_one_add_bounds hs
    refine ⟨h0, h1.trans_eq ?_⟩
    ring
  have hq_pos : ∀ x : ℝ, 0 < q x := fun x ↦ Real.exp_pos _
  -- Integrability of the moment family.
  have hint_pow : ∀ n : ℕ,
      Integrable (fun x : ℝ ↦ x ^ n * q x) := by
    intro n
    have h := kth_integrable_pow (k := 1) le_rfl n ht
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [hq_def]
    congr 2
    rw [show ((Nat.factorial (2 * 1) : ℕ) : ℝ) = 2 by norm_num [Nat.factorial]]
    ring
  have hint_q : Integrable q := by
    have := hint_pow 0
    simpa using this
  have hint_x4q : Integrable (fun x : ℝ ↦ t * b * (x ^ 4 * q x)) :=
    (hint_pow 4).const_mul _
  have hint_lin : Integrable (fun x : ℝ ↦ q x - t * b * (x ^ 4 * q x)) :=
    hint_q.sub hint_x4q
  -- The remainder-carrying integrand and its domination.
  have hint_qr : Integrable (fun x ↦ q x * r x) := by
    have hg : Integrable (fun x : ℝ ↦ (t * b) ^ 2 * (x ^ 8 * q x)) :=
      (hint_pow 8).const_mul _
    apply hg.mono'
    · apply Continuous.aestronglyMeasurable
      simp only [hq_def, hr_def]
      fun_prop
    · filter_upwards with x
      obtain ⟨h0, h1⟩ := hr_bounds x
      rw [Real.norm_of_nonneg (mul_nonneg (hq_pos x).le h0)]
      calc q x * r x ≤ q x * ((t * b) ^ 2 * x ^ 8) :=
            mul_le_mul_of_nonneg_left h1 (hq_pos x).le
        _ = (t * b) ^ 2 * (x ^ 8 * q x) := by ring
  -- The partition function in split form.
  have hZ : partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t =
      ∫ x, (q x - t * b * (x ^ 4 * q x) + q x * r x) := by
    unfold partitionFunction
    congr 1
    funext x
    simp only [hq_def, hr_def]
    rw [show -(t * (x ^ 2 / 2 + b * x ^ 4)) =
        -(t * x ^ 2) / 2 + -(t * b * x ^ 4) by ring, Real.exp_add]
    ring
  -- Integrate the three pieces.
  have hsplit : partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t =
      (∫ x, q x) - t * b * (∫ x, x ^ 4 * q x) + ∫ x, q x * r x := by
    rw [hZ]
    rw [MeasureTheory.integral_add hint_lin hint_qr]
    rw [MeasureTheory.integral_sub hint_q hint_x4q]
    rw [MeasureTheory.integral_const_mul]
  -- Closed forms for the two moments.
  have hm0 : (∫ x, q x) = Real.sqrt (2 * π) * t ^ (-(1 : ℝ) / 2) := by
    have h := integral_pow_mul_exp_neg_t_sq_half 0 ht
    simp only [hq_def]
    norm_num [Nat.doubleFactorial] at h ⊢
    linarith [h]
  have hm2 : (∫ x, x ^ 4 * q x) =
      3 * Real.sqrt (2 * π) * t ^ (-(5 : ℝ) / 2) := by
    have h := integral_pow_mul_exp_neg_t_sq_half 2 ht
    simp only [hq_def]
    norm_num [Nat.doubleFactorial] at h ⊢
    linarith [h]
  -- rpow product identity.
  have hpow : t * t ^ (-(5 : ℝ) / 2) = t ^ (-(3 : ℝ) / 2) := by
    nth_rewrite 1 [← Real.rpow_one t]
    rw [← Real.rpow_add ht]
    norm_num
  -- The expansion error is exactly the remainder integral.
  have hE : partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t
      - Real.sqrt (2 * π) * t ^ (-(1 : ℝ) / 2)
      + 3 * b * Real.sqrt (2 * π) * t ^ (-(3 : ℝ) / 2) =
      ∫ x, q x * r x := by
    rw [hsplit, hm0, hm2, ← hpow]
    ring
  rw [hE]
  constructor
  · exact MeasureTheory.integral_nonneg fun x ↦
      mul_nonneg (hq_pos x).le (hr_bounds x).1
  · have hg : Integrable (fun x : ℝ ↦ (t * b) ^ 2 * (x ^ 8 * q x)) :=
      (hint_pow 8).const_mul _
    have hle : (∫ x, q x * r x) ≤ ∫ x, (t * b) ^ 2 * (x ^ 8 * q x) := by
      apply MeasureTheory.integral_mono hint_qr hg
      intro x
      obtain ⟨h0, h1⟩ := hr_bounds x
      calc q x * r x ≤ q x * ((t * b) ^ 2 * x ^ 8) :=
            mul_le_mul_of_nonneg_left h1 (hq_pos x).le
        _ = (t * b) ^ 2 * (x ^ 8 * q x) := by ring
    refine hle.trans ?_
    have hm4 : (∫ x, x ^ 8 * q x) =
        105 * Real.sqrt (2 * π) * t ^ (-(9 : ℝ) / 2) := by
      have h := integral_pow_mul_exp_neg_t_sq_half 4 ht
      simp only [hq_def]
      norm_num [Nat.doubleFactorial] at h ⊢
      linarith [h]
    rw [MeasureTheory.integral_const_mul, hm4]
    have hpow2 : t ^ 2 * t ^ (-(9 : ℝ) / 2) = t ^ (-(5 : ℝ) / 2) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]
      norm_num
    apply le_of_eq
    calc (t * b) ^ 2 * (105 * Real.sqrt (2 * π) * t ^ (-(9 : ℝ) / 2))
        = 105 * b ^ 2 * Real.sqrt (2 * π) *
            (t ^ 2 * t ^ (-(9 : ℝ) / 2)) := by ring
      _ = 105 * b ^ 2 * Real.sqrt (2 * π) * t ^ (-(5 : ℝ) / 2) := by
          rw [hpow2]

/-- **Expansion-based recovery of the quartic coefficient** (germbij
Section 7.4 pairing, first instance). If the partition functions of
`x²/2 + b₁·x⁴` and `x²/2 + b₂·x⁴` (with `b₁, b₂ ≥ 0`) eventually agree,
then `b₁ = b₂`: the coefficient is read off from the `t^(-3/2)`
correction of the expansion. -/
theorem quartic_coefficient_recovery_of_eventuallyEq {b₁ b₂ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (h : (fun t ↦ partitionFunction (fun x ↦ x ^ 2 / 2 + b₁ * x ^ 4) t)
      =ᶠ[atTop] fun t ↦
        partitionFunction (fun x ↦ x ^ 2 / 2 + b₂ * x ^ 4) t) :
    b₁ = b₂ := by
  by_contra hne
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  set D : ℝ := |b₁ - b₂| with hD_def
  have hD : 0 < D := abs_pos.mpr (sub_ne_zero.mpr hne)
  set S : ℝ := b₁ ^ 2 + b₂ ^ 2 with hS_def
  have hS : 0 ≤ S := by positivity
  set t : ℝ := max T 1 + 35 * S / D + 1 with ht_def
  have htT : T ≤ t := by
    have h1 : T ≤ max T 1 := le_max_left _ _
    have h2 : 0 ≤ 35 * S / D := by positivity
    linarith
  have ht0 : (0 : ℝ) < t := by
    have h1 : (1 : ℝ) ≤ max T 1 := le_max_right _ _
    have h2 : 0 ≤ 35 * S / D := by positivity
    linarith
  obtain ⟨hlo₁, hhi₁⟩ := quartic_partition_expansion_bounds hb₁ ht0
  obtain ⟨hlo₂, hhi₂⟩ := quartic_partition_expansion_bounds hb₂ ht0
  have heq := hT t htT
  simp only at heq
  have hsqrt : (0 : ℝ) < Real.sqrt (2 * π) :=
    Real.sqrt_pos.mpr (by positivity)
  have htpow : (0 : ℝ) < t ^ (-(5 : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
  have hnn₁ : 0 ≤ 105 * b₁ ^ 2 * Real.sqrt (2 * π) * t ^ (-(5 : ℝ) / 2) :=
    by positivity
  have hnn₂ : 0 ≤ 105 * b₂ ^ 2 * Real.sqrt (2 * π) * t ^ (-(5 : ℝ) / 2) :=
    by positivity
  -- The difference of the two expansion errors is the correction gap.
  have hgap : |3 * (b₁ - b₂) * Real.sqrt (2 * π) * t ^ (-(3 : ℝ) / 2)|
      ≤ 105 * S * Real.sqrt (2 * π) * t ^ (-(5 : ℝ) / 2) := by
    rw [abs_le, hS_def]
    constructor <;> nlinarith [hhi₁, hhi₂, hlo₁, hlo₂, heq, hnn₁, hnn₂]
  -- Cancel the positive factor √(2π)·t^(-5/2) after t^(-3/2) = t·t^(-5/2).
  have hpow : t ^ (-(3 : ℝ) / 2) = t * t ^ (-(5 : ℝ) / 2) := by
    nth_rewrite 2 [← Real.rpow_one t]
    rw [← Real.rpow_add ht0]
    norm_num
  have habs : |3 * (b₁ - b₂) * Real.sqrt (2 * π) *
      (t * t ^ (-(5 : ℝ) / 2))| =
      3 * D * t * (Real.sqrt (2 * π) * t ^ (-(5 : ℝ) / 2)) := by
    rw [abs_mul, abs_mul, abs_mul]
    rw [abs_of_nonneg hsqrt.le, abs_of_nonneg (mul_pos ht0 htpow).le]
    rw [show |(3 : ℝ)| = 3 from abs_of_nonneg (by norm_num)]
    rw [hD_def]
    ring
  rw [hpow, habs] at hgap
  have hkey : 3 * D * t ≤ 105 * S := by
    have h' := hgap.trans_eq
      (show 105 * S * Real.sqrt (2 * π) * t ^ (-(5 : ℝ) / 2) =
        105 * S * (Real.sqrt (2 * π) * t ^ (-(5 : ℝ) / 2)) by ring)
    exact le_of_mul_le_mul_right h' (mul_pos hsqrt htpow)
  -- But t was chosen large enough to contradict this.
  have hmax : (1 : ℝ) ≤ max T 1 := le_max_right _ _
  have hexp : 3 * D * t = 3 * D * max T 1 + 105 * S + 3 * D := by
    rw [ht_def]
    field_simp
    ring
  have hnn : 0 ≤ 3 * D * max T 1 :=
    mul_nonneg (by positivity) (le_trans zero_le_one hmax)
  linarith [hkey, hexp, hnn, hD]

end Laplace.OneD
