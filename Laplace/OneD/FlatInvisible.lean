/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.GaussianMoments
import Laplace.OneD.IntegralRemainder

/-!
# Flat perturbations are invisible to the expansions

The quantitative core of the germbij note's Proposition 4.1, the
analyticity-necessity half of the note's story: perturbing the harmonic
potential by a nonnegative function that is flat at the minimum changes
every compactly-supported-observable integral by less than any power of
`1/t` (`flat_perturbation_invisible`). No expansion machinery is
needed: the pointwise identity
`e^(-tL) - e^(-t(L+f)) = e^(-tL)·(1 - e^(-tf))` with
`1 - e^(-s) ≤ s`, together with a global polynomial domination of `f`
(flatness near `0`; boundedness absorbed polynomially away from it),
reduces the difference to a single closed-form Gaussian moment at
arbitrarily high order. This is the exact counterpoint to the
identifiability theorem: its sector bound needs the finite vanishing
order that flatness destroys, and here flatness indeed hides the
perturbation beyond all orders.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- **Flat perturbations are invisible** (germbij Proposition 4.1,
quantitative core). If `f` is continuous, `0 ≤ f ≤ M`, and flat at `0`
(dominated by every even power on a neighborhood), then for every
continuous compactly supported `φ` and every `N`, the perturbed and
unperturbed integrals differ by `O(t^(-N))`. -/
theorem flat_perturbation_invisible
    {f φ : ℝ → ℝ} {M : ℝ} (hf_c : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hf_bdd : ∀ x, f x ≤ M)
    (hflat : ∀ n : ℕ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ x : ℝ, |x| ≤ δ → f x ≤ C * x ^ (2 * n))
    (hφ_c : Continuous φ) (hφ_s : HasCompactSupport φ) :
    ∀ N : ℕ, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |(∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2)))) -
        ∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2 + f x)))| ≤
      K / t ^ N := by
  intro N
  obtain ⟨C, δ, hC, hδ, hnear⟩ := hflat (N + 1)
  -- A global bound for |φ|.
  obtain ⟨B, hB⟩ := hφ_s.exists_bound_of_continuousOn hφ_c.continuousOn
  set Mφ : ℝ := max B 0 with hMφ_def
  have hMφ : ∀ x, |φ x| ≤ Mφ := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · calc |φ x| = ‖φ x‖ := (Real.norm_eq_abs _).symm
        _ ≤ B := hB x hx
        _ ≤ Mφ := le_max_left _ _
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
      exact le_max_right _ _
  have hMφ0 : 0 ≤ Mφ := le_max_right _ _
  -- Global polynomial domination of f.
  have hM0 : 0 ≤ M := le_trans (hf0 0) (hf_bdd 0)
  set D : ℝ := M / δ ^ (2 * (N + 1)) with hD_def
  have hD0 : 0 ≤ D := by positivity
  have hdom : ∀ x : ℝ, f x ≤ (C + D) * x ^ (2 * (N + 1)) := by
    intro x
    have hx2 : (0 : ℝ) ≤ x ^ (2 * (N + 1)) := by
      rw [pow_mul]
      positivity
    rcases le_total |x| δ with hx | hx
    · calc f x ≤ C * x ^ (2 * (N + 1)) := hnear x hx
        _ ≤ (C + D) * x ^ (2 * (N + 1)) := by nlinarith
    · have habs : x ^ (2 * (N + 1)) = |x| ^ (2 * (N + 1)) := by
        rw [pow_mul, pow_mul, sq_abs]
      have h1 : δ ^ (2 * (N + 1)) ≤ x ^ (2 * (N + 1)) := by
        rw [habs]
        exact pow_le_pow_left₀ hδ.le hx _
      have h2 : M ≤ D * x ^ (2 * (N + 1)) := by
        rw [hD_def, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left h1 hM0]
      calc f x ≤ M := hf_bdd x
        _ ≤ D * x ^ (2 * (N + 1)) := h2
        _ ≤ (C + D) * x ^ (2 * (N + 1)) := by nlinarith
  -- The constant.
  refine ⟨Mφ * (C + D) * (Nat.doubleFactorial (2 * (N + 1) - 1) : ℝ) * Real.sqrt (2 * π),
    1, by positivity, le_refl 1, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  -- Integrability of the two integrands.
  have hint1 : Integrable
      (fun x : ℝ ↦ φ x * Real.exp (-(t * (x ^ 2 / 2)))) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    apply HasCompactSupport.intro hφ_s
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hint2 : Integrable
      (fun x : ℝ ↦ φ x * Real.exp (-(t * (x ^ 2 / 2 + f x)))) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    apply HasCompactSupport.intro hφ_s
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  -- The comparison integrand.
  have hint_g : Integrable (fun x : ℝ ↦
      Mφ * (C + D) * t * (x ^ (2 * (N + 1)) *
        Real.exp (-(t * x ^ 2) / 2))) := by
    have h := integrable_pow_mul_exp_neg_mul_sq
      (c := t / 2) (by positivity) (2 * (N + 1))
    exact (h.congr (Filter.Eventually.of_forall fun x ↦ by
      ring)).const_mul _
  -- Pointwise bound on the difference of integrands.
  have hpt : ∀ x : ℝ,
      |φ x * Real.exp (-(t * (x ^ 2 / 2))) -
        φ x * Real.exp (-(t * (x ^ 2 / 2 + f x)))| ≤
      Mφ * (C + D) * t * (x ^ (2 * (N + 1)) *
        Real.exp (-(t * x ^ 2) / 2)) := by
    intro x
    have hexp_pos : (0 : ℝ) < Real.exp (-(t * (x ^ 2 / 2))) :=
      Real.exp_pos _
    have hsplit : Real.exp (-(t * (x ^ 2 / 2 + f x))) =
        Real.exp (-(t * (x ^ 2 / 2))) * Real.exp (-(t * f x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hone : 0 ≤ 1 - Real.exp (-(t * f x)) ∧
        1 - Real.exp (-(t * f x)) ≤ t * f x := by
      constructor
      · have : Real.exp (-(t * f x)) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
          apply Real.exp_le_exp.mpr
          have := hf0 x
          nlinarith
        linarith
      · have h := Real.add_one_le_exp (-(t * f x))
        linarith
    calc |φ x * Real.exp (-(t * (x ^ 2 / 2))) -
          φ x * Real.exp (-(t * (x ^ 2 / 2 + f x)))|
        = |φ x| * (Real.exp (-(t * (x ^ 2 / 2))) *
            (1 - Real.exp (-(t * f x)))) := by
          rw [hsplit, show φ x * Real.exp (-(t * (x ^ 2 / 2))) -
            φ x * (Real.exp (-(t * (x ^ 2 / 2))) *
              Real.exp (-(t * f x))) =
            φ x * (Real.exp (-(t * (x ^ 2 / 2))) *
              (1 - Real.exp (-(t * f x)))) by ring, abs_mul]
          congr 1
          exact abs_of_nonneg (by nlinarith [hone.1, hexp_pos.le])
      _ ≤ Mφ * (Real.exp (-(t * (x ^ 2 / 2))) * (t * f x)) := by
          apply mul_le_mul (hMφ x) _ (by nlinarith [hone.1, hexp_pos.le])
            hMφ0
          apply mul_le_mul_of_nonneg_left hone.2 hexp_pos.le
      _ ≤ Mφ * (Real.exp (-(t * (x ^ 2 / 2))) *
            (t * ((C + D) * x ^ (2 * (N + 1))))) := by
          apply mul_le_mul_of_nonneg_left _ hMφ0
          apply mul_le_mul_of_nonneg_left _ hexp_pos.le
          apply mul_le_mul_of_nonneg_left (hdom x) ht0.le
      _ = Mφ * (C + D) * t * (x ^ (2 * (N + 1)) *
            Real.exp (-(t * x ^ 2) / 2)) := by
          rw [show -(t * (x ^ 2 / 2)) = -(t * x ^ 2) / 2 by ring]
          ring
  -- Assemble.
  have hmom := integral_pow_mul_exp_neg_t_sq_half (N + 1) ht0
  calc |(∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2)))) -
        ∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2 + f x)))|
      = |∫ x : ℝ, (φ x * Real.exp (-(t * (x ^ 2 / 2))) -
          φ x * Real.exp (-(t * (x ^ 2 / 2 + f x))))| := by
        rw [integral_sub hint1 hint2]
    _ ≤ ∫ x : ℝ, |φ x * Real.exp (-(t * (x ^ 2 / 2))) -
          φ x * Real.exp (-(t * (x ^ 2 / 2 + f x)))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, Mφ * (C + D) * t * (x ^ (2 * (N + 1)) *
          Real.exp (-(t * x ^ 2) / 2)) :=
        integral_mono (hint1.sub hint2).abs hint_g hpt
    _ = Mφ * (C + D) * t * ((Nat.doubleFactorial (2 * (N + 1) - 1) : ℝ) *
          Real.sqrt (2 * π) * t ^ (-(((N + 1) : ℕ) : ℝ) - 1 / 2)) := by
        rw [integral_const_mul]
        congr 1
        rw [hmom]
        congr 1
        push_cast
        ring
    _ ≤ Mφ * (C + D) * (Nat.doubleFactorial (2 * (N + 1) - 1) : ℝ) *
          Real.sqrt (2 * π) / t ^ N := by
        have hbridge : t * t ^ (-(((N + 1) : ℕ) : ℝ) - 1 / 2) ≤
            (t ^ N)⁻¹ := by
          have h1 : t * t ^ (-(((N + 1) : ℕ) : ℝ) - 1 / 2) =
              t ^ (-((N : ℝ)) - 1 / 2) := by
            nth_rewrite 1 [← Real.rpow_one t]
            rw [← Real.rpow_add ht0]
            congr 1
            push_cast
            ring
          have h2 : t ^ (-((N : ℝ)) - 1 / 2) ≤ t ^ (-((N : ℝ))) := by
            apply Real.rpow_le_rpow_of_exponent_le ht
            linarith
          have h3 : t ^ (-((N : ℝ))) = (t ^ N)⁻¹ := by
            rw [Real.rpow_neg ht0.le, Real.rpow_natCast]
          rw [h1, ← h3]
          exact h2
        have hK0 : (0 : ℝ) ≤ Mφ * (C + D) * (Nat.doubleFactorial (2 * (N + 1) - 1) : ℝ) *
            Real.sqrt (2 * π) := by positivity
        calc Mφ * (C + D) * t * ((Nat.doubleFactorial (2 * (N + 1) - 1) : ℝ) *
              Real.sqrt (2 * π) * t ^ (-(((N + 1) : ℕ) : ℝ) - 1 / 2))
            = (Mφ * (C + D) * (Nat.doubleFactorial (2 * (N + 1) - 1) : ℝ) *
                Real.sqrt (2 * π)) *
              (t * t ^ (-(((N + 1) : ℕ) : ℝ) - 1 / 2)) := by ring
          _ ≤ (Mφ * (C + D) * (Nat.doubleFactorial (2 * (N + 1) - 1) : ℝ) *
                Real.sqrt (2 * π)) * (t ^ N)⁻¹ := by
              apply mul_le_mul_of_nonneg_left hbridge hK0
          _ = Mφ * (C + D) * (Nat.doubleFactorial (2 * (N + 1) - 1) : ℝ) *
                Real.sqrt (2 * π) / t ^ N := by
              rw [div_eq_mul_inv]

/-- The flat-perturbation difference decays superpolynomially, in the
`IsLittleO` vocabulary of `Laplace.Decay`: the exact hypothesis shape
that `lower_bound_not_superpolynomial` refutes for analytic pencil
differences is here *satisfied* by a flat perturbation. -/
theorem flat_perturbation_superpolynomial
    {f φ : ℝ → ℝ} {M : ℝ} (hf_c : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hf_bdd : ∀ x, f x ≤ M)
    (hflat : ∀ n : ℕ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ x : ℝ, |x| ≤ δ → f x ≤ C * x ^ (2 * n))
    (hφ_c : Continuous φ) (hφ_s : HasCompactSupport φ) :
    ∀ N : ℕ,
      (fun t : ℝ ↦ (∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2)))) -
        ∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2 + f x)))) =o[Filter.atTop]
      fun t : ℝ ↦ t ^ (-(N : ℝ)) := by
  intro N
  obtain ⟨K, T, hK, hT, hbound⟩ :=
    flat_perturbation_invisible hf_c hf0 hf_bdd hflat hφ_c hφ_s (N + 1)
  have h1 : (fun t : ℝ ↦ (∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2)))) -
      ∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2 + f x)))) =O[Filter.atTop]
      fun t : ℝ ↦ t ^ (-((N : ℝ) + 1)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨K, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop T,
      Filter.eventually_ge_atTop (1 : ℝ)] with t htT ht1
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have hrw : K / t ^ (N + 1) = K * ‖t ^ (-((N : ℝ) + 1))‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _),
        Real.rpow_neg ht0.le,
        show ((N : ℝ) + 1) = (((N + 1 : ℕ) : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, div_eq_mul_inv]
    calc ‖(∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2)))) -
          ∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2 + f x)))‖
        ≤ K / t ^ (N + 1) := hbound t htT
      _ = K * ‖t ^ (-((N : ℝ) + 1))‖ := hrw
  have h2 : (fun t : ℝ ↦ t ^ (-((N : ℝ) + 1))) =o[Filter.atTop]
      fun t : ℝ ↦ t ^ (-(N : ℝ)) := by
    refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht h0
      exact absurd h0 (Real.rpow_pos_of_pos ht _).ne'
    · have hratio : ∀ᶠ t : ℝ in Filter.atTop,
          t ^ (-((N : ℝ) + 1)) / t ^ (-(N : ℝ)) = t⁻¹ := by
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
        rw [← Real.rpow_sub ht, show -((N : ℝ) + 1) - -(N : ℝ) = -1 by ring,
          Real.rpow_neg_one]
      rw [Filter.tendsto_congr' hratio]
      exact tendsto_inv_atTop_zero
  exact h1.trans_isLittleO h2

end Laplace.OneD
