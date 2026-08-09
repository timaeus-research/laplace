/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.StableRecovery

/-!
# The stabilizer envelope

Stage C2 of the smooth-germ programme, first installment. The
degree-`D` Taylor polynomial of a smooth loss need not be confining
(its top coefficient can be negative), so the comparison argument
stabilizes it with an even monomial `d·x^M`, `M > D`: in scaled
coordinates the stabilizer first appears at rung `M - 2 > R`, so it
is invisible to every recovered coefficient. The consult's
coefficient-wise construction (`exists_stabilizer_envelope`) produces
`d` by an elementary case split at `|x| = ρ`,
`ρ = min(1, a/(2(B+1)))`, `B = ∑|c_i|`, yielding the global envelope
`(a/2)·x² ≤ a·x² + ∑ c_i·x^(3+i) + d·x^M` with no suprema or
compactness arguments.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- **The stabilizer envelope** (stage C2.2 core). For `a > 0`,
higher coefficients `c` at degrees `3, …, R'+2`, and an even `M`
above every degree present, there is `d ≥ 0` such that the stabilized
polynomial dominates `(a/2)·x²` globally. -/
theorem exists_stabilizer_envelope
    {R' : ℕ} {a : ℝ} (ha : 0 < a) (c : Fin R' → ℝ) {M : ℕ}
    (hM_even : Even M) (hM : R' + 2 < M) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ x : ℝ,
      a / 2 * x ^ 2 ≤
        a * x ^ 2 + (∑ i : Fin R', c i * x ^ (2 + (i.1 + 1))) +
          d * x ^ M := by
  set B : ℝ := ∑ i : Fin R', |c i| with hB_def
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  set ρ : ℝ := min 1 (a / (2 * (B + 1))) with hρ_def
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hBρ : B * ρ ≤ a / 2 := by
    have h1 : ρ ≤ a / (2 * (B + 1)) := min_le_right _ _
    have h2 : B * ρ ≤ B * (a / (2 * (B + 1))) :=
      mul_le_mul_of_nonneg_left h1 hB0
    have h3 : B * (a / (2 * (B + 1))) ≤ a / 2 := by
      rw [← mul_div_assoc,
        div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  refine ⟨(∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1))) / ρ ^ M,
    by positivity, fun x ↦ ?_⟩
  have hxM : (0 : ℝ) ≤ x ^ M := hM_even.pow_nonneg x
  have habsM : |x| ^ M = x ^ M := hM_even.pow_abs x
  -- The sum is bounded below by minus its absolute row.
  have hsum_lb : -(∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1))) ≤
      ∑ i : Fin R', c i * x ^ (2 + (i.1 + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have h1 : |c i * x ^ (2 + (i.1 + 1))| =
        |c i| * |x| ^ (2 + (i.1 + 1)) := by
      rw [abs_mul, abs_pow]
    calc -(|c i| * |x| ^ (2 + (i.1 + 1))) = -|c i * x ^ (2 + (i.1 + 1))| := by
          rw [h1]
      _ ≤ c i * x ^ (2 + (i.1 + 1)) := neg_abs_le _
  rcases le_total |x| ρ with hx | hx
  · -- Inner region: each degree ≥ 3 term is ≤ B·ρ·x² ≤ (a/2)·x².
    have hx1 : |x| ≤ 1 := le_trans hx hρ1
    have hterm : ∀ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1)) ≤
        |c i| * (|x| * x ^ 2) := by
      intro i
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h3 : |x| ^ (2 + (i.1 + 1)) ≤ |x| ^ 3 :=
        pow_le_pow_of_le_one (abs_nonneg _) hx1 (by omega)
      calc |x| ^ (2 + (i.1 + 1)) ≤ |x| ^ 3 := h3
        _ = |x| * x ^ 2 := by
            rw [pow_succ, sq_abs]
            ring
    have hsum_ub : (∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1))) ≤
        B * ρ * x ^ 2 := by
      calc (∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1)))
          ≤ ∑ i : Fin R', |c i| * (|x| * x ^ 2) :=
            Finset.sum_le_sum fun i _ ↦ hterm i
        _ = B * (|x| * x ^ 2) := by
            rw [hB_def, Finset.sum_mul]
        _ ≤ B * (ρ * x ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hB0
            apply mul_le_mul_of_nonneg_right hx (sq_nonneg x)
        _ = B * ρ * x ^ 2 := by ring
    have hd : (0 : ℝ) ≤ (∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1))) /
        ρ ^ M * x ^ M := by
      apply mul_nonneg _ hxM
      positivity
    have hBρx : B * ρ * x ^ 2 ≤ a / 2 * x ^ 2 :=
      mul_le_mul_of_nonneg_right hBρ (sq_nonneg x)
    nlinarith [hsum_lb, hsum_ub]
  · -- Outer region: each term is absorbed by the stabilizer.
    have hterm : ∀ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1)) ≤
        |c i| * ρ ^ (2 + (i.1 + 1)) / ρ ^ M * x ^ M := by
      intro i
      have hj : 2 + (i.1 + 1) ≤ M := by omega
      have hkey : |x| ^ (2 + (i.1 + 1)) * ρ ^ M ≤
          ρ ^ (2 + (i.1 + 1)) * |x| ^ M := by
        have h1 : ρ ^ M = ρ ^ (2 + (i.1 + 1)) *
            ρ ^ (M - (2 + (i.1 + 1))) := by
          rw [← pow_add]
          congr 1
          omega
        have h2 : |x| ^ M = |x| ^ (2 + (i.1 + 1)) *
            |x| ^ (M - (2 + (i.1 + 1))) := by
          rw [← pow_add]
          congr 1
          omega
        rw [h1, h2]
        have h3 : ρ ^ (M - (2 + (i.1 + 1))) ≤
            |x| ^ (M - (2 + (i.1 + 1))) :=
          pow_le_pow_left₀ hρ0.le hx _
        calc |x| ^ (2 + (i.1 + 1)) *
              (ρ ^ (2 + (i.1 + 1)) * ρ ^ (M - (2 + (i.1 + 1))))
            ≤ |x| ^ (2 + (i.1 + 1)) *
              (ρ ^ (2 + (i.1 + 1)) * |x| ^ (M - (2 + (i.1 + 1)))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = ρ ^ (2 + (i.1 + 1)) *
              (|x| ^ (2 + (i.1 + 1)) * |x| ^ (M - (2 + (i.1 + 1)))) := by
              ring
      have hρM : (0 : ℝ) < ρ ^ M := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hρM]
      calc |c i| * |x| ^ (2 + (i.1 + 1)) * ρ ^ M
          = |c i| * (|x| ^ (2 + (i.1 + 1)) * ρ ^ M) := by ring
        _ ≤ |c i| * (ρ ^ (2 + (i.1 + 1)) * |x| ^ M) :=
            mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
        _ = |c i| * ρ ^ (2 + (i.1 + 1)) * |x| ^ M := by ring
        _ = |c i| * ρ ^ (2 + (i.1 + 1)) * x ^ M := by
            rw [habsM]
    have habsorb : (∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1))) ≤
        (∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1))) / ρ ^ M * x ^ M := by
      calc (∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1)))
          ≤ ∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1)) / ρ ^ M * x ^ M :=
            Finset.sum_le_sum fun i _ ↦ hterm i
        _ = (∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1))) / ρ ^ M *
            x ^ M := by
            rw [← Finset.sum_mul, ← Finset.sum_div]
    nlinarith [hsum_lb, habsorb, sq_nonneg x, ha]

/-- **Exact Gaussian scaling in `q`-space** (stage C2.3): with
`t·q² = 1`, the absolute moment against `e^(-t·a·x²)` is exactly
`q^(k+1)` times the reference moment. -/
theorem abs_moment_scaling
    {a t q : ℝ} (k : ℕ) (hq : 0 < q) (hqt : t * q ^ 2 = 1) :
    (∫ x : ℝ, |x| ^ k * Real.exp (-(t * (a * x ^ 2)))) =
      q ^ (k + 1) * ∫ y : ℝ, |y| ^ k * Real.exp (-(a * y ^ 2)) := by
  have hsub := MeasureTheory.Measure.integral_comp_mul_right
    (g := fun x : ℝ ↦ |x| ^ k * Real.exp (-(t * (a * x ^ 2)))) (a := q)
  rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hq)] at hsub
  have hpt : ∀ y : ℝ,
      |y * q| ^ k * Real.exp (-(t * (a * (y * q) ^ 2))) =
      q ^ k * (|y| ^ k * Real.exp (-(a * y ^ 2))) := by
    intro y
    rw [abs_mul, abs_of_pos hq, mul_pow]
    have harg : t * (a * (y * q) ^ 2) = a * y ^ 2 := by
      have : t * (a * (y * q) ^ 2) = a * y ^ 2 * (t * q ^ 2) := by
        ring
      rw [this, hqt, mul_one]
    rw [harg]
    ring
  calc (∫ x : ℝ, |x| ^ k * Real.exp (-(t * (a * x ^ 2))))
      = q * ∫ y : ℝ, |y * q| ^ k *
          Real.exp (-(t * (a * (y * q) ^ 2))) := by
        rw [hsub]
        field_simp
    _ = q * ∫ y : ℝ, q ^ k * (|y| ^ k * Real.exp (-(a * y ^ 2))) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = q ^ (k + 1) * ∫ y : ℝ, |y| ^ k * Real.exp (-(a * y ^ 2)) := by
        rw [integral_const_mul, pow_succ]
        ring

/-- **The envelope tail bound** (stage C2.5): outside radius `r`, the
tail of any envelope-dominated Gibbs integral is controlled by the
superpolynomial prefactor `e^(-(t/2)·ρ·r²)` times a full Gaussian
moment at half scale. -/
theorem tail_integral_le
    {K : ℝ → ℝ} {ρK t r : ℝ} (hρ : 0 < ρK) (ht : 0 < t) (hr : 0 ≤ r)
    (henv : ∀ x, ρK * x ^ 2 ≤ K x) (hK_cont : Continuous K) (s : ℕ) :
    ∫ x in {x : ℝ | r ≤ |x|}, |x| ^ s * Real.exp (-(t * K x)) ≤
      Real.exp (-(t / 2 * (ρK * r ^ 2))) *
        ∫ x : ℝ, |x| ^ s * Real.exp (-(t / 2 * (ρK * x ^ 2))) := by
  have hset : MeasurableSet {x : ℝ | r ≤ |x|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hmajor : Integrable (fun x : ℝ ↦
      Real.exp (-(t / 2 * (ρK * r ^ 2))) *
        (|x| ^ s * Real.exp (-(t / 2 * (ρK * x ^ 2))))) := by
    have h := integrable_abs_pow_mul_exp_neg_kth (k := 1)
      le_rfl s (ρ := t / 2 * ρK) (by positivity)
    refine (h.congr (Filter.Eventually.of_forall fun x ↦ ?_)).const_mul _
    simp only [mul_assoc]
  have hpt : ∀ x ∈ {x : ℝ | r ≤ |x|},
      |x| ^ s * Real.exp (-(t * K x)) ≤
      Real.exp (-(t / 2 * (ρK * r ^ 2))) *
        (|x| ^ s * Real.exp (-(t / 2 * (ρK * x ^ 2)))) := by
    intro x hx
    have habs : r ≤ |x| := hx
    have hx2 : r ^ 2 ≤ x ^ 2 := by
      have h1 : r ^ 2 ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
      rw [← sq_abs x]
      exact h1
    have hsplit : Real.exp (-(t * (ρK * x ^ 2))) =
        Real.exp (-(t / 2 * (ρK * x ^ 2))) *
          Real.exp (-(t / 2 * (ρK * x ^ 2))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc |x| ^ s * Real.exp (-(t * K x))
        ≤ |x| ^ s * Real.exp (-(t * (ρK * x ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          have h := mul_le_mul_of_nonneg_left (henv x) ht.le
          linarith
      _ = Real.exp (-(t / 2 * (ρK * x ^ 2))) *
          (|x| ^ s * Real.exp (-(t / 2 * (ρK * x ^ 2)))) := by
          rw [hsplit]
          ring
      _ ≤ Real.exp (-(t / 2 * (ρK * r ^ 2))) *
          (|x| ^ s * Real.exp (-(t / 2 * (ρK * x ^ 2)))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply Real.exp_le_exp.mpr
          have h : t / 2 * (ρK * r ^ 2) ≤ t / 2 * (ρK * x ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hx2 hρ.le
          linarith
  have hint_f : IntegrableOn (fun x : ℝ ↦
      |x| ^ s * Real.exp (-(t * K x))) {x : ℝ | r ≤ |x|} := by
    apply Integrable.integrableOn
    have hdom := integrable_abs_pow_mul_exp_neg_kth (k := 1)
      le_rfl s (ρ := t * ρK) (by positivity)
    have hdom' : Integrable (fun x : ℝ ↦
        |x| ^ s * Real.exp (-(t * ρK * x ^ 2))) := by
      refine hdom.congr (Filter.Eventually.of_forall fun x ↦ ?_)
      norm_num
    refine hdom'.mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
    · exact ((continuous_abs.pow s).mul (Real.continuous_exp.comp
        (hK_cont.const_smul t).neg)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs,
        abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (henv x) ht.le
      linarith
  calc ∫ x in {x : ℝ | r ≤ |x|}, |x| ^ s * Real.exp (-(t * K x))
      ≤ ∫ x in {x : ℝ | r ≤ |x|},
          Real.exp (-(t / 2 * (ρK * r ^ 2))) *
            (|x| ^ s * Real.exp (-(t / 2 * (ρK * x ^ 2)))) :=
        setIntegral_mono_on hint_f hmajor.integrableOn hset hpt
    _ ≤ ∫ x : ℝ, Real.exp (-(t / 2 * (ρK * r ^ 2))) *
          (|x| ^ s * Real.exp (-(t / 2 * (ρK * x ^ 2)))) :=
        setIntegral_le_integral hmajor
          (Filter.Eventually.of_forall fun x ↦ by positivity)
    _ = Real.exp (-(t / 2 * (ρK * r ^ 2))) *
          ∫ x : ℝ, |x| ^ s * Real.exp (-(t / 2 * (ρK * x ^ 2))) :=
        integral_const_mul _ _

end Laplace.OneD
