/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.ExpGraded
import Laplace.Multi.DegreeRecovery

/-!
# The correction coefficient functions

Stage 5a of the forward-expansion programme. The integrated numerator
expansion's coefficients are `a_j = ∫ z^α e^{-T₂(z)} P_j(z) dz`, where
`P_j(z)` is the order-`j` graded correction coefficient of stage 4
instantiated at the exponent data `a_s = V_s(z)` of stage 3. For those
integrals to exist and for the dominated-convergence step, the
coefficient functions `z ↦ P_j(z)` need continuity and polynomial
growth. Both are inductions on the power through
`Polynomial.coeff_mul`, seeded by the if-then-else description of the
exponent polynomial's coefficients and the operator-norm bound on
diagonal Taylor terms.
-/

open Real Filter Topology Asymptotics Polynomial

namespace Laplace.Multi

variable {d : ℕ}

/-- The exponent polynomial's coefficients, explicitly. -/
theorem exponentPoly_coeff (a : ℕ → ℝ) (N u : ℕ) :
    (exponentPoly a N).coeff u =
      if u ∈ Finset.Icc 1 N then a u else 0 := by
  unfold exponentPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite,
    mul_one, mul_zero]
  exact Finset.sum_ite_eq _ u a

/-- The graded exp polynomial's coefficients, as a finite sum over
coefficients of powers. -/
theorem gradedExpPoly_coeff (a : ℕ → ℝ) (N j : ℕ) :
    (gradedExpPoly a N).coeff j =
      ∑ i ∈ Finset.range (N + 1),
        (-1 : ℝ) ^ i / (i.factorial : ℝ) *
          (exponentPoly a N ^ i).coeff j := by
  unfold gradedExpPoly
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.coeff_C_mul]

/-- **The correction coefficient functions**: the graded correction
coefficients of stage 4, instantiated at the exponent data of the
exponent split. -/
noncomputable def correctionCoeffFn (L : EuclidD d → ℝ) (N j : ℕ)
    (z : EuclidD d) : ℝ :=
  expCorrectionCoeff (fun s ↦ exponentTerm s L z) N j

/-- The zeroth coefficient function is constantly one. -/
theorem correctionCoeffFn_zero (L : EuclidD d → ℝ) (N : ℕ)
    (z : EuclidD d) : correctionCoeffFn L N 0 z = 1 :=
  expCorrectionCoeff_zero _ N

/-- Continuity of the exponent polynomial's coefficient functions. -/
theorem continuous_exponentPoly_coeff (L : EuclidD d → ℝ) (N u : ℕ) :
    Continuous fun z : EuclidD d ↦
      (exponentPoly (fun s ↦ exponentTerm s L z) N).coeff u := by
  simp only [exponentPoly_coeff]
  split_ifs with h
  · exact taylorHomogeneousTerm_continuous (u + 2) L
  · exact continuous_const

/-- Continuity of the coefficient functions of powers of the exponent
polynomial: induction through `Polynomial.coeff_mul`. -/
theorem continuous_exponentPoly_pow_coeff (L : EuclidD d → ℝ)
    (N : ℕ) : ∀ i k : ℕ, Continuous fun z : EuclidD d ↦
      (exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff k := by
  intro i
  induction i with
  | zero =>
    intro k
    simp only [pow_zero, Polynomial.coeff_one]
    exact continuous_const
  | succ i ih =>
    intro k
    have hcm : ∀ z : EuclidD d,
        (exponentPoly (fun s ↦ exponentTerm s L z) N ^ (i + 1)).coeff k =
        ∑ x ∈ Finset.antidiagonal k,
          (exponentPoly (fun s ↦ exponentTerm s L z) N).coeff x.1 *
            (exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff x.2 :=
      fun z ↦ by rw [pow_succ', Polynomial.coeff_mul]
    simp only [hcm]
    exact continuous_finset_sum _ fun x _ ↦
      (continuous_exponentPoly_coeff L N x.1).mul (ih x.2)

/-- Continuity of the correction coefficient functions. -/
theorem continuous_correctionCoeffFn (L : EuclidD d → ℝ) (N j : ℕ) :
    Continuous (correctionCoeffFn L N j) := by
  unfold correctionCoeffFn expCorrectionCoeff
  simp only [gradedExpPoly_coeff]
  exact continuous_finset_sum _ fun i _ ↦
    continuous_const.mul (continuous_exponentPoly_pow_coeff L N i j)

/-- Growth bound for the exponent polynomial's coefficient
functions. -/
theorem abs_exponentPoly_coeff_le (L : EuclidD d → ℝ) (N u : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclidD d,
      |(exponentPoly (fun s ↦ exponentTerm s L z) N).coeff u| ≤
        C * (1 + ‖z‖) ^ (u + 2) := by
  refine ⟨((u + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (u + 2) L 0‖,
    by positivity, fun z ↦ ?_⟩
  rw [exponentPoly_coeff]
  split_ifs with h
  · calc |exponentTerm u L z|
        ≤ ((u + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (u + 2) L 0‖ *
          ‖z‖ ^ (u + 2) := abs_taylorHomogeneousTerm_le (u + 2) L z
      _ ≤ ((u + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (u + 2) L 0‖ *
          (1 + ‖z‖) ^ (u + 2) := by
          gcongr
          linarith [norm_nonneg z]
  · rw [abs_zero]
    positivity

/-- Growth bound for the coefficient functions of powers: induction
through `Polynomial.coeff_mul`, with the antidiagonal constraint
matching the exponents. -/
theorem abs_exponentPoly_pow_coeff_le (L : EuclidD d → ℝ) (N : ℕ) :
    ∀ i k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclidD d,
      |(exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff k| ≤
        C * (1 + ‖z‖) ^ (k + 2 * i) := by
  intro i
  induction i with
  | zero =>
    intro k
    refine ⟨1, zero_le_one, fun z ↦ ?_⟩
    simp only [pow_zero, Polynomial.coeff_one]
    have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ (k + 2 * 0) :=
      one_le_pow₀ (by linarith [norm_nonneg z])
    split_ifs with h
    · rw [abs_one, one_mul]
      exact hone
    · rw [abs_zero]
      positivity
  | succ i ih =>
    intro k
    choose C1 hC10 hC1 using abs_exponentPoly_coeff_le L N
    choose C2 hC20 hC2 using ih
    refine ⟨∑ x ∈ Finset.antidiagonal k, C1 x.1 * C2 x.2,
      Finset.sum_nonneg fun x _ ↦ mul_nonneg (hC10 _) (hC20 _),
      fun z ↦ ?_⟩
    have hcm : (exponentPoly (fun s ↦ exponentTerm s L z) N ^ (i + 1)).coeff k =
        ∑ x ∈ Finset.antidiagonal k,
          (exponentPoly (fun s ↦ exponentTerm s L z) N).coeff x.1 *
            (exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff x.2 := by
      rw [pow_succ', Polynomial.coeff_mul]
    rw [hcm]
    calc |∑ x ∈ Finset.antidiagonal k,
          (exponentPoly (fun s ↦ exponentTerm s L z) N).coeff x.1 *
            (exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff x.2|
        ≤ ∑ x ∈ Finset.antidiagonal k,
          |(exponentPoly (fun s ↦ exponentTerm s L z) N).coeff x.1 *
            (exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff x.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ Finset.antidiagonal k,
          C1 x.1 * C2 x.2 * (1 + ‖z‖) ^ (k + 2 * (i + 1)) := by
          refine Finset.sum_le_sum fun x hx ↦ ?_
          have hxk : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
          rw [abs_mul]
          calc |(exponentPoly (fun s ↦ exponentTerm s L z) N).coeff x.1| *
                |(exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff x.2|
              ≤ (C1 x.1 * (1 + ‖z‖) ^ (x.1 + 2)) *
                (C2 x.2 * (1 + ‖z‖) ^ (x.2 + 2 * i)) :=
                mul_le_mul (hC1 x.1 z) (hC2 x.2 z) (abs_nonneg _)
                  (mul_nonneg (hC10 _) (by positivity))
            _ = C1 x.1 * C2 x.2 *
                ((1 + ‖z‖) ^ (x.1 + 2) * (1 + ‖z‖) ^ (x.2 + 2 * i)) :=
                mul_mul_mul_comm _ _ _ _
            _ = C1 x.1 * C2 x.2 * (1 + ‖z‖) ^ (k + 2 * (i + 1)) := by
                rw [← pow_add,
                  show x.1 + 2 + (x.2 + 2 * i) = k + 2 * (i + 1) from by omega]
      _ = (∑ x ∈ Finset.antidiagonal k, C1 x.1 * C2 x.2) *
          (1 + ‖z‖) ^ (k + 2 * (i + 1)) := by
          rw [Finset.sum_mul]
  -- the `omega` above uses `hxk : x.1 + x.2 = k`

/-- **Growth bound for the correction coefficient functions**:
polynomial of degree `j + 2N` in `‖z‖`, so integrable against any
Gaussian. -/
theorem abs_correctionCoeffFn_le (L : EuclidD d → ℝ) (N j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclidD d,
      |correctionCoeffFn L N j z| ≤ C * (1 + ‖z‖) ^ (j + 2 * N) := by
  choose Cp hCp0 hCp using abs_exponentPoly_pow_coeff_le L N
  refine ⟨∑ i ∈ Finset.range (N + 1), (i.factorial : ℝ)⁻¹ * Cp i j,
    Finset.sum_nonneg fun i _ ↦
      mul_nonneg (by positivity) (hCp0 _ _),
    fun z ↦ ?_⟩
  unfold correctionCoeffFn expCorrectionCoeff
  rw [gradedExpPoly_coeff]
  have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  calc |∑ i ∈ Finset.range (N + 1),
        (-1 : ℝ) ^ i / (i.factorial : ℝ) *
          (exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff j|
      ≤ ∑ i ∈ Finset.range (N + 1),
        |(-1 : ℝ) ^ i / (i.factorial : ℝ) *
          (exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (N + 1),
        (i.factorial : ℝ)⁻¹ * Cp i j * (1 + ‖z‖) ^ (j + 2 * N) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi' : i ≤ N := by
          have := Finset.mem_range.mp hi
          omega
        rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
          Nat.abs_cast]
        calc 1 / (i.factorial : ℝ) *
              |(exponentPoly (fun s ↦ exponentTerm s L z) N ^ i).coeff j|
            ≤ 1 / (i.factorial : ℝ) *
              (Cp i j * (1 + ‖z‖) ^ (j + 2 * i)) := by
              gcongr
              exact hCp i j z
          _ ≤ 1 / (i.factorial : ℝ) *
              (Cp i j * (1 + ‖z‖) ^ (j + 2 * N)) := by
              have hpow : (1 + ‖z‖) ^ (j + 2 * i) ≤
                  (1 + ‖z‖) ^ (j + 2 * N) :=
                pow_le_pow_right₀ hbase (by omega)
              have hin := mul_le_mul_of_nonneg_left hpow (hCp0 i j)
              exact mul_le_mul_of_nonneg_left hin (by positivity)
          _ = (i.factorial : ℝ)⁻¹ * Cp i j * (1 + ‖z‖) ^ (j + 2 * N) := by
              rw [one_div]
              ring
    _ = (∑ i ∈ Finset.range (N + 1), (i.factorial : ℝ)⁻¹ * Cp i j) *
        (1 + ‖z‖) ^ (j + 2 * N) := by
        rw [Finset.sum_mul]

end Laplace.Multi
