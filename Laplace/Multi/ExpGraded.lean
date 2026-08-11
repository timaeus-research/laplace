/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.ForwardDomain

/-!
# The graded expansion of the exponential correction factor

Stage 4 of the forward-expansion programme, at scalar level. The
exponent split (stage 3) writes the rescaled exponent as
`T₂(z) + ∑_{s=1}^N q^s V_s(z) + q^N ρ_q(z)`; the numerator stage must
expand `exp(-(∑_s q^s a_s + q^N ρ_q))` to order `N` in `q`. The
collection mechanism here is `gradedExpPoly`: exp's Taylor truncation
composed with the exponent polynomial, whose coefficients
`expCorrectionCoeff` are the expansion coefficients. With that choice
the expansion theorem needs no coefficient identities: strip `ρ` via
the first-order exponential bound, apply exp's Taylor remainder at
`x = -A(q)` where `A(q) = O(q)`, and observe that the polynomial tail
above degree `N` carries `q^(N+1)`. The design consult's recursion
`P_j = -(1/j) ∑ s a_s P_{j-s}` computes the same numbers; it is not
needed as a definition.
-/

open Real Filter Topology Asymptotics Polynomial

namespace Laplace.Multi

/-- The exponent polynomial `∑_{s=1}^N a_s X^s`. -/
noncomputable def exponentPoly (a : ℕ → ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ s ∈ Finset.Icc 1 N, Polynomial.C (a s) * Polynomial.X ^ s

/-- **The graded exp polynomial**: exp's Taylor truncation composed
with the exponent polynomial. Its coefficients are the expansion
coefficients of `exp(-∑_s q^s a_s)`. -/
noncomputable def gradedExpPoly (a : ℕ → ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (N + 1),
    Polynomial.C ((-1 : ℝ) ^ i / (i.factorial : ℝ)) * exponentPoly a N ^ i

/-- The order-`j` correction coefficient. -/
noncomputable def expCorrectionCoeff (a : ℕ → ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  (gradedExpPoly a N).coeff j

theorem exponentPoly_eval (a : ℕ → ℝ) (N : ℕ) (q : ℝ) :
    (exponentPoly a N).eval q = ∑ s ∈ Finset.Icc 1 N, a s * q ^ s := by
  unfold exponentPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]

theorem gradedExpPoly_eval (a : ℕ → ℝ) (N : ℕ) (q : ℝ) :
    (gradedExpPoly a N).eval q =
      ∑ i ∈ Finset.range (N + 1),
        (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)) ^ i / (i.factorial : ℝ) := by
  unfold gradedExpPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    exponentPoly_eval, neg_pow]
  ring

/-- The exponent sum vanishes at `q = 0`. -/
theorem exponent_sum_zero (a : ℕ → ℝ) (N : ℕ) :
    ∑ s ∈ Finset.Icc 1 N, a s * (0 : ℝ) ^ s = 0 := by
  refine Finset.sum_eq_zero fun s hs ↦ ?_
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  rw [zero_pow (by omega), mul_zero]

/-- The zeroth coefficient is `1`: the correction factor tends to
one. -/
theorem expCorrectionCoeff_zero (a : ℕ → ℝ) (N : ℕ) :
    expCorrectionCoeff a N 0 = 1 := by
  unfold expCorrectionCoeff
  rw [Polynomial.coeff_zero_eq_eval_zero, gradedExpPoly_eval,
    exponent_sum_zero, neg_zero]
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro i _ hi
    rw [zero_pow hi, zero_div]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Linear bound on the exponent sum for `q ∈ [0, 1]`. -/
theorem abs_exponent_sum_le (a : ℕ → ℝ) (N : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |∑ s ∈ Finset.Icc 1 N, a s * q ^ s| ≤
      (∑ s ∈ Finset.Icc 1 N, |a s|) * q := by
  calc |∑ s ∈ Finset.Icc 1 N, a s * q ^ s|
      ≤ ∑ s ∈ Finset.Icc 1 N, |a s * q ^ s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Finset.Icc 1 N, |a s| * q := by
        refine Finset.sum_le_sum fun s hs ↦ ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 s)]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc q ^ s ≤ q ^ 1 :=
              pow_le_pow_of_le_one hq0 hq1 (Finset.mem_Icc.mp hs).1
          _ = q := pow_one q
    _ = (∑ s ∈ Finset.Icc 1 N, |a s|) * q := by
        rw [Finset.sum_mul]

/-- The exponent sum vanishes at `0⁺`. -/
theorem tendsto_exponent_sum (a : ℕ → ℝ) (N : ℕ) :
    Tendsto (fun q : ℝ ↦ ∑ s ∈ Finset.Icc 1 N, a s * q ^ s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : Continuous fun q : ℝ ↦ ∑ s ∈ Finset.Icc 1 N, a s * q ^ s :=
    continuous_finset_sum _ fun s _ ↦
      continuous_const.mul (continuous_pow s)
  have := hc.tendsto (0 : ℝ)
  rw [exponent_sum_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `q^(N+1) = o(q^N)` at `0⁺`. -/
theorem isLittleO_pow_succ_nhdsGT (N : ℕ) :
    (fun q : ℝ ↦ q ^ (N + 1)) =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N :=
  (Asymptotics.isLittleO_pow_pow (by omega : N < N + 1)).mono
    nhdsWithin_le_nhds

/-- **The graded expansion of the exponential correction factor**:
for any perturbation `ρ` vanishing at `0⁺`,
`exp(-(∑_{s=1}^N q^s a_s + q^N ρ_q))` agrees with the polynomial
`∑_{j=0}^N q^j c_j` to order `o(q^N)`, where `c_j` are the graded
correction coefficients. -/
theorem exp_graded_expansion (a : ℕ → ℝ) (N : ℕ) {ρ : ℝ → ℝ}
    (hρ : Tendsto ρ (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (fun q : ℝ ↦
      Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s + q ^ N * ρ q)) -
        ∑ j ∈ Finset.range (N + 1), expCorrectionCoeff a N j * q ^ j)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N := by
  have hA := tendsto_exponent_sum a N
  have hpert : Tendsto (fun q : ℝ ↦ q ^ N * ρ q) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hqN : Tendsto (fun q : ℝ ↦ q ^ N) (𝓝[>] (0 : ℝ))
        (𝓝 ((0 : ℝ) ^ N)) :=
      ((continuous_pow N).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have := hqN.mul hρ
    rwa [mul_zero] at this
  -- Step I: stripping the perturbation is o(q^N)
  have hT1 : (fun q : ℝ ↦
      Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s + q ^ N * ρ q)) -
        Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)))
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N := by
    have hbig : (fun q : ℝ ↦
        Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s + q ^ N * ρ q)) -
          Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)))
        =O[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N * ρ q := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨4, ?_⟩
      have hexp2 : ∀ᶠ q in 𝓝[>] (0 : ℝ),
          Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)) ≤ 2 := by
        have hAneg : Tendsto
            (fun q : ℝ ↦ -(∑ s ∈ Finset.Icc 1 N, a s * q ^ s))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have := hA.neg
          rwa [neg_zero] at this
        have hcomp : Tendsto
            (fun q : ℝ ↦ Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)))
            (𝓝[>] (0 : ℝ)) (𝓝 1) := by
          have := (Real.continuous_exp.tendsto (0 : ℝ)).comp hAneg
          simpa using this
        exact hcomp.eventually_le_const one_lt_two
      have hsmall : ∀ᶠ q in 𝓝[>] (0 : ℝ), |q ^ N * ρ q| ≤ 1 := by
        have := hpert.abs
        rw [abs_zero] at this
        exact this.eventually_le_const one_pos
      filter_upwards [hexp2, hsmall] with q h2 h1
      have hsplit : Real.exp
            (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s + q ^ N * ρ q)) -
            Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)) =
          Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)) *
            (Real.exp (-(q ^ N * ρ q)) - 1) := by
        rw [neg_add, Real.exp_add]
        ring
      rw [Real.norm_eq_abs, Real.norm_eq_abs, hsplit, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have hone : |Real.exp (-(q ^ N * ρ q)) - 1| ≤ 2 * |q ^ N * ρ q| := by
        have := Real.abs_exp_sub_one_le (x := -(q ^ N * ρ q))
          (by rwa [abs_neg])
        rwa [abs_neg] at this
      calc Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)) *
            |Real.exp (-(q ^ N * ρ q)) - 1|
          ≤ 2 * (2 * |q ^ N * ρ q|) :=
            mul_le_mul h2 hone (abs_nonneg _) (by norm_num)
        _ = 4 * |q ^ N * ρ q| := by ring
    refine hbig.trans_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hρε : ∀ᶠ q in 𝓝[>] (0 : ℝ), |ρ q| ≤ ε := by
      have := hρ.abs
      rw [abs_zero] at this
      exact this.eventually_le_const hε
    filter_upwards [hρε, self_mem_nhdsWithin] with q hq hq0
    have hq0' : (0 : ℝ) < q := Set.mem_Ioi.mp hq0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (pow_pos hq0' N)]
    calc q ^ N * |ρ q| ≤ q ^ N * ε :=
          mul_le_mul_of_nonneg_left hq (pow_pos hq0' N).le
      _ = ε * q ^ N := by ring
  -- Step II: exp's Taylor remainder at x = -A(q) is o(q^N)
  have hT2 : (fun q : ℝ ↦
      Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)) -
        (gradedExpPoly a N).eval q)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N := by
    have hexp0 : ∀ x : ℝ, |x| ≤ 1 →
        |Real.exp x - ∑ m ∈ Finset.range (N + 1),
          x ^ m / (m.factorial : ℝ)| ≤
        |x| ^ (N + 1) * (((N + 1).succ : ℝ) /
          (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ))) :=
      fun x hx ↦ Real.exp_bound hx (Nat.succ_pos N)
    have hc0 : (0 : ℝ) ≤ ((N + 1).succ : ℝ) /
        (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ)) := by positivity
    have hbig : (fun q : ℝ ↦
        Real.exp (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s)) -
          (gradedExpPoly a N).eval q)
        =O[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (N + 1) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨(∑ s ∈ Finset.Icc 1 N, |a s|) ^ (N + 1) *
        (((N + 1).succ : ℝ) /
          (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ))), ?_⟩
      have hA1 : ∀ᶠ q in 𝓝[>] (0 : ℝ),
          |∑ s ∈ Finset.Icc 1 N, a s * q ^ s| ≤ 1 := by
        have := hA.abs
        rw [abs_zero] at this
        exact this.eventually_le_const one_pos
      have hq01 : ∀ᶠ q in 𝓝[>] (0 : ℝ), q ∈ Set.Ioo (0 : ℝ) 1 :=
        Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [hA1, hq01] with q hAq hq
      obtain ⟨hq0, hq1⟩ := hq
      rw [gradedExpPoly_eval, Real.norm_eq_abs, Real.norm_eq_abs]
      refine le_trans (hexp0 (-(∑ s ∈ Finset.Icc 1 N, a s * q ^ s))
        (by rwa [abs_neg])) ?_
      rw [abs_neg]
      have habs : |∑ s ∈ Finset.Icc 1 N, a s * q ^ s| ≤
          (∑ s ∈ Finset.Icc 1 N, |a s|) * q :=
        abs_exponent_sum_le a N hq0.le hq1.le
      have hpow : |∑ s ∈ Finset.Icc 1 N, a s * q ^ s| ^ (N + 1) ≤
          ((∑ s ∈ Finset.Icc 1 N, |a s|) * q) ^ (N + 1) := by
        gcongr
      calc |∑ s ∈ Finset.Icc 1 N, a s * q ^ s| ^ (N + 1) *
            (((N + 1).succ : ℝ) /
              (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ)))
          ≤ ((∑ s ∈ Finset.Icc 1 N, |a s|) * q) ^ (N + 1) *
            (((N + 1).succ : ℝ) /
              (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_right hpow hc0
        _ = (∑ s ∈ Finset.Icc 1 N, |a s|) ^ (N + 1) *
            (((N + 1).succ : ℝ) /
              (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ))) *
            |q ^ (N + 1)| := by
            rw [mul_pow, abs_of_pos (pow_pos hq0 (N + 1))]
            ring
    exact hbig.trans_isLittleO (isLittleO_pow_succ_nhdsGT N)
  -- Step III: the polynomial tail above degree N is o(q^N)
  have hT3 : (fun q : ℝ ↦
      (gradedExpPoly a N).eval q -
        ∑ j ∈ Finset.range (N + 1), expCorrectionCoeff a N j * q ^ j)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N := by
    have hdeg : (gradedExpPoly a N).natDegree <
        max ((gradedExpPoly a N).natDegree + 1) (N + 1) :=
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    have hNn : N + 1 ≤ max ((gradedExpPoly a N).natDegree + 1) (N + 1) :=
      le_max_right _ _
    have hbig : (fun q : ℝ ↦
        (gradedExpPoly a N).eval q -
          ∑ j ∈ Finset.range (N + 1), expCorrectionCoeff a N j * q ^ j)
        =O[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (N + 1) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨∑ j ∈ Finset.Ico (N + 1)
        (max ((gradedExpPoly a N).natDegree + 1) (N + 1)),
        |(gradedExpPoly a N).coeff j|, ?_⟩
      have hq01 : ∀ᶠ q in 𝓝[>] (0 : ℝ), q ∈ Set.Ioo (0 : ℝ) 1 :=
        Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [hq01] with q hq
      obtain ⟨hq0, hq1⟩ := hq
      have heval : (gradedExpPoly a N).eval q =
          ∑ j ∈ Finset.range
            (max ((gradedExpPoly a N).natDegree + 1) (N + 1)),
            (gradedExpPoly a N).coeff j * q ^ j :=
        Polynomial.eval_eq_sum_range' hdeg q
      have hsplit : ∑ j ∈ Finset.range
            (max ((gradedExpPoly a N).natDegree + 1) (N + 1)),
            (gradedExpPoly a N).coeff j * q ^ j =
          (∑ j ∈ Finset.range (N + 1),
            (gradedExpPoly a N).coeff j * q ^ j) +
            ∑ j ∈ Finset.Ico (N + 1)
              (max ((gradedExpPoly a N).natDegree + 1) (N + 1)),
              (gradedExpPoly a N).coeff j * q ^ j := by
        simp only [Finset.range_eq_Ico]
        rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) hNn]
      have hcsum : ∑ j ∈ Finset.range (N + 1),
          expCorrectionCoeff a N j * q ^ j =
          ∑ j ∈ Finset.range (N + 1),
            (gradedExpPoly a N).coeff j * q ^ j := rfl
      rw [heval, hsplit, hcsum, add_sub_cancel_left,
        Real.norm_eq_abs, Real.norm_eq_abs]
      calc |∑ j ∈ Finset.Ico (N + 1)
            (max ((gradedExpPoly a N).natDegree + 1) (N + 1)),
            (gradedExpPoly a N).coeff j * q ^ j|
          ≤ ∑ j ∈ Finset.Ico (N + 1)
              (max ((gradedExpPoly a N).natDegree + 1) (N + 1)),
              |(gradedExpPoly a N).coeff j * q ^ j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.Ico (N + 1)
              (max ((gradedExpPoly a N).natDegree + 1) (N + 1)),
              |(gradedExpPoly a N).coeff j| * q ^ (N + 1) := by
            refine Finset.sum_le_sum fun j hj ↦ ?_
            rw [abs_mul, abs_of_pos (pow_pos hq0 j)]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact pow_le_pow_of_le_one hq0.le hq1.le
              (Finset.mem_Ico.mp hj).1
        _ = (∑ j ∈ Finset.Ico (N + 1)
              (max ((gradedExpPoly a N).natDegree + 1) (N + 1)),
              |(gradedExpPoly a N).coeff j|) * |q ^ (N + 1)| := by
            rw [Finset.sum_mul, abs_of_pos (pow_pos hq0 (N + 1))]
    exact hbig.trans_isLittleO (isLittleO_pow_succ_nhdsGT N)
  -- assemble the telescope
  have hsum := (hT1.add hT2).add hT3
  refine hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with q
  ring

end Laplace.Multi
