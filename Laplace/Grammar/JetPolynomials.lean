/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LeadingCoeffNonzero

/-!
# Jet polynomials of the exponential factor (grammar §4.2, all orders in `d = 1`)

For the fluctuation `ξ(u) = ∑_{i<R} xᵢ uⁱ + O(u^R)` write `g = ξ − x₀`. The `u`-jet of `e^{βs g(u)}`
to order `R` has coefficients

  `E_n(s) = ∑_{m<R} (βs)^m/m! · [uⁿ](g_R(u)^m)`,   `g_R(u) = ∑_{1≤i<R} xᵢ uⁱ`

(`expJet`), finite sums of polynomial coefficients. We prove the **exponential jet remainder**

  `|e^{βs g(u)} − ∑_{n<R} E_n(s) uⁿ| ≤ C u^R (1+s)^R e^{β L₁ b s}`   (`0 ≤ u ≤ b`, `s ≥ 0`)

(`exp_jet_remainder`) from the Taylor remainder of `ξ` and the Lipschitz bound `|g(u)| ≤ L₁ u`,
using the exponential tail bound, the identity `aᵐ − bᵐ = (a−b)∑ aⁱb^{m-1-i}` and the truncation
error of a polynomial on `[0, b]` (`poly_trunc_le`). Zero `sorry`/`axiom`.
-/

open Real Finset Polynomial

namespace Laplace.Grammar

/-- The degree-`< R` truncation error of a polynomial on `[0, b]`. -/
theorem poly_trunc_le (P : ℝ[X]) (R : ℕ) (b u : ℝ) (hu : 0 ≤ u) (hub : u ≤ b) :
    |P.eval u - ∑ n ∈ range R, P.coeff n * u ^ n|
      ≤ u ^ R * ∑ n ∈ Ico R (max R (P.natDegree + 1)), |P.coeff n| * b ^ (n - R) := by
  set M := max R (P.natDegree + 1) with hM
  have hRM : R ≤ M := le_max_left _ _
  have hdeg : P.natDegree < M := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  rw [Polynomial.eval_eq_sum_range' hdeg, ← Finset.sum_range_add_sum_Ico _ hRM,
    add_sub_cancel_left, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [Finset.mem_Ico] at hn
  rw [abs_mul, abs_of_nonneg (pow_nonneg hu _)]
  have : u ^ n = u ^ R * u ^ (n - R) := by rw [← pow_add, Nat.add_sub_cancel' hn.1]
  rw [this]
  have h2 : u ^ (n - R) ≤ b ^ (n - R) := pow_le_pow_left₀ hu hub _
  calc |P.coeff n| * (u ^ R * u ^ (n - R)) = u ^ R * (|P.coeff n| * u ^ (n - R)) := by ring
    _ ≤ u ^ R * (|P.coeff n| * b ^ (n - R)) := by gcongr

/-- The truncation constant of a polynomial. -/
noncomputable def truncConst (P : ℝ[X]) (R : ℕ) (b : ℝ) : ℝ :=
  ∑ n ∈ Ico R (max R (P.natDegree + 1)), |P.coeff n| * b ^ (n - R)

/-- The Taylor polynomial `∑_{i<R} xᵢ Xⁱ`. -/
noncomputable def jetPoly (x : ℕ → ℝ) (R : ℕ) : ℝ[X] := ∑ i ∈ range R, C (x i) * X ^ i

theorem eval_jetPoly (x : ℕ → ℝ) (R : ℕ) (u : ℝ) :
    (jetPoly x R).eval u = ∑ i ∈ range R, x i * u ^ i := by
  unfold jetPoly
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem coeff_jetPoly (x : ℕ → ℝ) (R n : ℕ) (hn : n < R) : (jetPoly x R).coeff n = x n := by
  unfold jetPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (range R) n]
  simp [hn]

/-- The shifted sequence `g_i = xᵢ` for `i ≥ 1`, `g₀ = 0`. -/
def shiftSeq (x : ℕ → ℝ) (i : ℕ) : ℝ := if i = 0 then 0 else x i

/-- The Taylor polynomial of `g = ξ − x₀` without constant term. -/
noncomputable def gPoly (x : ℕ → ℝ) (R : ℕ) : ℝ[X] := jetPoly (shiftSeq x) R

theorem eval_gPoly (x : ℕ → ℝ) (R : ℕ) (u : ℝ) :
    (gPoly x R).eval u = ∑ i ∈ range R, shiftSeq x i * u ^ i := eval_jetPoly _ R u

/-- The exponential jet coefficient `E_n(s) = ∑_{m<R} (βs)^m/m! · [uⁿ](g_R^m)`. -/
noncomputable def expJet (β : ℝ) (x : ℕ → ℝ) (R n : ℕ) (s : ℝ) : ℝ :=
  ∑ m ∈ range R, (β * s) ^ m / (m.factorial : ℝ) * ((gPoly x R) ^ m).coeff n

/-- The exponential jet coefficient bound constant. -/
noncomputable def expJetConst (β : ℝ) (x : ℕ → ℝ) (R n : ℕ) : ℝ :=
  ∑ m ∈ range R, β ^ m / (m.factorial : ℝ) * |((gPoly x R) ^ m).coeff n|

theorem expJet_continuous (β : ℝ) (x : ℕ → ℝ) (R n : ℕ) : Continuous (expJet β x R n) := by
  unfold expJet
  exact continuous_finsetSum _ fun m _ =>
    (((continuous_const.mul continuous_id).pow m).div_const _).mul continuous_const

/-- `|E_n(s)| ≤ expJetConst · (1+s)^R` for `s ≥ 0`. -/
theorem expJet_abs_le (β : ℝ) (hβ : 0 < β) (x : ℕ → ℝ) (R n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    |expJet β x R n s| ≤ expJetConst β x R n * (1 + s) ^ R := by
  unfold expJet expJetConst
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [Finset.mem_range] at hm
  rw [abs_mul, abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ β * s),
    abs_of_pos (by positivity : (0 : ℝ) < m.factorial), mul_pow]
  have hsm : s ^ m ≤ (1 + s) ^ R :=
    (pow_le_pow_left₀ hs (by linarith) m).trans (pow_le_pow_right₀ (by linarith) hm.le)
  have hc : 0 ≤ β ^ m / (m.factorial : ℝ) * |((gPoly x R) ^ m).coeff n| := by positivity
  calc β ^ m * s ^ m / (m.factorial : ℝ) * |((gPoly x R) ^ m).coeff n|
      = (β ^ m / (m.factorial : ℝ) * |((gPoly x R) ^ m).coeff n|) * s ^ m := by ring
    _ ≤ (β ^ m / (m.factorial : ℝ) * |((gPoly x R) ^ m).coeff n|) * (1 + s) ^ R :=
        mul_le_mul_of_nonneg_left hsm hc

/-- `|aᵐ − bᵐ| ≤ m |a − b| Mᵐ⁻¹` when `|a|, |b| ≤ M`. -/
theorem abs_pow_sub_pow_le' (a b M : ℝ) (m : ℕ) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |a ^ m - b ^ m| ≤ m * |a - b| * M ^ (m - 1) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans ha
  rcases m with _ | m
  · simp
  · rw [← geom_sum₂_mul, abs_mul, Nat.add_sub_cancel]
    have hsum : |∑ i ∈ range (m + 1), a ^ i * b ^ (m - i)| ≤ ((m + 1 : ℕ) : ℝ) * M ^ m := by
      calc |∑ i ∈ range (m + 1), a ^ i * b ^ (m - i)|
          ≤ ∑ i ∈ range (m + 1), |a ^ i * b ^ (m - i)| :=
            Finset.abs_sum_le_sum_abs (fun i => a ^ i * b ^ (m - i)) (range (m + 1))
        _ ≤ ∑ _i ∈ range (m + 1), (M ^ m : ℝ) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [Finset.mem_range] at hi
            rw [abs_mul, abs_pow, abs_pow]
            calc |a| ^ i * |b| ^ (m - i) ≤ M ^ i * M ^ (m - i) :=
                  mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ha _)
                    (pow_le_pow_left₀ (abs_nonneg _) hb _) (by positivity) (by positivity)
              _ = M ^ m := by rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 hi)]
        _ = ((m + 1 : ℕ) : ℝ) * M ^ m := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc |∑ i ∈ range (m + 1), a ^ i * b ^ (m - i)| * |a - b|
        ≤ ((m + 1 : ℕ) : ℝ) * M ^ m * |a - b| := mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
      _ = _ := by ring

/-- `|g_R(u)| ≤ L₂ u` on `[0, b]` with `L₂ = ∑_{1≤i<R} |xᵢ| b^{i-1}`. -/
theorem eval_gPoly_abs_le (x : ℕ → ℝ) (R : ℕ) (b u : ℝ) (hu : 0 ≤ u) (hub : u ≤ b) :
    |(gPoly x R).eval u| ≤ (∑ i ∈ range R, |shiftSeq x i| * b ^ (i - 1)) * u := by
  rw [eval_gPoly, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg hu]
  rcases i with _ | i
  · simp [shiftSeq]
  · rw [Nat.add_sub_cancel, pow_succ]
    have : u ^ i ≤ b ^ i := pow_le_pow_left₀ hu hub i
    calc |shiftSeq x (i + 1)| * (u ^ i * u) ≤ |shiftSeq x (i + 1)| * (b ^ i * u) := by gcongr
      _ = _ := by ring

/-- **The exponential jet remainder**: with `|g(u) − g_R(u)| ≤ K u^R` and `|g(u)| ≤ L₁ u` on
`[0, b]`, for `s ≥ 0`,
`|e^{βs g(u)} − ∑_{n<R} E_n(s) uⁿ| ≤ C u^R (1+s)^R e^{β L₁ b s}` with an explicit `C`. -/
theorem exp_jet_remainder (β b K L₁ : ℝ) (hβ : 0 < β) (hb : 0 < b) (hK : 0 ≤ K) (hL₁ : 0 ≤ L₁)
    (x : ℕ → ℝ) (R : ℕ) (g : ℝ → ℝ)
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) b, |g u - (gPoly x R).eval u| ≤ K * u ^ R)
    (hgL : ∀ u ∈ Set.Icc (0 : ℝ) b, |g u| ≤ L₁ * u) (u s : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) b)
    (hs : 0 ≤ s) :
    |Real.exp (β * s * g u) - ∑ n ∈ range R, expJet β x R n s * u ^ n|
      ≤ ((β * L₁) ^ R / (R.factorial : ℝ)
          + ∑ m ∈ range R, β ^ m / (m.factorial : ℝ)
            * (K * m * (max L₁ (∑ i ∈ range R, |shiftSeq x i| * b ^ (i - 1)) * b) ^ (m - 1)
              + truncConst ((gPoly x R) ^ m) R b))
        * u ^ R * (1 + s) ^ R * Real.exp (β * L₁ * b * s) := by
  have hu0 : 0 ≤ u := hu.1
  have hub : u ≤ b := hu.2
  set L₂ : ℝ := ∑ i ∈ range R, |shiftSeq x i| * b ^ (i - 1) with hL₂
  have hL₂ : 0 ≤ L₂ := Finset.sum_nonneg fun i _ => by positivity
  set L₃ : ℝ := max L₁ L₂ with hL₃
  have hL₃ : 0 ≤ L₃ := le_trans hL₁ (le_max_left _ _)
  set gP : ℝ := (gPoly x R).eval u with hgP
  have hgu : |g u| ≤ L₁ * u := hgL u hu
  have hgPu : |gP| ≤ L₂ * u := eval_gPoly_abs_le x R b u hu0 hub
  have hgub : |g u| ≤ L₃ * b := hgu.trans (mul_le_mul (le_max_left _ _) hub hu0 hL₃)
  have hgPub : |gP| ≤ L₃ * b := hgPu.trans (mul_le_mul (le_max_right _ _) hub hu0 hL₃)
  have hbs : 0 ≤ β * s := by positivity
  -- Step 1: the exponential tail
  have h1 : |Real.exp (β * s * g u) - ∑ m ∈ range R, (β * s * g u) ^ m / m.factorial|
      ≤ (β * L₁) ^ R / (R.factorial : ℝ) * u ^ R * (1 + s) ^ R * Real.exp (β * L₁ * b * s) := by
    have := abs_exp_sub_sum_range_le (β * s * g u) R
    refine this.trans ?_
    have habs : |β * s * g u| ≤ β * s * (L₁ * u) := by
      rw [abs_mul, abs_of_nonneg hbs]; exact mul_le_mul_of_nonneg_left hgu hbs
    have hexp : Real.exp |β * s * g u| ≤ Real.exp (β * L₁ * b * s) := by
      refine Real.exp_le_exp.2 (habs.trans ?_)
      have : β * s * (L₁ * u) ≤ β * s * (L₁ * b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hub hL₁) hbs
      linarith
    have hpow : |β * s * g u| ^ R ≤ (β * L₁) ^ R * u ^ R * (1 + s) ^ R := by
      calc |β * s * g u| ^ R ≤ (β * s * (L₁ * u)) ^ R := pow_le_pow_left₀ (abs_nonneg _) habs R
        _ = (β * L₁) ^ R * u ^ R * s ^ R := by ring
        _ ≤ (β * L₁) ^ R * u ^ R * (1 + s) ^ R := by
            gcongr; linarith
    calc |β * s * g u| ^ R / (R.factorial : ℝ) * Real.exp |β * s * g u|
        ≤ ((β * L₁) ^ R * u ^ R * (1 + s) ^ R) / (R.factorial : ℝ) * Real.exp (β * L₁ * b * s) := by
          gcongr
      _ = _ := by ring
  -- Step 2: each power `gᵐ` versus the truncated polynomial power
  have h2 : ∀ m ∈ range R, |(g u) ^ m - ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n|
      ≤ (K * m * (L₃ * b) ^ (m - 1) + truncConst ((gPoly x R) ^ m) R b)
        * u ^ R := by
    intro m _
    have ha : |(g u) ^ m - gP ^ m| ≤ m * |g u - gP| * (L₃ * b) ^ (m - 1) :=
      abs_pow_sub_pow_le' (g u) gP (L₃ * b) m hgub hgPub
    have hb' : |gP ^ m - ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n|
        ≤ u ^ R * truncConst ((gPoly x R) ^ m) R b := by
      have := poly_trunc_le ((gPoly x R) ^ m) R b u hu0 hub
      rwa [Polynomial.eval_pow] at this
    have hgg : |g u - gP| ≤ K * u ^ R := hg u hu
    have hLb : 0 ≤ (L₃ * b) ^ (m - 1) := pow_nonneg (by positivity) _
    calc |(g u) ^ m - ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n|
        ≤ |(g u) ^ m - gP ^ m| + |gP ^ m - ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n| :=
          abs_sub_le ((g u) ^ m) (gP ^ m) (∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n)
      _ ≤ m * |g u - gP| * (L₃ * b) ^ (m - 1) + u ^ R * truncConst ((gPoly x R) ^ m) R b :=
          add_le_add ha hb'
      _ ≤ m * (K * u ^ R) * (L₃ * b) ^ (m - 1) + u ^ R * truncConst ((gPoly x R) ^ m) R b := by
          gcongr
      _ = _ := by ring
  -- Step 3: assemble: the jet sum is the truncated exponential polynomial
  have hjet : ∑ n ∈ range R, expJet β x R n s * u ^ n
      = ∑ m ∈ range R, (β * s) ^ m / (m.factorial : ℝ)
          * ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n := by
    unfold expJet
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hsplit : Real.exp (β * s * g u) - ∑ n ∈ range R, expJet β x R n s * u ^ n
      = (Real.exp (β * s * g u) - ∑ m ∈ range R, (β * s * g u) ^ m / m.factorial)
        + ∑ m ∈ range R, (β * s) ^ m / (m.factorial : ℝ)
          * ((g u) ^ m - ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n) := by
    rw [hjet]
    have e : ∀ m ∈ range R, (β * s) ^ m / (m.factorial : ℝ)
        * ((g u) ^ m - ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n)
        = (β * s * g u) ^ m / m.factorial
          - (β * s) ^ m / (m.factorial : ℝ) * ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n := by
      intro m _; rw [mul_pow]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib]
    ring
  have hE1 : 1 ≤ Real.exp (β * L₁ * b * s) := Real.one_le_exp (by positivity)
  have hE0 : 0 ≤ Real.exp (β * L₁ * b * s) := (Real.exp_pos _).le
  have h3 : |∑ m ∈ range R, (β * s) ^ m / (m.factorial : ℝ)
      * ((g u) ^ m - ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n)|
      ≤ (∑ m ∈ range R, β ^ m / (m.factorial : ℝ)
          * (K * m * (L₃ * b) ^ (m - 1) + truncConst ((gPoly x R) ^ m) R b))
        * u ^ R * (1 + s) ^ R * Real.exp (β * L₁ * b * s) := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    rw [Finset.mem_range] at hm
    have hsm : s ^ m ≤ (1 + s) ^ R :=
      (pow_le_pow_left₀ hs (by linarith) m).trans (pow_le_pow_right₀ (by linarith) hm.le)
    rw [abs_mul, abs_div, abs_pow, abs_of_nonneg hbs,
      abs_of_pos (by positivity : (0:ℝ) < m.factorial), mul_pow]
    have hT := h2 m (Finset.mem_range.2 hm)
    have hT0 : 0 ≤ K * m * (L₃ * b) ^ (m - 1) + truncConst ((gPoly x R) ^ m) R b := by
      have : 0 ≤ truncConst ((gPoly x R) ^ m) R b :=
        Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hb.le _)
      positivity
    calc β ^ m * s ^ m / (m.factorial : ℝ)
          * |(g u) ^ m - ∑ n ∈ range R, ((gPoly x R) ^ m).coeff n * u ^ n|
        ≤ β ^ m * s ^ m / (m.factorial : ℝ)
          * ((K * m * (L₃ * b) ^ (m - 1) + truncConst ((gPoly x R) ^ m) R b) * u ^ R) := by
          gcongr
      _ = (β ^ m / (m.factorial : ℝ)
            * (K * m * (L₃ * b) ^ (m - 1) + truncConst ((gPoly x R) ^ m) R b))
          * u ^ R * s ^ m * 1 := by ring
      _ ≤ (β ^ m / (m.factorial : ℝ)
            * (K * m * (L₃ * b) ^ (m - 1) + truncConst ((gPoly x R) ^ m) R b))
          * u ^ R * (1 + s) ^ R * Real.exp (β * L₁ * b * s) := by
          gcongr
  rw [hsplit]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h3
    _ = _ := by ring

end Laplace.Grammar
