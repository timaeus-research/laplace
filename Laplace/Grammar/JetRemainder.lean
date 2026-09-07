/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.JetPolynomials

/-!
# The amplitude jet remainder (grammar §4.2, all orders in `d = 1`)

For `ξ(u) = ∑_{i<R} xᵢ uⁱ + O(u^R)`, `η(u) = ∑_{i<R} yᵢ uⁱ + O(u^R)` on `[0, b]`, the `u`-jet of the
amplitude `η(u) e^{βsξ(u)}` to order `R` has coefficients `F_j(s) = e^{βsa} P_j(s)`,
`P_j(s) = ∑_{ℓ≤j} y_ℓ E_{j-ℓ}(s)` (`ampJet`), and

  `|η(u) e^{βsξ(u)} − ∑_{j<R} u^j F_j(s)| ≤ C u^R (1+s)^R e^{βs(a + L₁ b)}`   (`amp_jet_remainder`).

The product with `η` is handled through polynomial multiplication: the jet sum is the degree-`< R`
truncation of `jetPoly y R * jetPoly (E_·(s)) R`, whose coefficients are the Cauchy products
(`coeff_jetPoly_mul`). Zero `sorry`/`axiom`.
-/

open Real Finset Polynomial

namespace Laplace.Grammar

/-- The coefficients of a Taylor polynomial. -/
theorem coeff_jetPoly' (x : ℕ → ℝ) (R n : ℕ) :
    (jetPoly x R).coeff n = if n < R then x n else 0 := by
  unfold jetPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (range R) n]
  simp [Finset.mem_range]

theorem abs_coeff_jetPoly_le (x : ℕ → ℝ) (R n : ℕ) :
    |(jetPoly x R).coeff n| ≤ ∑ i ∈ range R, |x i| := by
  rw [coeff_jetPoly']
  split_ifs with hn
  · exact Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 hn)
  · simp only [abs_zero]
    exact Finset.sum_nonneg fun i _ => abs_nonneg _

theorem natDegree_jetPoly_le (x : ℕ → ℝ) (R : ℕ) : (jetPoly x R).natDegree ≤ R - 1 := by
  unfold jetPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- The Cauchy-product coefficients of a product of two Taylor polynomials, below the truncation
order. -/
theorem coeff_jetPoly_mul (y E : ℕ → ℝ) (R j : ℕ) (hj : j < R) :
    (jetPoly y R * jetPoly E R).coeff j = ∑ ℓ ∈ range (j + 1), y ℓ * E (j - ℓ) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l => (jetPoly y R).coeff k * (jetPoly E R).coeff l) j]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [Finset.mem_range] at hℓ
  rw [coeff_jetPoly y R ℓ (by omega), coeff_jetPoly E R (j - ℓ) (by omega)]

theorem abs_coeff_jetPoly_mul_le (y E : ℕ → ℝ) (R n : ℕ) :
    |(jetPoly y R * jetPoly E R).coeff n|
      ≤ ((n : ℝ) + 1) * ((∑ i ∈ range R, |y i|) * ∑ l ∈ range R, |E l|) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l => (jetPoly y R).coeff k * (jetPoly E R).coeff l) n]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ range (n + 1), |(jetPoly y R).coeff k * (jetPoly E R).coeff (n - k)|
      ≤ (∑ i ∈ range R, |y i|) * ∑ l ∈ range R, |E l| := by
    intro k _
    rw [abs_mul]
    exact mul_le_mul (abs_coeff_jetPoly_le y R k) (abs_coeff_jetPoly_le E R (n - k))
      (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  calc ∑ k ∈ range (n + 1), |(jetPoly y R).coeff k * (jetPoly E R).coeff (n - k)|
      ≤ ∑ _k ∈ range (n + 1), ((∑ i ∈ range R, |y i|) * ∑ l ∈ range R, |E l|) :=
        Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- The truncation constant of the product polynomial, uniformly in the second factor. -/
theorem truncConst_jetPoly_mul_le (y E : ℕ → ℝ) (R : ℕ) (hR : 0 < R) (b : ℝ) (hb : 0 ≤ b) :
    truncConst (jetPoly y R * jetPoly E R) R b
      ≤ (∑ n ∈ Ico R (2 * R), ((n : ℝ) + 1) * b ^ (n - R))
        * ((∑ i ∈ range R, |y i|) * ∑ l ∈ range R, |E l|) := by
  unfold truncConst
  have hdeg : (jetPoly y R * jetPoly E R).natDegree + 1 ≤ 2 * R := by
    have h1 := natDegree_jetPoly_le y R
    have h2 := natDegree_jetPoly_le E R
    have := Polynomial.natDegree_mul_le (p := jetPoly y R) (q := jetPoly E R)
    omega
  have hsub : Ico R (max R ((jetPoly y R * jetPoly E R).natDegree + 1)) ⊆ Ico R (2 * R) := by
    intro n hn
    rw [Finset.mem_Ico] at hn ⊢
    refine ⟨hn.1, lt_of_lt_of_le hn.2 (max_le (by omega) hdeg)⟩
  calc ∑ n ∈ Ico R (max R ((jetPoly y R * jetPoly E R).natDegree + 1)),
        |(jetPoly y R * jetPoly E R).coeff n| * b ^ (n - R)
      ≤ ∑ n ∈ Ico R (2 * R), |(jetPoly y R * jetPoly E R).coeff n| * b ^ (n - R) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          mul_nonneg (abs_nonneg _) (pow_nonneg hb _)
    _ ≤ ∑ n ∈ Ico R (2 * R), (((n : ℝ) + 1) * ((∑ i ∈ range R, |y i|) * ∑ l ∈ range R, |E l|))
          * b ^ (n - R) := by
        refine Finset.sum_le_sum fun n _ => ?_
        exact mul_le_mul_of_nonneg_right (abs_coeff_jetPoly_mul_le y E R n) (pow_nonneg hb _)
    _ = _ := by
        rw [Finset.sum_mul (Ico R (2 * R))]
        refine Finset.sum_congr rfl ?_
        intro n _
        ring

/-- The amplitude jet coefficients `P_j(s) = ∑_{ℓ≤j} y_ℓ E_{j-ℓ}(s)`. -/
noncomputable def ampJet (β : ℝ) (x y : ℕ → ℝ) (R j : ℕ) (s : ℝ) : ℝ :=
  ∑ ℓ ∈ range (j + 1), y ℓ * expJet β x R (j - ℓ) s

theorem ampJet_continuous (β : ℝ) (x y : ℕ → ℝ) (R j : ℕ) : Continuous (ampJet β x y R j) := by
  unfold ampJet
  exact continuous_finsetSum _ fun ℓ _ => continuous_const.mul (expJet_continuous β x R _)

/-- The Taylor polynomial of `g = ξ − x₀` evaluates to the Taylor sum of `ξ` minus `x₀`. -/
theorem eval_gPoly_eq (x : ℕ → ℝ) (R : ℕ) (hR : 0 < R) (u : ℝ) :
    (gPoly x R).eval u = (∑ i ∈ range R, x i * u ^ i) - x 0 := by
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  rw [eval_gPoly, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [shiftSeq, Nat.succ_ne_zero, if_false, if_true, pow_zero, mul_one, add_zero]
  ring

/-- **The amplitude jet remainder**: there is `C` with
`|η(u) e^{βsξ(u)} − ∑_{j<R} u^j e^{βs x₀} P_j(s)| ≤ C u^R (1+s)^R e^{βs(x₀ + L₁ b)}`
on `[0,b] × [0,∞)`. -/
theorem amp_jet_remainder (β b K L₁ : ℝ) (hβ : 0 < β) (hb : 0 < b) (hK : 0 ≤ K) (hL₁ : 0 ≤ L₁)
    (x y : ℕ → ℝ) (R : ℕ) (hR : 0 < R) (ξ η : ℝ → ℝ)
    (hξT : ∀ u ∈ Set.Icc (0 : ℝ) b, |ξ u - ∑ i ∈ range R, x i * u ^ i| ≤ K * u ^ R)
    (hηT : ∀ u ∈ Set.Icc (0 : ℝ) b, |η u - ∑ i ∈ range R, y i * u ^ i| ≤ K * u ^ R)
    (hξL : ∀ u ∈ Set.Icc (0 : ℝ) b, |ξ u - x 0| ≤ L₁ * u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |η u * Real.exp (β * s * ξ u)
          - ∑ j ∈ range R, u ^ j * (Real.exp (β * s * x 0) * ampJet β x y R j s)|
        ≤ C * u ^ R * (1 + s) ^ R * Real.exp (β * s * (x 0 + L₁ * b)) := by
  set a : ℝ := x 0 with ha
  set g : ℝ → ℝ := fun u => ξ u - a with hgdef
  have hg : ∀ u ∈ Set.Icc (0 : ℝ) b, |g u - (gPoly x R).eval u| ≤ K * u ^ R := by
    intro u hu
    rw [eval_gPoly_eq x R hR u]
    simp only [hgdef, ha]
    have := hξT u hu
    rwa [show ξ u - x 0 - ((∑ i ∈ range R, x i * u ^ i) - x 0)
      = ξ u - ∑ i ∈ range R, x i * u ^ i by ring]
  have hgL : ∀ u ∈ Set.Icc (0 : ℝ) b, |g u| ≤ L₁ * u := fun u hu => hξL u hu
  -- the exponential jet remainder constant
  set C₁ : ℝ := (β * L₁) ^ R / (R.factorial : ℝ)
    + ∑ m ∈ range R, β ^ m / (m.factorial : ℝ)
      * (K * m * (max L₁ (∑ i ∈ range R, |shiftSeq x i| * b ^ (i - 1)) * b) ^ (m - 1)
        + truncConst ((gPoly x R) ^ m) R b) with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have h1 : 0 ≤ (β * L₁) ^ R / (R.factorial : ℝ) := by positivity
    have h2 : ∀ m ∈ range R, 0 ≤ β ^ m / (m.factorial : ℝ)
        * (K * m * (max L₁ (∑ i ∈ range R, |shiftSeq x i| * b ^ (i - 1)) * b) ^ (m - 1)
          + truncConst ((gPoly x R) ^ m) R b) := by
      intro m _
      have : 0 ≤ truncConst ((gPoly x R) ^ m) R b :=
        Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hb.le _)
      have : 0 ≤ max L₁ (∑ i ∈ range R, |shiftSeq x i| * b ^ (i - 1)) := le_max_of_le_left hL₁
      positivity
    exact add_nonneg h1 (Finset.sum_nonneg h2)
  -- constants for the product
  set Y : ℝ := ∑ i ∈ range R, |y i| with hY
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => abs_nonneg _
  set Yb : ℝ := ∑ i ∈ range R, |y i| * b ^ i with hYb
  have hYb0 : 0 ≤ Yb := Finset.sum_nonneg fun i _ => by positivity
  set EC : ℝ := ∑ l ∈ range R, expJetConst β x R l with hEC
  have hEC0 : 0 ≤ EC := Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => by positivity
  set T : ℝ := ∑ n ∈ Ico R (2 * R), ((n : ℝ) + 1) * b ^ (n - R) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  refine ⟨K + Yb * C₁ + T * (Y * EC), by positivity, fun u hu s hs => ?_⟩
  have hu0 : 0 ≤ u := hu.1
  have hub : u ≤ b := hu.2
  have hbs : 0 ≤ β * s := by positivity
  -- notation
  set E : ℝ := Real.exp (β * s * g u) with hE
  set Ejet : ℝ := ∑ n ∈ range R, expJet β x R n s * u ^ n with hEjet
  set ηP : ℝ := ∑ i ∈ range R, y i * u ^ i with hηP
  set Es : ℕ → ℝ := fun n => expJet β x R n s with hEs
  have hEle : E ≤ Real.exp (β * L₁ * b * s) := by
    rw [hE]
    refine Real.exp_le_exp.2 ?_
    have := (le_abs_self (g u)).trans (hgL u hu)
    have := mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_left hub hL₁)) hbs
    linarith
  have hE1 : 1 ≤ Real.exp (β * L₁ * b * s) := Real.one_le_exp (by positivity)
  have hs1 : 1 ≤ (1 + s) ^ R := one_le_pow₀ (by linarith)
  have hEjr := exp_jet_remainder β b K L₁ hβ hb hK hL₁ x R g hg hgL u s hu hs
  rw [← hC₁] at hEjr
  -- the three pieces
  have hA : |(η u - ηP) * E| ≤ K * u ^ R * (1 + s) ^ R * Real.exp (β * L₁ * b * s) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |η u - ηP| * E ≤ (K * u ^ R) * Real.exp (β * L₁ * b * s) :=
          mul_le_mul (hηT u hu) hEle (Real.exp_pos _).le (by positivity)
      _ = K * u ^ R * 1 * Real.exp (β * L₁ * b * s) := by ring
      _ ≤ _ := by gcongr
  have hηPb : |ηP| ≤ Yb := by
    rw [hηP, hYb]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_pow, abs_of_nonneg hu0]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 hub i) (abs_nonneg _)
  have hB : |ηP * (E - Ejet)| ≤ Yb * C₁ * u ^ R * (1 + s) ^ R * Real.exp (β * L₁ * b * s) := by
    rw [abs_mul]
    calc |ηP| * |E - Ejet| ≤ Yb * (C₁ * u ^ R * (1 + s) ^ R * Real.exp (β * L₁ * b * s)) :=
          mul_le_mul hηPb hEjr (abs_nonneg _) hYb0
      _ = _ := by ring
  -- the product piece via polynomials
  have hprod_eval : ηP * Ejet = (jetPoly y R * jetPoly Es R).eval u := by
    rw [Polynomial.eval_mul, eval_jetPoly, eval_jetPoly]
  have hjetsum : ∑ j ∈ range R, ampJet β x y R j s * u ^ j
      = ∑ j ∈ range R, (jetPoly y R * jetPoly Es R).coeff j * u ^ j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [coeff_jetPoly_mul y Es R j (Finset.mem_range.1 hj)]
    rfl
  have hEsb : ∑ l ∈ range R, |Es l| ≤ EC * (1 + s) ^ R := by
    rw [hEC, Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => expJet_abs_le β hβ x R l s hs
  have hC : |ηP * Ejet - ∑ j ∈ range R, ampJet β x y R j s * u ^ j|
      ≤ T * (Y * EC) * u ^ R * (1 + s) ^ R * Real.exp (β * L₁ * b * s) := by
    rw [hprod_eval, hjetsum]
    have h1 := poly_trunc_le (jetPoly y R * jetPoly Es R) R b u hu0 hub
    have h2 := truncConst_jetPoly_mul_le y Es R hR b hb.le
    rw [← hY] at h2
    calc |(jetPoly y R * jetPoly Es R).eval u
          - ∑ j ∈ range R, (jetPoly y R * jetPoly Es R).coeff j * u ^ j|
        ≤ u ^ R * truncConst (jetPoly y R * jetPoly Es R) R b := h1
      _ ≤ u ^ R * (T * (Y * ∑ l ∈ range R, |Es l|)) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hu0 _)
      _ ≤ u ^ R * (T * (Y * (EC * (1 + s) ^ R))) := by gcongr
      _ = T * (Y * EC) * u ^ R * (1 + s) ^ R * 1 := by ring
      _ ≤ _ := by gcongr
  -- assemble
  have hsplit : η u * Real.exp (β * s * ξ u)
      - ∑ j ∈ range R, u ^ j * (Real.exp (β * s * a) * ampJet β x y R j s)
      = Real.exp (β * s * a)
        * ((η u - ηP) * E + ηP * (E - Ejet)
          + (ηP * Ejet - ∑ j ∈ range R, ampJet β x y R j s * u ^ j)) := by
    have hexp : Real.exp (β * s * ξ u) = Real.exp (β * s * a) * E := by
      rw [hE, hgdef, ← Real.exp_add]; congr 1; ring
    have hsum : ∑ j ∈ range R, u ^ j * (Real.exp (β * s * a) * ampJet β x y R j s)
        = Real.exp (β * s * a) * ∑ j ∈ range R, ampJet β x y R j s * u ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hexp, hsum]; ring
  have hexp2 : Real.exp (β * s * a) * Real.exp (β * L₁ * b * s)
      = Real.exp (β * s * (a + L₁ * b)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (β * s * a) * |(η u - ηP) * E + ηP * (E - Ejet)
        + (ηP * Ejet - ∑ j ∈ range R, ampJet β x y R j s * u ^ j)|
      ≤ Real.exp (β * s * a) * (|(η u - ηP) * E| + |ηP * (E - Ejet)|
        + |ηP * Ejet - ∑ j ∈ range R, ampJet β x y R j s * u ^ j|) :=
        mul_le_mul_of_nonneg_left (abs_add_three _ _ _) (Real.exp_pos _).le
    _ ≤ Real.exp (β * s * a) * ((K + Yb * C₁ + T * (Y * EC)) * u ^ R * (1 + s) ^ R
        * Real.exp (β * L₁ * b * s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        linarith [hA, hB, hC]
    _ = _ := by rw [← hexp2]; ring

end Laplace.Grammar
