/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PolynomialPerturbation

/-!
# Leading asymptotic of the standard integral for polynomial data (grammar §4.2)

The one-dimensional leading term of `cor:standardintegralexp` for general polynomial data
`ξ(u) = ξ₀ + ∑_{j<D} c_j u^{j+1}` and `η(u) = ∑_{i≤E} e_i u^i`:

  `∫₀^b u^h η(u) e^{-βn u^{2k} + β√n u^k ξ(u)} du
      ~ η(0) · (2k)^{-1} S_{(h+1)/(2k)}(ξ(0)) · n^{-(h+1)/(2k)}`

as `n → ∞` (for `η(0) ≠ 0`). Only the values `ξ(0)`, `η(0)` at the origin of the chart enter the
leading coefficient, and the leading exponent is the first element `(h+1)/(2k)` of `Λ(h,k)`; every
other monomial of `ξ` or `η` contributes at order `n^{-(h+2)/(2k)}` or beyond. On the way we package
the polynomial-`ξ` two-term bound as `Z - (2k)^{-1} n^{-(h+1)/(2k)} S(ξ₀) = O(n^{-(h+2)/(2k)})`.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

/-- `n^{-a} = o(n^{-b})` as `n → ∞` when `b < a`. -/
theorem isLittleO_rpow_neg_rpow_neg {a b : ℝ} (hab : b < a) :
    (fun n : ℝ => n ^ (-a)) =o[atTop] fun n : ℝ => n ^ (-b) := by
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn h
    exact absurd h (Real.rpow_pos_of_pos hn _).ne'
  · refine (tendsto_rpow_neg_atTop (sub_pos.2 hab)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    rw [← Real.rpow_sub hn]; congr 1; ring

/-- `n^{-a} = O(n^{-b})` as `n → ∞` when `b ≤ a`. -/
theorem isBigO_rpow_neg_rpow_neg {a b : ℝ} (hab : b ≤ a) :
    (fun n : ℝ => n ^ (-a)) =O[atTop] fun n : ℝ => n ^ (-b) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn0 _),
    abs_of_pos (Real.rpow_pos_of_pos hn0 _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hab)

/-- **Leading term for a polynomial perturbation** `ξ = ξ₀ + ∑_{j<D} c_j u^{j+1}`:
`Z_chart - (2k)^{-1} n^{-(h+1)/(2k)} S_{(h+1)/(2k)}(ξ₀) = O(n^{-(h+2)/(2k)})`. -/
theorem standardIntegral1D_polynomial_leading_isBigO (β ξ₀ b : ℝ) (c : ℕ → ℝ) (h k D : ℕ)
    (hβ : 0 < β) (hb : 0 < b) (hk : 0 < k) :
    (fun n : ℝ => (∫ u in Ioc 0 b, u ^ h * Real.exp (-β * n * u ^ (2 * k)
        + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1))))
      - (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
          * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀)
      =O[atTop] fun n : ℝ => n ^ (-(((h : ℝ) + 2) / (2 * k))) := by
  set μ : ℝ := ((h : ℝ) + 2) / (2 * k) with hμ
  set ε : ℝ := β / 4 * b ^ (2 * k) with hε
  have hε0 : 0 < ε := by positivity
  set C : ℝ := ∑ j ∈ Finset.range D, |c j| * b ^ j with hC
  -- constants
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (β * C) ^ 2 / 2 * ((1 / (2 * (k : ℝ)))
    * fluctuation β ((((h + 2 : ℕ) : ℝ) + 1) / (2 * k) + 1) (ξ₀ + C * b)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ, B = fun j => |β * c j| * ((1 / (2 * (k : ℝ)))
    * fluctuation β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀) := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K : ℝ, K = Real.exp (β * ξ₀ ^ 2 / 2)
    * ((β / 4) ^ (-(((h : ℝ) + 1) / (2 * k))) * (1 / (2 * (k : ℝ)))
      * Real.Gamma (((h : ℝ) + 1) / (2 * k))) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℝ, K = fun j => Real.exp (β * ξ₀ ^ 2 / 2)
    * ((β / 4) ^ (-((((h + (j + 1) + k : ℕ) : ℝ) + 1) / (2 * k))) * (1 / (2 * (k : ℝ)))
      * Real.Gamma ((((h + (j + 1) + k : ℕ) : ℝ) + 1) / (2 * k))) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hR]
    have := fluctuation_pos β ((((h + 2 : ℕ) : ℝ) + 1) / (2 * k) + 1) (ξ₀ + C * b) hβ
      (by positivity)
    positivity
  have hB0 : ∀ j, 0 ≤ B j := by
    intro j; simp only [hB]
    have := fluctuation_pos β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀ hβ
      (by positivity)
    positivity
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]
    have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < ((h : ℝ) + 1) / (2 * k))
    positivity
  have hK0 : ∀ j, 0 ≤ K j := by
    intro j; simp only [hK]
    have := Real.Gamma_pos_of_pos
      (by positivity : (0 : ℝ) < (((h + (j + 1) + k : ℕ) : ℝ) + 1) / (2 * k))
    positivity
  -- the two exponentially small scales
  have hl₀ : (fun n : ℝ => Real.exp (-ε * n)) =o[atTop] fun n : ℝ => n ^ (-μ) :=
    isLittleO_exp_neg_mul_rpow_atTop hε0 (-μ)
  have hl₁ : (fun n : ℝ => Real.sqrt n * Real.exp (-ε * n)) =o[atTop] fun n : ℝ => n ^ (-μ) := by
    have h0 := (isBigO_refl (fun n : ℝ => Real.sqrt n) atTop).mul_isLittleO
      (isLittleO_exp_neg_mul_rpow_atTop hε0 (-μ - 1 / 2))
    refine h0.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]; congr 1; ring
  apply IsBigO.of_bound (R + K₀ + ∑ j ∈ Finset.range D, |β * c j| * K j
    + ∑ j ∈ Finset.range D, B j)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hl₀.bound one_pos, hl₁.bound one_pos]
    with n hn hb₀ hb₁
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow_pos : 0 < n ^ (-μ) := Real.rpow_pos_of_pos hn0 _
  simp only [Real.norm_eq_abs] at hb₀ hb₁ ⊢
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos hpow_pos, one_mul] at hb₀
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg n) (Real.exp_pos _).le), abs_of_pos hpow_pos,
    one_mul] at hb₁
  rw [abs_of_pos hpow_pos]
  have hmain := standardIntegral1D_polynomial_second_order β n ξ₀ b c h k D hβ hn hb hk
  rw [← hC] at hmain
  -- power comparisons for `n ≥ 1`
  have hpowR : n ^ (-((((h + 2 : ℕ) : ℝ) + 1) / (2 * k))) ≤ n ^ (-μ) := by
    apply Real.rpow_le_rpow_of_exponent_le hn
    rw [hμ, neg_le_neg_iff, div_le_div_iff_of_pos_right (by positivity)]; push_cast; linarith
  have hpowB : ∀ j : ℕ, n ^ (-((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k))) ≤ n ^ (-μ) := by
    intro j
    apply Real.rpow_le_rpow_of_exponent_le hn
    rw [hμ, neg_le_neg_iff, div_le_div_iff_of_pos_right (by positivity)]; push_cast
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- tails
  have ht₀ := standardIntegral1D_tail_le β n ξ₀ b h k hβ hn hb hk
  rw [show -(β / 4) * n * b ^ (2 * k) = -ε * n by rw [hε]; ring] at ht₀
  have htail₀ : (∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k)
      + β * Real.sqrt n * u ^ k * ξ₀)) ≤ K₀ * n ^ (-μ) := by
    calc _ ≤ _ := ht₀
      _ = K₀ * Real.exp (-ε * n) := by rw [hK₀]; ring
      _ ≤ K₀ * n ^ (-μ) := mul_le_mul_of_nonneg_left hb₀ hK₀0
  have htail₁ : ∀ j : ℕ, (∫ u in Ioi b, u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
      * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) ≤ K j * n ^ (-μ) := by
    intro j
    have hH : (fun u : ℝ => u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        = fun u => Real.sqrt n * (u ^ (h + (j + 1) + k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) := by
      funext u; rw [pow_add u (h + (j + 1))]; ring
    have ht := standardIntegral1D_tail_le β n ξ₀ b (h + (j + 1) + k) k hβ hn hb hk
    rw [show -(β / 4) * n * b ^ (2 * k) = -ε * n by rw [hε]; ring] at ht
    rw [hH, integral_const_mul]
    calc Real.sqrt n * ∫ u in Ioi b, u ^ (h + (j + 1) + k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
        ≤ Real.sqrt n * (K j * Real.exp (-ε * n)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg n)
          calc _ ≤ _ := ht
            _ = K j * Real.exp (-ε * n) := by simp only [hK]; ring
      _ = K j * (Real.sqrt n * Real.exp (-ε * n)) := by ring
      _ ≤ K j * n ^ (-μ) := mul_le_mul_of_nonneg_left hb₁ (hK0 j)
  -- the first-order terms are `O(n^{-μ})` individually
  have hfirst : |∑ j ∈ Finset.range D, β * c j
      * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k)))
        * fluctuation β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀)|
      ≤ (∑ j ∈ Finset.range D, B j) * n ^ (-μ) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have hS := fluctuation_pos β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀ hβ
      (by positivity)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / (2 * (k : ℝ)))
      * n ^ (-((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k)))
      * fluctuation β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀)]
    simp only [hB]
    calc |β * c j| * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀)
        ≤ |β * c j| * ((1 / (2 * (k : ℝ))) * n ^ (-μ)
          * fluctuation β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hpowB j) (by positivity)) hS.le) (abs_nonneg _)
      _ = _ := by ring
  -- assemble
  set Z := ∫ u in Ioc 0 b, u ^ h * Real.exp (-β * n * u ^ (2 * k)
    + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1)))
  set A₀ := (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
    * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀
  set S₁ := ∑ j ∈ Finset.range D, β * c j
    * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k)))
      * fluctuation β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀)
  have hsum_tails : ∑ j ∈ Finset.range D, |β * c j| * ∫ u in Ioi b,
      u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
      ≤ (∑ j ∈ Finset.range D, |β * c j| * K j) * n ^ (-μ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (htail₁ j) (abs_nonneg _)
  have hmain' : |Z - A₀ - S₁| ≤ R * n ^ (-μ) + K₀ * n ^ (-μ)
      + (∑ j ∈ Finset.range D, |β * c j| * K j) * n ^ (-μ) := by
    calc |Z - A₀ - S₁| ≤ _ := hmain
      _ = R * n ^ (-((((h + 2 : ℕ) : ℝ) + 1) / (2 * k)))
          + (∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
          + ∑ j ∈ Finset.range D, |β * c j| * ∫ u in Ioi b,
              u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
              * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
          rw [hR]; ring
      _ ≤ R * n ^ (-μ) + K₀ * n ^ (-μ) + (∑ j ∈ Finset.range D, |β * c j| * K j) * n ^ (-μ) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hpowR hR0) htail₀) hsum_tails
  calc |Z - A₀| = |(Z - A₀ - S₁) + S₁| := by congr 1; ring
    _ ≤ |Z - A₀ - S₁| + |S₁| := abs_add_le _ _
    _ ≤ (R * n ^ (-μ) + K₀ * n ^ (-μ) + (∑ j ∈ Finset.range D, |β * c j| * K j) * n ^ (-μ))
        + (∑ j ∈ Finset.range D, B j) * n ^ (-μ) := add_le_add hmain' hfirst
    _ = _ := by ring

/-- **Leading asymptotic of the standard integral for polynomial data** (grammar §4.2, the leading
term of `cor:standardintegralexp` in one dimension): for `ξ(u) = ξ₀ + ∑_{j<D} c_j u^{j+1}` and
`η(u) = ∑_{i≤E} e_i u^i` with `η(0) = e_0 ≠ 0`,

`∫₀^b u^h η(u) e^{-βn u^{2k} + β√n u^k ξ(u)} du
    ~ η(0) (2k)^{-1} S_{(h+1)/(2k)}(ξ₀) n^{-(h+1)/(2k)}`.

Only the chart-origin values `ξ(0)`, `η(0)` enter the leading coefficient. -/
theorem standardIntegral1D_weighted_leading_isEquivalent (β ξ₀ b : ℝ) (c e : ℕ → ℝ) (h k D E : ℕ)
    (hβ : 0 < β) (hb : 0 < b) (hk : 0 < k) (he0 : e 0 ≠ 0) :
    (fun n : ℝ => ∫ u in Ioc 0 b, u ^ h * (∑ i ∈ Finset.range (E + 1), e i * u ^ i)
        * Real.exp (-β * n * u ^ (2 * k)
          + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1))))
      ~[atTop] fun n : ℝ => e 0 * ((1 / (2 * (k : ℝ))) * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀)
        * n ^ (-(((h : ℝ) + 1) / (2 * k))) := by
  set μ₁ : ℝ := ((h : ℝ) + 1) / (2 * k) with hμ₁
  set ν : ℝ := ((h : ℝ) + 2) / (2 * k) with hν
  have hμν : μ₁ < ν := by
    rw [hμ₁, hν, div_lt_div_iff_of_pos_right (by positivity)]; linarith
  set A₀ : ℝ := (1 / (2 * (k : ℝ))) * fluctuation β μ₁ ξ₀ with hA₀
  have hA₀pos : 0 < A₀ := by
    rw [hA₀]; have := fluctuation_pos β μ₁ ξ₀ hβ (by positivity); positivity
  -- the unweighted chart integrals at shifted powers
  set Zf : ℕ → ℝ → ℝ := fun h' n => ∫ u in Ioc 0 b, u ^ h' * Real.exp (-β * n * u ^ (2 * k)
    + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1))) with hZf
  have hA : ∀ h' : ℕ, (fun n : ℝ => Zf h' n - (1 / (2 * (k : ℝ)))
      * n ^ (-(((h' : ℝ) + 1) / (2 * k))) * fluctuation β (((h' : ℝ) + 1) / (2 * k)) ξ₀)
      =O[atTop] fun n : ℝ => n ^ (-(((h' : ℝ) + 2) / (2 * k))) :=
    fun h' => standardIntegral1D_polynomial_leading_isBigO β ξ₀ b c h' k D hβ hb hk
  -- linearity in the weight
  have hJc : Continuous (fun u : ℝ => ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1)) :=
    continuous_const.add (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow _))
  have hlin : ∀ n : ℝ, (∫ u in Ioc 0 b, u ^ h * (∑ i ∈ Finset.range (E + 1), e i * u ^ i)
        * Real.exp (-β * n * u ^ (2 * k)
          + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1))))
      = ∑ i ∈ Finset.range (E + 1), e i * Zf (h + i) n := by
    intro n
    have hcontE : Continuous (fun u : ℝ => Real.exp (-β * n * u ^ (2 * k)
        + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1)))) :=
      Real.continuous_exp.comp ((continuous_const.mul (continuous_pow _)).add
        ((continuous_const.mul (continuous_pow k)).mul hJc))
    have hfun : (fun u : ℝ => u ^ h * (∑ i ∈ Finset.range (E + 1), e i * u ^ i)
        * Real.exp (-β * n * u ^ (2 * k)
          + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1))))
        = fun u => ∑ i ∈ Finset.range (E + 1), e i * (u ^ (h + i)
          * Real.exp (-β * n * u ^ (2 * k)
            + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1)))) := by
      funext u
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
    have hi : ∀ i ∈ Finset.range (E + 1), IntegrableOn (fun u : ℝ => e i * (u ^ (h + i)
        * Real.exp (-β * n * u ^ (2 * k)
          + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1)))))
        (Ioc 0 b) := fun i _ =>
      (continuous_const.mul ((continuous_pow _).mul hcontE)).integrableOn_Ioc
    rw [hfun, integral_finsetSum _ hi]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  -- the difference from the leading term is `O(n^{-ν})`
  have hdiff : (fun n : ℝ => (∑ i ∈ Finset.range (E + 1), e i * Zf (h + i) n)
      - e 0 * A₀ * n ^ (-μ₁)) =O[atTop] fun n : ℝ => n ^ (-ν) := by
    have hsplit : ∀ n : ℝ, (∑ i ∈ Finset.range (E + 1), e i * Zf (h + i) n) - e 0 * A₀ * n ^ (-μ₁)
        = (∑ i ∈ Finset.range E, e (i + 1) * Zf (h + (i + 1)) n)
          + e 0 * (Zf h n - (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
            * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀) := by
      intro n; rw [Finset.sum_range_succ', hA₀]; simp only [add_zero]; ring
    have hS0 : (∑ i ∈ Finset.range E, fun n : ℝ => e (i + 1) * Zf (h + (i + 1)) n)
        =O[atTop] fun n : ℝ => n ^ (-ν) := by
      refine IsBigO.sum fun i _ => ?_
      have h1 := (hA (h + (i + 1))).trans (isBigO_rpow_neg_rpow_neg
        (a := (((h + (i + 1) : ℕ) : ℝ) + 2) / (2 * k)) (b := ν)
        (by rw [hν, div_le_div_iff_of_pos_right (by positivity)]; push_cast
            linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]))
      have h2 : (fun n : ℝ => (1 / (2 * (k : ℝ))) * n ^ (-((((h + (i + 1) : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + (i + 1) : ℕ) : ℝ) + 1) / (2 * k)) ξ₀)
          =O[atTop] fun n : ℝ => n ^ (-ν) := by
        have := (isBigO_rpow_neg_rpow_neg (a := (((h + (i + 1) : ℕ) : ℝ) + 1) / (2 * k)) (b := ν)
          (by rw [hν, div_le_div_iff_of_pos_right (by positivity)]; push_cast
              linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])).const_mul_left
          ((1 / (2 * (k : ℝ))) * fluctuation β ((((h + (i + 1) : ℕ) : ℝ) + 1) / (2 * k)) ξ₀)
        exact this.congr_left fun n => by ring
      have h12 : (fun n : ℝ => Zf (h + (i + 1)) n) =O[atTop] fun n : ℝ => n ^ (-ν) :=
        (h1.add h2).congr_left fun n => by ring
      exact h12.const_mul_left (e (i + 1))
    have hS : (fun n : ℝ => ∑ i ∈ Finset.range E, e (i + 1) * Zf (h + (i + 1)) n)
        =O[atTop] fun n : ℝ => n ^ (-ν) :=
      hS0.congr_left fun n => by simp only [Finset.sum_apply]
    have h0 : (fun n : ℝ => e 0 * (Zf h n - (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
        * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀)) =O[atTop] fun n : ℝ => n ^ (-ν) :=
      (hA h).const_mul_left (e 0)
    exact (hS.add h0).congr_left fun n => (hsplit n).symm
  -- conclude
  apply IsLittleO.isEquivalent
  have hlittle : (fun n : ℝ => (∑ i ∈ Finset.range (E + 1), e i * Zf (h + i) n)
      - e 0 * A₀ * n ^ (-μ₁)) =o[atTop] fun n : ℝ => e 0 * A₀ * n ^ (-μ₁) :=
    (hdiff.trans_isLittleO (isLittleO_rpow_neg_rpow_neg hμν)).const_mul_right
      (mul_ne_zero he0 hA₀pos.ne')
  have hfin : (fun n : ℝ => (∫ u in Ioc 0 b, u ^ h * (∑ i ∈ Finset.range (E + 1), e i * u ^ i)
        * Real.exp (-β * n * u ^ (2 * k)
          + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1))))
      - e 0 * A₀ * n ^ (-μ₁)) =o[atTop] fun n : ℝ => e 0 * A₀ * n ^ (-μ₁) :=
    hlittle.congr_left fun n => by rw [hlin n]
  exact hfin

end Laplace.Grammar
