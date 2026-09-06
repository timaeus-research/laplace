/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AllOrdersAsymptotic

/-!
# Two-term expansion for a polynomial perturbation (grammar §4.2)

For a general polynomial perturbation `ξ(u) = ξ₀ + ∑_{j<D} c_j u^{j+1}` (any `ξ` analytic at `0`
with
`ξ(0) = ξ₀`, truncated), the first-order term of the Taylor tree is a *sum over monomials*: each
`c_j u^{j+1}` contributes `β c_j (2k)^{-1} n^{-(h+j+2)/(2k)} S_{(h+j+2)/(2k)+1/2}(ξ₀)`, so the
exponents
`(h+j+2)/(2k)` for `j < D` all appear — the arithmetic progression of `Λ(h,k)` is populated by the
different monomials of `ξ`, not just by powers of one. The remainder after these terms is bounded by
an explicit multiple of `n^{-(h+3)/(2k)}` (the `u²`-order of the Taylor remainder of `e^{x}`) plus
the
boundary tails. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- **Two-term expansion of the chart standard integral for a polynomial perturbation**
`ξ(u) = ξ₀ + ∑_{j<D} c_j u^{j+1}`, with explicit remainder: for `n ≥ 1`, writing
`C = ∑_{j<D} |c_j| b^j`,

`|Z_chart - (2k)^{-1} n^{-(h+1)/(2k)} S_{(h+1)/(2k)}(ξ₀)
   - ∑_{j<D} β c_j (2k)^{-1} n^{-(h+j+2)/(2k)} S_{(h+j+2)/(2k)+1/2}(ξ₀)|
   ≤ (βC)²/2 (2k)^{-1} n^{-(h+3)/(2k)} S_{(h+3)/(2k)+1}(ξ₀ + C b) + tail₀ + ∑_{j<D} |β c_j|
tail_{1,j}`.
-/
theorem standardIntegral1D_polynomial_second_order (β n ξ₀ b : ℝ) (c : ℕ → ℝ) (h k D : ℕ)
    (hβ : 0 < β) (hn : 1 ≤ n) (hb : 0 < b) (hk : 0 < k) :
    |(∫ u in Ioc 0 b, u ^ h * Real.exp (-β * n * u ^ (2 * k)
        + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1))))
      - (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
          * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀
      - ∑ j ∈ Finset.range D, β * c j
          * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀)|
      ≤ (β * ∑ j ∈ Finset.range D, |c j| * b ^ j) ^ 2 / 2
          * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + 2 : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + 2 : ℕ) : ℝ) + 1) / (2 * k) + 1)
              (ξ₀ + (∑ j ∈ Finset.range D, |c j| * b ^ j) * b))
        + (∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        + ∑ j ∈ Finset.range D, |β * c j| * ∫ u in Ioi b, u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨pop, hpop⟩ : ∃ f : ℝ → ℝ,
      f = fun u => Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ f : ℝ → ℝ, f = fun u => ∑ j ∈ Finset.range D, c j * u ^ (j + 1) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ f : ℝ → ℝ, f = fun u => β * Real.sqrt n * u ^ k * J u := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ j ∈ Finset.range D, |c j| * b ^ j := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]; exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (pow_nonneg hb.le _)
  obtain ⟨g₀, hg₀⟩ : ∃ g : ℝ → ℝ, g = fun u => u ^ h * pop u := ⟨_, rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g : ℝ → ℝ, g = fun u => u ^ h * pop u * x u := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g : ℝ → ℝ,
      g = fun u => u ^ h * pop u * (Real.exp (x u) - 1 - x u) := ⟨_, rfl⟩
  have hcont_pop : Continuous pop := by rw [hpop]; fun_prop
  have hcont_J : Continuous J := by
    rw [hJ]; exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow _)
  have hcont_x : Continuous x := by
    rw [hx]; exact (continuous_const.mul (continuous_pow k)).mul hcont_J
  have hdecomp : (fun u : ℝ => u ^ h * Real.exp (-β * n * u ^ (2 * k)
      + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1))))
      = fun u => g₀ u + g₁ u + g₂ u := by
    funext u
    simp only [hg₀, hg₁, hg₂, hpop, hx, hJ]
    rw [show -β * n * u ^ (2 * k)
        + β * Real.sqrt n * u ^ k * (ξ₀ + ∑ j ∈ Finset.range D, c j * u ^ (j + 1))
        = (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
          + β * Real.sqrt n * u ^ k * ∑ j ∈ Finset.range D, c j * u ^ (j + 1) by ring, Real.exp_add]
    ring
  have hcont₀ : Continuous g₀ := by rw [hg₀]; exact (continuous_pow h).mul hcont_pop
  have hcont₁ : Continuous g₁ := by rw [hg₁]; exact ((continuous_pow h).mul hcont_pop).mul hcont_x
  have hcont₂ : Continuous g₂ := by
    rw [hg₂]
    exact ((continuous_pow h).mul hcont_pop).mul
      (((Real.continuous_exp.comp hcont_x).sub continuous_const).sub hcont_x)
  have hi₀ : IntegrableOn g₀ (Ioc 0 b) := hcont₀.integrableOn_Ioc
  have hi₁ : IntegrableOn g₁ (Ioc 0 b) := hcont₁.integrableOn_Ioc
  have hi₂ : IntegrableOn g₂ (Ioc 0 b) := hcont₂.integrableOn_Ioc
  have hi₀₁ : IntegrableOn (fun u => g₀ u + g₁ u) (Ioc 0 b) := hi₀.add hi₁
  -- zeroth order
  have hI₀ : (∫ u in Ioc 0 b, g₀ u)
      = (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
          * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀
        - ∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
    have hint := standardIntegrand_integrableOn β n ξ₀ h k hβ hn0 hk
    have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl b)) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hb.le))
    rw [Ioc_union_Ioi_eq_Ioi hb.le, standardIntegral1D_eq_fluctuation β n ξ₀ h k hn0 hk] at hsplit
    simp only [hg₀, hpop]
    linarith
  -- first order: a sum over the monomials of the perturbation
  have hg₁sum : ∀ u, g₁ u = ∑ j ∈ Finset.range D,
      β * c j * (u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k) * pop u) := by
    intro u
    rw [show g₁ u = (u ^ h * pop u * (β * Real.sqrt n * u ^ k))
        * ∑ j ∈ Finset.range D, c j * u ^ (j + 1) by simp only [hg₁, hx, hJ]; ring, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring
  have hterm : ∀ j ∈ Finset.range D,
      (∫ u in Ioc 0 b, β * c j * (u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k) * pop u))
      = β * c j * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀)
        - β * c j * ∫ u in Ioi b, u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
    intro j _
    have hH : (fun u : ℝ => u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        = fun u => Real.sqrt n * (u ^ (h + (j + 1) + k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) := by
      funext u; rw [pow_add u (h + (j + 1))]; ring
    have hint : IntegrableOn (fun u : ℝ => u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) (Ioi 0) := by
      rw [hH]
      exact (standardIntegrand_integrableOn β n ξ₀ (h + (j + 1) + k) k hβ hn0 hk).const_mul _
    have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl b)) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hb.le))
    have hins := standardIntegral1D_insertion β n ξ₀ (h + (j + 1)) k 1 hn0 hk
    simp only [pow_one] at hins
    rw [Ioc_union_Ioi_eq_Ioi hb.le, hins] at hsplit
    rw [integral_const_mul, ← mul_sub]
    simp only [hpop]
    congr 1
    linarith
  have hI₁ : (∫ u in Ioc 0 b, g₁ u)
      = (∑ j ∈ Finset.range D, β * c j
          * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + (j + 1) : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀))
        - ∑ j ∈ Finset.range D, β * c j * ∫ u in Ioi b, u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
    have hfun : g₁ = fun u => ∑ j ∈ Finset.range D,
        β * c j * (u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k) * pop u) := funext hg₁sum
    have hiT : ∀ j ∈ Finset.range D, IntegrableOn
        (fun u : ℝ => β * c j * (u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k) * pop u)) (Ioc 0 b) :=
      fun j _ => (continuous_const.mul (((continuous_pow _).mul
        (continuous_const.mul (continuous_pow k))).mul hcont_pop)).integrableOn_Ioc
    rw [hfun, integral_finsetSum _ hiT, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  -- the remainder
  obtain ⟨a', ha'⟩ : ∃ a : ℝ, a = ξ₀ + C * b := ⟨_, rfl⟩
  obtain ⟨bnd, hbnd⟩ : ∃ g : ℝ → ℝ, g = fun u => (β * C) ^ 2 / 2
      * (u ^ (h + 2) * (Real.sqrt n * u ^ k) ^ 2
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) := ⟨_, rfl⟩
  have hbnd_int : IntegrableOn bnd (Ioi 0) := by
    have hH : (fun u : ℝ => u ^ (h + 2) * (Real.sqrt n * u ^ k) ^ 2
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a'))
        = fun u => Real.sqrt n ^ 2 * (u ^ (h + 2 + k * 2)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) := by
      funext u; rw [mul_pow, ← pow_mul, pow_add u (h + 2)]; ring
    have hint : IntegrableOn (fun u : ℝ => u ^ (h + 2) * (Real.sqrt n * u ^ k) ^ 2
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) (Ioi 0) := by
      rw [hH]
      exact (standardIntegrand_integrableOn β n a' (h + 2 + k * 2) k hβ hn0 hk).const_mul _
    rw [hbnd]; exact hint.const_mul _
  have hbnd_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ bnd u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    simp only [hbnd]; positivity
  have hbnd_val : (∫ u in Ioi 0, bnd u)
      = (β * C) ^ 2 / 2 * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + 2 : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + 2 : ℕ) : ℝ) + 1) / (2 * k) + 1) a') := by
    simp only [hbnd]
    rw [integral_const_mul, standardIntegral1D_insertion β n a' (h + 2) k 2 hn0 hk,
      show (((2 : ℕ) : ℝ)) / 2 = 1 by norm_num]
  have hpt : ∀ u ∈ Ioc (0 : ℝ) b, |g₂ u| ≤ bnd u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hub : u ≤ b := hu.2
    have hR := abs_exp_sub_one_sub_self_le (x u)
    have hpop_pos : 0 < pop u := by simp only [hpop]; exact Real.exp_pos _
    have hupop : 0 ≤ u ^ h * pop u := mul_nonneg (pow_nonneg hu0.le h) hpop_pos.le
    -- the polynomial perturbation is at most `C u` on the chart
    have hJle : |J u| ≤ C * u := by
      simp only [hJ]
      calc |∑ j ∈ Finset.range D, c j * u ^ (j + 1)|
          ≤ ∑ j ∈ Finset.range D, |c j * u ^ (j + 1)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j ∈ Finset.range D, |c j| * u ^ j * u := Finset.sum_congr rfl fun j _ => by
            rw [abs_mul, abs_pow, abs_of_nonneg hu0.le, pow_succ]; ring
        _ ≤ ∑ j ∈ Finset.range D, |c j| * b ^ j * u := Finset.sum_le_sum fun j _ => by gcongr
        _ = C * u := by rw [hC, Finset.sum_mul]
    have hxle : |x u| ≤ β * Real.sqrt n * u ^ k * (C * u) := by
      simp only [hx]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β * Real.sqrt n * u ^ k)]
      exact mul_le_mul_of_nonneg_left hJle (by positivity)
    have hx2 : x u ^ 2 / 2 ≤ (β * Real.sqrt n * u ^ k * (C * u)) ^ 2 / 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hxle 2
      rw [sq_abs] at this
      linarith
    have hexpB : Real.exp |x u| ≤ Real.exp (β * Real.sqrt n * u ^ k * (C * b)) := by
      apply Real.exp_le_exp.2
      calc |x u| ≤ β * Real.sqrt n * u ^ k * (C * u) := hxle
        _ ≤ β * Real.sqrt n * u ^ k * (C * b) := by gcongr
    have hpopB : pop u * Real.exp (β * Real.sqrt n * u ^ k * (C * b))
        = Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a') := by
      simp only [hpop]; rw [← Real.exp_add]; congr 1; rw [ha']; ring
    calc |g₂ u| = u ^ h * pop u * |Real.exp (x u) - 1 - x u| := by
          simp only [hg₂]; rw [abs_mul, abs_of_nonneg hupop]
      _ ≤ u ^ h * pop u * (x u ^ 2 / 2 * Real.exp |x u|) := mul_le_mul_of_nonneg_left hR hupop
      _ ≤ u ^ h * pop u * ((β * Real.sqrt n * u ^ k * (C * u)) ^ 2 / 2
            * Real.exp (β * Real.sqrt n * u ^ k * (C * b))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hx2 hexpB (Real.exp_pos _).le (by positivity)) hupop
      _ = (β * C) ^ 2 / 2 * (u ^ (h + 2) * (Real.sqrt n * u ^ k) ^ 2
            * (pop u * Real.exp (β * Real.sqrt n * u ^ k * (C * b)))) := by ring
      _ = bnd u := by simp only [hbnd]; rw [hpopB]
  have hI₂ : |∫ u in Ioc 0 b, g₂ u|
      ≤ (β * C) ^ 2 / 2 * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + 2 : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + 2 : ℕ) : ℝ) + 1) / (2 * k) + 1) a') := by
    calc |∫ u in Ioc 0 b, g₂ u| ≤ ∫ u in Ioc 0 b, |g₂ u| := abs_integral_le_integral_abs
      _ ≤ ∫ u in Ioc 0 b, bnd u :=
          setIntegral_mono_on hi₂.abs (hbnd_int.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hpt
      _ ≤ ∫ u in Ioi 0, bnd u := by
          apply setIntegral_mono_set hbnd_int
          · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
            exact Filter.Eventually.of_forall fun u hu => hbnd_nonneg u hu
          · exact Ioc_subset_Ioi_self.eventuallyLE
      _ = _ := hbnd_val
  rw [ha', hC] at hI₂
  have htail₀ : 0 ≤ ∫ u in Ioi b,
      u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (pow_nonneg (hb.trans hu).le h) (Real.exp_pos _).le
  have htail₁ : ∀ j : ℕ, 0 ≤ ∫ u in Ioi b, u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
      * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := fun j =>
    setIntegral_nonneg measurableSet_Ioi fun u hu => by
      have hu0 : (0 : ℝ) < u := hb.trans hu
      positivity
  -- assemble
  rw [hdecomp, integral_add hi₀₁ hi₂, integral_add hi₀ hi₁, hI₀, hI₁]
  have key : ∀ (A T SA ST I : ℝ), A - T + (SA - ST) + I - A - SA = I - T - ST := by intros; ring
  rw [key]
  have hST : |∑ j ∈ Finset.range D, β * c j * ∫ u in Ioi b,
          u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)|
      ≤ ∑ j ∈ Finset.range D, |β * c j| * ∫ u in Ioi b, u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [abs_mul, abs_of_nonneg (htail₁ j)]
  calc _ ≤ |∫ u in Ioc 0 b, g₂ u| + |∫ u in Ioi b,
          u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)|
        + |∑ j ∈ Finset.range D, β * c j * ∫ u in Ioi b, u ^ (h + (j + 1)) * (Real.sqrt n * u ^ k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)| := by
        calc _ ≤ |(∫ u in Ioc 0 b, g₂ u) - ∫ u in Ioi b,
              u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)| + _ :=
              abs_sub _ _
          _ ≤ _ := by gcongr; exact abs_sub _ _
    _ ≤ _ := by
        rw [abs_of_nonneg htail₀]
        exact add_le_add (add_le_add hI₂ le_rfl) hST

end Laplace.Grammar
