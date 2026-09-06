/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Asymptotic

/-!
# The second-order term of the one-dimensional Taylor tree (grammar §4.2)

For `ξ(u) = ξ₀ + c u^m` we isolate the first two terms of the monomial Taylor tree with an explicit
remainder. Writing `e^{x} = 1 + x + R(x)` with `|R(x)| ≤ (x²/2) e^{|x|}` (proved here for all real
`x`; Mathlib only has the `|x| ≤ 1` version) and `x = β√n u^k c u^m`, the chart standard integral is

  `(2k)^{-1} n^{-μ₁} S_{μ₁}(ξ₀) + βc (2k)^{-1} n^{-μ₂} S_{μ₂ + 1/2}(ξ₀) + (remainder)`,

`μ₁ = (h+1)/(2k)`, `μ₂ = (h+m+1)/(2k)`, where the remainder is bounded by an explicit multiple of
`n^{-(h+2m+1)/(2k)}` plus the two exponentially small boundary tails. This exhibits the *second*
exponent `μ₂ ∈ Λ(h,k)` with its fluctuation-function coefficient. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- **Global second-order remainder bound for the exponential**: `|eˣ - 1 - x| ≤ (x²/2) e^{|x|}` for
every real `x` (Mathlib's `abs_exp_sub_one_sub_id_le` needs `|x| ≤ 1`). From the exponential series,
comparing `|x|^{p+2}/(p+2)!` with `(x²/2)|x|^p/p!`. -/
theorem abs_exp_sub_one_sub_self_le (x : ℝ) :
    |Real.exp x - 1 - x| ≤ x ^ 2 / 2 * Real.exp |x| := by
  have hexp : HasSum (fun p : ℕ => x ^ p / p.factorial) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have hexpa : HasSum (fun p : ℕ => |x| ^ p / p.factorial) (Real.exp |x|) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp |x|
  have h2 : HasSum (fun p : ℕ => x ^ (p + 2) / (p + 2).factorial)
      (Real.exp x - ∑ i ∈ Finset.range 2, x ^ i / (i.factorial : ℝ)) :=
    (hasSum_nat_add_iff' 2).2 hexp
  have hsum2 : (∑ i ∈ Finset.range 2, x ^ i / (i.factorial : ℝ)) = 1 + x := by
    norm_num [Finset.sum_range_succ]
  rw [hsum2] at h2
  have hg : HasSum (fun p : ℕ => x ^ 2 / 2 * (|x| ^ p / p.factorial))
      (x ^ 2 / 2 * Real.exp |x|) := hexpa.mul_left _
  have hterm : ∀ p : ℕ,
      |x ^ (p + 2) / (p + 2).factorial| ≤ x ^ 2 / 2 * (|x| ^ p / p.factorial) := by
    intro p
    have hfac : (2 : ℝ) * p.factorial ≤ ((p + 2).factorial : ℝ) := by
      have : 2 * p.factorial ≤ (p + 2).factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        exact Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      exact_mod_cast this
    have hfpos : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
    rw [abs_div, abs_pow, Nat.abs_cast]
    calc |x| ^ (p + 2) / ((p + 2).factorial : ℝ) ≤ |x| ^ (p + 2) / (2 * p.factorial) := by
          gcongr
      _ = x ^ 2 / 2 * (|x| ^ p / p.factorial) := by rw [pow_add, sq_abs]; ring
  have hle : Real.exp x - (1 + x) ≤ x ^ 2 / 2 * Real.exp |x| :=
    hasSum_le (fun p => (le_abs_self _).trans (hterm p)) h2 hg
  have hge : -(Real.exp x - (1 + x)) ≤ x ^ 2 / 2 * Real.exp |x| :=
    hasSum_le (fun p => (neg_le_abs _).trans (hterm p)) h2.neg hg
  rw [abs_le]; constructor <;> linarith

/-- **Two-term expansion of the chart standard integral with explicit remainder**
(grammar §4.2, the first two terms of `thm:TaylorTree` for `d = 1`, `ξ = ξ₀ + c u^m`): for `n ≥ 1`,

`|Z_chart - (2k)^{-1} n^{-μ₁} S_{μ₁}(ξ₀) - βc (2k)^{-1} n^{-μ₂} S_{μ₂+1/2}(ξ₀)|
   ≤ (βc)²/2 · (2k)^{-1} n^{-(h+2m+1)/(2k)} S_{(h+2m+2k+1)/(2k)}(ξ₀ + |c| b^m)
     + tail₀ + |βc| tail₁`,

where `tail₀`, `tail₁` are the boundary tails of the zeroth- and first-order insertion integrals
over `(b, ∞)` (each `O(e^{-(β/4) b^{2k} n})` by `standardIntegral1D_tail_le`). -/
theorem standardIntegral1D_second_order (β n ξ₀ c b : ℝ) (h k m : ℕ)
    (hβ : 0 < β) (hn : 1 ≤ n) (hb : 0 < b) (hk : 0 < k) :
    |(∫ u in Ioc 0 b,
        u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m)))
      - (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
          * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀
      - β * c * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + m : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀)|
      ≤ (β * c) ^ 2 / 2 * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + 2 * m : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + 2 * m + 2 * k : ℕ) : ℝ) + 1) / (2 * k)) (ξ₀ + |c| * b ^ m))
        + (∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        + |β * c| * ∫ u in Ioi b, u ^ (h + m) * (Real.sqrt n * u ^ k)
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
  have hn0 : (0 : ℝ) < n := by linarith
  -- the population kernel and the perturbation variable
  obtain ⟨pop, hpop⟩ : ∃ f : ℝ → ℝ,
      f = fun u => Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ f : ℝ → ℝ, f = fun u => β * Real.sqrt n * u ^ k * c * u ^ m := ⟨_, rfl⟩
  -- the three pieces
  obtain ⟨g₀, hg₀⟩ : ∃ g : ℝ → ℝ, g = fun u => u ^ h * pop u := ⟨_, rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g : ℝ → ℝ, g = fun u => u ^ h * pop u * x u := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g : ℝ → ℝ,
      g = fun u => u ^ h * pop u * (Real.exp (x u) - 1 - x u) := ⟨_, rfl⟩
  have hdecomp : (fun u : ℝ =>
      u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m)))
      = fun u => g₀ u + g₁ u + g₂ u := by
    funext u
    simp only [hg₀, hg₁, hg₂, hpop, hx]
    rw [show -β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m)
        = (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
          + β * Real.sqrt n * u ^ k * c * u ^ m by ring, Real.exp_add]
    ring
  have hcont_pop : Continuous pop := by rw [hpop]; fun_prop
  have hcont_x : Continuous x := by rw [hx]; fun_prop
  have hcont₀ : Continuous g₀ := by
    rw [hg₀]; exact (continuous_pow h).mul hcont_pop
  have hcont₁ : Continuous g₁ := by
    rw [hg₁]; exact ((continuous_pow h).mul hcont_pop).mul hcont_x
  have hcont₂ : Continuous g₂ := by
    rw [hg₂]
    exact ((continuous_pow h).mul hcont_pop).mul
      (((Real.continuous_exp.comp hcont_x).sub continuous_const).sub hcont_x)
  have hi₀ : IntegrableOn g₀ (Ioc 0 b) := hcont₀.integrableOn_Ioc
  have hi₁ : IntegrableOn g₁ (Ioc 0 b) := hcont₁.integrableOn_Ioc
  have hi₂ : IntegrableOn g₂ (Ioc 0 b) := hcont₂.integrableOn_Ioc
  have hi₀₁ : IntegrableOn (fun u => g₀ u + g₁ u) (Ioc 0 b) := hi₀.add hi₁
  -- zeroth-order piece: chart = half-line − tail
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
  -- first-order piece: βc · (chart insertion at p = 1) = βc · (half-line − tail)
  have hI₁ : (∫ u in Ioc 0 b, g₁ u)
      = β * c * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + m : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀
        - ∫ u in Ioi b, u ^ (h + m) * (Real.sqrt n * u ^ k)
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) := by
    have hG : (fun u : ℝ => u ^ (h + m) * (Real.sqrt n * u ^ k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        = fun u => Real.sqrt n * (u ^ (h + m + k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) := by
      funext u; rw [pow_add u (h + m)]; ring
    have hint : IntegrableOn (fun u : ℝ => u ^ (h + m) * (Real.sqrt n * u ^ k)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) (Ioi 0) := by
      rw [hG]; exact (standardIntegrand_integrableOn β n ξ₀ (h + m + k) k hβ hn0 hk).const_mul _
    have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl b)) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hb.le))
    have hins := standardIntegral1D_insertion β n ξ₀ (h + m) k 1 hn0 hk
    simp only [pow_one] at hins
    rw [Ioc_union_Ioi_eq_Ioi hb.le, hins] at hsplit
    have hg₁' : (∫ u in Ioc 0 b, g₁ u) = β * c * ∫ u in Ioc 0 b, u ^ (h + m) * (Real.sqrt n * u ^ k)
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u _
      simp only [hg₁, hpop, hx]
      rw [pow_add]; ring
    rw [hg₁']
    congr 1
    linarith
  -- second-order remainder bound
  obtain ⟨a', ha'⟩ : ∃ a : ℝ, a = ξ₀ + |c| * b ^ m := ⟨_, rfl⟩
  obtain ⟨bnd, hbnd⟩ : ∃ g : ℝ → ℝ, g = fun u => (β * c) ^ 2 / 2 * n * (u ^ (h + 2 * m + 2 * k)
    * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) := ⟨_, rfl⟩
  have hbnd_int : IntegrableOn bnd (Ioi 0) := by
    rw [hbnd]
    exact (standardIntegrand_integrableOn β n a' (h + 2 * m + 2 * k) k hβ hn0 hk).const_mul _
  have hbnd_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ bnd u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    simp only [hbnd]; positivity
  have hpt : ∀ u ∈ Ioc (0 : ℝ) b, |g₂ u| ≤ bnd u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hub : u ≤ b := hu.2
    have hR := abs_exp_sub_one_sub_self_le (x u)
    have hxabs : |x u| ≤ β * Real.sqrt n * u ^ k * |c| * b ^ m := by
      simp only [hx]
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hβ, abs_of_nonneg (Real.sqrt_nonneg n),
        abs_of_nonneg (pow_nonneg hu0.le k), abs_of_nonneg (pow_nonneg hu0.le m)]
      gcongr
    have hxsq : (x u) ^ 2 = (β * c) ^ 2 * n * (u ^ (2 * k) * u ^ (2 * m)) := by
      simp only [hx]
      rw [show β * Real.sqrt n * u ^ k * c * u ^ m
          = (β * c) * Real.sqrt n * (u ^ k * u ^ m) by ring,
        mul_pow, mul_pow, Real.sq_sqrt hn0.le]
      ring
    have hpop_pos : 0 < pop u := by simp only [hpop]; exact Real.exp_pos _
    have hkey : pop u * Real.exp |x u|
        ≤ Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a') := by
      simp only [hpop]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [ha']
      nlinarith [hxabs]
    have hupop : (0 : ℝ) ≤ u ^ h * pop u := mul_nonneg (pow_nonneg hu0.le h) hpop_pos.le
    calc |g₂ u| = u ^ h * pop u * |Real.exp (x u) - 1 - x u| := by
          simp only [hg₂]
          rw [abs_mul, abs_of_nonneg hupop]
      _ ≤ u ^ h * pop u * ((x u) ^ 2 / 2 * Real.exp |x u|) :=
          mul_le_mul_of_nonneg_left hR hupop
      _ = (x u) ^ 2 / 2 * u ^ h * (pop u * Real.exp |x u|) := by ring
      _ ≤ (x u) ^ 2 / 2 * u ^ h
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a') :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = bnd u := by
          simp only [hbnd]
          rw [hxsq]; ring
  have hI₂ : |∫ u in Ioc 0 b, g₂ u|
      ≤ (β * c) ^ 2 / 2 * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + 2 * m : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + 2 * m + 2 * k : ℕ) : ℝ) + 1) / (2 * k)) a') := by
    have hval : (∫ u in Ioi 0, bnd u)
        = (β * c) ^ 2 / 2 * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + 2 * m : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + 2 * m + 2 * k : ℕ) : ℝ) + 1) / (2 * k)) a') := by
      simp only [hbnd]
      rw [integral_const_mul, standardIntegral1D_eq_fluctuation β n a' (h + 2 * m + 2 * k) k hn0 hk]
      have hpow : n * n ^ (-((((h + 2 * m + 2 * k : ℕ) : ℝ) + 1) / (2 * k)))
          = n ^ (-((((h + 2 * m : ℕ) : ℝ) + 1) / (2 * k))) := by
        nth_rewrite 1 [show n = n ^ (1 : ℝ) from (Real.rpow_one n).symm]
        rw [← Real.rpow_add hn0]; congr 1; push_cast; field_simp; ring
      calc (β * c) ^ 2 / 2 * n * ((1 / (2 * (k : ℝ)))
            * n ^ (-((((h + 2 * m + 2 * k : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + 2 * m + 2 * k : ℕ) : ℝ) + 1) / (2 * k)) a')
          = (β * c) ^ 2 / 2 * ((1 / (2 * (k : ℝ)))
            * (n * n ^ (-((((h + 2 * m + 2 * k : ℕ) : ℝ) + 1) / (2 * k))))
            * fluctuation β ((((h + 2 * m + 2 * k : ℕ) : ℝ) + 1) / (2 * k)) a') := by ring
        _ = _ := by rw [hpow]
    calc |∫ u in Ioc 0 b, g₂ u| ≤ ∫ u in Ioc 0 b, |g₂ u| := abs_integral_le_integral_abs
      _ ≤ ∫ u in Ioc 0 b, bnd u :=
          setIntegral_mono_on hi₂.abs (hbnd_int.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hpt
      _ ≤ ∫ u in Ioi 0, bnd u := by
          apply setIntegral_mono_set hbnd_int
          · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
            exact Filter.Eventually.of_forall fun u hu => hbnd_nonneg u hu
          · exact Ioc_subset_Ioi_self.eventuallyLE
      _ = _ := hval
  -- assemble
  rw [hdecomp, integral_add hi₀₁ hi₂, integral_add hi₀ hi₁, hI₀, hI₁]
  have htail₀ : 0 ≤ ∫ u in Ioi b,
      u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (pow_nonneg (hb.trans hu).le h) (Real.exp_pos _).le
  have htail₁ : 0 ≤ ∫ u in Ioi b, u ^ (h + m) * (Real.sqrt n * u ^ k)
      * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => by
      have hu0 : (0 : ℝ) < u := hb.trans hu
      positivity
  set T₀ := ∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
  set T₁ := ∫ u in Ioi b, u ^ (h + m) * (Real.sqrt n * u ^ k)
      * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
  set I₂ := ∫ u in Ioc 0 b, g₂ u
  set A₀ := (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
    * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀
  set A₁ := (1 / (2 * (k : ℝ))) * n ^ (-((((h + m : ℕ) : ℝ) + 1) / (2 * k)))
    * fluctuation β ((((h + m : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀
  rw [show A₀ - T₀ + β * c * (A₁ - T₁) + I₂ - A₀ - β * c * A₁ = I₂ - T₀ - β * c * T₁ by ring]
  calc |I₂ - T₀ - β * c * T₁| ≤ |I₂| + |T₀| + |β * c * T₁| := by
        calc |I₂ - T₀ - β * c * T₁| ≤ |I₂ - T₀| + |β * c * T₁| := abs_sub _ _
          _ ≤ |I₂| + |T₀| + |β * c * T₁| := by gcongr; exact abs_sub _ _
    _ = |I₂| + T₀ + |β * c| * T₁ := by rw [abs_of_nonneg htail₀, abs_mul, abs_of_nonneg htail₁]
    _ ≤ _ := by rw [← ha']; gcongr

end Laplace.Grammar
