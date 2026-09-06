/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.SecondOrderAsymptotic

/-!
# The one-dimensional Taylor tree to all orders, monomial perturbation (grammar §4.2)

For `ξ(u) = ξ₀ + c u^m` and any truncation order `N`, the chart standard integral is

  `Z_chart = ∑_{p<N} (βc)^p/p! · (2k)^{-1} n^{-μ_p} S_{μ_p + p/2}(ξ₀) + (remainder)`,
  `μ_p = (h+mp+1)/(2k)`,

with the remainder bounded explicitly by
`(β|c|)^N/N! · (2k)^{-1} n^{-μ_N} S_{μ_N + N/2}(ξ₀ + |c| b^m)` plus the `N` exponentially small
boundary tails. The exponents `μ_p` are the first `N` points of the
arithmetic progression `(h+1)/(2k) + (m/(2k))ℕ ⊆ Λ(h,k)`: this is `thm:TaylorTree` /
`cor:standardintegralexp` to every order, in one dimension, with all coefficients explicit
fluctuation functions. The analytic input is a global bound
`|eˣ - ∑_{p<N} xᵖ/p!| ≤ |x|^N/N! · e^{|x|}`, proved from the exponential series. Zero
`sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- **Global Taylor remainder bound for the exponential**:
`|eˣ - ∑_{p<N} xᵖ/p!| ≤ |x|^N/N! · e^{|x|}` for every real `x` and every `N`
(generalising `abs_exp_sub_one_sub_self_le`, the case `N = 2`). -/
theorem abs_exp_sub_sum_range_le (x : ℝ) (N : ℕ) :
    |Real.exp x - ∑ p ∈ Finset.range N, x ^ p / p.factorial|
      ≤ |x| ^ N / N.factorial * Real.exp |x| := by
  have hexp : HasSum (fun p : ℕ => x ^ p / p.factorial) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have hexpa : HasSum (fun p : ℕ => |x| ^ p / p.factorial) (Real.exp |x|) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp |x|
  have hN : HasSum (fun p : ℕ => x ^ (p + N) / (p + N).factorial)
      (Real.exp x - ∑ i ∈ Finset.range N, x ^ i / (i.factorial : ℝ)) :=
    (hasSum_nat_add_iff' N).2 hexp
  have hg : HasSum (fun p : ℕ => |x| ^ N / N.factorial * (|x| ^ p / p.factorial))
      (|x| ^ N / N.factorial * Real.exp |x|) := hexpa.mul_left _
  have hterm : ∀ p : ℕ,
      |x ^ (p + N) / (p + N).factorial| ≤ |x| ^ N / N.factorial * (|x| ^ p / p.factorial) := by
    intro p
    have hfac : ((p.factorial * N.factorial : ℕ) : ℝ) ≤ ((p + N).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add p N)
    have hfpos : (0 : ℝ) < p.factorial * N.factorial := by positivity
    rw [abs_div, abs_pow, Nat.abs_cast]
    calc |x| ^ (p + N) / ((p + N).factorial : ℝ)
        ≤ |x| ^ (p + N) / ((p.factorial * N.factorial : ℕ) : ℝ) := by gcongr
      _ = |x| ^ N / N.factorial * (|x| ^ p / p.factorial) := by
          rw [pow_add]; push_cast; ring
  have hle : Real.exp x - ∑ i ∈ Finset.range N, x ^ i / (i.factorial : ℝ)
      ≤ |x| ^ N / N.factorial * Real.exp |x| :=
    hasSum_le (fun p => (le_abs_self _).trans (hterm p)) hN hg
  have hge : -(Real.exp x - ∑ i ∈ Finset.range N, x ^ i / (i.factorial : ℝ))
      ≤ |x| ^ N / N.factorial * Real.exp |x| :=
    hasSum_le (fun p => (neg_le_abs _).trans (hterm p)) hN.neg hg
  rw [abs_le]; constructor <;> linarith

/-- **The one-dimensional Taylor tree to order `N` with explicit remainder**
(grammar §4.2 `thm:TaylorTree`, `d = 1`, `ξ = ξ₀ + c u^m`): for `n ≥ 1`,

`|Z_chart - ∑_{p<N} (βc)^p/p! (2k)^{-1} n^{-μ_p} S_{μ_p+p/2}(ξ₀)|
   ≤ (β|c|)^N/N! (2k)^{-1} n^{-μ_N} S_{μ_N+N/2}(ξ₀+|c|b^m) + ∑_{p<N} (β|c|)^p/p! tail_p`,

`μ_p = (h+mp+1)/(2k)`, where `tail_p` is the boundary tail over `(b,∞)` of the `p`-th insertion
integral (exponentially small by `standardIntegral1D_tail_le`). -/
theorem standardIntegral1D_taylor_tree (β n ξ₀ c b : ℝ) (h k m N : ℕ)
    (hβ : 0 < β) (hn : 1 ≤ n) (hb : 0 < b) (hk : 0 < k) :
    |(∫ u in Ioc 0 b,
        u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m)))
      - ∑ p ∈ Finset.range N, (β * c) ^ p / p.factorial
          * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m * p : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + m * p : ℕ) : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) ξ₀)|
      ≤ (β * |c|) ^ N / N.factorial
          * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m * N : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + m * N : ℕ) : ℝ) + 1) / (2 * k) + (N : ℝ) / 2)
              (ξ₀ + |c| * b ^ m))
        + ∑ p ∈ Finset.range N, (β * |c|) ^ p / p.factorial
            * ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
              * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨pop, hpop⟩ : ∃ f : ℝ → ℝ,
      f = fun u => Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ f : ℝ → ℝ, f = fun u => β * Real.sqrt n * u ^ k * c * u ^ m := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ → ℝ, G = fun p u =>
      (β * c) ^ p / p.factorial * (u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p * pop u) := ⟨_, rfl⟩
  obtain ⟨gR, hgR⟩ : ∃ g : ℝ → ℝ, g = fun u =>
      u ^ h * pop u * (Real.exp (x u) - ∑ p ∈ Finset.range N, x u ^ p / p.factorial) := ⟨_, rfl⟩
  have hcont_pop : Continuous pop := by rw [hpop]; fun_prop
  have hcont_x : Continuous x := by rw [hx]; fun_prop
  have hGval : ∀ p u, G p u = (u ^ h * pop u) * (x u ^ p / p.factorial) := by
    intro p u
    simp only [hG, hx]
    rw [show β * Real.sqrt n * u ^ k * c * u ^ m = (β * c) * (Real.sqrt n * u ^ k) * u ^ m by ring,
      mul_pow, mul_pow, ← pow_mul, pow_add]
    ring
  -- pointwise decomposition: finite Taylor part plus remainder
  have hdecomp : (fun u : ℝ =>
      u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m)))
      = fun u => (∑ p ∈ Finset.range N, G p u) + gR u := by
    funext u
    have hexp : Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m))
        = pop u * Real.exp (x u) := by
      simp only [hpop, hx]; rw [← Real.exp_add]; congr 1; ring
    have hsum : (∑ p ∈ Finset.range N, G p u)
        = (u ^ h * pop u) * ∑ p ∈ Finset.range N, x u ^ p / p.factorial := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => hGval p u
    rw [hexp, hsum]
    simp only [hgR]
    ring
  -- continuity and integrability on the chart
  have hcontG : ∀ p, Continuous (G p) := by
    intro p
    have : G p = fun u => (β * c) ^ p / p.factorial
        * (u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p * pop u) := by simp only [hG]
    rw [this]
    exact continuous_const.mul (((continuous_pow _).mul
      ((continuous_const.mul (continuous_pow k)).pow p)).mul hcont_pop)
  have hcontR : Continuous gR := by
    rw [hgR]
    exact ((continuous_pow h).mul hcont_pop).mul ((Real.continuous_exp.comp hcont_x).sub
      (continuous_finsetSum _ fun p _ => (hcont_x.pow p).div_const _))
  have hiG : ∀ p ∈ Finset.range N, IntegrableOn (G p) (Ioc 0 b) :=
    fun p _ => (hcontG p).integrableOn_Ioc
  have hiS : IntegrableOn (fun u => ∑ p ∈ Finset.range N, G p u) (Ioc 0 b) :=
    integrable_finsetSum _ hiG
  have hiR : IntegrableOn gR (Ioc 0 b) := hcontR.integrableOn_Ioc
  -- each Taylor term: chart integral = half-line insertion value − tail
  have hterm : ∀ p ∈ Finset.range N, (∫ u in Ioc 0 b, G p u)
      = (β * c) ^ p / p.factorial
          * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m * p : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + m * p : ℕ) : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) ξ₀)
        - (β * c) ^ p / p.factorial * ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
    intro p _
    have hGp : G p = fun u => (β * c) ^ p / p.factorial * (u ^ (h + m * p)
        * (Real.sqrt n * u ^ k) ^ p
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) := by
      simp only [hG, hpop]
    have hH : (fun u : ℝ => u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        = fun u => Real.sqrt n ^ p * (u ^ (h + m * p + k * p)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) := by
      funext u; rw [mul_pow, ← pow_mul, pow_add u (h + m * p)]; ring
    have hint : IntegrableOn (fun u : ℝ => u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) (Ioi 0) := by
      rw [hH]
      exact (standardIntegrand_integrableOn β n ξ₀ (h + m * p + k * p) k hβ hn0 hk).const_mul _
    have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl b)) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hb.le))
    rw [Ioc_union_Ioi_eq_Ioi hb.le, standardIntegral1D_insertion β n ξ₀ (h + m * p) k p hn0 hk]
      at hsplit
    rw [hGp, integral_const_mul, ← mul_sub]
    congr 1
    linarith
  -- the remainder: dominated by the `N`-th insertion at the shifted argument
  obtain ⟨a', ha'⟩ : ∃ a : ℝ, a = ξ₀ + |c| * b ^ m := ⟨_, rfl⟩
  obtain ⟨bnd, hbnd⟩ : ∃ g : ℝ → ℝ, g = fun u => (β * |c|) ^ N / N.factorial
      * (u ^ (h + m * N) * (Real.sqrt n * u ^ k) ^ N
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) := ⟨_, rfl⟩
  have hbnd_int : IntegrableOn bnd (Ioi 0) := by
    have hH : (fun u : ℝ => u ^ (h + m * N) * (Real.sqrt n * u ^ k) ^ N
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a'))
        = fun u => Real.sqrt n ^ N * (u ^ (h + m * N + k * N)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) := by
      funext u; rw [mul_pow, ← pow_mul, pow_add u (h + m * N)]; ring
    have hint : IntegrableOn (fun u : ℝ => u ^ (h + m * N) * (Real.sqrt n * u ^ k) ^ N
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) (Ioi 0) := by
      rw [hH]
      exact (standardIntegrand_integrableOn β n a' (h + m * N + k * N) k hβ hn0 hk).const_mul _
    rw [hbnd]; exact hint.const_mul _
  have hbnd_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ bnd u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    simp only [hbnd]; positivity
  have hbnd_val : (∫ u in Ioi 0, bnd u)
      = (β * |c|) ^ N / N.factorial
          * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m * N : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + m * N : ℕ) : ℝ) + 1) / (2 * k) + (N : ℝ) / 2) a') := by
    simp only [hbnd]
    rw [integral_const_mul, standardIntegral1D_insertion β n a' (h + m * N) k N hn0 hk]
  have hpt : ∀ u ∈ Ioc (0 : ℝ) b, |gR u| ≤ bnd u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hub : u ≤ b := hu.2
    have hR := abs_exp_sub_sum_range_le (x u) N
    have hpop_pos : 0 < pop u := by simp only [hpop]; exact Real.exp_pos _
    have hupop : 0 ≤ u ^ h * pop u := mul_nonneg (pow_nonneg hu0.le h) hpop_pos.le
    have hxabs : |x u| = β * Real.sqrt n * u ^ k * |c| * u ^ m := by
      simp only [hx]
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hβ, abs_of_nonneg (Real.sqrt_nonneg n),
        abs_of_nonneg (pow_nonneg hu0.le k), abs_of_nonneg (pow_nonneg hu0.le m)]
    have hxle : |x u| ≤ β * Real.sqrt n * u ^ k * |c| * b ^ m := by rw [hxabs]; gcongr
    have hkey : pop u * Real.exp |x u|
        ≤ Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a') := by
      simp only [hpop]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [ha']
      nlinarith [hxle]
    have hxN : |x u| ^ N = (β * |c|) ^ N * (u ^ (m * N) * (Real.sqrt n * u ^ k) ^ N) := by
      rw [hxabs, show β * Real.sqrt n * u ^ k * |c| * u ^ m
          = (β * |c|) * (Real.sqrt n * u ^ k) * u ^ m by ring, mul_pow, mul_pow, ← pow_mul]
      ring
    calc |gR u|
        = u ^ h * pop u * |Real.exp (x u) - ∑ p ∈ Finset.range N, x u ^ p / p.factorial| := by
          simp only [hgR]; rw [abs_mul, abs_of_nonneg hupop]
      _ ≤ u ^ h * pop u * (|x u| ^ N / N.factorial * Real.exp |x u|) :=
          mul_le_mul_of_nonneg_left hR hupop
      _ = |x u| ^ N / N.factorial * u ^ h * (pop u * Real.exp |x u|) := by ring
      _ ≤ |x u| ^ N / N.factorial * u ^ h
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a') :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = bnd u := by simp only [hbnd]; rw [hxN, pow_add]; ring
  have hIR : |∫ u in Ioc 0 b, gR u|
      ≤ (β * |c|) ^ N / N.factorial
          * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m * N : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + m * N : ℕ) : ℝ) + 1) / (2 * k) + (N : ℝ) / 2) a') := by
    calc |∫ u in Ioc 0 b, gR u| ≤ ∫ u in Ioc 0 b, |gR u| := abs_integral_le_integral_abs
      _ ≤ ∫ u in Ioc 0 b, bnd u :=
          setIntegral_mono_on hiR.abs (hbnd_int.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hpt
      _ ≤ ∫ u in Ioi 0, bnd u := by
          apply setIntegral_mono_set hbnd_int
          · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
            exact Filter.Eventually.of_forall fun u hu => hbnd_nonneg u hu
          · exact Ioc_subset_Ioi_self.eventuallyLE
      _ = _ := hbnd_val
  rw [ha'] at hIR
  -- tails are nonnegative
  have htail_nonneg : ∀ p : ℕ, 0 ≤ ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
      * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := fun p =>
    setIntegral_nonneg measurableSet_Ioi fun u hu => by
      have hu0 : (0 : ℝ) < u := hb.trans hu
      positivity
  -- assemble
  rw [hdecomp, integral_add hiS hiR, integral_finsetSum _ hiG, Finset.sum_congr rfl hterm,
    Finset.sum_sub_distrib]
  have key : ∀ (SA ST IR : ℝ), SA - ST + IR - SA = IR - ST := by intros; ring
  rw [key]
  have hST : |∑ p ∈ Finset.range N, (β * c) ^ p / p.factorial
        * ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)|
      ≤ ∑ p ∈ Finset.range N, (β * |c|) ^ p / p.factorial
        * ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [abs_mul, abs_div, abs_pow, abs_mul, abs_of_pos hβ, Nat.abs_cast,
      abs_of_nonneg (htail_nonneg p)]
  calc _ ≤ |∫ u in Ioc 0 b, gR u| + |∑ p ∈ Finset.range N, (β * c) ^ p / p.factorial
        * ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)| := abs_sub _ _
    _ ≤ _ := add_le_add hIR hST

end Laplace.Grammar
