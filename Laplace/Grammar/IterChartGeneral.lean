/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.IteratedDivPrim
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The `d`-fold chart integral with general `(k, h)`, all exponents equal (grammar §4.2)

For exponent vectors `k, h : ℕ → ℕ` the `d`-fold chart standard integral is defined recursively,
integrating the coordinates one at a time:

  `Z_0(c) = f(c)`,  `Z_{d+1}(c) = ∫₀^b u^{h_d} Z_d(c u^{k_d}) du`,

so that `Z_d(√n)` is the standard integral over `(0,b]^d` with the monomial `∏ u_i^{k_i}` and the
weight `∏ u_i^{h_i}`. When all candidate exponents `p_i = (h_i+1)/k_i` (`i < d`) equal `p`,

  `Z_d(c) = (∏_{i<d} k_i^{-1}) · c^{-p} · H_{d-1}(c b^{∑ k_i})`,

with `H_m = iterDivPrim (F_{p-1}) m` the iterated weighted primitives, and consequently

  `Z_d(√n) ~ (∏ k_i^{-1}) · A_{p-1}/(2^{d-1}(d-1)!) · n^{-p/2} (log n)^{d-1}`,

the multiplicity-`d` statement of `thm:TaylorTree` with arbitrary `k` and `h`. At `k = h + 1 = 1`
this is unit 39. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The `d`-fold chart integral with exponent vectors `k`, `h`, as a function of the scale `c`. -/
noncomputable def iterChartGen (β a b : ℝ) (k h : ℕ → ℕ) : ℕ → ℝ → ℝ
  | 0 => fun c => quadKernel β a c
  | d + 1 => fun c => ∫ u in Ioc (0 : ℝ) b, u ^ (h d) * iterChartGen β a b k h d (c * u ^ (k d))

theorem iterChartGen_zero (β a b : ℝ) (k h : ℕ → ℕ) (c : ℝ) :
    iterChartGen β a b k h 0 c = quadKernel β a c := rfl

theorem iterChartGen_succ (β a b : ℝ) (k h : ℕ → ℕ) (d : ℕ) (c : ℝ) :
    iterChartGen β a b k h (d + 1) c
      = ∫ u in Ioc (0 : ℝ) b, u ^ (h d) * iterChartGen β a b k h d (c * u ^ (k d)) := rfl

/-- **Exact reduction, all exponents equal**:
`Z_{d+1}(c) = (∏_{i ≤ d} k_i^{-1}) c^{-p} H_d(c b^{∑_{i ≤ d} k_i})`. -/
theorem iterChartGen_succ_eq (β a b : ℝ) (k h : ℕ → ℕ) (p : ℝ) (hb : 0 < b) (hk : ∀ i, 0 < k i)
    (d : ℕ) (hp : ∀ i, i ≤ d → ((h i : ℝ) + 1) / k i = p) (c : ℝ) (hc : 0 < c) :
    iterChartGen β a b k h (d + 1) c
      = (∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * c ^ (-p)
        * iterDivPrim (weightedPrimitive β a (p - 1)) d
            (c * b ^ (∑ i ∈ Finset.range (d + 1), k i)) := by
  induction d generalizing c with
  | zero =>
    rw [iterChartGen_succ, Finset.prod_range_one, Finset.sum_range_one, iterDivPrim_zero]
    set G : ℝ → ℝ := fun s => quadKernel β a (c * s) with hG
    have hpt : ∀ u : ℝ, u ^ (h 0) * iterChartGen β a b k h 0 (c * u ^ (k 0))
        = u ^ (h 0) * G (u ^ (k 0)) := by
      intro u; simp only [hG, iterChartGen_zero]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u _ => hpt u),
      integral_Ioc_pow_mul_comp_pow (h 0) (k 0) b G (hk 0) hb, hp 0 le_rfl]
    simp only [hG]
    rw [integral_Ioc_rpow_mul_comp_mul_left (p - 1) c _ (quadKernel β a) hc (by positivity),
      show p - 1 + 1 = p by ring]
    unfold weightedPrimitive
    ring
  | succ d ih =>
    have hp' : ∀ i, i ≤ d → ((h i : ℝ) + 1) / k i = p := fun i hi => hp i (Nat.le_succ_of_le hi)
    have hpd := hp (d + 1) le_rfl
    set K : ℝ := ∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i with hK
    set S : ℕ := ∑ i ∈ Finset.range (d + 1), k i with hS
    set H : ℝ → ℝ := iterDivPrim (weightedPrimitive β a (p - 1)) d with hH
    have hB : 0 < c * b ^ S := by positivity
    set G : ℝ → ℝ := fun s => s ^ (-p) * H (c * b ^ S * s) with hG
    have hpt : ∀ u ∈ Ioc (0 : ℝ) b,
        u ^ (h (d + 1)) * iterChartGen β a b k h (d + 1) (c * u ^ (k (d + 1)))
          = (K * c ^ (-p)) * (u ^ (h (d + 1)) * G (u ^ (k (d + 1)))) := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu.1
      rw [ih hp' (c * u ^ (k (d + 1))) (by positivity)]
      simp only [hG, hH, hK, hS]
      rw [Real.mul_rpow hc.le (by positivity),
        show c * u ^ (k (d + 1)) * b ^ S = c * b ^ S * u ^ (k (d + 1)) by ring]
      ring
    rw [iterChartGen_succ, setIntegral_congr_fun measurableSet_Ioc hpt,
      MeasureTheory.integral_const_mul,
      integral_Ioc_pow_mul_comp_pow (h (d + 1)) (k (d + 1)) b G (hk (d + 1)) hb, hpd]
    simp only [hG]
    have hpt2 : ∀ s ∈ Ioc (0 : ℝ) (b ^ (k (d + 1))), s ^ (p - 1) * (s ^ (-p) * H (c * b ^ S * s))
        = s ^ (-1 : ℝ) * H (c * b ^ S * s) := by
      intro s hs
      rw [← mul_assoc, ← Real.rpow_add hs.1, show p - 1 + -p = -1 by ring]
    rw [setIntegral_congr_fun measurableSet_Ioc hpt2,
      integral_Ioc_rpow_mul_comp_mul_left (-1) (c * b ^ S) _ H hB (by positivity),
      show -((-1 : ℝ) + 1) = 0 by norm_num, Real.rpow_zero, one_mul]
    have hint : (∫ x in Ioc (0 : ℝ) (c * b ^ S * b ^ (k (d + 1))), x ^ (-1 : ℝ) * H x)
        = iterDivPrim (weightedPrimitive β a (p - 1)) (d + 1)
            (c * b ^ (∑ i ∈ Finset.range (d + 1 + 1), k i)) := by
      rw [iterDivPrim_succ, Finset.sum_range_succ, ← hS, pow_add, ← mul_assoc]
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      rw [Real.rpow_neg hx.1.le, Real.rpow_one, inv_mul_eq_div, hH]
    rw [hint, Finset.prod_range_succ, ← hK]
    ring

/-- `log^i L = o(log^m L)` for `i < m`. -/
theorem isLittleO_log_pow_log_pow {i m : ℕ} (him : i < m) :
    (fun L : ℝ => Real.log L ^ i) =o[atTop] fun L : ℝ => Real.log L ^ m :=
  (isLittleO_pow_pow_atTop_of_lt him).comp_tendsto Real.tendsto_log_atTop

/-- **Leading asymptotic of the iterated primitives of a general base**:
`H_m(L) ~ (A/m!) log^m L` for `m ≥ 1`. -/
theorem iterDivPrim_isEquivalent {G : ℝ → ℝ} {A M C δ ε : ℝ} (hG : LogBase G A M C δ ε) (hA : 0 < A)
    (m : ℕ) (hm : 0 < m) :
    (fun L : ℝ => iterDivPrim G m L) ~[atTop]
      fun L : ℝ => A / (m.factorial : ℝ) * Real.log L ^ m := by
  have hε := hG.ε_pos
  have hM : 0 ≤ M := by
    have := hG.tail 1 le_rfl
    rw [Real.one_rpow, mul_one] at this
    exact (abs_nonneg _).trans this
  have hMε : 0 ≤ M / ε ^ m := by positivity
  apply IsLittleO.isEquivalent
  have hdecomp : ∀ L : ℝ, iterDivPrim G m L - A / (m.factorial : ℝ) * Real.log L ^ m
      = (∑ i ∈ Finset.range m, divCoeff G A m i * Real.log L ^ i) + divRem G A m L := by
    intro L
    rw [divRem, Finset.sum_range_succ, divCoeff_top]
    ring
  have hsum : (fun L : ℝ => ∑ i ∈ Finset.range m, divCoeff G A m i * Real.log L ^ i)
      =o[atTop] fun L : ℝ => Real.log L ^ m := by
    have h := IsLittleO.sum (l := atTop)
      (A := fun i => fun L : ℝ => divCoeff G A m i * Real.log L ^ i)
      (g' := fun L : ℝ => Real.log L ^ m) (s := Finset.range m)
      (fun i hi => (isLittleO_log_pow_log_pow (Finset.mem_range.1 hi)).const_mul_left _)
    refine h.congr_left fun L => ?_
    simp [Finset.sum_apply]
  have hθ : (fun L : ℝ => divRem G A m L) =o[atTop] fun L : ℝ => Real.log L ^ m := by
    have h1 : (fun L : ℝ => divRem G A m L) =O[atTop] fun _ : ℝ => (1 : ℝ) := by
      apply IsBigO.of_bound (M / ε ^ m)
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
      rw [Real.norm_eq_abs, norm_one, mul_one]
      refine (divRem_abs_le hG m L hL).trans ?_
      calc M / ε ^ m * L ^ (-ε) ≤ M / ε ^ m * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)) hMε
        _ = M / ε ^ m := mul_one _
    have h2 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun L : ℝ => Real.log L ^ m := by
      refine isLittleO_const_left.2 (Or.inr ?_)
      have : Tendsto (fun L : ℝ => Real.log L ^ m) atTop atTop :=
        (tendsto_pow_atTop hm.ne').comp Real.tendsto_log_atTop
      simpa [Function.comp_def, Real.norm_eq_abs] using tendsto_abs_atTop_atTop.comp this
    exact h1.trans_isLittleO h2
  have hA0 : A / (m.factorial : ℝ) ≠ 0 := (div_pos hA (by positivity)).ne'
  refine ((hsum.add hθ).congr_left fun L => (hdecomp L).symm).const_mul_right hA0

/-- **The general multiplicity theorem, all-equal case, arbitrary `(k, h)`**
(grammar §4.2 `thm:TaylorTree`, `d + 2` coordinates all with candidate exponent `p/2`):
`Z_{d+2}(√n) ~ (∏ k_i^{-1}) · A_{p-1}/(2^{d+1}(d+1)!) · n^{-p/2} (log n)^{d+1}`. -/
theorem iterChartGen_isEquivalent (β a b : ℝ) (k h : ℕ → ℕ) (p : ℝ) (hβ : 0 < β) (hb : 0 < b)
    (hk : ∀ i, 0 < k i) (d : ℕ) (hp : ∀ i, i ≤ d + 1 → ((h i : ℝ) + 1) / k i = p) :
    (fun n : ℝ => iterChartGen β a b k h (d + 2) (Real.sqrt n)) ~[atTop]
      fun n : ℝ => (∏ i ∈ Finset.range (d + 2), (1 : ℝ) / k i)
        * (weightedMass β a (p - 1) / (2 ^ (d + 1) * ((d + 1).factorial : ℝ)))
        * (n ^ (-(p / 2)) * Real.log n ^ (d + 1)) := by
  have hp0 : 0 < p := by
    rw [← hp 0 (Nat.zero_le _)]
    have := hk 0
    positivity
  have hγ : -1 < p - 1 := by linarith
  have hG := weightedPrimitive_logBase β a (p - 1) hβ hγ
  have hA : 0 < weightedMass β a (p - 1) := weightedMass_pos β a (p - 1) hβ hγ
  set A := weightedMass β a (p - 1) with hAdef
  set K : ℝ := ∏ i ∈ Finset.range (d + 2), (1 : ℝ) / k i with hK
  set S : ℕ := ∑ i ∈ Finset.range (d + 2), k i with hS
  have hZ : ∀ n : ℝ, 0 < n → iterChartGen β a b k h (d + 2) (Real.sqrt n)
      = K * (Real.sqrt n) ^ (-p) * iterDivPrim (weightedPrimitive β a (p - 1)) (d + 1)
          (Real.sqrt n * b ^ S) := fun n hn =>
    iterChartGen_succ_eq β a b k h p hb hk (d + 1) hp (Real.sqrt n) (Real.sqrt_pos.2 hn)
  have hLtend : Tendsto (fun n : ℝ => Real.sqrt n * b ^ S) atTop atTop :=
    tendsto_sqrt_atTop.atTop_mul_const (pow_pos hb _)
  have h2 := (iterDivPrim_isEquivalent hG hA (d + 1) (Nat.succ_pos d)).comp_tendsto hLtend
  have h3 := (log_sqrt_mul_pow_isEquivalent b hb S).pow (d + 1)
  have h4 : (fun n : ℝ => iterDivPrim (weightedPrimitive β a (p - 1)) (d + 1) (Real.sqrt n * b ^ S))
      ~[atTop] fun n : ℝ => A / ((d + 1).factorial : ℝ) * ((1 / 2 : ℝ) * Real.log n) ^ (d + 1) := by
    refine h2.trans ?_
    have := (IsEquivalent.refl (u := fun _ : ℝ => A / ((d + 1).factorial : ℝ)) (l := atTop)).mul h3
    exact this
  have h5 := (IsEquivalent.refl (u := fun n : ℝ => K * (Real.sqrt n) ^ (-p)) (l := atTop)).mul h4
  refine (h5.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    simp only [Pi.mul_apply]
    rw [hZ n hn]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    simp only [Pi.mul_apply]
    have hpow : (Real.sqrt n) ^ (-p) = n ^ (-(p / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
      congr 1
      ring
    rw [hpow, mul_pow, div_pow, one_pow]
    field_simp

end Laplace.Grammar
