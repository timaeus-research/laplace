/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.IteratedLogExpansion

/-!
# General `(k, h)` two-dimensional reduction via weighted primitives (grammar §4.2)

Units 35–43 treated `k = (1,…,1)`. Here the two-dimensional chart integral with arbitrary
exponents `k = (k₁, k₂)`, `h = (h₁, h₂)` is reduced exactly to a one-dimensional integral against
the **weighted primitive** `F_γ(x) = ∫₀^x t^γ f(t) dt` of the quadratic kernel. With
`p_i = (h_i + 1)/k_i` (so the candidate exponents of `thm:TaylorTree` are `p_i/2`),

  `Z(n) = 1/(k₁k₂) · n^{-p₁/2} · b^{k₂(p₂ − p₁)} · ∫₀^{L} x^{p₁ − p₂ − 1} F_{p₂ − 1}(x) dx`,
  `L = √n b^{k₁ + k₂}`.

The integral converges as `L → ∞` iff `p₁ < p₂` (no logarithm), grows like `A_{p₂−1} log L` iff
`p₁ = p₂` (one logarithm), and is dominated by the other coordinate iff `p₁ > p₂`. The two tools are
the chart power substitution `∫₀^b u^h g(u^k) du = (1/k) ∫₀^{b^k} s^{(h+1)/k − 1} g(s) ds` and the
scaling `∫₀^L s^γ G(ds) ds = d^{-(γ+1)} ∫₀^{dL} x^γ G(x) dx`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- **Chart power substitution**: `∫₀^b u^h g(u^k) du = (1/k) ∫₀^{b^k} s^{(h+1)/k − 1} g(s) ds`. -/
theorem integral_Ioc_pow_mul_comp_pow (h k : ℕ) (b : ℝ) (g : ℝ → ℝ) (hk : 0 < k) (hb : 0 < b) :
    (∫ u in Ioc (0 : ℝ) b, u ^ h * g (u ^ k))
      = 1 / (k : ℝ) * ∫ s in Ioc (0 : ℝ) (b ^ k), s ^ (((h : ℝ) + 1) / k - 1) * g s := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set G : ℝ → ℝ :=
    (Ioc (0 : ℝ) (b ^ k)).indicator (fun s => 1 / (k : ℝ) * (s ^ (((h : ℝ) + 1) / k - 1) * g s))
    with hG
  have hsub := integral_comp_rpow_Ioi_of_pos (g := G) hk'
  have hR : (∫ y in Ioi (0 : ℝ), G y)
      = 1 / (k : ℝ) * ∫ s in Ioc (0 : ℝ) (b ^ k), s ^ (((h : ℝ) + 1) / k - 1) * g s := by
    rw [hG, setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 Ioc_subset_Ioi_self,
      MeasureTheory.integral_const_mul]
  have hL : ∀ x ∈ Ioi (0 : ℝ), ((k : ℝ) * x ^ ((k : ℝ) - 1)) • G (x ^ (k : ℝ))
      = (Ioc (0 : ℝ) b).indicator (fun u => u ^ h * g (u ^ k)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hxp : x ^ (k : ℝ) = x ^ k := Real.rpow_natCast x k
    have hmem : x ^ k ∈ Ioc (0 : ℝ) (b ^ k) ↔ x ∈ Ioc (0 : ℝ) b := by
      simp only [mem_Ioc]
      constructor
      · rintro ⟨_, hle⟩
        exact ⟨hx0, (pow_le_pow_iff_left₀ hx0.le hb.le hk.ne').1 hle⟩
      · rintro ⟨_, hle⟩
        exact ⟨by positivity, pow_le_pow_left₀ hx0.le hle k⟩
    rw [hxp, smul_eq_mul, hG]
    by_cases hxb : x ∈ Ioc (0 : ℝ) b
    · rw [Set.indicator_of_mem (hmem.2 hxb), Set.indicator_of_mem hxb]
      have h1 : (x ^ k : ℝ) ^ (((h : ℝ) + 1) / k - 1) = x ^ ((h : ℝ) + 1 - k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        congr 1
        field_simp
      have h2 : x ^ ((k : ℝ) - 1) * x ^ ((h : ℝ) + 1 - k) = x ^ h := by
        rw [← Real.rpow_add hx0, show (k : ℝ) - 1 + ((h : ℝ) + 1 - k) = ((h : ℕ) : ℝ) by ring,
          Real.rpow_natCast]
      calc (k : ℝ) * x ^ ((k : ℝ) - 1)
            * (1 / (k : ℝ) * ((x ^ k) ^ (((h : ℝ) + 1) / k - 1) * g (x ^ k)))
          = ((k : ℝ) * (1 / (k : ℝ))) * (x ^ ((k : ℝ) - 1) * x ^ ((h : ℝ) + 1 - k))
            * g (x ^ k) := by
            rw [h1]; ring
        _ = x ^ h * g (x ^ k) := by rw [h2, mul_one_div_cancel hk'.ne', one_mul]
    · rw [Set.indicator_of_notMem (fun hm => hxb (hmem.1 hm)), Set.indicator_of_notMem hxb,
        mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hL, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 Ioc_subset_Ioi_self, hR] at hsub
  exact hsub

/-- **Scaling with a power weight**: `∫₀^L s^γ G(ds) ds = d^{-(γ+1)} ∫₀^{dL} x^γ G(x) dx`. -/
theorem integral_Ioc_rpow_mul_comp_mul_left (γ d L : ℝ) (G : ℝ → ℝ) (hd : 0 < d) (hL : 0 ≤ L) :
    (∫ s in Ioc (0 : ℝ) L, s ^ γ * G (d * s))
      = d ^ (-(γ + 1)) * ∫ x in Ioc (0 : ℝ) (d * L), x ^ γ * G x := by
  have hdγ : d ^ γ ≠ 0 := (Real.rpow_pos_of_pos hd γ).ne'
  have hpt : ∀ s ∈ Ioc (0 : ℝ) L, s ^ γ * G (d * s) = d ^ (-γ) * ((d * s) ^ γ * G (d * s)) := by
    intro s hs
    rw [Real.mul_rpow hd.le hs.1.le, Real.rpow_neg hd.le]
    field_simp
  have hsub : (∫ s in (0 : ℝ)..L, (d * s) ^ γ * G (d * s))
      = d⁻¹ • ∫ x in (d * 0)..(d * L), x ^ γ * G x :=
    intervalIntegral.integral_comp_mul_left (fun x => x ^ γ * G x) hd.ne'
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, MeasureTheory.integral_const_mul,
    ← intervalIntegral.integral_of_le hL, hsub, mul_zero, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity), ← mul_assoc]
  congr 1
  rw [Real.rpow_neg hd.le, Real.rpow_neg hd.le, Real.rpow_add hd, Real.rpow_one, mul_inv]

/-- The standard-integral exponential is the quadratic kernel at `√n t`. -/
theorem exp_eq_quadKernel_sqrt (β a n t : ℝ) (hn : 0 ≤ n) :
    Real.exp (-β * n * t ^ 2 + β * Real.sqrt n * t * a) = quadKernel β a (Real.sqrt n * t) := by
  rw [quadKernel, mul_pow, Real.sq_sqrt hn]
  congr 1
  ring

/-- The weighted primitive `F_γ(x) = ∫₀^x t^γ f(t) dt` of the quadratic kernel. -/
noncomputable def weightedPrimitive (β a γ x : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) x, t ^ γ * quadKernel β a t

/-- The two-dimensional chart integral with general exponents `k = (k₁, k₂)`, `h = (h₁, h₂)`. -/
noncomputable def twoDGeneral (β a b n : ℝ) (h₁ h₂ k₁ k₂ : ℕ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, ∫ v in Ioc (0 : ℝ) b,
    u ^ h₁ * v ^ h₂
      * Real.exp (-β * n * (u ^ k₁ * v ^ k₂) ^ 2 + β * Real.sqrt n * (u ^ k₁ * v ^ k₂) * a)

/-- Inner integral:
`∫₀^b v^{h₂} e^{…} dv = (1/k₂) u^{h₁} (√n u^{k₁})^{-p₂} F_{p₂−1}(√n u^{k₁} b^{k₂})`. -/
theorem twoDGeneral_inner (β a b n u p₂ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hn : 0 < n) (hb : 0 < b)
    (hu : 0 < u) (hk₂ : 0 < k₂) (hp₂ : p₂ = ((h₂ : ℝ) + 1) / k₂) :
    (∫ v in Ioc (0 : ℝ) b, u ^ h₁ * v ^ h₂
        * Real.exp (-β * n * (u ^ k₁ * v ^ k₂) ^ 2 + β * Real.sqrt n * (u ^ k₁ * v ^ k₂) * a))
      = 1 / (k₂ : ℝ) * u ^ h₁ * ((Real.sqrt n * u ^ k₁) ^ (-p₂)
          * weightedPrimitive β a (p₂ - 1) (Real.sqrt n * u ^ k₁ * b ^ k₂)) := by
  have hc : 0 < Real.sqrt n * u ^ k₁ := by positivity
  set G : ℝ → ℝ := fun s => quadKernel β a (Real.sqrt n * u ^ k₁ * s) with hG
  have hpt : ∀ v : ℝ, u ^ h₁ * v ^ h₂
      * Real.exp (-β * n * (u ^ k₁ * v ^ k₂) ^ 2 + β * Real.sqrt n * (u ^ k₁ * v ^ k₂) * a)
      = u ^ h₁ * (v ^ h₂ * G (v ^ k₂)) := by
    intro v
    simp only [hG]
    rw [exp_eq_quadKernel_sqrt β a n _ hn.le,
      show Real.sqrt n * (u ^ k₁ * v ^ k₂) = Real.sqrt n * u ^ k₁ * v ^ k₂ by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc (fun v _ => hpt v), MeasureTheory.integral_const_mul,
    integral_Ioc_pow_mul_comp_pow h₂ k₂ b G hk₂ hb, ← hp₂]
  simp only [hG]
  rw [integral_Ioc_rpow_mul_comp_mul_left (p₂ - 1) _ _ (quadKernel β a) hc (by positivity),
    show p₂ - 1 + 1 = p₂ by ring]
  unfold weightedPrimitive
  ring

/-- **Exact general `(k, h)` two-dimensional reduction**:
`Z(n) = 1/(k₁k₂) · n^{-p₁/2} b^{k₂(p₂−p₁)} · ∫₀^{√n b^{k₁+k₂}} x^{p₁−p₂−1} F_{p₂−1}(x) dx`. -/
theorem twoDGeneral_eq (β a b n : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hn : 0 < n) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) :
    twoDGeneral β a b n h₁ h₂ k₁ k₂
      = 1 / ((k₁ : ℝ) * k₂)
        * (n ^ (-(((h₁ : ℝ) + 1) / k₁ / 2))
          * b ^ ((k₂ : ℝ) * (((h₂ : ℝ) + 1) / k₂ - ((h₁ : ℝ) + 1) / k₁)))
        * ∫ x in Ioc (0 : ℝ) (Real.sqrt n * b ^ (k₁ + k₂)),
            x ^ (((h₁ : ℝ) + 1) / k₁ - ((h₂ : ℝ) + 1) / k₂ - 1)
              * weightedPrimitive β a (((h₂ : ℝ) + 1) / k₂ - 1) x := by
  unfold twoDGeneral
  obtain ⟨p₁, hp₁⟩ : ∃ p : ℝ, p = ((h₁ : ℝ) + 1) / k₁ := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂⟩ : ∃ p : ℝ, p = ((h₂ : ℝ) + 1) / k₂ := ⟨_, rfl⟩
  rw [← hp₁, ← hp₂]
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  set G : ℝ → ℝ := fun s => 1 / (k₂ : ℝ) * ((Real.sqrt n * s) ^ (-p₂)
    * weightedPrimitive β a (p₂ - 1) (Real.sqrt n * s * b ^ k₂)) with hG
  have hinner : ∀ u ∈ Ioc (0 : ℝ) b, (∫ v in Ioc (0 : ℝ) b, u ^ h₁ * v ^ h₂
      * Real.exp (-β * n * (u ^ k₁ * v ^ k₂) ^ 2 + β * Real.sqrt n * (u ^ k₁ * v ^ k₂) * a))
      = u ^ h₁ * G (u ^ k₁) := by
    intro u hu
    rw [twoDGeneral_inner β a b n u p₂ h₁ h₂ k₁ k₂ hn hb hu.1 hk₂ hp₂]
    simp only [hG]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hinner,
    integral_Ioc_pow_mul_comp_pow h₁ k₁ b G hk₁ hb, ← hp₁]
  simp only [hG]
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = Real.sqrt n * b ^ k₂ := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hpt : ∀ s ∈ Ioc (0 : ℝ) (b ^ k₁), s ^ (p₁ - 1) * (1 / (k₂ : ℝ)
      * ((Real.sqrt n * s) ^ (-p₂) * weightedPrimitive β a (p₂ - 1) (Real.sqrt n * s * b ^ k₂)))
      = (1 / (k₂ : ℝ) * Real.sqrt n ^ (-p₂))
        * (s ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) (d * s)) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    rw [Real.mul_rpow hsn.le hs0.le, show Real.sqrt n * s * b ^ k₂ = d * s by rw [hd]; ring,
      show p₁ - p₂ - 1 = (p₁ - 1) + (-p₂) by ring, Real.rpow_add hs0]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, MeasureTheory.integral_const_mul,
    integral_Ioc_rpow_mul_comp_mul_left (p₁ - p₂ - 1) d (b ^ k₁) (weightedPrimitive β a (p₂ - 1))
      hd0 (by positivity),
    show d * b ^ k₁ = Real.sqrt n * b ^ (k₁ + k₂) by rw [hd, pow_add]; ring,
    show -(p₁ - p₂ - 1 + 1) = -(p₁ - p₂) by ring]
  have h1 : Real.sqrt n ^ (-p₂) * d ^ (-(p₁ - p₂))
      = Real.sqrt n ^ (-p₁) * (b ^ k₂ : ℝ) ^ (-(p₁ - p₂)) := by
    rw [hd, Real.mul_rpow hsn.le (by positivity), ← mul_assoc, ← Real.rpow_add hsn,
      show -p₂ + -(p₁ - p₂) = -p₁ by ring]
  have h2 : Real.sqrt n ^ (-p₁) = n ^ (-(p₁ / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
    congr 1
    ring
  have h3 : (b ^ k₂ : ℝ) ^ (-(p₁ - p₂)) = b ^ ((k₂ : ℝ) * (p₂ - p₁)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    congr 1
    ring
  have key : Real.sqrt n ^ (-p₂) * d ^ (-(p₁ - p₂))
      = n ^ (-(p₁ / 2)) * b ^ ((k₂ : ℝ) * (p₂ - p₁)) := by
    rw [h1, h2, h3]
  rw [← key]
  ring

end Laplace.Grammar
