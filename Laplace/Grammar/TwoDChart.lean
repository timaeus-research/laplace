/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDSecondOrder

/-!
# The `d = 2` theorem for the chart amplitude `η e^{βsξ}` (grammar §4.2)

The amplitude-level hypotheses of unit 88 (axis Lipschitz bounds and the mixed second difference)
are derived for `Φ(u,v,s) = η(u,v) e^{βsξ(u,v)}` from Lipschitz and mixed-difference bounds on
`ξ, η` themselves (which hold for `C²` functions): `amp_sub_le`, `amp_mixed_le`. Consequently the
two-dimensional chart integral with equal exponents satisfies

  `Z(N) = N^{-p} (A log N + B) + O(N^{-(p+δ)} (1 + log N))`,  `A = (k₁k₂)⁻¹ η(0,0) S_p(ξ(0,0))`

(`twoDChart_second_order`, `twoDChart_A`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- `|η₁ e^{βsξ₁} − η₂ e^{βsξ₂}| ≤ (|η₁−η₂| + M βs |ξ₁−ξ₂|) e^{βsL}` for `|ξᵢ| ≤ L`, `|η₂| ≤ M`. -/
theorem amp_sub_le (β L M ξ₁ ξ₂ η₁ η₂ s : ℝ) (hβ : 0 < β) (hs : 0 ≤ s) (hξ₁ : |ξ₁| ≤ L)
    (hξ₂ : |ξ₂| ≤ L) (hη₂ : |η₂| ≤ M) :
    |η₁ * Real.exp (β * s * ξ₁) - η₂ * Real.exp (β * s * ξ₂)|
      ≤ (|η₁ - η₂| + M * (β * s) * |ξ₁ - ξ₂|) * Real.exp (β * s * L) := by
  have hbs : 0 ≤ β * s := by positivity
  have hE₁ : Real.exp (β * s * ξ₁) ≤ Real.exp (β * s * L) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hξ₁) hbs)
  have hE₂ : Real.exp (β * s * ξ₂) ≤ Real.exp (β * s * L) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hξ₂) hbs)
  have hdiff : |Real.exp (β * s * ξ₁) - Real.exp (β * s * ξ₂)|
      ≤ β * s * |ξ₁ - ξ₂| * Real.exp (β * s * L) := by
    calc |Real.exp (β * s * ξ₁) - Real.exp (β * s * ξ₂)|
        ≤ |β * s * ξ₁ - β * s * ξ₂| * Real.exp (max (β * s * ξ₁) (β * s * ξ₂)) :=
          abs_exp_sub_exp_le _ _
      _ = β * s * |ξ₁ - ξ₂| * Real.exp (max (β * s * ξ₁) (β * s * ξ₂)) := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hbs]
      _ ≤ β * s * |ξ₁ - ξ₂| * Real.exp (β * s * L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (max_le ?_ ?_)) (by positivity)
          · exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hξ₁) hbs
          · exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hξ₂) hbs
  have hsplit : η₁ * Real.exp (β * s * ξ₁) - η₂ * Real.exp (β * s * ξ₂)
      = (η₁ - η₂) * Real.exp (β * s * ξ₁)
        + η₂ * (Real.exp (β * s * ξ₁) - Real.exp (β * s * ξ₂)) := by ring
  have hM : 0 ≤ M := (abs_nonneg _).trans hη₂
  rw [hsplit]
  calc |(η₁ - η₂) * Real.exp (β * s * ξ₁) + η₂ * (Real.exp (β * s * ξ₁) - Real.exp (β * s * ξ₂))|
      ≤ |η₁ - η₂| * Real.exp (β * s * ξ₁)
          + |η₂| * |Real.exp (β * s * ξ₁) - Real.exp (β * s * ξ₂)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ |η₁ - η₂| * Real.exp (β * s * L) + M * (β * s * |ξ₁ - ξ₂| * Real.exp (β * s * L)) := by
        gcongr
    _ = _ := by ring

/-- The rectangle difference of a product. -/
theorem rect_diff_mul (f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃ : ℝ) :
    f₃ * g₃ - f₁ * g₁ - f₂ * g₂ + f₀ * g₀
      = (f₃ - f₁ - f₂ + f₀) * g₃ + (f₁ - f₀) * (g₃ - g₁) + (f₂ - f₀) * (g₃ - g₂)
        + f₀ * (g₃ - g₁ - g₂ + g₀) := by ring

/-- **Mixed second difference of the exponential factor**: with `Eᵢ = e^{βs aᵢ}`,
`|E₃ − E₁ − E₂ + E₀| ≤ (β² s² K² uv + βs K uv) e^{5βLs}` under the Lipschitz/mixed bounds on `a`. -/
theorem exp_rect_diff_le (β L K u v s a₀ a₁ a₂ a₃ : ℝ) (hβ : 0 < β) (hs : 0 ≤ s) (hL : 0 ≤ L)
    (hK : 0 ≤ K) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h₀ : |a₀| ≤ L) (h₁ : |a₁| ≤ L) (h₂ : |a₂| ≤ L) (h₃ : |a₃| ≤ L)
    (h₁₀ : |a₁ - a₀| ≤ K * u) (h₂₀ : |a₂ - a₀| ≤ K * v)
    (hD : |a₃ - a₁ - a₂ + a₀| ≤ K * (u * v)) :
    |Real.exp (β * s * a₃) - Real.exp (β * s * a₁) - Real.exp (β * s * a₂) + Real.exp (β * s * a₀)|
      ≤ (β ^ 2 * s ^ 2 * K ^ 2 * (u * v) + β * s * K * (u * v)) * Real.exp (5 * β * L * s) := by
  have hbs : 0 ≤ β * s := by positivity
  set t₁ : ℝ := β * s * (a₁ - a₀) with ht₁
  set t₂ : ℝ := β * s * (a₂ - a₀) with ht₂
  set t₃ : ℝ := β * s * (a₃ - a₀) with ht₃
  set E₀ : ℝ := Real.exp (β * s * a₀) with hE₀
  have hE₀L : E₀ ≤ Real.exp (β * s * L) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans h₀) hbs)
  have hEi : ∀ i, |Real.exp (β * s * i) - E₀| = E₀ * |Real.exp (β * s * (i - a₀)) - 1| := by
    intro i
    rw [hE₀, show β * s * i = β * s * a₀ + β * s * (i - a₀) by ring, Real.exp_add, ← mul_sub_one,
      abs_mul, abs_of_pos (Real.exp_pos _)]
  -- the key identity
  have hid : Real.exp (β * s * a₃) - Real.exp (β * s * a₁) - Real.exp (β * s * a₂)
      + Real.exp (β * s * a₀)
      = E₀ * ((Real.exp t₁ - 1) * (Real.exp t₂ - 1) + (Real.exp t₃ - Real.exp (t₁ + t₂))) := by
    have e1 : Real.exp (β * s * a₁) = E₀ * Real.exp t₁ := by
      rw [hE₀, ht₁, ← Real.exp_add]; ring_nf
    have e2 : Real.exp (β * s * a₂) = E₀ * Real.exp t₂ := by
      rw [hE₀, ht₂, ← Real.exp_add]; ring_nf
    have e3 : Real.exp (β * s * a₃) = E₀ * Real.exp t₃ := by
      rw [hE₀, ht₃, ← Real.exp_add]; ring_nf
    rw [e1, e2, e3, Real.exp_add]; ring
  -- bounds on the `tᵢ`
  have ht₁b : |t₁| ≤ β * s * (K * u) := by
    rw [ht₁, abs_mul, abs_of_nonneg hbs]; exact mul_le_mul_of_nonneg_left h₁₀ hbs
  have ht₂b : |t₂| ≤ β * s * (K * v) := by
    rw [ht₂, abs_mul, abs_of_nonneg hbs]; exact mul_le_mul_of_nonneg_left h₂₀ hbs
  have hDb : |t₃ - (t₁ + t₂)| ≤ β * s * (K * (u * v)) := by
    rw [ht₁, ht₂, ht₃, show β * s * (a₃ - a₀) - (β * s * (a₁ - a₀) + β * s * (a₂ - a₀))
      = β * s * (a₃ - a₁ - a₂ + a₀) by ring, abs_mul, abs_of_nonneg hbs]
    exact mul_le_mul_of_nonneg_left hD hbs
  have hti : ∀ i, |i| ≤ L → |β * s * (i - a₀)| ≤ β * s * (2 * L) := by
    intro i hi
    rw [abs_mul, abs_of_nonneg hbs]
    refine mul_le_mul_of_nonneg_left ?_ hbs
    calc |i - a₀| ≤ |i| + |a₀| := abs_sub _ _
      _ ≤ L + L := add_le_add hi h₀
      _ = 2 * L := by ring
  have ht₁L : |t₁| ≤ β * s * (2 * L) := hti a₁ h₁
  have ht₂L : |t₂| ≤ β * s * (2 * L) := hti a₂ h₂
  have ht₃L : |t₃| ≤ β * s * (2 * L) := hti a₃ h₃
  -- first product
  have hP : |(Real.exp t₁ - 1) * (Real.exp t₂ - 1)|
      ≤ (β * s * (K * u)) * (β * s * (K * v)) * Real.exp (4 * β * L * s) := by
    rw [abs_mul]
    have h1 := abs_exp_sub_one_le' t₁
    have h2 := abs_exp_sub_one_le' t₂
    have hex : Real.exp |t₁| * Real.exp |t₂| ≤ Real.exp (4 * β * L * s) := by
      rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_; linarith
    calc |Real.exp t₁ - 1| * |Real.exp t₂ - 1|
        ≤ (|t₁| * Real.exp |t₁|) * (|t₂| * Real.exp |t₂|) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = (|t₁| * |t₂|) * (Real.exp |t₁| * Real.exp |t₂|) := by ring
      _ ≤ (β * s * (K * u)) * (β * s * (K * v)) * Real.exp (4 * β * L * s) := by
          gcongr
  -- second difference
  have hQ : |Real.exp t₃ - Real.exp (t₁ + t₂)|
      ≤ β * s * (K * (u * v)) * Real.exp (4 * β * L * s) := by
    calc |Real.exp t₃ - Real.exp (t₁ + t₂)|
        ≤ |t₃ - (t₁ + t₂)| * Real.exp (max t₃ (t₁ + t₂)) := abs_exp_sub_exp_le _ _
      _ ≤ β * s * (K * (u * v)) * Real.exp (4 * β * L * s) := by
          have hbsL : 0 ≤ β * s * L := mul_nonneg hbs hL
          refine mul_le_mul hDb (Real.exp_le_exp.2 (max_le ?_ ?_)) (Real.exp_pos _).le
            (by positivity)
          · have := le_abs_self t₃; linarith
          · have := le_abs_self t₁; have := le_abs_self t₂; linarith
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hE0 : 0 ≤ E₀ := (Real.exp_pos _).le
  have hsum := (abs_add_le _ _).trans (add_le_add hP hQ)
  calc E₀ * |(Real.exp t₁ - 1) * (Real.exp t₂ - 1) + (Real.exp t₃ - Real.exp (t₁ + t₂))|
      ≤ Real.exp (β * s * L) * ((β * s * (K * u)) * (β * s * (K * v)) * Real.exp (4 * β * L * s)
          + β * s * (K * (u * v)) * Real.exp (4 * β * L * s)) :=
        mul_le_mul hE₀L hsum (abs_nonneg _) (Real.exp_pos _).le
    _ = (β ^ 2 * s ^ 2 * K ^ 2 * (u * v) + β * s * K * (u * v))
          * (Real.exp (β * s * L) * Real.exp (4 * β * L * s)) := by ring
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-- **Mixed second difference of the chart amplitude**. -/
theorem amp_mixed_le (β L K M u v s a₀ a₁ a₂ a₃ e₀ e₁ e₂ e₃ : ℝ) (hβ : 0 < β) (hs : 0 ≤ s)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hM : 0 ≤ M) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h₀ : |a₀| ≤ L) (h₁ : |a₁| ≤ L) (h₂ : |a₂| ≤ L) (h₃ : |a₃| ≤ L)
    (h₁₀ : |a₁ - a₀| ≤ K * u) (h₂₀ : |a₂ - a₀| ≤ K * v) (h₃₁ : |a₃ - a₁| ≤ K * v)
    (h₃₂ : |a₃ - a₂| ≤ K * u) (hD : |a₃ - a₁ - a₂ + a₀| ≤ K * (u * v))
    (he₀ : |e₀| ≤ M) (he₁₀ : |e₁ - e₀| ≤ K * u) (he₂₀ : |e₂ - e₀| ≤ K * v)
    (heD : |e₃ - e₁ - e₂ + e₀| ≤ K * (u * v)) :
    |e₃ * Real.exp (β * s * a₃) - e₁ * Real.exp (β * s * a₁) - e₂ * Real.exp (β * s * a₂)
        + e₀ * Real.exp (β * s * a₀)|
      ≤ (K + 2 * K ^ 2 * β + M * β ^ 2 * K ^ 2 + M * β * K) * (u * v) * ((1 + s) ^ 2
        * Real.exp (5 * β * L * s)) := by
  have hbs : 0 ≤ β * s := by positivity
  set E : ℝ → ℝ := fun a => Real.exp (β * s * a) with hE
  have hEL : ∀ a, |a| ≤ L → E a ≤ Real.exp (β * s * L) := fun a ha =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans ha) hbs)
  have hE5 : Real.exp (β * s * L) ≤ Real.exp (5 * β * L * s) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hEdiff : ∀ a a', |a| ≤ L → |a'| ≤ L →
      |E a - E a'| ≤ β * s * |a - a'| * Real.exp (β * s * L) := by
    intro a a' ha ha'
    calc |E a - E a'| ≤ |β * s * a - β * s * a'| * Real.exp (max (β * s * a) (β * s * a')) :=
          abs_exp_sub_exp_le _ _
      _ = β * s * |a - a'| * Real.exp (max (β * s * a) (β * s * a')) := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hbs]
      _ ≤ β * s * |a - a'| * Real.exp (β * s * L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (max_le ?_ ?_)) (by positivity)
          · exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans ha) hbs
          · exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans ha') hbs
  rw [rect_diff_mul e₀ e₁ e₂ e₃ (E a₀) (E a₁) (E a₂) (E a₃)]
  have hT1 : |(e₃ - e₁ - e₂ + e₀) * E a₃| ≤ K * (u * v) * Real.exp (β * s * L) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul heD (hEL a₃ h₃) (Real.exp_pos _).le (by positivity)
  have hT2 : |(e₁ - e₀) * (E a₃ - E a₁)|
      ≤ K * u * (β * s * (K * v) * Real.exp (β * s * L)) := by
    rw [abs_mul]
    refine mul_le_mul he₁₀ ((hEdiff a₃ a₁ h₃ h₁).trans ?_) (abs_nonneg _) (by positivity)
    gcongr
  have hT3 : |(e₂ - e₀) * (E a₃ - E a₂)|
      ≤ K * v * (β * s * (K * u) * Real.exp (β * s * L)) := by
    rw [abs_mul]
    refine mul_le_mul he₂₀ ((hEdiff a₃ a₂ h₃ h₂).trans ?_) (abs_nonneg _) (by positivity)
    gcongr
  have hT4 : |e₀ * (E a₃ - E a₁ - E a₂ + E a₀)|
      ≤ M * ((β ^ 2 * s ^ 2 * K ^ 2 * (u * v) + β * s * K * (u * v))
          * Real.exp (5 * β * L * s)) := by
    rw [abs_mul]
    exact mul_le_mul he₀ (exp_rect_diff_le β L K u v s a₀ a₁ a₂ a₃ hβ hs hL hK hu hv h₀ h₁ h₂ h₃
      h₁₀ h₂₀ hD) (abs_nonneg _) hM
  have hsum := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add hT1 hT2)) hT3)) hT4)
  refine hsum.trans ?_
  -- collect: everything is `uv · e^{5βLs} · (polynomial in s)`
  have hs1 : 1 ≤ (1 + s) ^ 2 := one_le_pow₀ (by linarith)
  have hs2 : s ≤ (1 + s) ^ 2 := by
    calc s ≤ 1 + s := by linarith
      _ ≤ (1 + s) ^ 2 := le_self_pow₀ (by linarith) two_ne_zero
  have hs3 : s ^ 2 ≤ (1 + s) ^ 2 := pow_le_pow_left₀ hs (by linarith) 2
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have hE5' : 0 ≤ Real.exp (5 * β * L * s) := (Real.exp_pos _).le
  have hA : K * (u * v) * Real.exp (β * s * L)
      ≤ K * (u * v) * ((1 + s) ^ 2 * Real.exp (5 * β * L * s)) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK huv)
    calc Real.exp (β * s * L) ≤ Real.exp (5 * β * L * s) := hE5
      _ = 1 * Real.exp (5 * β * L * s) := (one_mul _).symm
      _ ≤ (1 + s) ^ 2 * Real.exp (5 * β * L * s) := mul_le_mul_of_nonneg_right hs1 hE5'
  have hB : K * u * (β * s * (K * v) * Real.exp (β * s * L))
      ≤ K ^ 2 * β * (u * v) * ((1 + s) ^ 2 * Real.exp (5 * β * L * s)) := by
    have : K * u * (β * s * (K * v) * Real.exp (β * s * L))
        = K ^ 2 * β * (u * v) * (s * Real.exp (β * s * L)) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hs2 hE5 (Real.exp_pos _).le (by positivity)
  have hC : K * v * (β * s * (K * u) * Real.exp (β * s * L))
      ≤ K ^ 2 * β * (u * v) * ((1 + s) ^ 2 * Real.exp (5 * β * L * s)) := by
    have : K * v * (β * s * (K * u) * Real.exp (β * s * L))
        = K ^ 2 * β * (u * v) * (s * Real.exp (β * s * L)) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hs2 hE5 (Real.exp_pos _).le (by positivity)
  have hD' : M * ((β ^ 2 * s ^ 2 * K ^ 2 * (u * v) + β * s * K * (u * v))
        * Real.exp (5 * β * L * s))
      ≤ (M * β ^ 2 * K ^ 2 + M * β * K) * (u * v) * ((1 + s) ^ 2 * Real.exp (5 * β * L * s)) := by
    have : M * ((β ^ 2 * s ^ 2 * K ^ 2 * (u * v) + β * s * K * (u * v)) * Real.exp (5 * β * L * s))
        = (M * β ^ 2 * K ^ 2 * s ^ 2 + M * β * K * s) * ((u * v) * Real.exp (5 * β * L * s)) := by
      ring
    rw [this]
    have c1 : 0 ≤ M * β ^ 2 * K ^ 2 := by positivity
    have c2 : 0 ≤ M * β * K := by positivity
    have e1 : M * β ^ 2 * K ^ 2 * s ^ 2 ≤ M * β ^ 2 * K ^ 2 * (1 + s) ^ 2 :=
      mul_le_mul_of_nonneg_left hs3 c1
    have e2 : M * β * K * s ≤ M * β * K * (1 + s) ^ 2 := mul_le_mul_of_nonneg_left hs2 c2
    calc (M * β ^ 2 * K ^ 2 * s ^ 2 + M * β * K * s) * ((u * v) * Real.exp (5 * β * L * s))
        ≤ (M * β ^ 2 * K ^ 2 * (1 + s) ^ 2 + M * β * K * (1 + s) ^ 2)
          * ((u * v) * Real.exp (5 * β * L * s)) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg huv hE5')
      _ = _ := by ring
  linarith

/-- The chart amplitude `Φ(u,v,s) = η(u,v) e^{βsξ(u,v)}`. -/
noncomputable def chartAmp (β : ℝ) (ξ η : ℝ → ℝ → ℝ) (u v s : ℝ) : ℝ :=
  η u v * Real.exp (β * s * ξ u v)

/-- `e^{βsL} ≤ e^{βs(5L)}` for `s, L ≥ 0`. -/
theorem exp_le_exp_five (β s L : ℝ) (hβ : 0 < β) (hs : 0 ≤ s) (hL : 0 ≤ L) :
    Real.exp (β * s * L) ≤ Real.exp (β * s * (5 * L)) := by
  refine Real.exp_le_exp.2 ?_
  have : 0 ≤ β * s * L := mul_nonneg (mul_nonneg hβ.le hs) hL
  nlinarith

/-- **The `d = 2` theorem for the chart amplitude**: under Lipschitz and mixed-difference bounds on
`ξ, η` (satisfied by `C²` functions), `Z(N) = N^{-p}(A log N + B) + O(N^{-(p+δ)}(1 + log N))`. -/
theorem twoDChart_second_order (β b L K M p : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (ξ η : ℝ → ℝ → ℝ)
    (hβ : 0 < β) (hb : 0 < b) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hL : 0 ≤ L) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hξc : Continuous (Function.uncurry ξ)) (hηc : Continuous (Function.uncurry η))
    (hξL : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, |ξ u v| ≤ L)
    (hηM : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, |η u v| ≤ M)
    (hξu : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, |ξ u v - ξ 0 v| ≤ K * u)
    (hξv : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, |ξ u v - ξ u 0| ≤ K * v)
    (hηu : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, |η u v - η 0 v| ≤ K * u)
    (hηv : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, |η u v - η u 0| ≤ K * v)
    (hξD : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, |ξ u v - ξ u 0 - ξ 0 v + ξ 0 0| ≤ K * (u * v))
    (hηD : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b,
      |η u v - η u 0 - η 0 v + η 0 0| ≤ K * (u * v)) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (chartAmp β ξ η)
        - N ^ (-p) * (twoDA β p k₁ k₂ (chartAmp β ξ η) * Real.log N
          + twoDB β b p k₁ k₂ (chartAmp β ξ η))) =O[atTop]
      fun N : ℝ => N ^ (-(p + min (k₁ : ℝ)⁻¹ (k₂ : ℝ)⁻¹)) * (1 + Real.log N) := by
  have h0b : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  -- continuity of the amplitude
  have hΦ : Continuous fun x : ℝ × ℝ × ℝ => chartAmp β ξ η x.1 x.2.1 x.2.2 := by
    unfold chartAmp
    have h1 : Continuous fun x : ℝ × ℝ × ℝ => η x.1 x.2.1 :=
      hηc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have h2 : Continuous fun x : ℝ × ℝ × ℝ => ξ x.1 x.2.1 :=
      hξc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    exact h1.mul (Real.continuous_exp.comp ((continuous_const.mul
      (continuous_snd.comp continuous_snd)).mul h2))
  -- axis Lipschitz bounds
  have hlipA : ∀ u ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s → |chartAmp β ξ η u 0 s - chartAmp β ξ η 0 0 s|
      ≤ K * (1 + M * β) * u * ((1 + s) * Real.exp (β * s * (5 * L))) := by
    intro u hu s hs
    unfold chartAmp
    have h := amp_sub_le β L M (ξ u 0) (ξ 0 0) (η u 0) (η 0 0) s hβ hs (hξL u hu 0 h0b)
      (hξL 0 h0b 0 h0b) (hηM 0 h0b 0 h0b)
    refine h.trans ?_
    have e1 := hηu u hu 0 h0b
    have e2 := hξu u hu 0 h0b
    have hbs : 0 ≤ β * s := by positivity
    have hE := exp_le_exp_five β s L hβ hs hL
    have hu0 : 0 ≤ u := hu.1
    calc (|η u 0 - η 0 0| + M * (β * s) * |ξ u 0 - ξ 0 0|) * Real.exp (β * s * L)
        ≤ (K * u + M * (β * s) * (K * u)) * Real.exp (β * s * L) := by gcongr
      _ ≤ (K * u + M * (β * s) * (K * u)) * Real.exp (β * s * (5 * L)) := by
          gcongr
      _ = K * u * (1 + M * β * s) * Real.exp (β * s * (5 * L)) := by ring
      _ ≤ K * u * ((1 + M * β) * (1 + s)) * Real.exp (β * s * (5 * L)) := by
          gcongr
          nlinarith [mul_nonneg hM hβ.le]
      _ = _ := by ring
  have hlipB : ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s → |chartAmp β ξ η 0 v s - chartAmp β ξ η 0 0 s|
      ≤ K * (1 + M * β) * v * ((1 + s) * Real.exp (β * s * (5 * L))) := by
    intro v hv s hs
    unfold chartAmp
    have h := amp_sub_le β L M (ξ 0 v) (ξ 0 0) (η 0 v) (η 0 0) s hβ hs (hξL 0 h0b v hv)
      (hξL 0 h0b 0 h0b) (hηM 0 h0b 0 h0b)
    refine h.trans ?_
    have e1 := hηv 0 h0b v hv
    have e2 := hξv 0 h0b v hv
    have hbs : 0 ≤ β * s := by positivity
    have hE := exp_le_exp_five β s L hβ hs hL
    have hv0 : 0 ≤ v := hv.1
    calc (|η 0 v - η 0 0| + M * (β * s) * |ξ 0 v - ξ 0 0|) * Real.exp (β * s * L)
        ≤ (K * v + M * (β * s) * (K * v)) * Real.exp (β * s * L) := by gcongr
      _ ≤ (K * v + M * (β * s) * (K * v)) * Real.exp (β * s * (5 * L)) := by
          gcongr
      _ = K * v * (1 + M * β * s) * Real.exp (β * s * (5 * L)) := by ring
      _ ≤ K * v * ((1 + M * β) * (1 + s)) * Real.exp (β * s * (5 * L)) := by
          gcongr
          nlinarith [mul_nonneg hM hβ.le]
      _ = _ := by ring
  -- mixed second difference
  have hmix : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |mixedAmp (chartAmp β ξ η) u v s|
        ≤ (K + 2 * K ^ 2 * β + M * β ^ 2 * K ^ 2 + M * β * K) * (u * v)
          * ((1 + s) ^ 2 * Real.exp (β * s * (5 * L))) := by
    intro u hu v hv s hs
    unfold mixedAmp chartAmp
    have h := amp_mixed_le β L K M u v s (ξ 0 0) (ξ u 0) (ξ 0 v) (ξ u v) (η 0 0) (η u 0) (η 0 v)
      (η u v) hβ hs hL hK hM hu.1 hv.1 (hξL 0 h0b 0 h0b) (hξL u hu 0 h0b) (hξL 0 h0b v hv)
      (hξL u hu v hv) (hξu u hu 0 h0b) (hξv 0 h0b v hv) (hξv u hu v hv) (hξu u hu v hv)
      (hξD u hu v hv) (hηM 0 h0b 0 h0b) (hηu u hu 0 h0b) (hηv 0 h0b v hv) (hηD u hu v hv)
    rw [show 5 * β * L * s = β * s * (5 * L) by ring] at h
    exact h
  have hΦ₀ : ∀ s, 0 ≤ s → |chartAmp β ξ η 0 0 s| ≤ M * Real.exp (β * s * (5 * L)) := by
    intro s hs
    unfold chartAmp
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hbs : 0 ≤ β * s := by positivity
    have hE : Real.exp (β * s * ξ 0 0) ≤ Real.exp (β * s * L) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hξL 0 h0b 0 h0b)) hbs)
    exact mul_le_mul (hηM 0 h0b 0 h0b) (hE.trans (exp_le_exp_five β s L hβ hs hL))
      (Real.exp_pos _).le hM
  exact twoDAmp_second_order β b (5 * L) (K * (1 + M * β))
    (K + 2 * K ^ 2 * β + M * β ^ 2 * K ^ 2 + M * β * K) M p h₁ h₂ k₁ k₂ (chartAmp β ξ η) hβ hb
    hk₁ hk₂ hp₁ hp₂ (by positivity) (by positivity) hΦ hlipA hlipB hmix hΦ₀

/-- The log coefficient of the chart integral is `(k₁k₂)⁻¹ η(0,0) S_p(ξ(0,0))`. -/
theorem twoDChart_A (β p : ℝ) (k₁ k₂ : ℕ) (ξ η : ℝ → ℝ → ℝ) :
    twoDA β p k₁ k₂ (chartAmp β ξ η)
      = 1 / ((k₁ : ℝ) * k₂) * (η 0 0 * weightedMass β (ξ 0 0) (p - 1)) := by
  unfold twoDA chartAmp
  rw [logMoment_const_exp]

/-- **The `n`-form**: at `N = √n`,
`Z(√n) = n^{-p/2} ((A/2) log n + B) + O(n^{-(p+δ)/2} (1 + log n))`. -/
theorem isBigO_sqrt_form (f : ℝ → ℝ) (e : ℝ)
    (h : f =O[atTop] fun N : ℝ => N ^ (-e) * (1 + Real.log N)) :
    (fun n : ℝ => f (Real.sqrt n)) =O[atTop] fun n : ℝ => n ^ (-(e / 2)) * (1 + Real.log n) := by
  have hcomp := h.comp_tendsto tendsto_sqrt_atTop
  refine hcomp.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
  have hn0 : 0 < n := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  simp only [Function.comp]
  rw [Real.log_sqrt hn0.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le, Real.norm_eq_abs,
    Real.norm_eq_abs, one_mul, show 1 / 2 * -e = -(e / 2) by ring]
  have hr : 0 ≤ n ^ (-(e / 2)) := Real.rpow_nonneg hn0.le _
  rw [abs_of_nonneg (mul_nonneg hr (by linarith)), abs_of_nonneg (mul_nonneg hr (by linarith))]
  exact mul_le_mul_of_nonneg_left (by linarith) hr

theorem twoDChart_main_sqrt (β b p A B : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ) (n : ℝ)
    (hn : 0 < n) :
    twoDAmp β b (Real.sqrt n) h₁ h₂ k₁ k₂ Φ
        - (Real.sqrt n) ^ (-p) * (A * Real.log (Real.sqrt n) + B)
      = twoDAmp β b (Real.sqrt n) h₁ h₂ k₁ k₂ Φ - n ^ (-(p / 2)) * (A / 2 * Real.log n + B) := by
  rw [Real.log_sqrt hn.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le,
    show 1 / 2 * -p = -(p / 2) by ring]
  ring

end Laplace.Grammar
