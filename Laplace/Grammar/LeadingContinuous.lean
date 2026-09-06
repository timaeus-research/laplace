/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LeadingGeneral

/-!
# Leading asymptotic of the standard integral for general continuous data (grammar §4.2)

The one-dimensional leading term of `cor:standardintegralexp` in its natural generality: for any
continuous `ξ`, `η` on the chart with `|ξ(u) - ξ(0)| ≤ C u` and `|η(u) - η(0)| ≤ C' u` (as for any
`C¹` or analytic function at the chart origin),

  `∫₀^b u^h η(u) e^{-βn u^{2k} + β√n u^k ξ(u)} du
      ~ η(0) · (2k)^{-1} S_{(h+1)/(2k)}(ξ(0)) · n^{-(h+1)/(2k)}`   (`η(0) ≠ 0`),

with the difference `O(n^{-(h+2)/(2k)})`. No series expansion of `ξ` is needed: the leading term
only sees `ξ(0)` and `η(0)`, and the first-order remainder `e^{x} - 1` is controlled by
`|e^{x} - 1| ≤ |x| e^{|x|}` (the `N = 1` case of `abs_exp_sub_sum_range_le`). This supersedes the
polynomial special cases for the leading order. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

/-- `|eˣ - 1| ≤ |x| e^{|x|}` for every real `x`. -/
theorem abs_exp_sub_one_le_abs_mul_exp (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  have := abs_exp_sub_sum_range_le x 1
  simpa [Finset.sum_range_one] using this

/-- **Leading term for continuous data, with error `O(n^{-(h+2)/(2k)})`**: for continuous `ξ, η`
with `|ξ u - ξ₀| ≤ C u` and `|η u - η₀| ≤ C' u` on `(0, b]`,
`Z_chart(ξ,η) - η₀ (2k)^{-1} S_{(h+1)/(2k)}(ξ₀) n^{-(h+1)/(2k)} = O(n^{-(h+2)/(2k)})`. -/
theorem standardIntegral1D_leading_isBigO_of_lipschitz (β ξ₀ η₀ b C C' : ℝ) (ξ η : ℝ → ℝ)
    (h k : ℕ) (hβ : 0 < β) (hb : 0 < b) (hk : 0 < k) (hC : 0 ≤ C)
    (hξc : Continuous ξ) (hηc : Continuous η)
    (hξ : ∀ u ∈ Ioc (0 : ℝ) b, |ξ u - ξ₀| ≤ C * u) (hη : ∀ u ∈ Ioc (0 : ℝ) b, |η u - η₀| ≤ C' * u) :
    (fun n : ℝ => (∫ u in Ioc 0 b,
        u ^ h * η u * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ u))
      - η₀ * ((1 / (2 * (k : ℝ))) * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀)
          * n ^ (-(((h : ℝ) + 1) / (2 * k))))
      =O[atTop] fun n : ℝ => n ^ (-(((h : ℝ) + 2) / (2 * k))) := by
  set μ₁ : ℝ := ((h : ℝ) + 1) / (2 * k) with hμ₁
  set ν : ℝ := ((h : ℝ) + 2) / (2 * k) with hν
  set ε : ℝ := β / 4 * b ^ (2 * k) with hε
  have hε0 : 0 < ε := by positivity
  set a' : ℝ := ξ₀ + C * b with ha'
  -- constants
  obtain ⟨K₀, hK₀⟩ : ∃ K : ℝ, K = Real.exp (β * ξ₀ ^ 2 / 2)
    * ((β / 4) ^ (-(((h : ℝ) + 1) / (2 * k))) * (1 / (2 * (k : ℝ)))
      * Real.Gamma (((h : ℝ) + 1) / (2 * k))) := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R : ℝ, R = |η₀| * (β * C) * ((1 / (2 * (k : ℝ)))
    * fluctuation β ((((h + 1 : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) a') := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R : ℝ, R = C' * ((1 / (2 * (k : ℝ)))
    * fluctuation β ((((h + 1 : ℕ) : ℝ) + 1) / (2 * k)) a') := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]
    have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < ((h : ℝ) + 1) / (2 * k))
    positivity
  have hl₀ : (fun n : ℝ => Real.exp (-ε * n)) =o[atTop] fun n : ℝ => n ^ (-ν) :=
    isLittleO_exp_neg_mul_rpow_atTop hε0 (-ν)
  apply IsBigO.of_bound (|η₀| * K₀ + R₁ + R₂)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hl₀.bound one_pos] with n hn hb₀
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow_pos : 0 < n ^ (-ν) := Real.rpow_pos_of_pos hn0 _
  simp only [Real.norm_eq_abs] at hb₀ ⊢
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos hpow_pos, one_mul] at hb₀
  rw [abs_of_pos hpow_pos]
  -- pieces
  obtain ⟨pop, hpop⟩ : ∃ f : ℝ → ℝ,
      f = fun u => Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ f : ℝ → ℝ, f = fun u => β * Real.sqrt n * u ^ k * (ξ u - ξ₀) := ⟨_, rfl⟩
  obtain ⟨g₀, hg₀⟩ : ∃ g : ℝ → ℝ, g = fun u => η₀ * (u ^ h * pop u) := ⟨_, rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g : ℝ → ℝ, g = fun u => η₀ * (u ^ h * pop u * (Real.exp (x u) - 1)) :=
    ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g : ℝ → ℝ, g = fun u => u ^ h * (η u - η₀) * (pop u * Real.exp (x u)) :=
    ⟨_, rfl⟩
  have hcont_pop : Continuous pop := by rw [hpop]; fun_prop
  have hcont_x : Continuous x := by
    rw [hx]; exact (continuous_const.mul (continuous_pow k)).mul (hξc.sub continuous_const)
  have hdecomp : (fun u : ℝ =>
      u ^ h * η u * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ u))
      = fun u => g₀ u + g₁ u + g₂ u := by
    funext u
    simp only [hg₀, hg₁, hg₂, hpop, hx]
    rw [show -β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ u
        = (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
          + β * Real.sqrt n * u ^ k * (ξ u - ξ₀) by ring, Real.exp_add]
    ring
  have hcont₀ : Continuous g₀ := by
    rw [hg₀]; exact continuous_const.mul ((continuous_pow h).mul hcont_pop)
  have hcont₁ : Continuous g₁ := by
    rw [hg₁]
    exact continuous_const.mul (((continuous_pow h).mul hcont_pop).mul
      ((Real.continuous_exp.comp hcont_x).sub continuous_const))
  have hcont₂ : Continuous g₂ := by
    rw [hg₂]
    exact ((continuous_pow h).mul (hηc.sub continuous_const)).mul
      (hcont_pop.mul (Real.continuous_exp.comp hcont_x))
  have hi₀ : IntegrableOn g₀ (Ioc 0 b) := hcont₀.integrableOn_Ioc
  have hi₁ : IntegrableOn g₁ (Ioc 0 b) := hcont₁.integrableOn_Ioc
  have hi₂ : IntegrableOn g₂ (Ioc 0 b) := hcont₂.integrableOn_Ioc
  have hi₀₁ : IntegrableOn (fun u => g₀ u + g₁ u) (Ioc 0 b) := hi₀.add hi₁
  -- zeroth order
  have hI₀ : (∫ u in Ioc 0 b, g₀ u)
      = η₀ * ((1 / (2 * (k : ℝ))) * n ^ (-μ₁) * fluctuation β μ₁ ξ₀
        - ∫ u in Ioi b,
            u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) := by
    have hint := standardIntegrand_integrableOn β n ξ₀ h k hβ hn0 hk
    have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl b)) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hb.le))
    rw [Ioc_union_Ioi_eq_Ioi hb.le, standardIntegral1D_eq_fluctuation β n ξ₀ h k hn0 hk] at hsplit
    simp only [hg₀, hpop]
    rw [integral_const_mul]
    congr 1
    linarith
  -- shared pointwise facts on the chart
  have hkey : ∀ u ∈ Ioc (0 : ℝ) b, pop u * Real.exp |x u|
      ≤ Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a') := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hxle : |x u| ≤ β * Real.sqrt n * u ^ k * (C * b) := by
      simp only [hx]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β * Real.sqrt n * u ^ k)]
      calc β * Real.sqrt n * u ^ k * |ξ u - ξ₀| ≤ β * Real.sqrt n * u ^ k * (C * u) :=
            mul_le_mul_of_nonneg_left (hξ u hu) (by positivity)
        _ ≤ β * Real.sqrt n * u ^ k * (C * b) := by gcongr; exact hu.2
    simp only [hpop]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [ha']; nlinarith [hxle]
  -- first-order piece
  obtain ⟨bnd₁, hbnd₁⟩ : ∃ g : ℝ → ℝ, g = fun u => |η₀| * (β * C) * (u ^ (h + 1)
      * (Real.sqrt n * u ^ k) * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) :=
    ⟨_, rfl⟩
  have hH₁ : (fun u : ℝ => u ^ (h + 1) * (Real.sqrt n * u ^ k)
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a'))
      = fun u => Real.sqrt n * (u ^ (h + 1 + k)
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) := by
    funext u; rw [pow_add u (h + 1)]; ring
  have hbnd₁_int : IntegrableOn bnd₁ (Ioi 0) := by
    have hint : IntegrableOn (fun u : ℝ => u ^ (h + 1) * (Real.sqrt n * u ^ k)
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) (Ioi 0) := by
      rw [hH₁]; exact (standardIntegrand_integrableOn β n a' (h + 1 + k) k hβ hn0 hk).const_mul _
    rw [hbnd₁]; exact hint.const_mul _
  have hbnd₁_val : (∫ u in Ioi 0, bnd₁ u) = R₁ * n ^ (-((((h + 1 : ℕ) : ℝ) + 1) / (2 * k))) := by
    simp only [hbnd₁]
    have hins := standardIntegral1D_insertion β n a' (h + 1) k 1 hn0 hk
    simp only [pow_one] at hins
    rw [integral_const_mul, hins, hR₁]; push_cast; ring
  have hpt₁ : ∀ u ∈ Ioc (0 : ℝ) b, |g₁ u| ≤ bnd₁ u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hpop_pos : 0 < pop u := by simp only [hpop]; exact Real.exp_pos _
    have hupop : 0 ≤ u ^ h * pop u := mul_nonneg (pow_nonneg hu0.le h) hpop_pos.le
    have hxle : |x u| ≤ β * Real.sqrt n * u ^ k * (C * u) := by
      simp only [hx]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β * Real.sqrt n * u ^ k)]
      exact mul_le_mul_of_nonneg_left (hξ u hu) (by positivity)
    calc |g₁ u| = |η₀| * (u ^ h * pop u * |Real.exp (x u) - 1|) := by
          simp only [hg₁]; rw [abs_mul, abs_mul, abs_of_nonneg hupop]
      _ ≤ |η₀| * (u ^ h * pop u * (|x u| * Real.exp |x u|)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (abs_exp_sub_one_le_abs_mul_exp (x u)) hupop) (abs_nonneg _)
      _ = |η₀| * (|x u| * u ^ h * (pop u * Real.exp |x u|)) := by ring
      _ ≤ |η₀| * ((β * Real.sqrt n * u ^ k * (C * u)) * u ^ h
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (mul_le_mul_of_nonneg_right hxle (pow_nonneg hu0.le h)) (hkey u hu)
              (by positivity) (by positivity)) (abs_nonneg _)
      _ = bnd₁ u := by simp only [hbnd₁]; rw [pow_succ]; ring
  have hI₁ : |∫ u in Ioc 0 b, g₁ u| ≤ R₁ * n ^ (-ν) := by
    have hR₁0 : 0 ≤ R₁ := by
      rw [hR₁]
      have := fluctuation_pos β ((((h + 1 : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) a' hβ
        (by positivity)
      positivity
    have hexp : n ^ (-((((h + 1 : ℕ) : ℝ) + 1) / (2 * k))) = n ^ (-ν) := by
      rw [hν]; push_cast; ring_nf
    calc |∫ u in Ioc 0 b, g₁ u| ≤ ∫ u in Ioc 0 b, |g₁ u| := abs_integral_le_integral_abs
      _ ≤ ∫ u in Ioc 0 b, bnd₁ u :=
          setIntegral_mono_on hi₁.abs (hbnd₁_int.mono_set Ioc_subset_Ioi_self)
            measurableSet_Ioc hpt₁
      _ ≤ ∫ u in Ioi 0, bnd₁ u := by
          apply setIntegral_mono_set hbnd₁_int
          · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
            refine Filter.Eventually.of_forall fun u hu => ?_
            have hu0 : (0 : ℝ) < u := hu
            simp only [hbnd₁, Pi.zero_apply]; positivity
          · exact Ioc_subset_Ioi_self.eventuallyLE
      _ = R₁ * n ^ (-ν) := by rw [hbnd₁_val, hexp]
  -- the weight piece
  obtain ⟨bnd₂, hbnd₂⟩ : ∃ g : ℝ → ℝ, g = fun u => C' * (u ^ (h + 1)
      * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a')) := ⟨_, rfl⟩
  have hbnd₂_int : IntegrableOn bnd₂ (Ioi 0) := by
    rw [hbnd₂]; exact (standardIntegrand_integrableOn β n a' (h + 1) k hβ hn0 hk).const_mul _
  have hbnd₂_val : (∫ u in Ioi 0, bnd₂ u) = R₂ * n ^ (-((((h + 1 : ℕ) : ℝ) + 1) / (2 * k))) := by
    simp only [hbnd₂]
    rw [integral_const_mul, standardIntegral1D_eq_fluctuation β n a' (h + 1) k hn0 hk, hR₂]; ring
  have hC'0 : 0 ≤ C' := by
    have := hη b ⟨hb, le_refl b⟩
    have h0 : (0 : ℝ) ≤ C' * b := (abs_nonneg _).trans this
    nlinarith
  have hpt₂ : ∀ u ∈ Ioc (0 : ℝ) b, |g₂ u| ≤ bnd₂ u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hpop_pos : 0 < pop u := by simp only [hpop]; exact Real.exp_pos _
    have hpe : 0 ≤ pop u * Real.exp (x u) := by positivity
    have hexpx : Real.exp (x u) ≤ Real.exp |x u| := Real.exp_le_exp.2 (le_abs_self _)
    calc |g₂ u| = u ^ h * |η u - η₀| * (pop u * Real.exp (x u)) := by
          simp only [hg₂]
          rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hu0.le h), abs_of_nonneg hpe]
      _ ≤ u ^ h * (C' * u) * (pop u * Real.exp |x u|) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hη u hu) (pow_nonneg hu0.le h))
            (mul_le_mul_of_nonneg_left hexpx hpop_pos.le) hpe (by positivity)
      _ ≤ u ^ h * (C' * u)
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a') :=
          mul_le_mul_of_nonneg_left (hkey u hu) (by positivity)
      _ = bnd₂ u := by simp only [hbnd₂]; rw [pow_succ]; ring
  have hI₂ : |∫ u in Ioc 0 b, g₂ u| ≤ R₂ * n ^ (-ν) := by
    have hexp : n ^ (-((((h + 1 : ℕ) : ℝ) + 1) / (2 * k))) = n ^ (-ν) := by
      rw [hν]; push_cast; ring_nf
    calc |∫ u in Ioc 0 b, g₂ u| ≤ ∫ u in Ioc 0 b, |g₂ u| := abs_integral_le_integral_abs
      _ ≤ ∫ u in Ioc 0 b, bnd₂ u :=
          setIntegral_mono_on hi₂.abs (hbnd₂_int.mono_set Ioc_subset_Ioi_self)
            measurableSet_Ioc hpt₂
      _ ≤ ∫ u in Ioi 0, bnd₂ u := by
          apply setIntegral_mono_set hbnd₂_int
          · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
            refine Filter.Eventually.of_forall fun u hu => ?_
            have hu0 : (0 : ℝ) < u := hu
            simp only [hbnd₂, Pi.zero_apply]; positivity
          · exact Ioc_subset_Ioi_self.eventuallyLE
      _ = R₂ * n ^ (-ν) := by rw [hbnd₂_val, hexp]
  -- the tail
  have ht₀ := standardIntegral1D_tail_le β n ξ₀ b h k hβ hn hb hk
  rw [show -(β / 4) * n * b ^ (2 * k) = -ε * n by rw [hε]; ring] at ht₀
  have htail₀ : (∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k)
      + β * Real.sqrt n * u ^ k * ξ₀)) ≤ K₀ * n ^ (-ν) := by
    calc _ ≤ _ := ht₀
      _ = K₀ * Real.exp (-ε * n) := by rw [hK₀]; ring
      _ ≤ K₀ * n ^ (-ν) := mul_le_mul_of_nonneg_left hb₀ hK₀0
  have htail_nonneg : 0 ≤ ∫ u in Ioi b,
      u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (pow_nonneg (hb.trans hu).le h) (Real.exp_pos _).le
  -- assemble
  rw [hdecomp, integral_add hi₀₁ hi₂, integral_add hi₀ hi₁, hI₀]
  set T₀ := ∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
  set I₁ := ∫ u in Ioc 0 b, g₁ u
  set I₂ := ∫ u in Ioc 0 b, g₂ u
  have key : ∀ (e A T i₁ i₂ : ℝ), e * (A - T) + i₁ + i₂ - e * A = -(e * T) + i₁ + i₂ := by
    intros; ring
  rw [show η₀ * ((1 / (2 * (k : ℝ))) * n ^ (-μ₁) * fluctuation β μ₁ ξ₀ - T₀) + I₁ + I₂
      - η₀ * ((1 / (2 * (k : ℝ))) * fluctuation β μ₁ ξ₀) * n ^ (-μ₁)
      = -(η₀ * T₀) + I₁ + I₂ by ring]
  calc |-(η₀ * T₀) + I₁ + I₂| ≤ |-(η₀ * T₀)| + |I₁| + |I₂| := by
        calc |-(η₀ * T₀) + I₁ + I₂| ≤ |-(η₀ * T₀) + I₁| + |I₂| := abs_add_le _ _
          _ ≤ |-(η₀ * T₀)| + |I₁| + |I₂| := by gcongr; exact abs_add_le _ _
    _ = |η₀| * T₀ + |I₁| + |I₂| := by rw [abs_neg, abs_mul, abs_of_nonneg htail_nonneg]
    _ ≤ |η₀| * (K₀ * n ^ (-ν)) + R₁ * n ^ (-ν) + R₂ * n ^ (-ν) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left htail₀ (abs_nonneg _)) hI₁) hI₂
    _ = (|η₀| * K₀ + R₁ + R₂) * n ^ (-ν) := by ring

/-- **Leading asymptotic of the standard integral for general continuous data** (grammar §4.2, the
leading term of `cor:standardintegralexp` in one dimension): for continuous `ξ, η` with
`|ξ u - ξ₀| ≤ C u`, `|η u - η₀| ≤ C' u` on `(0, b]` and `η₀ ≠ 0`,
`∫₀^b u^h η(u) e^{-βn u^{2k} + β√n u^k ξ(u)} du
    ~ η₀ (2k)^{-1} S_{(h+1)/(2k)}(ξ₀) n^{-(h+1)/(2k)}`. -/
theorem standardIntegral1D_leading_isEquivalent_of_lipschitz (β ξ₀ η₀ b C C' : ℝ) (ξ η : ℝ → ℝ)
    (h k : ℕ) (hβ : 0 < β) (hb : 0 < b) (hk : 0 < k) (hC : 0 ≤ C) (hη₀ : η₀ ≠ 0)
    (hξc : Continuous ξ) (hηc : Continuous η)
    (hξ : ∀ u ∈ Ioc (0 : ℝ) b, |ξ u - ξ₀| ≤ C * u) (hη : ∀ u ∈ Ioc (0 : ℝ) b, |η u - η₀| ≤ C' * u) :
    (fun n : ℝ => ∫ u in Ioc 0 b,
        u ^ h * η u * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ u))
      ~[atTop] fun n : ℝ => η₀ * ((1 / (2 * (k : ℝ))) * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀)
        * n ^ (-(((h : ℝ) + 1) / (2 * k))) := by
  have hμν : ((h : ℝ) + 1) / (2 * k) < ((h : ℝ) + 2) / (2 * k) := by
    rw [div_lt_div_iff_of_pos_right (by positivity)]; linarith
  have hA₀pos : 0 < (1 / (2 * (k : ℝ))) * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀ := by
    have := fluctuation_pos β (((h : ℝ) + 1) / (2 * k)) ξ₀ hβ (by positivity); positivity
  apply IsLittleO.isEquivalent
  exact ((standardIntegral1D_leading_isBigO_of_lipschitz β ξ₀ η₀ b C C' ξ η h k hβ hb hk hC hξc hηc
    hξ hη).trans_isLittleO (isLittleO_rpow_neg_rpow_neg hμν)).const_mul_right
    (mul_ne_zero hη₀ hA₀pos.ne')

end Laplace.Grammar
