/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The exponent along a ray in rate space

The exponent part of the relative push-forward statement (Astra's item E, germbij_slop S14) in one
loss variable: for a positive sum of monomials `F(x, s) = ∑ c_ν x^{a_ν} s^{b_ν}` on `(0, 1)` with
density `x^h`, along the ray `s = t^{-γ}` the free energy exponent is
`-log Z / log t → (h+1) · max(0, max_ν (1 − b_ν γ)/a_ν)` (`tendsto_rayExponent`). The maximum of
affine functions of `γ` is the chain of Newton edges read in rate space; its kinks are the layers of
the wall (for `x⁶ + x⁴s² + x²s⁶` they sit at `γ = 1/10` and `1/6`). The proof is the classical pair
of bounds: on `x ≤ t^{-a*}` every term of `tF` is `O(1)` (`rayZ_ge`), and on `x ≥ t^{-(a*-ε)}` the
dominant term is `≥ c t^{a ε}`, so that region is exponentially negligible (`rayZ_le`).
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The positive-monomial loss along the ray `s = t^{-γ}`. -/
noncomputable def rayLoss (c a b : ι → ℝ) (γ t x : ℝ) : ℝ :=
  ∑ ν, c ν * x ^ (a ν) * (t ^ (-γ)) ^ (b ν)

/-- The partition function on `(0,1)` with density `x^h`. -/
noncomputable def rayZ (c a b : ι → ℝ) (h : ℕ) (γ t : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, x ^ h * Real.exp (-(t * rayLoss c a b γ t x))

/-- The LP value in one loss variable: `max(0, max_ν (1 − b_ν γ)/a_ν)`. -/
noncomputable def rayExp (a b : ι → ℝ) (γ : ℝ) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty fun ν ↦ (1 - b ν * γ) / a ν)

/-- Positivity of coefficients and exponents. -/
structure RayData (c a b : ι → ℝ) (γ : ℝ) : Prop where
  hc : ∀ ν, 0 < c ν
  ha : ∀ ν, 0 < a ν
  hb : ∀ ν, 0 ≤ b ν
  hγ : 0 ≤ γ

theorem rayExp_nonneg (a b : ι → ℝ) (γ : ℝ) : 0 ≤ rayExp a b γ := le_max_left _ _

theorem le_rayExp (a b : ι → ℝ) (γ : ℝ) (ν : ι) : (1 - b ν * γ) / a ν ≤ rayExp a b γ :=
  le_max_of_le_right (Finset.le_sup' (fun ν ↦ (1 - b ν * γ) / a ν) (Finset.mem_univ ν))

/-- Either the LP value is `0` or it is attained by some monomial. -/
theorem rayExp_eq_zero_or_attained (a b : ι → ℝ) (γ : ℝ) :
    rayExp a b γ = 0 ∨ ∃ ν, (1 - b ν * γ) / a ν = rayExp a b γ := by
  obtain ⟨ν, _, hν⟩ := Finset.exists_max_image Finset.univ (fun ν ↦ (1 - b ν * γ) / a ν)
    Finset.univ_nonempty
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun ν ↦ (1 - b ν * γ) / a ν) =
      (1 - b ν * γ) / a ν := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun ν' _ ↦ hν ν' (Finset.mem_univ _)
    · exact Finset.le_sup' (fun ν ↦ (1 - b ν * γ) / a ν) (Finset.mem_univ ν)
  unfold rayExp
  rw [hsup]
  rcases le_or_gt ((1 - b ν * γ) / a ν) 0 with h | h
  · left; exact max_eq_left h
  · right; exact ⟨ν, (max_eq_right h.le).symm⟩

namespace RayData

variable {c a b : ι → ℝ} {γ : ℝ} (hd : RayData c a b γ)
include hd

omit [Nonempty ι] in
theorem continuous_rayLoss (t : ℝ) : Continuous (rayLoss c a b γ t) := by
  unfold rayLoss
  exact continuous_finsetSum _ fun ν _ ↦
    (continuous_const.mul (Real.continuous_rpow_const (hd.ha ν).le)).mul continuous_const

omit [Nonempty ι] in
theorem rayLoss_nonneg {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) : 0 ≤ rayLoss c a b γ t x :=
  Finset.sum_nonneg fun ν _ ↦ mul_nonneg (mul_nonneg (hd.hc ν).le (Real.rpow_nonneg hx _))
    (Real.rpow_nonneg (Real.rpow_pos_of_pos ht _).le _)

omit [Nonempty ι] in
/-- One monomial of the sum. -/
theorem term_le_rayLoss {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) (ν : ι) :
    c ν * x ^ (a ν) * (t ^ (-γ)) ^ (b ν) ≤ rayLoss c a b γ t x :=
  Finset.single_le_sum (f := fun ν ↦ c ν * x ^ (a ν) * (t ^ (-γ)) ^ (b ν))
    (fun ν _ ↦ mul_nonneg (mul_nonneg (hd.hc ν).le (Real.rpow_nonneg hx _))
      (Real.rpow_nonneg (Real.rpow_pos_of_pos ht _).le _)) (Finset.mem_univ ν)

omit [Fintype ι] [Nonempty ι] in
/-- On `x ≤ t^{-r}` with `a r ≥ 1 − γ b`, each term of `tF` is at most `c`. -/
theorem mul_term_le {t x : ℝ} (ht : 1 ≤ t) (hx : 0 ≤ x) {r : ℝ} (hxr : x ≤ t ^ (-r)) (ν : ι)
    (hr : 1 - b ν * γ ≤ a ν * r) :
    t * (c ν * x ^ (a ν) * (t ^ (-γ)) ^ (b ν)) ≤ c ν := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have h1 : x ^ (a ν) ≤ (t ^ (-r)) ^ (a ν) := Real.rpow_le_rpow hx hxr (hd.ha ν).le
  have h2 : (t ^ (-r)) ^ (a ν) * (t ^ (-γ)) ^ (b ν) = t ^ (-(r * a ν) - γ * b ν) := by
    rw [← Real.rpow_mul ht0.le, ← Real.rpow_mul ht0.le, ← Real.rpow_add ht0]
    ring_nf
  have h3 : t * t ^ (-(r * a ν) - γ * b ν) = t ^ (1 - r * a ν - γ * b ν) := by
    have := Real.rpow_add ht0 1 (-(r * a ν) - γ * b ν)
    rw [Real.rpow_one] at this
    rw [← this]
    ring_nf
  have h4 : t ^ (1 - r * a ν - γ * b ν) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht (by nlinarith [hd.hγ, hd.hb ν])
  calc t * (c ν * x ^ (a ν) * (t ^ (-γ)) ^ (b ν))
      ≤ t * (c ν * (t ^ (-r)) ^ (a ν) * (t ^ (-γ)) ^ (b ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1 (hd.hc ν).le)
          (Real.rpow_nonneg (Real.rpow_pos_of_pos ht0 _).le _)) ht0.le
      _ = c ν * (t * ((t ^ (-r)) ^ (a ν) * (t ^ (-γ)) ^ (b ν))) := by ring
      _ = c ν * t ^ (1 - r * a ν - γ * b ν) := by rw [h2, h3]
      _ ≤ c ν * 1 := mul_le_mul_of_nonneg_left h4 (hd.hc ν).le
      _ = c ν := mul_one _

/-- On `x ≤ t^{-a*}` the rescaled loss is bounded by `C = ∑ c_ν`. -/
theorem mul_rayLoss_le {t x : ℝ} (ht : 1 ≤ t) (hx : 0 ≤ x) (hxr : x ≤ t ^ (-rayExp a b γ)) :
    t * rayLoss c a b γ t x ≤ ∑ ν, c ν := by
  unfold rayLoss
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ν _ ↦ hd.mul_term_le ht hx hxr ν ?_
  have := le_rayExp a b γ ν
  rw [div_le_iff₀ (hd.ha ν)] at this
  linarith

/-- The dominant monomial on `x ≥ t^{-(a*−ε)}`: `tF ≥ c_ν t^{a_ν ε}`. -/
theorem mul_rayLoss_ge {t x : ℝ} (ht : 1 ≤ t) {ν : ι} {ε : ℝ}
    (hν : (1 - b ν * γ) / a ν = rayExp a b γ) (hxr : t ^ (-(rayExp a b γ - ε)) ≤ x) :
    c ν * t ^ (a ν * ε) ≤ t * rayLoss c a b γ t x := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hx : 0 ≤ x := (Real.rpow_pos_of_pos ht0 _).le.trans hxr
  have h1 : (t ^ (-(rayExp a b γ - ε))) ^ (a ν) ≤ x ^ (a ν) :=
    Real.rpow_le_rpow (Real.rpow_pos_of_pos ht0 _).le hxr (hd.ha ν).le
  have hr : a ν * rayExp a b γ = 1 - b ν * γ := by
    rw [← hν, mul_div_cancel₀ _ (hd.ha ν).ne']
  have h2 : t * (c ν * (t ^ (-(rayExp a b γ - ε))) ^ (a ν) * (t ^ (-γ)) ^ (b ν)) =
      c ν * t ^ (a ν * ε) := by
    rw [← Real.rpow_mul ht0.le, ← Real.rpow_mul ht0.le]
    have e : t * (c ν * t ^ (-(rayExp a b γ - ε) * a ν) * t ^ (-γ * b ν)) =
        c ν * (t ^ (1 : ℝ) * t ^ (-(rayExp a b γ - ε) * a ν) * t ^ (-γ * b ν)) := by
      rw [Real.rpow_one]; ring
    rw [e, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
    congr 2
    linear_combination -hr
  calc c ν * t ^ (a ν * ε)
      = t * (c ν * (t ^ (-(rayExp a b γ - ε))) ^ (a ν) * (t ^ (-γ)) ^ (b ν)) := h2.symm
    _ ≤ t * (c ν * x ^ (a ν) * (t ^ (-γ)) ^ (b ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1 (hd.hc ν).le)
          (Real.rpow_nonneg (Real.rpow_pos_of_pos ht0 _).le _)) ht0.le
    _ ≤ t * rayLoss c a b γ t x :=
        mul_le_mul_of_nonneg_left (hd.term_le_rayLoss ht0 hx ν) ht0.le

omit [Nonempty ι] in
theorem integrableOn_integrand (h : ℕ) (t : ℝ) (s : Set ℝ) (hs : s ⊆ Icc 0 1) :
    IntegrableOn (fun x ↦ x ^ h * Real.exp (-(t * rayLoss c a b γ t x))) s := by
  have := hd.continuous_rayLoss t
  exact ((by fun_prop : Continuous fun x : ℝ ↦ x ^ h *
    Real.exp (-(t * rayLoss c a b γ t x))).integrableOn_Icc).mono_set hs

omit [Nonempty ι] hd in
theorem integral_Ioo_pow (h : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ∫ x in Ioo (0 : ℝ) r, x ^ h = r ^ (h + 1) / (h + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr, integral_pow]
  simp

omit [Nonempty ι] hd in
theorem integrableOn_pow (h : ℕ) (s : Set ℝ) (hs : s ⊆ Icc 0 1) :
    IntegrableOn (fun x : ℝ ↦ x ^ h) s :=
  ((by fun_prop : Continuous fun x : ℝ ↦ x ^ h).integrableOn_Icc).mono_set hs

/-- **Lower bound.** `Z ≥ e^{-C} t^{-a*(h+1)}/(h+1)`. -/
theorem rayZ_ge (h : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-∑ ν, c ν) * (t ^ (-rayExp a b γ)) ^ (h + 1) / (h + 1) ≤ rayZ c a b h γ t := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  set r := t ^ (-rayExp a b γ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos ht0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (neg_nonpos.mpr (rayExp_nonneg _ _ _))
  have hsub : Ioo (0 : ℝ) r ⊆ Ioo 0 1 := Ioo_subset_Ioo le_rfl hr1
  have hnn : ∀ x, 0 ≤ x → 0 ≤ x ^ h * Real.exp (-(t * rayLoss c a b γ t x)) :=
    fun x hx ↦ mul_nonneg (pow_nonneg hx _) (Real.exp_pos _).le
  calc Real.exp (-∑ ν, c ν) * r ^ (h + 1) / (h + 1)
      = ∫ x in Ioo (0 : ℝ) r, Real.exp (-∑ ν, c ν) * x ^ h := by
        rw [integral_const_mul, integral_Ioo_pow h hr0.le, mul_div_assoc]
    _ ≤ ∫ x in Ioo (0 : ℝ) r, x ^ h * Real.exp (-(t * rayLoss c a b γ t x)) := by
        refine setIntegral_mono_on ((integrableOn_pow h _ (hsub.trans Ioo_subset_Icc_self)).const_mul _)
          (hd.integrableOn_integrand h t _ (hsub.trans Ioo_subset_Icc_self)) measurableSet_Ioo
          fun x hx ↦ ?_
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg hx.1.le _)
        have := hd.mul_rayLoss_le ht hx.1.le hx.2.le
        linarith
    _ ≤ rayZ c a b h γ t := by
        unfold rayZ
        refine setIntegral_mono_set (hd.integrableOn_integrand h t _ Ioo_subset_Icc_self)
          ((ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun x hx ↦
            hnn x hx.1.le)) (Filter.Eventually.of_forall hsub)

/-- **Upper bound.** For a maximising monomial `ν` and `0 < ε < a*`:
`Z ≤ t^{-(a*-ε)(h+1)} + e^{-c_ν t^{a_ν ε}}`. -/
theorem rayZ_le (h : ℕ) {t : ℝ} (ht : 1 < t) {ν : ι} {ε : ℝ}
    (hεr : ε < rayExp a b γ) (hν : (1 - b ν * γ) / a ν = rayExp a b γ) :
    rayZ c a b h γ t ≤
      (t ^ (-(rayExp a b γ - ε))) ^ (h + 1) + Real.exp (-(c ν * t ^ (a ν * ε))) := by
  have ht0 : 0 < t := one_pos.trans ht
  set r' := t ^ (-(rayExp a b γ - ε)) with hr'
  have hr'0 : 0 < r' := Real.rpow_pos_of_pos ht0 _
  have hr'1 : r' < 1 := Real.rpow_lt_one_of_one_lt_of_neg ht (by linarith)
  have hsplit : Ioo (0 : ℝ) 1 = Ioo 0 r' ∪ Ico r' 1 := (Ioo_union_Ico_eq_Ioo hr'0 hr'1.le).symm
  have hdisj : Disjoint (Ioo (0 : ℝ) r') (Ico r' 1) :=
    Set.disjoint_left.mpr fun x hx hx' ↦ (hx.2.not_ge hx'.1)
  have hsub1 : Ioo (0 : ℝ) r' ⊆ Icc 0 1 := (Ioo_subset_Ioo le_rfl hr'1.le).trans Ioo_subset_Icc_self
  have hsub2 : Ico r' 1 ⊆ Icc 0 1 := (Ico_subset_Ico hr'0.le le_rfl).trans Ico_subset_Icc_self
  have hI1 := hd.integrableOn_integrand h t _ hsub1
  have hI2 := hd.integrableOn_integrand h t _ hsub2
  unfold rayZ
  rw [hsplit, setIntegral_union hdisj measurableSet_Ico hI1 hI2]
  refine add_le_add ?_ ?_
  · calc ∫ x in Ioo (0 : ℝ) r', x ^ h * Real.exp (-(t * rayLoss c a b γ t x))
        ≤ ∫ x in Ioo (0 : ℝ) r', x ^ h := by
          refine setIntegral_mono_on hI1 (integrableOn_pow h _ hsub1) measurableSet_Ioo
            fun x hx ↦ ?_
          have := hd.rayLoss_nonneg ht0 hx.1.le
          exact mul_le_of_le_one_right (pow_nonneg hx.1.le _)
            (Real.exp_le_one_iff.mpr (by nlinarith))
      _ = r' ^ (h + 1) / (h + 1) := integral_Ioo_pow h hr'0.le
      _ ≤ r' ^ (h + 1) := div_le_self (pow_nonneg hr'0.le _) (by
          have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
          linarith)
  · have hbound : ∀ x ∈ Ico r' 1, ‖x ^ h * Real.exp (-(t * rayLoss c a b γ t x))‖ ≤
        Real.exp (-(c ν * t ^ (a ν * ε))) := by
      intro x hx
      have hx0 : 0 ≤ x := hr'0.le.trans hx.1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx0 _) (Real.exp_pos _).le)]
      have hK := hd.mul_rayLoss_ge ht.le hν hx.1
      calc x ^ h * Real.exp (-(t * rayLoss c a b γ t x))
          ≤ 1 * Real.exp (-(t * rayLoss c a b γ t x)) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 hx.2.le) (Real.exp_pos _).le
        _ ≤ Real.exp (-(c ν * t ^ (a ν * ε))) := by
            rw [one_mul]
            exact Real.exp_le_exp.mpr (by linarith)
    have hvol : volume (Ico r' 1) < ⊤ := by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top
    have h1 := norm_setIntegral_le_of_norm_le_const hvol hbound
    have hreal : volume.real (Ico r' 1) ≤ 1 := by
      rw [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
      linarith
    calc ∫ x in Ico r' 1, x ^ h * Real.exp (-(t * rayLoss c a b γ t x))
        ≤ ‖∫ x in Ico r' 1, x ^ h * Real.exp (-(t * rayLoss c a b γ t x))‖ := le_norm_self _
      _ ≤ Real.exp (-(c ν * t ^ (a ν * ε))) * volume.real (Ico r' 1) := h1
      _ ≤ Real.exp (-(c ν * t ^ (a ν * ε))) * 1 :=
          mul_le_mul_of_nonneg_left hreal (Real.exp_pos _).le
      _ = Real.exp (-(c ν * t ^ (a ν * ε))) := mul_one _

omit [Nonempty ι] in
/-- The trivial upper bound `Z ≤ 1`. -/
theorem rayZ_le_one (h : ℕ) {t : ℝ} (ht : 0 < t) : rayZ c a b h γ t ≤ 1 := by
  unfold rayZ
  calc ∫ x in Ioo (0 : ℝ) 1, x ^ h * Real.exp (-(t * rayLoss c a b γ t x))
      ≤ ∫ x in Ioo (0 : ℝ) 1, x ^ h := by
        refine setIntegral_mono_on (hd.integrableOn_integrand h t _ Ioo_subset_Icc_self)
          (integrableOn_pow h _ Ioo_subset_Icc_self) measurableSet_Ioo fun x hx ↦ ?_
        have := hd.rayLoss_nonneg ht hx.1.le
        exact mul_le_of_le_one_right (pow_nonneg hx.1.le _)
          (Real.exp_le_one_iff.mpr (by nlinarith))
    _ = 1 ^ (h + 1) / (h + 1) := integral_Ioo_pow h zero_le_one
    _ ≤ 1 := by
        rw [one_pow]
        exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]) (by positivity)

theorem rayZ_pos (h : ℕ) {t : ℝ} (ht : 1 ≤ t) : 0 < rayZ c a b h γ t :=
  lt_of_lt_of_le (by
    have := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos ht) (-rayExp a b γ)
    positivity) (hd.rayZ_ge h ht)

omit [Nonempty ι] hd in
/-- `e^{-c t^p} ≤ t^{-q}` eventually, for `p > 0`, `c > 0`. -/
theorem eventually_exp_neg_rpow_le {cc p q : ℝ} (hc : 0 < cc) (hp : 0 < p) :
    ∀ᶠ t : ℝ in atTop, Real.exp (-(cc * t ^ p)) ≤ t ^ (-q) := by
  have h1 : Tendsto (fun u : ℝ ↦ u ^ (q / p) * Real.exp (-cc * u)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q / p) cc hc
  have h2 := h1.comp (tendsto_rpow_atTop hp)
  have h3 : Tendsto (fun t : ℝ ↦ t ^ q * Real.exp (-(cc * t ^ p))) atTop (𝓝 0) := by
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp]
    rw [← Real.rpow_mul ht.le, mul_div_cancel₀ _ hp.ne', neg_mul]
  filter_upwards [h3.eventually (eventually_le_nhds one_pos), eventually_gt_atTop 0] with t ht ht0
  have hq : 0 < t ^ q := Real.rpow_pos_of_pos ht0 _
  rw [Real.rpow_neg ht0.le]
  calc Real.exp (-(cc * t ^ p)) = (t ^ q * Real.exp (-(cc * t ^ p))) / t ^ q := by
        field_simp
    _ ≤ 1 / t ^ q := div_le_div_of_nonneg_right ht hq.le
    _ = (t ^ q)⁻¹ := one_div _

/-- **The exponent along a ray.** `-log Z / log t → (h+1) · a*`. -/
theorem tendsto_rayExponent (h : ℕ) :
    Tendsto (fun t ↦ -Real.log (rayZ c a b h γ t) / Real.log t) atTop
      (𝓝 ((h + 1) * rayExp a b γ)) := by
  set r := rayExp a b γ with hr
  set C := ∑ ν, c ν with hC
  have hr0 : 0 ≤ r := rayExp_nonneg a b γ
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  -- upper envelope
  have hup : ∀ᶠ t in atTop, -Real.log (rayZ c a b h γ t) / Real.log t ≤
      (h + 1) * r + (C + Real.log (h + 1)) / Real.log t := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    have ht0 : 0 < t := one_pos.trans ht
    have hlt : 0 < Real.log t := Real.log_pos ht
    have hZ := hd.rayZ_ge h ht.le
    have hpos : 0 < Real.exp (-C) * (t ^ (-r)) ^ (h + 1) / (h + 1) := by
      have := Real.rpow_pos_of_pos ht0 (-r)
      positivity
    have hlog := Real.log_le_log hpos hZ
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by
      have := Real.rpow_pos_of_pos ht0 (-r); positivity), Real.log_exp,
      ← Real.rpow_natCast, ← Real.rpow_mul ht0.le, Real.log_rpow ht0] at hlog
    push_cast at hlog
    rw [div_le_iff₀ hlt]
    have e : ((h + 1) * r + (C + Real.log (h + 1)) / Real.log t) * Real.log t =
        (h + 1) * r * Real.log t + (C + Real.log (h + 1)) := by
      field_simp
    rw [e]
    nlinarith [hlog]
  -- lower envelope
  have hlow : ∀ ε > 0, ∀ᶠ t in atTop, (h + 1) * r - ε ≤
      -Real.log (rayZ c a b h γ t) / Real.log t := by
    intro ε hε
    by_cases hr0' : r = 0
    · filter_upwards [eventually_gt_atTop 1] with t ht
      have hlt : 0 < Real.log t := Real.log_pos ht
      have hZpos := hd.rayZ_pos h ht.le
      have hZ1 := hd.rayZ_le_one h (one_pos.trans ht)
      have : Real.log (rayZ c a b h γ t) ≤ 0 := Real.log_nonpos hZpos.le hZ1
      have : 0 ≤ -Real.log (rayZ c a b h γ t) / Real.log t :=
        div_nonneg (by linarith) hlt.le
      rw [hr0']
      linarith
    · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr0')
      obtain ⟨ν, hν⟩ : ∃ ν, (1 - b ν * γ) / a ν = r := by
        rcases rayExp_eq_zero_or_attained a b γ with h0 | h0
        · exact absurd h0 hr0'
        · exact h0
      set ε' := min (r / 2) (ε / (2 * (h + 1))) with hε'
      have hε'0 : 0 < ε' := lt_min (half_pos hrpos) (by positivity)
      have hε'r : ε' < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hrpos)
      have hε'ε : (h + 1) * ε' ≤ ε / 2 := by
        have := min_le_right (r / 2) (ε / (2 * (h + 1)))
        calc (h + 1) * ε' ≤ (h + 1) * (ε / (2 * (h + 1))) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = ε / 2 := by field_simp
      have hexp := eventually_exp_neg_rpow_le (cc := c ν) (p := a ν * ε')
        (q := (r - ε') * (h + 1)) (hd.hc ν) (mul_pos (hd.ha ν) hε'0)
      have hlog2 : Tendsto (fun t : ℝ ↦ Real.log 2 / Real.log t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
      filter_upwards [eventually_gt_atTop 1, hexp,
        hlog2.eventually (eventually_le_nhds (half_pos hε))] with t ht hexp hl2
      have ht0 : 0 < t := one_pos.trans ht
      have hlt : 0 < Real.log t := Real.log_pos ht
      have hZle := hd.rayZ_le h ht hε'r hν
      have hpow : (t ^ (-(r - ε'))) ^ (h + 1) = t ^ (-((r - ε') * (h + 1))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
        push_cast
        ring_nf
      rw [hpow] at hZle
      have hZ2 : rayZ c a b h γ t ≤ 2 * t ^ (-((r - ε') * (h + 1))) := by linarith
      have hZpos := hd.rayZ_pos h ht.le
      have hlog := Real.log_le_log hZpos hZ2
      rw [Real.log_mul two_ne_zero (Real.rpow_pos_of_pos ht0 _).ne', Real.log_rpow ht0] at hlog
      -- `-log Z / log t ≥ (r - ε')(h+1) - log 2 / log t`
      rw [le_div_iff₀ hlt]
      have : ((h + 1) * r - ε) * Real.log t ≤ ((r - ε') * (h + 1)) * Real.log t - Real.log 2 := by
        have h2 : Real.log 2 ≤ ε / 2 * Real.log t := by
          rwa [div_le_iff₀ hlt] at hl2
        nlinarith
      linarith
  -- conclude
  refine tendsto_order.2 ⟨fun a' ha' ↦ ?_, fun a' ha' ↦ ?_⟩
  · have hε : 0 < ((h + 1) * r - a') / 2 := by linarith
    filter_upwards [hlow _ hε] with t ht
    linarith
  · have h0 : Tendsto (fun t : ℝ ↦ (C + Real.log (h + 1)) / Real.log t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    filter_upwards [hup, h0.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < a' - (h + 1) * r))]
      with t ht hlt
    linarith

end RayData

end Laplace.Multi
