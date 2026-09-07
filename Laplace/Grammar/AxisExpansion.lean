/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDGenDensity

/-!
# The axis expansion of a one-variable amplitude (grammar §4.2, `d = 2`)

For an amplitude `Ψ(u, s)` depending on the first coordinate only, Lipschitz in `u` at `0`, the
one-variable density of unit 86 expands as

  `ρ_Ψ(r, s) = r^{p-1} log(1/r) · Ψ(0,s)/(k₁k₂) + r^{p-1} · (log R · Ψ(0,s)/(k₁k₂) + I_Ψ(s)/k₂)
              + O(r^{p-1+1/k₁} (1+s) e^{βLs})`,   `I_Ψ(s) = ∫₀^b (Ψ(u,s) − Ψ(0,s))/u du`

(`uDensity_expansion`), and the density-transfer theorem gives, for `N ≥ 1`,

  `Z_Ψ(N) = N^{-p} (A_Ψ log N + B_Ψ) + O(N^{-(p+1/k₁)} (1 + log N))`

with `A_Ψ = (k₁k₂)⁻¹ ∫ s^{p-1} e^{-βs²} Ψ(0,s) ds` and
`B_Ψ = (k₁k₂)⁻¹ ∫ s^{p-1} (log R − log s) e^{-βs²} Ψ(0,s) ds + k₂⁻¹ ∫ s^{p-1} e^{-βs²} I_Ψ(s) ds`
(`twoDAmp_uOnly_expansion`). The constant `B_Ψ` sees the whole axis `{v = 0}`, not only the
corner. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- The axis integral `I_Ψ(s) = ∫₀^b u⁻¹ (Ψ(u,s) − Ψ(0,s)) du`. -/
noncomputable def axisIntegral (b : ℝ) (Ψ : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, u⁻¹ * (Ψ u s - Ψ 0 s)

/-- The log-coefficient function `c₀(s) = Ψ(0,s)/(k₁k₂)`. -/
noncomputable def uCoeff₀ (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  1 / ((k₁ : ℝ) * k₂) * Ψ 0 s

/-- The constant-coefficient function `c₁(s) = log R · Ψ(0,s)/(k₁k₂) + I_Ψ(s)/k₂`. -/
noncomputable def uCoeff₁ (b : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  1 / ((k₁ : ℝ) * k₂) * (Real.log (b ^ (k₁ + k₂)) * Ψ 0 s) + 1 / (k₂ : ℝ) * axisIntegral b Ψ s

/-- The remainder envelope `H(s) = (C₁/k₂) (b^{k₂})^{-1/k₁} (1+s) e^{βsL}`. -/
noncomputable def uEnvelope (β b L C₁ : ℝ) (k₁ k₂ : ℕ) (s : ℝ) : ℝ :=
  C₁ / (k₂ : ℝ) * (b ^ k₂) ^ (-(k₁ : ℝ)⁻¹) * ((1 + |s|) * Real.exp (β * s * L))

/-- Integrability of `u⁻¹(Ψ(u,s) − Ψ(0,s))` on `(0, b]` from the Lipschitz bound. -/
theorem axis_integrand_integrableOn (β b L C₁ : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) (s : ℝ) (hs : 0 ≤ s)
    (hlip : ∀ u ∈ Icc (0 : ℝ) b, |Ψ u s - Ψ 0 s| ≤ C₁ * u * ((1 + s) * Real.exp (β * s * L))) :
    IntegrableOn (fun u => u⁻¹ * (Ψ u s - Ψ 0 s)) (Ioc 0 b) := by
  have hmeas : Measurable fun u : ℝ => u⁻¹ * (Ψ u s - Ψ 0 s) :=
    measurable_inv.mul ((hΨc.measurable.comp (measurable_id.prodMk measurable_const)).sub
      measurable_const)
  refine Integrable.mono' (integrableOn_const (C := C₁ * ((1 + s) * Real.exp (β * s * L)))
    measure_Ioc_lt_top.ne) hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hu.1)]
  have := hlip u ⟨hu.1.le, hu.2⟩
  have hu0 : u ≠ 0 := hu.1.ne'
  calc u⁻¹ * |Ψ u s - Ψ 0 s| ≤ u⁻¹ * (C₁ * u * ((1 + s) * Real.exp (β * s * L))) :=
        mul_le_mul_of_nonneg_left this (inv_pos.2 hu.1).le
    _ = C₁ * ((1 + s) * Real.exp (β * s * L)) := by field_simp

/-- **Exact decomposition of the density integral**: for `0 < m ≤ b`,
`∫_m^b u⁻¹ Ψ(u,s) = Ψ(0,s) log(b/m) + I_Ψ(s) − ∫₀^m u⁻¹ (Ψ(u,s) − Ψ(0,s))`. -/
theorem uDensity_integral_eq (β b L C₁ : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) (s : ℝ) (hs : 0 ≤ s)
    (hlip : ∀ u ∈ Icc (0 : ℝ) b, |Ψ u s - Ψ 0 s| ≤ C₁ * u * ((1 + s) * Real.exp (β * s * L)))
    (m : ℝ) (hm : 0 < m) (hmb : m ≤ b) :
    (∫ u in Icc m b, u⁻¹ * Ψ u s)
      = Ψ 0 s * Real.log (b / m) + axisIntegral b Ψ s
        - ∫ u in Ioc (0 : ℝ) m, u⁻¹ * (Ψ u s - Ψ 0 s) := by
  have hint := axis_integrand_integrableOn β b L C₁ Ψ hΨc s hs hlip
  have hint₁ : IntegrableOn (fun u : ℝ => u⁻¹ * Ψ 0 s) (Ioc m b) := by
    have hII : IntervalIntegrable (fun x : ℝ => x⁻¹) volume m b :=
      intervalIntegral.intervalIntegrable_inv (f := fun x => x)
        (fun u hu => by rw [uIcc_of_le hmb] at hu; exact (lt_of_lt_of_le hm hu.1).ne')
        continuousOn_id
    exact hII.1.mul_const _
  have hlog : ∫ u in Icc m b, u⁻¹ = Real.log (b / m) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hmb,
      integral_inv_of_pos hm (lt_of_lt_of_le hm hmb)]
  have hsplit : ∀ u : ℝ, u⁻¹ * Ψ u s = u⁻¹ * Ψ 0 s + u⁻¹ * (Ψ u s - Ψ 0 s) := by
    intro u; ring
  simp_rw [hsplit]
  rw [integral_Icc_eq_integral_Ioc, integral_add hint₁ (hint.mono_set (Ioc_subset_Ioc_left hm.le)),
    integral_mul_const, ← integral_Icc_eq_integral_Ioc, hlog]
  -- split the axis integral at `m`
  have hunion : axisIntegral b Ψ s
      = (∫ u in Ioc (0 : ℝ) m, u⁻¹ * (Ψ u s - Ψ 0 s)) + ∫ u in Ioc m b, u⁻¹ * (Ψ u s - Ψ 0 s) := by
    unfold axisIntegral
    rw [← Ioc_union_Ioc_eq_Ioc hm.le hmb]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hint.mono_set (Ioc_subset_Ioc_right hmb)) (hint.mono_set (Ioc_subset_Ioc_left hm.le))
  rw [hunion]; ring

/-- Measurability of the density integral in `(r, s)`. -/
theorem uDensity_integral_measurable (b : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) :
    Measurable fun z : ℝ × ℝ => ∫ u in Icc ((z.1 / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b, u⁻¹ * Ψ u z.2 := by
  set F : (ℝ × ℝ) × ℝ → ℝ := fun w =>
    if (w.1.1 / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) ≤ w.2 ∧ w.2 ≤ b then w.2⁻¹ * Ψ w.2 w.1.2 else 0 with hF
  have hFm : Measurable F := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_le (((measurable_fst.comp measurable_fst).div_const _).pow_const _)
        measurable_snd).inter (measurableSet_le measurable_snd measurable_const)
    · exact measurable_snd.inv.mul (hΨc.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have heq : (fun z : ℝ × ℝ => ∫ u in Icc ((z.1 / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b, u⁻¹ * Ψ u z.2)
      = fun z => ∫ u, F (z, u) := by
    funext z
    rw [← integral_indicator (μ := (volume : Measure ℝ)) (f := fun u : ℝ => u⁻¹ * Ψ u z.2)
      measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hF, indicator_apply, mem_Icc]
  rw [heq]
  exact (StronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
    hFm.stronglyMeasurable).measurable

/-- Measurability of the axis integral in `s`. -/
theorem axisIntegral_measurable (b : ℝ) (Ψ : ℝ → ℝ → ℝ) (hΨc : Continuous (Function.uncurry Ψ)) :
    Measurable (axisIntegral b Ψ) := by
  unfold axisIntegral
  set F : ℝ × ℝ → ℝ := fun w => w.2⁻¹ * (Ψ w.2 w.1 - Ψ 0 w.1) with hF
  have hFm : Measurable F :=
    measurable_snd.inv.mul ((hΨc.measurable.comp (measurable_snd.prodMk measurable_fst)).sub
      (hΨc.measurable.comp (measurable_const.prodMk measurable_fst)))
  have : (fun s => ∫ u in Ioc (0 : ℝ) b, u⁻¹ * (Ψ u s - Ψ 0 s))
      = fun s => ∫ u, F (s, u) ∂((volume : Measure ℝ).restrict (Ioc 0 b)) := by
    funext s; rfl
  rw [this]
  exact (StronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioc 0 b)) hFm.stronglyMeasurable).measurable

/-- **The density expansion of a one-variable amplitude**. -/
theorem uDensity_expansion (β b L C₁ p : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hC₁ : 0 ≤ C₁) (hΨc : Continuous (Function.uncurry Ψ))
    (hlip : ∀ u ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |Ψ u s - Ψ 0 s| ≤ C₁ * u * ((1 + s) * Real.exp (β * s * L))) :
    DensityExpansion (uDensity p b k₁ k₂ Ψ) ![p, p] ![1, 0]
      ![uCoeff₀ k₁ k₂ Ψ, uCoeff₁ b k₁ k₂ Ψ] (p + (k₁ : ℝ)⁻¹) (b ^ (k₁ + k₂)) 1
      (uEnvelope β b L C₁ k₁ k₂) where
  R_pos := by positivity
  α_lt := by
    intro i
    have : (0 : ℝ) < (k₁ : ℝ)⁻¹ := by positivity
    fin_cases i <;> simp <;> linarith
  j_le := by intro i; fin_cases i <;> simp
  ρ_meas := by
    unfold uDensity Function.uncurry
    exact (measurable_const.mul (measurable_fst.pow_const _)).mul
      (uDensity_integral_measurable b k₁ k₂ Ψ hΨc)
  c_meas := by
    intro i
    have h0 : Measurable fun s => Ψ 0 s :=
      hΨc.measurable.comp (measurable_const.prodMk measurable_id)
    fin_cases i
    · exact measurable_const.mul h0
    · exact (measurable_const.mul (measurable_const.mul h0)).add
        (measurable_const.mul (axisIntegral_measurable b Ψ hΨc))
  H_meas := by
    unfold uEnvelope
    exact measurable_const.mul ((measurable_const.add continuous_abs.measurable).mul
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).mul measurable_const)))
  H_nonneg := by
    intro s
    unfold uEnvelope
    have h1 : 0 ≤ C₁ / (k₂ : ℝ) * (b ^ k₂) ^ (-(k₁ : ℝ)⁻¹) :=
      mul_nonneg (div_nonneg hC₁ (Nat.cast_nonneg _)) (Real.rpow_nonneg (by positivity) _)
    exact mul_nonneg h1 (mul_nonneg (by positivity) (Real.exp_pos _).le)
  rem := by
    intro r hr s hs
    have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
    have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
    have hbk : 0 < b ^ k₂ := by positivity
    set m : ℝ := (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) with hm
    have hm0 : 0 < m := Real.rpow_pos_of_pos (div_pos hr.1 hbk) _
    have hmb : m ≤ b := by
      have : (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) ≤ (b ^ k₁) ^ ((k₁ : ℝ)⁻¹) := by
        refine Real.rpow_le_rpow (div_pos hr.1 hbk).le ?_ (by positivity)
        rw [div_le_iff₀ hbk, ← pow_add]; exact hr.2
      rwa [Real.pow_rpow_inv_natCast hb.le hk₁.ne'] at this
    have hlip' : ∀ u ∈ Icc (0 : ℝ) b, |Ψ u s - Ψ 0 s| ≤ C₁ * u * ((1 + s) * Real.exp (β * s * L)) :=
      fun u hu => hlip u hu s hs.le
    have hdec := uDensity_integral_eq β b L C₁ Ψ hΨc s hs.le hlip' m hm0 hmb
    -- `log(b/m) = (log R + log(1/r)) / k₁`
    have hlogm : Real.log (b / m) = (Real.log (b ^ (k₁ + k₂)) + Real.log (1 / r)) / k₁ := by
      rw [Real.log_div hb.ne' hm0.ne', hm, Real.log_rpow (div_pos hr.1 hbk),
        Real.log_div hr.1.ne' hbk.ne', Real.log_pow, Real.log_pow, one_div, Real.log_inv]
      push_cast
      field_simp
      ring
    -- the tail
    set T : ℝ := ∫ u in Ioc (0 : ℝ) m, u⁻¹ * (Ψ u s - Ψ 0 s) with hT
    have hTle : |T| ≤ m * (C₁ * ((1 + s) * Real.exp (β * s * L))) := by
      have hint := (axis_integrand_integrableOn β b L C₁ Ψ hΨc s hs.le hlip').mono_set
        (Ioc_subset_Ioc_right hmb)
      have hbnd : ∀ u ∈ Ioc (0 : ℝ) m, ‖u⁻¹ * (Ψ u s - Ψ 0 s)‖
          ≤ C₁ * ((1 + s) * Real.exp (β * s * L)) := by
        intro u hu
        have hu0 : u ≠ 0 := hu.1.ne'
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hu.1)]
        have := hlip' u ⟨hu.1.le, hu.2.trans hmb⟩
        calc u⁻¹ * |Ψ u s - Ψ 0 s| ≤ u⁻¹ * (C₁ * u * ((1 + s) * Real.exp (β * s * L))) :=
              mul_le_mul_of_nonneg_left this (inv_pos.2 hu.1).le
          _ = C₁ * ((1 + s) * Real.exp (β * s * L)) := by field_simp
      calc |T| = ‖T‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ u in Ioc (0 : ℝ) m, C₁ * ((1 + s) * Real.exp (β * s * L)) :=
            norm_integral_le_of_norm_le (integrableOn_const measure_Ioc_lt_top.ne)
              ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hbnd))
        _ = m * (C₁ * ((1 + s) * Real.exp (β * s * L))) := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le hm0.le, sub_zero, smul_eq_mul]
    -- assemble
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_one, pow_zero,
      mul_one]
    unfold uDensity uCoeff₀ uCoeff₁ uEnvelope
    rw [← hm, hdec, hlogm]
    have hexpr : 1 / (k₂ : ℝ) * r ^ (p - 1)
        * (Ψ 0 s * ((Real.log (b ^ (k₁ + k₂)) + Real.log (1 / r)) / k₁) + axisIntegral b Ψ s - T)
        - (r ^ (p - 1) * Real.log (1 / r) * (1 / ((k₁ : ℝ) * k₂) * Ψ 0 s)
          + r ^ (p - 1) * (1 / ((k₁ : ℝ) * k₂) * (Real.log (b ^ (k₁ + k₂)) * Ψ 0 s)
            + 1 / (k₂ : ℝ) * axisIntegral b Ψ s))
        = -(1 / (k₂ : ℝ) * r ^ (p - 1) * T) := by
      field_simp
      ring
    rw [hexpr, abs_neg, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / k₂),
      abs_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    -- `r^{p-1} m = r^{p+1/k₁-1} (b^{k₂})^{-1/k₁}`
    have hmr : m = r ^ ((k₁ : ℝ)⁻¹) * (b ^ k₂) ^ (-(k₁ : ℝ)⁻¹) := by
      rw [hm, Real.div_rpow hr.1.le hbk.le, Real.rpow_neg hbk.le, div_eq_mul_inv]
    have hrp : r ^ (p - 1) * r ^ ((k₁ : ℝ)⁻¹) = r ^ (p + (k₁ : ℝ)⁻¹ - 1) := by
      rw [← Real.rpow_add hr.1]; ring_nf
    have hlogr : (1 : ℝ) ≤ 1 + |Real.log r| := by linarith [abs_nonneg (Real.log r)]
    have hs' : |s| = s := abs_of_pos hs
    have hE0 : 0 ≤ C₁ * ((1 + s) * Real.exp (β * s * L)) :=
      mul_nonneg hC₁ (mul_nonneg (by linarith) (Real.exp_pos _).le)
    have hrp0 : 0 ≤ r ^ (p + (k₁ : ℝ)⁻¹ - 1) := Real.rpow_nonneg hr.1.le _
    have hbb : 0 ≤ (b ^ k₂) ^ (-(k₁ : ℝ)⁻¹) := Real.rpow_nonneg hbk.le _
    have hpre : 0 ≤ 1 / (k₂ : ℝ) * r ^ (p - 1) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg hr.1.le _)
    calc 1 / (k₂ : ℝ) * r ^ (p - 1) * |T|
        ≤ 1 / (k₂ : ℝ) * r ^ (p - 1) * (m * (C₁ * ((1 + s) * Real.exp (β * s * L)))) :=
          mul_le_mul_of_nonneg_left hTle hpre
      _ = r ^ (p + (k₁ : ℝ)⁻¹ - 1) * 1 * (C₁ / (k₂ : ℝ) * (b ^ k₂) ^ (-(k₁ : ℝ)⁻¹)
          * ((1 + |s|) * Real.exp (β * s * L))) := by
          rw [hmr, hs', ← hrp]; ring
      _ ≤ r ^ (p + (k₁ : ℝ)⁻¹ - 1) * (1 + |Real.log r|) * (C₁ / (k₂ : ℝ) * (b ^ k₂) ^ (-(k₁ : ℝ)⁻¹)
          * ((1 + |s|) * Real.exp (β * s * L))) := by
          have hK : 0 ≤ C₁ / (k₂ : ℝ) * (b ^ k₂) ^ (-(k₁ : ℝ)⁻¹)
              * ((1 + |s|) * Real.exp (β * s * L)) :=
            mul_nonneg (mul_nonneg (div_nonneg hC₁ hk₂'.le) hbb)
              (mul_nonneg (by positivity) (Real.exp_pos _).le)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogr hrp0) hK

/-- **Weighted-moment integrability with log powers**: if `|c s| ≤ e^{βsa'}(A + B s + D s²)` on
`(0,∞)`, the moment integrands of unit 83 are integrable for every log degree `j` and `γ > -1`. -/
theorem moment_integrableOn_of_bound' (β a' γ A B D : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (j : ℕ)
    (c : ℝ → ℝ) (hc : Measurable c)
    (hbound : ∀ s, 0 < s → |c s| ≤ Real.exp (β * s * a') * (A + B * s + D * s ^ 2)) :
    IntegrableOn (fun s => s ^ γ * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|))
      (Ioi 0) := by
  have h0 := logPowShift_weightedKernel_integrableOn β a' γ 1 hβ hγ j
  have h1 := logPowShift_weightedKernel_integrableOn β a' (γ + 1) 1 hβ (by linarith) j
  have h2 := logPowShift_weightedKernel_integrableOn β a' (γ + 2) 1 hβ (by linarith) j
  have hdom : IntegrableOn (fun s : ℝ =>
      A * ((1 + |Real.log s|) ^ j * (s ^ γ * quadKernel β a' s))
      + B * ((1 + |Real.log s|) ^ j * (s ^ (γ + 1) * quadKernel β a' s))
      + D * ((1 + |Real.log s|) ^ j * (s ^ (γ + 2) * quadKernel β a' s))) (Ioi 0) :=
    ((h0.const_mul A).add (h1.const_mul B)).add (h2.const_mul D)
  refine Integrable.mono' hdom ?_ ?_
  · exact (((measurable_id.pow_const _).mul ((measurable_const.add
      (continuous_abs.measurable.comp Real.measurable_log)).pow_const _)).mul
      ((Real.measurable_exp.comp (measurable_const.mul (measurable_id.pow_const _))).mul
        (continuous_abs.measurable.comp hc))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hsγ : 0 ≤ s ^ γ := Real.rpow_nonneg hs0.le _
    have hL : 0 ≤ (1 + |Real.log s|) ^ j := pow_nonneg (by positivity) _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg hsγ hL) (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)))]
    have hq : Real.exp (-β * s ^ 2) * Real.exp (β * s * a') = quadKernel β a' s :=
      exp_mul_exp_eq_quadKernel β a' s
    have hs1 : s ^ (γ + 1) = s ^ γ * s := by rw [Real.rpow_add hs0, Real.rpow_one]
    have hs2 : s ^ (γ + 2) = s ^ γ * s ^ 2 := by rw [Real.rpow_add hs0, Real.rpow_two]
    rw [hs1, hs2, ← hq]
    have := hbound s hs0
    have hE : 0 ≤ Real.exp (-β * s ^ 2) := (Real.exp_pos _).le
    calc s ^ γ * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|)
        ≤ s ^ γ * (1 + |Real.log s|) ^ j
          * (Real.exp (-β * s ^ 2) * (Real.exp (β * s * a') * (A + B * s + D * s ^ 2))) := by
          gcongr
      _ = _ := by ring

/-- A transferred term of log degree `1`: `N^{-α} (log N · M₀ − M₁)`. -/
theorem transferTerm_one (β α : ℝ) (c : ℝ → ℝ) (N : ℝ) :
    transferTerm β α 1 c N
      = N ^ (-α) * (Real.log N * logMoment β α 0 c - logMoment β α 1 c) := by
  unfold transferTerm
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one, Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, one_mul, mul_one, zero_add, neg_one_mul]
  ring

theorem logMoment_const_mul (β α : ℝ) (ℓ : ℕ) (κ : ℝ) (c : ℝ → ℝ) :
    logMoment β α ℓ (fun s => κ * c s) = κ * logMoment β α ℓ c := by
  unfold logMoment
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

theorem logMoment_add (β α : ℝ) (ℓ : ℕ) (c₁ c₂ : ℝ → ℝ)
    (h₁ : IntegrableOn (fun s => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c₁ s))
      (Ioi 0))
    (h₂ : IntegrableOn (fun s => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c₂ s))
      (Ioi 0)) :
    logMoment β α ℓ (fun s => c₁ s + c₂ s) = logMoment β α ℓ c₁ + logMoment β α ℓ c₂ := by
  unfold logMoment
  rw [← integral_add h₁ h₂]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

/-- The axis integral is bounded by `b C₁ (1+s) e^{βsL}`. -/
theorem axisIntegral_le (β b L C₁ : ℝ) (Ψ : ℝ → ℝ → ℝ) (hb : 0 < b) (s : ℝ) (hs : 0 ≤ s)
    (hlip : ∀ u ∈ Icc (0 : ℝ) b, |Ψ u s - Ψ 0 s| ≤ C₁ * u * ((1 + s) * Real.exp (β * s * L))) :
    |axisIntegral b Ψ s| ≤ b * (C₁ * ((1 + s) * Real.exp (β * s * L))) := by
  have hbnd : ∀ u ∈ Ioc (0 : ℝ) b, ‖u⁻¹ * (Ψ u s - Ψ 0 s)‖
      ≤ C₁ * ((1 + s) * Real.exp (β * s * L)) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.1.ne'
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hu.1)]
    have := hlip u ⟨hu.1.le, hu.2⟩
    calc u⁻¹ * |Ψ u s - Ψ 0 s| ≤ u⁻¹ * (C₁ * u * ((1 + s) * Real.exp (β * s * L))) :=
          mul_le_mul_of_nonneg_left this (inv_pos.2 hu.1).le
      _ = C₁ * ((1 + s) * Real.exp (β * s * L)) := by field_simp
  calc |axisIntegral b Ψ s| = ‖axisIntegral b Ψ s‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ u in Ioc (0 : ℝ) b, C₁ * ((1 + s) * Real.exp (β * s * L)) :=
        norm_integral_le_of_norm_le (integrableOn_const measure_Ioc_lt_top.ne)
          ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hbnd))
    _ = b * (C₁ * ((1 + s) * Real.exp (β * s * L))) := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hb.le, sub_zero, smul_eq_mul]

/-- The log coefficient `A_Ψ = (k₁k₂)⁻¹ ∫ s^{p-1} e^{-βs²} Ψ(0,s) ds`. -/
noncomputable def axisA (β p : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  1 / ((k₁ : ℝ) * k₂) * logMoment β p 0 (Ψ 0)

/-- The constant coefficient
`B_Ψ = (k₁k₂)⁻¹ ∫ s^{p-1} (log R − log s) e^{-βs²} Ψ(0,s) ds
      + k₂⁻¹ ∫ s^{p-1} e^{-βs²} I_Ψ(s) ds`. -/
noncomputable def axisB (β b p : ℝ) (k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  1 / ((k₁ : ℝ) * k₂) * (Real.log (b ^ (k₁ + k₂)) * logMoment β p 0 (Ψ 0)
    - logMoment β p 1 (Ψ 0)) + 1 / (k₂ : ℝ) * logMoment β p 0 (axisIntegral b Ψ)

/-- **The axis expansion**: for a one-variable amplitude `Ψ(u, s)`, Lipschitz in `u` at `0` and
of exponential type in `s`, `Z_Ψ(N) = N^{-p}(A_Ψ log N + B_Ψ) + O(N^{-(p+1/k₁)} (1 + log N))`. -/
theorem twoDAmp_uOnly_expansion (β b L C₁ M p : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hβ : 0 < β) (hb : 0 < b) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hC₁ : 0 ≤ C₁)
    (hΨc : Continuous (Function.uncurry Ψ))
    (hlip : ∀ u ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |Ψ u s - Ψ 0 s| ≤ C₁ * u * ((1 + s) * Real.exp (β * s * L)))
    (hΨ₀ : ∀ s, 0 ≤ s → |Ψ 0 s| ≤ M * Real.exp (β * s * L)) :
    ∃ K' : ℝ, ∀ N : ℝ, 1 ≤ N →
      |twoDAmp β b N h₁ h₂ k₁ k₂ (fun u _ s => Ψ u s)
        - N ^ (-p) * (axisA β p k₁ k₂ Ψ * Real.log N + axisB β b p k₁ k₂ Ψ)|
        ≤ K' * N ^ (-(p + (k₁ : ℝ)⁻¹)) * (1 + Real.log N) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hp0 : 0 < p := by rw [← hp₁]; positivity
  set R : ℝ := b ^ (k₁ + k₂) with hR
  have hD := uDensity_expansion β b L C₁ p k₁ k₂ Ψ hb hk₁ hk₂ hC₁ hΨc hlip
  have hΨ₀m : Measurable fun s => Ψ 0 s :=
    hΨc.measurable.comp (measurable_const.prodMk measurable_id)
  have hIm : Measurable (axisIntegral b Ψ) := axisIntegral_measurable b Ψ hΨc
  -- bounds on the coefficient functions
  have hc₀b : ∀ s, 0 < s → |uCoeff₀ k₁ k₂ Ψ s|
      ≤ Real.exp (β * s * L) * (1 / ((k₁ : ℝ) * k₂) * M + 0 * s + 0 * s ^ 2) := by
    intro s hs
    unfold uCoeff₀
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((k₁ : ℝ) * k₂))]
    have := hΨ₀ s hs.le
    calc 1 / ((k₁ : ℝ) * k₂) * |Ψ 0 s| ≤ 1 / ((k₁ : ℝ) * k₂) * (M * Real.exp (β * s * L)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hc₁b : ∀ s, 0 < s → |uCoeff₁ b k₁ k₂ Ψ s|
      ≤ Real.exp (β * s * L) * ((1 / ((k₁ : ℝ) * k₂) * (|Real.log R| * M) + 1 / (k₂ : ℝ) * (b * C₁))
        + (1 / (k₂ : ℝ) * (b * C₁)) * s + 0 * s ^ 2) := by
    intro s hs
    unfold uCoeff₁
    have hI := axisIntegral_le β b L C₁ Ψ hb s hs.le (fun u hu => hlip u hu s hs.le)
    have h0 := hΨ₀ s hs.le
    have hE := Real.exp_pos (β * s * L)
    have hk12 : (0 : ℝ) < 1 / ((k₁ : ℝ) * k₂) := by positivity
    have hk2 : (0 : ℝ) < 1 / (k₂ : ℝ) := by positivity
    calc |1 / ((k₁ : ℝ) * k₂) * (Real.log R * Ψ 0 s) + 1 / (k₂ : ℝ) * axisIntegral b Ψ s|
        ≤ |1 / ((k₁ : ℝ) * k₂) * (Real.log R * Ψ 0 s)| + |1 / (k₂ : ℝ) * axisIntegral b Ψ s| :=
          abs_add_le _ _
      _ = 1 / ((k₁ : ℝ) * k₂) * (|Real.log R| * |Ψ 0 s|) + 1 / (k₂ : ℝ) * |axisIntegral b Ψ s| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hk12, abs_of_pos hk2]
      _ ≤ 1 / ((k₁ : ℝ) * k₂) * (|Real.log R| * (M * Real.exp (β * s * L)))
          + 1 / (k₂ : ℝ) * (b * (C₁ * ((1 + s) * Real.exp (β * s * L)))) := by gcongr
      _ = _ := by ring
  have hHb : ∀ s, 0 < s → |uEnvelope β b L C₁ k₁ k₂ s|
      ≤ Real.exp (β * s * L) * (C₁ / (k₂ : ℝ) * (b ^ k₂) ^ (-(k₁ : ℝ)⁻¹)
        + (C₁ / (k₂ : ℝ) * (b ^ k₂) ^ (-(k₁ : ℝ)⁻¹)) * s + 0 * s ^ 2) := by
    intro s hs
    rw [abs_of_nonneg (hD.H_nonneg s)]
    unfold uEnvelope
    rw [abs_of_pos hs]
    ring_nf; rfl
  -- moment hypotheses
  have hMc : ∀ i, IntegrableOn (fun s => s ^ (![p, p] i - 1) * (1 + |Real.log s|) ^ (![1, 0] i : ℕ)
      * (Real.exp (-β * s ^ 2) * |(![uCoeff₀ k₁ k₂ Ψ, uCoeff₁ b k₁ k₂ Ψ] i) s|)) (Ioi 0) := by
    intro i
    fin_cases i
    · exact moment_integrableOn_of_bound' β L (p - 1) _ 0 0 hβ (by linarith) 1 _ (hD.c_meas 0) hc₀b
    · exact moment_integrableOn_of_bound' β L (p - 1) _ _ 0 hβ (by linarith) 0 _ (hD.c_meas 1) hc₁b
  have hMt : ∀ i, IntegrableOn (fun s => s ^ (p + (k₁ : ℝ)⁻¹ - 1)
      * (1 + |Real.log s|) ^ (![1, 0] i : ℕ)
      * (Real.exp (-β * s ^ 2) * |(![uCoeff₀ k₁ k₂ Ψ, uCoeff₁ b k₁ k₂ Ψ] i) s|)) (Ioi 0) := by
    intro i
    have hk₁inv : (0 : ℝ) < (k₁ : ℝ)⁻¹ := by positivity
    have hexp : (-1 : ℝ) < p + (k₁ : ℝ)⁻¹ - 1 := by linarith
    fin_cases i
    · exact moment_integrableOn_of_bound' β L _ _ 0 0 hβ hexp 1 _ (hD.c_meas 0) hc₀b
    · exact moment_integrableOn_of_bound' β L _ _ _ 0 hβ hexp 0 _ (hD.c_meas 1) hc₁b
  have hMH : IntegrableOn (fun s => s ^ (p + (k₁ : ℝ)⁻¹ - 1) * (1 + |Real.log s|) ^ 1
      * (Real.exp (-β * s ^ 2) * uEnvelope β b L C₁ k₁ k₂ s)) (Ioi 0) := by
    have hk₁inv : (0 : ℝ) < (k₁ : ℝ)⁻¹ := by positivity
    have hexp : (-1 : ℝ) < p + (k₁ : ℝ)⁻¹ - 1 := by linarith
    have := moment_integrableOn_of_bound' β L _ _ _ 0 hβ hexp 1 _ hD.H_meas hHb
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    beta_reduce
    rw [abs_of_nonneg (hD.H_nonneg s)]
  -- moment integrability of the pieces of `c₁` (for linearity)
  have hΨ₀int : ∀ ℓ, ℓ ≤ 1 → IntegrableOn (fun s => s ^ (p - 1) * Real.log s ^ ℓ
      * (Real.exp (-β * s ^ 2) * Ψ 0 s)) (Ioi 0) := by
    intro ℓ hℓ
    have hb' : ∀ s, 0 < s → |Ψ 0 s| ≤ Real.exp (β * s * L) * (M + 0 * s + 0 * s ^ 2) := by
      intro s hs; have := hΨ₀ s hs.le; linarith [show (0:ℝ) = 0 * s + 0 * s ^ 2 by ring]
    exact moment_integrand_integrableOn β p 1 ℓ (Ψ 0) hℓ hΨ₀m
      (moment_integrableOn_of_bound' β L (p - 1) M 0 0 hβ (by linarith) 1 _ hΨ₀m hb') _
      measurableSet_Ioi le_rfl
  have hIint : IntegrableOn (fun s => s ^ (p - 1) * Real.log s ^ 0
      * (Real.exp (-β * s ^ 2) * axisIntegral b Ψ s)) (Ioi 0) := by
    have hb' : ∀ s, 0 < s → |axisIntegral b Ψ s|
        ≤ Real.exp (β * s * L) * (b * C₁ + (b * C₁) * s + 0 * s ^ 2) := by
      intro s hs
      have := axisIntegral_le β b L C₁ Ψ hb s hs.le (fun u hu => hlip u hu s hs.le)
      calc |axisIntegral b Ψ s| ≤ b * (C₁ * ((1 + s) * Real.exp (β * s * L))) := this
        _ = _ := by ring
    exact moment_integrand_integrableOn β p 0 0 (axisIntegral b Ψ) le_rfl hIm
      (moment_integrableOn_of_bound' β L (p - 1) _ _ 0 hβ (by linarith) 0 _ hIm hb') _
      measurableSet_Ioi le_rfl
  -- the transferred terms
  have hT₀ : ∀ N : ℝ, transferTerm β p 1 (uCoeff₀ k₁ k₂ Ψ) N
      = N ^ (-p) * (Real.log N * (1 / ((k₁ : ℝ) * k₂) * logMoment β p 0 (Ψ 0))
        - 1 / ((k₁ : ℝ) * k₂) * logMoment β p 1 (Ψ 0)) := by
    intro N
    rw [transferTerm_one]
    unfold uCoeff₀
    rw [logMoment_const_mul, logMoment_const_mul]
  have hT₁ : ∀ N : ℝ, transferTerm β p 0 (uCoeff₁ b k₁ k₂ Ψ) N
      = N ^ (-p) * (1 / ((k₁ : ℝ) * k₂) * (Real.log R * logMoment β p 0 (Ψ 0))
        + 1 / (k₂ : ℝ) * logMoment β p 0 (axisIntegral b Ψ)) := by
    intro N
    rw [transferTerm_zero]
    unfold uCoeff₁
    have h1 : IntegrableOn (fun s => s ^ (p - 1) * Real.log s ^ 0
        * (Real.exp (-β * s ^ 2) * (1 / ((k₁ : ℝ) * k₂) * (Real.log R * Ψ 0 s)))) (Ioi 0) := by
      have this : IntegrableOn (fun s => (1 / ((k₁ : ℝ) * k₂) * Real.log R)
          * (s ^ (p - 1) * Real.log s ^ 0 * (Real.exp (-β * s ^ 2) * Ψ 0 s))) (Ioi 0) :=
        (hΨ₀int 0 (Nat.zero_le _)).const_mul (1 / ((k₁ : ℝ) * k₂) * Real.log R)
      refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
      beta_reduce; ring
    have h2 : IntegrableOn (fun s => s ^ (p - 1) * Real.log s ^ 0
        * (Real.exp (-β * s ^ 2) * (1 / (k₂ : ℝ) * axisIntegral b Ψ s))) (Ioi 0) := by
      have this : IntegrableOn (fun s => (1 / (k₂ : ℝ))
          * (s ^ (p - 1) * Real.log s ^ 0 * (Real.exp (-β * s ^ 2) * axisIntegral b Ψ s)))
          (Ioi 0) := hIint.const_mul (1 / (k₂ : ℝ))
      refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
      beta_reduce; ring
    rw [logMoment_add β p 0 _ _ h1 h2, logMoment_const_mul, logMoment_const_mul,
      logMoment_const_mul]
  -- apply the transfer theorem
  refine ⟨envMoment β (p + (k₁ : ℝ)⁻¹) 1 (uEnvelope β b L C₁ k₁ k₂)
    + ∑ i, R ^ (![p, p] i - (p + (k₁ : ℝ)⁻¹)) * tailMoment β (p + (k₁ : ℝ)⁻¹) (![1, 0] i)
      (![uCoeff₀ k₁ k₂ Ψ, uCoeff₁ b k₁ k₂ Ψ] i), fun N hN => ?_⟩
  have hmain := densityTransfer_bound hD β hMc hMt hMH N hN
  rw [pow_one] at hmain
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hmain
  rw [hT₀, hT₁, ← twoDAmp_uOnly_eq_transferZ β b N p h₁ h₂ k₁ k₂ hβ.le hb (by linarith) hk₁ hk₂
    hp₁ hp₂ Ψ hΨc] at hmain
  have hgoal : N ^ (-p) * (axisA β p k₁ k₂ Ψ * Real.log N + axisB β b p k₁ k₂ Ψ)
      = N ^ (-p) * (Real.log N * (1 / ((k₁ : ℝ) * k₂) * logMoment β p 0 (Ψ 0))
          - 1 / ((k₁ : ℝ) * k₂) * logMoment β p 1 (Ψ 0))
        + N ^ (-p) * (1 / ((k₁ : ℝ) * k₂) * (Real.log R * logMoment β p 0 (Ψ 0))
          + 1 / (k₂ : ℝ) * logMoment β p 0 (axisIntegral b Ψ)) := by
    unfold axisA axisB; ring
  rw [hgoal]
  calc _ ≤ _ := hmain
    _ = _ := by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring

end Laplace.Grammar
