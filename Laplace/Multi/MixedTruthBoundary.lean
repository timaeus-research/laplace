/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MixedTruthExport

/-!
# The critical-boundary regression of the mixed truth

Astra's round-15 regression (item 3): the mixed truth `T = z₀ z₁` with the phase `F = a z₁`
(`a > 0`), vanishing on the whole axis `z₁ = 0` of the wall, and the monomial observable
`z₀^q z₁^p ψ`. Along the ray `s = σ/t` the fibre kernel decays like `t^{-p}` with an
incomplete-Gamma coefficient:

`t^p K_t(σ/t) → σ^q ∫_{2σ}^∞ u^{p-q-1} e^{-au} ψ(σ/u, 0) du`

(`mix_tendsto_totalKernel_boundary`). The mass sits on the whole segment `{z₁ = 0}` of the wall
(the phase is tied along it), weighted by `u ↦ ψ(σ/u, 0)`: the fibre `z₀ z₁ = σ/t` is
parametrised by `z₁ = u/t`, `z₀ = σ/u`, and `e^{-t a z₁} = e^{-au}` is scale-free. The proof is
the substitution `x = u/t` in the explicit kernel `∫_{2s}^{1/2} g(s/x, x) dx/x` followed by
dominated convergence on `(2σ, ∞)`. The transport to the resolution-produced chart data over the
thin region (`exported_mix_totalKernel_eq`, factored out of `exported_mix_tendsto_totalKernel`)
gives the same limit for every `TruthChartsData 1 (z₀ z₁) (mixThin ε)`
(`exported_mix_tendsto_totalKernel_boundary`). With `p = q + 1` the coefficient is
`σ^q ∫_{2σ}^∞ e^{-au} du = σ^q e^{-2aσ}/a`; the lower limit `2σ` is the size `1/2` of the box.
-/

open Filter MeasureTheory Set Topology Real
open scoped ENNReal

namespace Laplace.Multi

/-- Integrability of `u^e e^{-au}` on `(c, ∞)` for `c > 0`, `a > 0` and any real exponent. -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {e a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ ↦ u ^ e * exp (-(a * u))) (Ioi c) := by
  have hcont : ContinuousOn (fun u : ℝ ↦ u ^ e * exp (-(a * u))) (Ioi c) :=
    (continuousOn_id.rpow_const fun u hu ↦ Or.inl (hc.trans hu).ne').mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
  rcases le_or_gt e 0 with he | he
  · have hint : IntegrableOn (fun u : ℝ ↦ c ^ e * exp (-a * u)) (Ioi c) :=
      (exp_neg_integrableOn_Ioi c ha).const_mul (c ^ e)
    refine hint.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu ↦ ?_)
    have hu : c < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hc.trans hu).le _)
      (exp_pos _).le), neg_mul]
    exact mul_le_mul_of_nonneg_right
      (antitoneOn_rpow_Ioi_of_exponent_nonpos he hc (hc.trans hu) hu.le) (exp_pos _).le
  · have hint := (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < e) one_pos ha).mono_set
      (Ioi_subset_Ioi hc.le)
    refine hint.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]

/-- The transport of the mixed kernel from the closed square to any chart data over the thin
region, for a nonnegative continuous observable supported in the closed square and a truth value
`s` inside the cutoff window. -/
theorem exported_mix_totalKernel_eq {ε : ℝ} (hε : 0 < ε)
    (D : TruthChartsData 1 (fun z ↦ z 0 * z 1) (mixThin ε)) {s : ℝ} (hs : 0 < s)
    (hsε : |s| ≤ ε / 2) {θr : (Fin 2 → ℝ) → ℝ} (hθrc : Continuous θr) (hθrn : ∀ z, 0 ≤ θr z)
    (hθrL : ∀ z, θr z ≠ 0 → z ∈ mixLc) :
    D.totalKernel (fun z ↦ ENNReal.ofReal (θr z)) s =
      mixData.totalKernel (fun z ↦ ENNReal.ofReal (θr z)) s := by
  have hT : Measurable fun z : Fin 2 → ℝ ↦ z 0 * z 1 := continuous_mixTruth.measurable
  set θ : (Fin 2 → ℝ) → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (θr z) with hθ
  set θε : (Fin 2 → ℝ) → ℝ≥0∞ :=
    fun z ↦ θ z * ENNReal.ofReal (truthCutoff ε (z 0 * z 1)) with hθε
  have hθc : Continuous θ := ENNReal.continuous_ofReal.comp hθrc
  have hθεc : Continuous θε := by
    have e : θε = fun z ↦ ENNReal.ofReal (θr z * truthCutoff ε (z 0 * z 1)) := by
      funext z
      simp only [hθε, hθ]
      rw [ENNReal.ofReal_mul (hθrn z)]
    rw [e]
    exact ENNReal.continuous_ofReal.comp
      (hθrc.mul ((continuous_truthCutoff ε).comp continuous_mixTruth))
  obtain ⟨C, hC⟩ := isCompact_mixLc.exists_bound_of_continuousOn hθrc.continuousOn
  have hθb : ∀ z, θ z ≤ ENNReal.ofReal C := fun z ↦ by
    by_cases hz : z ∈ mixLc
    · exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hC z hz))
    · have : θr z = 0 := by
        by_contra h
        exact hz (hθrL z h)
      simp only [hθ, this, ENNReal.ofReal_zero]
      exact zero_le
  have hθεb : ∀ z, θε z ≤ ENNReal.ofReal C := fun z ↦ by
    refine (mul_le_of_le_one_right zero_le ?_).trans (hθb z)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (truthCutoff_le_one _ _)
  have hθεL : ∀ z, θε z ≠ 0 → z ∈ mixLc ∩ mixThin ε := fun z hz ↦ by
    have h1 : θ z ≠ 0 := fun h ↦ hz (by simp only [hθε, h, zero_mul])
    have h2 : truthCutoff ε (z 0 * z 1) ≠ 0 := fun h ↦ hz (by
      simp only [hθε, h, ENNReal.ofReal_zero, mul_zero])
    have hzL : z ∈ mixLc := hθrL z fun h ↦ h1 (by simp only [hθ, h, ENNReal.ofReal_zero])
    exact ⟨hzL, mixLc_subset hzL, (abs_lt_of_truthCutoff_ne_zero hε h2).le⟩
  have hae := TruthChartsData.totalKernel_ae_eq_of_support mixDataC D hT measurableSet_mixLc
    (measurableSet_mixThin ε) hθεc.measurable hθεL
  have heq : mixDataC.totalKernel θε s = D.totalKernel θε s :=
    eq_of_ae_eq_of_continuousAt hae
      (mixDataC.continuousAt_totalKernel hθεc ENNReal.ofReal_ne_top hθεb
        (fun z hz ↦ (hθεL z hz).1) hs.ne')
      (D.continuousAt_totalKernel hθεc ENNReal.ofReal_ne_top hθεb
        (fun z hz ↦ (hθεL z hz).2) hs.ne')
  have hcut : ∀ {L : Set (Fin 2 → ℝ)} (D' : TruthChartsData 1 (fun z ↦ z 0 * z 1) L),
      D'.totalKernel θε s = D'.totalKernel θ s := fun D' ↦ by
    rw [hθε, TruthChartsData.totalKernel_mul_comp_truth D' θ
      (fun s ↦ ENNReal.ofReal (truthCutoff ε s)) ENNReal.ofReal_ne_top,
      truthCutoff_eq_one hε hsε, ENNReal.ofReal_one, one_mul]
  rw [hcut, hcut] at heq
  rw [← heq, mixDataC_totalKernel_eq hs]

/-- The boundary observable `e^{-t a z₁} z₀^q z₁^p ψ(z)` is nonnegative when `ψ ≥ 0` is
supported in the closed square. -/
theorem boundaryObs_nonneg {a t : ℝ} {p q : ℕ} {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ∀ z, 0 ≤ ψ z)
    (hψL : ∀ z, ψ z ≠ 0 → z ∈ mixLc) (z : Fin 2 → ℝ) :
    0 ≤ exp (-(t * (a * z 1))) * (z 0 ^ q * z 1 ^ p * ψ z) := by
  refine mul_nonneg (exp_pos _).le ?_
  by_cases hz : ψ z = 0
  · simp [hz]
  · have hm := hψL z hz
    exact mul_nonneg (mul_nonneg (pow_nonneg hm.1.1 q) (pow_nonneg hm.2.1 p)) (hψ z)

/-- **The critical-boundary regression, record level.** For the phase `F = a z₁` (`a > 0`) and
the observable `z₀^q z₁^p ψ` along the ray `s = σ/t`, `t^p` times the fibre kernel converges to
`σ^q ∫_{2σ}^∞ u^{p-q-1} e^{-au} ψ(σ/u, 0) du`. -/
theorem mix_tendsto_totalKernel_boundary {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) (p q : ℕ)
    {ψ : (Fin 2 → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z)
    (hψL : ∀ z, ψ z ≠ 0 → z ∈ mixLc) :
    Tendsto (fun t ↦ t ^ p * (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (a * z 1))) * (z 0 ^ q * z 1 ^ p * ψ z)))
        (σ / t)).toReal)
      atTop (𝓝 (σ ^ q * ∫ u in Ioi (2 * σ),
        u ^ ((p : ℝ) - q - 1) * exp (-(a * u)) * ψ ![σ / u, 0])) := by
  set e : ℝ := (p : ℝ) - q - 1 with he_def
  -- the rescaled integrand
  set G : ℝ → ℝ → ℝ := fun t u ↦ u ^ e * exp (-(a * u)) * ψ ![σ / u, u / t] with hG
  set G₀ : ℝ → ℝ := fun u ↦ u ^ e * exp (-(a * u)) * ψ ![σ / u, 0] with hG₀
  -- a bound for `ψ`
  obtain ⟨C, hC⟩ := isCompact_mixLc.exists_bound_of_continuousOn hψc.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 zero_mem_mixLc)
  have hψb : ∀ z, |ψ z| ≤ C := fun z ↦ by
    by_cases hz : z ∈ mixLc
    · exact (Real.norm_eq_abs _).symm ▸ hC z hz
    · have : ψ z = 0 := by
        by_contra h
        exact hz (hψL z h)
      rw [this, abs_zero]
      exact hC0
  -- Step 1: the exact rescaling for `t ≥ 4σ`
  have hkey : ∀ t : ℝ, 4 * σ ≤ t →
      t ^ p * (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (a * z 1))) * (z 0 ^ q * z 1 ^ p * ψ z)))
        (σ / t)).toReal = σ ^ q * ∫ u in (2 * σ)..(t / 2), G t u := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hs : 0 < σ / t := div_pos hσ ht0
    have h2σ : 2 * (σ / t) ≤ 1 / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ ht0]
      linarith
    rw [mixData_totalKernel_toReal (by fun_prop) (boundaryObs_nonneg hψ hψL) hs,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2σ]
    have hsub := intervalIntegral.integral_comp_div (a := 2 * σ) (b := t / 2)
      (f := fun x ↦ exp (-(t * (a * (![σ / t / x, x] : Fin 2 → ℝ) 1))) *
        ((![σ / t / x, x] : Fin 2 → ℝ) 0 ^ q * (![σ / t / x, x] : Fin 2 → ℝ) 1 ^ p *
          ψ ![σ / t / x, x]) / x) ht0.ne'
    rw [show 2 * (σ / t) = 2 * σ / t by ring, show (1 : ℝ) / 2 = t / 2 / t by field_simp]
    rw [show (∫ x in 2 * σ / t..t / 2 / t,
        exp (-(t * (a * (![σ / t / x, x] : Fin 2 → ℝ) 1))) *
          ((![σ / t / x, x] : Fin 2 → ℝ) 0 ^ q * (![σ / t / x, x] : Fin 2 → ℝ) 1 ^ p *
            ψ ![σ / t / x, x]) / x) = t⁻¹ * ∫ u in (2 * σ)..(t / 2),
        exp (-(t * (a * (![σ / t / (u / t), u / t] : Fin 2 → ℝ) 1))) *
          ((![σ / t / (u / t), u / t] : Fin 2 → ℝ) 0 ^ q *
            (![σ / t / (u / t), u / t] : Fin 2 → ℝ) 1 ^ p * ψ ![σ / t / (u / t), u / t]) /
          (u / t) by
      rw [eq_inv_mul_iff_mul_eq₀ ht0.ne', ← smul_eq_mul, ← hsub]]
    rw [← mul_assoc, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [Set.uIcc_of_le (by linarith)] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    simp only [hG, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e1 : σ / t / (u / t) = σ / u := by field_simp
    have e2 : t * (a * (u / t)) = a * u := by field_simp
    rw [e1, e2, he_def, Real.rpow_sub hu0, Real.rpow_sub hu0, Real.rpow_natCast,
      Real.rpow_natCast, Real.rpow_one, div_pow, div_pow]
    field_simp
  -- Step 2: dominated convergence on `(2σ, ∞)`
  have hbound_int : IntegrableOn (fun u : ℝ ↦ C * (u ^ e * exp (-(a * u)))) (Ioi (2 * σ)) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi ha (by linarith)).const_mul C
  have hGcont : ∀ t, ContinuousOn (G t) (Ioi (2 * σ)) := fun t ↦ by
    refine ((continuousOn_id.rpow_const fun u hu ↦ Or.inl (by
      have : 2 * σ < u := hu
      exact (by linarith : (0:ℝ) < u).ne')).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn).mul
      (hψc.comp_continuousOn ?_)
    refine continuousOn_pi.2 fun i ↦ ?_
    fin_cases i
    · exact continuousOn_const.div continuousOn_id fun u hu ↦ by
        have : 2 * σ < u := hu
        exact (by linarith : (0:ℝ) < u).ne'
    · exact continuousOn_id.div_const _
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (2 * σ))) (l := atTop)
    (F := fun t u ↦ (Iic (t / 2)).indicator (G t) u) (f := G₀)
    (fun u ↦ C * (u ^ e * exp (-(a * u))))
    (Eventually.of_forall fun t ↦
      ((hGcont t).aestronglyMeasurable measurableSet_Ioi).indicator measurableSet_Iic)
    (Eventually.of_forall fun t ↦
      (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu ↦ ?_))
    hbound_int
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu ↦ ?_))
  · refine ((hdct.const_mul (σ ^ q)).congr' ?_)
    filter_upwards [eventually_ge_atTop (4 * σ)] with t ht
    rw [hkey t ht]
    congr 1
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      inter_comm, Ioi_inter_Iic, intervalIntegral.integral_of_le (by linarith)]
  · -- the bound
    have hu' : 2 * σ < u := hu
    have hu0 : 0 < u := by linarith
    have hnn : 0 ≤ u ^ e * exp (-(a * u)) :=
      mul_nonneg (Real.rpow_nonneg hu0.le _) (exp_pos _).le
    refine (norm_indicator_le_norm_self _ _).trans ?_
    simp only [hG]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    calc u ^ e * exp (-(a * u)) * |ψ ![σ / u, u / t]| ≤ u ^ e * exp (-(a * u)) * C :=
          mul_le_mul_of_nonneg_left (hψb _) hnn
      _ = C * (u ^ e * exp (-(a * u))) := by ring
  · -- the pointwise limit
    have hu' : 2 * σ < u := hu
    have hev : ∀ᶠ t in atTop, (Iic (t / 2)).indicator (G t) u = G t u := by
      filter_upwards [eventually_ge_atTop (2 * u)] with t ht
      exact indicator_of_mem (by simp only [mem_Iic]; linarith) _
    refine Tendsto.congr' (hev.mono fun t h ↦ h.symm) ?_
    simp only [hG, hG₀]
    refine Tendsto.mul tendsto_const_nhds ?_
    refine hψc.continuousAt.tendsto.comp ?_
    refine tendsto_pi_nhds.2 fun i ↦ ?_
    fin_cases i
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds.div_atTop tendsto_id

/-- **The critical-boundary regression for the exported chart data.** Every chart system for the
mixed truth over the thin region `mixThin ε` — in particular the one produced by the resolution
of `z₀ z₁ · a z₁` — has the incomplete-Gamma coefficient
`σ^q ∫_{2σ}^∞ u^{p-q-1} e^{-au} ψ(σ/u, 0) du` at the scale `t^{-p}`. -/
theorem exported_mix_tendsto_totalKernel_boundary {ε : ℝ} (hε : 0 < ε)
    (D : TruthChartsData 1 (fun z ↦ z 0 * z 1) (mixThin ε)) {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (p q : ℕ) {ψ : (Fin 2 → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z)
    (hψL : ∀ z, ψ z ≠ 0 → z ∈ mixLc) :
    Tendsto (fun t ↦ t ^ p * (D.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (a * z 1))) * (z 0 ^ q * z 1 ^ p * ψ z)))
        (σ / t)).toReal)
      atTop (𝓝 (σ ^ q * ∫ u in Ioi (2 * σ),
        u ^ ((p : ℝ) - q - 1) * exp (-(a * u)) * ψ ![σ / u, 0])) := by
  refine (mix_tendsto_totalKernel_boundary hσ ha p q hψc hψ hψL).congr' ?_
  filter_upwards [eventually_gt_atTop (max 1 (2 * σ / ε))] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans ht.le)
  have hs : 0 < σ / t := div_pos hσ ht0
  have hsε : |σ / t| ≤ ε / 2 := by
    rw [abs_of_pos hs, div_le_iff₀ ht0]
    have h2 : 2 * σ / ε < t := (le_max_right _ _).trans_lt ht
    rw [div_lt_iff₀ hε] at h2
    linarith
  have hL : ∀ z, exp (-(t * (a * z 1))) * (z 0 ^ q * z 1 ^ p * ψ z) ≠ 0 → z ∈ mixLc :=
    fun z hz ↦ hψL z fun h ↦ hz (by simp [h])
  rw [exported_mix_totalKernel_eq hε D hs hsε (by fun_prop) (boundaryObs_nonneg hψ hψL) hL]

end Laplace.Multi
