/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MixedTruthExport

/-!
# The critical-boundary regression of the mixed truth

Astra's round-15 regression (item 3), repaired after the round-16 audit: the mixed truth
`T = z₀ z₁` with the phase `F = a(z) z₁` (`a` continuous and positive on the closed square),
vanishing on the whole axis `z₁ = 0` of the wall, and the monomial observable `z₀^q z₁^p ψ`
with `ψ ≥ 0` continuous — with NO support hypothesis on `ψ`: the restriction to the square is
internal to the record `mixData` (its kernel only evaluates the observable on the fibre points
`(s/x, x)`, `x ∈ [2s, 1/2]`), and a globally continuous observable supported in the closed square
would vanish on the boundary segment `z₁ = 0` that carries the limit. Along the ray `s = σ/t`
the fibre kernel decays like `t^{-p}` with an incomplete-Gamma coefficient that sees the
observable and the unit along the whole segment:

`t^p K_t(σ/t) → σ^q ∫_{2σ}^∞ u^{p-q-1} e^{-u a(σ/u, 0)} ψ(σ/u, 0) du`

(`mix_tendsto_totalKernel_boundary`); the fibre is parametrised by `z₁ = u/t`, `z₀ = σ/u`, on
which `e^{-t a z₁} = e^{-u a}`. With constant unit, `ψ ≡ 1` and `p = q + 1` the limit is the
positive constant `σ^q e^{-2aσ}/a` (`mix_tendsto_totalKernel_boundary_const`), the acceptance
value for the certificate route; the lower limit `2σ` is the size `1/2` of the box. The proof is
the substitution `x = u/t` in the explicit kernel `∫_{2s}^{1/2} g(s/x, x) dx/x`
(`mixData_totalKernel_toReal'`, needing nonnegativity only on the positive quadrant) followed by
dominated convergence on `(2σ, ∞)` against `C u^{p-q-1} e^{-a_min u}`.

`exported_mix_totalKernel_eq` factors the transport step of `exported_mix_tendsto_totalKernel`
(observables supported in the closed square). It does NOT give an exported form of the boundary
regression with a nonzero limit: a continuous observable supported in the square has zero
boundary trace, and for an observable not supported in the region the pointwise identification
of two chart kernels at `s = σ/t` (as opposed to their a.e. equality) is not available — the
"pointwise chart-independence of fibre evaluations" item of the round-16 audit.
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

/-- The real form of the mixed kernel for a continuous integrand that is nonnegative on the
positive quadrant `mixL'` (the kernel only evaluates it there). -/
theorem mixData_totalKernel_toReal' {g : (Fin 2 → ℝ) → ℝ} (hgc : Continuous g)
    (hg : ∀ z ∈ mixL', 0 ≤ g z) {s : ℝ} (hs : 0 < s) :
    (mixData.totalKernel (fun z ↦ ENNReal.ofReal (g z)) s).toReal =
      ∫ x in Icc (2 * s) (1 / 2), g ![s / x, x] / x := by
  rw [mixData_totalKernel hs]
  have hmem : ∀ x ∈ Icc (2 * s) (1 / 2), (![s / x, x] : Fin 2 → ℝ) ∈ mixL' := fun x hx ↦ by
    have hx0 : 0 < x := by linarith [hx.1]
    rw [mem_mixL'_iff]
    refine ⟨⟨div_pos hs hx0, ?_⟩, hx0, hx.2⟩
    rw [div_le_iff₀ hx0]
    linarith [hx.1]
  have hvec : ContinuousOn (fun x : ℝ ↦ (![s / x, x] : Fin 2 → ℝ)) (Icc (2 * s) (1 / 2)) := by
    refine continuousOn_pi.2 fun i ↦ ?_
    fin_cases i
    · exact continuousOn_const.div continuousOn_id fun x hx ↦ by
        have := hx.1
        exact (by linarith : (0 : ℝ) < x).ne'
    · exact continuousOn_id
  have hcont : ContinuousOn (fun x : ℝ ↦ g ![s / x, x] / x) (Icc (2 * s) (1 / 2)) :=
    (hgc.comp_continuousOn hvec).div continuousOn_id fun x hx ↦ by
      have := hx.1
      exact (by linarith : (0 : ℝ) < x).ne'
  have hint : IntegrableOn (fun x : ℝ ↦ g ![s / x, x] / x) (Icc (2 * s) (1 / 2)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (2 * s) (1 / 2))] fun x : ℝ ↦ g ![s / x, x] / x := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun x hx ↦ ?_)
    have := hx.1
    exact div_nonneg (hg _ (hmem x hx)) (by linarith)
  have h1 : ∫⁻ x in Icc (2 * s) (1 / 2), ENNReal.ofReal (g ![s / x, x]) * ENNReal.ofReal (1 / x) =
      ∫⁻ x in Icc (2 * s) (1 / 2), ENNReal.ofReal (g ![s / x, x] / x) :=
    setLIntegral_congr_fun measurableSet_Icc fun x hx ↦ by
      rw [← ENNReal.ofReal_mul (hg _ (hmem x hx)), mul_one_div]
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)]

/-- The boundary observable `e^{-t a(z) z₁} z₀^q z₁^p ψ(z)` is nonnegative on the positive
quadrant when `ψ ≥ 0`. -/
theorem boundaryObs_nonneg {a ψ : (Fin 2 → ℝ) → ℝ} {t : ℝ} {p q : ℕ} (hψ : ∀ z, 0 ≤ ψ z)
    (z : Fin 2 → ℝ) (hz : z ∈ mixL') :
    0 ≤ exp (-(t * (a z * z 1))) * (z 0 ^ q * z 1 ^ p * ψ z) :=
  mul_nonneg (exp_pos _).le
    (mul_nonneg (mul_nonneg (pow_nonneg hz.1.1.le q) (pow_nonneg hz.2.1.le p)) (hψ z))

/-- **The critical-boundary regression, record level.** For the phase `F = a(z) z₁` (`a`
continuous, positive on the closed square) and the observable `z₀^q z₁^p ψ` (`ψ ≥ 0` continuous,
no support hypothesis) along the ray `s = σ/t`, `t^p` times the fibre kernel converges to
`σ^q ∫_{2σ}^∞ u^{p-q-1} e^{-u a(σ/u, 0)} ψ(σ/u, 0) du`. -/
theorem mix_tendsto_totalKernel_boundary {σ : ℝ} (hσ : 0 < σ) {a ψ : (Fin 2 → ℝ) → ℝ}
    (hac : Continuous a) (ha : ∀ z ∈ mixLc, 0 < a z) (p q : ℕ) (hψc : Continuous ψ)
    (hψ : ∀ z, 0 ≤ ψ z) :
    Tendsto (fun t ↦ t ^ p * (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (a z * z 1))) * (z 0 ^ q * z 1 ^ p * ψ z)))
        (σ / t)).toReal)
      atTop (𝓝 (σ ^ q * ∫ u in Ioi (2 * σ),
        u ^ ((p : ℝ) - q - 1) * exp (-(u * a ![σ / u, 0])) * ψ ![σ / u, 0])) := by
  set e : ℝ := (p : ℝ) - q - 1 with he_def
  -- the rescaled integrand
  set G : ℝ → ℝ → ℝ :=
    fun t u ↦ u ^ e * exp (-(u * a ![σ / u, u / t])) * ψ ![σ / u, u / t] with hG
  set G₀ : ℝ → ℝ := fun u ↦ u ^ e * exp (-(u * a ![σ / u, 0])) * ψ ![σ / u, 0] with hG₀
  -- bounds for `ψ` and `a` on the square
  obtain ⟨C, hC⟩ := isCompact_mixLc.exists_bound_of_continuousOn hψc.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 zero_mem_mixLc)
  obtain ⟨z₀, hz₀, hmin⟩ := isCompact_mixLc.exists_isMinOn ⟨0, zero_mem_mixLc⟩ hac.continuousOn
  set amin : ℝ := a z₀ with hamin_def
  have hamin : 0 < amin := ha z₀ hz₀
  have hage : ∀ z ∈ mixLc, amin ≤ a z := fun z hz ↦ hmin hz
  have hpt : ∀ t u : ℝ, 2 * σ ≤ u → u ≤ t / 2 → (![σ / u, u / t] : Fin 2 → ℝ) ∈ mixLc := by
    intro t u hu1 hu2
    have hu0 : 0 < u := by linarith
    have ht0 : 0 < t := by linarith
    rw [mem_mixLc_iff]
    refine ⟨⟨(div_pos hσ hu0).le, ?_⟩, (div_pos hu0 ht0).le, ?_⟩
    · rw [div_le_iff₀ hu0]
      linarith
    · rw [div_le_iff₀ ht0]
      linarith
  -- Step 1: the exact rescaling for `t ≥ 4σ`
  have hkey : ∀ t : ℝ, 4 * σ ≤ t →
      t ^ p * (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (a z * z 1))) * (z 0 ^ q * z 1 ^ p * ψ z)))
        (σ / t)).toReal = σ ^ q * ∫ u in (2 * σ)..(t / 2), G t u := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hs : 0 < σ / t := div_pos hσ ht0
    have h2σ : 2 * (σ / t) ≤ 1 / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ ht0]
      linarith
    rw [mixData_totalKernel_toReal' (by fun_prop) (boundaryObs_nonneg hψ) hs,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2σ]
    have hsub := intervalIntegral.integral_comp_div (a := 2 * σ) (b := t / 2)
      (f := fun x ↦ exp (-(t * (a ![σ / t / x, x] * (![σ / t / x, x] : Fin 2 → ℝ) 1))) *
        ((![σ / t / x, x] : Fin 2 → ℝ) 0 ^ q * (![σ / t / x, x] : Fin 2 → ℝ) 1 ^ p *
          ψ ![σ / t / x, x]) / x) ht0.ne'
    rw [show 2 * (σ / t) = 2 * σ / t by ring, show (1 : ℝ) / 2 = t / 2 / t by field_simp]
    rw [show (∫ x in 2 * σ / t..t / 2 / t,
        exp (-(t * (a ![σ / t / x, x] * (![σ / t / x, x] : Fin 2 → ℝ) 1))) *
          ((![σ / t / x, x] : Fin 2 → ℝ) 0 ^ q * (![σ / t / x, x] : Fin 2 → ℝ) 1 ^ p *
            ψ ![σ / t / x, x]) / x) = t⁻¹ * ∫ u in (2 * σ)..(t / 2),
        exp (-(t * (a ![σ / t / (u / t), u / t] *
            (![σ / t / (u / t), u / t] : Fin 2 → ℝ) 1))) *
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
    have e2 : t * (a ![σ / u, u / t] * (u / t)) = u * a ![σ / u, u / t] := by field_simp
    rw [e1, e2, he_def, Real.rpow_sub hu0, Real.rpow_sub hu0, Real.rpow_natCast,
      Real.rpow_natCast, Real.rpow_one, div_pow, div_pow]
    field_simp
  -- Step 2: dominated convergence on `(2σ, ∞)`
  have hbound_int : IntegrableOn (fun u : ℝ ↦ C * (u ^ e * exp (-(amin * u)))) (Ioi (2 * σ)) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi hamin (by linarith)).const_mul C
  have hvec : ∀ t : ℝ, ContinuousOn (fun u : ℝ ↦ (![σ / u, u / t] : Fin 2 → ℝ)) (Ioi (2 * σ)) := by
    intro t
    refine continuousOn_pi.2 fun i ↦ ?_
    fin_cases i
    · exact continuousOn_const.div continuousOn_id fun u hu ↦ by
        have : 2 * σ < u := hu
        exact (by linarith : (0:ℝ) < u).ne'
    · exact continuousOn_id.div_const _
  have hGcont : ∀ t, ContinuousOn (G t) (Ioi (2 * σ)) := fun t ↦
    (((continuousOn_id.rpow_const fun u hu ↦ Or.inl (by
      have : 2 * σ < u := hu
      exact (by linarith : (0:ℝ) < u).ne')).mul
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_id.mul (hac.comp_continuousOn (hvec t))).neg)).mul
      (hψc.comp_continuousOn (hvec t)))
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (2 * σ))) (l := atTop)
    (F := fun t u ↦ (Iic (t / 2)).indicator (G t) u) (f := G₀)
    (fun u ↦ C * (u ^ e * exp (-(amin * u))))
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
    have hnn : 0 ≤ u ^ e * exp (-(amin * u)) :=
      mul_nonneg (Real.rpow_nonneg hu0.le _) (exp_pos _).le
    by_cases hut : u ∈ Iic (t / 2)
    · rw [indicator_of_mem hut]
      have hmem := hpt t u hu'.le hut
      simp only [hG]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu0.le _)
        (exp_pos _).le)]
      have hexp : exp (-(u * a ![σ / u, u / t])) ≤ exp (-(amin * u)) := by
        rw [Real.exp_le_exp]
        nlinarith [hage _ hmem, hu0]
      calc u ^ e * exp (-(u * a ![σ / u, u / t])) * |ψ ![σ / u, u / t]|
          ≤ u ^ e * exp (-(amin * u)) * C := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hu0.le _)) ?_
              (abs_nonneg _) hnn
            exact (Real.norm_eq_abs _).symm ▸ hC _ hmem
        _ = C * (u ^ e * exp (-(amin * u))) := by ring
    · rw [indicator_of_notMem hut, norm_zero]
      exact mul_nonneg hC0 hnn
  · -- the pointwise limit
    have hu' : 2 * σ < u := hu
    have hev : ∀ᶠ t in atTop, (Iic (t / 2)).indicator (G t) u = G t u := by
      filter_upwards [eventually_ge_atTop (2 * u)] with t ht
      exact indicator_of_mem (by simp only [mem_Iic]; linarith) _
    refine Tendsto.congr' (hev.mono fun t h ↦ h.symm) ?_
    simp only [hG, hG₀]
    have hv : Tendsto (fun t : ℝ ↦ (![σ / u, u / t] : Fin 2 → ℝ)) atTop (𝓝 ![σ / u, 0]) := by
      refine tendsto_pi_nhds.2 fun i ↦ ?_
      fin_cases i
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds.div_atTop tendsto_id
    refine (Tendsto.mul tendsto_const_nhds ?_).mul (hψc.continuousAt.tendsto.comp hv)
    exact (Real.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds.mul (hac.continuousAt.tendsto.comp hv)).neg)

/-- **The acceptance value**: constant unit, `ψ ≡ 1`, `p = q + 1`: the limit is
`σ^q e^{-2aσ}/a > 0`. -/
theorem mix_tendsto_totalKernel_boundary_const {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) (q : ℕ) :
    Tendsto (fun t ↦ t ^ (q + 1) * (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (a * z 1))) * (z 0 ^ q * z 1 ^ (q + 1) * 1)))
        (σ / t)).toReal)
      atTop (𝓝 (σ ^ q * (exp (-(a * (2 * σ))) / a))) := by
  have h := mix_tendsto_totalKernel_boundary hσ (a := fun _ ↦ a) continuous_const
    (fun _ _ ↦ ha) (q + 1) q (ψ := fun _ ↦ 1) continuous_const (fun _ ↦ zero_le_one)
  have hI : (∫ u in Ioi (2 * σ), u ^ (((q + 1 : ℕ) : ℝ) - q - 1) *
      exp (-(u * (fun _ : Fin 2 → ℝ ↦ a) ![σ / u, 0])) * (fun _ : Fin 2 → ℝ ↦ (1 : ℝ)) ![σ / u, 0])
      = exp (-(a * (2 * σ))) / a := by
    have h1 : ∀ u ∈ Ioi (2 * σ), u ^ (((q + 1 : ℕ) : ℝ) - q - 1) *
        exp (-(u * (fun _ : Fin 2 → ℝ ↦ a) ![σ / u, 0])) *
          (fun _ : Fin 2 → ℝ ↦ (1 : ℝ)) ![σ / u, 0] = (fun x ↦ exp (-x)) (a * u) := by
      intro u _
      beta_reduce
      rw [show (((q + 1 : ℕ) : ℝ) - q - 1) = 0 by push_cast; ring, Real.rpow_zero, mul_comm u a]
      simp only [one_mul, mul_one]
    rw [setIntegral_congr_fun measurableSet_Ioi h1,
      integral_comp_mul_left_Ioi (fun x ↦ exp (-x)) (2 * σ) ha, integral_exp_neg_Ioi, smul_eq_mul,
      div_eq_inv_mul]
  rw [hI] at h
  exact h

end Laplace.Multi
