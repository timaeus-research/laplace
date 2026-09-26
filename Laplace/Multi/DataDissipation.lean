/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.QuadraticInformationBound
import Laplace.Multi.FixedNormalLimit
import Laplace.Multi.FiniteResponse
import Laplace.Multi.BasepointCurvature
import Laplace.Multi.PathLengthPrimitive

/-!
# Dissipation along the data path

Along the data path `ρ_t = ν.tilted (t h)`, `t ∈ [0, ∞)`, with `h ≤ H` and a charged top set
`p_* = ν{h = H} > 0`, the gap `δ = H − h ≥ 0` dissipates exactly the log-mass of the top set:

  `∫₀^∞ E_{ρ_t} δ dt = log (1/p_*)`   (`integral_Ioi_gap_dataPath`),

because `E_{ρ_t} δ = −(d/dt) log ∫ e^{−tδ} dν` and `∫ e^{−tδ} dν → p_*`
(`tendsto_integral_exp_neg_gap`).
Consequently every bounded statistic's mean along the data path has finite variation,

  `|Cov_{ρ_t}(S_j, h)| ≤ 2‖S_j‖_∞ E_{ρ_t} δ`,   `∫₀^∞ |Cov_{ρ_t}(S_j, h)| dt ≤ 2‖S_j‖_∞ log (1/p_*)`

(`abs_dataCov_le_gap`, `integral_abs_dataCov_le`), the data path converges to the conditional law
on the top set (`tendsto_integral_dataPath_atTop`), and the total displacement of the moment curve
is `∫₀^∞ Cov_{ρ_t}(S_j, h) dt = E_ν[S_j | h = H] − E_ν S_j` (`integral_Ioi_dataCov`).
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Dissipation

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h) {H : ℝ} (hH : ∀ x, h x ≤ H)
include hh

omit [Nonempty X] [IsProbabilityMeasure ν] hh in
/-- The data path is the tilt by the negative gap. -/
theorem tilted_data_eq_tilted_neg_gap (t : ℝ) :
    ν.tilted (fun x ↦ t * h x) = ν.tilted (fun x ↦ -(t * (H - h x))) := by
  have e : (fun x ↦ t * h x) = fun x ↦ -(t * (H - h x)) + t * H := by funext x; ring
  rw [e, tilted_add_const]

omit [Nonempty X] in
theorem isProbabilityMeasure_dataPath' (t : ℝ) :
    IsProbabilityMeasure (ν.tilted fun x ↦ t * h x) :=
  isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (hh.const_mul t))

omit [Nonempty X] in
/-- The mean gap along the data path. -/
theorem integral_gap_dataPath (t : ℝ) :
    ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) = H - ∫ x, h x ∂ν.tilted (fun x ↦ t * h x) := by
  have := isProbabilityMeasure_dataPath' ν hh t
  rw [integral_sub (integrable_const _) (integrable_of_bdd_prob _ hh), integral_const]
  simp

include hH in
omit [Nonempty X] [IsProbabilityMeasure ν] hh in
theorem integral_gap_dataPath_nonneg (t : ℝ) :
    0 ≤ ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) :=
  integral_nonneg fun x ↦ sub_nonneg.2 (hH x)

/-- The mean gap is differentiable, hence continuous, in the path parameter. -/
theorem hasDerivAt_integral_gap_dataPath (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, (H - h x) ∂ν.tilted (fun x ↦ s * h x))
      ((∫ x, (H - h x) * h x ∂ν.tilted (fun x ↦ t * h x)) -
        (∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x)) * ∫ x, h x ∂ν.tilted (fun x ↦ t * h x)) t :=
  hasDerivAt_integral_tilted ν hh ((Bdd.const H).sub hh) t

theorem continuous_integral_gap_dataPath :
    Continuous fun s ↦ ∫ x, (H - h x) ∂ν.tilted (fun x ↦ s * h x) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_integral_gap_dataPath ν hh t).continuousAt

omit [Nonempty X] [IsProbabilityMeasure ν] hh in
/-- The partition function of the gap is the tilted normaliser shifted by `e^{−TH}`. -/
theorem integral_exp_neg_gap_eq (T : ℝ) :
    ∫ x, exp (-(T * (H - h x))) ∂ν = (∫ x, exp (T * h x) ∂ν) * exp (-(T * H)) := by
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  beta_reduce
  rw [← exp_add]
  congr 1
  ring

/-- **The dissipation identity on a finite window**:
`∫₀^T E_{ρ_t} δ dt = −log ∫ e^{−Tδ} dν`. -/
theorem intervalIntegral_gap_dataPath (T : ℝ) :
    ∫ t in (0 : ℝ)..T, ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) =
      -Real.log (∫ x, exp (-(T * (H - h x))) ∂ν) := by
  have hK : ∀ s, HasDerivAt (fun s ↦ H * s - Real.log (∫ x, exp (s * h x) ∂ν))
      (∫ x, (H - h x) ∂ν.tilted (fun x ↦ s * h x)) s := fun s ↦ by
    have h1 := ((hasDerivAt_id s).const_mul H).sub (hasDerivAt_log_integral_exp ν hh s)
    refine h1.congr_deriv ?_
    rw [integral_gap_dataPath ν hh s]
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hK s)
    ((continuous_integral_gap_dataPath ν hh).intervalIntegrable _ _)]
  have hpos : 0 < ∫ x, exp (T * h x) ∂ν :=
    integral_exp_pos (integrable_exp_of_bdd ν (hh.const_mul T))
  rw [integral_exp_neg_gap_eq, Real.log_mul hpos.ne' (exp_pos _).ne', Real.log_exp]
  simp only [zero_mul, Real.exp_zero, integral_const, probReal_univ, one_smul, Real.log_one,
    sub_zero, mul_zero]
  ring

include hH in
omit [Nonempty X] in
/-- The gap partition function converges to the mass of the top set. -/
theorem tendsto_integral_exp_neg_gap :
    Tendsto (fun T ↦ ∫ x, exp (-(T * (H - h x))) ∂ν) atTop (𝓝 (ν.real {x | h x = H})) := by
  have hmeas : MeasurableSet {x | h x = H} := measurableSet_eq_fun hh.1 measurable_const
  have hmg : Measurable fun x ↦ H - h x := hh.1.const_sub H
  have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := (atTop : Filter ℝ))
    (F := fun T x ↦ exp (-(T * (H - h x)))) (f := ({x | h x = H} : Set X).indicator 1)
    (fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun T ↦ (((hmg.const_mul T).neg.exp).aestronglyMeasurable)) ?_
    (integrable_const _) ?_
  · rwa [integral_indicator_one hmeas] at h
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    refine ae_of_all _ fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hT (sub_nonneg.2 (hH x))))
  · refine ae_of_all _ fun x ↦ ?_
    by_cases hx : h x = H
    · have e : ∀ T : ℝ, exp (-(T * (H - h x))) = 1 := fun T ↦ by rw [hx]; simp
      simp only [e, Set.indicator_of_mem (show x ∈ {x | h x = H} from hx), Pi.one_apply]
      exact tendsto_const_nhds
    · have hpos : 0 < H - h x := lt_of_le_of_ne (sub_nonneg.2 (hH x)) fun e ↦ hx (by linarith)
      rw [Set.indicator_of_notMem (show x ∉ {x | h x = H} from hx)]
      exact tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hpos)

include hH in
omit [Nonempty X] in
/-- The gap partition function dominates the mass of the top set for `T ≥ 0`. -/
theorem top_mass_le_integral_exp_neg_gap {T : ℝ} (hT : 0 ≤ T) :
    ν.real {x | h x = H} ≤ ∫ x, exp (-(T * (H - h x))) ∂ν := by
  have hmeas : MeasurableSet {x | h x = H} := measurableSet_eq_fun hh.1 measurable_const
  have hmg : Measurable fun x ↦ H - h x := hh.1.const_sub H
  rw [← integral_indicator_one hmeas]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator hmeas)
    (integrable_of_bdd_prob ν ⟨(hmg.const_mul T).neg.exp, 1, fun x ↦ ?_⟩) fun x ↦ ?_
  · rw [abs_of_pos (exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hT (sub_nonneg.2 (hH x))))
  · by_cases hx : h x = H
    · rw [Set.indicator_of_mem (show x ∈ {x | h x = H} from hx), Pi.one_apply, hx]
      simp
    · rw [Set.indicator_of_notMem (show x ∉ {x | h x = H} from hx)]
      exact (exp_pos _).le

include hH in
/-- Every window's dissipation is at most `log (1/p_*)`. -/
theorem intervalIntegral_gap_dataPath_le (hp : 0 < ν.real {x | h x = H}) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) ≤
      Real.log (1 / ν.real {x | h x = H}) := by
  rw [intervalIntegral_gap_dataPath ν hh, one_div, Real.log_inv, neg_le_neg_iff]
  exact Real.log_le_log hp (top_mass_le_integral_exp_neg_gap ν hh hH hT)

include hH in
/-- **The total dissipation is the log-mass of the top set** (as a limit of windows). -/
theorem tendsto_intervalIntegral_gap_dataPath (hp : 0 < ν.real {x | h x = H}) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x)) atTop
      (𝓝 (Real.log (1 / ν.real {x | h x = H}))) := by
  simp_rw [intervalIntegral_gap_dataPath ν hh]
  rw [one_div, Real.log_inv]
  exact ((Real.continuousAt_log hp.ne').tendsto.comp (tendsto_integral_exp_neg_gap ν hh hH)).neg

include hH in
/-- The mean gap is integrable on the half-line. -/
theorem integrableOn_gap_dataPath (hp : 0 < ν.real {x | h x = H}) :
    IntegrableOn (fun t ↦ ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x)) (Ioi 0) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (Real.log (1 / ν.real {x | h x = H})) 0
    (b := id) (l := atTop) (fun T ↦ (continuous_integral_gap_dataPath ν hh).integrableOn_Ioc)
    tendsto_id ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simp only [id_eq]
  calc ∫ t in (0 : ℝ)..T, ‖∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x)‖
      = ∫ t in (0 : ℝ)..T, ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) :=
        intervalIntegral.integral_congr fun t _ ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (integral_gap_dataPath_nonneg ν hH t)]
    _ ≤ _ := intervalIntegral_gap_dataPath_le ν hh hH hp hT

include hH in
/-- **The dissipation identity**: `∫₀^∞ E_{ρ_t} δ dt = log (1/p_*)`. -/
theorem integral_Ioi_gap_dataPath (hp : 0 < ν.real {x | h x = H}) :
    ∫ t in Ioi (0 : ℝ), ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) =
      Real.log (1 / ν.real {x | h x = H}) :=
  tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_gap_dataPath ν hh hH hp)
      (tendsto_id (α := ℝ)))
    (tendsto_intervalIntegral_gap_dataPath ν hh hH hp)

omit [Nonempty X] [IsProbabilityMeasure ν] hh in
/-- The tilted integral of a bounded statistic along the data path, in gap form. -/
theorem integral_dataPath_eq_div {g : X → ℝ} (T : ℝ) :
    ∫ x, g x ∂ν.tilted (fun x ↦ T * h x) =
      (∫ x, exp (-(T * (H - h x))) * g x ∂ν) / ∫ x, exp (-(T * (H - h x))) ∂ν := by
  rw [tilted_data_eq_tilted_neg_gap ν (H := H), integral_tilted, ← integral_div]
  exact integral_congr_ae (ae_of_all _ fun x ↦ by simp only [smul_eq_mul]; ring)

include hH in
omit [Nonempty X] in
/-- The data path converges to the conditional law on the top set: for every bounded `g`,
`E_{ρ_T} g → E_ν[g 1_{h = H}] / ν{h = H}`. -/
theorem tendsto_integral_dataPath_atTop (hp : 0 < ν.real {x | h x = H}) {g : X → ℝ}
    (hg : Bdd g) :
    Tendsto (fun T ↦ ∫ x, g x ∂ν.tilted (fun x ↦ T * h x)) atTop
      (𝓝 ((∫ x in {x | h x = H}, g x ∂ν) / ν.real {x | h x = H})) := by
  have hmeas : MeasurableSet {x | h x = H} := measurableSet_eq_fun hh.1 measurable_const
  have hmg : Measurable fun x ↦ H - h x := hh.1.const_sub H
  obtain ⟨hgm, K, hK⟩ := hg
  have hnum : Tendsto (fun T ↦ ∫ x, exp (-(T * (H - h x))) * g x ∂ν) atTop
      (𝓝 (∫ x in {x | h x = H}, g x ∂ν)) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := (atTop : Filter ℝ))
      (F := fun T x ↦ exp (-(T * (H - h x))) * g x) (f := ({x | h x = H} : Set X).indicator g)
      (fun _ ↦ K)
      (Eventually.of_forall fun T ↦ ((((hmg.const_mul T).neg.exp).mul hgm).aestronglyMeasurable))
      ?_ (integrable_const _) ?_
    · rwa [integral_indicator hmeas] at h
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      refine ae_of_all _ fun x ↦ ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
      calc exp (-(T * (H - h x))) * |g x| ≤ 1 * |g x| :=
            mul_le_mul_of_nonneg_right
              (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hT (sub_nonneg.2 (hH x)))))
              (abs_nonneg _)
        _ ≤ K := by rw [one_mul]; exact hK x
    · refine ae_of_all _ fun x ↦ ?_
      by_cases hx : h x = H
      · have e : ∀ T : ℝ, exp (-(T * (H - h x))) * g x = g x := fun T ↦ by rw [hx]; simp
        simp only [e, Set.indicator_of_mem (show x ∈ {x | h x = H} from hx)]
        exact tendsto_const_nhds
      · have hpos : 0 < H - h x := lt_of_le_of_ne (sub_nonneg.2 (hH x)) fun e ↦ hx (by linarith)
        rw [Set.indicator_of_notMem (show x ∉ {x | h x = H} from hx)]
        have := (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hpos)).mul_const
          (g x)
        simpa using this
  simp_rw [integral_dataPath_eq_div ν (H := H)]
  exact hnum.div (tendsto_integral_exp_neg_gap ν hh hH) hp.ne'

end Dissipation

section MomentCurve

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]

omit [Nonempty X] in
/-- A one-sided centring bound: `|Cov_ρ(f, g)| ≤ 2‖f‖_∞ E_ρ g` for `g ≥ 0`. -/
theorem abs_lawCov_le_mul_integral_of_nonneg (ρ : Measure X) [IsProbabilityMeasure ρ]
    {f g : X → ℝ} (hf : Bdd f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) (hg : Bdd g)
    (hg0 : ∀ x, 0 ≤ g x) : |lawCov ρ f g| ≤ 2 * K * ∫ x, g x ∂ρ := by
  have hfi := integrable_of_bdd_prob ρ hf
  have hgi := integrable_of_bdd_prob ρ hg
  have hfgi := integrable_of_bdd_prob ρ (hf.mul hg)
  have hEf : |∫ x, f x ∂ρ| ≤ K := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |f x| ∂ρ ≤ ∫ _, K ∂ρ := integral_mono hfi.abs (integrable_const _) hK
      _ = K := by simp
  have e : lawCov ρ f g = ∫ x, (f x - ∫ y, f y ∂ρ) * g x ∂ρ := by
    have e2 : ∀ x, (f x - ∫ y, f y ∂ρ) * g x = f x * g x - (∫ y, f y ∂ρ) * g x :=
      fun x ↦ by ring
    simp_rw [e2]
    rw [integral_sub hfgi (hgi.const_mul _), integral_const_mul, lawCov]
  rw [e]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  have hint : Integrable (fun x ↦ |(f x - ∫ y, f y ∂ρ) * g x|) ρ := by
    have := (hfgi.sub (hgi.const_mul (∫ y, f y ∂ρ))).abs
    refine this.congr (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.sub_apply]
    ring_nf
  refine integral_mono hint (hgi.const_mul _) fun x ↦ ?_
  · rw [abs_mul, abs_of_nonneg (hg0 x)]
    refine mul_le_mul_of_nonneg_right ?_ (hg0 x)
    calc |f x - ∫ y, f y ∂ρ| ≤ |f x| + |∫ y, f y ∂ρ| := abs_sub _ _
      _ ≤ K + K := add_le_add (hK x) hEf
      _ = 2 * K := by ring

omit [Nonempty X] in
/-- Covariance with `c − g` is minus the covariance with `g`. -/
theorem lawCov_const_sub_right (ρ : Measure X) [IsProbabilityMeasure ρ] {f g : X → ℝ}
    (hf : Bdd f) (hg : Bdd g) (c : ℝ) :
    lawCov ρ f (fun x ↦ c - g x) = -lawCov ρ f g := by
  have hfi := integrable_of_bdd_prob ρ hf
  have hgi := integrable_of_bdd_prob ρ hg
  have hfgi := integrable_of_bdd_prob ρ (hf.mul hg)
  have e : ∀ x, f x * (c - g x) = c * f x - f x * g x := fun x ↦ by ring
  simp only [lawCov]
  simp_rw [e]
  rw [integral_sub (hfi.const_mul _) hfgi, integral_const_mul,
    integral_sub (integrable_const _) hgi, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring

variable {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  {h : X → ℝ} (hh : Bdd h) {H : ℝ} (hH : ∀ x, h x ≤ H)
include hS hh hH

omit [Nonempty X] [Fintype J] [Nonempty J] in
/-- **The data forcing is dominated by the mean gap**:
`|Cov_{ρ_t}(S_j, h)| ≤ 2‖S_j‖_∞ E_{ρ_t} δ`. -/
theorem abs_dataCov_le_gap (j : J) {K : ℝ} (hK : ∀ x, |S j x| ≤ K) (t : ℝ) :
    |dataCov S ν h t j| ≤ 2 * K * ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) := by
  have := isProbabilityMeasure_dataPath' ν hh t
  have e : dataCov S ν h t j = -lawCov (ν.tilted fun x ↦ t * h x) (S j) (fun x ↦ H - h x) := by
    rw [lawCov_const_sub_right _ (hS j) hh, neg_neg]
    rfl
  rw [e, abs_neg]
  exact abs_lawCov_le_mul_integral_of_nonneg _ (hS j) hK ((Bdd.const H).sub hh)
    fun x ↦ sub_nonneg.2 (hH x)

omit [Fintype J] [Nonempty J] hH in
theorem continuous_dataCov (j : J) : Continuous fun t ↦ dataCov S ν h t j :=
  continuous_iff_continuousAt.2 fun t ↦ by
    obtain ⟨K', hK'⟩ := hasDerivAt_dataCov hS ν hh t
    exact (hasDerivAt_pi.1 hK' j).continuousAt

omit [Fintype J] [Nonempty J] in
/-- The data forcing is integrable on the half-line. -/
theorem integrableOn_dataCov (hp : 0 < ν.real {x | h x = H}) (j : J) :
    IntegrableOn (fun t ↦ dataCov S ν h t j) (Ioi 0) := by
  obtain ⟨-, K, hK⟩ := hS j
  refine ((integrableOn_gap_dataPath ν hh hH hp).const_mul (2 * K)).mono'
    (continuous_dataCov ν hS hh j).aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_dataCov_le_gap ν hS hh hH j hK t

omit [Fintype J] [Nonempty J] in
/-- **Finite variation of the moment curve**:
`∫₀^∞ |Cov_{ρ_t}(S_j, h)| dt ≤ 2‖S_j‖_∞ log (1/p_*)`. -/
theorem integral_abs_dataCov_le (hp : 0 < ν.real {x | h x = H}) (j : J) {K : ℝ}
    (hK : ∀ x, |S j x| ≤ K) :
    ∫ t in Ioi (0 : ℝ), |dataCov S ν h t j| ≤ 2 * K * Real.log (1 / ν.real {x | h x = H}) := by
  rw [← integral_Ioi_gap_dataPath ν hh hH hp, ← integral_const_mul]
  exact integral_mono (integrableOn_dataCov ν hS hh hH hp j).abs
    ((integrableOn_gap_dataPath ν hh hH hp).const_mul _) fun t ↦
      abs_dataCov_le_gap ν hS hh hH j hK t

omit [Fintype J] [Nonempty J] hH in
/-- The mean of a statistic along the data path is a primitive of the data forcing. -/
theorem hasDerivAt_integral_dataPath (j : J) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, S j x ∂ν.tilted (fun x ↦ s * h x)) (dataCov S ν h t j) t :=
  hasDerivAt_integral_tilted ν hh (hS j) t

omit [Fintype J] [Nonempty J] in
/-- **The total displacement of the moment curve**:
`∫₀^∞ Cov_{ρ_t}(S_j, h) dt = E_ν[S_j | h = H] − E_ν S_j`. -/
theorem integral_Ioi_dataCov (hp : 0 < ν.real {x | h x = H}) (j : J) :
    ∫ t in Ioi (0 : ℝ), dataCov S ν h t j =
      (∫ x in {x | h x = H}, S j x ∂ν) / ν.real {x | h x = H} - ∫ x, S j x ∂ν := by
  have h0 : (∫ x, S j x ∂ν.tilted (fun x ↦ (0 : ℝ) * h x)) = ∫ x, S j x ∂ν := by
    simp
  rw [← h0]
  exact integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ ↦ hasDerivAt_integral_dataPath ν hS hh j t)
    (integrableOn_dataCov ν hS hh hH hp j) (tendsto_integral_dataPath_atTop ν hh hH hp (hS j))

end MomentCurve

end Laplace.Multi
