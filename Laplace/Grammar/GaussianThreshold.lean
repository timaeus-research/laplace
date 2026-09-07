/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.GaussianDichotomy

/-!
# The constant-Gaussian fluctuation model: the finiteness threshold (rem:pop_vs_emp)

For `X ~ N(0, v)` the expected Gaussian moment `E₊[J_p(X)]` (unit 161) equals
`∫₀^∞ s^{p−1} e^{−(β − β²v/2)s²} ds`, hence

* if `βv < 2`: `E₊[J_p(X)] = J_p(0) (1 − βv/2)^{−p/2} < ∞` (`lintegral_gaussMomentJ_eq_of_lt`),
  and it strictly exceeds `J_p(0)` when `v > 0` (`lt_lintegral_gaussMomentJ`);
* if `βv ≥ 2`: `E₊[J_p(X)] = ∞` (`lintegral_gaussMomentJ_eq_top_of_ge`).

So the expected leading coefficient is finite iff `βv < 2` (`lintegral_gaussMomentJ_lt_top_iff`):
averaging the asymptotic coefficients over the fluctuation is not justified by the samplewise
expansion alone, and a temperature threshold appears. Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace Laplace.Grammar

/-- `∫₀^∞ s^{p−1} e^{−c s²} ds = c^{−p/2} Γ(p/2)/2`. -/
theorem integral_rpow_mul_exp_neg_mul_sq (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * Real.exp (-c * s ^ 2)
      = c ^ (-p / 2) * (1 / 2) * Real.Gamma (p / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := p - 1) (b := c) two_pos
    (by linarith) hc
  simp only [Real.rpow_two] at h
  rw [h, show p - 1 + 1 = p by ring, neg_div]

/-- The Gaussian moment at `x = 0`. -/
theorem gaussMomentJ_zero (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) :
    gaussMomentJ β p 0 = β ^ (-p / 2) * (1 / 2) * Real.Gamma (p / 2) := by
  unfold gaussMomentJ logMoment
  rw [← integral_rpow_mul_exp_neg_mul_sq β p hβ hp]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp

/-- The integrand of the Tonelli identity is a Gaussian moment integrand with the shifted rate. -/
theorem gaussTail_integrand_eq (β p v s : ℝ) :
    s ^ (p - 1) * Real.exp (-β * s ^ 2) * Real.exp (v * (β * s) ^ 2 / 2)
      = s ^ (p - 1) * Real.exp (-(β - β ^ 2 * v / 2) * s ^ 2) := by
  rw [mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- **Subcritical case** `βv < 2`: the expected moment is `J_p(0)(1 − βv/2)^{−p/2}`. -/
theorem gaussTail_eq_of_lt (β p v : ℝ) (hβ : 0 < β) (hp : 0 < p) (_hv : 0 ≤ v) (h : β * v < 2) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (p - 1) * Real.exp (-β * s ^ 2)
        * Real.exp (v * (β * s) ^ 2 / 2))
      = ENNReal.ofReal (gaussMomentJ β p 0 * (1 - β * v / 2) ^ (-p / 2)) := by
  set c := β - β ^ 2 * v / 2 with hcdef
  have h1 : 0 < 1 - β * v / 2 := by linarith
  have hc : 0 < c := by rw [hcdef, show β - β ^ 2 * v / 2 = β * (1 - β * v / 2) by ring]; positivity
  have hint : IntegrableOn (fun s : ℝ => s ^ (p - 1) * Real.exp (-c * s ^ 2)) (Ioi 0) := by
    have := gaussMoment_exp_integrableOn c p 0 hc hp
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp
  simp_rw [gaussTail_integrand_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
    fun s hs => by
      have : 0 < s ^ (p - 1) := Real.rpow_pos_of_pos hs _
      change (0 : ℝ) ≤ s ^ (p - 1) * Real.exp (-c * s ^ 2)
      positivity)]
  congr 1
  rw [integral_rpow_mul_exp_neg_mul_sq c p hc hp, gaussMomentJ_zero β p hβ hp,
    show c = β * (1 - β * v / 2) by rw [hcdef]; ring, Real.mul_rpow hβ.le h1.le]
  ring

/-- `∫₁^∞ s^{p−1} ds = ∞` for `p > 0`. -/
theorem lintegral_rpow_Ioi_one_eq_top (p : ℝ) (hp : 0 < p) :
    ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (s ^ (p - 1)) = ⊤ := by
  have hnot : ¬ IntegrableOn (fun s : ℝ => s ^ (p - 1)) (Ioi 1) := by
    rw [integrableOn_Ioi_rpow_iff one_pos]; linarith
  have hmeas : AEStronglyMeasurable (fun s : ℝ => s ^ (p - 1)) (volume.restrict (Ioi 1)) :=
    (measurable_id.pow_const _).aestronglyMeasurable
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi 1)] fun s : ℝ => s ^ (p - 1) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
      Real.rpow_nonneg (by linarith [show (1 : ℝ) < s from hs]) _
  have hfin : ¬ HasFiniteIntegral (fun s : ℝ => s ^ (p - 1)) (volume.restrict (Ioi 1)) :=
    fun h => hnot ⟨hmeas, h⟩
  rw [hasFiniteIntegral_iff_ofReal hnn, not_lt, top_le_iff] at hfin
  exact hfin

/-- **Supercritical case** `βv ≥ 2`: the expected moment is infinite. -/
theorem gaussTail_eq_top_of_ge (β p v : ℝ) (hβ : 0 < β) (hp : 0 < p) (h : 2 ≤ β * v) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (p - 1) * Real.exp (-β * s ^ 2)
        * Real.exp (v * (β * s) ^ 2 / 2)) = ⊤ := by
  set c := β - β ^ 2 * v / 2 with hcdef
  have hc : c ≤ 0 := by
    rw [hcdef, show β - β ^ 2 * v / 2 = β * (1 - β * v / 2) by ring]
    exact mul_nonpos_of_nonneg_of_nonpos hβ.le (by linarith)
  refine top_le_iff.1 ?_
  calc (⊤ : ENNReal) = ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (s ^ (p - 1)) :=
        (lintegral_rpow_Ioi_one_eq_top p hp).symm
    _ ≤ ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (s ^ (p - 1) * Real.exp (-β * s ^ 2)
          * Real.exp (v * (β * s) ^ 2 / 2)) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
        have hs1 : (1 : ℝ) < s := hs
        rw [gaussTail_integrand_eq]
        refine ENNReal.ofReal_le_ofReal ?_
        have hnn : 0 ≤ s ^ (p - 1) := Real.rpow_nonneg (by linarith) _
        have hexp : 1 ≤ Real.exp (-c * s ^ 2) :=
          Real.one_le_exp (by nlinarith [sq_nonneg s])
        exact le_mul_of_one_le_right hnn hexp
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (p - 1) * Real.exp (-β * s ^ 2)
          * Real.exp (v * (β * s) ^ 2 / 2)) :=
        lintegral_mono_set (Ioi_subset_Ioi zero_le_one)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Expected leading moment, subcritical**: `E₊[J_p(X)] = J_p(0)(1 − βv/2)^{−p/2}`. -/
theorem lintegral_gaussMomentJ_eq_of_lt (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (X : Ω → ℝ)
    (hX : Measurable X) (v : NNReal) (hXg : μ.map X = gaussianReal 0 v) (h : β * v < 2) :
    ∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ
      = ENNReal.ofReal (gaussMomentJ β p 0 * (1 - β * v / 2) ^ (-p / 2)) := by
  rw [lintegral_gaussMomentJ_eq β p hβ hp X hX v hXg]
  exact gaussTail_eq_of_lt β p v hβ hp v.coe_nonneg h

/-- **Expected leading moment, supercritical**: `E₊[J_p(X)] = ∞` when `βv ≥ 2`. -/
theorem lintegral_gaussMomentJ_eq_top_of_ge (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (X : Ω → ℝ)
    (hX : Measurable X) (v : NNReal) (hXg : μ.map X = gaussianReal 0 v) (h : 2 ≤ β * v) :
    ∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ = ⊤ := by
  rw [lintegral_gaussMomentJ_eq β p hβ hp X hX v hXg]
  exact gaussTail_eq_top_of_ge β p v hβ hp h

/-- **The finiteness threshold**: the expected leading moment is finite iff `βv < 2`. -/
theorem lintegral_gaussMomentJ_lt_top_iff (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (X : Ω → ℝ)
    (hX : Measurable X) (v : NNReal) (hXg : μ.map X = gaussianReal 0 v) :
    (∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ) < ⊤ ↔ β * v < 2 := by
  constructor
  · intro hlt
    by_contra hge
    rw [lintegral_gaussMomentJ_eq_top_of_ge β p hβ hp X hX v hXg (not_lt.1 hge)] at hlt
    exact lt_irrefl _ hlt
  · intro h
    rw [lintegral_gaussMomentJ_eq_of_lt β p hβ hp X hX v hXg h]
    exact ENNReal.ofReal_lt_top

/-- **Jensen gap**: for a nondegenerate subcritical Gaussian fluctuation the expected leading
moment strictly exceeds the fluctuation-free value `J_p(0)`. -/
theorem lt_lintegral_gaussMomentJ (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (X : Ω → ℝ)
    (hX : Measurable X) (v : NNReal) (hv : 0 < (v : ℝ)) (hXg : μ.map X = gaussianReal 0 v)
    (h : β * v < 2) :
    ENNReal.ofReal (gaussMomentJ β p 0) < ∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ := by
  rw [lintegral_gaussMomentJ_eq_of_lt β p hβ hp X hX v hXg h]
  have hJ := gaussMomentJ_pos β p 0 hβ hp
  have h1 : 0 < 1 - β * v / 2 := by linarith
  have h2 : 1 - β * v / 2 < 1 := by
    have : 0 < β * v := mul_pos hβ hv
    linarith
  have hpow : 1 < (1 - β * v / 2) ^ (-p / 2) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg h1 h2 (by linarith)
  refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
  exact lt_mul_of_one_lt_right hJ hpow

end Laplace.Grammar
