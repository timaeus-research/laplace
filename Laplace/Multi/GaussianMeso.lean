/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.LocationRecovery

/-!
# The mesoscopic cutoff

Stage 2 of the forward-expansion programme: the localization layer.
`mesoscopicSet q` is the ball `√q · ‖z‖ ≤ 1` in the rescaled
variable — small enough that `q`-scaled points fall in every fixed
Taylor ball (`‖q • z‖ ≤ √q` there), large enough to eventually
contain every fixed point. Outside it, rate-halving turns Gaussian
envelopes into `e^{-(c/2)/q}` times a fixed Gaussian moment, which
is smaller than every power of `q` at `0⁺`
(`exp_neg_div_isLittleO_pow`); by coercivity the same holds for the
rescaled Boltzmann integrand (`integrand_meso_tail_isLittleO`) — the
outer-tail removal every later expansion stage consumes.
-/

open Real MeasureTheory Filter Topology Asymptotics Set

namespace Laplace.Multi

variable {d : ℕ}

/-- The mesoscopic window in the rescaled variable:
`√q · ‖z‖ ≤ 1`, i.e. `‖z‖ ≤ q^(-1/2)` for `q > 0`. -/
def mesoscopicSet (d : ℕ) (q : ℝ) : Set (EuclidD d) :=
  {z | Real.sqrt q * ‖z‖ ≤ 1}

theorem measurableSet_mesoscopicSet (q : ℝ) :
    MeasurableSet (mesoscopicSet d q) :=
  (isClosed_le (continuous_const.mul continuous_norm)
    continuous_const).measurableSet

/-- Every fixed point is eventually inside the mesoscopic window. -/
theorem eventually_mem_mesoscopicSet (z : EuclidD d) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), z ∈ mesoscopicSet d q := by
  have hlim : Tendsto (fun q : ℝ ↦ Real.sqrt q * ‖z‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hs : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at hs
    have hmul : Tendsto (fun q : ℝ ↦ Real.sqrt q * ‖z‖)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 * ‖z‖)) :=
      (hs.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds
    rwa [zero_mul] at hmul
  filter_upwards [hlim.eventually_le_const one_pos] with q hq
  exact hq

/-- On the mesoscopic window, `q`-scaled points eventually lie in
every fixed ball: `‖q • z‖ ≤ √q` there. -/
theorem smul_mem_ball_of_mesoscopic {r : ℝ} (hr : 0 < r) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), ∀ z ∈ mesoscopicSet d q,
      ‖q • z‖ < r := by
  have hmin : (0 : ℝ) < min (r ^ 2) 1 := by positivity
  filter_upwards [Ioo_mem_nhdsGT hmin] with q hq z hz
  obtain ⟨hq0, hqlt⟩ := hq
  have hsq : Real.sqrt q * Real.sqrt q = q :=
    Real.mul_self_sqrt hq0.le
  have hkey : ‖q • z‖ = Real.sqrt q * (Real.sqrt q * ‖z‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0, ← mul_assoc,
      hsq]
  have hle : ‖q • z‖ ≤ Real.sqrt q := by
    rw [hkey]
    calc Real.sqrt q * (Real.sqrt q * ‖z‖) ≤ Real.sqrt q * 1 :=
          mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg q)
      _ = Real.sqrt q := mul_one _
  have hlt : Real.sqrt q < r := by
    have hq_lt_r2 : q < r ^ 2 := lt_of_lt_of_le hqlt (min_le_left _ _)
    have := Real.sqrt_lt_sqrt hq0.le hq_lt_r2
    rwa [Real.sqrt_sq hr.le] at this
  exact lt_of_le_of_lt hle hlt

/-- **Exponential beats every power at the origin**:
`e^{-c/q} = o(q^M)` at `0⁺` for every `c > 0` and `M`. -/
theorem exp_neg_div_isLittleO_pow {c : ℝ} (hc : 0 < c) (M : ℕ) :
    (fun q : ℝ ↦ Real.exp (-(c / q))) =o[𝓝[>] (0 : ℝ)]
      fun q : ℝ ↦ q ^ M := by
  have hatTop : Tendsto (fun t : ℝ ↦ t ^ M * Real.exp (-(c * t)))
      atTop (𝓝 0) := by
    have hbase := tendsto_pow_mul_exp_neg_atTop_nhds_zero M
    have hcomp := hbase.comp (tendsto_id.const_mul_atTop hc)
    have h2 : Tendsto (fun t : ℝ ↦
        (c * t) ^ M * Real.exp (-(c * t))) atTop (𝓝 0) := hcomp
    have h3 := h2.const_mul ((c ^ M)⁻¹)
    rw [mul_zero] at h3
    refine h3.congr fun t ↦ ?_
    rw [mul_pow]
    have hcM : (c : ℝ) ^ M ≠ 0 := (pow_pos hc M).ne'
    field_simp
  have hq : Tendsto (fun q : ℝ ↦ (q : ℝ)⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hcomp2 : Tendsto (fun q : ℝ ↦
      (q⁻¹) ^ M * Real.exp (-(c * q⁻¹))) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hatTop.comp hq
  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [hcomp2.eventually_le_const hε,
    self_mem_nhdsWithin] with q hle hq0
  have hq0' : (0 : ℝ) < q := hq0
  have hkey : Real.exp (-(c / q)) =
      q ^ M * ((q⁻¹) ^ M * Real.exp (-(c * q⁻¹))) := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0'.ne', one_pow,
      one_mul, div_eq_mul_inv]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_pos (pow_pos hq0' M), hkey]
  calc q ^ M * ((q⁻¹) ^ M * Real.exp (-(c * q⁻¹)))
      ≤ q ^ M * ε := mul_le_mul_of_nonneg_left hle
        (pow_pos hq0' M).le
    _ = ε * q ^ M := mul_comm _ _

/-- **The Gaussian mesoscopic tail is beyond all orders**: outside
the mesoscopic window, polynomial-times-Gaussian integrals are
`o(q^M)` at `0⁺` for every `M`, by rate-halving. -/
theorem gaussian_meso_tail_isLittleO (p M : ℕ) {c : ℝ}
    (hc : 0 < c) :
    (fun q : ℝ ↦ ∫ z in (mesoscopicSet d q)ᶜ,
      ‖z‖ ^ p * Real.exp (-c * ‖z‖ ^ 2)) =o[𝓝[>] (0 : ℝ)]
      fun q : ℝ ↦ q ^ M := by
  have hc2 : (0 : ℝ) < c / 2 := by positivity
  have hK : (0 : ℝ) ≤ ∫ z : EuclidD d,
      ‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2) :=
    integral_nonneg fun z ↦ by positivity
  have hbound : ∀ᶠ q in 𝓝[>] (0 : ℝ),
      ∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ p * Real.exp (-c * ‖z‖ ^ 2)
        ≤ Real.exp (-((c/2) / q)) * ∫ z : EuclidD d,
          ‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : (0 : ℝ) < q := hq
    have hpw : ∀ z ∈ (mesoscopicSet d q)ᶜ,
        ‖z‖ ^ p * Real.exp (-c * ‖z‖ ^ 2) ≤
        Real.exp (-((c/2) / q)) *
          (‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2)) := by
      intro z hz
      have hgt : 1 < Real.sqrt q * ‖z‖ := by
        rw [Set.mem_compl_iff, mesoscopicSet, Set.mem_setOf_eq] at hz
        linarith [lt_of_not_ge hz]
      have hz2 : 1 / q ≤ ‖z‖ ^ 2 := by
        have h1 : 1 < (Real.sqrt q * ‖z‖) * (Real.sqrt q * ‖z‖) := by
          nlinarith [hgt, Real.sqrt_nonneg q, norm_nonneg z]
        have hexp : (Real.sqrt q * ‖z‖) * (Real.sqrt q * ‖z‖) =
            q * ‖z‖ ^ 2 := by
          rw [show (Real.sqrt q * ‖z‖) * (Real.sqrt q * ‖z‖) =
            (Real.sqrt q * Real.sqrt q) * (‖z‖ * ‖z‖) from by ring,
            Real.mul_self_sqrt hq0.le, sq]
        rw [hexp] at h1
        rw [div_le_iff₀ hq0, mul_comm]
        linarith
      have hsplit : Real.exp (-c * ‖z‖ ^ 2) =
          Real.exp (-(c/2) * ‖z‖ ^ 2) *
            Real.exp (-(c/2) * ‖z‖ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hfac : Real.exp (-(c/2) * ‖z‖ ^ 2) ≤
          Real.exp (-((c/2) / q)) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hz2 hc2.le
        rw [show (c/2) * (1/q) = (c/2)/q from by ring] at hmul
        linarith
      calc ‖z‖ ^ p * Real.exp (-c * ‖z‖ ^ 2)
          = Real.exp (-(c/2) * ‖z‖ ^ 2) *
              (‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2)) := by
            rw [hsplit]; ring
        _ ≤ Real.exp (-((c/2) / q)) *
              (‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_right hfac ?_
            positivity
    calc ∫ z in (mesoscopicSet d q)ᶜ,
        ‖z‖ ^ p * Real.exp (-c * ‖z‖ ^ 2)
        ≤ ∫ z in (mesoscopicSet d q)ᶜ,
            Real.exp (-((c/2) / q)) *
              (‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2)) := by
          refine setIntegral_mono_on ?_ ?_
            (measurableSet_mesoscopicSet q).compl hpw
          · exact (integrable_pow_mul_exp_neg_mul_sq hc p).integrableOn
          · exact ((integrable_pow_mul_exp_neg_mul_sq hc2 p).const_mul
              _).integrableOn
      _ = Real.exp (-((c/2) / q)) * ∫ z in (mesoscopicSet d q)ᶜ,
            ‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2) := by
          rw [integral_const_mul]
      _ ≤ Real.exp (-((c/2) / q)) * ∫ z : EuclidD d,
            ‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine setIntegral_le_integral
            (integrable_pow_mul_exp_neg_mul_sq hc2 p)
            (Filter.Eventually.of_forall fun z ↦ ?_)
          positivity
  have hexp := (exp_neg_div_isLittleO_pow hc2 M).const_mul_left
    (∫ z : EuclidD d, ‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2))
  rw [isLittleO_iff] at hexp ⊢
  intro ε hε
  filter_upwards [hexp hε, hbound, self_mem_nhdsWithin]
    with q hq1 hq2 hq3
  have hnn : (0 : ℝ) ≤ ∫ z in (mesoscopicSet d q)ᶜ,
      ‖z‖ ^ p * Real.exp (-c * ‖z‖ ^ 2) :=
    setIntegral_nonneg (measurableSet_mesoscopicSet q).compl
      fun z _ ↦ by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hq1' : (∫ z : EuclidD d,
      ‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2)) *
      Real.exp (-((c/2) / q)) ≤ ε * ‖q ^ M‖ := by
    refine le_trans ?_ hq1
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  calc ∫ z in (mesoscopicSet d q)ᶜ,
      ‖z‖ ^ p * Real.exp (-c * ‖z‖ ^ 2)
      ≤ Real.exp (-((c/2) / q)) * ∫ z : EuclidD d,
          ‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2) := hq2
    _ = (∫ z : EuclidD d, ‖z‖ ^ p * Real.exp (-(c/2) * ‖z‖ ^ 2)) *
          Real.exp (-((c/2) / q)) := mul_comm _ _
    _ ≤ ε * ‖q ^ M‖ := hq1'

/-- **Coercivity transfer**: the rescaled Boltzmann integrand's
mesoscopic tail, with any polynomial weight, is beyond all orders. -/
theorem integrand_meso_tail_isLittleO {L : EuclidD d → ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ} (A : LocalLaplaceDomain L H)
    (p M : ℕ) :
    (fun q : ℝ ↦ ∫ z in (mesoscopicSet d q)ᶜ,
      ‖z‖ ^ p * |A.integrand (fun _ ↦ 1) q z|)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ M := by
  have hgauss := gaussian_meso_tail_isLittleO (d := d) p M A.c_pos
  rw [isLittleO_iff] at hgauss ⊢
  intro ε hε
  filter_upwards [hgauss hε, self_mem_nhdsWithin] with q hq1 hq0
  have hq0' : (0 : ℝ) < q := hq0
  have hpw : ∀ z : EuclidD d,
      ‖z‖ ^ p * |A.integrand (fun _ ↦ 1) q z| ≤
      ‖z‖ ^ p * Real.exp (-A.c * ‖z‖ ^ 2) := by
    intro z
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold LocalLaplaceDomain.integrand
    by_cases hm : z ∈ {x : EuclidD d | q • x ∈ A.U}
    · rw [Set.indicator_of_mem hm, one_mul,
        abs_of_pos (Real.exp_pos _)]
      have hlow := A.rescaled_lower hq0' hm
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [Set.indicator_of_notMem hm, abs_zero]
      positivity
  have hmono : ∫ z in (mesoscopicSet d q)ᶜ,
      ‖z‖ ^ p * |A.integrand (fun _ ↦ 1) q z| ≤
      ∫ z in (mesoscopicSet d q)ᶜ,
        ‖z‖ ^ p * Real.exp (-A.c * ‖z‖ ^ 2) := by
    refine setIntegral_mono_on ?_ ?_
      (measurableSet_mesoscopicSet q).compl fun z _ ↦ hpw z
    · refine Integrable.integrableOn ?_
      have hint := A.integrable_integrand continuous_const
        (⟨1, 0, zero_le_one, fun x ↦ by norm_num⟩ :
          HasPolynomialGrowth fun _ : EuclidD d ↦ (1:ℝ)) hq0'
      have : Integrable (fun z : EuclidD d ↦
          ‖z‖ ^ p * Real.exp (-A.c * ‖z‖ ^ 2)) :=
        integrable_pow_mul_exp_neg_mul_sq A.c_pos p
      refine this.mono' ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
      · exact (continuous_norm.pow p).aestronglyMeasurable.mul
          hint.abs.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
          (0:ℝ) ≤ ‖z‖ ^ p), abs_abs]
        exact hpw z
    · exact (integrable_pow_mul_exp_neg_mul_sq A.c_pos p).integrableOn
  have hnn : (0 : ℝ) ≤ ∫ z in (mesoscopicSet d q)ᶜ,
      ‖z‖ ^ p * |A.integrand (fun _ ↦ 1) q z| :=
    setIntegral_nonneg (measurableSet_mesoscopicSet q).compl
      fun z _ ↦ by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc ∫ z in (mesoscopicSet d q)ᶜ,
      ‖z‖ ^ p * |A.integrand (fun _ ↦ 1) q z|
      ≤ ∫ z in (mesoscopicSet d q)ᶜ,
          ‖z‖ ^ p * Real.exp (-A.c * ‖z‖ ^ 2) := hmono
    _ ≤ ‖∫ z in (mesoscopicSet d q)ᶜ,
          ‖z‖ ^ p * Real.exp (-A.c * ‖z‖ ^ 2)‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
    _ ≤ ε * ‖q ^ M‖ := hq1

end Laplace.Multi
