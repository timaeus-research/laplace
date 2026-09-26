/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ConditionalFisherLoss
import Laplace.Multi.EndpointConvergence

/-!
# The conditional variational formula for the fibre information

For a data law `D = dν` with bounded positive density and conditional density `a = E_ν[d | σ(S)]`,
the fibre information `L = KL(D ‖ D↑) = KL(D ‖ aν)` is a Donsker–Varadhan supremum over bounded
tests on the full space, with the normaliser conditioned on the statistic:

`L = max_{g bounded} { E_D g − E_D log E_ν[e^g | σ(S)] }`.

The mechanism is an exact identity: the conditional tilt `T_g = e^g / E_ν[e^g | σ(S)] · aν` is a
probability law with the same `σ(S)`-marginal as `D`, and

`KL(D ‖ T_g) = L − E_D g + E_D log E_ν[e^g | σ(S)]`  (`toReal_klDiv_condTilt`),

so nonnegativity of the left side is the inequality, and `g = log(d/a)` (bounded here) makes
`T_g = D` and attains the maximum. Both identities are read through the seabed's tilted-right
divergence formula `KL(D ‖ ν.tilted f) = KL(D ‖ ν) − E_D f + log E_ν e^f`, since every normalised
positive density law is the tilt of `ν` by its logarithm.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Tilt

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- A normalised positive density law is the exponential tilt of `ν` by its logarithm. -/
theorem densLaw_eq_tilted_log {p : X → ℝ} (hp : ∀ x, 0 < p x) (hp1 : ∫ x, p x ∂ν = 1) :
    densLaw ν p = ν.tilted fun x ↦ Real.log (p x) := by
  have e2 : ∫ x, Real.exp (Real.log (p x)) ∂ν = 1 := by
    rw [← hp1]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ Real.exp_log (hp x))
  unfold densLaw Measure.tilted
  congr 1
  funext x
  simp only [Real.exp_log (hp x), e2, div_one]

/-- `|log y| ≤ max |log c| |log C|` on `[c, C]`, `c > 0`. -/
theorem abs_log_le_of_mem {c C y : ℝ} (hc0 : 0 < c) (hcy : c ≤ y) (hyC : y ≤ C) :
    |Real.log y| ≤ max (|Real.log c|) (|Real.log C|) := by
  have h1 := Real.log_le_log hc0 hcy
  have h2 := Real.log_le_log (hc0.trans_le hcy) hyC
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log c), le_max_left (|Real.log c|) (|Real.log C|)]
  · linarith [le_abs_self (Real.log C), le_max_right (|Real.log c|) (|Real.log C|)]

end Tilt

section Variational

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {d : X → ℝ} (hd : Measurable d) {c C : ℝ} (hc0 : 0 < c) (hc : ∀ x, c ≤ d x) (hC : ∀ x, d x ≤ C)
  (hnorm : ∫ x, d x ∂ν = 1) {a : X → ℝ} (ham : Measurable[statSigma S] a) (hac : ∀ x, c ≤ a x)
  (haC : ∀ x, a x ≤ C) (ha : a =ᵐ[ν] ν[d | statSigma S])
include hS hd hc0 hc hC hnorm ham hac haC ha

omit [Nonempty X] hS ham hac haC ha in
theorem isProbabilityMeasure_densLaw : IsProbabilityMeasure (densLaw ν d) := by
  have h := isProbabilityMeasure_densLaw_bridge ν hd hc0 hc hC hnorm zero_le_one le_rfl
  have e : bridgeDens d 1 = d := by
    funext x
    unfold bridgeDens
    ring
  rwa [e] at h

omit [Nonempty X] hd hc0 hc hC ham hac haC in
theorem integral_condDens : ∫ x, a x ∂ν = 1 := by
  rw [integral_congr_ae ha, integral_condExp (statSigma_le hS), hnorm]

omit [Nonempty X] ham hac haC in
/-- The statistic lift of `dν` is the law of its conditional density. -/
theorem statisticLift_densLaw_eq_condDens :
    statisticLift ν (densLaw ν d) (statPoint S) = densLaw ν a := by
  have h := statisticLift_densLaw_bridge hS ν hd hc0 hc hC hnorm ha zero_le_one le_rfl
  have e1 : bridgeDens d 1 = d := by
    funext x
    unfold bridgeDens
    ring
  have e2 : bridgeDens a 1 = a := by
    funext x
    unfold bridgeDens
    ring
  rwa [e1, e2] at h

omit [Nonempty X] hS ham hac haC ha in
/-- Bounded measurable functions are integrable against the data law. -/
theorem integrable_densLaw_of_abs_le {g : X → ℝ} (hg : Measurable g) {G : ℝ} (hG : ∀ x, |g x| ≤ G) :
    Integrable g (densLaw ν d) := by
  have := isProbabilityMeasure_densLaw ν hd hc0 hc hC hnorm
  exact Integrable.of_bound hg.aestronglyMeasurable G (Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs]; exact hG x)

section CondTilt

variable {g : X → ℝ} (hg : Measurable g) {G : ℝ} (hG : ∀ x, |g x| ≤ G) {cg : X → ℝ}
  (hcgm : Measurable[statSigma S] cg) (hcg0 : ∀ x, Real.exp (-G) ≤ cg x)
  (hcgG : ∀ x, cg x ≤ Real.exp G) (hcg : cg =ᵐ[ν] ν[fun x ↦ Real.exp (g x) | statSigma S])
include hg hG hcgm hcg0 hcgG hcg

omit [MeasurableSpace X] [Nonempty X] hS hd hc hC hnorm ham haC ha hg hG hcgm hcgG hcg in
theorem condTilt_pos (x : X) : 0 < Real.exp (g x) / cg x * a x :=
  mul_pos (div_pos (Real.exp_pos _) ((Real.exp_pos _).trans_le (hcg0 x)))
    (lt_of_lt_of_le hc0 (hac x))

omit [Nonempty X] hd hc hC hcgG in
/-- **The conditional tilt is normalised**: `∫ e^g / E_ν[e^g|σ(S)] · a dν = 1`. -/
theorem integral_condTilt : ∫ x, Real.exp (g x) / cg x * a x ∂ν = 1 := by
  have hcgpos : ∀ x, 0 < cg x := fun x ↦ (Real.exp_pos _).trans_le (hcg0 x)
  have hφ : Bdd fun x ↦ Real.exp (g x) := ⟨hg.exp, Real.exp G, fun x ↦ by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hG x))⟩
  have hw : StronglyMeasurable[statSigma S] fun x ↦ a x / cg x :=
    (ham.div hcgm).stronglyMeasurable
  have hwc : ∀ x, |a x / cg x| ≤ C / Real.exp (-G) := fun x ↦ by
    rw [abs_div, abs_of_pos (hcgpos x), abs_of_pos (lt_of_lt_of_le hc0 (hac x))]
    exact div_le_div₀ (hc0.le.trans ((hac x).trans (haC x))) (haC x) (Real.exp_pos _) (hcg0 x)
  have e : ∀ x, Real.exp (g x) / cg x * a x = a x / cg x * Real.exp (g x) := fun x ↦ by ring
  simp_rw [e]
  rw [integral_mul_condExp_statSigma hS ν hφ hw hwc]
  have : ∫ x, a x / cg x * (ν[fun x ↦ Real.exp (g x) | statSigma S]) x ∂ν = ∫ x, a x ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hcg] with x hx
    rw [← hx, div_mul_cancel₀ _ (hcgpos x).ne']
  rw [this]
  exact integral_condDens hS ν hnorm ha

omit [Nonempty X] hd hc hC hcgG in
/-- The conditional tilt is the tilt of `ν` by `g + log a − log E_ν[e^g|σ(S)]`. -/
theorem condTilt_eq_tilted :
    densLaw ν (fun x ↦ Real.exp (g x) / cg x * a x) =
      ν.tilted fun x ↦ g x + Real.log (a x) - Real.log (cg x) := by
  have hcgpos : ∀ x, 0 < cg x := fun x ↦ (Real.exp_pos _).trans_le (hcg0 x)
  have hapos : ∀ x, 0 < a x := fun x ↦ lt_of_lt_of_le hc0 (hac x)
  rw [densLaw_eq_tilted_log ν (condTilt_pos hc0 hac hcg0)
    (integral_condTilt hS ν hc0 hnorm ham hac haC ha hg hG hcgm hcg0 hcg)]
  congr 1
  funext x
  rw [Real.log_mul (div_pos (Real.exp_pos _) (hcgpos x)).ne' (hapos x).ne',
    Real.log_div (Real.exp_pos _).ne' (hcgpos x).ne', Real.log_exp]
  ring

omit [Nonempty X] in
/-- **The conditional Donsker–Varadhan identity**:
`KL(D ‖ T_g) = KL(D ‖ aν) − E_D g + E_D log E_ν[e^g | σ(S)]`. -/
theorem toReal_klDiv_condTilt :
    (klDiv (densLaw ν d) (densLaw ν (fun x ↦ Real.exp (g x) / cg x * a x))).toReal =
      (klDiv (densLaw ν d) (densLaw ν a)).toReal - ∫ x, g x ∂densLaw ν d +
        ∫ x, Real.log (cg x) ∂densLaw ν d := by
  have hm := statSigma_le hS
  have ham' : Measurable a := ham.mono hm le_rfl
  have hcgm' : Measurable cg := hcgm.mono hm le_rfl
  have hcgpos : ∀ x, 0 < cg x := fun x ↦ (Real.exp_pos _).trans_le (hcg0 x)
  have hapos : ∀ x, 0 < a x := fun x ↦ lt_of_lt_of_le hc0 (hac x)
  have hDP := isProbabilityMeasure_densLaw ν hd hc0 hc hC hnorm
  have hDν : densLaw ν d ≪ ν := withDensity_absolutelyContinuous ν _
  have hDfin : klDiv (densLaw ν d) ν ≠ ⊤ := klDiv_densLaw_ne_top ν hd hc0 hc hC
  have hllr : Integrable (llr (densLaw ν d) ν) (densLaw ν d) := (klDiv_ne_top_iff.1 hDfin).2
  have hla : ∀ x, |Real.log (a x)| ≤ max (|Real.log c|) (|Real.log C|) := fun x ↦
    abs_log_le_of_mem hc0 (hac x) (haC x)
  have hlc : ∀ x, |Real.log (cg x)| ≤ G := fun x ↦ by
    rw [abs_le]
    constructor
    · have := Real.log_le_log (Real.exp_pos _) (hcg0 x)
      rwa [Real.log_exp] at this
    · have := Real.log_le_log (hcgpos x) (hcgG x)
      rwa [Real.log_exp] at this
  have hf1 : Bdd fun x ↦ g x + Real.log (a x) - Real.log (cg x) :=
    ⟨(hg.add ham'.log).sub hcgm'.log, G + max (|Real.log c|) (|Real.log C|) + G, fun x ↦ by
      refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hG x) (hla x)))
        (hlc x))⟩
  have hf2 : Bdd fun x ↦ Real.log (a x) := ⟨ham'.log, _, hla⟩
  have hZ1 : ∫ x, Real.exp (g x + Real.log (a x) - Real.log (cg x)) ∂ν = 1 := by
    rw [← integral_condTilt hS ν hc0 hnorm ham hac haC ha hg hG hcgm hcg0 hcg]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [Real.exp_sub, Real.exp_add, Real.exp_log (hapos x), Real.exp_log (hcgpos x)]
    ring
  have hZ2 : ∫ x, Real.exp (Real.log (a x)) ∂ν = 1 := by
    rw [← integral_condDens hS ν hnorm ha]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ Real.exp_log (hapos x))
  have hDV1 := integral_sub_log_le_toReal_klDiv ν (densLaw ν d) hDν hllr hf1
  have hDV2 := integral_sub_log_le_toReal_klDiv ν (densLaw ν d) hDν hllr hf2
  rw [hZ1, Real.log_one, sub_zero] at hDV1
  rw [hZ2, Real.log_one, sub_zero] at hDV2
  rw [condTilt_eq_tilted hS ν hc0 hnorm ham hac haC ha hg hG hcgm hcg0 hcg,
    densLaw_eq_tilted_log ν hapos (integral_condDens hS ν hnorm ha),
    klDiv_tilted_right_eq ν _ hDν hDfin hf1, klDiv_tilted_right_eq ν _ hDν hDfin hf2, hZ1, hZ2,
    Real.log_one, add_zero, add_zero, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith)]
  have hgi := integrable_densLaw_of_abs_le ν hd hc0 hc hC hnorm hg hG
  have hai := integrable_densLaw_of_abs_le ν hd hc0 hc hC hnorm ham'.log hla
  have hci := integrable_densLaw_of_abs_le ν hd hc0 hc hC hnorm hcgm'.log hlc
  have hga : Integrable (fun x ↦ g x + Real.log (a x)) (densLaw ν d) := hgi.add hai
  rw [integral_sub hga hci, integral_add hgi hai]
  ring

omit [Nonempty X] in
/-- **The conditional Donsker–Varadhan inequality**: for every bounded `g`,
`E_D g − E_D log E_ν[e^g | σ(S)] ≤ KL(D ‖ aν)`. -/
theorem condDV_le :
    ∫ x, g x ∂densLaw ν d - ∫ x, Real.log (cg x) ∂densLaw ν d ≤
      (klDiv (densLaw ν d) (densLaw ν a)).toReal := by
  have h := toReal_klDiv_condTilt hS ν hd hc0 hc hC hnorm ham hac haC ha hg hG hcgm hcg0 hcgG hcg
  have h0 : 0 ≤ (klDiv (densLaw ν d)
      (densLaw ν (fun x ↦ Real.exp (g x) / cg x * a x))).toReal := ENNReal.toReal_nonneg
  linarith

end CondTilt

omit [Nonempty X] in
/-- **Attainment**: the test `g₀ = log d − log a` has `E_ν[e^{g₀} | σ(S)] = 1` and
`E_D g₀ = KL(D ‖ aν)`. -/
theorem condDV_attained :
    ((ν[fun x ↦ Real.exp (Real.log (d x) - Real.log (a x)) | statSigma S]) =ᵐ[ν]
      fun _ ↦ (1 : ℝ)) ∧
      ∫ x, (Real.log (d x) - Real.log (a x)) ∂densLaw ν d =
        (klDiv (densLaw ν d) (densLaw ν a)).toReal := by
  have hm := statSigma_le hS
  have ham' : Measurable a := ham.mono hm le_rfl
  have hapos : ∀ x, 0 < a x := fun x ↦ lt_of_lt_of_le hc0 (hac x)
  have hdpos : ∀ x, 0 < d x := fun x ↦ lt_of_lt_of_le hc0 (hc x)
  have hdi := integrable_of_bounds ν hd hc hC
  -- the conditional expectation of `d/a` is `1`
  have hone : (ν[fun x ↦ Real.exp (Real.log (d x) - Real.log (a x)) | statSigma S]) =ᵐ[ν]
      fun _ ↦ 1 := by
    have e : (fun x ↦ Real.exp (Real.log (d x) - Real.log (a x))) = (fun x ↦ (a x)⁻¹) * d := by
      funext x
      rw [Pi.mul_apply, Real.exp_sub, Real.exp_log (hdpos x), Real.exp_log (hapos x),
        div_eq_inv_mul]
    have hinv : StronglyMeasurable[statSigma S] fun x ↦ (a x)⁻¹ := ham.inv.stronglyMeasurable
    have hinvd : Integrable ((fun x ↦ (a x)⁻¹) * d) ν := by
      refine hdi.bdd_mul (c := c⁻¹) (ham'.inv).aestronglyMeasurable
        (Eventually.of_forall fun x ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hapos x))]
      exact inv_anti₀ hc0 (hac x)
    rw [e]
    have h := condExp_mul_of_stronglyMeasurable_left (μ := ν) (m := statSigma S) hinv hinvd hdi
    filter_upwards [h, ha] with x hx hx2
    rw [hx, Pi.mul_apply, ← hx2, inv_mul_cancel₀ (hapos x).ne']
  refine ⟨hone, ?_⟩
  -- the identity at `g₀`, `cg = 1`
  have hg0m : Measurable fun x ↦ Real.log (d x) - Real.log (a x) := hd.log.sub ham'.log
  have hG0 : ∀ x, |Real.log (d x) - Real.log (a x)| ≤
      max (|Real.log c|) (|Real.log C|) + max (|Real.log c|) (|Real.log C|) := fun x ↦
    (abs_sub _ _).trans (add_le_add (abs_log_le_of_mem hc0 (hc x) (hC x))
      (abs_log_le_of_mem hc0 (hac x) (haC x)))
  have hG0nn : 0 ≤ max (|Real.log c|) (|Real.log C|) + max (|Real.log c|) (|Real.log C|) := by
    positivity
  have h := toReal_klDiv_condTilt hS ν hd hc0 hc hC hnorm ham hac haC ha hg0m hG0
    (cg := fun _ ↦ 1) measurable_const (fun x ↦ Real.exp_le_one_iff.2 (by linarith))
    (fun x ↦ Real.one_le_exp hG0nn) hone.symm
  have e : (fun x ↦ Real.exp (Real.log (d x) - Real.log (a x)) / (fun _ ↦ (1 : ℝ)) x * a x) =
      d := by
    funext x
    simp only [div_one, Real.exp_sub, Real.exp_log (hdpos x), Real.exp_log (hapos x)]
    exact div_mul_cancel₀ _ (hapos x).ne'
  have hDP := isProbabilityMeasure_densLaw ν hd hc0 hc hC hnorm
  rw [e, klDiv_self, ENNReal.toReal_zero] at h
  simp only [Real.log_one, integral_zero, add_zero] at h
  linarith

/-- **The conditional variational formula**: the fibre information is the maximum over bounded tests
of `E_D g − E_D log E_ν[e^g | σ(S)]`, attained at `g = log(d/a)`. -/
theorem fibre_isGreatest_condDV :
    IsGreatest {v : ℝ | ∃ g : X → ℝ, Bdd g ∧ v = ∫ x, g x ∂densLaw ν d -
        ∫ x, Real.log ((ν[fun y ↦ Real.exp (g y) | statSigma S]) x) ∂densLaw ν d}
      (klDiv (densLaw ν d) (statisticLift ν (densLaw ν d) (statPoint S))).toReal := by
  have hm := statSigma_le hS
  have ham' : Measurable a := ham.mono hm le_rfl
  have hDν : densLaw ν d ≪ ν := withDensity_absolutelyContinuous ν _
  rw [statisticLift_densLaw_eq_condDens hS ν hd hc0 hc hC hnorm ha]
  obtain ⟨hone, hval⟩ := condDV_attained hS ν hd hc0 hc hC hnorm ham hac haC ha
  constructor
  · refine ⟨fun x ↦ Real.log (d x) - Real.log (a x), ⟨hd.log.sub ham'.log, _, fun x ↦
      (abs_sub _ _).trans (add_le_add (abs_log_le_of_mem hc0 (hc x) (hC x))
        (abs_log_le_of_mem hc0 (hac x) (haC x)))⟩, ?_⟩
    have h0 : ∫ x, Real.log ((ν[fun y ↦ Real.exp (Real.log (d y) - Real.log (a y)) |
        statSigma S]) x) ∂densLaw ν d = 0 := by
      rw [← integral_zero X ℝ (μ := densLaw ν d)]
      refine integral_congr_ae ?_
      filter_upwards [hDν.ae_eq hone] with x hx
      rw [hx, Real.log_one]
    rw [h0, sub_zero, hval]
  · rintro v ⟨g, hg, rfl⟩
    obtain ⟨hgm, G, hG⟩ := hg
    obtain ⟨cg, hcgm, hcg0, hcgG, hcg⟩ := exists_condDens hS ν (d := fun x ↦ Real.exp (g x))
      hgm.exp (c := Real.exp (-G)) (fun x ↦ Real.exp_le_exp.2 (by linarith [(abs_le.1 (hG x)).1]))
      (C := Real.exp G) (fun x ↦ Real.exp_le_exp.2 ((le_abs_self _).trans (hG x)))
    have h := condDV_le hS ν hd hc0 hc hC hnorm ham hac haC ha hgm hG hcgm hcg0 hcgG hcg
    have e : ∫ x, Real.log ((ν[fun y ↦ Real.exp (g y) | statSigma S]) x) ∂densLaw ν d =
        ∫ x, Real.log (cg x) ∂densLaw ν d := by
      refine integral_congr_ae ?_
      filter_upwards [hDν.ae_eq hcg] with x hx
      rw [hx]
    rw [e]
    exact h

end Variational

end Laplace.Multi
