/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFisherEnergyVariation
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Stationarity of the Fisher energy characterises Levi-Civita geodesics

The converse of the first variation: a `C²` path `θ` in the response chart is stationary for the
Fisher energy under every fixed-endpoint test variation `Θ(s,t) = θ(t) + s φ(t) z` (`φ` a `C²`
scalar vanishing outside `(0,1)`, `z ∈ W`) **iff** it satisfies the Levi-Civita geodesic equation
`θ'' + ½ C_θ(θ',θ') = 0` on `(0,1)`.

* `lcAccel`: the Levi-Civita acceleration `a(t) = θ''(t) + ½ C_{θ(t)}(θ'(t),θ'(t))`.
* `TestField`: a `C²` scalar test function with explicit derivatives, vanishing outside `(0,1)`;
  `TestField.ofBump` realises a Mathlib smooth bump supported in a ball inside `(0,1)`.
* `testVariation`: the fixed-endpoint variation `θ + (s φ) z` as a `FisherVariation`;
  `hasDerivAt_fisherEnergy_testVariation`: its energy derivative at `s = 0` is
  `−∫₀¹ φ(t) G_{θ(t)}(z, a(t)) dt`.
* `lcAccel_eq_zero_of_testPairings`: **the analytic core** — if all test pairings vanish, the
  acceleration vanishes on `(0,1)` (positive definiteness of `G`, continuity, a bump).
* `stationary_fisherEnergy_iff_lcGeodesic`: **stationarity ⇔ Levi-Civita geodesic**.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Stationarity

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The Levi-Civita acceleration `a(t) = θ''(t) + ½ C_{θ(t)}(θ'(t), θ'(t))` of a path with velocity
`V` and acceleration `A`. -/
noncomputable def lcAccel (θ V A : ℝ → 𝕍) (t : ℝ) : 𝕍 :=
  A t + (1 / 2 : ℝ) • mChristoffel hS ν (θ t) (V t) (V t)

omit hS in
/-- A `C²` scalar test function with explicit derivatives, vanishing outside `(0,1)`. -/
structure TestField where
  /-- The test function. -/
  φ : ℝ → ℝ
  /-- Its derivative. -/
  φ' : ℝ → ℝ
  /-- Its second derivative. -/
  φ'' : ℝ → ℝ
  hasDerivAt : ∀ t, HasDerivAt φ (φ' t) t
  hasDerivAt' : ∀ t, HasDerivAt φ' (φ'' t) t
  continuous'' : Continuous φ''
  zero_outside : ∀ t, t ∉ Ioo (0 : ℝ) 1 → φ t = 0

omit hS in
theorem TestField.continuous (φ : TestField) : Continuous φ.φ :=
  continuous_iff_continuousAt.mpr fun t ↦ (φ.hasDerivAt t).continuousAt

omit hS in
theorem TestField.continuous' (φ : TestField) : Continuous φ.φ' :=
  continuous_iff_continuousAt.mpr fun t ↦ (φ.hasDerivAt' t).continuousAt

omit hS in
theorem TestField.zero (φ : TestField) : φ.φ 0 = 0 :=
  φ.zero_outside 0 fun h ↦ lt_irrefl _ h.1

omit hS in
theorem TestField.one (φ : TestField) : φ.φ 1 = 0 :=
  φ.zero_outside 1 fun h ↦ lt_irrefl _ h.2

omit hS in
/-- A smooth bump centred at `c` with outer radius `r`, `closedBall c r ⊆ (0,1)`, as a test
field. -/
noncomputable def TestField.ofBump {c : ℝ} (f : ContDiffBump c)
    (hf : Metric.closedBall c f.rOut ⊆ Ioo (0 : ℝ) 1) : TestField where
  φ := f
  φ' := deriv f
  φ'' := deriv (deriv f)
  hasDerivAt t := ((contDiff_infty_iff_deriv.mp f.contDiff).1 t).hasDerivAt
  hasDerivAt' t :=
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp f.contDiff).2).1 t).hasDerivAt
  continuous'' :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp f.contDiff).2).2.continuous
  zero_outside t ht := by
    apply f.zero_of_le_dist
    by_contra h
    push Not at h
    exact ht (hf (Metric.mem_closedBall.mpr h.le))

omit hS in
theorem TestField.ofBump_apply {c : ℝ} (f : ContDiffBump c)
    (hf : Metric.closedBall c f.rOut ⊆ Ioo (0 : ℝ) 1) (t : ℝ) :
    (TestField.ofBump f hf).φ t = f t := rfl

omit hS in
variable (S) in
/-- A `C²` path in the direction space: velocity and acceleration with continuity. -/
structure C2Path where
  /-- The path. -/
  θ : ℝ → 𝕍
  /-- Its velocity. -/
  V : ℝ → 𝕍
  /-- Its acceleration. -/
  A : ℝ → 𝕍
  hasDerivAt : ∀ t, HasDerivAt θ (V t) t
  hasDerivAt' : ∀ t, HasDerivAt V (A t) t
  continuous_A : Continuous A

omit hS [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
theorem C2Path.continuous (γ : C2Path S ν) : Continuous γ.θ :=
  continuous_iff_continuousAt.mpr fun t ↦ (γ.hasDerivAt t).continuousAt

omit hS [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
theorem C2Path.continuous_V (γ : C2Path S ν) : Continuous γ.V :=
  continuous_iff_continuousAt.mpr fun t ↦ (γ.hasDerivAt' t).continuousAt

omit hS in
/-- The fixed-endpoint test variation `Θ(s,t) = θ(t) + (s φ(t)) z` of a `C²` path. -/
noncomputable def testVariation (γ : C2Path S ν) (φ : TestField) (z : 𝕍) :
    FisherVariation S ν where
  Θ s t := γ.θ t + (s * φ.φ t) • z
  V s t := γ.V t + (s * φ.φ' t) • z
  A s t := γ.A t + (s * φ.φ'' t) • z
  U _ t := φ.φ t • z
  W _ t := φ.φ' t • z
  hasDerivAt_t s t := (γ.hasDerivAt t).add (((φ.hasDerivAt t).const_mul s).smul_const z)
  hasDerivAt_tt s t := (γ.hasDerivAt' t).add (((φ.hasDerivAt' t).const_mul s).smul_const z)
  hasDerivAt_s s t := by
    have h := (((hasDerivAt_id s).mul_const (φ.φ t)).smul_const z).const_add (γ.θ t)
    simpa only [id_eq, one_mul] using h
  hasDerivAt_st s t := by
    have h := (((hasDerivAt_id s).mul_const (φ.φ' t)).smul_const z).const_add (γ.V t)
    simpa only [id_eq, one_mul] using h
  hasDerivAt_ts _ t := (φ.hasDerivAt t).smul_const z
  continuous_Θ := (γ.continuous.comp continuous_snd).add
    ((continuous_fst.mul (φ.continuous.comp continuous_snd)).smul continuous_const)
  continuous_V := (γ.continuous_V.comp continuous_snd).add
    ((continuous_fst.mul (φ.continuous'.comp continuous_snd)).smul continuous_const)
  continuous_A := (γ.continuous_A.comp continuous_snd).add
    ((continuous_fst.mul (φ.continuous''.comp continuous_snd)).smul continuous_const)
  continuous_U := (φ.continuous.comp continuous_snd).smul continuous_const
  continuous_W := (φ.continuous'.comp continuous_snd).smul continuous_const

/-- **The energy derivative under a test variation**: `E'(0) = −∫₀¹ φ(t) G_{θ(t)}(z, a(t)) dt`. -/
theorem hasDerivAt_fisherEnergy_testVariation (γ : C2Path S ν) (φ : TestField) (z : 𝕍) :
    HasDerivAt (fisherEnergy ν (testVariation ν γ φ z))
      (-∫ t in (0 : ℝ)..1, φ.φ t * G (γ.θ t) z (lcAccel hS ν γ.θ γ.V γ.A t)) 0 := by
  have h := fisherEnergy_variation hS ν (testVariation ν γ φ z)
  simp only [testVariation, zero_mul, zero_smul, add_zero, φ.zero, φ.one, fisherInner_zero_left,
    sub_zero, zero_sub] at h
  refine h.congr_deriv ?_
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [lcAccel, fisherInner_smul_left]

/-- **The analytic core**: if every test pairing `∫₀¹ φ G(z, a)` vanishes, the Levi-Civita
acceleration vanishes on `(0,1)`. -/
theorem lcAccel_eq_zero_of_testPairings (γ : C2Path S ν)
    (hpair : ∀ (φ : TestField) (z : 𝕍),
      ∫ t in (0 : ℝ)..1, φ.φ t * G (γ.θ t) z (lcAccel hS ν γ.θ γ.V γ.A t) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) 1, lcAccel hS ν γ.θ γ.V γ.A t = 0 := by
  intro t₀ ht₀
  by_contra hne
  set a := lcAccel hS ν γ.θ γ.V γ.A with ha
  -- continuity of the acceleration and of the pairing
  have hac : Continuous a := by
    rw [ha]
    unfold lcAccel
    have h := (continuous_mChristoffel hS ν).comp
      (γ.continuous.prodMk (γ.continuous_V.prodMk γ.continuous_V))
    have h' : Continuous fun t ↦ mChristoffel hS ν (γ.θ t) (γ.V t) (γ.V t) := by
      simpa only [Function.comp_def] using h
    exact γ.continuous_A.add (h'.const_smul (1 / 2 : ℝ))
  set z := a t₀ with hz
  have hg : Continuous fun t ↦ G (γ.θ t) z (a t) := by
    have h := (continuous_fisherInner hS ν).comp
      (γ.continuous.prodMk ((continuous_const (y := z)).prodMk hac))
    simpa only [Function.comp_def] using h
  have hpos : 0 < G (γ.θ t₀) z (a t₀) := by rw [← hz]; exact fisherInner_self_pos hS ν _ hne
  -- a ball around `t₀` inside `(0,1)` on which the pairing is positive
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.ball t₀ r ⊆
      {t | 0 < G (γ.θ t) z (a t)} ∩ Ioo 0 1 := by
    have hopen : IsOpen ({t | 0 < G (γ.θ t) z (a t)} ∩ Ioo (0 : ℝ) 1) :=
      (isOpen_lt continuous_const hg).inter isOpen_Ioo
    exact Metric.isOpen_iff.mp hopen t₀ ⟨hpos, ht₀⟩
  -- the bump with outer radius `r/2`
  let f : ContDiffBump t₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hf : Metric.closedBall t₀ f.rOut ⊆ Ioo (0 : ℝ) 1 := fun t ht ↦
    (hball (Metric.closedBall_subset_ball (by change r / 2 < r; linarith) ht)).2
  have hkey := hpair (TestField.ofBump f hf) z
  simp only [TestField.ofBump_apply] at hkey
  -- the integrand is nonnegative with support the ball, so the integral is positive
  have hnn : ∀ t, 0 ≤ f t * G (γ.θ t) z (a t) := by
    intro t
    by_cases ht : t ∈ Metric.ball t₀ f.rOut
    · exact mul_nonneg f.nonneg
        (hball (Metric.ball_subset_ball (by change r / 2 ≤ r; linarith) ht)).1.le
    · rw [f.zero_of_le_dist (not_lt.mp fun h ↦ ht (Metric.mem_ball.mpr h)), zero_mul]
  have hcont : Continuous fun t ↦ f t * G (γ.θ t) z (a t) := f.continuous.mul hg
  have hsupp : Function.support (fun t ↦ f t * G (γ.θ t) z (a t)) = Metric.ball t₀ f.rOut := by
    ext t
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
    constructor
    · intro h
      by_contra ht
      exact h.1 (f.zero_of_le_dist (not_lt.mp fun h' ↦ ht (Metric.mem_ball.mpr h')))
    · intro ht
      exact ⟨(f.pos_of_mem_ball ht).ne',
        (hball (Metric.ball_subset_ball (by change r / 2 ≤ r; linarith) ht)).1.ne'⟩
  have hgt : 0 < ∫ t in (0 : ℝ)..1, f t * G (γ.θ t) z (a t) := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' (ae_of_all _ hnn)
      (hcont.intervalIntegrable 0 1)]
    refine ⟨zero_lt_one, ?_⟩
    rw [hsupp]
    have hsub : Metric.ball t₀ f.rOut ⊆ Metric.ball t₀ f.rOut ∩ Ioc 0 1 := fun t ht ↦
      ⟨ht, let h := hf (Metric.ball_subset_closedBall ht); ⟨h.1, h.2.le⟩⟩
    exact lt_of_lt_of_le (Metric.measure_ball_pos volume t₀ (f.rIn_pos.trans f.rIn_lt_rOut))
      (measure_mono hsub)
  rw [hkey] at hgt
  exact lt_irrefl _ hgt

omit hS in
/-- **Stationarity for fixed-endpoint test variations.** -/
def StationaryFixedEndpoints (γ : C2Path S ν) : Prop :=
  ∀ (φ : TestField) (z : 𝕍), HasDerivAt (fisherEnergy ν (testVariation ν γ φ z)) 0 0

/-- **Stationarity of the Fisher energy ⇔ the Levi-Civita geodesic equation on `(0,1)`.** -/
theorem stationary_fisherEnergy_iff_lcGeodesic (γ : C2Path S ν) :
    StationaryFixedEndpoints ν γ ↔ ∀ t ∈ Ioo (0 : ℝ) 1, lcAccel hS ν γ.θ γ.V γ.A t = 0 := by
  constructor
  · intro hstat
    refine lcAccel_eq_zero_of_testPairings hS ν γ fun φ z ↦ ?_
    have h := (hasDerivAt_fisherEnergy_testVariation hS ν γ φ z).unique (hstat φ z)
    linarith
  · intro hgeo φ z
    refine (hasDerivAt_fisherEnergy_testVariation hS ν γ φ z).congr_deriv ?_
    rw [neg_eq_zero]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_le zero_le_one] at ht
    by_cases hint : t ∈ Ioo (0 : ℝ) 1
    · simp only [hgeo t hint, fisherInner_zero_right, mul_zero]
    · simp only [φ.zero_outside t hint, zero_mul]

end Stationarity

end Laplace.Multi
