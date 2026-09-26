/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LiftDensity
import Laplace.Multi.ResidualQuadratic

/-!
# The fibre and marginal residuals along a tilt are quadratic

Along the tilts `ν_t ∝ e^{tf} ν`, with `h = f − E_ν f`, `g = E_ν[h | σ(S)]` the conditional score
and `a` the regression coefficient of `f` on the statistic (`⟨a, u⟩ = ‖B₀h‖²`):

* `KL(ν_t↑ ‖ ν)/t² → (∫ g²)/2`                     (`tendsto_klDiv_statisticLift_tilt_div_sq`)
* fibre: `KL(ν_t ‖ ν_t↑)/t² → (∫ (h − g)²)/2`         (`tendsto_klDiv_tilt_statisticLift_div_sq`)
* marginal: `KL(S_*ν_t ‖ S_*Π(M_t))/t² → (∫ g² − ⟨a,u⟩)/2`   (`tendsto_klDiv_map_tilt_div_sq`)

Together with `‖h‖²/2` for the total and `‖B₀h‖²/2` for the visible information, this is the full
quadratic shadow of `KL(D‖ν) = 𝓘(M_D) + R + L` as the three-way Pythagoras
`‖h‖² = ‖Bh‖² + ‖Ch − Bh‖² + ‖h − Ch‖²` of the nested projections: at the featureless point the
nonlinear information split and the linear split of scores are the same geometry.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Basic

variable {X : Type*} [MeasurableSpace X] {J : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The remainder of the tilt density: `e_t = p_t − 1 − t(f − E_ν f)`. -/
noncomputable def tiltErr (f : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  tiltDens ν f t x - (1 + t * (f x - ∫ y, f y ∂ν))

omit hS in
/-- `E_ν[g · h | σ(S)] = g · E_ν[h | σ(S)]` integrated: `∫ g h = ∫ g²` for `g = E_ν[h|σ(S)]`. -/
theorem integral_condExp_mul_self {h : X → ℝ} (hh : Bdd h)
    (hm : statSigma S ≤ ‹MeasurableSpace X›) :
    ∫ x, (ν[h | statSigma S]) x * h x ∂ν = ∫ x, (ν[h | statSigma S]) x ^ 2 ∂ν := by
  obtain ⟨hhm, B, hB⟩ := hh
  have hgb : ∀ᵐ x ∂ν, ‖(ν[h | statSigma S]) x‖ ≤ B := by
    filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (Eventually.of_forall hB)] with x hx
    rw [Real.norm_eq_abs]
    exact hx
  have hi := integrable_of_bdd_prob ν ⟨hhm, B, hB⟩
  have hpull := condExp_stronglyMeasurable_mul_of_bound hm stronglyMeasurable_condExp hi B hgb
  have h1 : ∫ x, (ν[(ν[h | statSigma S]) * h | statSigma S]) x ∂ν =
      ∫ x, ((ν[h | statSigma S]) * h) x ∂ν := integral_condExp hm
  rw [integral_congr_ae hpull] at h1
  simp only [Pi.mul_apply] at h1
  rw [← h1]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- **The conditional density expansion**: `E[p_t | σ(S)] = 1 + t E[h | σ(S)] + E[e_t | σ(S)]`. -/
theorem condExp_tiltDens_ae_eq {f : X → ℝ} (hf : Bdd f) (t : ℝ) :
    ν[tiltDens ν f t | statSigma S] =ᵐ[ν] fun x ↦
      1 + t * (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x +
        (ν[tiltErr ν f t | statSigma S]) x := by
  have hm := statSigma_le hS
  obtain ⟨hfm, B, hB⟩ := hf
  have hint_h : Integrable (fun y ↦ f y - ∫ z, f z ∂ν) ν :=
    (integrable_of_bdd_prob ν ⟨hfm, B, hB⟩).sub (integrable_const _)
  have hint_p : Integrable (tiltDens ν f t) ν :=
    (integrable_exp_of_bdd ν (Bdd.const_mul t ⟨hfm, B, hB⟩)).div_const _
  have hint_lin : Integrable ((fun _ ↦ (1 : ℝ)) + fun y ↦ t * (f y - ∫ z, f z ∂ν)) ν :=
    (integrable_const 1).add (hint_h.const_mul t)
  have hint_e : Integrable (tiltErr ν f t) ν := by
    refine (hint_p.sub hint_lin).congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply, Pi.add_apply, tiltErr]
  have e : tiltDens ν f t = ((fun _ ↦ (1 : ℝ)) + fun y ↦ t * (f y - ∫ z, f z ∂ν)) + tiltErr ν
      f t := by
    funext x
    simp only [Pi.add_apply, tiltErr]
    ring
  rw [e]
  have h1 := condExp_add hint_lin hint_e (m := statSigma S)
  have h2 := condExp_add (integrable_const (1 : ℝ)) (hint_h.const_mul t) (m := statSigma S)
  have e3 : (fun y ↦ t * (f y - ∫ z, f z ∂ν)) = t • fun y ↦ f y - ∫ z, f z ∂ν := by
    funext y
    simp
  have h3 := condExp_smul (m := statSigma S) (μ := ν) t (fun y ↦ f y - ∫ z, f z ∂ν)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, Pi.add_apply, hx2, Pi.add_apply, condExp_const hm, e3, hx3, Pi.smul_apply, smul_eq_mul]

omit hS in
/-- For `|t| ≤ 1/(8(B+1))` the tilt density lies in `[1/2, 2]`. -/
theorem tiltDens_mem_Icc {f : X → ℝ} (hfm : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |f x| ≤ B) {t : ℝ} (ht : |t| ≤ 1 / (8 * (B + 1))) (x : X) :
    1 / 2 ≤ tiltDens ν f t x ∧ tiltDens ν f t x ≤ 2 := by
  have ht' : |t| ≤ 1 / (4 * (B + 1)) := by
    refine ht.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h := tiltDens_sub_le ν hfm hB0 hB ht' x
  have hEf : |∫ y, f y ∂ν| ≤ B := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_const B)
      (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hB y)).trans ?_
    rw [integral_const, probReal_univ, one_smul]
  have hh : |f x - ∫ y, f y ∂ν| ≤ 2 * B := by
    calc |f x - ∫ y, f y ∂ν| ≤ |f x| + |∫ y, f y ∂ν| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB x) hEf
      _ = 2 * B := by ring
  have htB : |t| * (B + 1) ≤ 1 / 8 := by
    calc |t| * (B + 1) ≤ 1 / (8 * (B + 1)) * (B + 1) := by gcongr
      _ = 1 / 8 := by field_simp
  have h1 : |t * (f x - ∫ y, f y ∂ν)| ≤ 1 / 4 := by
    rw [abs_mul]
    calc |t| * |f x - ∫ y, f y ∂ν| ≤ |t| * (2 * B) := by gcongr
      _ ≤ 2 * (|t| * (B + 1)) := by nlinarith [abs_nonneg t]
      _ ≤ 1 / 4 := by linarith
  have h2 : 9 * B ^ 2 * t ^ 2 ≤ 9 / 64 := by
    have : (|t| * (B + 1)) ^ 2 ≤ (1 / 8) ^ 2 := pow_le_pow_left₀ (by positivity) htB 2
    rw [mul_pow, sq_abs] at this
    nlinarith [sq_nonneg t, sq_nonneg B, mul_nonneg (sq_nonneg t) hB0]
  have h3 := abs_le.1 h
  have h4 := abs_le.1 h1
  constructor <;> linarith

end Basic

section Lift

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The information of the lifted tilt is quadratic**: `KL(ν_t↑ ‖ ν)/t² → (∫ g²)/2` with
`g = E_ν[f − E_ν f | σ(S)]` the conditional score. -/
theorem tendsto_klDiv_statisticLift_tilt_div_sq {f : X → ℝ} (hf : Bdd f) :
    Tendsto (fun t ↦ (klDiv (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S)) ν).toReal /
        t ^ 2) (𝓝[≠] 0)
      (𝓝 ((∫ x, (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x ^ 2 ∂ν) / 2)) := by
  obtain ⟨hfm, B, hB⟩ := hf
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  have hm := statSigma_le hS
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (8 * (B + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hbounds : ∀ t, |t| ≤ δ → ∀ x, 1 / 2 ≤ tiltDens ν f t x ∧ tiltDens ν f t x ≤ 2 :=
    fun t ht x ↦ tiltDens_mem_Icc ν hfm hB0 hB (by rw [hδdef] at ht; exact ht) x
  have hkl : ∀ t, |t| ≤ δ →
      (klDiv (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S)) ν).toReal =
        ∫ x, klFun ((ν[tiltDens ν f t | statSigma S]) x) ∂ν := by
    intro t ht
    have hpm : Measurable (tiltDens ν f t) :=
      (Real.measurable_exp.comp (hfm.const_mul t)).div_const _
    have hpi : Integrable (tiltDens ν f t) ν :=
      (integrable_exp_of_bdd ν (Bdd.const_mul t ⟨hfm, B, hB⟩)).div_const _
    have hp0 : 0 ≤ᵐ[ν] tiltDens ν f t :=
      Eventually.of_forall fun x ↦ by
        simp only [Pi.zero_apply]
        linarith [(hbounds t ht x).1]
    have : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (tiltDens ν f t x)) :=
      isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (Bdd.const_mul t ⟨hfm, B, hB⟩))
    rw [tilted_eq_withDensity_tiltDens, statisticLift_eq_withDensity_condExp hS ν hpm hpi hp0]
    refine toReal_klDiv_withDensity_ofReal_ae ν (C := 2)
      (stronglyMeasurable_condExp.measurable.mono hm le_rfl) one_half_pos ?_ ?_
    · have := condExp_mono (m := statSigma S) (integrable_const (1 / 2 : ℝ)) hpi
        (Eventually.of_forall fun x ↦ (hbounds t ht x).1)
      rw [condExp_const hm] at this
      exact this
    · have := condExp_mono (m := statSigma S) hpi (integrable_const (2 : ℝ))
        (Eventually.of_forall fun x ↦ (hbounds t ht x).2)
      rw [condExp_const hm] at this
      exact this
  have hh2B : ∀ x, |f x - ∫ z, f z ∂ν| ≤ 2 * B := fun x ↦ by
    have hEf : |∫ y, f y ∂ν| ≤ B := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le (integrable_const B)
        (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hB y)).trans ?_
      rw [integral_const, probReal_univ, one_smul]
    calc |f x - ∫ y, f y ∂ν| ≤ |f x| + |∫ y, f y ∂ν| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB x) hEf
      _ = 2 * B := by ring
  have hgm : AEStronglyMeasurable (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) ν :=
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have hgB : ∀ᵐ x ∂ν, |(ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x| ≤ 2 * B :=
    ae_bdd_abs_condExp_of_ae_bdd_abs (Eventually.of_forall hh2B)
  have hq : ∀ t, ∀ᵐ x ∂ν, (ν[tiltDens ν f t | statSigma S]) x =
      1 + t * (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x +
        (ν[tiltErr ν f t | statSigma S]) x := fun t ↦ by
    filter_upwards [condExp_tiltDens_ae_eq hS ν ⟨hfm, B, hB⟩ t] with x hx
    exact hx
  have he : ∀ t, |t| ≤ δ → ∀ᵐ x ∂ν, |(ν[tiltErr ν f t | statSigma S]) x| ≤ 9 * B ^ 2 * t ^ 2 := by
    intro t ht
    have ht' : |t| ≤ 1 / (4 * (B + 1)) := by
      rw [hδdef] at ht
      refine ht.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact ae_bdd_abs_condExp_of_ae_bdd_abs
      (Eventually.of_forall fun x ↦ tiltDens_sub_le ν hfm hB0 hB ht' x)
  have hqm : ∀ t, AEStronglyMeasurable (ν[tiltDens ν f t | statSigma S]) ν := fun t ↦
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have hlim := tendsto_integral_klFun_div_sq ν hgm (by positivity : (0 : ℝ) ≤ 2 * B) hgB hq hδ
    (by positivity) he hqm
  refine hlim.congr' ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds (0 : ℝ) hδ)] with t ht
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
  rw [hkl t ht]

/-- **The fibre residual along a tilt is quadratic**: `KL(ν_t ‖ ν_t↑)/t² → (∫ (h − g)²)/2` with
`h = f − E_ν f` and `g = E_ν[h | σ(S)]`. -/
theorem tendsto_klDiv_tilt_statisticLift_div_sq {f : X → ℝ} (hf : Bdd f) :
    Tendsto (fun t ↦ (klDiv (ν.tilted fun x ↦ t * f x)
        (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S))).toReal / t ^ 2) (𝓝[≠] 0)
      (𝓝 ((∫ x, ((f x - ∫ z, f z ∂ν) - (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x) ^ 2 ∂ν)
        / 2)) := by
  have hm := statSigma_le hS
  obtain ⟨hfm, B, hB⟩ := hf
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  have hh : Bdd fun y ↦ f y - ∫ z, f z ∂ν := Bdd.sub (⟨hfm, B, hB⟩ : Bdd f) (Bdd.const _)
  -- exact identity: `KL(D‖lift) = KL(D‖ν) − KL(lift‖ν)`
  have hid : ∀ t, (klDiv (ν.tilted fun x ↦ t * f x)
      (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S))).toReal =
      (klDiv (ν.tilted fun x ↦ t * f x) ν).toReal -
        (klDiv (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S)) ν).toReal := by
    intro t
    have hP := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (Bdd.const_mul t ⟨hfm, B, hB⟩))
    have hD : ν.tilted (fun x ↦ t * f x) ≪ ν := tilted_absolutelyContinuous ν _
    have hfin : klDiv (ν.tilted fun x ↦ t * f x) ν ≠ ⊤ := by
      rw [klDiv_tilted_eq ν (Bdd.const_mul t ⟨hfm, B, hB⟩)]
      exact ENNReal.ofReal_ne_top
    have h1 := klDiv_eq_klDiv_statisticLift_add_map ν (ν.tilted fun x ↦ t * f x) (statPoint S)
      (measurable_statPoint hS) hD hfin
    rw [← klDiv_statisticLift_eq_map ν _ (statPoint S) (measurable_statPoint hS) hD] at h1
    have hne1 : klDiv (ν.tilted fun x ↦ t * f x)
        (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S)) ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at h1
      exact hfin h1
    have hne2 : klDiv (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S)) ν ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at h1
      exact hfin h1
    rw [h1, ENNReal.toReal_add hne1 hne2]
    ring
  have hK := tendsto_klDiv_tilted_div_sq ν ⟨hfm, B, hB⟩
  have hL := tendsto_klDiv_statisticLift_tilt_div_sq hS ν ⟨hfm, B, hB⟩
  -- identify the limit: `Var f − ∫ g² = ∫ (h − g)²`
  have hvar : lawCov ν f f = ∫ x, (f x - ∫ z, f z ∂ν) ^ 2 ∂ν := by
    rw [lawCov_self_eq_integral_sq ν ⟨hfm, B, hB⟩]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [hvar] at hK
  have hsum := hK.sub hL
  have hgB : ∀ᵐ x ∂ν, |(ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x| ≤ 2 * B := by
    obtain ⟨-, B', hB'⟩ := hh
    have h2 : ∀ x, |f x - ∫ z, f z ∂ν| ≤ 2 * B := fun x ↦ by
      have hEf : |∫ y, f y ∂ν| ≤ B := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_of_norm_le (integrable_const B)
          (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hB y)).trans ?_
        rw [integral_const, probReal_univ, one_smul]
      calc |f x - ∫ y, f y ∂ν| ≤ |f x| + |∫ y, f y ∂ν| := abs_sub _ _
        _ ≤ B + B := add_le_add (hB x) hEf
        _ = 2 * B := by ring
    exact ae_bdd_abs_condExp_of_ae_bdd_abs (Eventually.of_forall h2)
  have hgm : AEStronglyMeasurable (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) ν :=
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have hg2 : Integrable (fun x ↦ (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x ^ 2) ν := by
    refine Integrable.of_bound (hgm.pow 2) ((2 * B) ^ 2) ?_
    filter_upwards [hgB] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hh2 : Integrable (fun x ↦ (f x - ∫ z, f z ∂ν) ^ 2) ν :=
    (integrable_of_bdd_prob ν (Bdd.mul hh hh)).congr (Eventually.of_forall fun x ↦ by simp [sq])
  have hgh : Integrable (fun x ↦ (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x *
      (f x - ∫ z, f z ∂ν)) ν := by
    refine Integrable.of_bound (hgm.mul (hh.1.aestronglyMeasurable)) (2 * B * (2 * B)) ?_
    filter_upwards [hgB] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    obtain ⟨-, B', hB'⟩ := hh
    have hEf : |∫ y, f y ∂ν| ≤ B := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le (integrable_const B)
        (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hB y)).trans ?_
      rw [integral_const, probReal_univ, one_smul]
    have h2 : |f x - ∫ y, f y ∂ν| ≤ 2 * B := by
      calc |f x - ∫ y, f y ∂ν| ≤ |f x| + |∫ y, f y ∂ν| := abs_sub _ _
        _ ≤ B + B := add_le_add (hB x) hEf
        _ = 2 * B := by ring
    exact mul_le_mul hx h2 (abs_nonneg _) (by linarith)
  have hcross := integral_condExp_mul_self ν hh hm
  have hlimit : (∫ x, (f x - ∫ z, f z ∂ν) ^ 2 ∂ν) / 2 -
      (∫ x, (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x ^ 2 ∂ν) / 2 =
      (∫ x, ((f x - ∫ z, f z ∂ν) - (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x) ^ 2 ∂ν) / 2 := by
    have e : ∫ x, ((f x - ∫ z, f z ∂ν) - (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x) ^ 2 ∂ν =
        ∫ x, ((f x - ∫ z, f z ∂ν) ^ 2 - 2 * ((ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x *
          (f x - ∫ z, f z ∂ν)) + (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x ^ 2) ∂ν :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have hA : Integrable (fun x ↦ (f x - ∫ z, f z ∂ν) ^ 2 -
        2 * ((ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x * (f x - ∫ z, f z ∂ν))) ν :=
      hh2.sub (hgh.const_mul 2)
    rw [e, integral_add hA hg2, integral_sub hh2 (hgh.const_mul 2), integral_const_mul, hcross]
    ring
  rw [← hlimit]
  refine hsum.congr fun t ↦ ?_
  rw [hid t, sub_div]

end Lift

section Marginal

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The marginal residual along a tilt is quadratic**:
`KL(S_*ν_t ‖ S_*Π(M_t))/t² → (∫ g² − ⟨a, u⟩)/2`, with `g` the conditional score and `a` the
regression coefficient (`⟨a,u⟩ = ‖B₀h‖²`). -/
theorem tendsto_klDiv_map_tilt_div_sq {f : X → ℝ} (hf : Bdd f) :
    ∃ a ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      (∀ j, lawCov ν (S j) (dirLoss S a) = lawCov ν (S j) f) ∧
      Tendsto (fun t ↦ (klDiv ((ν.tilted fun x ↦ t * f x).map (statPoint S))
        ((responseProjection hS ν (tiltResponse S ν f t)).map (statPoint S))).toReal / t ^ 2)
        (𝓝[≠] 0)
        (𝓝 (((∫ x, (ν[fun y ↦ f y - ∫ z, f z ∂ν | statSigma S]) x ^ 2 ∂ν) -
          dotJ a (fun j ↦ lawCov ν (S j) f)) / 2)) := by
  obtain ⟨a, ha, hreg, hI⟩ := tendsto_genRate_tiltResponse_div_sq hS ν hf
  refine ⟨a, ha, hreg, ?_⟩
  obtain ⟨hfm, B, hB⟩ := hf
  -- exact identity: `R = KL(lift‖ν) − 𝓘(M_t)`
  have hid : ∀ t, (klDiv ((ν.tilted fun x ↦ t * f x).map (statPoint S))
      ((responseProjection hS ν (tiltResponse S ν f t)).map (statPoint S))).toReal =
      (klDiv (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S)) ν).toReal -
        (genRate ν S (tiltResponse S ν f t)).toReal := by
    intro t
    have hP := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (Bdd.const_mul t ⟨hfm, B, hB⟩))
    have hD : ν.tilted (fun x ↦ t * f x) ≪ ν := tilted_absolutelyContinuous ν _
    have hfin : klDiv (ν.tilted fun x ↦ t * f x) ν ≠ ⊤ := by
      rw [klDiv_tilted_eq ν (Bdd.const_mul t ⟨hfm, B, hB⟩)]
      exact ENNReal.ofReal_ne_top
    have hsplit : klDiv (ν.tilted fun x ↦ t * f x)
        (responseProjection hS ν (tiltResponse S ν f t)) =
        klDiv (ν.tilted fun x ↦ t * f x)
          (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S)) +
        klDiv ((ν.tilted fun x ↦ t * f x).map (statPoint S))
          ((responseProjection hS ν (tiltResponse S ν f t)).map (statPoint S)) :=
      klDiv_responseProjection_eq_statisticLift_add_map' hS ν (ν.tilted fun x ↦ t * f x) hfin
    have htot := klDiv_tilt_eq_genRate_add hS ν ⟨hfm, B, hB⟩ t
    have h1 := klDiv_eq_klDiv_statisticLift_add_map ν (ν.tilted fun x ↦ t * f x) (statPoint S)
      (measurable_statPoint hS) hD hfin
    rw [← klDiv_statisticLift_eq_map ν _ (statPoint S) (measurable_statPoint hS) hD] at h1
    have hne1 : klDiv (ν.tilted fun x ↦ t * f x)
        (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S)) ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at h1
      exact hfin h1
    have hne2 : klDiv (statisticLift ν (ν.tilted fun x ↦ t * f x) (statPoint S)) ν ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at h1
      exact hfin h1
    have hPne : klDiv (ν.tilted fun x ↦ t * f x)
        (responseProjection hS ν (tiltResponse S ν f t)) ≠ ⊤ := by
      intro htop
      obtain ⟨-, -, -, hpyth⟩ := responseProjection_spec hS ν
        (genRate_tiltResponse_ne_top hS ν ⟨hfm, B, hB⟩ t)
      have h := hpyth (ν.tilted fun x ↦ t * f x) inferInstance rfl
      rw [htop, top_add] at h
      exact hfin h
    have hRne : klDiv ((ν.tilted fun x ↦ t * f x).map (statPoint S))
        ((responseProjection hS ν (tiltResponse S ν f t)).map (statPoint S)) ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at hsplit
      exact hPne hsplit
    have hsplit' := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add hne1 hRne] at hsplit'
    have hh1 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_add hne1 hne2] at hh1
    linarith
  have hL := tendsto_klDiv_statisticLift_tilt_div_sq hS ν ⟨hfm, B, hB⟩
  have h := hL.sub hI
  rw [sub_div]
  refine h.congr fun t ↦ ?_
  rw [hid t, sub_div]

end Marginal

end Laplace.Multi
