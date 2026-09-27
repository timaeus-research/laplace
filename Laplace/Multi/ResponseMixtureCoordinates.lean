/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDataHessian
import Laplace.Multi.ExponentialPath

/-!
# Mixture coordinates on the data manifold

The response map `Φ(ρ) = θ(E_ρ S)` is nonlinear in exponential (tilt) coordinates but affine after
passing to expectations. This module builds the **density-affine** data journeys that make this
exact.

* The **local mixture tilt** `g^m_{g,k}(t) = g + log(1 + t k̄)`, `k̄ = k − E_{ρ_g} k`, has law
`dρ_{g^m(t)} = (1 + t k̄) dρ_g` for small `t` (`integral_localMixTilt`), so every expectation is
affine in `t` with slope the covariance with `k`: `E_{ρ_{g^m(t)}} f = E_{ρ_g} f + t
Cov_{ρ_g}(f,k)`, and its mean is `M(g) + t Cov_{ρ_g}(S,k)` (`mean_localMixTilt`,
`eventually_mean_localMixTilt`). Its first-order density perturbation matches that of the
exponential journey `g + t k`. * The **endpoint mixture tilt** `mixTilt g h t = log((1−t) e^g/Z_g +
t e^h/Z_h)` has law `(1−t) ρ_g + t ρ_h` (`integral_mixTilt`) and affine mean `(1−t) M(g) + t M(h)`
(`mean_mixTilt`).

These are the coordinates in which the response fibres are convex and the mixture connection of the
family is transported exactly (the following modules).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section LocalMixture

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]
  {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k)
include hg hk

/-- The centred direction `k̄ = k − E_{ρ_g} k`. -/
noncomputable def centred (g k : X → ℝ) : X → ℝ := fun x ↦ k x - ∫ y, k y ∂ν.tilted g

omit [Nonempty X] [IsProbabilityMeasure ν] hg in
theorem bdd_centred : Bdd (centred ν g k) := hk.sub (Bdd.const _)

omit [Nonempty X] in
theorem integral_centred : ∫ x, centred ν g k x ∂ν.tilted g = 0 := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  unfold centred
  rw [integral_sub (integrable_of_bdd_prob _ hk) (integrable_const _), integral_const,
    probReal_univ, one_smul, sub_self]

omit [Nonempty X] in
/-- `E_{ρ_g}[f k̄] = Cov_{ρ_g}(f, k)`. -/
theorem integral_mul_centred {f : X → ℝ} (hf : Bdd f) :
    ∫ x, f x * centred ν g k x ∂ν.tilted g = lawCov (ν.tilted g) f k := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  unfold centred lawCov
  have e : ∀ x, f x * (k x - ∫ y, k y ∂ν.tilted g) = f x * k x - f x * ∫ y, k y ∂ν.tilted g :=
    fun x ↦ by ring
  simp_rw [e]
  rw [integral_sub (integrable_of_bdd_prob _ (hf.mul hk))
    ((integrable_of_bdd_prob _ hf).mul_const _), integral_mul_const]

variable (g k) in
/-- **The local mixture tilt** `g + log(1 + t k̄)`. -/
noncomputable def localMixTilt (t : ℝ) : X → ℝ :=
  fun x ↦ g x + Real.log (1 + t * centred ν g k x)

omit [IsProbabilityMeasure ν] hg in
/-- For small `t` the local mixture density `1 + t k̄` is pinched between `1/2` and `3/2`. -/
theorem eventually_localMix_bounds :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ x, 1 / 2 ≤ 1 + t * centred ν g k x ∧ 1 + t * centred ν g k x ≤ 3 / 2 := by
  obtain ⟨K, hK⟩ := (bdd_centred ν hk (g := g)).2
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK (Classical.arbitrary X))
  have hε : (0 : ℝ) < 1 / (2 * (K + 1)) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht x
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  have h1 : |t * centred ν g k x| ≤ |t| * K := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg t)
  have h2 : |t| * K ≤ 1 / 2 := by
    calc |t| * K ≤ |t| * (K + 1) := by gcongr; linarith
      _ ≤ 1 / (2 * (K + 1)) * (K + 1) := by gcongr
      _ = 1 / 2 := by field_simp
  constructor
  · nlinarith [neg_abs_le (t * centred ν g k x)]
  · nlinarith [le_abs_self (t * centred ν g k x)]

omit [Nonempty X] [IsProbabilityMeasure ν] in
theorem bdd_localMixTilt {t : ℝ}
    (hb : ∀ x, 1 / 2 ≤ 1 + t * centred ν g k x ∧ 1 + t * centred ν g k x ≤ 3 / 2) :
    Bdd (localMixTilt ν g k t) :=
  hg.add (bdd_log_of_bounds
    (measurable_const.add (measurable_const.mul (hk.1.sub measurable_const))) one_half_pos
    (fun x ↦ (hb x).1) (fun x ↦ (hb x).2))

omit [Nonempty X] in
/-- **The fundamental identity**: under the local mixture tilt every expectation is affine in `t`
with slope the covariance: `E_{ρ_{g^m(t)}} f = E_{ρ_g} f + t Cov_{ρ_g}(f, k)`. -/
theorem integral_localMixTilt {t : ℝ}
    (hb : ∀ x, 1 / 2 ≤ 1 + t * centred ν g k x ∧ 1 + t * centred ν g k x ≤ 3 / 2) {f : X → ℝ}
    (hf : Bdd f) :
    ∫ x, f x ∂ν.tilted (localMixTilt ν g k t) =
      ∫ x, f x ∂ν.tilted g + t * lawCov (ν.tilted g) f k := by
  have hP := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have e : ν.tilted (localMixTilt ν g k t) =
      (ν.tilted g).tilted (fun x ↦ Real.log (1 + t * centred ν g k x)) := by
    rw [tilted_tilted (integrable_exp_of_bdd ν hg)]
    rfl
  rw [e, integral_tilted]
  have hpos : ∀ x, 0 < 1 + t * centred ν g k x := fun x ↦ lt_of_lt_of_le one_half_pos (hb x).1
  have e2 : ∀ x, Real.exp (Real.log (1 + t * centred ν g k x)) = 1 + t * centred ν g k x :=
    fun x ↦ Real.exp_log (hpos x)
  simp_rw [e2]
  have hZ : ∫ x, (1 + t * centred ν g k x) ∂ν.tilted g = 1 := by
    rw [integral_add (integrable_const _)
      ((integrable_of_bdd_prob _ (bdd_centred ν hk)).const_mul t), integral_const, probReal_univ,
      one_smul, integral_const_mul, integral_centred ν hg hk, mul_zero, add_zero]
  rw [hZ]
  simp only [div_one, smul_eq_mul]
  have e3 : ∀ x, (1 + t * centred ν g k x) * f x = f x + t * (f x * centred ν g k x) :=
    fun x ↦ by ring
  simp_rw [e3]
  rw [integral_add (integrable_of_bdd_prob _ hf)
    ((integrable_of_bdd_prob _ (hf.mul (bdd_centred ν hk))).const_mul t), integral_const_mul,
    integral_mul_centred ν hg hk hf]

end LocalMixture

section LocalMean

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k)
include hS hg hk

omit [Nonempty X] [Fintype J] [Nonempty J] in
/-- **The mean of the local mixture is affine with slope the forcing**:
`E_{ρ_{g^m(t)}} S = M(g) + t Cov_{ρ_g}(S, k)`. -/
theorem mean_localMixTilt {t : ℝ}
    (hb : ∀ x, 1 / 2 ≤ 1 + t * centred ν g k x ∧ 1 + t * centred ν g k x ≤ 3 / 2) :
    (fun j ↦ ∫ x, S j x ∂ν.tilted (localMixTilt ν g k t)) =
      (fun j ↦ ∫ x, S j x ∂ν.tilted g) + t • forcing S ν g k := by
  funext j
  rw [integral_localMixTilt ν hg hk hb (hS j), Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

omit [Fintype J] [Nonempty J] in
theorem eventually_mean_localMixTilt :
    ∀ᶠ t : ℝ in 𝓝 0, (fun j ↦ ∫ x, S j x ∂ν.tilted (localMixTilt ν g k t)) =
      (fun j ↦ ∫ x, S j x ∂ν.tilted g) + t • forcing S ν g k := by
  filter_upwards [eventually_localMix_bounds ν hk (g := g)] with t hb
  exact mean_localMixTilt hS ν hg hk hb

end LocalMean

section EndpointMixture

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]
  {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h)
include hg hh

variable (g) in
/-- The normalised tilt density `e^g / Z_g`. -/
noncomputable def normDens : X → ℝ := fun x ↦ Real.exp (g x) / ∫ y, Real.exp (g y) ∂ν

omit [Nonempty X] hh in
theorem normDens_pos (x : X) : 0 < normDens ν g x :=
  div_pos (Real.exp_pos _) (integral_exp_pos (integrable_exp_of_bdd ν hg))

omit [Nonempty X] [IsProbabilityMeasure ν] hg hh in
theorem measurable_normDens (hg : Measurable g) : Measurable (normDens ν g) :=
  (Real.measurable_exp.comp hg).div_const _

omit [Nonempty X] hh in
theorem integral_normDens : ∫ x, normDens ν g x ∂ν = 1 := by
  unfold normDens
  rw [integral_div, div_self (integral_exp_pos (integrable_exp_of_bdd ν hg)).ne']

omit [Nonempty X] hh in
/-- Uniform bounds on the normalised density. -/
theorem normDens_bounds :
    ∃ c C : ℝ, 0 < c ∧ (∀ x, c ≤ normDens ν g x) ∧ ∀ x, normDens ν g x ≤ C := by
  obtain ⟨K, hK⟩ := hg.2
  have hZ := integral_exp_pos (integrable_exp_of_bdd ν hg)
  refine ⟨Real.exp (-K) / ∫ y, Real.exp (g y) ∂ν, Real.exp K / ∫ y, Real.exp (g y) ∂ν,
    by positivity, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (abs_le.1 (hK x)).1) hZ.le
  · exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (abs_le.1 (hK x)).2) hZ.le

omit [Nonempty X] hh in
theorem bdd_normDens : Bdd (normDens ν g) := by
  obtain ⟨c, C, -, hc, hC⟩ := normDens_bounds ν hg
  exact ⟨measurable_normDens ν hg.1, max |c| |C|, fun x ↦ by
    rw [abs_le]
    constructor
    · linarith [hc x, neg_abs_le c, le_max_left |c| |C|]
    · linarith [hC x, le_abs_self C, le_max_right |c| |C|]⟩

omit [Nonempty X] [IsProbabilityMeasure ν] hg hh in
/-- Expectations under a tilt are integrals against the normalised density. -/
theorem integral_tilted_eq_normDens {f : X → ℝ} :
    ∫ x, f x ∂ν.tilted g = ∫ x, normDens ν g x * f x ∂ν := by
  rw [integral_tilted]
  rfl

variable (g h) in
/-- **The endpoint mixture tilt** `log((1 − t) e^g/Z_g + t e^h/Z_h)`. -/
noncomputable def mixTilt (t : ℝ) : X → ℝ :=
  fun x ↦ Real.log ((1 - t) * normDens ν g x + t * normDens ν h x)

omit [Nonempty X] in
theorem mixDens_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : X) :
    0 < (1 - t) * normDens ν g x + t * normDens ν h x := by
  have ha := normDens_pos ν hg x
  have hb := normDens_pos ν hh x
  have hm := lt_min ha hb
  nlinarith [mul_le_mul_of_nonneg_left (min_le_left (normDens ν g x) (normDens ν h x))
    (sub_nonneg.2 ht1), mul_le_mul_of_nonneg_left (min_le_right (normDens ν g x) (normDens ν h x))
    ht0]

omit [Nonempty X] in
theorem bdd_mixTilt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Bdd (mixTilt ν g h t) := by
  obtain ⟨cg, Cg, hcg, hg1, hg2⟩ := normDens_bounds ν hg
  obtain ⟨ch, Ch, hch, hh1, hh2⟩ := normDens_bounds ν hh
  refine bdd_log_of_bounds ((measurable_const.mul (measurable_normDens ν hg.1)).add
    (measurable_const.mul (measurable_normDens ν hh.1))) (lt_min hcg hch) (fun x ↦ ?_)
    (fun x ↦ ?_) (c := min cg ch) (C := max Cg Ch)
  · nlinarith [mul_le_mul_of_nonneg_left (hg1 x) (sub_nonneg.2 ht1),
      mul_le_mul_of_nonneg_left (hh1 x) ht0, min_le_left cg ch, min_le_right cg ch]
  · nlinarith [mul_le_mul_of_nonneg_left (hg2 x) (sub_nonneg.2 ht1),
      mul_le_mul_of_nonneg_left (hh2 x) ht0, le_max_left Cg Ch, le_max_right Cg Ch]

omit [Nonempty X] in
/-- **The endpoint mixture has law `(1 − t) ρ_g + t ρ_h`**: every expectation is the mixture of
the endpoint expectations. -/
theorem integral_mixTilt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {f : X → ℝ} (hf : Bdd f) :
    ∫ x, f x ∂ν.tilted (mixTilt ν g h t) =
      (1 - t) * ∫ x, f x ∂ν.tilted g + t * ∫ x, f x ∂ν.tilted h := by
  rw [integral_tilted, integral_tilted_eq_normDens ν (g := g),
    integral_tilted_eq_normDens ν (g := h)]
  have e : ∀ x, Real.exp (mixTilt ν g h t x) = (1 - t) * normDens ν g x + t * normDens ν h x :=
    fun x ↦ Real.exp_log (mixDens_pos ν hg hh ht0 ht1 x)
  simp_rw [e]
  have hZ : ∫ x, ((1 - t) * normDens ν g x + t * normDens ν h x) ∂ν = 1 := by
    rw [integral_add ((integrable_of_bdd_prob _ (bdd_normDens ν hg)).const_mul _)
      ((integrable_of_bdd_prob _ (bdd_normDens ν hh)).const_mul _), integral_const_mul,
      integral_const_mul, integral_normDens ν hg, integral_normDens ν hh]
    ring
  rw [hZ]
  simp only [div_one, smul_eq_mul]
  have e3 : ∀ x, ((1 - t) * normDens ν g x + t * normDens ν h x) * f x =
      (1 - t) * (normDens ν g x * f x) + t * (normDens ν h x * f x) := fun x ↦ by ring
  simp_rw [e3]
  rw [integral_add ((integrable_of_bdd_prob _ ((bdd_normDens ν hg).mul hf)).const_mul _)
    ((integrable_of_bdd_prob _ ((bdd_normDens ν hh).mul hf)).const_mul _), integral_const_mul,
    integral_const_mul]

end EndpointMixture

section EndpointMean

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h)
include hS hg hh

omit [Nonempty X] [Fintype J] [Nonempty J] in
/-- **The mean of the endpoint mixture is the mean segment**: `(1 − t) M(g) + t M(h)`. -/
theorem mean_mixTilt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun j ↦ ∫ x, S j x ∂ν.tilted (mixTilt ν g h t)) =
      (1 - t) • (fun j ↦ ∫ x, S j x ∂ν.tilted g) + t • (fun j ↦ ∫ x, S j x ∂ν.tilted h) := by
  funext j
  rw [integral_mixTilt ν hg hh ht0 ht1 (hS j)]
  rfl

end EndpointMean

end Laplace.Multi
