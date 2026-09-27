/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseJourneyResolution
import Laplace.Multi.ResponseSubmersionCalculus
import Laplace.Multi.ResponseDefect
import Laplace.Multi.ThermalTransport

/-!
# The canonical journey from the featureless law to the data law

For a data law `D = q ν` whose density is bounded away from `0` and `∞`, the exponential segment
`ρ_t = ν.tilted (t · log q) = q^t ν / Z(t)` runs from the featureless law `ρ_0 = ν` to the data law
`ρ_1 = D` (`journeyLaw_zero`, `journeyLaw_one`). It is a coefficient journey with `h = log q`, so
the whole journey calculus applies; this file records what is specific to it.

* **Endpoints of the response path** (`journeyResponse_zero`, `journeyResponse_one`):
  `Φ(ρ_0) = 0` and `Φ(ρ_1) = θ(E_D S)`; the response path is the seabed's data path
  (`responseOf_eq_dataTheta`) and a coefficient journey (`coeffResponse_unit`).
* **Velocity and length** (`hasDerivAt_journeyResponse`, `fisherDist_journey_le`): the response
  path is `C¹` with velocity `DΦ_{t log q}[log q]`, and
  `d_F(0, θ(E_D S)) ≤ L_e(q) = ∫_0^1 √G^{resp}_{t log q}(log q) dt`.
* **The initial response is determined by regression of `log q` on the statistics**
  (`lawCov_logDens_eq_fisherVar_add_residual`): `Var_ν(log q) = |DΦ_0[log q]|²_{F,0} +
  Var_ν(log q − hor_0(DΦ_0[log q]))`.
* **The information rises monotonically along the journey** (`hasDerivAt_klDiv_journey`,
  `monotoneOn_klDiv_journey`, `klDiv_journey_le`): `d/dt D(ρ_t‖ν) = t Var_{ρ_t}(log q) ≥ 0`, so
  `D(ρ_t‖ν)` increases from `0` to `D(D‖ν)` on `[0, 1]`.

The segment is the exponential-connection geodesic from `ν` to `D`; it is neither a Fisher–Rao
geodesic of the data manifold nor a shortest response path, and `ν` maximises entropy relative to
`ν` only.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Density

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

variable (q : X → ℝ) in
/-- The log-density `log q`. -/
noncomputable def logDens : X → ℝ := fun x ↦ Real.log (q x)

variable {q : X → ℝ} (hqm : Measurable q) {c C : ℝ} (hc : 0 < c) (hq : ∀ x, c ≤ q x ∧ q x ≤ C)
include hqm hc hq

omit [IsProbabilityMeasure ν] in
/-- A density bounded away from `0` and `∞` has a bounded log-density. -/
theorem bdd_logDens : Bdd (logDens q) := by
  refine ⟨hqm.log, max |Real.log c| |Real.log C|, fun x ↦ ?_⟩
  have h1 : Real.log c ≤ Real.log (q x) := Real.log_le_log hc (hq x).1
  have h2 : Real.log (q x) ≤ Real.log C := Real.log_le_log (hc.trans_le (hq x).1) (hq x).2
  change |Real.log (q x)| ≤ _
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log c), le_max_left |Real.log c| |Real.log C|]
  · linarith [le_abs_self (Real.log C), le_max_right |Real.log c| |Real.log C|]

omit [IsProbabilityMeasure ν] hqm in
/-- **The journey ends at the data law**: `ν.tilted (1 · log q) = q ν`. -/
theorem journeyLaw_one (hq1 : ∫ x, q x ∂ν = 1) :
    ν.tilted (fun x ↦ 1 * logDens q x) = ν.withDensity fun x ↦ ENNReal.ofReal (q x) := by
  have he : ∀ y, Real.exp (1 * logDens q y) = q y := fun y ↦ by
    rw [one_mul, logDens, Real.exp_log (hc.trans_le (hq y).1)]
  rw [Measure.tilted]
  simp only [he, hq1, div_one]

omit hqm hc hq in
/-- **The journey starts at the featureless law**: `ν.tilted (0 · log q) = ν`. -/
theorem journeyLaw_zero : ν.tilted (fun x ↦ 0 * logDens q x) = ν := tilted_zero_mul ν _

end Density

section Journey

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {q : X → ℝ} (hh : Bdd (logDens q))
include hS hh

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit hh in
theorem responseVel_congr {g g' k k' : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hg' : Bdd g')
    (hk' : Bdd k') (eg : g = g') (ek : k = k') :
    responseVel hS ν hg hk = responseVel hS ν hg' hk' := by
  subst eg
  subst ek
  rfl

omit hh in
theorem pullbackForm_congr {g g' k k' : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hg' : Bdd g')
    (hk' : Bdd k') (eg : g = g') (ek : k = k') :
    pullbackForm hS ν hg hk = pullbackForm hS ν hg' hk' := by
  subst eg
  subst ek
  rfl

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hh in
theorem dirLoss_unit_logDens (t : ℝ) :
    dirLoss (fun _ : Unit ↦ logDens q) (fun _ ↦ t) = fun x ↦ t * logDens q x := by
  funext x
  simp only [dirLoss, Finset.univ_unique, Finset.sum_singleton]

/-- **The journey's response path is the seabed's data path.** -/
theorem responseOf_eq_dataTheta (t : ℝ) :
    responseOf hS ν (fun x ↦ t * logDens q x) = dataTheta hS ν hh t := by
  unfold responseOf responseTheta dataTheta
  congr 1
  apply Subtype.ext
  rw [toV]
  split_ifs with h
  · rfl
  · exact absurd (pathV hS ν hh t).2 h

omit hh in
/-- **The journey's response path is a coefficient journey** (one coefficient, `h = log q`). -/
theorem coeffResponse_unit (t : ℝ) :
    coeffResponse hS ν (fun _ : Unit ↦ logDens q) (fun t _ ↦ t) t =
      responseOf hS ν (fun x ↦ t * logDens q x) := by
  rw [coeffResponse, dirLoss_unit_logDens]

/-- **The journey starts at the featureless response** `Φ(ρ_0) = 0`. -/
theorem journeyResponse_zero : responseOf hS ν (fun x ↦ 0 * logDens q x) = 0 := by
  rw [responseOf_eq_dataTheta hS ν hh, dataTheta_zero]

omit hh in
/-- **The journey ends at the response of the data law** `Φ(ρ_1) = θ(E_D S)`. -/
theorem journeyResponse_one {c C : ℝ} (hc : 0 < c)
    (hq : ∀ x, c ≤ q x ∧ q x ≤ C) (hq1 : ∫ x, q x ∂ν = 1) :
    responseOf hS ν (fun x ↦ 1 * logDens q x) =
      θr (fun i ↦ ∫ x, S i x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q x))) := by
  rw [responseOf, journeyLaw_one ν hc hq hq1]

/-- **The response path is `C¹`** with velocity `DΦ_{t log q}[log q]`. -/
theorem hasDerivAt_journeyResponse (t₀ : ℝ) :
    HasDerivAt (fun t ↦ responseOf hS ν (fun x ↦ t * logDens q x))
      (responseVel hS ν (hh.const_mul t₀) hh) t₀ := by
  have ha : ∀ t : ℝ, HasDerivAt (fun t ↦ fun _ : Unit ↦ t) (fun _ : Unit ↦ (1 : ℝ)) t :=
    fun t ↦ hasDerivAt_pi.2 fun _ ↦ hasDerivAt_id t
  have hd := hasDerivAt_coeffResponse hS ν (fun _ : Unit ↦ hh) ha continuous_const t₀
  refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun t ↦
    (coeffResponse_unit hS ν t).symm)).congr_deriv ?_
  exact responseVel_congr hS ν _ _ _ _ (dirLoss_unit_logDens t₀)
    (by rw [dirLoss_unit_logDens]; exact funext fun x ↦ one_mul _)

/-- **The length bound for the canonical journey**:
`d_F(Φ(ρ_0), Φ(ρ_1)) ≤ ∫_0^1 √G^{resp}_{t log q}(log q) dt`. -/
theorem fisherDist_journey_le :
    fisherDist S ν (responseOf hS ν (fun x ↦ 0 * logDens q x))
        (responseOf hS ν (fun x ↦ 1 * logDens q x)) ≤
      ∫ s in (0 : ℝ)..1, √(pullbackForm hS ν (hh.const_mul s) hh) := by
  have ha : ∀ t : ℝ, HasDerivAt (fun t ↦ fun _ : Unit ↦ t) (fun _ : Unit ↦ (1 : ℝ)) t :=
    fun t ↦ hasDerivAt_pi.2 fun _ ↦ hasDerivAt_id t
  have h := fisherDist_coeffResponse_le hS ν (fun _ : Unit ↦ hh) ha continuous_const
    (zero_le_one : (0 : ℝ) ≤ 1)
  have e : ∀ s : ℝ, pullbackForm hS ν (bdd_dirLoss (fun _ : Unit ↦ hh) ((fun t _ ↦ t) s))
      (bdd_dirLoss (fun _ : Unit ↦ hh) ((fun _ _ ↦ (1 : ℝ)) s)) =
      pullbackForm hS ν (hh.const_mul s) hh := fun s ↦
    pullbackForm_congr hS ν _ _ _ _ (dirLoss_unit_logDens s)
      (by rw [dirLoss_unit_logDens]; exact funext fun x ↦ one_mul _)
  rw [coeffResponse_unit, coeffResponse_unit] at h
  simp only [e] at h
  exact h

/-- **The featureless response distance to the data response is bounded by the journey length.**
-/
theorem fisherDist_zero_dataResponse_le {c C : ℝ} (hc : 0 < c)
    (hq : ∀ x, c ≤ q x ∧ q x ≤ C) (hq1 : ∫ x, q x ∂ν = 1) :
    fisherDist S ν 0 (θr (fun i ↦ ∫ x, S i x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (q x)))) ≤
      ∫ s in (0 : ℝ)..1, √(pullbackForm hS ν (hh.const_mul s) hh) := by
  rw [← journeyResponse_zero hS ν hh, ← journeyResponse_one hS ν hc hq hq1]
  exact fisherDist_journey_le hS ν hh

/-- The featureless law is matched: `ρ_0 = P_{Φ(ρ_0)}`. -/
theorem journeyLaw_zero_matched :
    ν.tilted (fun x ↦ 0 * logDens q x) =
      Pfam (responseOf hS ν (fun x ↦ 0 * logDens q x) : J → ℝ) := by
  rw [journeyResponse_zero hS ν hh, journeyLaw_zero, familyMeasure_one_zero_eq_tilted hS ν]
  have e : (fun x ↦ -1 * dirLoss S ((0 : 𝕍) : J → ℝ) x) = fun x ↦ 0 * logDens q x := by
    funext x
    simp [dirLoss]
  rw [e, journeyLaw_zero]

/-- **The initial response is determined by regression of `log q` on the statistics**:
`Var_ν(log q) = |DΦ_0[log q]|²_{F,0} + Var_ν(log q − hor_0(DΦ_0[log q]))`. -/
theorem lawCov_logDens_eq_fisherVar_add_residual :
    lawCov ν (logDens q) (logDens q) =
      fisherVar S ν ((0 : 𝕍) : J → ℝ) (responseVel hS ν (hh.const_mul 0) hh : J → ℝ) +
      lawCov ν
        (fun x ↦ logDens q x -
          horizontalLift hS ν (hh.const_mul 0) (responseVel hS ν (hh.const_mul 0) hh) x)
        (fun x ↦ logDens q x -
          horizontalLift hS ν (hh.const_mul 0) (responseVel hS ν (hh.const_mul 0) hh) x) := by
  have h1 := lawCov_self_eq_horizontal_add_residual hS ν (hh.const_mul 0) hh
  have h2 := lawCov_horizontalLift_self_of_matched hS ν (hh.const_mul 0)
    (journeyLaw_zero_matched hS ν hh) (responseVel hS ν (hh.const_mul 0) hh)
  rw [journeyLaw_zero] at h1 h2
  rw [h1, h2, journeyResponse_zero hS ν hh]

omit [Fintype J] [Nonempty J] hS in
/-- **The information rises along the journey**: `d/dt D(ρ_t‖ν) = t Var_{ρ_t}(log q)`. -/
theorem hasDerivAt_klDiv_journey (t₀ : ℝ) :
    HasDerivAt (fun t ↦ (klDiv (ν.tilted fun x ↦ t * logDens q x) ν).toReal)
      (t₀ * lawCov (ν.tilted fun x ↦ t₀ * logDens q x) (logDens q) (logDens q)) t₀ :=
  (hasDerivAt_klDiv_tilted_toReal ν hh t₀).congr_deriv (by rw [lawCov])

omit [Fintype J] [Nonempty J] hS in
/-- **The information is monotone from the featureless law onwards.** -/
theorem monotoneOn_klDiv_journey :
    MonotoneOn (fun t ↦ (klDiv (ν.tilted fun x ↦ t * logDens q x) ν).toReal) (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun t _ ↦ (hasDerivAt_klDiv_journey ν hh t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hasDerivAt_klDiv_journey ν hh t).differentiableAt.differentiableWithinAt)
    fun t ht ↦ ?_
  rw [interior_Ici] at ht
  rw [(hasDerivAt_klDiv_journey ν hh t).deriv]
  have := isProbabilityMeasure_dataPath ν hh t
  exact mul_nonneg (le_of_lt ht) (lawCov_self_nonneg _ hh)

omit [Fintype J] [Nonempty J] hS in
/-- **The journey's information never exceeds that of the data law**: for `t ∈ [0, 1]`,
`D(ρ_t‖ν) ≤ D(D‖ν)`. -/
theorem klDiv_journey_le {c C : ℝ} (hc : 0 < c)
    (hq : ∀ x, c ≤ q x ∧ q x ≤ C) (hq1 : ∫ x, q x ∂ν = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (klDiv (ν.tilted fun x ↦ t * logDens q x) ν).toReal ≤
      (klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (q x)) ν).toReal := by
  rw [← journeyLaw_one ν hc hq hq1]
  exact monotoneOn_klDiv_journey ν hh ht0 (zero_le_one : (0 : ℝ) ≤ 1) ht1

end Journey

end Laplace.Multi
