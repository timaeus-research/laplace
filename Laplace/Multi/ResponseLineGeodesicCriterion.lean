/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSamplingGeometry
import Laplace.Multi.ResponseFisherEnergyStationarity
import Laplace.Multi.ResponseFeaturelessJourney

/-!
# When is a mean-straight journey a Fisher geodesic?

Mean-affine journeys (response lines, the featureless journey, the model journey) are
m-geodesics: `θ'' = −C(θ',θ')`. Their Levi-Civita acceleration `θ'' + ½ C(θ',θ')` is therefore
`−½ C(θ',θ')`, and the given parametrisation is a Levi-Civita geodesic of the Fisher metric —
equivalently, by `ResponseFisherEnergyStationarity`, an energy-stationary journey — **iff the
m-Christoffel symbol vanishes on its velocity**, `C_θ(θ',θ') = 0`
(`responseLine_lcAccel`, `responseLine_lcGeodesic_iff`, `featurelessJourney_lcAccel`,
`featurelessJourney_lcGeodesic_iff`). In particular in an e/m-flat direction (vanishing third
cumulant along the velocity) the two geometries agree; in general the canonical information
journey is not a shortest journey.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Criterion

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The Levi-Civita acceleration of a response line is `−½ C(V,V)`. -/
theorem responseLine_lcAccel (θ₀ e : 𝕍) {t : ℝ} (ht : t ∈ responseLineDomain S ν θ₀ e) :
    deriv (responseLineVel hS ν θ₀ e) t + (1 / 2 : ℝ) • mChristoffel hS ν (responseLine hS ν θ₀ e t)
      (responseLineVel hS ν θ₀ e t) (responseLineVel hS ν θ₀ e t) =
      -((1 / 2 : ℝ) • mChristoffel hS ν (responseLine hS ν θ₀ e t) (responseLineVel hS ν θ₀ e t)
        (responseLineVel hS ν θ₀ e t)) := by
  rw [(hasDerivAt_responseLineVel hS ν θ₀ e ht).deriv]
  module

/-- **A response line is Levi-Civita geodesic at `t` iff the m-Christoffel symbol vanishes on its
velocity.** -/
theorem responseLine_lcGeodesic_iff (θ₀ e : 𝕍) {t : ℝ} (ht : t ∈ responseLineDomain S ν θ₀ e) :
    deriv (responseLineVel hS ν θ₀ e) t + (1 / 2 : ℝ) • mChristoffel hS ν (responseLine hS ν θ₀ e t)
        (responseLineVel hS ν θ₀ e t) (responseLineVel hS ν θ₀ e t) = 0 ↔
      mChristoffel hS ν (responseLine hS ν θ₀ e t) (responseLineVel hS ν θ₀ e t)
        (responseLineVel hS ν θ₀ e t) = 0 := by
  rw [responseLine_lcAccel hS ν θ₀ e ht, neg_eq_zero, smul_eq_zero]
  simp

/-- The Levi-Civita acceleration of the featureless journey is `−½ C(θ',θ')`. -/
theorem featurelessJourney_lcAccel {g : X → ℝ} (hg : Bdd g) {t : ℝ}
    (ht : t ∈ journeyDomain S ν g) :
    deriv (journeyVel hS ν hg) t + (1 / 2 : ℝ) • mChristoffel hS ν (featurelessJourney hS ν g t)
      (journeyVel hS ν hg t) (journeyVel hS ν hg t) =
      -((1 / 2 : ℝ) • mChristoffel hS ν (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
        (journeyVel hS ν hg t)) := by
  rw [(hasDerivAt_journeyVel hS ν hg ht).deriv]
  module

/-- **The featureless journey is Levi-Civita geodesic at `t` iff `C(θ',θ') = 0`.** -/
theorem featurelessJourney_lcGeodesic_iff {g : X → ℝ} (hg : Bdd g) {t : ℝ}
    (ht : t ∈ journeyDomain S ν g) :
    deriv (journeyVel hS ν hg) t + (1 / 2 : ℝ) • mChristoffel hS ν (featurelessJourney hS ν g t)
        (journeyVel hS ν hg t) (journeyVel hS ν hg t) = 0 ↔
      mChristoffel hS ν (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
        (journeyVel hS ν hg t) = 0 := by
  rw [featurelessJourney_lcAccel hS ν hg ht, neg_eq_zero, smul_eq_zero]
  simp

/-- The m-Christoffel symbol vanishes on `v` iff the third operator does (the chart derivative is
invertible). -/
theorem mChristoffel_self_eq_zero_iff (θ v : 𝕍) :
    mChristoffel hS ν θ v v = 0 ↔ thirdOp hS ν θ v v = 0 := by
  unfold mChristoffel
  constructor
  · intro h
    have := congrArg (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ) h
    rwa [ContinuousLinearEquiv.apply_symm_apply, map_zero] at this
  · intro h
    rw [h, map_zero]

end Criterion

end Laplace.Multi
