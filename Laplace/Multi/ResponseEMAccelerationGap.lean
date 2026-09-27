/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseMixtureConnection

/-!
# The data third cumulant is the exponential/mixture acceleration gap

At a base law `ρ_g` and a bounded direction `k`, the exponential journey `g + t k` and the local
mixture journey `g + log(1 + t k̄)` have the same first-order density perturbation and hence the
same response velocity `DΦ_g[k]` (`mixResponseVel_zero`). Their response accelerations differ:
the exponential journey accelerates by the response Hessian `H_g(k,k)`
(`hasDerivAt_expResponseVel_zero`), the mixture journey by the mixture-connection term
`a_m = −A⁻¹ T_{Φ(g)}(v, v)` (`hasDerivAt_mixResponseVel_zero'`), and

  `H_g(k,k) − a_m = A_g⁻¹ B_g(k,k)`   (`responseHess_sub_mixResponseAccel`):

**the transported data third cumulant is exactly the gap between the two accelerations.** In
mixture-covariant terms, the mixture-covariant acceleration of the response to an exponential
data journey is `A⁻¹ B_g(k,k)` (`responseHess_add_mConnection`, bilinear form), and the two
accelerations agree exactly when the data third cumulant `B_g(k,k)` vanishes
(`responseHess_eq_mixResponseAccel_iff`). This is the geometric content of the Hessian formula: the
model cumulant `T` is the mixture connection of the family, the data cumulant `B` is the genuine
e/m discrepancy of the data journey.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Gap

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k)
include hS hg hk

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The mixture acceleration** `a_m = −A_g⁻¹ T_{Φ(g)}(DΦ_g[k], DΦ_g[k])`. -/
noncomputable def mixResponseAccel : 𝕍 :=
  -(CDE (responseOf hS ν g)).symm
    (thirdOp hS ν (responseOf hS ν g) (responseVel hS ν hg hk) (responseVel hS ν hg hk))

/-- The mixture journey accelerates by `a_m`. -/
theorem hasDerivAt_mixResponseVel_zero' :
    HasDerivAt (mixResponseVel hS ν hg hk) (mixResponseAccel hS ν hg hk) 0 :=
  hasDerivAt_mixResponseVel_zero hS ν hg hk

/-- The exponential journey accelerates by the response Hessian. -/
theorem hasDerivAt_expResponseVel_zero :
    HasDerivAt (fun t ↦ responseVel hS ν (hg.add (Bdd.const_mul t hk)) hk)
      (responseHess hS ν hg hk hk) 0 := by
  have h := hasDerivAt_responseVel_add hS ν hg hk hk 0
  rwa [responseHess_congr hS ν _ hg hk hk (by funext x; simp)] at h

/-- **THE E/M ACCELERATION GAP**: `H_g(k,k) − a_m = A_g⁻¹ B_g(k,k)`. -/
theorem responseHess_sub_mixResponseAccel :
    responseHess hS ν hg hk hk - mixResponseAccel hS ν hg hk =
      (CDE (responseOf hS ν g)).symm (dataThird hS ν hg hk hk) := by
  unfold responseHess mixResponseAccel
  rw [map_sub, sub_neg_eq_add, sub_add_cancel]

/-- **The mixture-covariant acceleration of the exponential journey** is the transported data
cumulant, bilinearly: `H_g(k,ℓ) + A⁻¹ T(DΦ[k], DΦ[ℓ]) = A⁻¹ B_g(k,ℓ)`. -/
theorem responseHess_add_mConnection {ℓ : X → ℝ} (hℓ : Bdd ℓ) :
    responseHess hS ν hg hk hℓ + (CDE (responseOf hS ν g)).symm
      (thirdOp hS ν (responseOf hS ν g) (responseVel hS ν hg hk) (responseVel hS ν hg hℓ)) =
      (CDE (responseOf hS ν g)).symm (dataThird hS ν hg hk hℓ) := by
  unfold responseHess
  rw [map_sub, sub_add_cancel]

/-- **The two accelerations agree exactly when the data third cumulant vanishes.** -/
theorem responseHess_eq_mixResponseAccel_iff :
    responseHess hS ν hg hk hk = mixResponseAccel hS ν hg hk ↔ dataThird hS ν hg hk hk = 0 := by
  rw [← sub_eq_zero, responseHess_sub_mixResponseAccel]
  exact (CDE (responseOf hS ν g)).symm.map_eq_zero_iff

/-- The two matched journeys share their initial response velocity. -/
theorem mixResponseVel_zero_eq_responseVel :
    mixResponseVel hS ν hg hk 0 = responseVel hS ν hg hk :=
  mixResponseVel_zero hS ν hg hk

/-- An invisible direction has vanishing forcing. -/
theorem forcing_eq_zero_of_responseVel_eq_zero (h0 : responseVel hS ν hg hk = 0) :
    forcing S ν g k = 0 := by
  unfold responseVel at h0
  rw [(CDE (responseOf hS ν g)).symm.map_eq_zero_iff] at h0
  exact congrArg Subtype.val h0

/-- **Invisible directions integrate to straight lines inside a fibre in density coordinates**: if
`DΦ_g[k] = 0`, the local mixture journey `g + log(1 + t k̄)` stays in the fibre of `Φ(g)`
exactly, for all small `t`. -/
theorem eventually_responseOf_localMixTilt_of_invisible (h0 : responseVel hS ν hg hk = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, responseOf hS ν (localMixTilt ν g k t) = responseOf hS ν g := by
  filter_upwards [eventually_localMix_bounds ν hk (g := g)] with t hb
  rw [responseOf_localMixTilt_eq hS ν hg hk hb,
    forcing_eq_zero_of_responseVel_eq_zero hS ν hg hk h0, smul_zero, add_zero]
  rfl

end Gap

end Laplace.Multi
