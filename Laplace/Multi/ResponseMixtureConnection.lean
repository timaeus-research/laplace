/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseGlobalFibres
import Laplace.Multi.CovarianceFrechet

/-!
# The mixture connection: response of a density-affine journey

Along the local mixture journey `g^m(t) = g + log(1 + t k̄)` of `ResponseMixtureCoordinates` the
feature means move on the straight line `M(g) + t Cov_{ρ_g}(S,k)`, so the response is the natural
coordinate of an affine mean path: `Φ(g^m(t)) = θ(M(g) + t F)` with `F = Cov_{ρ_g}(S,k)` the
forcing (`responseOf_localMixTilt_eq`). Its velocity is the forcing transported through the inverse
chart derivative at the moving point, `v_m(t) = A_{θ_t}⁻¹ F` (`mixResponseVel`,
`hasDerivAt_responseOf_localMixTilt`), and its acceleration is the **mixture-connection
correction**

`v_m'(t) = − A_{θ_t}⁻¹ T_{θ_t}(v_m(t), v_m(t))`   (`hasDerivAt_mixResponseVel`),

the third-cumulant operator of the family (the derivative of the chart derivative) pulled back by
the inverse chart derivative. A mixture-affine data journey is thus carried to a mixture geodesic
of the family: its mean is affine, and in natural coordinates it bends by exactly the connection
term `Γ^m_θ(u,v) = A_θ⁻¹ T_θ(u,v)`. This is the mixture (m-) connection, not the Levi-Civita
connection of the Fisher metric, whose correction carries a factor `1/2`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Connection

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k)
include hS hg hk

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The forcing as an element of the direction space. -/
noncomputable def forcingV : 𝕍 := ⟨forcing S ν g k, forcing_mem_dirSpan hS ν hg hk⟩

theorem coe_forcingV : ((forcingV hS ν hg hk : 𝕍) : J → ℝ) = forcing S ν g k := rfl

/-- The affine mean path `M(g) + t F`. -/
local notation "Mpath" t => tiltedMean S ν g + t • forcing S ν g k

/-- **The response of the local mixture journey is the natural coordinate of the affine mean
path.** -/
theorem responseOf_localMixTilt_eq {t : ℝ}
    (hb : ∀ x, 1 / 2 ≤ 1 + t * centred ν g k x ∧ 1 + t * centred ν g k x ≤ 3 / 2) :
    responseOf hS ν (localMixTilt ν g k t) = θr (Mpath t) := by
  change θr (tiltedMean S ν (localMixTilt ν g k t)) = _
  rw [show tiltedMean S ν (localMixTilt ν g k t) = Mpath t from mean_localMixTilt hS ν hg hk hb]

set_option linter.unusedFintypeInType false in
omit [Nonempty J] in
/-- The affine mean path stays in the response domain where the local mixture is defined. -/
theorem mpath_mem {t : ℝ}
    (hb : ∀ x, 1 / 2 ≤ 1 + t * centred ν g k x ∧ 1 + t * centred ν g k x ≤ 3 / 2) :
    (Mpath t) ∈ Ω := by
  rw [show (Mpath t) = tiltedMean S ν (localMixTilt ν g k t) from
    (mean_localMixTilt hS ν hg hk hb).symm]
  exact mean_tilted_mem_intrinsicInterior hS ν (bdd_localMixTilt ν hg hk hb)

/-- **The mixture response velocity** `v_m(t) = A_{θ(M + tF)}⁻¹ F`. -/
noncomputable def mixResponseVel (t : ℝ) : 𝕍 := (CDE (θr (Mpath t))).symm (forcingV hS ν hg hk)

theorem mixResponseVel_zero : mixResponseVel hS ν hg hk 0 = responseVel hS ν hg hk := by
  unfold mixResponseVel responseVel
  rw [zero_smul, add_zero]
  rfl

/-- The displacement `(t − t₀) F` in the direction space. -/
theorem hasDerivAt_displacement (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (t - t₀) • (forcingV hS ν hg hk)) (forcingV hS ν hg hk) t₀ := by
  simpa using ((hasDerivAt_id t₀).sub_const t₀).smul_const (forcingV hS ν hg hk)

theorem mpath_eq (t t₀ : ℝ) :
    (Mpath t₀) + (((t - t₀) • (forcingV hS ν hg hk) : 𝕍) : J → ℝ) = Mpath t := by
  rw [Submodule.coe_smul, coe_forcingV, add_assoc, ← add_smul, add_sub_cancel]

/-- **The velocity of the natural coordinate along the affine mean path** is the transported
forcing. -/
theorem hasDerivAt_responseTheta_mpath {t₀ : ℝ} (hrel : (Mpath t₀) ∈ Ω) :
    HasDerivAt (fun t ↦ θr (Mpath t)) (mixResponseVel hS ν hg hk t₀) t₀ := by
  have hF := (hasStrictFDerivAt_responseTheta_add hS ν hrel).hasFDerivAt
  have hz := hasDerivAt_displacement hS ν hg hk t₀
  have h := hF.comp_hasDerivAt_of_eq t₀ hz (by simp)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv rfl
  change θr (Mpath t) = θr ((Mpath t₀) + (((t - t₀) • (forcingV hS ν hg hk) : 𝕍) : J → ℝ))
  rw [mpath_eq]

/-- **The local mixture journey's response is differentiable near `0` with velocity `v_m`.** -/
theorem eventually_hasDerivAt_responseOf_localMixTilt :
    ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun s ↦ responseOf hS ν (localMixTilt ν g k s))
      (mixResponseVel hS ν hg hk t) t := by
  have h1 := eventually_localMix_bounds ν hk (g := g)
  have h2 := eventually_eventually_nhds.2 h1
  filter_upwards [h1, h2] with t hb hnb
  refine (hasDerivAt_responseTheta_mpath hS ν hg hk (mpath_mem hS ν hg hk hb)).congr_of_eventuallyEq
    (hnb.mono fun s hs ↦ ?_)
  exact responseOf_localMixTilt_eq hS ν hg hk hs

/-- **The mixture-connection correction**: the mixture response velocity has derivative
`− A_{θ_t}⁻¹ T_{θ_t}(v_m(t), v_m(t))`. -/
theorem hasDerivAt_mixResponseVel {t₀ : ℝ} (hrel : (Mpath t₀) ∈ Ω) :
    HasDerivAt (mixResponseVel hS ν hg hk)
      (-(CDE (θr (Mpath t₀))).symm (thirdOp hS ν (θr (Mpath t₀)) (mixResponseVel hS ν hg hk t₀)
        (mixResponseVel hS ν hg hk t₀))) t₀ := by
  have hinv := hasFDerivAt_inverse_response_apply hS ν hrel (forcingV hS ν hg hk)
  have hz := hasDerivAt_displacement hS ν hg hk t₀
  have h := hinv.comp_hasDerivAt_of_eq t₀ hz (by simp)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · change mixResponseVel hS ν hg hk t =
      (CDE (θr ((Mpath t₀) + (((t - t₀) • (forcingV hS ν hg hk) : 𝕍) : J → ℝ)))).symm
        (forcingV hS ν hg hk)
    rw [mpath_eq]
    rfl
  · rw [inverse_response_deriv_apply]
    rfl

/-- The mixture-connection correction at the base point, in terms of the response velocity. -/
theorem hasDerivAt_mixResponseVel_zero :
    HasDerivAt (mixResponseVel hS ν hg hk)
      (-(CDE (responseOf hS ν g)).symm (thirdOp hS ν (responseOf hS ν g)
        (responseVel hS ν hg hk) (responseVel hS ν hg hk))) 0 := by
  have hrel : (Mpath (0 : ℝ)) ∈ Ω := by
    rw [zero_smul, add_zero]
    exact mean_tilted_mem_intrinsicInterior hS ν hg
  have h := hasDerivAt_mixResponseVel hS ν hg hk (t₀ := 0) hrel
  rw [mixResponseVel_zero] at h
  refine h.congr_deriv ?_
  have e : θr (Mpath (0 : ℝ)) = responseOf hS ν g := by
    rw [zero_smul, add_zero]
    rfl
  rw [e]

end Connection

end Laplace.Multi
