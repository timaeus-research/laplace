/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseNoiseCalibration
import Laplace.Multi.ResponsePullbackVariation
import Laplace.Multi.ResponseEMAccelerationGap

/-!
# Fisher jets: the metric derivative and the mixture Christoffel operator

The Fisher form `G_θ(v,w) = Cov_{P_θ}(⟨v,S⟩,⟨w,S⟩) = −⟨v, A_θ w⟩` (`fisherInner`) is an inner
product on the direction space `𝕍`. Along a line `θ + t u` in the natural coordinates its derivative
is a third cumulant of the family, `−⟨v, T_θ(u,w)⟩` (`hasDerivAt_fisherInner_line`), and this
pairing is totally symmetric in `(u,v,w)` (`dotJ_thirdOp_symm₁₂`, `dotJ_thirdOp_symm₂₃`): the
Fisher metric is a Hessian metric in the natural chart.

The **mixture Christoffel operator** `C_θ(u,v) = A_θ⁻¹ T_θ(u,v)` (`mChristoffel`) is the unique
vector with `G_θ(C_θ(u,v), w) = ∂_u G_θ(v,w)` for all `w` (`fisherInner_mChristoffel`,
`hasDerivAt_fisherInner_line_mChristoffel`, `mChristoffel_unique`). It is symmetric in `(u,v)` and
Fisher-symmetric in all three slots. Two structural consequences for the response map:

* the response Hessian is the mixture-covariant Hessian of the response,
  `H_g(k,ℓ) = A⁻¹ B_g(k,ℓ) − C_θ(DΦ_g k, DΦ_g ℓ)` (`responseHess_eq_sub_mChristoffel`);
* the mixture journey through a data law is an **m-geodesic** of the response chart:
  its acceleration is `−C_θ(V,V)` (`mixResponseAccel_eq_neg_mChristoffel`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Jets

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **Positivity of the Fisher form.** -/
theorem fisherInner_self_pos (θ : 𝕍) {v : 𝕍} (hv : v ≠ 0) : 0 < fisherInner S ν θ v v := by
  rw [fisherInner_self]
  exact fisherVar_pos_of_ne_zero hS ν θ hv

/-- The pairing `⟨u, T_θ(v,w)⟩` is symmetric in the first two slots. -/
theorem dotJ_thirdOp_symm₁₂ (θ u v w : 𝕍) :
    dotJ (u : J → ℝ) (thirdOp hS ν θ v w : J → ℝ) =
      dotJ (v : J → ℝ) (thirdOp hS ν θ u w : J → ℝ) := by
  rw [dotJ_thirdOp hS ν, dotJ_thirdOp hS ν, thirdCentral_comm₁₂, thirdCentral_comm₂₃,
    thirdCentral_comm₁₂]

/-- The pairing `⟨u, T_θ(v,w)⟩` is symmetric in the last two slots. -/
theorem dotJ_thirdOp_symm₂₃ (θ u v w : 𝕍) :
    dotJ (u : J → ℝ) (thirdOp hS ν θ v w : J → ℝ) =
      dotJ (u : J → ℝ) (thirdOp hS ν θ w v : J → ℝ) := by
  rw [thirdOp_symm hS ν]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- The line `t ↦ θ + t u` in the natural coordinates. -/
theorem hasDerivAt_natLine (θ u : 𝕍) (t₀ : ℝ) : HasDerivAt (fun t : ℝ ↦ θ + t • u) u t₀ := by
  have h := ((hasDerivAt_id t₀).smul_const u).const_add θ
  simpa using h

/-- The restricted covariance operator along a line, applied to a fixed direction. -/
theorem hasDerivAt_chartDeriv_line (θ u w : 𝕍) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (CD (θ + t • u) w : J → ℝ))
      (thirdOp hS ν (θ + t₀ • u) u w : J → ℝ) t₀ := by
  have h1 := (hasFDerivAt_chartDeriv_coe hS ν (θ + t₀ • u) w).comp_hasDerivAt t₀
    (hasDerivAt_natLine ν θ u t₀)
  rw [thirdCoordCLM_apply hS ν, ← thirdOp_coe_apply hS ν] at h1
  exact h1

/-- **The derivative of the Fisher form along a line is a third cumulant**:
`d/dt G_{θ+tu}(v,w) = −⟨v, T_{θ+tu}(u,w)⟩`. -/
theorem hasDerivAt_fisherInner_line (θ u v w : 𝕍) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ fisherInner S ν (θ + t • u) v w)
      (-dotJ (v : J → ℝ) (thirdOp hS ν (θ + t₀ • u) u w : J → ℝ)) t₀ := by
  have e : (fun t : ℝ ↦ fisherInner S ν (θ + t • u) v w) =
      fun t ↦ -dotJ (v : J → ℝ) (CD (θ + t • u) w : J → ℝ) :=
    funext fun t ↦ fisherInner_eq_neg_dotJ hS ν _ v w
  rw [e]
  have h := (hasDerivAt_dotJ (hasDerivAt_const t₀ (v : J → ℝ))
    (hasDerivAt_chartDeriv_line hS ν θ u w t₀)).neg
  refine h.congr_deriv ?_
  rw [dotJ_zero_left, zero_add]

/-- The metric derivative at the base point as a third cumulant of the family:
`d/dt G_{θ+tu}(v,w)|₀ = −κ_{P_θ}(⟨v,S⟩, ⟨w,S⟩, ⟨u,S⟩)`. -/
theorem hasDerivAt_fisherInner_line_zero (θ u v w : 𝕍) :
    HasDerivAt (fun t : ℝ ↦ fisherInner S ν (θ + t • u) v w)
      (-thirdCentral (Pfam (θ : J → ℝ)) (dirLoss S (v : J → ℝ)) (dirLoss S (w : J → ℝ))
        (dirLoss S (u : J → ℝ))) 0 := by
  have h := hasDerivAt_fisherInner_line hS ν θ u v w 0
  rw [zero_smul, add_zero, dotJ_thirdOp hS ν] at h
  exact h

/-- **The metric derivative is totally symmetric** (the Fisher metric is a Hessian metric in the
natural chart): `∂_u G(v,w) = ∂_v G(u,w)`. -/
theorem hasDerivAt_fisherInner_line_swap (θ u v w : 𝕍) :
    HasDerivAt (fun t : ℝ ↦ fisherInner S ν (θ + t • u) v w)
      (-dotJ (u : J → ℝ) (thirdOp hS ν θ v w : J → ℝ)) 0 := by
  have h := hasDerivAt_fisherInner_line hS ν θ u v w 0
  rw [zero_smul, add_zero, dotJ_thirdOp_symm₁₂ hS ν] at h
  exact h

/-- **The mixture Christoffel operator** `C_θ(u,v) = A_θ⁻¹ T_θ(u,v)`. -/
noncomputable def mChristoffel (θ u v : 𝕍) : 𝕍 := (CDE θ).symm (thirdOp hS ν θ u v)

theorem mChristoffel_symm (θ u v : 𝕍) : mChristoffel hS ν θ u v = mChristoffel hS ν θ v u := by
  unfold mChristoffel
  rw [thirdOp_symm hS ν]

/-- **The mixture Christoffel operator lowers to the third cumulant**:
`G_θ(C_θ(u,v), w) = −⟨w, T_θ(u,v)⟩`. -/
theorem fisherInner_mChristoffel (θ u v w : 𝕍) :
    fisherInner S ν θ (mChristoffel hS ν θ u v) w =
      -dotJ (w : J → ℝ) (thirdOp hS ν θ u v : J → ℝ) := by
  rw [fisherInner_comm hS ν, mChristoffel]
  exact fisherInner_chartDerivEquiv_symm hS ν θ w (thirdOp hS ν θ u v).2

/-- The lowered Christoffel operator as a third cumulant of the family. -/
theorem fisherInner_mChristoffel_eq_thirdCentral (θ u v w : 𝕍) :
    fisherInner S ν θ (mChristoffel hS ν θ u v) w =
      -thirdCentral (Pfam (θ : J → ℝ)) (dirLoss S (w : J → ℝ)) (dirLoss S (v : J → ℝ))
        (dirLoss S (u : J → ℝ)) := by
  rw [fisherInner_mChristoffel hS ν, dotJ_thirdOp hS ν]

/-- The lowered Christoffel operator is symmetric in all three slots. -/
theorem fisherInner_mChristoffel_swap (θ u v w : 𝕍) :
    fisherInner S ν θ (mChristoffel hS ν θ u v) w =
      fisherInner S ν θ (mChristoffel hS ν θ u w) v := by
  rw [fisherInner_mChristoffel hS ν, fisherInner_mChristoffel hS ν,
    dotJ_thirdOp_symm₁₂ hS ν θ w u v, dotJ_thirdOp_symm₂₃ hS ν θ u w v,
    dotJ_thirdOp_symm₁₂ hS ν θ u v w]

/-- **The mixture Christoffel operator is the metric derivative**:
`d/dt G_{θ+tu}(v,w)|₀ = G_θ(C_θ(u,v), w)`. -/
theorem hasDerivAt_fisherInner_line_mChristoffel (θ u v w : 𝕍) :
    HasDerivAt (fun t : ℝ ↦ fisherInner S ν (θ + t • u) v w)
      (fisherInner S ν θ (mChristoffel hS ν θ u v) w) 0 := by
  rw [fisherInner_mChristoffel hS ν, dotJ_thirdOp_symm₁₂ hS ν θ w u v,
    dotJ_thirdOp_symm₂₃ hS ν θ u w v]
  exact hasDerivAt_fisherInner_line_swap hS ν θ u v w

omit [Nonempty J] in
theorem fisherInner_sub_left (θ u u' v : 𝕍) :
    fisherInner S ν θ (u - u') v = fisherInner S ν θ u v - fisherInner S ν θ u' v := by
  rw [sub_eq_add_neg, fisherInner_add_left hS ν, ← neg_one_smul ℝ u', fisherInner_smul_left,
    neg_one_mul, ← sub_eq_add_neg]

/-- **Uniqueness**: a vector lowering to the third cumulant against every direction is the
mixture Christoffel operator. -/
theorem mChristoffel_unique (θ u v : 𝕍) {c : 𝕍}
    (hc : ∀ w : 𝕍, fisherInner S ν θ c w = -dotJ (w : J → ℝ) (thirdOp hS ν θ u v : J → ℝ)) :
    c = mChristoffel hS ν θ u v := by
  by_contra hne
  have hd : c - mChristoffel hS ν θ u v ≠ 0 := sub_ne_zero.mpr hne
  have h0 : fisherInner S ν θ (c - mChristoffel hS ν θ u v) (c - mChristoffel hS ν θ u v) = 0 := by
    rw [fisherInner_sub_left hS ν, hc, fisherInner_mChristoffel hS ν, sub_self]
  exact (fisherInner_self_pos hS ν θ hd).ne' h0

end Jets

section Response

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k)
include hS hg hk

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The response Hessian is the mixture-covariant Hessian**:
`H_g(k,ℓ) = A⁻¹ B_g(k,ℓ) − C_θ(DΦ_g k, DΦ_g ℓ)` at `θ = Φ(g)`. -/
theorem responseHess_eq_sub_mChristoffel {ℓ : X → ℝ} (hℓ : Bdd ℓ) :
    responseHess hS ν hg hk hℓ =
      (CDE (responseOf hS ν g)).symm (dataThird hS ν hg hk hℓ) -
        mChristoffel hS ν (responseOf hS ν g) (responseVel hS ν hg hk)
          (responseVel hS ν hg hℓ) := by
  unfold responseHess mChristoffel
  rw [map_sub]

/-- **Mixture journeys are m-geodesics of the response chart**: the acceleration of the response
along the mixture journey is `−C_θ(V,V)` with `V = DΦ_g k`. -/
theorem mixResponseAccel_eq_neg_mChristoffel :
    mixResponseAccel hS ν hg hk =
      -mChristoffel hS ν (responseOf hS ν g) (responseVel hS ν hg hk) (responseVel hS ν hg hk) :=
  rfl

/-- The m-geodesic equation for the mixture journey: `θ'' + C_θ(θ',θ') = 0` at `t = 0`. -/
theorem hasDerivAt_mixResponseVel_zero_mChristoffel :
    HasDerivAt (mixResponseVel hS ν hg hk)
      (-mChristoffel hS ν (responseOf hS ν g) (responseVel hS ν hg hk) (responseVel hS ν hg hk))
      0 :=
  hasDerivAt_mixResponseVel_zero' hS ν hg hk

end Response

end Laplace.Multi
