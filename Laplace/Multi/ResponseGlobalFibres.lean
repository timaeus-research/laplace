/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseMixtureCoordinates

/-!
# The fibres of the response map

The response map `Φ(g) = θ(E_{ρ_g} S)` on bounded tilts is a **fixed-moment map**: two data laws
have the same response exactly when they have the same feature means (`responseOf_eq_iff`). Hence
the fibres `{g : Φ(g) = θ}` are convex under mixing of laws: the endpoint mixture tilt of two
members of a fibre stays in the fibre (`responseOf_mixTilt_of_eq`). Every fibre contains a
canonical model representative, the model tilt `−⟨θ, S⟩` whose law is `P_θ`
(`responseOf_modelTilt`), and the mixture segment from any member of the fibre to its model
representative stays in the fibre (`responseOf_mix_model`): at law level `ρ ↦ (1 − t) ρ + t
P_{Φ(ρ)}` is a response-preserving contraction of the data manifold onto the family
(`integral_mix_model`). The response map is thus the quotient of the bounded-tilt data manifold by
its fixed-moment fibres, each fibre a convex set in density coordinates retracting onto the
exponential family.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Fibres

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
variable (S) in
/-- The feature means of a data law. -/
noncomputable def tiltedMean (g : X → ℝ) : J → ℝ := fun j ↦ ∫ x, S j x ∂ν.tilted g

/-- **The response is a fixed-moment map**: `Φ(g) = Φ(h) ↔ E_{ρ_g} S = E_{ρ_h} S`. -/
theorem responseOf_eq_iff {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h) :
    responseOf hS ν g = responseOf hS ν h ↔ tiltedMean S ν g = tiltedMean S ν h := by
  constructor
  · intro e
    have e' : θr (tiltedMean S ν g) = θr (tiltedMean S ν h) := e
    have h1 := meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (mean_tilted_mem_intrinsicInterior hS ν hg)
    have h2 := meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (mean_tilted_mem_intrinsicInterior hS ν hh)
    change mean (θr (tiltedMean S ν g)) = tiltedMean S ν g at h1
    change mean (θr (tiltedMean S ν h)) = tiltedMean S ν h at h2
    rw [← h1, ← h2, e']
  · intro e
    change θr (tiltedMean S ν g) = θr (tiltedMean S ν h)
    rw [e]

omit [Nonempty X] [Fintype J] [Nonempty J] in
/-- The means of an endpoint mixture. -/
theorem tiltedMean_mixTilt {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    tiltedMean S ν (mixTilt ν g h t) = (1 - t) • tiltedMean S ν g + t • tiltedMean S ν h :=
  mean_mixTilt hS ν hg hh ht0 ht1

/-- **Fibres are convex under mixing**: the endpoint mixture of two data laws with the same
response has that response. -/
theorem responseOf_mixTilt_of_eq {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h)
    (e : responseOf hS ν g = responseOf hS ν h) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    responseOf hS ν (mixTilt ν g h t) = responseOf hS ν g := by
  rw [responseOf_eq_iff hS ν (bdd_mixTilt ν hg hh ht0 ht1) hg,
    tiltedMean_mixTilt hS ν hg hh ht0 ht1, ← (responseOf_eq_iff hS ν hg hh).1 e, ← add_smul,
    sub_add_cancel, one_smul]

variable (S) in
/-- The model tilt `−⟨θ, S⟩`, whose law is `P_θ`. -/
noncomputable def modelTilt (θ : J → ℝ) : X → ℝ := fun x ↦ -1 * dirLoss S θ x

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem bdd_modelTilt (θ : J → ℝ) : Bdd (modelTilt S θ) := (bdd_dirLoss hS θ).const_mul (-1)

omit [Nonempty J] in
theorem tilted_modelTilt (θ : J → ℝ) : ν.tilted (modelTilt S θ) = Pfam θ :=
  (familyMeasure_one_zero_eq_tilted hS ν θ).symm

omit [Nonempty J] in
theorem tiltedMean_modelTilt (θ : J → ℝ) : tiltedMean S ν (modelTilt S θ) = mean θ := by
  change (fun j ↦ ∫ x, S j x ∂ν.tilted (modelTilt S θ)) = _
  rw [tilted_modelTilt hS ν θ]
  exact mean_familyMeasure_one_zero hS ν θ

/-- The response of a family mean is its natural coordinate. -/
theorem responseTheta_meanMap (θ : 𝕍) : θr (mean (θ : J → ℝ)) = θ := by
  unfold responseTheta
  have e : toV ν (fun _ ↦ (1 : ℝ)) S (mean (θ : J → ℝ)) =
      chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS θ := by
    apply Subtype.ext
    rw [toV_apply (meanMap_sub_mem_dirSpan measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS _ 0), chartV_apply]
  rw [e, chartVInv_chartV]

/-- **The model tilt is a section of the response map**: `Φ(−⟨θ,S⟩) = θ`. -/
theorem responseOf_modelTilt (θ : 𝕍) : responseOf hS ν (modelTilt S (θ : J → ℝ)) = θ := by
  change θr (tiltedMean S ν (modelTilt S (θ : J → ℝ))) = θ
  rw [tiltedMean_modelTilt hS ν, responseTheta_meanMap hS ν θ]

/-- **The fibre retracts onto its model representative**: the mixture segment from `ρ_g` to
`P_{Φ(g)}` stays in the fibre of `Φ(g)`. -/
theorem responseOf_mix_model {g : X → ℝ} (hg : Bdd g) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    responseOf hS ν (mixTilt ν g (modelTilt S (responseOf hS ν g : J → ℝ)) t) =
      responseOf hS ν g :=
  responseOf_mixTilt_of_eq hS ν hg (bdd_modelTilt hS _) (responseOf_modelTilt hS ν _).symm ht0 ht1

/-- The law of the retraction segment: `(1 − t) ρ_g + t P_{Φ(g)}`. -/
theorem integral_mix_model {g : X → ℝ} (hg : Bdd g) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {f : X → ℝ} (hf : Bdd f) :
    ∫ x, f x ∂ν.tilted (mixTilt ν g (modelTilt S (responseOf hS ν g : J → ℝ)) t) =
      (1 - t) * ∫ x, f x ∂ν.tilted g + t * ∫ x, f x ∂Pfam (responseOf hS ν g : J → ℝ) := by
  rw [integral_mixTilt ν hg (bdd_modelTilt hS _) ht0 ht1 hf, tilted_modelTilt hS ν]

/-- **Fibres are determined by the model representative**: `Φ(g) = θ ↔ E_{ρ_g} S = E_{P_θ} S`. -/
theorem responseOf_eq_iff_tiltedMean_eq_meanMap {g : X → ℝ} (hg : Bdd g) (θ : 𝕍) :
    responseOf hS ν g = θ ↔ tiltedMean S ν g = mean (θ : J → ℝ) := by
  rw [← tiltedMean_modelTilt hS ν, ← responseOf_eq_iff hS ν hg (bdd_modelTilt hS _),
    responseOf_modelTilt hS ν θ]

end Fibres

end Laplace.Multi
