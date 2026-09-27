/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFiniteSaturation
import Laplace.Multi.ResponseTopologicalQuotient
import Laplace.Multi.ResponseGlobalInformationLandscape
import Laplace.Multi.FixedNormalLimit
import Laplace.Multi.QuotientMeanMap
import Laplace.Multi.FaceGauge

/-!
# For affinely spanning features the data manifold is the response space

If every bounded function is a.e. an affine function of the features (`SpansAffine`), then every
data law `ρ_g = ν.tilted g` **is** a model law: `ρ_g = P_{Φ(g)}`
(`tilted_eq_familyMeasure_responseOf_of_spansAffine`). Consequently

* the information defect vanishes identically and `KL(ρ_g ‖ ν)` is entirely carried by the
  response journey (`responseInformationDefect_eq_zero_of_spansAffine`,
  `totalInfo_eq_responseInfo_of_spansAffine`);
* the response map `DataLaw ν → W` is injective, hence (being a quotient map with a continuous
  section) a **homeomorphism** `DataLaw ν ≃ₜ W` (`saturatedHomeomorph`): the data manifold and
  the response space coincide, and the fibres of the response are single points.

This is the abstract form of "the full simplex is the model"; the finite affine-basis simplex
satisfies `SpansAffine` pointwise (`spansAffine_of_forall`).
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Identification

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty J] in
/-- A tilt by a feature contrast is the family member at the negated coordinate. -/
theorem tilted_dirLoss_eq_familyMeasure_neg (b : J → ℝ) :
    ν.tilted (dirLoss S b) = Pfam (-b) := by
  rw [← tilted_modelTilt hS ν (-b)]
  congr 1
  funext x
  simp [modelTilt, dirLoss_neg]

/-- **Every data law of an affinely spanning family is a model law**: `ρ_g = P_{Φ(g)}`. -/
theorem tilted_eq_familyMeasure_responseOf_of_spansAffine (hspan : SpansAffine S ν) {g : X → ℝ}
    (hg : Bdd g) : ν.tilted g = Pfam (responseOf hS ν g : J → ℝ) := by
  obtain ⟨b, k, hbk⟩ := hspan g hg
  have e1 : ν.tilted g = Pfam (-b) := by
    rw [tilted_congr hbk, tilted_add_const, tilted_dirLoss_eq_familyMeasure_neg hS ν]
  have hm : mean (responseOf hS ν g : J → ℝ) = mean (-b) := by
    rw [← (responseOf_eq_iff_tiltedMean_eq_meanMap hS ν hg _).1 rfl,
      ← tiltedMean_modelTilt hS ν (-b)]
    unfold tiltedMean
    rw [e1, tilted_modelTilt hS ν]
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hk : -b - (responseOf hS ν g : J → ℝ) ∈ invisibleSet ν S :=
    (meanMap_eq_iff_invisible measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const h0 hS one_pos _ _).1 hm
  rw [e1, ← familyMeasure_add_of_invisible hS ν (responseOf hS ν g : J → ℝ) hk, add_sub_cancel]

/-- The information defect vanishes identically for an affinely spanning family. -/
theorem responseInformationDefect_eq_zero_of_spansAffine (hspan : SpansAffine S ν) {g : X → ℝ}
    (hg : Bdd g) : responseInformationDefect hS ν g = 0 :=
  (responseInformationDefect_eq_zero_iff hS ν hg).2
    (tilted_eq_familyMeasure_responseOf_of_spansAffine hS ν hspan hg)

/-- **All information is carried by the response** for an affinely spanning family. -/
theorem totalInfo_eq_responseInfo_of_spansAffine (hspan : SpansAffine S ν) {g : X → ℝ}
    (hg : Bdd g) : totalInfo ν g = responseInfo hS ν g := by
  rw [totalInfo_eq_defect_add_responseInfo hS ν hg,
    responseInformationDefect_eq_zero_of_spansAffine hS ν hspan hg, zero_add]

omit [Nonempty X] [Nonempty J] hS in
/-- Two bounded tilts with the same law have a.e. the same normalised density. -/
theorem normDens_ae_eq_of_tilted_eq {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k)
    (h : ν.tilted g = ν.tilted k) : normDens ν g =ᵐ[ν] normDens ν k := by
  have hbg := bdd_normDens ν hg
  have hbk := bdd_normDens ν hk
  have hbd : Bdd fun x ↦ normDens ν g x - normDens ν k x := hbg.sub hbk
  have e1 := integral_tilted_eq_normDens ν (g := g) (f := fun x ↦ normDens ν g x - normDens ν k x)
  have e2 := integral_tilted_eq_normDens ν (g := k) (f := fun x ↦ normDens ν g x - normDens ν k x)
  rw [h] at e1
  have h1 : ∫ x, normDens ν g x * (normDens ν g x - normDens ν k x) ∂ν =
      ∫ x, normDens ν k x * (normDens ν g x - normDens ν k x) ∂ν := e1.symm.trans e2
  have hi1 : Integrable (fun x ↦ normDens ν g x * (normDens ν g x - normDens ν k x)) ν :=
    integrable_of_bdd_prob ν (hbg.mul hbd)
  have hi2 : Integrable (fun x ↦ normDens ν k x * (normDens ν g x - normDens ν k x)) ν :=
    integrable_of_bdd_prob ν (hbk.mul hbd)
  have h2 : ∫ x, (normDens ν g x - normDens ν k x) * (normDens ν g x - normDens ν k x) ∂ν = 0 := by
    have e : (fun x ↦ (normDens ν g x - normDens ν k x) * (normDens ν g x - normDens ν k x)) =
        fun x ↦ normDens ν g x * (normDens ν g x - normDens ν k x) -
          normDens ν k x * (normDens ν g x - normDens ν k x) := by
      funext x; ring
    rw [e, integral_sub hi1 hi2, h1, sub_self]
  have hint : Integrable (fun x ↦ (normDens ν g x - normDens ν k x) *
      (normDens ν g x - normDens ν k x)) ν := integrable_of_bdd_prob ν (hbd.mul hbd)
  have h3 := (integral_eq_zero_iff_of_nonneg (fun x ↦ mul_self_nonneg _) hint).mp h2
  filter_upwards [h3] with x hx
  simp only [Pi.zero_apply, mul_self_eq_zero, sub_eq_zero] at hx
  exact hx

/-- **The response map is injective on the data manifold** of an affinely spanning family. -/
theorem lawResponse_injective_of_spansAffine (hspan : SpansAffine S ν) :
    Function.Injective (lawResponse hS ν) := by
  intro p q hpq
  obtain ⟨g, hg, hp⟩ := p.2
  obtain ⟨k, hk, hq⟩ := q.2
  have hp' : p = toDataLaw ν g hg := Subtype.ext hp
  have hq' : q = toDataLaw ν k hk := Subtype.ext hq
  rw [hp', hq', lawResponse_toDataLaw hS ν, lawResponse_toDataLaw hS ν] at hpq
  have ht : ν.tilted g = ν.tilted k := by
    rw [tilted_eq_familyMeasure_responseOf_of_spansAffine hS ν hspan hg,
      tilted_eq_familyMeasure_responseOf_of_spansAffine hS ν hspan hk, hpq]
  rw [hp', hq']
  exact Subtype.ext (MemLp.toLp_congr (memLp_normDens ν hg) (memLp_normDens ν hk)
    (normDens_ae_eq_of_tilted_eq ν hg hk ht))

/-- **The data manifold of an affinely spanning family is the response space**: the response
map is a homeomorphism `DataLaw ν ≃ₜ W` with inverse the model law. -/
noncomputable def saturatedHomeomorph (hspan : SpansAffine S ν) : DataLaw ν ≃ₜ 𝕍 where
  toFun := lawResponse hS ν
  invFun := modelLaw hS ν
  left_inv p := lawResponse_injective_of_spansAffine hS ν hspan
    (lawResponse_modelLaw hS ν (lawResponse hS ν p))
  right_inv := lawResponse_modelLaw hS ν
  continuous_toFun := continuous_lawResponse hS ν
  continuous_invFun := continuous_modelLaw hS ν

/-- Response fibres are single points for an affinely spanning family. -/
theorem eq_of_lawResponse_eq_of_spansAffine (hspan : SpansAffine S ν) {p q : DataLaw ν}
    (h : lawResponse hS ν p = lawResponse hS ν q) : p = q :=
  lawResponse_injective_of_spansAffine hS ν hspan h

end Identification

end Laplace.Multi
