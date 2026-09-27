/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDensityTopology
import Mathlib.Analysis.Convex.Contractible

/-!
# The mixture deformation retraction onto the family and contractible fibres

Mixtures of data laws are data laws: the normalised density of the mixture tilt is the mixture of
the densities (`normDens_mixTilt`, `lawDens_mixTilt`), so the space of data laws is a **convex**
subset of `L¹(ν)` (`convex_dataLawSet`), hence contractible (`contractibleSpace_dataLaw`).

The **mixture deformation** `H_t(p) = (1 − t) p + t p_{Φ(p)}` (`deform`) slides every data law along
the mixture segment to the model law with the same moments. It is jointly continuous
(`continuous_deform`), starts at the identity (`deform_zero`), ends on the family (`deform_one`),
fixes the family pointwise (`deform_modelLaw`) and **preserves the response**
(`lawResponse_deform`): it is a strong deformation retraction of the space of data laws onto the
family, fibrewise for the response map. Each response fibre `Φ⁻¹(θ)` is a convex subset of `L¹(ν)`
containing the model law `p_θ` (`convex_responseFibre`), hence **contractible**
(`contractibleSpace_responseFibre`).
-/

open MeasureTheory Filter Topology Set unitInterval

namespace Laplace.Multi

section Mixture

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- **The normalised density of the mixture tilt is the mixture of the densities.** -/
theorem normDens_mixTilt {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    normDens ν (mixTilt ν g h t) = fun x ↦ (1 - t) * normDens ν g x + t * normDens ν h x := by
  funext x
  have hpos := mixDens_pos ν hg hh ht0 ht1
  have hint : ∫ y, Real.exp (mixTilt ν g h t y) ∂ν = 1 := by
    have e : (fun y ↦ Real.exp (mixTilt ν g h t y)) =
        fun y ↦ (1 - t) * normDens ν g y + t * normDens ν h y :=
      funext fun y ↦ Real.exp_log (hpos y)
    rw [e, integral_add ((integrable_of_bdd_prob ν (bdd_normDens ν hg)).const_mul _)
      ((integrable_of_bdd_prob ν (bdd_normDens ν hh)).const_mul _), integral_const_mul,
      integral_const_mul, integral_normDens ν hg, integral_normDens ν hh]
    ring
  have e : normDens ν (mixTilt ν g h t) x =
      Real.exp (mixTilt ν g h t x) / ∫ y, Real.exp (mixTilt ν g h t y) ∂ν := rfl
  rw [e, hint, div_one]
  exact Real.exp_log (hpos x)

/-- **Mixtures of data laws are data laws** in `L¹(ν)`. -/
theorem lawDens_mixTilt {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    lawDens ν (mixTilt ν g h t) (bdd_mixTilt ν hg hh ht0 ht1) =
      (1 - t) • lawDens ν g hg + t • lawDens ν h hh := by
  unfold lawDens
  rw [← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ ?_)
  rw [normDens_mixTilt ν hg hh ht0 ht1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The set of data laws inside `L¹(ν)`. -/
def dataLawSet : Set (Lp ℝ 1 ν) := {p | ∃ g : X → ℝ, ∃ hg : Bdd g, p = lawDens ν g hg}

theorem mem_dataLawSet_iff (p : Lp ℝ 1 ν) :
    p ∈ dataLawSet ν ↔ ∃ g : X → ℝ, ∃ hg : Bdd g, p = lawDens ν g hg := Iff.rfl

/-- **The space of data laws is convex.** -/
theorem convex_dataLawSet : Convex ℝ (dataLawSet ν) := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ a b ha hb hab
  refine ⟨mixTilt ν g h b, bdd_mixTilt ν hg hh hb (by linarith), ?_⟩
  rw [lawDens_mixTilt ν hg hh hb (by linarith), show 1 - b = a by linarith]

theorem nonempty_dataLawSet : (dataLawSet ν).Nonempty :=
  ⟨lawDens ν (fun _ ↦ 0) (Bdd.const 0), fun _ ↦ 0, Bdd.const 0, rfl⟩

/-- **The space of data laws is contractible.** -/
theorem contractibleSpace_dataLaw : ContractibleSpace (DataLaw ν) :=
  (convex_dataLawSet ν).contractibleSpace (nonempty_dataLawSet ν)

end Mixture

section Deform

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- **The mixture deformation** `H_t(p) = (1 − t) p + t p_{Φ(p)}` of a data law toward the model
law with the same moments. -/
noncomputable def deform (t : I) (p : DataLaw ν) : DataLaw ν :=
  ⟨(1 - (t : ℝ)) • p.1 + (t : ℝ) • (modelLaw hS ν (lawResponse hS ν p)).1, by
    obtain ⟨g, hg, hp⟩ := p.2
    refine ⟨mixTilt ν g (modelTilt S (lawResponse hS ν p : J → ℝ)) t,
      bdd_mixTilt ν hg (bdd_modelTilt hS _) t.2.1 t.2.2, ?_⟩
    rw [lawDens_mixTilt ν hg (bdd_modelTilt hS _) t.2.1 t.2.2, ← hp]
    rfl⟩

theorem deform_coe (t : I) (p : DataLaw ν) :
    (deform hS ν t p).1 = (1 - (t : ℝ)) • p.1 + (t : ℝ) • (modelLaw hS ν (lawResponse hS ν p)).1 :=
  rfl

/-- The deformation starts at the identity. -/
theorem deform_zero (p : DataLaw ν) : deform hS ν 0 p = p :=
  Subtype.ext (by rw [deform_coe]; simp)

/-- The deformation ends on the family. -/
theorem deform_one (p : DataLaw ν) : deform hS ν 1 p = modelLaw hS ν (lawResponse hS ν p) :=
  Subtype.ext (by rw [deform_coe]; simp)

/-- The deformation fixes the family pointwise. -/
theorem deform_modelLaw (t : I) (θ : 𝕍) : deform hS ν t (modelLaw hS ν θ) = modelLaw hS ν θ :=
  Subtype.ext (by rw [deform_coe, lawResponse_modelLaw, ← add_smul, sub_add_cancel, one_smul])

/-- The deformation of the law of a tilt is the law of the mixture tilt with its model law. -/
theorem deform_toDataLaw (t : I) {g : X → ℝ} (hg : Bdd g) :
    deform hS ν t (toDataLaw ν g hg) =
      toDataLaw ν (mixTilt ν g (modelTilt S (responseOf hS ν g : J → ℝ)) t)
        (bdd_mixTilt ν hg (bdd_modelTilt hS _) t.2.1 t.2.2) := by
  refine Subtype.ext ?_
  rw [deform_coe, lawResponse_toDataLaw]
  exact (lawDens_mixTilt ν hg (bdd_modelTilt hS _) t.2.1 t.2.2).symm

/-- **The deformation preserves the response**: `Φ(H_t(p)) = Φ(p)`. -/
theorem lawResponse_deform (t : I) (p : DataLaw ν) :
    lawResponse hS ν (deform hS ν t p) = lawResponse hS ν p := by
  obtain ⟨g, hg, hp⟩ := p.2
  have hp' : p = toDataLaw ν g hg := Subtype.ext hp
  rw [hp', deform_toDataLaw, lawResponse_toDataLaw, lawResponse_toDataLaw]
  exact responseOf_mixTilt_of_eq hS ν hg (bdd_modelTilt hS _) (responseOf_modelTilt hS ν _).symm
    t.2.1 t.2.2

/-- **The deformation is jointly continuous.** -/
theorem continuous_deform : Continuous fun q : I × DataLaw ν ↦ deform hS ν q.1 q.2 := by
  have hc : Continuous fun q : I × DataLaw ν ↦
      (1 - (q.1 : ℝ)) • q.2.1 + (q.1 : ℝ) • (modelLaw hS ν (lawResponse hS ν q.2)).1 :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp
        ((continuous_modelLaw hS ν).comp ((continuous_lawResponse hS ν).comp continuous_snd))))
  exact hc.subtype_mk _

/-- **The response fibre** over `θ`, as a subset of `L¹(ν)`: the data laws with response `θ`. -/
def responseFibre (θ : 𝕍) : Set (Lp ℝ 1 ν) :=
  {p | ∃ hp : p ∈ dataLawSet ν, lawResponse hS ν ⟨p, hp⟩ = θ}

theorem modelLaw_mem_responseFibre (θ : 𝕍) : (modelLaw hS ν θ).1 ∈ responseFibre hS ν θ :=
  ⟨(modelLaw hS ν θ).2, lawResponse_modelLaw hS ν θ⟩

/-- The law of a tilt lies in the fibre of its response. -/
theorem toDataLaw_mem_responseFibre {g : X → ℝ} (hg : Bdd g) :
    (toDataLaw ν g hg).1 ∈ responseFibre hS ν (responseOf hS ν g) :=
  ⟨(toDataLaw ν g hg).2, lawResponse_toDataLaw hS ν hg⟩

/-- **The response fibres are convex.** -/
theorem convex_responseFibre (θ : 𝕍) : Convex ℝ (responseFibre hS ν θ) := by
  rintro p ⟨hp, hpθ⟩ q ⟨hq, hqθ⟩ a b ha hb hab
  obtain ⟨g, hg, rfl⟩ := hp
  obtain ⟨h, hh, rfl⟩ := hq
  have hmix := bdd_mixTilt ν hg hh hb (by linarith)
  have h1 : responseOf hS ν g = θ := by rw [← lawResponse_toDataLaw hS ν hg]; exact hpθ
  have h2 : responseOf hS ν h = θ := by rw [← lawResponse_toDataLaw hS ν hh]; exact hqθ
  have e : a • lawDens ν g hg + b • lawDens ν h hh = lawDens ν (mixTilt ν g h b) hmix := by
    rw [lawDens_mixTilt ν hg hh hb (by linarith), show 1 - b = a by linarith]
  refine ⟨⟨mixTilt ν g h b, hmix, e⟩, ?_⟩
  have e' : (⟨a • lawDens ν g hg + b • lawDens ν h hh, ⟨mixTilt ν g h b, hmix, e⟩⟩ : DataLaw ν) =
      toDataLaw ν (mixTilt ν g h b) hmix := Subtype.ext e
  rw [e', lawResponse_toDataLaw, responseOf_mixTilt_of_eq hS ν hg hh (h1.trans h2.symm) hb
    (by linarith), h1]

/-- **The response fibres are contractible.** -/
theorem contractibleSpace_responseFibre (θ : 𝕍) : ContractibleSpace (responseFibre hS ν θ) :=
  (convex_responseFibre hS ν θ).contractibleSpace ⟨_, modelLaw_mem_responseFibre hS ν θ⟩

end Deform

end Laplace.Multi
