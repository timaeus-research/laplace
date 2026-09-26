/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DataRetraction
import Laplace.Multi.ProjectionPythagoras
import Laplace.Multi.EntropyProjection

/-!
# The dual foliation: KL splitting against every family member and Fisher orthogonality

* `toReal_klDiv_split_family`, `klDiv_split_family`: for a law `ρ ≪ ν` of finite information with
  response `M`, and every family member `Q_θ`,
  `KL(ρ ‖ Q_θ) = KL(ρ ‖ Q_M) + KL(Q_M ‖ Q_θ)`. The reconstruction `Q_M` is therefore the unique
  information projection of `ρ` onto the whole family (`klDiv_family_le`, `eq_of_klDiv_family_eq`):
  the fixed-response fibre through `ρ` and the family meet at `Q_M` orthogonally in the KL sense.
* `integral_responseScore_mul_invisible`: an invisible direction `k` (zero mass, zero feature
  moments) is orthogonal to every tangent score, `∫ ℓ_{M,u} k dν = 0`.
* `momentL1_toL1_famDens_mul`, `dataReconDeriv_section`: at a point `q_M` of the section, a data
  tangent `h = q_M φ` has visible part `Cov_{Q_M}(S, φ)` and `DR_{q_M}[q_M φ] = q_M · B_M φ`: the
  retraction differential at the section is the regression (Fisher-orthogonal) projection, and the
  tangent Pythagoras `E_{Q_M} φ² = g_M(c_φ, c_φ) + E_{Q_M}(N_M φ)²` (`TangentPythagoras`) is the
  orthogonal splitting of the data tangent space into the family tangent and the fibre.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The direction loss integrates to `⟨θ, M⟩` under any law with response `M`. -/
theorem integral_dirLoss_of_response (ρ : Measure X) [IsProbabilityMeasure ρ] {M : J → ℝ}
    (hρM : (fun i ↦ ∫ x, S i x ∂ρ) = M) (θ : J → ℝ) : ∫ x, dirLoss S θ x ∂ρ = dotJ θ M := by
  unfold dirLoss dotJ
  rw [integral_finsetSum _ fun j _ ↦ (integrable_of_bdd_prob ρ (hS j)).const_mul (θ j)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_const_mul, ← hρM]

omit [Nonempty J] in
/-- The family members have finite information. -/
theorem klDiv_familyMeasure_ne_top (θ : J → ℝ) : klDiv (Pfam θ) ν ≠ ⊤ := by
  rw [familyMeasure_one_zero_eq_tilted hS ν,
    klDiv_tilted_eq ν (Bdd.const_mul (-1) (bdd_dirLoss hS θ))]
  exact ENNReal.ofReal_ne_top

/-- **KL splitting against every family member**: for a law `ρ ≪ ν` of finite information with
response `M` and every natural parameter `θ`,
`KL(ρ ‖ Q_θ) = KL(ρ ‖ Q_M) + KL(Q_M ‖ Q_θ)`. -/
theorem toReal_klDiv_split_family (ρ : Measure X) [IsProbabilityMeasure ρ] (hρν : ρ ≪ ν)
    (hfin : klDiv ρ ν ≠ ⊤) {M : J → ℝ} (hρM : (fun i ↦ ∫ x, S i x ∂ρ) = M)
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (θ : J → ℝ) :
    (klDiv ρ (Pfam θ)).toReal =
      (klDiv ρ (Pfam (θr M))).toReal + (klDiv (Pfam (θr M)) (Pfam θ)).toReal := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hQM := integral_stat_responseTheta hS ν hrel
  obtain ⟨fθ, hfθ⟩ : ∃ f : X → ℝ, f = fun x ↦ -1 * dirLoss S θ x := ⟨_, rfl⟩
  obtain ⟨fM, hfM⟩ : ∃ f : X → ℝ, f = fun x ↦ -1 * dirLoss S (θr M) x := ⟨_, rfl⟩
  have hbθ : Bdd fθ := hfθ ▸ Bdd.const_mul (-1) (bdd_dirLoss hS θ)
  have hbM : Bdd fM := hfM ▸ Bdd.const_mul (-1) (bdd_dirLoss hS (θr M))
  have hPθ : Pfam θ = ν.tilted fθ := by rw [hfθ]; exact familyMeasure_one_zero_eq_tilted hS ν θ
  have hPM : Pfam (θr M) = ν.tilted fM := by
    rw [hfM]; exact familyMeasure_one_zero_eq_tilted hS ν (θr M)
  have hQν : Pfam (θr M) ≪ ν := by rw [hPM]; exact tilted_absolutelyContinuous ν _
  have hQfin := klDiv_familyMeasure_ne_top hS ν (θr M)
  -- the integrals of the direction losses
  have iθρ : ∫ x, fθ x ∂ρ = -1 * dotJ θ M := by
    rw [hfθ, integral_const_mul, integral_dirLoss_of_response hS ρ hρM]
  have iMρ : ∫ x, fM x ∂ρ = -1 * dotJ (θr M) M := by
    rw [hfM, integral_const_mul, integral_dirLoss_of_response hS ρ hρM]
  have iθQ : ∫ x, fθ x ∂(Pfam (θr M)) = -1 * dotJ θ M := by
    rw [hfθ, integral_const_mul, integral_dirLoss_of_response hS _ hQM]
  have iMQ : ∫ x, fM x ∂(Pfam (θr M)) = -1 * dotJ (θr M) M := by
    rw [hfM, integral_const_mul, integral_dirLoss_of_response hS _ hQM]
  -- the tilted-reference formulas
  have e1 := toReal_klDiv_tilted_right ν ρ hρν hfin hbθ
  have e2 := toReal_klDiv_tilted_right ν ρ hρν hfin hbM
  have e3 := toReal_klDiv_tilted_right ν (Pfam (θr M)) hQν hQfin hbθ
  have e4 := toReal_klDiv_tilted_right ν (Pfam (θr M)) hQν hQfin hbM
  rw [← hPM, klDiv_self, ENNReal.toReal_zero, iMQ] at e4
  rw [← hPθ] at e1 e3
  rw [← hPM] at e2
  rw [e1, e2, e3, iθρ, iMρ, iθQ]
  linarith

omit [Nonempty J] in
/-- The information of a law with respect to a family member is finite. -/
theorem klDiv_family_ne_top (ρ : Measure X) [IsProbabilityMeasure ρ] (hρν : ρ ≪ ν)
    (hfin : klDiv ρ ν ≠ ⊤) (θ : J → ℝ) : klDiv ρ (Pfam θ) ≠ ⊤ := by
  rw [familyMeasure_one_zero_eq_tilted hS ν,
    klDiv_tilted_right_eq ν ρ hρν hfin (Bdd.const_mul (-1) (bdd_dirLoss hS θ))]
  exact ENNReal.ofReal_ne_top

/-- **KL splitting against every family member** (in `ℝ≥0∞`). -/
theorem klDiv_split_family (ρ : Measure X) [IsProbabilityMeasure ρ] (hρν : ρ ≪ ν)
    (hfin : klDiv ρ ν ≠ ⊤) {M : J → ℝ} (hρM : (fun i ↦ ∫ x, S i x ∂ρ) = M)
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (θ : J → ℝ) :
    klDiv ρ (Pfam θ) = klDiv ρ (Pfam (θr M)) + klDiv (Pfam (θr M)) (Pfam θ) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hQν : Pfam (θr M) ≪ ν := by
    rw [familyMeasure_one_zero_eq_tilted hS ν]; exact tilted_absolutelyContinuous ν _
  have h1 := klDiv_family_ne_top hS ν ρ hρν hfin θ
  have h2 := klDiv_family_ne_top hS ν ρ hρν hfin (θr M)
  have h3 := klDiv_family_ne_top hS ν (Pfam (θr M)) hQν (klDiv_familyMeasure_ne_top hS ν _) θ
  rw [← ENNReal.toReal_eq_toReal_iff' h1 (ENNReal.add_ne_top.2 ⟨h2, h3⟩), ENNReal.toReal_add h2 h3]
  exact toReal_klDiv_split_family hS ν ρ hρν hfin hρM hrel θ

/-- **The reconstruction is the information projection onto the whole family**:
`KL(ρ ‖ Q_M) ≤ KL(ρ ‖ Q_θ)` for every `θ`. -/
theorem klDiv_family_le (ρ : Measure X) [IsProbabilityMeasure ρ] (hρν : ρ ≪ ν)
    (hfin : klDiv ρ ν ≠ ⊤) {M : J → ℝ} (hρM : (fun i ↦ ∫ x, S i x ∂ρ) = M)
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (θ : J → ℝ) :
    klDiv ρ (Pfam (θr M)) ≤ klDiv ρ (Pfam θ) := by
  rw [klDiv_split_family hS ν ρ hρν hfin hρM hrel θ]
  exact le_self_add

/-- **Uniqueness of the information projection**: equality holds only at the reconstruction. -/
theorem klDiv_family_eq_iff (ρ : Measure X) [IsProbabilityMeasure ρ] (hρν : ρ ≪ ν)
    (hfin : klDiv ρ ν ≠ ⊤) {M : J → ℝ} (hρM : (fun i ↦ ∫ x, S i x ∂ρ) = M)
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (θ : J → ℝ) :
    klDiv ρ (Pfam θ) = klDiv ρ (Pfam (θr M)) ↔ Pfam (θr M) = Pfam θ := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hPθ : IsProbabilityMeasure (Pfam θ) :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) θ
  have h2 := klDiv_family_ne_top hS ν ρ hρν hfin (θr M)
  rw [klDiv_split_family hS ν ρ hρν hfin hρM hrel θ, ← klDiv_eq_zero_iff]
  constructor
  · intro h
    have := (ENNReal.add_right_inj h2).1 (h.trans (add_zero _).symm)
    exact this
  · intro h
    rw [h, add_zero]

section Fisher

variable {M : J → ℝ}

/-- **Invisible directions are orthogonal to the tangent scores**: if `∫ k dν = 0` and
`∫ S k dν = 0` then `∫ ℓ_{M,u} k dν = 0`. -/
theorem integral_responseScore_mul_invisible (u : 𝕍) {k : X → ℝ} (hk : Integrable k ν)
    (hk0 : ∫ x, k x ∂ν = 0) (hkS : ∀ j, ∫ x, S j x * k x ∂ν = 0) :
    ∫ x, responseScore hS ν M u x * k x ∂ν = 0 := by
  obtain ⟨w, hw⟩ : ∃ w : J → ℝ, w = ((chartDerivEquiv measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS (θr M)).symm u : J → ℝ) := ⟨_, rfl⟩
  have hSk : ∀ j, Integrable (fun x ↦ S j x * k x) ν := fun j ↦
    hk.bdd_mul (hS j).1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact (hS j).2.choose_spec x)
  have e : ∀ x, responseScore hS ν M u x * k x =
      dotJ w M * k x - ∑ j, w j * (S j x * k x) := fun x ↦ by
    unfold responseScore dirLoss
    rw [← hw, sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp_rw [e]
  rw [integral_sub (hk.const_mul _) (integrable_finsetSum _ fun j _ ↦ (hSk j).const_mul _),
    integral_const_mul, integral_finsetSum _ fun j _ ↦ (hSk j).const_mul _, hk0, mul_zero]
  simp only [integral_const_mul, hkS, mul_zero, Finset.sum_const_zero, sub_zero]

/-- A bounded relative perturbation `φ` of `q_M` gives an integrable data tangent `q_M φ`. -/
theorem integrable_famDens_mul_of_bdd {φ : X → ℝ} (hφ : Bdd φ) :
    Integrable (fun x ↦ famDens S ν (θr M) x * φ x) ν := by
  obtain ⟨B, hB0, hB⟩ := exists_feature_bound hS
  exact integrable_of_bdd_prob ν ((bdd_famDens hS ν hB0 hB _).mul hφ)

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

omit hrel in
/-- **The visible part of a data tangent at the section is the response covariance**:
for `h = q_M φ` with `E_{Q_M} φ = 0`, `m(h) = Cov_{Q_M}(S, φ)`. -/
theorem momentL1_toL1_famDens_mul {φ : X → ℝ} (hφ : Bdd φ)
    (hφ0 : ∫ x, famDens S ν (θr M) x * φ x ∂ν = 0) :
    momentL1 hS ν ((integrable_famDens_mul_of_bdd hS ν hφ).toL1
      (fun x ↦ famDens S ν (θr M) x * φ x)) = respCov hS ν M φ := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  funext j
  rw [momentL1_apply]
  have h1 : ∫ x, S j x * ((integrable_famDens_mul_of_bdd hS ν hφ).toL1
      (fun x ↦ famDens S ν (θr M) x * φ x)) x ∂ν =
      ∫ x, famDens S ν (θr M) x * (S j x * φ x) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [Integrable.coeFn_toL1 (integrable_famDens_mul_of_bdd hS ν hφ)] with x hx
    rw [hx]
    ring
  have hφQ : ∫ x, φ x ∂(Pfam (θr M)) = 0 := by rw [integral_famDens_mul hS ν]; exact hφ0
  rw [h1, ← integral_famDens_mul hS ν]
  unfold respCov lawCov
  rw [hφQ, mul_zero, sub_zero]

omit hrel in
/-- **The retraction differential at the section is the regression projection**: for a data
tangent `h = q_M φ` with `E_{Q_M} φ = 0`, `DR_{q_M}[h] = [q_M ℓ_{M, Cov(S,φ)}] = [q_M · B_M φ]`. -/
theorem dataReconDeriv_section {φ : X → ℝ} (hφ : Bdd φ)
    (hφ0 : ∫ x, famDens S ν (θr M) x * φ x ∂ν = 0) :
    ((reconstructionDeriv hS ν M).comp (visibleL1 hS ν))
        ((integrable_famDens_mul_of_bdd hS ν hφ).toL1 (fun x ↦ famDens S ν (θr M) x * φ x)) =
      (integrable_famDens_mul_of_bdd hS ν
        (bdd_responseScore hS ν M ⟨respCov hS ν M φ, respCov_mem_dirSpan hS ν hφ⟩)).toL1
        (fun x ↦ famDens S ν (θr M) x * regProj hS ν M hφ x) := by
  rw [ContinuousLinearMap.comp_apply, visibleL1_apply, momentL1_toL1_famDens_mul hS ν hφ hφ0]
  have e : dirProjL S ν (respCov hS ν M φ) = ⟨respCov hS ν M φ, respCov_mem_dirSpan hS ν hφ⟩ :=
    Subtype.ext (dirProjL_of_mem ν (respCov_mem_dirSpan hS ν hφ))
  rw [e, reconstructionDeriv_apply]
  rfl

/-- **Fisher-orthogonal splitting of a data tangent at the section**: for `E_{Q_M} φ = 0`,
`E_{Q_M} φ² = g_M(c_φ, c_φ) + E_{Q_M}(φ − B_M φ)²` — the visible (tangent-score) part and the
invisible (fibre) part are orthogonal in `L²(Q_M)`. -/
theorem fisher_orthogonal_splitting {φ : X → ℝ} (hφ : Bdd φ)
    (hφ0 : ∫ x, famDens S ν (θr M) x * φ x ∂ν = 0) :
    ∫ x, φ x ^ 2 ∂(Pfam (θr M)) =
      fisherForm hS ν M ⟨respCov hS ν M φ, respCov_mem_dirSpan hS ν hφ⟩
        ⟨respCov hS ν M φ, respCov_mem_dirSpan hS ν hφ⟩ +
        ∫ x, (φ x - regProj hS ν M hφ x) ^ 2 ∂(Pfam (θr M)) := by
  have hφQ : ∫ x, φ x ∂(Pfam (θr M)) = 0 := by rw [integral_famDens_mul hS ν]; exact hφ0
  have h := tangent_pythagoras hS ν hrel hφ
  rw [hφQ] at h
  simp only [sub_zero] at h
  rw [h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [normalProj, hφQ, sub_zero]

end Fisher

end Laplace.Multi
