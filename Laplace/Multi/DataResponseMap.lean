/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.EntropyCompletion
import Laplace.Multi.ThermalTransport

/-!
# The data-to-response map and the exact information decomposition

The completion principle furnishes, for every response `M` of finite rate, a unique entropy
minimiser: the **response projection** `Π_ν(M)` (`responseProjection`). This turns the response of
any data law into a canonical representative, and the Pythagorean form of completion becomes the
flagship identity of the whole programme, for every probability law `D`:
  `KL(D ‖ ν) = 𝓘_ν(E_D S) + KL(D ‖ Π_ν(E_D S))`             (`information_decomposition`),
total information in the data = information visible through the responses + information
invisible to them (both sides `⊤` when the rate is infinite, `klDiv_eq_top_of_genRate_eq_top`).

Laws equivalent to `ν` have responses in the relative interior of the moment body
(`mean_mem_intrinsicInterior_of_equiv`), in particular all bounded exponential tilts
(`mean_tilted_mem_intrinsicInterior`). Along the exponential data path `D_s = ν.tilted (s f)`
towards a data law `D = ν.tilted f` the response moves by covariance
(`hasDerivAt_dataResponsePath`), the information accumulates as `∫₀ˢ u Var_{D_u}(f) du`
(`klDiv_tilted_eq_integral`), and this integral splits exactly into the visible rate and the
invisible residual (`information_decomposition_path`).

On a positive supporting face the projection is the projection of the conditioned law
(`responseProjection_faceMeasure`): the conditional charts are compatible with the entry costs.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hS

open Classical in
/-- **The response projection** `Π_ν(M)`: the unique entropy minimiser with response `M` (the zero
measure when `ν` is not a probability law or the rate is infinite). -/
noncomputable def responseProjection (ν : Measure X) (M : J → ℝ) : Measure X :=
  if h : IsProbabilityMeasure ν ∧ genRate ν S M ≠ ⊤ then
    (haveI := h.1; Classical.choose (exists_pythagorean_minimiser hS ν h.2))
  else 0

theorem responseProjection_spec (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
    (hfin : genRate ν S M ≠ ⊤) :
    IsProbabilityMeasure (responseProjection hS ν M) ∧
      (fun i ↦ ∫ x, S i x ∂responseProjection hS ν M) = M ∧
      klDiv (responseProjection hS ν M) ν = genRate ν S M ∧
      ∀ ρ : Measure X, IsProbabilityMeasure ρ → (fun i ↦ ∫ x, S i x ∂ρ) = M →
        klDiv ρ ν = klDiv ρ (responseProjection hS ν M) + genRate ν S M := by
  unfold responseProjection
  rw [dif_pos ⟨inferInstance, hfin⟩]
  exact Classical.choose_spec (exists_pythagorean_minimiser hS ν hfin)

omit [Nonempty X] [Nonempty J] in
/-- An infinite rate at the response of `D` means infinite information in `D`. -/
theorem klDiv_eq_top_of_genRate_eq_top (ν : Measure X) [IsProbabilityMeasure ν] (D : Measure X)
    [IsProbabilityMeasure D] (h : genRate ν S (fun i ↦ ∫ x, S i x ∂D) = ⊤) : klDiv D ν = ⊤ :=
  top_le_iff.1 (h ▸ genRate_le_klDiv ν hS D rfl)

/-- **The exact information decomposition**: `KL(D ‖ ν) = 𝓘_ν(E_D S) + KL(D ‖ Π_ν(E_D S))`. -/
theorem information_decomposition (ν : Measure X) [IsProbabilityMeasure ν] (D : Measure X)
    [IsProbabilityMeasure D] (hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤) :
    klDiv D ν = genRate ν S (fun i ↦ ∫ x, S i x ∂D) +
      klDiv D (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)) := by
  rw [(responseProjection_spec hS ν hfin).2.2.2 D inferInstance rfl, add_comm]

omit [Nonempty X] [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- The essential range is the same for equivalent laws. -/
theorem essRange_eq_of_equiv (ν D : Measure X) (hDν : D ≪ ν) (hνD : ν ≪ D) :
    essRange D (fun _ ↦ (1 : ℝ)) S = essRange ν (fun _ ↦ (1 : ℝ)) S := by
  ext y
  rw [mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS,
    mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS]
  refine forall_congr' fun r ↦ forall_congr' fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra h0
    exact h.ne' (hDν (le_antisymm (not_lt.1 h0) zero_le))
  · by_contra h0
    exact h.ne' (hνD (le_antisymm (not_lt.1 h0) zero_le))

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- The response of a law lies in its own moment body. -/
theorem mean_mem_momentBody_general (D : Measure X) [IsProbabilityMeasure D] :
    (fun i ↦ ∫ x, S i x ∂D) ∈ momentBody D (fun _ ↦ (1 : ℝ)) S := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hπpos : (0 : ℝ) < ∫ x, (fun _ : X ↦ (1 : ℝ)) x ∂D := by simp
  have hm := mean_mem_momentBody (μ := D) measurable_const (integrable_const _) (fun _ ↦ one_pos)
    hπpos hS 0
  have e : meanMap D (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 = fun i ↦ ∫ x, S i x ∂D := by
    funext i
    change priorExp D (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S 0) (S i) 1 = _
    rw [← integral_familyMeasure measurable_const (integrable_const _) (fun _ ↦ one_pos) hπpos
      measurable_const h0 hS 0 (S i), familyMeasure_one_zero D S]
  rw [e] at hm
  exact hm

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **Laws equivalent to `ν` have responses in the relative interior of the moment body.** -/
theorem mean_mem_intrinsicInterior_of_equiv (ν : Measure X) [IsProbabilityMeasure ν]
    (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (hνD : ν ≪ D) :
    (fun i ↦ ∫ x, S i x ∂D) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  rw [mem_intrinsicInterior_iff_forall_supporting (convex_momentBody S)]
  have hK : momentBody D (fun _ ↦ (1 : ℝ)) S = momentBody ν (fun _ ↦ (1 : ℝ)) S := by
    unfold momentBody
    rw [essRange_eq_of_equiv hS ν D hDν hνD]
  refine ⟨hK ▸ mean_mem_momentBody_general hS D, fun e he y hy ↦ ?_⟩
  have hae : ∀ᵐ x ∂ν, dirLoss S e x ≤ dotJ e (fun i ↦ ∫ x, S i x ∂D) := by
    filter_upwards [ae_statPoint_mem_essRange (μ := ν) measurable_const (fun _ ↦ one_pos) hS]
      with x hx
    exact he _ (essRange_subset_momentBody S hx)
  have hcompl := compl_eq_zero_of_mean_face ν hS D hDν hae rfl
  have hμ : ∀ᵐ x ∂ν, dirLoss S e x = dotJ e (fun i ↦ ∫ x, S i x ∂D) := by
    rw [ae_iff]
    exact hνD hcompl
  have hle := momentBody_subset_halfspace (μ := ν) measurable_const (fun _ ↦ one_pos) hS
    (hμ.mono fun x hx ↦ hx.le)
  have hge := momentBody_subset_halfspace (μ := ν) measurable_const (fun _ ↦ one_pos) hS
    (u := -e) (β := -dotJ e (fun i ↦ ∫ x, S i x ∂D)) (by
      filter_upwards [hμ] with x hx
      rw [show -e = (-1 : ℝ) • e by rw [neg_one_smul], dirLoss_smul]
      change (-1 : ℝ) * dirLoss S e x ≤ _
      rw [hx]
      linarith)
  have h1 := hle hy
  have h2 := hge hy
  simp only [Set.mem_ofPred_eq, dotJ_neg_left] at h1 h2
  linarith

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **Bounded exponential tilts have interior responses.** -/
theorem mean_tilted_mem_intrinsicInterior (ν : Measure X) [IsProbabilityMeasure ν] {f : X → ℝ}
    (hf : Bdd f) :
    (fun i ↦ ∫ x, S i x ∂ν.tilted f) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hf)
  exact mean_mem_intrinsicInterior_of_equiv hS ν (ν.tilted f) (tilted_absolutelyContinuous ν f)
    (absolutelyContinuous_tilted (integrable_exp_of_bdd ν hf))

omit [Fintype J] [Nonempty J] in
/-- **The response of the data path moves by covariance**: along `D_s = ν.tilted (s f)`,
`d/ds E_{D_s} S_i = Cov_{D_s}(S_i, f)`. -/
theorem hasDerivAt_dataResponsePath (ν : Measure X) [IsProbabilityMeasure ν] {f : X → ℝ}
    (hf : Bdd f) (i : J) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * f x))
      (∫ x, S i x * f x ∂ν.tilted (fun x ↦ s₀ * f x) -
        (∫ x, S i x ∂ν.tilted (fun x ↦ s₀ * f x)) * ∫ x, f x ∂ν.tilted (fun x ↦ s₀ * f x)) s₀ :=
  hasDerivAt_integral_tilted ν hf (hS i) s₀

omit hS [Fintype J] [Nonempty J] in
/-- The information along the data path is the integrated fluctuation:
`KL(D_s ‖ ν) = ∫₀ˢ u Var_{D_u}(f) du`. -/
theorem klDiv_tilted_eq_integral (ν : Measure X) [IsProbabilityMeasure ν] {f : X → ℝ}
    (hf : Bdd f) (s : ℝ) :
    (klDiv (ν.tilted (fun x ↦ s * f x)) ν).toReal =
      ∫ u in (0 : ℝ)..s, u * (∫ x, f x * f x ∂ν.tilted (fun x ↦ u * f x) -
        (∫ x, f x ∂ν.tilted (fun x ↦ u * f x)) * ∫ x, f x ∂ν.tilted (fun x ↦ u * f x)) := by
  have hc1 : Continuous fun u : ℝ ↦ ∫ x, f x * f x ∂ν.tilted (fun x ↦ u * f x) :=
    continuous_iff_continuousAt.2 fun u ↦
      (hasDerivAt_integral_tilted ν hf (hf.mul hf) u).continuousAt
  have hc2 : Continuous fun u : ℝ ↦ ∫ x, f x ∂ν.tilted (fun x ↦ u * f x) :=
    continuous_iff_continuousAt.2 fun u ↦ (hasDerivAt_integral_tilted ν hf hf u).continuousAt
  have hcont : Continuous fun u : ℝ ↦ u * (∫ x, f x * f x ∂ν.tilted (fun x ↦ u * f x) -
      (∫ x, f x ∂ν.tilted (fun x ↦ u * f x)) * ∫ x, f x ∂ν.tilted (fun x ↦ u * f x)) :=
    continuous_id.mul (hc1.sub (hc2.mul hc2))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u ↦ (klDiv (ν.tilted (fun x ↦ u * f x)) ν).toReal)
    (fun u _ ↦ hasDerivAt_klDiv_tilted_toReal ν hf u) (hcont.intervalIntegrable 0 s)
  rw [h]
  have h0 : ν.tilted (fun x ↦ (0 : ℝ) * f x) = ν := by
    have e : (fun x ↦ (0 : ℝ) * f x) = fun _ ↦ (0 : ℝ) := funext fun x ↦ zero_mul _
    rw [e, tilted_const', measure_univ, inv_one, one_smul]
  rw [h0, klDiv_self, ENNReal.toReal_zero, sub_zero]

/-- **The information decomposition along the data path**:
`∫₀ˢ u Var_{D_u}(f) du = 𝓘_ν(E_{D_s} S) + KL(D_s ‖ Π_ν(E_{D_s} S))`. -/
theorem information_decomposition_path (ν : Measure X) [IsProbabilityMeasure ν] {f : X → ℝ}
    (hf : Bdd f) (s : ℝ) :
    ∫ u in (0 : ℝ)..s, u * (∫ x, f x * f x ∂ν.tilted (fun x ↦ u * f x) -
        (∫ x, f x ∂ν.tilted (fun x ↦ u * f x)) * ∫ x, f x ∂ν.tilted (fun x ↦ u * f x)) =
      (genRate ν S (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * f x))).toReal +
        (klDiv (ν.tilted (fun x ↦ s * f x))
          (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * f x)))).toReal := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (Bdd.const_mul s hf))
  have hkl : klDiv (ν.tilted (fun x ↦ s * f x)) ν ≠ ⊤ := by
    rw [klDiv_tilted_eq ν (Bdd.const_mul s hf)]
    exact ENNReal.ofReal_ne_top
  have hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * f x)) ≠ ⊤ := fun h ↦
    hkl (klDiv_eq_top_of_genRate_eq_top hS ν _ h)
  have hdec := information_decomposition hS ν (ν.tilted (fun x ↦ s * f x)) hfin
  have hres : klDiv (ν.tilted (fun x ↦ s * f x))
      (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * f x))) ≠ ⊤ := by
    rw [hdec] at hkl
    exact (ENNReal.add_ne_top.1 hkl).2
  rw [← klDiv_tilted_eq_integral ν hf s, hdec, ENNReal.toReal_add hfin hres]

/-- **Compatibility of the conditional charts**: on a positive supporting face the response
projection is the projection of the conditioned law. -/
theorem responseProjection_faceMeasure (ν : Measure X) [IsProbabilityMeasure ν] {e : J → ℝ}
    {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss S e x ≤ β) (hp : 0 < ν.real {x | dirLoss S e x = β})
    {M : J → ℝ} (hM : dotJ e M = β)
    (hfinF : genRate (faceMeasure ν {x | dirLoss S e x = β}) S M ≠ ⊤) :
    responseProjection hS ν M =
      responseProjection hS (faceMeasure ν {x | dirLoss S e x = β}) M := by
  have hF0 : ν {x | dirLoss S e x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  have hF : MeasurableSet {x | dirLoss S e x = β} :=
    measurableSet_eq_fun (bdd_dirLoss hS e).1 measurable_const
  have hface := genRate_face_eq ν hS hβ hp hM
  have hfin : genRate ν S M ≠ ⊤ := by
    rw [hface]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hfinF⟩
  obtain ⟨hPν, hmeanν, hklν, hpyν⟩ := responseProjection_spec hS ν hfin
  obtain ⟨hPF', hmeanF, hklF, -⟩ :=
    responseProjection_spec hS (faceMeasure ν {x | dirLoss S e x = β}) hfinF
  have hac : responseProjection hS (faceMeasure ν {x | dirLoss S e x = β}) M ≪
      faceMeasure ν {x | dirLoss S e x = β} :=
    (klDiv_ne_top_iff.1 (by rw [hklF]; exact hfinF)).1
  have hchain := klDiv_eq_klDiv_faceMeasure_add ν hF hp _ hac
  have hattain : klDiv (responseProjection hS (faceMeasure ν {x | dirLoss S e x = β}) M) ν =
      genRate ν S M := by
    rw [hchain, hklF, hface, add_comm]
  have h := hpyν _ hPF' hmeanF
  rw [hattain] at h
  have h0 : klDiv (responseProjection hS (faceMeasure ν {x | dirLoss S e x = β}) M)
      (responseProjection hS ν M) = 0 := by
    have h' : 0 + genRate ν S M =
        klDiv (responseProjection hS (faceMeasure ν {x | dirLoss S e x = β}) M)
          (responseProjection hS ν M) + genRate ν S M := by
      rw [zero_add]
      exact h
    exact ((ENNReal.add_left_inj hfin).1 h').symm
  exact (klDiv_eq_zero_iff.1 h0).symm

end Laplace.Multi
