/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.DataResponseMap
import Laplace.Multi.IntrinsicChart

/-!
# The conditioning certificate

The completion principle is made explicit. An **exposed chain** for a response `M`
(`ExposedChain ν S M A n`) is a nested sequence of `n` events, each the positive-mass face of a
supporting functional of the *current conditional* moment body, proper for that body, with `M` on
its hyperplane; `A` is the terminal event. Along a chain:

* the events are measurable and of positive mass (`ExposedChain.measurableSet`, `ExposedChain.pos`);
* the affine dimension of the moment body drops at least by one per step:
  `n + dim 𝕍_{ν_A} ≤ dim 𝕍_ν` (`ExposedChain.finrank_add_le`), so chains have length at most
  `dim 𝕍_ν`;
* the entry costs telescope to the mass of the terminal event:
  `𝓘_ν(M) = −log ν(A) + 𝓘_{ν_A}(M)` (`ExposedChain.genRate_eq`), through the conditioning
  associativity `(ν_A)_B = ν_{A ∩ B}` (`faceMeasure_faceMeasure`).

**Every finite-rate response has a chain whose terminal conditional body contains it in the
relative interior** (`exists_exposedChain`), and the response projection is then the intrinsic tilt
of the terminal conditioned law (`responseProjection_eq_of_exposedChain`): the minimiser is a
bounded exponential tilt of a law obtained from `ν` by at most `dim 𝕍_ν` positive-mass exposed
conditionings.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]

section FaceAlgebra

variable (ν : Measure X) [IsProbabilityMeasure ν]

omit [Fintype J] in
theorem faceMeasure_univ : faceMeasure ν Set.univ = ν := by
  unfold faceMeasure
  rw [measure_univ, inv_one, one_smul, Measure.restrict_univ]

omit [Fintype J] [IsProbabilityMeasure ν] in
theorem faceMeasure_apply {A : Set X} (hA : MeasurableSet A) (B : Set X) :
    faceMeasure ν A B = (ν A)⁻¹ * ν (B ∩ A) := by
  unfold faceMeasure
  rw [Measure.smul_apply, Measure.restrict_apply' hA, smul_eq_mul]

omit [Fintype J] [IsProbabilityMeasure ν] in
theorem faceMeasure_real_apply {A : Set X} (hA : MeasurableSet A) (B : Set X) :
    (faceMeasure ν A).real B = ν.real (B ∩ A) / ν.real A := by
  rw [measureReal_def, faceMeasure_apply ν hA, ENNReal.toReal_mul, ENNReal.toReal_inv,
    measureReal_def, measureReal_def, div_eq_inv_mul]

omit [Fintype J] in
/-- **Conditioning associativity**: `(ν_A)_B = ν_{A ∩ B}`. -/
theorem faceMeasure_faceMeasure {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : ν A ≠ 0) :
    faceMeasure (faceMeasure ν A) B = faceMeasure ν (A ∩ B) := by
  have hAt : ν A ≠ ⊤ := measure_ne_top _ _
  unfold faceMeasure
  rw [Measure.restrict_smul, Measure.restrict_restrict hB, Measure.smul_apply,
    Measure.restrict_apply' hA, smul_eq_mul, smul_smul, Set.inter_comm B A]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hAt)) (Or.inl (ENNReal.inv_ne_top.2 hA0)),
    inv_inv, mul_right_comm, ENNReal.mul_inv_cancel hA0 hAt, one_mul]

omit [Fintype J] in
theorem faceMeasure_real_le_one {A : Set X} (B : Set X) (hA0 : ν A ≠ 0) :
    (faceMeasure ν A).real B ≤ 1 := by
  have := isProbabilityMeasure_faceMeasure ν hA0
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

end FaceAlgebra

/-- **An exposed chain** for the response `M`: nested events, each the positive-mass face of a
supporting functional of the current conditional moment body, proper for that body, with `M` on
its hyperplane. -/
inductive ExposedChain (ν : Measure X) (S : J → X → ℝ) (M : J → ℝ) : Set X → ℕ → Prop
  | root : ExposedChain ν S M Set.univ 0
  | step {A : Set X} {n : ℕ} (hA : ExposedChain ν S M A n) (e : J → ℝ) (β : ℝ)
      (hβ : ∀ᵐ x ∂faceMeasure ν A, dirLoss S e x ≤ β)
      (hproper : ∃ y ∈ momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S, dotJ e y ≠ β)
      (hpos : 0 < (faceMeasure ν A).real {x | dirLoss S e x = β}) (hM : dotJ e M = β) :
      ExposedChain ν S M (A ∩ {x | dirLoss S e x = β}) (n + 1)

section Chain

variable [Nonempty X] [Nonempty J] {ν : Measure X} [IsProbabilityMeasure ν] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) {M : J → ℝ}
include hS

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] hS in
theorem ExposedChain.castSet {A B : Set X} {n : ℕ} (h : ExposedChain ν S M A n) (hAB : A = B) :
    ExposedChain ν S M B n := hAB ▸ h

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem ExposedChain.measurableSet {A : Set X} {n : ℕ} (h : ExposedChain ν S M A n) :
    MeasurableSet A := by
  induction h with
  | root => exact MeasurableSet.univ
  | @step _ _ _ e β _ _ _ _ ih =>
    exact ih.inter (measurableSet_eq_fun (bdd_dirLoss hS e).1 measurable_const)

omit [Nonempty X] [Nonempty J] in
theorem ExposedChain.pos {A : Set X} {n : ℕ} (h : ExposedChain ν S M A n) : 0 < ν.real A := by
  induction h with
  | root => simp
  | @step A _ hA e β _ _ hpos _ ih =>
    rw [faceMeasure_real_apply ν (hA.measurableSet hS), Set.inter_comm] at hpos
    exact (div_pos_iff_of_pos_right ih).1 hpos

omit [Nonempty J] in
/-- **The affine dimension drops at least by one per step.** -/
theorem ExposedChain.finrank_add_le {A : Set X} {n : ℕ} (h : ExposedChain ν S M A n) :
    n + Module.finrank ℝ (dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) ≤
      Module.finrank ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S) := by
  induction h with
  | root =>
    rw [faceMeasure_univ]
    simp
  | @step A n hA e β hβ hproper hpos hM ih =>
    have hA0 : ν A ≠ 0 := (ENNReal.toReal_pos_iff.1 (hA.pos hS)).1.ne'
    have hPA := isProbabilityMeasure_faceMeasure ν hA0
    obtain ⟨y₁, hy₁, hne⟩ := hproper
    have hFm : MeasurableSet {x | dirLoss S e x = β} :=
      measurableSet_eq_fun (bdd_dirLoss hS e).1 measurable_const
    have hF0 : faceMeasure ν A {x | dirLoss S e x = β} ≠ 0 :=
      (ENNReal.toReal_pos_iff.1 hpos).1.ne'
    have hPF := isProbabilityMeasure_faceMeasure (faceMeasure ν A) hF0
    have hy₀ := mean_mem_momentBody_general hS (faceMeasure (faceMeasure ν A)
      {x | dirLoss S e x = β})
    have hy₀K := momentBody_faceMeasure_subset (faceMeasure ν A) hFm hS hpos hy₀
    have hy₀β : dotJ e (fun i ↦ ∫ x, S i x ∂faceMeasure (faceMeasure ν A)
        {x | dirLoss S e x = β}) = β :=
      momentBody_faceMeasure_subset_hyperplane (faceMeasure ν A) hFm hS hpos rfl hy₀
    have hlt := finrank_dirSpan_faceMeasure_lt (faceMeasure ν A) hFm hS hpos rfl hy₀K hy₁
      (by rw [hy₀β]; exact hne.symm)
    rw [faceMeasure_faceMeasure ν (hA.measurableSet hS) hFm hA0] at hlt
    omega

omit [Nonempty X] [Nonempty J] hS in
theorem prob_real_le_one (ν : Measure X) [IsProbabilityMeasure ν] (A : Set X) : ν.real A ≤ 1 := by
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

omit [Nonempty X] [Nonempty J] in
/-- **The entry costs telescope to the mass of the terminal event**:
`𝓘_ν(M) = −log ν(A) + 𝓘_{ν_A}(M)` along a chain. -/
theorem ExposedChain.genRate_eq {A : Set X} {n : ℕ} (h : ExposedChain ν S M A n) :
    genRate ν S M = ENNReal.ofReal (-Real.log (ν.real A)) + genRate (faceMeasure ν A) S M := by
  induction h with
  | root =>
    rw [faceMeasure_univ]
    simp
  | @step A n hA e β hβ hproper hpos hM ih =>
    have hA0 : ν A ≠ 0 := (ENNReal.toReal_pos_iff.1 (hA.pos hS)).1.ne'
    have hPA := isProbabilityMeasure_faceMeasure ν hA0
    have hFm : MeasurableSet {x | dirLoss S e x = β} :=
      measurableSet_eq_fun (bdd_dirLoss hS e).1 measurable_const
    have hAB : 0 < ν.real (A ∩ {x | dirLoss S e x = β}) :=
      (ExposedChain.step hA e β hβ hproper hpos hM).pos hS
    have hface := genRate_face_eq (faceMeasure ν A) hS hβ hpos hM
    rw [faceMeasure_faceMeasure ν (hA.measurableSet hS) hFm hA0] at hface
    rw [ih, hface, ← add_assoc]
    congr 1
    have h1 : 0 ≤ -Real.log (ν.real A) :=
      neg_nonneg.2 (Real.log_nonpos (hA.pos hS).le (prob_real_le_one ν A))
    have h2 : 0 ≤ -Real.log ((faceMeasure ν A).real {x | dirLoss S e x = β}) :=
      neg_nonneg.2 (Real.log_nonpos hpos.le (faceMeasure_real_le_one ν _ hA0))
    rw [← ENNReal.ofReal_add h1 h2]
    congr 1
    rw [faceMeasure_real_apply ν (hA.measurableSet hS), Set.inter_comm,
      Real.log_div hAB.ne' (hA.pos hS).ne']
    ring

omit [Nonempty X] [Nonempty J] in
/-- **Prefixing a chain of the conditioned law by its first face.** -/
theorem ExposedChain.prefix {F : Set X} {e : J → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss S e x ≤ β)
    (hproper : ∃ y ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, dotJ e y ≠ β)
    (hpos : 0 < ν.real {x | dirLoss S e x = β}) (hM : dotJ e M = β)
    (hF : F = {x | dirLoss S e x = β}) {A : Set X} {n : ℕ}
    (h : ExposedChain (faceMeasure ν F) S M A n) : ExposedChain ν S M (F ∩ A) (n + 1) := by
  have hF0 : ν F ≠ 0 := by
    rw [hF]
    exact (ENNReal.toReal_pos_iff.1 hpos).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  have hFm : MeasurableSet F := by
    rw [hF]
    exact measurableSet_eq_fun (bdd_dirLoss hS e).1 measurable_const
  induction h with
  | root =>
    have h1 : ExposedChain ν S M (Set.univ ∩ {x | dirLoss S e x = β}) (0 + 1) :=
      ExposedChain.step ExposedChain.root e β (by rw [faceMeasure_univ]; exact hβ)
        (by rw [faceMeasure_univ]; exact hproper) (by rw [faceMeasure_univ]; exact hpos) hM
    exact ExposedChain.castSet h1 (by rw [hF, Set.univ_inter, Set.inter_univ])
  | @step A' n' hA e' β' hβ' hproper' hpos' hM' ih =>
    have hassoc := faceMeasure_faceMeasure ν hFm (hA.measurableSet hS) hF0
    rw [hassoc] at hβ' hproper' hpos'
    exact ExposedChain.castSet (ExposedChain.step ih e' β' hβ' hproper' hpos' hM')
      (Set.inter_assoc _ _ _)

/-- **Every finite-rate response has an exposed chain whose terminal conditional body contains it
in the relative interior.** -/
theorem exists_exposedChain (ν : Measure X) [IsProbabilityMeasure ν] (hfin : genRate ν S M ≠ ⊤) :
    ∃ (A : Set X) (n : ℕ), ExposedChain ν S M A n ∧
      M ∈ intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) := by
  suffices H : ∀ k : ℕ, ∀ (ν : Measure X) [IsProbabilityMeasure ν],
      Module.finrank ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S) = k → genRate ν S M ≠ ⊤ →
        ∃ (A : Set X) (n : ℕ), ExposedChain ν S M A n ∧
          M ∈ intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) from
    H _ ν rfl hfin
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ν _ hk hfin
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hπpos : (0 : ℝ) < ∫ x, (fun _ : X ↦ (1 : ℝ)) x ∂ν := by simp
  have hπi : Integrable (fun _ : X ↦ (1 : ℝ)) ν := integrable_const _
  have hπ : ∀ x, (0 : ℝ) < (fun _ : X ↦ (1 : ℝ)) x := fun _ ↦ one_pos
  have hMK : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
    by_contra h
    refine hfin ?_
    rw [genRate_eq_rateFun ν S M]
    exact rateFun_eq_top_of_not_mem measurable_const hπi hπ hπpos measurable_const h0 hS (t := 1) h
  by_cases hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)
  · exact ⟨Set.univ, 0, ExposedChain.root, by rw [faceMeasure_univ]; exact hrel⟩
  · rw [mem_intrinsicInterior_iff_forall_supporting (convex_momentBody S)] at hrel
    push Not at hrel
    obtain ⟨e, he, y₁, hy₁, hne⟩ := hrel hMK
    obtain ⟨F, hFdef⟩ : ∃ F : Set X, F = {x | dirLoss S e x = dotJ e M} := ⟨_, rfl⟩
    have hF : MeasurableSet F := by
      rw [hFdef]
      exact measurableSet_eq_fun (bdd_dirLoss hS e).1 measurable_const
    have hβ : ∀ᵐ x ∂ν, dirLoss S e x ≤ dotJ e M := by
      filter_upwards [ae_statPoint_mem_essRange (μ := ν) measurable_const hπ hS] with x hx
      exact he _ (essRange_subset_momentBody S hx)
    have hF0 : ν F ≠ 0 := by
      intro h0'
      refine hfin (genRate_eq_top_of_null_face ν hS hβ ?_ rfl)
      rw [← hFdef]
      exact h0'
    have hp' : 0 < ν.real {x | dirLoss S e x = dotJ e M} := by
      rw [← hFdef]
      exact ENNReal.toReal_pos hF0 (measure_ne_top _ _)
    have hp : 0 < ν.real F := by
      rw [hFdef]
      exact hp'
    have hface := genRate_face_eq ν hS hβ hp' rfl
    rw [← hFdef] at hface
    have hPF := isProbabilityMeasure_faceMeasure ν hF0
    have hfinF : genRate (faceMeasure ν F) S M ≠ ⊤ := by
      intro h
      rw [h, add_top] at hface
      exact hfin hface
    have hlt := finrank_dirSpan_faceMeasure_lt ν hF hS hp hFdef hy₁ hMK hne
    rw [hk] at hlt
    obtain ⟨A', n', hchain, hrel'⟩ := ih _ hlt (faceMeasure ν F) rfl hfinF
    refine ⟨F ∩ A', n' + 1,
      ExposedChain.prefix hS hβ ⟨y₁, hy₁, hne⟩ hp' rfl hFdef hchain, ?_⟩
    rw [← faceMeasure_faceMeasure ν hF (hchain.measurableSet hS) hF0]
    exact hrel'

/-- **The response projection is the intrinsic tilt of the terminal conditioned law.** -/
theorem responseProjection_eq_of_exposedChain (ν : Measure X) [IsProbabilityMeasure ν]
    {A : Set X} {n : ℕ} (h : ExposedChain ν S M A n)
    (hrel : M ∈ intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S)) :
    ∃ θ ∈ dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S,
      responseProjection hS ν M =
        familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := by
  have hA0 : ν A ≠ 0 := (ENNReal.toReal_pos_iff.1 (h.pos hS)).1.ne'
  have hPA := isProbabilityMeasure_faceMeasure ν hA0
  have hAm := h.measurableSet hS
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hπpos : (0 : ℝ) < ∫ x, (fun _ : X ↦ (1 : ℝ)) x ∂faceMeasure ν A := by simp
  have hπi : Integrable (fun _ : X ↦ (1 : ℝ)) (faceMeasure ν A) := integrable_const _
  have hπ : ∀ x, (0 : ℝ) < (fun _ : X ↦ (1 : ℝ)) x := fun _ ↦ one_pos
  obtain ⟨θ, hθV, hmin⟩ := exists_min_variational_rel measurable_const hπi hπ hπpos hS hrel
  have hθ := meanMap_eq_of_min_rel measurable_const hπi hπ hπpos hS (intrinsicInterior_subset hrel)
    hθV hmin
  refine ⟨θ, hθV, ?_⟩
  -- the tilt of the conditioned law attains the rate of `ν`
  have hQ := familyMeasure_one_zero (faceMeasure ν A) S
  have hP := isProbabilityMeasure_familyMeasure measurable_const hπi hπ hπpos measurable_const h0
    hS (t := 1) θ
  have hmean : (fun i ↦ ∫ x, S i x ∂familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 θ) = M := by
    rw [← hθ]
    exact funext fun i ↦
      integral_familyMeasure measurable_const hπi hπ hπpos measurable_const h0 hS θ (S i)
  have hkl0 := klDiv_familyMeasure_zero measurable_const hπi hπ hπpos measurable_const h0 hS
    one_pos θ
  rw [hQ] at hkl0
  have hklA : klDiv (familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)
      (faceMeasure ν A) = genRate (faceMeasure ν A) S M := by
    rw [hkl0, genRate_eq_rateFun, ← hθ,
      rateFun_meanMap measurable_const hπi hπ hπpos measurable_const h0 hS one_pos θ]
  have hfinA : genRate (faceMeasure ν A) S M ≠ ⊤ := by
    rw [← hklA, hkl0]
    exact ENNReal.ofReal_ne_top
  have hcost := h.genRate_eq hS
  have hfin : genRate ν S M ≠ ⊤ := by
    rw [hcost]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hfinA⟩
  have hac : familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ ≪
      faceMeasure ν A := withDensity_absolutelyContinuous _ _
  have hchain := klDiv_eq_klDiv_faceMeasure_add ν hAm (h.pos hS) _ hac
  have hattain : klDiv (familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)
      ν = genRate ν S M := by
    rw [hchain, hklA, hcost, add_comm]
  obtain ⟨-, -, -, hpy⟩ := responseProjection_spec hS ν hfin
  have hp := hpy _ hP hmean
  rw [hattain] at hp
  have hz : klDiv (familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)
      (responseProjection hS ν M) = 0 := by
    have h' : 0 + genRate ν S M =
        klDiv (familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)
          (responseProjection hS ν M) + genRate ν S M := by
      rw [zero_add]
      exact hp
    exact ((ENNReal.add_left_inj hfin).1 h').symm
  have := (responseProjection_spec hS ν hfin).1
  exact (klDiv_eq_zero_iff.1 hz).symm

end Chain

end Laplace.Multi
