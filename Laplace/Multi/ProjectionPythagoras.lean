/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PinskerObservable

/-!
# The reference-independent Pythagorean theorem of the response projection

The information decomposition `KL(D ‖ ν) = 𝓘(E_D S) + KL(D ‖ Π(E_D S))` is the Pythagorean theorem
of the projection onto the response fibre relative to the reference law `ν`. It holds relative to
every member of the family: for a data law `D` of finite information and every natural
coordinate `η`,

  `KL(D ‖ P_η) = KL(D ‖ Π(E_D S)) + KL(Π(E_D S) ‖ P_η)`   (`klDiv_familyMeasure_eq_add_projection`),

boundary responses of finite rate included. The projection is not merely the best approximation of
the data relative to `ν`; it is the information projection relative to the whole family. The proof
is the bounded-tilt identity `KL(R ‖ ν_f) = KL(R ‖ ν) − E_R f + log E_ν e^f` at `R = D` and
`R = Π(E_D S)`, whose means agree.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The bounded-tilt identity in real form, with the Donsker–Varadhan nonnegativity. -/
theorem toReal_klDiv_tilted_right (ρ : Measure X) [IsProbabilityMeasure ρ] (hρν : ρ ≪ ν)
    (hfin : klDiv ρ ν ≠ ⊤) {f : X → ℝ} (hf : Bdd f) :
    (klDiv ρ (ν.tilted f)).toReal =
      (klDiv ρ ν).toReal - ∫ x, f x ∂ρ + Real.log (∫ x, Real.exp (f x) ∂ν) := by
  rw [klDiv_tilted_right_eq ν ρ hρν hfin hf, ENNReal.toReal_ofReal]
  have := integral_sub_log_le_toReal_klDiv ν ρ hρν (klDiv_ne_top_iff.1 hfin).2 hf
  linarith

/-- **The Pythagorean theorem relative to every family member**:
`KL(D ‖ P_η) = KL(D ‖ Π(E_D S)) + KL(Π(E_D S) ‖ P_η)` for a data law of finite information. -/
theorem klDiv_familyMeasure_eq_add_projection (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) (η : J → ℝ) :
    klDiv D (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η) =
      klDiv D (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)) +
        klDiv (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D))
          (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hDν : D ≪ ν := (klDiv_ne_top_iff.1 hDkl).1
  have hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤ := fun h ↦
    hDkl (klDiv_eq_top_of_genRate_eq_top hS ν D h)
  obtain ⟨hP, hM, hkl, -⟩ := responseProjection_spec hS ν hfin
  have := hP
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D) := ⟨_, rfl⟩
  rw [← hQ] at hM hkl ⊢
  have hQP : IsProbabilityMeasure Q := by
    rw [hQ]
    exact hP
  have hQkl : klDiv Q ν ≠ ⊤ := by
    rw [hkl]
    exact hfin
  have hQν : Q ≪ ν := (klDiv_ne_top_iff.1 hQkl).1
  have hdec := information_decomposition hS ν D hfin
  rw [← hQ, ← hkl] at hdec
  have hDQ : klDiv D Q ≠ ⊤ := by
    intro h
    rw [h, add_top] at hdec
    exact hDkl hdec
  -- the family member as a tilt
  obtain ⟨f, hf⟩ : ∃ f : X → ℝ, f = fun x ↦ -(1 : ℝ) * dirLoss S η x := ⟨_, rfl⟩
  have hbdd : Bdd f := hf ▸ Bdd.const_mul (-1) (bdd_dirLoss hS η)
  have hfam : familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η = ν.tilted f := by
    rw [hf, familyMeasure_eq_tilted measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const h0 hS one_pos η, familyMeasure_one_zero]
  rw [hfam]
  -- equal means of `f` under `D` and `Q`
  have hmean : ∫ x, f x ∂D = ∫ x, f x ∂Q := by
    rw [hf, integral_const_mul, integral_const_mul, ← dotJ_integral_eq D hS η,
      ← dotJ_integral_eq Q hS η, hM]
  have h1 := toReal_klDiv_tilted_right ν D hDν hDkl hbdd
  have h2 := toReal_klDiv_tilted_right ν Q hQν hQkl hbdd
  have hfin1 : klDiv D (ν.tilted f) ≠ ⊤ := by
    rw [klDiv_tilted_right_eq ν D hDν hDkl hbdd]
    exact ENNReal.ofReal_ne_top
  have hfin2 : klDiv Q (ν.tilted f) ≠ ⊤ := by
    rw [klDiv_tilted_right_eq ν Q hQν hQkl hbdd]
    exact ENNReal.ofReal_ne_top
  have hdec' := congrArg ENNReal.toReal hdec
  rw [ENNReal.toReal_add hQkl hDQ] at hdec'
  rw [← ENNReal.toReal_eq_toReal_iff' hfin1 (ENNReal.add_ne_top.2 ⟨hDQ, hfin2⟩),
    ENNReal.toReal_add hDQ hfin2, h1, h2, hmean]
  linarith

end Laplace.Multi
