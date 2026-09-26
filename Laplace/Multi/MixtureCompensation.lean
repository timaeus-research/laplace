/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MixtureBridge

/-!
# The mixture compensation identity and strict convexity of the rate

For probability laws `P₀, P₁ ≪ ν` and the mixture `Q = a P₀ + b P₁` (`a + b = 1`, `a, b > 0`)

  `a KL(P₀ ‖ ν) + b KL(P₁ ‖ ν) = KL(Q ‖ ν) + a KL(P₀ ‖ Q) + b KL(P₁ ‖ Q)`
                                                              (`klDiv_mixture_compensation`)

an identity in `ℝ≥0∞` with no integrability hypotheses: it is the pointwise identity
`a klFun f₀ + b klFun f₁ = klFun g + a g klFun (f₀/g) + b g klFun (f₁/g)` for the densities
(`klFun_mixture_identity`), integrated against `ν`. The right-hand side exhibits the convexity
defect of the divergence as a Jensen–Shannon-type quantity.

Applied to the response projections `Pᵢ = Π_ν(Mᵢ)`, whose mixture has response `a M₀ + b M₁`, and
combined with the exact information decomposition of the mixture, it yields the **gap identity** of
the rate

  `a 𝓘(M₀) + b 𝓘(M₁) = 𝓘(a M₀ + b M₁) + [a KL(P₀ ‖ Q) + b KL(P₁ ‖ Q) + KL(Q ‖ Π_ν(a M₀ + b M₁))]`
                                                              (`genRate_mixture_gap`)

valid for all finite-rate responses, boundary strata included, and hence **strict convexity of the
rate on its finite domain**: `𝓘(a M₀ + b M₁) < a 𝓘(M₀) + b 𝓘(M₁)` whenever `M₀ ≠ M₁`
(`genRate_mixture_lt`). The interior Hessian theorem (`hessian_rateFun_chart_pos`) gives strict
convexity only on the intrinsic interior; this is the global statement.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

section Pointwise

/-- The pointwise mixture identity for `klFun`: if `g = a f₀ + b f₁` with `a + b = 1` and
`fᵢ = hᵢ g`, then `a klFun f₀ + b klFun f₁ = klFun g + a g klFun h₀ + b g klFun h₁`. -/
theorem klFun_mixture_identity {a b f₀ f₁ g h₀ h₁ : ℝ} (hab : a + b = 1)
    (hg : g = a * f₀ + b * f₁) (h₀g : f₀ = h₀ * g) (h₁g : f₁ = h₁ * g) :
    a * klFun f₀ + b * klFun f₁ = klFun g + a * (g * klFun h₀) + b * (g * klFun h₁) := by
  have key : ∀ {f h : ℝ}, f = h * g → f * Real.log f = f * Real.log h + f * Real.log g := by
    intro f h hf
    by_cases hf0 : f = 0
    · simp [hf0]
    · have hh : h ≠ 0 := fun h0 ↦ hf0 (by rw [hf, h0, zero_mul])
      have hg0 : g ≠ 0 := fun h0 ↦ hf0 (by rw [hf, h0, mul_zero])
      rw [hf, Real.log_mul hh hg0]
      ring
  have e₀ := key h₀g
  have e₁ := key h₁g
  simp only [klFun_apply]
  linear_combination a * e₀ + b * e₁ - Real.log g * hg + (a * Real.log h₀ - a) * h₀g +
    (b * Real.log h₁ - b) * h₁g + (1 - g) * hab

/-- The pointwise mixture identity in `ℝ≥0∞`, for finite densities `f₀, f₁` and any `h₀, h₁`
with `hᵢ g = fᵢ`. -/
theorem ofReal_klFun_mixture_identity {a b : ℝ≥0} (hab : a + b = 1) {f₀ f₁ g h₀ h₁ : ℝ≥0∞}
    (hf₀ : f₀ ≠ ⊤) (hf₁ : f₁ ≠ ⊤) (hg : g = (a : ℝ≥0∞) * f₀ + (b : ℝ≥0∞) * f₁)
    (h₀g : h₀ * g = f₀) (h₁g : h₁ * g = f₁) :
    (a : ℝ≥0∞) * ENNReal.ofReal (klFun f₀.toReal) +
        (b : ℝ≥0∞) * ENNReal.ofReal (klFun f₁.toReal) =
      ENNReal.ofReal (klFun g.toReal) + (a : ℝ≥0∞) * (g * ENNReal.ofReal (klFun h₀.toReal)) +
        (b : ℝ≥0∞) * (g * ENNReal.ofReal (klFun h₁.toReal)) := by
  have hg' : g ≠ ⊤ := by
    rw [hg]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hf₀,
      ENNReal.mul_ne_top ENNReal.coe_ne_top hf₁⟩
  obtain ⟨F₀, hF₀, rfl⟩ : ∃ F : ℝ, 0 ≤ F ∧ f₀ = ENNReal.ofReal F :=
    ⟨f₀.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hf₀).symm⟩
  obtain ⟨F₁, hF₁, rfl⟩ : ∃ F : ℝ, 0 ≤ F ∧ f₁ = ENNReal.ofReal F :=
    ⟨f₁.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hf₁).symm⟩
  obtain ⟨G, hG, rfl⟩ : ∃ F : ℝ, 0 ≤ F ∧ g = ENNReal.ofReal F :=
    ⟨g.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hg').symm⟩
  have hab' : (a : ℝ) + b = 1 := by exact_mod_cast hab
  have hGr : G = (a : ℝ) * F₀ + (b : ℝ) * F₁ := by
    have := hg
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul a.coe_nonneg, ← ENNReal.ofReal_mul b.coe_nonneg,
      ← ENNReal.ofReal_add (mul_nonneg a.coe_nonneg hF₀) (mul_nonneg b.coe_nonneg hF₁)] at this
    exact (ENNReal.ofReal_eq_ofReal_iff hG
      (add_nonneg (mul_nonneg a.coe_nonneg hF₀) (mul_nonneg b.coe_nonneg hF₁))).1 this
  have h₀r : F₀ = h₀.toReal * G := by
    have := congrArg ENNReal.toReal h₀g
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hG, ENNReal.toReal_ofReal hF₀, eq_comm] at this
    exact this
  have h₁r : F₁ = h₁.toReal * G := by
    have := congrArg ENNReal.toReal h₁g
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hG, ENNReal.toReal_ofReal hF₁, eq_comm] at this
    exact this
  rw [ENNReal.toReal_ofReal hF₀, ENNReal.toReal_ofReal hF₁, ENNReal.toReal_ofReal hG]
  have hk₀ := klFun_nonneg (ENNReal.toReal_nonneg (a := h₀))
  have hk₁ := klFun_nonneg (ENNReal.toReal_nonneg (a := h₁))
  have L : (a : ℝ≥0∞) * ENNReal.ofReal (klFun F₀) + (b : ℝ≥0∞) * ENNReal.ofReal (klFun F₁) =
      ENNReal.ofReal ((a : ℝ) * klFun F₀ + (b : ℝ) * klFun F₁) := by
    rw [ENNReal.ofReal_add (mul_nonneg a.coe_nonneg (klFun_nonneg hF₀))
        (mul_nonneg b.coe_nonneg (klFun_nonneg hF₁)),
      ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  have R : ENNReal.ofReal (klFun G) +
        (a : ℝ≥0∞) * (ENNReal.ofReal G * ENNReal.ofReal (klFun h₀.toReal)) +
        (b : ℝ≥0∞) * (ENNReal.ofReal G * ENNReal.ofReal (klFun h₁.toReal)) =
      ENNReal.ofReal (klFun G + (a : ℝ) * (G * klFun h₀.toReal) +
        (b : ℝ) * (G * klFun h₁.toReal)) := by
    have n₀ := mul_nonneg a.coe_nonneg (mul_nonneg hG hk₀)
    have n₁ := mul_nonneg b.coe_nonneg (mul_nonneg hG hk₁)
    rw [ENNReal.ofReal_add (add_nonneg (klFun_nonneg hG) n₀) n₁,
      ENNReal.ofReal_add (klFun_nonneg hG) n₀,
      ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
      ENNReal.ofReal_mul hG, ENNReal.ofReal_mul hG,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  rw [L, R]
  congr 1
  exact klFun_mixture_identity hab' hGr h₀r h₁r

end Pointwise

section Compensation

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

/-- **The mixture compensation identity**: for `P₀, P₁ ≪ ν` and `Q = a P₀ + b P₁` with
`a + b = 1`, `a, b ≠ 0`,
`a KL(P₀ ‖ ν) + b KL(P₁ ‖ ν) = KL(Q ‖ ν) + a KL(P₀ ‖ Q) + b KL(P₁ ‖ Q)` in `ℝ≥0∞`. -/
theorem klDiv_mixture_compensation (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] [IsFiniteMeasure P₁]
    (h₀ : P₀ ≪ ν) (h₁ : P₁ ≪ ν) {a b : ℝ≥0} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a : ℝ≥0∞) * klDiv P₀ ν + (b : ℝ≥0∞) * klDiv P₁ ν =
      klDiv (a • P₀ + b • P₁) ν + (a : ℝ≥0∞) * klDiv P₀ (a • P₀ + b • P₁) +
        (b : ℝ≥0∞) * klDiv P₁ (a • P₀ + b • P₁) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Measure X, Q = a • P₀ + b • P₁ := ⟨_, rfl⟩
  have hQfin : IsFiniteMeasure Q := by rw [hQ]; infer_instance
  have hQν : Q ≪ ν := by rw [hQ]; exact mixture_absolutelyContinuous ν h₀ h₁ a b
  have hP₀Q : P₀ ≪ Q := by
    rw [hQ]
    exact (Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.2 ha)).trans
      (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))
  have hP₁Q : P₁ ≪ Q := by
    rw [hQ]
    exact (Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.2 hb)).trans
      (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))
  have hrn : Q.rnDeriv ν =ᵐ[ν]
      fun x ↦ (a : ℝ≥0∞) * P₀.rnDeriv ν x + (b : ℝ≥0∞) * P₁.rnDeriv ν x := by
    rw [hQ]
    filter_upwards [Measure.rnDeriv_add' (a • P₀) (b • P₁) ν, Measure.rnDeriv_smul_left' P₀ ν a,
      Measure.rnDeriv_smul_left' P₁ ν b] with x hx1 hx2 hx3
    rw [hx1, Pi.add_apply, hx2, hx3]
    rfl
  rw [← hQ, klDiv_eq_lintegral_klFun_of_ac h₀, klDiv_eq_lintegral_klFun_of_ac h₁,
    klDiv_eq_lintegral_klFun_of_ac hQν, klDiv_eq_lintegral_klFun_of_ac hP₀Q,
    klDiv_eq_lintegral_klFun_of_ac hP₁Q]
  have hwd : ∀ F : X → ℝ≥0∞, Measurable F → ∫⁻ x, F x ∂Q = ∫⁻ x, Q.rnDeriv ν x * F x ∂ν := by
    intro F hF
    have := lintegral_withDensity_eq_lintegral_mul ν (Measure.measurable_rnDeriv Q ν) hF
    rw [Measure.withDensity_rnDeriv_eq Q ν hQν] at this
    exact this
  have hm₀ : Measurable fun x ↦ ENNReal.ofReal (klFun (P₀.rnDeriv ν x).toReal) :=
    (by fun_prop : Measurable fun x ↦ klFun (P₀.rnDeriv ν x).toReal).ennreal_ofReal
  have hm₁ : Measurable fun x ↦ ENNReal.ofReal (klFun (P₁.rnDeriv ν x).toReal) :=
    (by fun_prop : Measurable fun x ↦ klFun (P₁.rnDeriv ν x).toReal).ennreal_ofReal
  have hmQ : Measurable fun x ↦ ENNReal.ofReal (klFun (Q.rnDeriv ν x).toReal) :=
    (by fun_prop : Measurable fun x ↦ klFun (Q.rnDeriv ν x).toReal).ennreal_ofReal
  have hk₀ : Measurable fun x ↦ ENNReal.ofReal (klFun (P₀.rnDeriv Q x).toReal) :=
    (by fun_prop : Measurable fun x ↦ klFun (P₀.rnDeriv Q x).toReal).ennreal_ofReal
  have hk₁ : Measurable fun x ↦ ENNReal.ofReal (klFun (P₁.rnDeriv Q x).toReal) :=
    (by fun_prop : Measurable fun x ↦ klFun (P₁.rnDeriv Q x).toReal).ennreal_ofReal
  have hg := Measure.measurable_rnDeriv Q ν
  have hgk₀ : Measurable fun x ↦ Q.rnDeriv ν x * ENNReal.ofReal (klFun (P₀.rnDeriv Q x).toReal) :=
    hg.mul hk₀
  have hgk₁ : Measurable fun x ↦ Q.rnDeriv ν x * ENNReal.ofReal (klFun (P₁.rnDeriv Q x).toReal) :=
    hg.mul hk₁
  have hm₀a : Measurable fun x ↦ (a : ℝ≥0∞) * ENNReal.ofReal (klFun (P₀.rnDeriv ν x).toReal) :=
    hm₀.const_mul _
  have hQa : Measurable fun x ↦ ENNReal.ofReal (klFun (Q.rnDeriv ν x).toReal) +
      (a : ℝ≥0∞) * (Q.rnDeriv ν x * ENNReal.ofReal (klFun (P₀.rnDeriv Q x).toReal)) :=
    hmQ.add (hgk₀.const_mul _)
  rw [hwd _ hk₀, hwd _ hk₁, ← lintegral_const_mul _ hm₀, ← lintegral_const_mul _ hm₁,
    ← lintegral_add_left hm₀a, ← lintegral_const_mul _ hgk₀,
    ← lintegral_const_mul _ hgk₁, ← lintegral_add_left hmQ, ← lintegral_add_left hQa]
  refine lintegral_congr_ae ?_
  filter_upwards [hrn, Measure.rnDeriv_mul_rnDeriv hP₀Q, Measure.rnDeriv_mul_rnDeriv hP₁Q,
    Measure.rnDeriv_ne_top P₀ ν, Measure.rnDeriv_ne_top P₁ ν] with x hgx hc₀ hc₁ ht₀ ht₁
  exact ofReal_klFun_mixture_identity hab ht₀ ht₁ hgx hc₀ hc₁

end Compensation

section Gap

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The gap identity for the rate**: for finite-rate responses `M₀, M₁`, with `Pᵢ = Π_ν(Mᵢ)`
and `Q = a P₀ + b P₁`,
`a 𝓘(M₀) + b 𝓘(M₁) = 𝓘(a M₀ + b M₁) + [a KL(P₀ ‖ Q) + b KL(P₁ ‖ Q) + KL(Q ‖ Π_ν(a M₀ + b M₁))]`. -/
theorem genRate_mixture_gap {M₀ M₁ : J → ℝ} (h₀ : genRate ν S M₀ ≠ ⊤) (h₁ : genRate ν S M₁ ≠ ⊤)
    {a b : ℝ≥0} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a : ℝ≥0∞) * genRate ν S M₀ + (b : ℝ≥0∞) * genRate ν S M₁ =
      genRate ν S ((a : ℝ) • M₀ + (b : ℝ) • M₁) +
        ((a : ℝ≥0∞) * klDiv (responseProjection hS ν M₀)
            (a • responseProjection hS ν M₀ + b • responseProjection hS ν M₁) +
          (b : ℝ≥0∞) * klDiv (responseProjection hS ν M₁)
            (a • responseProjection hS ν M₀ + b • responseProjection hS ν M₁) +
          klDiv (a • responseProjection hS ν M₀ + b • responseProjection hS ν M₁)
            (responseProjection hS ν ((a : ℝ) • M₀ + (b : ℝ) • M₁))) := by
  obtain ⟨hP₀, hM₀, hkl₀, -⟩ := responseProjection_spec hS ν h₀
  obtain ⟨hP₁, hM₁, hkl₁, -⟩ := responseProjection_spec hS ν h₁
  obtain ⟨P₀, hP₀e⟩ : ∃ P, P = responseProjection hS ν M₀ := ⟨_, rfl⟩
  obtain ⟨P₁, hP₁e⟩ : ∃ P, P = responseProjection hS ν M₁ := ⟨_, rfl⟩
  rw [← hP₀e] at hP₀ hM₀ hkl₀ ⊢
  rw [← hP₁e] at hP₁ hM₁ hkl₁ ⊢
  have hkl₀' : klDiv P₀ ν ≠ ⊤ := by rw [hkl₀]; exact h₀
  have hkl₁' : klDiv P₁ ν ≠ ⊤ := by rw [hkl₁]; exact h₁
  have hP₀ν : P₀ ≪ ν := (klDiv_ne_top_iff.1 hkl₀').1
  have hP₁ν : P₁ ≪ ν := (klDiv_ne_top_iff.1 hkl₁').1
  obtain ⟨Q, hQ⟩ : ∃ Q : Measure X, Q = a • P₀ + b • P₁ := ⟨_, rfl⟩
  have hQP : IsProbabilityMeasure Q := by rw [hQ]; exact isProbabilityMeasure_mixture P₀ P₁ hab
  have hQM : (fun i ↦ ∫ x, S i x ∂Q) = (a : ℝ) • M₀ + (b : ℝ) • M₁ := by
    rw [hQ, mean_mixture hS P₀ P₁ a b, hM₀, hM₁]
  have hcomp := klDiv_mixture_compensation ν P₀ P₁ hP₀ν hP₁ν hab ha hb
  rw [← hQ] at hcomp ⊢
  have hLfin : (a : ℝ≥0∞) * klDiv P₀ ν + (b : ℝ≥0∞) * klDiv P₁ ν ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hkl₀',
      ENNReal.mul_ne_top ENNReal.coe_ne_top hkl₁'⟩
  have hQkl : klDiv Q ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top hLfin ?_
    rw [hcomp]
    exact le_self_add.trans le_self_add
  have hfinQ : genRate ν S ((a : ℝ) • M₀ + (b : ℝ) • M₁) ≠ ⊤ := by
    rw [← hQM]
    exact fun h ↦ hQkl (klDiv_eq_top_of_genRate_eq_top hS ν Q h)
  obtain ⟨-, -, -, hpyth⟩ := responseProjection_spec hS ν hfinQ
  have hdec := hpyth Q hQP hQM
  rw [← hkl₀, ← hkl₁, hcomp, hdec]
  ring

/-- **Strict convexity of the rate on its finite domain**: `𝓘(a M₀ + b M₁) < a 𝓘(M₀) + b 𝓘(M₁)`
for distinct finite-rate responses `M₀ ≠ M₁` and `a + b = 1`, `a, b ≠ 0`. -/
theorem genRate_mixture_lt {M₀ M₁ : J → ℝ} (h₀ : genRate ν S M₀ ≠ ⊤) (h₁ : genRate ν S M₁ ≠ ⊤)
    (hne : M₀ ≠ M₁) {a b : ℝ≥0} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0) :
    genRate ν S ((a : ℝ) • M₀ + (b : ℝ) • M₁) <
      (a : ℝ≥0∞) * genRate ν S M₀ + (b : ℝ≥0∞) * genRate ν S M₁ := by
  have hgap := genRate_mixture_gap hS ν h₀ h₁ hab ha hb
  have hLfin : (a : ℝ≥0∞) * genRate ν S M₀ + (b : ℝ≥0∞) * genRate ν S M₁ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top h₀,
      ENNReal.mul_ne_top ENNReal.coe_ne_top h₁⟩
  have hfin : genRate ν S ((a : ℝ) • M₀ + (b : ℝ) • M₁) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hLfin ?_
    rw [hgap]
    exact le_self_add
  rw [hgap]
  refine ENNReal.lt_add_right hfin ?_
  intro hzero
  obtain ⟨hP₀, hM₀, -, -⟩ := responseProjection_spec hS ν h₀
  obtain ⟨hP₁, hM₁, -, -⟩ := responseProjection_spec hS ν h₁
  set P₀ := responseProjection hS ν M₀ with hP₀e
  set P₁ := responseProjection hS ν M₁ with hP₁e
  have hQP : IsProbabilityMeasure (a • P₀ + b • P₁) := isProbabilityMeasure_mixture P₀ P₁ hab
  have hz : (a : ℝ≥0∞) * klDiv P₀ (a • P₀ + b • P₁) = 0 :=
    ((add_eq_zero.1 (add_eq_zero.1 hzero).1).1)
  rcases mul_eq_zero.1 hz with hz | hz
  · exact ha (ENNReal.coe_eq_zero.1 hz)
  · have hPQ : P₀ = a • P₀ + b • P₁ := klDiv_eq_zero_iff.1 hz
    have hmean : M₀ = (a : ℝ) • M₀ + (b : ℝ) • M₁ := by
      rw [← hM₀, ← hM₁]
      conv_lhs => rw [hPQ]
      exact mean_mixture hS P₀ P₁ a b
    have hab' : (a : ℝ) + b = 1 := by exact_mod_cast hab
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    apply hne
    funext i
    have hi := congrFun hmean i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    have : (b : ℝ) * (M₁ i - M₀ i) = 0 := by linear_combination -hi - M₀ i * hab'
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hb'
    · linarith

end Gap

end Laplace.Multi
