/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ResidualInformation
import Laplace.Multi.ConditioningCertificate

/-!
# The residual split for every finite-rate response

The residual split `KL(D ‖ P) = KL(D ‖ D↑) + KL(S_*D ‖ S_*P)` holds for every probability law
`P = ν.withDensity (g ∘ S)` whose density is a (possibly unbounded) function of the statistic, for
data laws of finite information (`klDiv_withDensity_comp_eq_statisticLift_add_map`): if the marginal
term is infinite so is the left side by data processing, and otherwise the log-likelihood ratios
split `D`-almost everywhere exactly as in the base case.

The response projection of **every** finite-rate response is such a law: by the exposed-chain
description it is a tilt of a positive-mass conditioning `ν(· | A)` with `A = S⁻¹(B)`
(`ExposedChain.exists_preimage`), hence `Π_ν(M) = ν.withDensity (g ∘ S)` with
`g = 1_B e^{−⟨θ,·⟩} / (ν(A) Z)` (`responseProjection_eq_withDensity_comp`). Therefore, with no
interiority hypothesis,

  `KL(D ‖ Π_ν(M_D)) = KL(D ‖ D↑) + KL(S_*D ‖ S_*Π_ν(M_D))`
                                     (`klDiv_responseProjection_eq_statisticLift_add_map'`)

for every data law of finite information: the invisible information of the atlas is the fibre
information plus the marginal information, on the boundary strata as well.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section General

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν D : Measure X)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : X → Y) (hS : Measurable S) (hD : D ≪ ν)
include hS hD

/-- **The residual split for densities that are functions of the statistic**: for a probability
law `P = ν.withDensity (g ∘ S)` and `KL(D ‖ ν) < ∞`,
`KL(D ‖ P) = KL(D ‖ D↑) + KL(S_*D ‖ S_*P)`. -/
theorem klDiv_withDensity_comp_eq_statisticLift_add_map {g : Y → ℝ≥0∞} (hg : Measurable g)
    (hP : IsProbabilityMeasure (ν.withDensity fun x ↦ g (S x))) (hfin : klDiv D ν ≠ ⊤) :
    klDiv D (ν.withDensity fun x ↦ g (S x)) =
      klDiv D (statisticLift ν D S) + klDiv (D.map S) ((ν.withDensity fun x ↦ g (S x)).map S) := by
  have hgS : Measurable fun x ↦ g (S x) := hg.comp hS
  rw [map_withDensity_comp ν S hS hg]
  have hlm : D.map S ≪ ν.map S := map_absolutelyContinuous ν D S hS hD
  have hmapfin : klDiv (D.map S) (ν.map S) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (klDiv_map_le (μ := D) (ν := ν) hS)
  have hPlam : IsProbabilityMeasure (D.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hPmu : IsProbabilityMeasure (ν.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hPL := isProbabilityMeasure_statisticLift ν D S hS hD
  have hPμg : IsProbabilityMeasure ((ν.map S).withDensity g) := by
    rw [← map_withDensity_comp ν S hS hg]
    exact Measure.isProbabilityMeasure_map hS.aemeasurable
  by_cases hfinP : klDiv (D.map S) ((ν.map S).withDensity g) = ⊤
  · rw [hfinP, add_top]
    refine top_le_iff.1 ?_
    rw [← hfinP, ← map_withDensity_comp ν S hS hg]
    exact klDiv_map_le (μ := D) (ν := ν.withDensity fun x ↦ g (S x)) hS
  obtain ⟨hlP, hintlP⟩ := klDiv_ne_top_iff.1 hfinP
  obtain ⟨-, hint⟩ := klDiv_ne_top_iff.1 hfin
  have hintY : Integrable (llr (D.map S) (ν.map S)) (D.map S) := (klDiv_ne_top_iff.1 hmapfin).2
  -- `g` vanishes only on a `D`-null set, and is finite almost everywhere
  have hg0 : D {x | g (S x) = 0} = 0 := by
    have hB : MeasurableSet {y | g y = 0} := measurableSet_eq_fun hg measurable_const
    have e : {x | g (S x) = 0} = S ⁻¹' {y | g y = 0} := rfl
    have key : ((ν.map S).withDensity g) {y | g y = 0} = 0 := by
      rw [withDensity_apply _ hB, setLIntegral_congr_fun (g := fun _ ↦ 0) hB (fun y hy ↦ hy)]
      exact lintegral_zero
    rw [e, ← Measure.map_apply hS hB]
    exact hlP key
  have hgtop_ν : ∀ᵐ x ∂ν, g (S x) ≠ ⊤ := by
    have h1 : ∫⁻ x, g (S x) ∂ν ≠ ⊤ := by
      have := hP.measure_univ
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
      rw [this]
      exact ENNReal.one_ne_top
    filter_upwards [ae_lt_top hgS h1] with x hx
    exact hx.ne
  have hgtop_μ : ∀ᵐ y ∂ν.map S, g y ≠ ⊤ := by
    have h1 : ∫⁻ y, g y ∂ν.map S ≠ ⊤ := by
      have := hPμg.measure_univ
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
      rw [this]
      exact ENNReal.one_ne_top
    filter_upwards [ae_lt_top hg h1] with y hy
    exact hy.ne
  -- `D ≪ P`
  have hDP : D ≪ ν.withDensity fun x ↦ g (S x) := by
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 ↦ ?_
    rw [withDensity_apply_eq_zero hgS] at h0
    have h1 : D ({x | g (S x) ≠ 0} ∩ A) = 0 := hD h0
    refine le_antisymm ?_ zero_le
    calc D A ≤ D (({x | g (S x) ≠ 0} ∩ A) ∪ {x | g (S x) = 0}) := by
          refine measure_mono fun x hx ↦ ?_
          by_cases h : g (S x) = 0
          · exact Or.inr h
          · exact Or.inl ⟨h, hx⟩
      _ ≤ D ({x | g (S x) ≠ 0} ∩ A) + D {x | g (S x) = 0} := measure_union_le _ _
      _ = 0 := by rw [h1, hg0, add_zero]
  -- the log-likelihood ratios split almost everywhere
  have haeX : llr D (ν.withDensity fun x ↦ g (S x)) =ᵐ[D]
      fun x ↦ llr D ν x - Real.log (g (S x)).toReal := by
    have hchain := Measure.rnDeriv_mul_rnDeriv (κ := ν) hDP
    have hdens : (ν.withDensity fun x ↦ g (S x)).rnDeriv ν =ᵐ[ν] fun x ↦ g (S x) :=
      Measure.rnDeriv_withDensity ν hgS
    have hpos := Measure.rnDeriv_pos hDP
    have hr_ne : ∀ᵐ x ∂D, g (S x) ≠ 0 := by
      rw [ae_iff]
      simpa using hg0
    have hLtop := hDP.ae_le (Measure.rnDeriv_ne_top D (ν.withDensity fun x ↦ g (S x)))
    filter_upwards [hD.ae_le hchain, hD.ae_le hdens, hpos, hr_ne, hD.ae_le hgtop_ν, hLtop]
      with x hc hd hp hr0 hrt hlt
    rw [Pi.mul_apply, hd] at hc
    simp only [llr]
    rw [← hc, ENNReal.toReal_mul,
      Real.log_mul (ENNReal.toReal_pos hp.ne' hlt).ne' (ENNReal.toReal_pos hr0 hrt).ne']
    ring
  have haeY : llr (D.map S) ((ν.map S).withDensity g) =ᵐ[D.map S]
      fun y ↦ llr (D.map S) (ν.map S) y - Real.log (g y).toReal := by
    have hchain := Measure.rnDeriv_mul_rnDeriv (κ := ν.map S) hlP
    have hdens : ((ν.map S).withDensity g).rnDeriv (ν.map S) =ᵐ[ν.map S] g :=
      Measure.rnDeriv_withDensity (ν.map S) hg
    have hpos := Measure.rnDeriv_pos hlP
    have hg0' : D.map S {y | g y = 0} = 0 := by
      rw [Measure.map_apply hS (measurableSet_eq_fun hg measurable_const)]
      exact hg0
    have hr_ne : ∀ᵐ y ∂D.map S, g y ≠ 0 := by
      rw [ae_iff]
      simpa using hg0'
    have hLtop := hlP.ae_le (Measure.rnDeriv_ne_top (D.map S) ((ν.map S).withDensity g))
    filter_upwards [hlm.ae_le hchain, hlm.ae_le hdens, hpos, hr_ne, hlm.ae_le hgtop_μ, hLtop]
      with y hc hd hp hr0 hrt hlt
    rw [Pi.mul_apply, hd] at hc
    simp only [llr]
    rw [← hc, ENNReal.toReal_mul,
      Real.log_mul (ENNReal.toReal_pos hp.ne' hlt).ne' (ENNReal.toReal_pos hr0 hrt).ne']
    ring
  -- integrability of the log-density
  have hlogY : Integrable (fun y ↦ Real.log (g y).toReal) (D.map S) := by
    have := hintY.sub hintlP
    refine this.congr ?_
    filter_upwards [haeY] with y hy
    simp only [Pi.sub_apply]
    rw [hy]
    ring
  have hlogX : Integrable (fun x ↦ Real.log (g (S x)).toReal) D :=
    (integrable_map_measure hlogY.aestronglyMeasurable hS.aemeasurable).1 hlogY
  have hintP : Integrable (llr D (ν.withDensity fun x ↦ g (S x))) D :=
    (hint.sub hlogX).congr haeX.symm
  -- the real identities
  have hbase := klDiv_eq_klDiv_statisticLift_add_map ν D S hS hD hfin
  have hfinL : klDiv D (statisticLift ν D S) ≠ ⊤ := by
    intro h
    rw [h, top_add] at hbase
    exact hfin hbase
  have hDL := absolutelyContinuous_statisticLift ν D S hS hD
  have hintL : Integrable (llr D (statisticLift ν D S)) D := (klDiv_ne_top_iff.1 hfinL).2
  have hc : (klDiv D ν).toReal = ∫ x, llr D ν x ∂D := by
    rw [toReal_klDiv hD hint, probReal_univ, probReal_univ, add_sub_cancel_right]
  have ha : (klDiv D (statisticLift ν D S)).toReal = ∫ x, llr D (statisticLift ν D S) x ∂D := by
    rw [toReal_klDiv hDL hintL, probReal_univ, probReal_univ, add_sub_cancel_right]
  have hb : (klDiv (D.map S) (ν.map S)).toReal =
      ∫ y, llr (D.map S) (ν.map S) y ∂D.map S := by
    rw [toReal_klDiv hlm hintY, probReal_univ, probReal_univ, add_sub_cancel_right]
  have hbase' : ∫ x, llr D ν x ∂D = (∫ x, llr D (statisticLift ν D S) x ∂D) +
      ∫ y, llr (D.map S) (ν.map S) y ∂D.map S := by
    rw [← hc, ← ha, ← hb, hbase, ENNReal.toReal_add hfinL hmapfin]
  have hsum : ∫ x, llr D (ν.withDensity fun x ↦ g (S x)) x ∂D =
      (∫ x, llr D (statisticLift ν D S) x ∂D) +
        ∫ y, llr (D.map S) ((ν.map S).withDensity g) y ∂D.map S := by
    rw [integral_congr_ae haeX, integral_sub hint hlogX, hbase', integral_congr_ae haeY,
      integral_sub hintY hlogY, integral_map hS.aemeasurable hlogY.aestronglyMeasurable]
    ring
  rw [klDiv_of_ac_of_integrable hDP hintP, klDiv_of_ac_of_integrable hDL hintL,
    klDiv_of_ac_of_integrable hlP hintlP]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [hsum, ENNReal.ofReal_add ?_ ?_]
  · rw [← ha]
    exact ENNReal.toReal_nonneg
  · have := toReal_klDiv hlP hintlP
    rw [probReal_univ, probReal_univ, add_sub_cancel_right] at this
    rw [← this]
    exact ENNReal.toReal_nonneg

end General

section Boundary

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The sets of an exposed chain are preimages of measurable sets of responses. -/
theorem ExposedChain.exists_preimage {M : J → ℝ} {A : Set X} {n : ℕ}
    (h : ExposedChain ν S M A n) : ∃ B : Set (J → ℝ), MeasurableSet B ∧ A = statPoint S ⁻¹' B := by
  induction h with
  | root => exact ⟨Set.univ, MeasurableSet.univ, by simp⟩
  | @step A n hA e β _ _ _ _ ih =>
    obtain ⟨B, hB, hAB⟩ := ih
    refine ⟨B ∩ {y | dotJ e y = β},
      hB.inter (measurableSet_eq_fun (continuous_dotJ_right e).measurable measurable_const), ?_⟩
    rw [hAB, Set.preimage_inter]
    congr 1

/-- **Every response projection has a density that is a function of the statistic.** -/
theorem responseProjection_eq_withDensity_comp {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    ∃ g : (J → ℝ) → ℝ≥0∞, Measurable g ∧
      responseProjection hS ν M = ν.withDensity fun x ↦ g (statPoint S x) := by
  obtain ⟨A, n, hchain, hrel⟩ := exists_exposedChain hS ν hfin
  obtain ⟨θ, -, hθ⟩ := responseProjection_eq_of_exposedChain hS ν hchain hrel
  obtain ⟨B, hB, hAB⟩ := ExposedChain.exists_preimage ν hchain
  have hAm : MeasurableSet A := hchain.measurableSet hS
  have hA0 : ν A ≠ 0 := (ENNReal.toReal_pos_iff.1 (hchain.pos hS)).1.ne'
  have hPA := isProbabilityMeasure_faceMeasure ν hA0
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = priorZ (faceMeasure ν A) (fun _ ↦ (1 : ℝ))
    (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 := ⟨_, rfl⟩
  refine ⟨fun y ↦ B.indicator (fun _ ↦ (ν A)⁻¹) y *
    ENNReal.ofReal (Real.exp (-(1 * (0 + dotJ θ y))) * 1 / Z), ?_, ?_⟩
  · refine (measurable_const.indicator hB).mul ?_
    exact ((((continuous_dotJ_right θ).measurable.const_add _).const_mul _).neg.exp.mul_const _
      |>.div_const _).ennreal_ofReal
  · have hm : Measurable (affLoss (fun _ ↦ (0 : ℝ)) S θ) := by
      unfold affLoss
      exact measurable_const.add (Finset.measurable_sum _ fun i _ ↦ (hS i).1.const_mul _)
    have hdens : Measurable fun x ↦ ENNReal.ofReal
        (Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * (fun _ : X ↦ (1 : ℝ)) x / Z) :=
      (((hm.const_mul 1).neg.exp.mul measurable_const).div_const Z).ennreal_ofReal
    rw [hθ]
    unfold familyMeasure
    rw [← hZ, faceMeasure_eq_withDensity ν hAm,
      ← withDensity_mul ν (measurable_const.indicator hAm) hdens]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    have e1 : A.indicator (fun _ ↦ (ν A)⁻¹) x = B.indicator (fun _ ↦ (ν A)⁻¹) (statPoint S x) := by
      rw [hAB]
      rfl
    have e2 : affLoss (fun _ ↦ (0 : ℝ)) S θ x = 0 + dotJ θ (statPoint S x) := by
      simp only [affLoss, dotJ, statPoint]
    rw [e1, e2]

/-- **The invisible information splits for every finite-information data law**:
`KL(D ‖ Π_ν(M_D)) = KL(D ‖ D↑) + KL(S_*D ‖ S_*Π_ν(M_D))`, with no interiority hypothesis. -/
theorem klDiv_responseProjection_eq_statisticLift_add_map' (D : Measure X)
    [IsProbabilityMeasure D] (hDkl : klDiv D ν ≠ ⊤) :
    klDiv D (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)) =
      klDiv D (statisticLift ν D (statPoint S)) +
        klDiv (D.map (statPoint S))
          ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)).map (statPoint S)) := by
  have hDν : D ≪ ν := (klDiv_ne_top_iff.1 hDkl).1
  have hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤ := fun h ↦
    hDkl (klDiv_eq_top_of_genRate_eq_top hS ν D h)
  obtain ⟨hP, -, -, -⟩ := responseProjection_spec hS ν hfin
  obtain ⟨g, hg, hPi⟩ := responseProjection_eq_withDensity_comp hS ν hfin
  rw [hPi] at hP ⊢
  exact klDiv_withDensity_comp_eq_statisticLift_add_map ν D (statPoint S) (measurable_statPoint hS)
    hDν hg hP hDkl

end Boundary

end Laplace.Multi
