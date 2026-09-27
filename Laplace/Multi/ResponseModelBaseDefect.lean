/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDefect
import Laplace.Multi.DataRayBlocks
import Laplace.Multi.EndpointConvergence
import Laplace.Multi.FixedNormalLimit
import Laplace.Multi.CompletionLawEqProjection

/-!
# The defect theorem at a model base point

Along a data path `D_t ∝ e^{t h} D` through a **model law** `D = P_{θ₀}` the response defect
`ℰ(t) = KL(D_t ‖ R_{m(D_t)})`, the information in the data law that the response family does not
represent, is quadratic to leading order with the **residual variance** of the score as
curvature:

`KL(D_t ‖ R_{m(D_t)}) / t² → ½ Var_D(h − g_h)`,   `g_h` the regression of `h` on the features
under `D`   (`tendsto_klDiv_tilted_familyMeasure_responseProjection_div_sq`).

To second order, the information invisible to the response is the variance of the score residual.
The proof has two ingredients.

* **Base change** (`responseProjection_familyMeasure_base`): the entropy projection of a mean
  does not depend on the base point chosen within the family, `Π^{P_{θ₀}}(M) = Π^ν(M)`. Since
  `KL(ρ ‖ P_{θ₀}) = KL(ρ ‖ ν) + ⟨θ₀, M⟩ + A(θ₀)` for every law `ρ` of mean `M`, the two
  constrained minimisation problems have the same minimiser; formally the Pythagorean identity at
  `ν` applied to the `P_{θ₀}`-projection forces `KL(Π^{P_{θ₀}}(M) ‖ Π^ν(M)) = 0`.
* **The defect theorem at the featureless law** (`tendsto_responseDefect_div_sq`): the seabed's
  `ℰ(0) = 0`, `ℰ'(0) = 0`, `ℰ''(0) = Var_ν(h − regressor)` (`ResponseDefect`) give
  `ℰ(t)/t² → ℰ''(0)/2` by L'Hôpital.

Applied with `ν` replaced by the model law `D` (any model law is the featureless law of the
family it generates) and transported back by base change, this is the defect theorem at every
model base point.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Featureless

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- **THE DEFECT THEOREM AT THE FEATURELESS LAW**: `ℰ(t)/t² → ½ Var_ν(h − regressor)`. -/
theorem tendsto_responseDefect_div_sq :
    Tendsto (fun t ↦ responseDefect S ν h t / t ^ 2) (𝓝[≠] 0)
      (𝓝 (lawCov ν (fun x ↦ h x - regressor hS ν hh x)
        (fun x ↦ h x - regressor hS ν hh x) / 2)) := by
  have hd : ∀ t, HasDerivAt (responseDefect S ν h) (deriv (responseDefect S ν h) t) t :=
    fun t ↦ (hasDerivAt_responseDefect hS ν hh t).differentiableAt.hasDerivAt
  have hd0 : deriv (responseDefect S ν h) 0 = 0 := (hasDerivAt_responseDefect_zero hS ν hh).deriv
  have hdd := hasDerivAt_deriv_responseDefect_zero hS ν hh
  rw [residual_variance hS ν hh] at hdd
  refine HasDerivAt.lhopital_zero_nhdsNE (f' := deriv (responseDefect S ν h))
    (g' := fun t ↦ 2 * t) (Eventually.of_forall hd)
    (Eventually.of_forall fun t ↦ by simpa using hasDerivAt_pow 2 t) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero two_ne_zero ht
  · have := (hd 0).continuousAt.tendsto
    rw [responseDefect_zero hS ν (h := h)] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have : Tendsto (fun t : ℝ ↦ t ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) := (continuous_pow 2).tendsto 0
    rw [zero_pow two_ne_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have hslope := hasDerivAt_iff_tendsto_slope.1 hdd
    have h2 := hslope.div_const 2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    rw [slope_def_field, hd0, sub_zero, sub_zero]
    field_simp

end Featureless

section BaseChange

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty J] in
/-- The divergence to a family member of a law of finite information and mean `M` is the
divergence to the base point plus a constant depending only on `M`. -/
theorem toReal_klDiv_familyMeasure_eq_add (θ₀ : J → ℝ) (ρ : Measure X) [IsProbabilityMeasure ρ]
    (hρν : ρ ≪ ν) (hfin : klDiv ρ ν ≠ ⊤) {M : J → ℝ} (hM : (fun i ↦ ∫ x, S i x ∂ρ) = M) :
    (klDiv ρ (Pfam θ₀)).toReal = (klDiv ρ ν).toReal + dotJ θ₀ M +
      Real.log (∫ x, Real.exp (-1 * dirLoss S θ₀ x) ∂ν) := by
  rw [familyMeasure_one_zero_eq_tilted hS ν, toReal_klDiv_tilted_right ν ρ hρν hfin
    ((bdd_dirLoss hS θ₀).const_mul (-1)), integral_const_mul, integral_dirLoss_eq_dotJ θ₀ ρ hS,
    hM]
  ring

omit [Nonempty J] in
/-- The divergence to a family member of a law of finite information is finite. -/
theorem klDiv_familyMeasure_ne_top_of_ne_top (θ₀ : J → ℝ) (ρ : Measure X)
    [IsProbabilityMeasure ρ] (hρν : ρ ≪ ν) (hfin : klDiv ρ ν ≠ ⊤) :
    klDiv ρ (Pfam θ₀) ≠ ⊤ := by
  rw [familyMeasure_one_zero_eq_tilted hS ν, klDiv_tilted_right_eq ν ρ hρν hfin
    ((bdd_dirLoss hS θ₀).const_mul (-1))]
  exact ENNReal.ofReal_ne_top

omit [Nonempty J] in
/-- The base point is a bounded tilt of every family member. -/
theorem eq_tilted_familyMeasure (θ₀ : J → ℝ) :
    ν = (Pfam θ₀).tilted (fun x ↦ -(-1 * dirLoss S θ₀ x)) := by
  rw [familyMeasure_one_zero_eq_tilted hS ν, tilted_tilted
    (integrable_exp_of_bdd ν ((bdd_dirLoss hS θ₀).const_mul (-1)))]
  have e : ((fun x ↦ -1 * dirLoss S θ₀ x) + fun x ↦ -(-1 * dirLoss S θ₀ x)) = 0 := by
    funext x
    simp
  rw [e, tilted_zero]

/-- **BASE CHANGE OF THE ENTROPY PROJECTION**: the entropy projection of a mean does not depend
on the base point chosen within the family, `Π^{P_{θ₀}}(M) = Π^ν(M)`. -/
theorem responseProjection_familyMeasure_base (θ₀ : J → ℝ) {M : J → ℝ}
    (hfin : genRate ν S M ≠ ⊤) :
    responseProjection hS (Pfam θ₀) M = responseProjection hS ν M := by
  have hD := isProbabilityMeasure_family hS ν θ₀
  have hf₀ : Bdd fun x ↦ -1 * dirLoss S θ₀ x := (bdd_dirLoss hS θ₀).const_mul (-1)
  -- the base-`ν` projection
  obtain ⟨hP, hmean, hkl, hpyth⟩ := responseProjection_spec hS ν hfin
  have hRν : responseProjection hS ν M ≪ ν := responseProjection_absolutelyContinuous hS ν hfin
  have hRkl : klDiv (responseProjection hS ν M) ν ≠ ⊤ := hkl ▸ hfin
  -- finite rate at base `D`
  have hRD : klDiv (responseProjection hS ν M) (Pfam θ₀) ≠ ⊤ :=
    klDiv_familyMeasure_ne_top_of_ne_top hS ν θ₀ _ hRν hRkl
  have hfinD : genRate (Pfam θ₀) S M ≠ ⊤ := by
    rw [← entropyProj_eq_genRate hS (Pfam θ₀) M]
    exact ne_top_of_le_ne_top hRD (entropyProj_le_klDiv (Pfam θ₀) _ hmean)
  -- the base-`D` projection
  obtain ⟨hP', hmean', hkl', -⟩ := responseProjection_spec hS (Pfam θ₀) hfinD
  have hR'D : responseProjection hS (Pfam θ₀) M ≪ Pfam θ₀ :=
    responseProjection_absolutelyContinuous hS (Pfam θ₀) hfinD
  have hR'Dkl : klDiv (responseProjection hS (Pfam θ₀) M) (Pfam θ₀) ≠ ⊤ := hkl' ▸ hfinD
  have hR'ν : responseProjection hS (Pfam θ₀) M ≪ ν :=
    hR'D.trans (familyMeasure_one_zero_eq_tilted hS ν θ₀ ▸ tilted_absolutelyContinuous ν _)
  have hR'kl : klDiv (responseProjection hS (Pfam θ₀) M) ν ≠ ⊤ := by
    have e := congrArg (fun μ ↦ klDiv (responseProjection hS (Pfam θ₀) M) μ)
      (eq_tilted_familyMeasure hS ν θ₀)
    simp only at e
    rw [e, klDiv_tilted_right_eq (Pfam θ₀) _ hR'D hR'Dkl (bdd_neg hf₀)]
    exact ENNReal.ofReal_ne_top
  -- minimality at base `D` transfers to base `ν`
  have hmin : klDiv (responseProjection hS (Pfam θ₀) M) (Pfam θ₀) ≤
      klDiv (responseProjection hS ν M) (Pfam θ₀) := by
    rw [hkl', ← entropyProj_eq_genRate hS (Pfam θ₀) M]
    exact entropyProj_le_klDiv (Pfam θ₀) _ hmean
  have hmin' : (klDiv (responseProjection hS (Pfam θ₀) M) ν).toReal ≤
      (klDiv (responseProjection hS ν M) ν).toReal := by
    have h1 := toReal_klDiv_familyMeasure_eq_add hS ν θ₀ _ hR'ν hR'kl hmean'
    have h2 := toReal_klDiv_familyMeasure_eq_add hS ν θ₀ _ hRν hRkl hmean
    have h3 := ENNReal.toReal_mono hRD hmin
    linarith
  -- the Pythagorean identity at base `ν` forces the two projections to coincide
  have hpy := hpyth _ hP' hmean'
  have hpy' : (klDiv (responseProjection hS (Pfam θ₀) M) ν).toReal =
      (klDiv (responseProjection hS (Pfam θ₀) M) (responseProjection hS ν M)).toReal +
        (klDiv (responseProjection hS ν M) ν).toReal := by
    rw [hpy, hkl, ENNReal.toReal_add ?_ hfin]
    intro htop
    rw [htop, top_add] at hpy
    exact hR'kl hpy
  have hzero : (klDiv (responseProjection hS (Pfam θ₀) M) (responseProjection hS ν M)).toReal
      = 0 := le_antisymm (by linarith) ENNReal.toReal_nonneg
  have hne : klDiv (responseProjection hS (Pfam θ₀) M) (responseProjection hS ν M) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hpy
    exact hR'kl hpy
  have := hP
  have := hP'
  exact klDiv_eq_zero_iff.1 ((ENNReal.toReal_eq_zero_iff _).1 hzero |>.resolve_right hne)

end BaseChange

section ModelBase

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The mean of a tilted model law has finite rate. -/
theorem genRate_tilted_familyMeasure_ne_top (θ₀ : J → ℝ) (t : ℝ) :
    genRate ν S (fun i ↦ ∫ x, S i x ∂(Pfam θ₀).tilted fun x ↦ t * h x) ≠ ⊤ := by
  have hf₀ : Bdd fun x ↦ -1 * dirLoss S θ₀ x := (bdd_dirLoss hS θ₀).const_mul (-1)
  rw [familyMeasure_one_zero_eq_tilted hS ν, tilted_tilted (integrable_exp_of_bdd ν hf₀)]
  exact genRate_ne_top_of_mem_intrinsicInterior hS ν
    (mean_tilted_mem_intrinsicInterior hS ν (hf₀.add (hh.const_mul t)))

/-- **THE DEFECT THEOREM AT A MODEL BASE POINT**: along `D_t ∝ e^{t h} P_{θ₀}`, the information
invisible to the response is, to second order, the residual variance of the score after regression
on the features under `D = P_{θ₀}`:
`KL(D_t ‖ R_{m(D_t)}) / t² → ½ Var_D(h − g_h)`. -/
theorem tendsto_klDiv_tilted_familyMeasure_responseProjection_div_sq (θ₀ : J → ℝ)
    (D : Measure X) [IsProbabilityMeasure D] (hD : D = Pfam θ₀) :
    Tendsto (fun t ↦ (klDiv (D.tilted fun x ↦ t * h x)
        (responseProjection hS ν fun i ↦ ∫ x, S i x ∂D.tilted fun x ↦ t * h x)).toReal /
      t ^ 2) (𝓝[≠] 0)
      (𝓝 (lawCov D (fun x ↦ h x - regressor hS D hh x)
        (fun x ↦ h x - regressor hS D hh x) / 2)) := by
  have key := tendsto_responseDefect_div_sq hS D hh
  refine key.congr' (Eventually.of_forall fun t ↦ ?_)
  rw [responseDefect_eq_klDiv hS D hh t]
  subst hD
  rw [responseProjection_familyMeasure_base hS ν θ₀
    (genRate_tilted_familyMeasure_ne_top hS ν hh θ₀ t)]

end ModelBase

end Laplace.Multi
