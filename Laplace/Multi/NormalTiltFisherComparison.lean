/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherSpeedForm
import Laplace.Multi.FacetFisherAccess
import Laplace.Multi.QuadraticInformationBound

/-!
# Face-normal translations are uniformly Fisher-Lipschitz

Let `A` be a face event and `a` a parameter with `⟨a,S⟩ = c` on `A` and `⟨a,S⟩ ≥ c` a.e. (a
sign-adjusted normal of the face). Translating by `a` reweights `P_θ` by `f_a = e^{−(⟨a,S⟩−c)} ≤ 1`,
`f_a = 1` on `A`, and the variance-minimisation formula gives
**`Var_{P_{θ+a}}⟨w,S⟩ ≤ Var_{P_θ}⟨w,S⟩ / P_θ(A)`**, uniformly in `a`. This is the key uniform
estimate of the normal-translation programme: translations by arbitrarily deep normals are
Fisher-Lipschitz on the region where the face keeps positive probability.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Tilt

variable {X : Type*} [MeasurableSpace X]

/-- **Variance under a sub-unit tilt**: if `e^g ≤ 1` a.e. and `p ≤ ∫ e^g`, then
`Var_{P.tilted g} f ≤ Var_P f / p`. -/
theorem lawCov_tilted_le_div (P : Measure X) [IsProbabilityMeasure P] {g : X → ℝ} (hg : Bdd g)
    (hg1 : ∀ᵐ x ∂P, g x ≤ 0) {f : X → ℝ} (hf : Bdd f) {p : ℝ} (hp : 0 < p)
    (hpg : p ≤ ∫ x, Real.exp (g x) ∂P) :
    lawCov (P.tilted g) f f ≤ lawCov P f f / p := by
  have hPt : IsProbabilityMeasure (P.tilted g) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd P hg)
  have hZ : 0 < ∫ x, Real.exp (g x) ∂P := lt_of_lt_of_le hp hpg
  obtain ⟨K, hK⟩ := hg.2
  have hexp : Bdd fun x ↦ Real.exp (g x) :=
    ⟨hg.1.exp, Real.exp K, fun x ↦ by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (abs_le.1 (hK x)).2⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ x, f x ∂P := ⟨_, rfl⟩
  have hq : Bdd fun x ↦ (f x - c) * (f x - c) := (hf.sub (Bdd.const c)).mul (hf.sub (Bdd.const c))
  have iq : Integrable (fun x ↦ (f x - c) * (f x - c)) P := integrable_of_bdd_prob P hq
  have ieq : Integrable (fun x ↦ Real.exp (g x) * ((f x - c) * (f x - c))) P :=
    integrable_of_bdd_prob P (hexp.mul hq)
  calc lawCov (P.tilted g) f f ≤ ∫ x, (f x - c) * (f x - c) ∂(P.tilted g) :=
        lawCov_self_le_integral_sq _ hf c
    _ = (1 / ∫ y, Real.exp (g y) ∂P) *
          ∫ x, Real.exp (g x) * ((f x - c) * (f x - c)) ∂P := by
        rw [integral_tilted, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [smul_eq_mul]
        ring
    _ ≤ (1 / ∫ y, Real.exp (g y) ∂P) * ∫ x, (f x - c) * (f x - c) ∂P := by
        refine mul_le_mul_of_nonneg_left (integral_mono_ae ieq iq (hg1.mono fun x hx ↦ ?_))
          (by positivity)
        exact mul_le_of_le_one_left (mul_self_nonneg _) (Real.exp_le_one_iff.2 hx)
    _ = lawCov P f f / ∫ y, Real.exp (g y) ∂P := by
        rw [lawCov_eq_integral_centred P hf hf, ← hc]
        ring
    _ ≤ lawCov P f f / p := div_le_div_of_nonneg_left (lawCov_self_nonneg P hf) hp hpg

end Tilt

section Family

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- Translating the parameter by `a` tilts the law by `e^{−(⟨a,S⟩ − c)}`. -/
theorem familyMeasure_add_eq_tilted (θ a : J → ℝ) (c : ℝ) :
    Pfam (θ + a) = (Pfam θ).tilted fun x ↦ -(dirLoss S a x - c) := by
  have h := familyMeasure_sub_smul_eq_tilted_base hS ν θ a (-1)
  rw [neg_one_smul, sub_neg_eq_add] at h
  rw [h, ← tilted_add_const _ _ c]
  congr 1
  funext x
  ring

/-- **Face-normal translations are uniformly Fisher-Lipschitz**:
`Var_{P_{θ+a}}⟨w,S⟩ ≤ Var_{P_θ}⟨w,S⟩ / P_θ(A)` when `⟨a,S⟩ = c` on `A` and `⟨a,S⟩ ≥ c` a.e. -/
theorem fisherVar_add_le_div (θ a w : J → ℝ) {c : ℝ} {A : Set X} (hA : MeasurableSet A)
    (hc : ∀ x ∈ A, dirLoss S a x = c) (hge : ∀ᵐ x ∂ν, c ≤ dirLoss S a x)
    (hp : 0 < (Pfam θ).real A) :
    fisherVar S ν (θ + a) w ≤ fisherVar S ν θ w / (Pfam θ).real A := by
  have hPθ := isProbabilityMeasure_family hS ν θ
  have hac : Pfam θ ≪ ν := by
    rw [familyMeasure_eq_withDensity_famDens]
    exact withDensity_absolutelyContinuous _ _
  have hgb : Bdd fun x ↦ -(dirLoss S a x - c) := bdd_neg ((bdd_dirLoss hS a).sub (Bdd.const c))
  rw [fisherVar, familyMeasure_add_eq_tilted hS ν θ a c, fisherVar]
  have hge' : ∀ᵐ x ∂Pfam θ, c ≤ dirLoss S a x := hac.ae_le hge
  refine lawCov_tilted_le_div (Pfam θ) hgb ?_ (bdd_dirLoss hS w) hp ?_
  · exact hge'.mono fun x hx ↦ by linarith
  · have hind : Integrable (A.indicator fun _ : X ↦ (1 : ℝ)) (Pfam θ) :=
      (integrable_const 1).indicator hA
    calc (Pfam θ).real A = ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂Pfam θ :=
          (integral_indicator_one hA).symm
      _ ≤ ∫ x, Real.exp (-(dirLoss S a x - c)) ∂Pfam θ := by
          refine integral_mono hind (integrable_exp_of_bdd _ hgb) fun x ↦ ?_
          by_cases hx : x ∈ A
          · simp only [Set.indicator_of_mem hx, hc x hx, sub_self, neg_zero, Real.exp_zero, le_refl]
          · simp only [Set.indicator_of_notMem hx]
            exact (Real.exp_pos _).le

/-- The Fisher norm form of the estimate. -/
theorem fisherNorm_add_le_div_sqrt (θ a w : J → ℝ) {c : ℝ} {A : Set X} (hA : MeasurableSet A)
    (hc : ∀ x ∈ A, dirLoss S a x = c) (hge : ∀ᵐ x ∂ν, c ≤ dirLoss S a x)
    (hp : 0 < (Pfam θ).real A) :
    fisherNorm S ν (θ + a) w ≤ fisherNorm S ν θ w / √((Pfam θ).real A) := by
  rw [fisherNorm, fisherNorm, ← Real.sqrt_div' _ hp.le]
  exact Real.sqrt_le_sqrt (fisherVar_add_le_div hS ν θ a w hA hc hge hp)

/-- **Deep normal translations towards an exposed face**: for `⟨u,S⟩ ≤ β` a.e. and `r ≥ 0`,
`Var_{P_{θ − ru}}⟨w,S⟩ ≤ Var_{P_θ}⟨w,S⟩ / P_θ{⟨u,S⟩ = β}`. -/
theorem fisherVar_sub_smul_le_div (θ u w : J → ℝ) {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    {r : ℝ} (hr : 0 ≤ r) (hp : 0 < (Pfam θ).real {x | dirLoss S u x = β}) :
    fisherVar S ν (θ - r • u) w ≤
      fisherVar S ν θ w / (Pfam θ).real {x | dirLoss S u x = β} := by
  have e : θ - r • u = θ + (-r) • u := by rw [neg_smul, sub_eq_add_neg]
  rw [e]
  refine fisherVar_add_le_div hS ν θ ((-r) • u) w (measurableSet_faceFibre hS u β) (c := -r * β)
    (fun x hx ↦ ?_) (hβ.mono fun x hx ↦ ?_) hp
  · simp only [dirLoss_smul]
    rw [show dirLoss S u x = β from hx]
  · simp only [dirLoss_smul]
    nlinarith

end Family

end Laplace.Multi
