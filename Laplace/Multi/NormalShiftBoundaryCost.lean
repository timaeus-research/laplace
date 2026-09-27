/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.NormalTiltFisherComparison
import Laplace.Multi.FisherCauchyRealisation

/-!
# A fixed normal shift costs at most `B_h √(1 − P_θ(A))`

For `h` in the sign-adjusted normal cone of a face event `A` (`⟨h,S⟩ = c` a.e. on `A`, `⟨h,S⟩ ≥ c` a.e.,
`|⟨h,S⟩ − c| ≤ B`), the Fisher distance from `θ` to `θ + h` is at most `B √(P_θ(A^c))`: along the
segment `θ + s h` the tilt only increases the mass of `A`, and the Fisher speed is the standard
deviation of `Y_h = ⟨h,S⟩ − c`, which vanishes on `A` and is bounded by `B`, so
`Var Y_h ≤ B² P(A^c) ≤ B² P_θ(A^c)`. **A fixed normal shift is Fisher-cheap wherever the face has
probability close to one** — the engine of normal-cone coalescence.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Tilt

variable {X : Type*} [MeasurableSpace X]

/-- Tilting by a nonpositive function vanishing on `A` does not decrease the mass of `A`. -/
theorem measureReal_le_measureReal_tilted (P : Measure X) [IsProbabilityMeasure P] {g : X → ℝ}
    (hg : Bdd g) (hg1 : ∀ᵐ x ∂P, g x ≤ 0) {A : Set X} (hA : MeasurableSet A)
    (hgA : ∀ᵐ x ∂P, x ∈ A → g x = 0) : P.real A ≤ (P.tilted g).real A := by
  have hZpos : 0 < ∫ x, Real.exp (g x) ∂P := integral_exp_pos (integrable_exp_of_bdd P hg)
  have hZle : ∫ x, Real.exp (g x) ∂P ≤ 1 := by
    calc ∫ x, Real.exp (g x) ∂P ≤ ∫ _, (1 : ℝ) ∂P :=
          integral_mono_ae (integrable_exp_of_bdd P hg) (integrable_const 1)
            (hg1.mono fun x hx ↦ Real.exp_le_one_iff.2 hx)
      _ = 1 := by simp
  have hAint : ∫ x in A, Real.exp (g x) / ∫ y, Real.exp (g y) ∂P ∂P =
      P.real A / ∫ y, Real.exp (g y) ∂P := by
    rw [integral_div]
    congr 1
    calc ∫ x in A, Real.exp (g x) ∂P = ∫ _ in A, (1 : ℝ) ∂P :=
          setIntegral_congr_ae hA (hgA.mono fun x hx hxA ↦ by rw [hx hxA, Real.exp_zero])
      _ = P.real A := by rw [setIntegral_const, smul_eq_mul, mul_one]
  have : (P.tilted g).real A = P.real A / ∫ y, Real.exp (g y) ∂P := by
    rw [measureReal_def, tilted_apply_eq_ofReal_integral' g hA,
      ENNReal.toReal_ofReal (integral_nonneg fun x ↦ by positivity), hAint]
  rw [this]
  exact le_div_self measureReal_nonneg hZpos hZle

/-- Tilting by a nonpositive function vanishing on `A` does not increase the mass of `A^c`. -/
theorem measureReal_tilted_compl_le (P : Measure X) [IsProbabilityMeasure P] {g : X → ℝ}
    (hg : Bdd g) (hg1 : ∀ᵐ x ∂P, g x ≤ 0) {A : Set X} (hA : MeasurableSet A)
    (hgA : ∀ᵐ x ∂P, x ∈ A → g x = 0) : (P.tilted g).real Aᶜ ≤ P.real Aᶜ := by
  have hPt : IsProbabilityMeasure (P.tilted g) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd P hg)
  rw [measureReal_compl hA, measureReal_compl hA, probReal_univ, probReal_univ]
  linarith [measureReal_le_measureReal_tilted P hg hg1 hA hgA]

end Tilt

section Shift

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The Fisher speed of a normal shift** is at most `B √(P_θ(A^c))` along the whole segment. -/
theorem fisherNorm_add_smul_normal_le (θ h : J → ℝ) {c B : ℝ} {A : Set X} (hA : MeasurableSet A)
    (hc : ∀ᵐ x ∂ν, x ∈ A → dirLoss S h x = c) (hge : ∀ᵐ x ∂ν, c ≤ dirLoss S h x)
    (hB : ∀ x, |dirLoss S h x - c| ≤ B) {s : ℝ} (hs : 0 ≤ s) :
    fisherNorm S ν (θ + s • h) h ≤ B * √((Pfam θ).real Aᶜ) := by
  have hPθ := isProbabilityMeasure_family hS ν θ
  have hPs := isProbabilityMeasure_family hS ν (θ + s • h)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  have hac : Pfam θ ≪ ν := by
    rw [familyMeasure_eq_withDensity_famDens]
    exact withDensity_absolutelyContinuous _ _
  -- the mass of `A^c` does not increase along the shift
  have hmass : (Pfam (θ + s • h)).real Aᶜ ≤ (Pfam θ).real Aᶜ := by
    rw [familyMeasure_add_eq_tilted hS ν θ (s • h) (s * c)]
    have hgb : Bdd fun x ↦ -(dirLoss S (s • h) x - s * c) :=
      bdd_neg ((bdd_dirLoss hS (s • h)).sub (Bdd.const _))
    have hge' : ∀ᵐ x ∂Pfam θ, c ≤ dirLoss S h x := hac.ae_le hge
    have hc' : ∀ᵐ x ∂Pfam θ, x ∈ A → dirLoss S h x = c := hac.ae_le hc
    refine measureReal_tilted_compl_le (Pfam θ) hgb (hge'.mono fun x hx ↦ ?_) hA
      (hc'.mono fun x hx hxA ↦ ?_)
    · simp only [dirLoss_smul]
      nlinarith
    · simp only [dirLoss_smul, hx hxA, sub_self, neg_zero]
  -- the speed is the standard deviation of `Y = ⟨h,S⟩ − c`, which vanishes on `A`
  have hY : Bdd fun x ↦ dirLoss S h x - c := (bdd_dirLoss hS h).sub (Bdd.const c)
  have hvar : fisherVar S ν (θ + s • h) h ≤ B ^ 2 * (Pfam (θ + s • h)).real Aᶜ := by
    rw [fisherVar, ← lawCov_sub_const_self _ (bdd_dirLoss hS h) c]
    refine (lawCov_self_le_integral_sq _ hY 0).trans ?_
    have hind : ∫ x, Aᶜ.indicator (fun _ ↦ B ^ 2) x ∂Pfam (θ + s • h) =
        B ^ 2 * (Pfam (θ + s • h)).real Aᶜ := by
      rw [integral_indicator hA.compl, setIntegral_const, smul_eq_mul, mul_comm]
    rw [← hind]
    have hYY : Bdd fun x ↦ (dirLoss S h x - c - 0) * (dirLoss S h x - c - 0) :=
      (hY.sub (Bdd.const 0)).mul (hY.sub (Bdd.const 0))
    have hcs : ∀ᵐ x ∂Pfam (θ + s • h), x ∈ A → dirLoss S h x = c := by
      have hac' : Pfam (θ + s • h) ≪ ν := by
        rw [familyMeasure_eq_withDensity_famDens]
        exact withDensity_absolutelyContinuous _ _
      exact hac'.ae_le hc
    refine integral_mono_ae (integrable_of_bdd_prob _ hYY)
      ((integrable_const _).indicator hA.compl) (hcs.mono fun x hcx ↦ ?_)
    simp only [sub_zero]
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_notMem (by simpa using hx), hcx hx, sub_self, mul_zero]
    · rw [Set.indicator_of_mem (by simpa using hx), ← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  rw [fisherNorm, ← Real.sqrt_sq hB0, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (hvar.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg _)))

/-- **A fixed normal shift costs at most `B √(P_θ(A^c))`.** -/
theorem fisherDist_add_normal_le (θ h : J → ℝ) (hθ : θ ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (hh : h ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {c B : ℝ} {A : Set X} (hA : MeasurableSet A)
    (hc : ∀ᵐ x ∂ν, x ∈ A → dirLoss S h x = c) (hge : ∀ᵐ x ∂ν, c ≤ dirLoss S h x)
    (hB : ∀ x, |dirLoss S h x - c| ≤ B) :
    fisherDist S ν ⟨θ, hθ⟩ ⟨θ + h, Submodule.add_mem _ hθ hh⟩ ≤ B * √((Pfam θ).real Aᶜ) := by
  have hmem : ∀ s : ℝ, θ + s • h ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun s ↦
    Submodule.add_mem _ hθ (Submodule.smul_mem _ _ hh)
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ θ + s • h) h s := fun s ↦ by
    have := ((hasDerivAt_id' (x := s)).smul_const h).const_add θ
    rwa [one_smul] at this
  have h1 := fisherDist_le_integral hS ν hmem hd continuous_const zero_le_one
  have e0 : (⟨θ + (0 : ℝ) • h, hmem 0⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) = ⟨θ, hθ⟩ :=
    Subtype.ext (by simp)
  have e1 : (⟨θ + (1 : ℝ) • h, hmem 1⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) =
      ⟨θ + h, Submodule.add_mem _ hθ hh⟩ := Subtype.ext (by simp)
  rw [e0, e1] at h1
  refine h1.trans ?_
  have hcont : Continuous fun s : ℝ ↦ fisherNorm S ν (θ + s • h) h :=
    continuous_fisherNorm_comp hS ν (continuous_const.add (continuous_id.smul continuous_const))
      continuous_const
  calc ∫ s in (0 : ℝ)..1, fisherNorm S ν (θ + s • h) h
      ≤ ∫ _ in (0 : ℝ)..1, B * √((Pfam θ).real Aᶜ) :=
        intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable _ _)
          (by simp) fun s hs ↦ fisherNorm_add_smul_normal_le hS ν θ h hA hc hge hB hs.1
    _ = B * √((Pfam θ).real Aᶜ) := by simp

end Shift

end Laplace.Multi
