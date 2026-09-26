/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.QuantitativeJets

/-!
# The explicit cubic remainder of the featureless expansion

* `norm_L1_le_of_forall_integral_mul_le`: the `L¹` norm is bounded by a bound on the pairings with
  all observables bounded by one (duality via the sign observable);
* `norm_iteratedDeriv_three_atlas_le_uniform`: `‖p'''(t)‖₁ ≤ 4L²D³/λ^{5/2}` on `(0,1)` under
  uniform coercivity and feature bounds along the atlas;
* `reconstructionL1_cubic_remainder`: **the explicit second-order featureless expansion**
  `‖p(s) − p(0) − s p'(0) − ½ s² p''(0)‖₁ ≤ (2L²D³/(3λ^{5/2})) s³` for all `s ∈ [0, 1]`, with the
  Lagrange constant `1/3!`: pair with an observable `|F| ≤ 1`, apply the real Lagrange remainder to
  `t ↦ E_{Q_{M_t}} F`, bound the third derivative by the third jet, and dualise.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff Nat

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

section Duality

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **Norm duality**: `‖f‖₁ ≤ C` as soon as `∫ F f ≤ C` for every observable with `|F| ≤ 1`. -/
theorem norm_L1_le_of_forall_integral_mul_le (f : X →₁[ν] ℝ) {C : ℝ}
    (h : ∀ F : X → ℝ, Bdd F → (∀ x, |F x| ≤ 1) → ∫ x, F x * f x ∂ν ≤ C) : ‖f‖ ≤ C := by
  have hm : Measurable f := (Lp.stronglyMeasurable f).measurable
  obtain ⟨F, hF⟩ : ∃ F : X → ℝ, F = fun x ↦ if 0 ≤ f x then 1 else -1 := ⟨_, rfl⟩
  have hF1 : ∀ x, |F x| ≤ 1 := fun x ↦ by
    rw [hF]
    beta_reduce
    split_ifs <;> simp
  have hFb : Bdd F := ⟨by
      rw [hF]
      exact Measurable.ite (measurableSet_le measurable_const hm) measurable_const
        measurable_const, 1, hF1⟩
  have h1 : ∫ x, F x * f x ∂ν = ∫ x, |f x| ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    rw [hF]
    beta_reduce
    split_ifs with hx
    · rw [one_mul, abs_of_nonneg hx]
    · rw [neg_one_mul, abs_of_neg (not_le.1 hx)]
  rw [L1.norm_eq_integral_norm]
  simp only [Real.norm_eq_abs]
  rw [← h1]
  exact h F hFb hF1

end Duality

section Cubic

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
  {lam L D : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L) (hD : 0 ≤ D)
  (hδ : dotJ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
    (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) ≤ D ^ 2)
  (hcov : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : dirSpan ν (fun _ ↦ (1 : ℝ)) S, lam * dotJ (v : J → ℝ) v ≤
    lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M t : J → ℝ))
      (dirLoss S v) (dirLoss S v))
  (hSb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    dotJ (fun j ↦ atlasPath S ν M t j - S j x) (fun j ↦ atlasPath S ν M t j - S j x) ≤ L ^ 2)
include hrel

/-- The reconstruction curve along the atlas. -/
local notation "p" => fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)

include hlam hL hD hδ hcov hSb in
/-- The third jet is uniformly bounded on `(0, 1)`. -/
theorem norm_iteratedDeriv_three_atlas_le_uniform :
    ∀ t ∈ Ioo (0 : ℝ) 1, ‖iteratedDeriv 3 p t‖ ≤ 4 * L ^ 2 * D ^ 3 / (lam ^ 2 * √lam) :=
  fun t ht ↦ norm_iteratedDeriv_three_atlas_le hS ν
    (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel) hrel hlam hL hD hδ
    (hcov t (Ioo_subset_Icc_self ht)) (hSb t (Ioo_subset_Icc_self ht)) ht

/-- The response of an observable along the atlas is `C^∞` on the interior atlas domain. -/
theorem contDiffOn_obsL1_atlas {F : X → ℝ} (hF : Bdd F) :
    ContDiffOn ℝ ∞ (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t)))
      (atlasDomain S ν M) :=
  (obsL1 ν hF).contDiff.comp_contDiffOn (contDiffOn_reconstructionL1_atlas hS ν
    (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel))

include hlam hL hD hδ hcov hSb in
/-- **The explicit cubic remainder of the featureless expansion**:
`‖p(s) − p(0) − s p'(0) − ½ s² p''(0)‖₁ ≤ (4L²D³/λ^{5/2}) s³/6` on `[0, 1]`. -/
theorem reconstructionL1_cubic_remainder :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ‖reconstructionL1 hS ν (atlasPath S ν M s) -
          ∑ k ∈ Finset.range 3, ((k ! : ℝ)⁻¹ * s ^ k) • iteratedDeriv k p 0‖ ≤
        4 * L ^ 2 * D ^ 3 / (lam ^ 2 * √lam) * s ^ 3 / 6 := by
  intro s hs
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  have hU := isOpen_atlas_interior hS ν hfin
  have hIcc := Icc_subset_atlasDomain hS ν hrel
  have hC3 := norm_iteratedDeriv_three_atlas_le_uniform hS ν hrel hlam hL hD hδ hcov hSb
  rcases eq_or_lt_of_le hs.1 with h0 | hs0
  · subst h0
    simp [Finset.sum_range_succ, iteratedDeriv_zero]
  refine norm_L1_le_of_forall_integral_mul_le ν _ fun F hF hF1 ↦ ?_
  have h0D : (0 : ℝ) ∈ atlasDomain S ν M := hIcc (left_mem_Icc.2 zero_le_one)
  have hsub : Icc 0 s ⊆ atlasDomain S ν M := (Icc_subset_Icc le_rfl hs.2).trans hIcc
  have hg := contDiffOn_obsL1_atlas hS ν hrel hF
  have hgAt : ∀ y ∈ Icc 0 s, ContDiffAt ℝ 2
      (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t))) y := fun y hy ↦
    (hg.contDiffAt (hU.mem_nhds (hsub hy))).of_le (by exact_mod_cast natCast_le_infty 2)
  have hg2 : ContDiffOn ℝ 2 (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t)))
      (uIcc 0 s) := by
    rw [uIcc_of_le hs.1]
    exact (hg.mono hsub).of_le (by exact_mod_cast natCast_le_infty 2)
  have hg' : DifferentiableOn ℝ (iteratedDerivWithin 2
      (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t))) (uIcc 0 s)) (uIoo 0 s) := by
    rw [uIcc_of_le hs.1, uIoo_of_le hs.1]
    have h1 := (contDiffOn_infty_iff_deriv_of_isOpen hU).1 hg
    have h2 := (contDiffOn_infty_iff_deriv_of_isOpen hU).1 h1.2
    have e2 : iteratedDeriv 2 (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t))) =
        deriv (deriv (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t)))) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    refine ((h2.2.differentiableOn (by simp)).mono (Ioo_subset_Icc_self.trans hsub)).congr
      fun y hy ↦ ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs0)
      (hgAt y (Ioo_subset_Icc_self hy)) (Ioo_subset_Icc_self hy), e2]
  obtain ⟨x', hx', hx⟩ := taylor_mean_remainder_lagrange (n := 2) hs0.ne hg2 hg'
  rw [uIoo_of_le hs.1] at hx'
  rw [uIcc_of_le hs.1, taylor_within_apply, sub_zero] at hx
  -- the Taylor polynomial of the response is the pairing with the Taylor polynomial
  have hT : ∀ k ∈ Finset.range 3, ((k ! : ℝ)⁻¹ * s ^ k) • iteratedDerivWithin k
      (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t))) (Icc 0 s) 0 =
      ((k ! : ℝ)⁻¹ * s ^ k) * obsL1 ν hF (iteratedDeriv k p 0) := fun k _ ↦ by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs0)
      ((hg.contDiffAt (hU.mem_nhds h0D)).of_le (by exact_mod_cast natCast_le_infty k))
      (left_mem_Icc.2 hs.1), clm_iteratedDeriv_reconstructionL1_atlas hS ν hfin _ k h0D,
      smul_eq_mul]
  rw [Finset.sum_congr rfl hT] at hx
  -- the third derivative is the pairing with the third jet
  have h3 : |iteratedDerivWithin 3
      (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t))) (Icc 0 s) x'| ≤
      4 * L ^ 2 * D ^ 3 / (lam ^ 2 * √lam) := by
    have hx'D : x' ∈ atlasDomain S ν M := hsub (Ioo_subset_Icc_self hx')
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs0)
      ((hg.contDiffAt (hU.mem_nhds hx'D)).of_le (by exact_mod_cast natCast_le_infty 3))
      (Ioo_subset_Icc_self hx'), ← clm_iteratedDeriv_reconstructionL1_atlas hS ν hfin _ 3 hx'D]
    refine (abs_obsL1_le ν hF hF1 _).trans ?_
    rw [one_mul]
    exact hC3 x' ⟨hx'.1, hx'.2.trans_le hs.2⟩
  -- the pairing with the remainder
  have e : ∫ x, F x * (reconstructionL1 hS ν (atlasPath S ν M s) -
      ∑ k ∈ Finset.range 3, ((k ! : ℝ)⁻¹ * s ^ k) • iteratedDeriv k p 0) x ∂ν =
      obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M s)) -
        ∑ k ∈ Finset.range 3, ((k ! : ℝ)⁻¹ * s ^ k) * obsL1 ν hF (iteratedDeriv k p 0) := by
    rw [← obsL1_apply ν hF, map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul]
  rw [e, hx]
  have hs3 : (0 : ℝ) ≤ s ^ 3 := by positivity
  calc iteratedDerivWithin (2 + 1)
        (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t))) (Icc 0 s) x' *
          s ^ (2 + 1) / (2 + 1)! ≤
        |iteratedDerivWithin (2 + 1)
          (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t))) (Icc 0 s) x'| *
          s ^ 3 / 6 := by
        rw [show (2 + 1 : ℕ) = 3 from rfl, show ((3 : ℕ)! : ℝ) = 6 by norm_num [Nat.factorial]]
        gcongr
        exact le_abs_self _
    _ ≤ 4 * L ^ 2 * D ^ 3 / (lam ^ 2 * √lam) * s ^ 3 / 6 := by
        gcongr

end Cubic

end Laplace.Multi
