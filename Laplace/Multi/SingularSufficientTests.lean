/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NormalizedSingular

/-!
# Sufficient test families for singular normalized identifiability

`NormalizedSingular` proves that projectively equal Laplace families force
`L₁ = L₂` near a common analytic zero, assuming the projective hypothesis for
*every* smooth compactly supported observable. Its proof uses only two
observables per bump `ψ` and coordinate `i`, with `g = L₂ - L₁` and
`∂_i = fderiv · (Pi.single i 1)`:

  `∂_i (ψ ∂_i g)`   and   `ψ ∂_i g ∂_i L₁`.

Integration by parts against `e^{-tL}` turns the first into `t ∫ ψ ∂_i g ∂_i L`,
and combining the two cancels the unknown scalar `C(t)`, leaving the plain
family `∫ ψ (∂_i g)² e^{-tL₂}` beyond all orders; square-weight rigidity does
the rest. This file makes the dependence explicit:

* `superPoly_integral_fderiv_sub_mul_exp_of_pair`: the cancellation identity
  from the projective hypothesis at the two observables only.
* `normalized_families_force_germ_eq_at_of_tests`: the germ theorem with the
  hypothesis restricted to a class `S` of tests containing the two observables
  for every bump and coordinate.
* `normalized_families_force_germ_eq_at_of_closed_tests`: the class form —
  `S` closed under `φ ↦ ∂_i φ` and `φ ↦ φ ∂_i L₁` and containing `ψ ∂_i g`.
* `normalized_families_force_eq_near_of_tests`,
  `normalized_expectations_force_eq_near_of_tests`: locus form and the form
  with the `1/Z` incorporated.

So in the singular case a family of `2 |ι|` observables per bump suffices for
identifiability; the family depends on the unknown difference `g` through
`∂_i g`, which is the honest content of "derivative-closed and closed under
multiplication by `∂_i L₁`" in the germbij note.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff Pointwise

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- **The cancellation identity from two observables.** If the projective
hypothesis holds at `∂_vφ` and at `φ ∂_vL₁`, then `∫ φ ∂_v(L₂ - L₁) e^{-tL₂}` is
beyond all orders. -/
theorem superPoly_integral_fderiv_sub_mul_exp_of_pair {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂) {C : ℝ → ℝ}
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (v : ι → ℝ)
    (hR₁ : SuperPoly fun t ↦ (∫ w, fderiv ℝ φ w v * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, fderiv ℝ φ w v * Real.exp (-(t * L₁ w)))
    (hR₂ : SuperPoly fun t ↦ (∫ w, φ w * fderiv ℝ L₁ w v * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * fderiv ℝ L₁ w v * Real.exp (-(t * L₁ w))) :
    SuperPoly fun t ↦ ∫ w, φ w *
      (fderiv ℝ (fun w ↦ L₂ w - L₁ w) w v * Real.exp (-(t * L₂ w))) := by
  refine (hR₁.div_id.sub hR₂).congr ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [integral_fderiv_mul_exp hφ hφs h2 t v, integral_fderiv_mul_exp hφ hφs h1 t v]
  have hL₂'c : Continuous fun w ↦ fderiv ℝ L₂ w v :=
    (h2.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hL₁'c : Continuous fun w ↦ fderiv ℝ L₁ w v :=
    (h1.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hec : Continuous fun w ↦ Real.exp (-(t * L₂ w)) := by fun_prop
  have hI₂ : Integrable fun w ↦ φ w * (fderiv ℝ L₂ w v * Real.exp (-(t * L₂ w))) :=
    (hφ.continuous.mul (hL₂'c.mul hec)).integrable_of_hasCompactSupport hφs.mul_right
  have hI₁ : Integrable fun w ↦ φ w * (fderiv ℝ L₁ w v * Real.exp (-(t * L₂ w))) :=
    (hφ.continuous.mul (hL₁'c.mul hec)).integrable_of_hasCompactSupport hφs.mul_right
  have hsub : ∫ w, φ w * (fderiv ℝ (fun w ↦ L₂ w - L₁ w) w v * Real.exp (-(t * L₂ w)))
      = (∫ w, φ w * (fderiv ℝ L₂ w v * Real.exp (-(t * L₂ w))))
        - ∫ w, φ w * (fderiv ℝ L₁ w v * Real.exp (-(t * L₂ w))) := by
    rw [← integral_sub hI₂ hI₁]
    congr 1
    funext w
    have hd : fderiv ℝ (fun w ↦ L₂ w - L₁ w) w = fderiv ℝ L₂ w - fderiv ℝ L₁ w :=
      ((h2.differentiable (by simp) w).hasFDerivAt.sub
        (h1.differentiable (by simp) w).hasFDerivAt).fderiv
    rw [hd]
    simp only [sub_apply]
    ring
  have hassoc : ∀ L : (ι → ℝ) → ℝ, ∫ w, φ w * fderiv ℝ L₁ w v * Real.exp (-(t * L w))
      = ∫ w, φ w * (fderiv ℝ L₁ w v * Real.exp (-(t * L w))) := fun L ↦ by
    congr 1
    funext w
    ring
  rw [hsub, hassoc L₂, hassoc L₁]
  field_simp
  ring

/-- **Singular normalized identifiability from a class of tests.** The
projective hypothesis is only needed for tests in a class `S` that contains,
for every smooth compactly supported `ψ` and coordinate `i`, the two
observables `∂_i(ψ ∂_i(L₂ - L₁))` and `ψ ∂_i(L₂ - L₁) ∂_i L₁`. -/
theorem normalized_families_force_germ_eq_at_of_tests [DecidableEq ι]
    {L₁ L₂ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p)
    (hp1 : L₁ p = 0) (hp2 : L₂ p = 0) {C : ℝ → ℝ}
    (S : ((ι → ℝ) → ℝ) → Prop)
    (hS₁ : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ i : ι,
      S fun w ↦ fderiv ℝ (fun w ↦ ψ w * fderiv ℝ (fun w ↦ L₂ w - L₁ w) w (Pi.single i 1)) w
        (Pi.single i 1))
    (hS₂ : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ i : ι,
      S fun w ↦ ψ w * fderiv ℝ (fun w ↦ L₂ w - L₁ w) w (Pi.single i 1) *
        fderiv ℝ L₁ w (Pi.single i 1))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, S φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  set g : (ι → ℝ) → ℝ := fun w ↦ L₂ w - L₁ w with hg_def
  have hgs : ContDiff ℝ ∞ g := h2.sub h1
  have hgd : Differentiable ℝ g := hgs.differentiable (by simp)
  have hgp : g p = 0 := by simp [hg_def, hp1, hp2]
  have hgA : AnalyticAt ℝ g p := hA2.sub hA1
  have hmin1 : IsLocalMin L₁ p := Eventually.of_forall fun w ↦ hp1 ▸ hL1 w
  have hmin2 : IsLocalMin L₂ p := Eventually.of_forall fun w ↦ hp2 ▸ hL2 w
  have hfg : fderiv ℝ g p = 0 := by
    have hd : fderiv ℝ g p = fderiv ℝ L₂ p - fderiv ℝ L₁ p :=
      ((h2.differentiable (by simp) p).hasFDerivAt.sub
        (h1.differentiable (by simp) p).hasFDerivAt).fderiv
    rw [hd, hmin1.fderiv_eq_zero, hmin2.fderiv_eq_zero, sub_zero]
  have hderiv : ∀ i : ι, ∀ᶠ w in 𝓝 p, fderiv ℝ g w (Pi.single i 1) = 0 := by
    intro i
    set v : ι → ℝ := Pi.single i 1 with hv_def
    have hac : Continuous fun w ↦ fderiv ℝ g w v :=
      (hgs.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    have has : ContDiff ℝ ∞ fun w ↦ fderiv ℝ g w v :=
      (contDiff_infty_iff_fderiv.mp hgs).2.clm_apply contDiff_const
    have haA : AnalyticAt ℝ (fun w ↦ fderiv ℝ g w v) p :=
      ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hgA.fderiv
    have hap : fderiv ℝ g p v = 0 := by rw [hfg]; rfl
    refine analytic_square_weight_eq_zero_near h2.continuous hL2 hp2 hA2.contDiffAt
      hac haA hap ?_
    intro ψ hψ hψs
    have hR₁ := hfam _ (hS₁ ψ hψ hψs i)
    have hR₂ := hfam _ (hS₂ ψ hψ hψs i)
    have hcanc := superPoly_integral_fderiv_sub_mul_exp_of_pair h1 h2
      (φ := fun w ↦ ψ w * fderiv ℝ g w v) (hψ.mul has) hψs.mul_right v hR₁ hR₂
    refine hcanc.congr (Eventually.of_forall fun t ↦ ?_)
    beta_reduce
    congr 1
    funext w
    simp only [hg_def]
    ring
  have := eventually_eq_zero_of_fderiv_single_eventually_zero hgd hgp hderiv
  filter_upwards [this] with w hw
  simp only [hg_def] at hw
  linarith

/-- **Class form.** A class of tests closed under the coordinate derivatives
`φ ↦ ∂_i φ` and under multiplication by `∂_i L₁`, and containing `ψ ∂_i(L₂ - L₁)`
for every smooth compactly supported `ψ`, suffices. -/
theorem normalized_families_force_germ_eq_at_of_closed_tests [DecidableEq ι]
    {L₁ L₂ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p)
    (hp1 : L₁ p = 0) (hp2 : L₂ p = 0) {C : ℝ → ℝ}
    (S : ((ι → ℝ) → ℝ) → Prop)
    (hSderiv : ∀ φ, S φ → ∀ i : ι, S fun w ↦ fderiv ℝ φ w (Pi.single i 1))
    (hSmul : ∀ φ, S φ → ∀ i : ι, S fun w ↦ φ w * fderiv ℝ L₁ w (Pi.single i 1))
    (hSgen : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ i : ι,
      S fun w ↦ ψ w * fderiv ℝ (fun w ↦ L₂ w - L₁ w) w (Pi.single i 1))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, S φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w :=
  normalized_families_force_germ_eq_at_of_tests h1 h2 hL1 hL2 hA1 hA2 hp1 hp2 S
    (fun ψ hψ hψs i ↦ hSderiv _ (hSgen ψ hψ hψs i) i)
    (fun ψ hψ hψs i ↦ hSmul _ (hSgen ψ hψ hψs i) i) hfam

/-- **Locus form** of `normalized_families_force_germ_eq_at_of_tests`. -/
theorem normalized_families_force_eq_near_of_tests [DecidableEq ι]
    {L₁ L₂ : (ι → ℝ) → ℝ} {W₀ : Set (ι → ℝ)}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p ∈ W₀, AnalyticAt ℝ L₁ p) (hA2 : ∀ p ∈ W₀, AnalyticAt ℝ L₂ p)
    (hzero1 : ∀ p ∈ W₀, L₁ p = 0) (hzero2 : ∀ p ∈ W₀, L₂ p = 0) {C : ℝ → ℝ}
    (S : ((ι → ℝ) → ℝ) → Prop)
    (hS₁ : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ i : ι,
      S fun w ↦ fderiv ℝ (fun w ↦ ψ w * fderiv ℝ (fun w ↦ L₂ w - L₁ w) w (Pi.single i 1)) w
        (Pi.single i 1))
    (hS₂ : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ i : ι,
      S fun w ↦ ψ w * fderiv ℝ (fun w ↦ L₂ w - L₁ w) w (Pi.single i 1) *
        fderiv ℝ L₁ w (Pi.single i 1))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, S φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w := by
  have h : ∀ p ∈ W₀, ∃ V : Set (ι → ℝ),
      (∀ w ∈ V, L₁ w = L₂ w) ∧ IsOpen V ∧ p ∈ V := fun p hp ↦
    eventually_nhds_iff.mp
      (normalized_families_force_germ_eq_at_of_tests h1 h2 hL1 hL2 (hA1 p hp) (hA2 p hp)
        (hzero1 p hp) (hzero2 p hp) S hS₁ hS₂ hfam)
  choose V hVeq hVopen hVmem using h
  refine ⟨⋃ p, ⋃ hp : p ∈ W₀, V p hp, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun p ↦ isOpen_iUnion fun hp ↦ hVopen p hp
  · exact fun p hp ↦ Set.mem_iUnion₂.mpr ⟨p, hp, hVmem p hp⟩
  · intro w hw
    obtain ⟨p, hp, hwV⟩ := Set.mem_iUnion₂.mp hw
    exact hVeq p hp w hwV

/-- **The form with the normalization, from a class of tests.** Normalized
expectations against a common window `χ` agreeing beyond all orders on the
class `S` force `L₁ = L₂` near the common analytic zeros. -/
theorem normalized_expectations_force_eq_near_of_tests [DecidableEq ι]
    {L₁ L₂ χ : (ι → ℝ) → ℝ} {W₀ : Set (ι → ℝ)}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p ∈ W₀, AnalyticAt ℝ L₁ p) (hA2 : ∀ p ∈ W₀, AnalyticAt ℝ L₂ p)
    (hzero1 : ∀ p ∈ W₀, L₁ p = 0) (hzero2 : ∀ p ∈ W₀, L₂ p = 0)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₂ w)))
    (S : ((ι → ℝ) → ℝ) → Prop)
    (hS₁ : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ i : ι,
      S fun w ↦ fderiv ℝ (fun w ↦ ψ w * fderiv ℝ (fun w ↦ L₂ w - L₁ w) w (Pi.single i 1)) w
        (Pi.single i 1))
    (hS₂ : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ i : ι,
      S fun w ↦ ψ w * fderiv ℝ (fun w ↦ L₂ w - L₁ w) w (Pi.single i 1) *
        fderiv ℝ L₁ w (Pi.single i 1))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, S φ →
      SuperPoly fun t ↦
        (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
        - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w)))) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w := by
  set Z₁ : ℝ → ℝ := fun t ↦ ∫ w, χ w * Real.exp (-(t * L₁ w)) with hZ₁_def
  set Z₂ : ℝ → ℝ := fun t ↦ ∫ w, χ w * Real.exp (-(t * L₂ w)) with hZ₂_def
  have hχint : Integrable χ := hχc.integrable_of_hasCompactSupport hχs
  have hZ₂le : ∀ t : ℝ, 0 ≤ t → Z₂ t ≤ ∫ w, χ w := by
    intro t ht
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun w ↦ mul_nonneg (hχ0 w) (Real.exp_nonneg _)
    · exact hχint
    · refine Eventually.of_forall fun w ↦ ?_
      have : Real.exp (-(t * L₂ w)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg ht (hL2 w))
      calc χ w * Real.exp (-(t * L₂ w)) ≤ χ w * 1 :=
            mul_le_mul_of_nonneg_left this (hχ0 w)
        _ = χ w := mul_one _
  have hZ₂O : Z₂ =O[atTop] fun _ : ℝ ↦ (1 : ℝ) := by
    refine IsBigO.of_bound (∫ w, χ w) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (hZ2 t), norm_one, mul_one]
    exact hZ₂le t ht
  refine normalized_families_force_eq_near_of_tests h1 h2 hL1 hL2 hA1 hA2 hzero1 hzero2
    (C := fun t ↦ Z₂ t / Z₁ t) S hS₁ hS₂ ?_
  intro φ hφ
  have hφ' := (hfam φ hφ).bounded_mul hZ₂O
  refine hφ'.congr (Eventually.of_forall fun t ↦ ?_)
  have h1t : Z₁ t ≠ 0 := (hZ1 t).ne'
  have h2t : Z₂ t ≠ 0 := (hZ2 t).ne'
  simp only [hZ₁_def, hZ₂_def] at h1t h2t ⊢
  field_simp

end Laplace
