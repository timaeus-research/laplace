/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.HomogeneousTaylor
import Laplace.Multi.PackageConstructor

/-!
# Realising a kernel direction by a pair of certified losses

`SufficientFamilies` shows that a degree-`k` homogeneous polynomial `Q` in
the kernel of a family's observation operator is invisible to that family
at the leading rate, *for any two certified losses whose degree-`k` Taylor
difference is `Q`*. This file supplies such a pair: `L₀ = qform H / 2` and
`L₁ = L₀ + Q`, both with certified `HigherLaplaceDomain k _ H` packages,
equal jets below `k`, different degree-`k` tensors, and Taylor difference
exactly `Q` (`exists_pair_of_kernel_direction`). Combined with
`finite_family_leading_rate_blind` this gives the existence form of the
finite-family obstruction (`exists_pair_finite_family_blind`): in `d ≥ 2`,
for every family of `n` tests and every `k ≥ max n 3`, there are two
certified losses with different `k`-jets whose data at every test of the
family agree to `o(q^(k-2))`.

The packages are built from `LocalQuadraticApprox` (quadratic Peano
remainder `Q = o(‖y‖²)`, from the homogeneous bound `|Q y| ≤ M ‖y‖^k`) and
its local lower bound, with Taylor remainder `|Q y| ≤ M ‖y‖^k` after the
Taylor terms of `qform H / 2` and `Q` are read off from
`HomogeneousTaylor`.
-/

open Asymptotics Filter MeasureTheory
open scoped Topology ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-- A continuous function homogeneous of degree `k` is bounded by `M ‖y‖^k`. -/
theorem exists_abs_le_of_isHomogeneous {Q : EuclidD d → ℝ} (hQc : Continuous Q)
    {k : ℕ} (hk : 0 < k) (hhom : IsHomogeneousOfDegree k Q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : EuclidD d, |Q y| ≤ M * ‖y‖ ^ k := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : EuclidD d) 1).exists_bound_of_continuousOn
    hQc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y ↦ ?_⟩
  by_cases hy : y = 0
  · subst hy
    have : Q 0 = 0 := by
      have := hhom 0 0
      rwa [zero_smul, zero_pow hk.ne', zero_mul] at this
    simp [this, zero_pow hk.ne']
  · have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set u : EuclidD d := ‖y‖⁻¹ • y with hu
    have hu1 : u ∈ Metric.sphere (0 : EuclidD d) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, hu, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hn.ne']
    have hyu : y = ‖y‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hQy : Q y = ‖y‖ ^ k * Q u := by
      conv_lhs => rw [hyu]
      exact hhom _ _
    rw [hQy, abs_mul, abs_of_pos (pow_pos hn k), mul_comm]
    have := hM u hu1
    rw [Real.norm_eq_abs] at this
    exact mul_le_mul_of_nonneg_right (this.trans (le_max_left _ _)) (pow_pos hn k).le

/-- Taylor terms are additive. -/
theorem taylorHomogeneousTerm_add {f g : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (j : ℕ) :
    taylorHomogeneousTerm j (fun x ↦ f x + g x) =
      fun x ↦ taylorHomogeneousTerm j f x + taylorHomogeneousTerm j g x := by
  funext x
  unfold taylorHomogeneousTerm
  have hsum : (fun x ↦ f x + g x) = f + g := by
    funext x
    simp
  rw [hsum, iteratedFDeriv_add_apply (hf.contDiffAt.of_le (natCast_le_infty j))
    (hg.contDiffAt.of_le (natCast_le_infty j)), add_apply]
  ring

/-- The half quadratic form. -/
noncomputable def halfQform (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) : ℝ :=
  qform H x / 2

theorem contDiff_halfQform (H : Matrix (Fin d) (Fin d) ℝ) : ContDiff ℝ ∞ (halfQform H) :=
  (contDiff_qform H).div_const 2

theorem isHomogeneousOfDegree_halfQform (H : Matrix (Fin d) (Fin d) ℝ) :
    IsHomogeneousOfDegree 2 (halfQform H) := by
  intro a x
  unfold halfQform
  rw [isHomogeneousOfDegree_qform H a x]
  ring

theorem halfQform_zero (H : Matrix (Fin d) (Fin d) ℝ) : halfQform H 0 = 0 := by
  unfold halfQform
  rw [qform_zero]
  simp

/-- The Taylor terms below order `k > 2` of `halfQform H + Q` sum to `halfQform H`
when `Q` is smooth and homogeneous of degree `k`. -/
theorem sum_taylor_halfQform_add {H : Matrix (Fin d) (Fin d) ℝ} {Q : EuclidD d → ℝ}
    (hQ : ContDiff ℝ ∞ Q) {k : ℕ} (hk : 2 < k) (hhom : IsHomogeneousOfDegree k Q)
    (y : EuclidD d) :
    ∑ j ∈ Finset.range k, taylorHomogeneousTerm j (fun x ↦ halfQform H x + Q x) y =
      halfQform H y := by
  have h : ∀ j ∈ Finset.range k, taylorHomogeneousTerm j (fun x ↦ halfQform H x + Q x) y =
      if j = 2 then halfQform H y else 0 := by
    intro j hj
    have hjk : j ≠ k := (Finset.mem_range.mp hj).ne
    rw [taylorHomogeneousTerm_add (contDiff_halfQform H) hQ,
      taylorHomogeneousTerm_of_isHomogeneous (contDiff_halfQform H)
        (isHomogeneousOfDegree_halfQform H),
      taylorHomogeneousTerm_of_isHomogeneous hQ hhom, if_neg hjk]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (Finset.range k) 2]
  simp [Finset.mem_range.mpr hk]

/-- The Taylor terms below order `k > 2` of `halfQform H` sum to itself. -/
theorem sum_taylor_halfQform {H : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} (hk : 2 < k) (y : EuclidD d) :
    ∑ j ∈ Finset.range k, taylorHomogeneousTerm j (halfQform H) y = halfQform H y := by
  have h : ∀ j ∈ Finset.range k, taylorHomogeneousTerm j (halfQform H) y =
      if j = 2 then halfQform H y else 0 := by
    intro j _
    rw [taylorHomogeneousTerm_of_isHomogeneous (contDiff_halfQform H)
      (isHomogeneousOfDegree_halfQform H)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (Finset.range k) 2]
  simp [Finset.mem_range.mpr hk]

/-- **The certified package for `halfQform H + Q`**, `Q` smooth, homogeneous of
degree `k > 2`, bounded by `M ‖y‖^k`. (Take `Q = 0` for the base loss.) -/
noncomputable def higherLaplaceDomain_halfQform_add {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q) {k : ℕ} (hk : 2 < k)
    (hhom : IsHomogeneousOfDegree k Q) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y : EuclidD d, |Q y| ≤ M * ‖y‖ ^ k) :
    HigherLaplaceDomain k (fun x ↦ halfQform H x + Q x) H := by
  classical
  set L : EuclidD d → ℝ := fun x ↦ halfQform H x + Q x with hL_def
  have hLs : ContDiff ℝ ∞ L := (contDiff_halfQform H).add hQ
  have hQ0 : Q 0 = 0 := by
    have := hhom 0 0
    rwa [zero_smul, zero_pow (by omega), zero_mul] at this
  have hL0 : L 0 = 0 := by simp [hL_def, halfQform_zero, hQ0]
  -- the quadratic package
  have hpeano : (fun y : EuclidD d ↦ L y - L 0 - qform H y / 2) =o[𝓝 0] fun y ↦ ‖y‖ ^ 2 := by
    have heq : (fun y : EuclidD d ↦ L y - L 0 - qform H y / 2) = Q := by
      funext y
      simp only [hL_def, halfQform, qform_zero, hQ0]
      ring
    rw [heq]
    have hbig : Q =O[𝓝 (0 : EuclidD d)] fun y ↦ ‖y‖ ^ k := by
      refine IsBigO.of_bound M (Eventually.of_forall fun y ↦ ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg y) k)]
      exact hM y
    exact hbig.trans_isLittleO (isLittleO_norm_pow_norm_pow (by omega))
  let A : LocalQuadraticApprox L H :=
    { hH_posDef := hH
      lambda := (qform_coercive hH).choose
      lambda_pos := (qform_coercive hH).choose_spec.1
      qform_lower := (qform_coercive hH).choose_spec.2
      quadratic_peano := hpeano }
  refine
    let δ := A.exists_local_lower_bound.choose
    let c := A.exists_local_lower_bound.choose_spec.choose
    ?_
  have hδ : 0 < δ := A.exists_local_lower_bound.choose_spec.choose_spec.1
  have hc : 0 < c := A.exists_local_lower_bound.choose_spec.choose_spec.2.1
  have hlow : ∀ q : ℝ, ∀ x : EuclidD d, 0 < q → ‖q • x‖ ≤ δ →
      c * ‖x‖ ^ 2 ≤ (L (q • x) - L 0) / q ^ 2 :=
    A.exists_local_lower_bound.choose_spec.choose_spec.2.2
  exact
    { toLocalQuadraticApprox := A
      U := Metric.ball (0 : EuclidD d) δ
      measurableSet_U := measurableSet_ball
      delta := δ
      delta_pos := hδ
      ball_subset_U := Set.Subset.rfl
      c := c
      c_pos := hc
      rescaled_lower := by
        intro q x hq hmem
        refine hlow q x hq ?_
        have := Metric.mem_ball.mp hmem
        rw [dist_zero_right] at this
        exact this.le
      measurable_L := hLs.continuous.measurable
      contDiff_k := hLs.of_le (natCast_le_infty k)
      taylorRadius := δ
      taylorRadius_pos := hδ
      taylorBall_subset := Set.Subset.rfl
      taylorRemainderConst := M
      taylorRemainderConst_nonneg := hM0
      taylorRemainder_bound := by
        intro y _
        rw [sum_taylor_halfQform_add hQ hk hhom]
        have : L y - halfQform H y = Q y := by simp [hL_def]
        rw [this]
        exact hM y }

/-- **A kernel direction is realised by two certified losses.** For `k > 2`,
positive definite `H`, and a nonzero degree-`k` homogeneous polynomial `Q`,
the losses `L₁ = qform H/2 + Q` and `L₂ = qform H/2` carry certified packages,
have equal jets below `k`, different degree-`k` tensors, and degree-`k` Taylor
difference exactly `Q`. -/
theorem exists_pair_of_kernel_direction {k : ℕ} (hk : 2 < k)
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {Q : EuclidD d → ℝ} (hQ : Q ∈ homogPolySpan d k) (hQne : Q ≠ 0) :
    ∃ (L₁ L₂ : EuclidD d → ℝ) (_ : HigherLaplaceDomain k L₁ H) (_ : HigherLaplaceDomain k L₂ H),
      (∀ j < k, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0) ∧
      iteratedFDeriv ℝ k L₁ 0 ≠ iteratedFDeriv ℝ k L₂ 0 ∧
      (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x) = Q := by
  have hQs : ContDiff ℝ ∞ Q := contDiff_of_mem_homogPolySpan hQ
  have hhom : IsHomogeneousOfDegree k Q := homogPolySpan_isHomogeneous hQ
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_isHomogeneous hQs.continuous (by omega) hhom
  have hzero_hom : IsHomogeneousOfDegree k (fun _ : EuclidD d ↦ (0 : ℝ)) := by
    intro a x
    simp
  have hzero_bound : ∀ y : EuclidD d, |(fun _ : EuclidD d ↦ (0 : ℝ)) y| ≤ 0 * ‖y‖ ^ k := by
    intro y
    simp
  let A₁ := higherLaplaceDomain_halfQform_add hH hQs hk hhom hM0 hM
  let A₂ := higherLaplaceDomain_halfQform_add hH contDiff_const hk hzero_hom le_rfl hzero_bound
  have hadd : ∀ j, iteratedFDeriv ℝ j (fun x ↦ halfQform H x + Q x) 0 =
      iteratedFDeriv ℝ j (halfQform H) 0 + iteratedFDeriv ℝ j Q 0 := by
    intro j
    have hsum : (fun x ↦ halfQform H x + Q x) = halfQform H + Q := by
      funext x
      simp
    rw [hsum, iteratedFDeriv_add_apply
      ((contDiff_halfQform H).contDiffAt.of_le (natCast_le_infty j))
      (hQs.contDiffAt.of_le (natCast_le_infty j))]
  have hL₂ : (fun x ↦ halfQform H x + (fun _ : EuclidD d ↦ (0 : ℝ)) x) = halfQform H := by
    funext x
    simp
  refine ⟨fun x ↦ halfQform H x + Q x, fun x ↦ halfQform H x + (fun _ ↦ (0 : ℝ)) x, A₁, A₂,
    ?_, ?_, ?_⟩
  · intro j hj
    rw [hL₂, hadd, iteratedFDeriv_zero_of_isHomogeneous hQs hhom hj.ne, add_zero]
  · rw [hL₂, hadd]
    intro heq
    have hk0 : iteratedFDeriv ℝ k Q 0 = 0 := by
      have := congrArg (fun T ↦ T - iteratedFDeriv ℝ k (halfQform H) 0) heq
      simpa using this
    apply hQne
    funext x
    have hd := iteratedFDeriv_diag_of_isHomogeneous hQs hhom x
    rw [hk0, zero_apply] at hd
    have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simpa [hfac] using hd.symm
  · funext x
    rw [hL₂, taylorHomogeneousTerm_add (contDiff_halfQform H) hQs,
      taylorHomogeneousTerm_of_isHomogeneous hQs hhom, if_pos rfl]
    simp

/-- **Existence form of the finite-family obstruction.** In `d ≥ 2`, for every
family of `n` continuous polynomially growing tests and every `k > 2` with
`n ≤ k`, there are two certified losses with equal jets below `k` and different
degree-`k` tensors whose rescaled moments at every test of the family agree to
`o(q^(k-2))`. -/
theorem exists_pair_finite_family_blind (hd : 2 ≤ d) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {n : ℕ} (φ : Fin n → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    {k : ℕ} (hk : 2 < k) (hnk : n ≤ k) :
    ∃ (L₁ L₂ : EuclidD d → ℝ) (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H),
      (∀ j < k, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0) ∧
      iteratedFDeriv ℝ k L₁ 0 ≠ iteratedFDeriv ℝ k L₂ 0 ∧
      ∀ i, (fun q : ℝ ↦ A₁.rescaledMoment (φ i) q - A₂.rescaledMoment (φ i) q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2) := by
  obtain ⟨Q, hQ, hQne, hblind⟩ := finite_family_leading_rate_blind hd hH φ hφc hφg hk hnk
  obtain ⟨L₁, L₂, A₁, A₂, hlower, hne, hdiff⟩ := exists_pair_of_kernel_direction hk hH hQ hQne
  exact ⟨L₁, L₂, A₁, A₂, hlower, hne, hblind A₁ A₂ hlower hdiff⟩

end Laplace.Multi
