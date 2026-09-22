/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GibbsRotation
import Laplace.Sampler.FrobeniusBridge

/-!
# The ambient mean and covariance of the rotated oscillator

`GibbsRotation` transported E2 to the note's frame *along the columns of `Q`*. The note also reports
the ambient mean shift and "the relative Frobenius error of the whole covariance", which are linear
combinations of the projected moments (`w − c = Q A(w)`):

* bilinearity of the Gibbs moments under integrability (`gibbsExpectation_finsetSum`,
  `gibbsExpectation_const_mul`, `gibbsExpectation_add_of_integrable`,
  `gibbsExpectation_const_of_ne_zero`,
  `gibbsCov_finsetSum_left`, `gibbsCov_const_mul_left`, `gibbsCov_comm`, `gibbsCov_const_add_left`,
  `gibbsCov_linear_combination`);
* integrability transport through the frame change (`integrable_comp_affineFrame`) and the
  monomial integrability of the separable oscillator (`integrable_monomial_separableAnharmonic`);
* the ambient moments of the `anharm` potential: `⟨wⱼ⟩ = cⱼ + ∑ᵢ Qⱼᵢ ⟨uᵢ⟩`
  (`gibbsExpectation_coord_rotatedAnharmonic`, `rotatedAnharmonic_ambient_mean_asymptotic`) and
  `Cov_w[wⱼ, wₖ] = ∑ᵢ Qⱼᵢ Qₖᵢ Var_{ℓᵢ}` (`gibbsCov_coord_rotatedAnharmonic`), i.e.
  `Cov_w = Q diag(Var) Qᵀ` (`gibbsCovMatrix_rotatedAnharmonic`);
* E2's first panel in Frobenius form (`frobenius_rel_laplace_rotatedAnharmonic`): the relative
  Frobenius error of the Laplace covariance `P⁻¹ = Q diag(1/(λᵢt)) Qᵀ` against the exact covariance
  satisfies `t² ‖Cov − P⁻¹‖_F² / ‖P⁻¹‖_F² → (a² − ½)²`, independently of the spectrum.
-/

open MeasureTheory Filter Topology Matrix Laplace.OneD

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-! ### Bilinearity under integrability -/

section Bilinear

variable (L : (ι → ℝ) → ℝ) (t : ℝ)

theorem gibbsExpectation_finsetSum {κ : Type*} (s : Finset κ) (φ : κ → (ι → ℝ) → ℝ)
    (hφ : ∀ k ∈ s, Integrable (fun w => φ k w * Real.exp (-(t * L w)))) :
    gibbsExpectation L t (fun w => ∑ k ∈ s, φ k w) = ∑ k ∈ s, gibbsExpectation L t (φ k) := by
  unfold gibbsExpectation
  rw [← Finset.sum_div, ← integral_finsetSum s hφ]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [Finset.sum_mul]

theorem gibbsExpectation_const_mul (a : ℝ) (φ : (ι → ℝ) → ℝ) :
    gibbsExpectation L t (fun w => a * φ w) = a * gibbsExpectation L t φ := by
  unfold gibbsExpectation
  rw [← mul_div_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  ring

theorem gibbsExpectation_add_of_integrable (φ ψ : (ι → ℝ) → ℝ)
    (hφ : Integrable (fun w => φ w * Real.exp (-(t * L w))))
    (hψ : Integrable (fun w => ψ w * Real.exp (-(t * L w)))) :
    gibbsExpectation L t (fun w => φ w + ψ w) =
      gibbsExpectation L t φ + gibbsExpectation L t ψ := by
  unfold gibbsExpectation
  rw [← add_div, ← integral_add hφ hψ]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  ring

theorem gibbsExpectation_const_of_ne_zero (a : ℝ) (hZ : partitionFunction L t ≠ 0) :
    gibbsExpectation L t (fun _ => a) = a := by
  have hZ' : (∫ w : ι → ℝ, Real.exp (-(t * L w))) ≠ 0 := hZ
  unfold gibbsExpectation partitionFunction
  rw [integral_const_mul, mul_div_assoc, div_self hZ', mul_one]

theorem gibbsCov_comm (φ ψ : (ι → ℝ) → ℝ) : gibbsCov L t φ ψ = gibbsCov L t ψ φ := by
  unfold gibbsCov
  have : (fun w => φ w * ψ w) = fun w => ψ w * φ w := by
    funext w
    ring
  rw [this, mul_comm (gibbsExpectation L t φ)]

theorem gibbsCov_finsetSum_left {κ : Type*} (s : Finset κ) (φ : κ → (ι → ℝ) → ℝ)
    (ψ : (ι → ℝ) → ℝ)
    (hφ : ∀ k ∈ s, Integrable (fun w => φ k w * Real.exp (-(t * L w))))
    (hφψ : ∀ k ∈ s, Integrable (fun w => φ k w * ψ w * Real.exp (-(t * L w)))) :
    gibbsCov L t (fun w => ∑ k ∈ s, φ k w) ψ = ∑ k ∈ s, gibbsCov L t (φ k) ψ := by
  unfold gibbsCov
  have h1 := gibbsExpectation_finsetSum L t s (fun k w => φ k w * ψ w) hφψ
  have h2 := gibbsExpectation_finsetSum L t s φ hφ
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← h2, ← h1]
  congr 2
  funext w
  rw [Finset.sum_mul]

theorem gibbsCov_const_mul_left (a : ℝ) (φ ψ : (ι → ℝ) → ℝ) :
    gibbsCov L t (fun w => a * φ w) ψ = a * gibbsCov L t φ ψ := by
  unfold gibbsCov
  have : (fun w => a * φ w * ψ w) = fun w => a * (φ w * ψ w) := by
    funext w
    ring
  rw [this, gibbsExpectation_const_mul, gibbsExpectation_const_mul]
  ring

/-- A constant shift of an observable does not change its covariances. -/
theorem gibbsCov_const_add_left (a : ℝ) (φ ψ : (ι → ℝ) → ℝ) (hZ : partitionFunction L t ≠ 0)
    (hL : Integrable (fun w => Real.exp (-(t * L w))))
    (hφ : Integrable (fun w => φ w * Real.exp (-(t * L w))))
    (hψ : Integrable (fun w => ψ w * Real.exp (-(t * L w))))
    (hφψ : Integrable (fun w => φ w * ψ w * Real.exp (-(t * L w)))) :
    gibbsCov L t (fun w => a + φ w) ψ = gibbsCov L t φ ψ := by
  unfold gibbsCov
  have h1 : (fun w => (a + φ w) * ψ w) = fun w => a * ψ w + φ w * ψ w := by
    funext w
    ring
  have hc : Integrable (fun w => (fun _ : ι → ℝ => a) w * Real.exp (-(t * L w))) :=
    hL.const_mul a
  have haψ : Integrable (fun w => a * ψ w * Real.exp (-(t * L w))) :=
    (hψ.const_mul a).congr (Eventually.of_forall fun w => by ring)
  rw [h1, gibbsExpectation_add_of_integrable L t _ _ haψ hφψ, gibbsExpectation_const_mul,
    gibbsExpectation_add_of_integrable L t (fun _ => a) φ hc hφ,
    gibbsExpectation_const_of_ne_zero L t a hZ]
  ring

/-- Constant shifts of both observables do not change the covariance. -/
theorem gibbsCov_const_add_both (a b : ℝ) (φ ψ : (ι → ℝ) → ℝ) (hZ : partitionFunction L t ≠ 0)
    (hL : Integrable (fun w => Real.exp (-(t * L w))))
    (hφ : Integrable (fun w => φ w * Real.exp (-(t * L w))))
    (hψ : Integrable (fun w => ψ w * Real.exp (-(t * L w))))
    (hφψ : Integrable (fun w => φ w * ψ w * Real.exp (-(t * L w)))) :
    gibbsCov L t (fun w => a + φ w) (fun w => b + ψ w) = gibbsCov L t φ ψ := by
  have hψ' : Integrable (fun w => (b + ψ w) * Real.exp (-(t * L w))) :=
    ((hL.const_mul b).add hψ).congr (Eventually.of_forall fun w => by
      simp only [Pi.add_apply]
      ring)
  have hφψ' : Integrable (fun w => φ w * (b + ψ w) * Real.exp (-(t * L w))) :=
    ((hφ.const_mul b).add hφψ).congr (Eventually.of_forall fun w => by
      simp only [Pi.add_apply]
      ring)
  have hψφ : Integrable (fun w => ψ w * φ w * Real.exp (-(t * L w))) :=
    hφψ.congr (Eventually.of_forall fun w => by ring)
  rw [gibbsCov_const_add_left L t a φ _ hZ hL hφ hψ' hφψ', gibbsCov_comm,
    gibbsCov_const_add_left L t b ψ φ hZ hL hψ hφ hψφ, gibbsCov_comm]

/-- **Bilinearity**: the covariance of two finite linear combinations. -/
theorem gibbsCov_linear_combination {κ : Type*} [Fintype κ] (X : κ → (ι → ℝ) → ℝ) (a b : κ → ℝ)
    (hX : ∀ i, Integrable (fun w => X i w * Real.exp (-(t * L w))))
    (hXX : ∀ i j, Integrable (fun w => X i w * X j w * Real.exp (-(t * L w)))) :
    gibbsCov L t (fun w => ∑ i, a i * X i w) (fun w => ∑ j, b j * X j w) =
      ∑ i, ∑ j, a i * b j * gibbsCov L t (X i) (X j) := by
  have haX : ∀ i, Integrable (fun w => a i * X i w * Real.exp (-(t * L w))) := fun i =>
    ((hX i).const_mul (a i)).congr (Eventually.of_forall fun w => by ring)
  have hbX : ∀ j, Integrable (fun w => b j * X j w * Real.exp (-(t * L w))) := fun j =>
    ((hX j).const_mul (b j)).congr (Eventually.of_forall fun w => by ring)
  have hmix : ∀ i, Integrable (fun w => a i * X i w * (∑ j, b j * X j w) *
      Real.exp (-(t * L w))) := fun i =>
    (integrable_finsetSum Finset.univ fun j _ => (hXX i j).const_mul (a i * b j)).congr
      (Eventually.of_forall fun w => by
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring)
  rw [gibbsCov_finsetSum_left L t Finset.univ (fun i w => a i * X i w) _ (fun i _ => haX i)
    (fun i _ => hmix i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gibbsCov_const_mul_left, gibbsCov_comm, gibbsCov_finsetSum_left L t Finset.univ
    (fun j w => b j * X j w) _ (fun j _ => hbX j) (fun j _ =>
      ((hXX j i).const_mul (b j)).congr (Eventually.of_forall fun w => by ring)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gibbsCov_const_mul_left, gibbsCov_comm L t (X j) (X i)]
  ring

end Bilinear

/-! ### Integrability transport -/

section Transport

variable [DecidableEq ι] {lam alpha gamma : ι → ℝ}

theorem integrable_comp_affineFrame {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (g : (ι → ℝ) → ℝ) (hg : AEStronglyMeasurable g volume) (hint : Integrable g) :
    Integrable (fun w => g (affineFrame Q c w)) :=
  ((integrable_comp_mulVec_iff Qᵀ (det_transpose_ne_zero_of_orthogonal hQ) g hg).mpr
    hint).comp_sub_right c

omit [DecidableEq ι] in
/-- Every coordinate monomial is integrable against the separable Boltzmann factor. -/
theorem integrable_monomial_separableAnharmonic (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) (e : ι → ℕ) :
    Integrable (fun u : ι → ℝ =>
      (∏ k, u k ^ e k) * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  refine (Integrable.fintype_prod (f := fun k x => x ^ e k *
      Real.exp (-(t * anharmonicPotential (lam k) (alpha k) (gamma k) x)))
    (fun k => integrable_pow_mul_exp_neg_t_anharmonic (e k) (hlam k) (hgamma k) (hdisc k) ht)).congr
    (Eventually.of_forall fun u => ?_)
  simp only [separableAnharmonic, exp_separablePotential, Finset.prod_mul_distrib]

theorem prod_pow_single (u : ι → ℝ) (i : ι) : ∏ k, u k ^ (Pi.single i 1 : ι → ℕ) k = u i := by
  rw [Finset.prod_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

theorem prod_pow_single_add (u : ι → ℝ) (i j : ι) :
    ∏ k, u k ^ (Pi.single i 1 + Pi.single j 1 : ι → ℕ) k = u i * u j := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pow_single]

omit [DecidableEq ι] in
theorem integrable_exp_separableAnharmonic (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ => Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  simpa using integrable_monomial_separableAnharmonic hlam hgamma hdisc ht 0

omit [DecidableEq ι] in
theorem integrable_coord_separableAnharmonic (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) (i : ι) :
    Integrable (fun u : ι → ℝ =>
      u i * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  classical
  simpa only [prod_pow_single] using
    integrable_monomial_separableAnharmonic hlam hgamma hdisc ht (Pi.single i 1)

omit [DecidableEq ι] in
theorem integrable_coord_mul_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (i j : ι) :
    Integrable (fun u : ι → ℝ =>
      u i * u j * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  classical
  refine (integrable_monomial_separableAnharmonic hlam hgamma hdisc ht
    (Pi.single i 1 + Pi.single j 1)).congr (Eventually.of_forall fun u => ?_)
  change (∏ k, u k ^ (Pi.single i 1 + Pi.single j 1 : ι → ℕ) k) * _ = _
  rw [prod_pow_single_add]

variable {Q : Matrix ι ι ℝ}

theorem integrable_exp_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) :
    Integrable (fun w : ι → ℝ => Real.exp (-(t * rotatedAnharmonic Q c lam alpha gamma w))) := by
  have hc := continuous_separableAnharmonic lam alpha gamma
  have hm : AEStronglyMeasurable
      (fun u => Real.exp (-(t * separableAnharmonic lam alpha gamma u))) volume :=
    (by fun_prop : Continuous fun u => Real.exp (-(t * separableAnharmonic lam alpha gamma u)))
      |>.aestronglyMeasurable
  exact integrable_comp_affineFrame hQ c _ hm
    (integrable_exp_separableAnharmonic hlam hgamma hdisc ht)

theorem integrable_coord_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (i : ι) :
    Integrable (fun w : ι → ℝ =>
      affineFrame Q c w i * Real.exp (-(t * rotatedAnharmonic Q c lam alpha gamma w))) := by
  have hc := continuous_separableAnharmonic lam alpha gamma
  have hm : AEStronglyMeasurable
      (fun u : ι → ℝ => u i * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) volume :=
    (by fun_prop : Continuous fun u : ι → ℝ =>
      u i * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) |>.aestronglyMeasurable
  exact integrable_comp_affineFrame hQ c _ hm
    (integrable_coord_separableAnharmonic hlam hgamma hdisc ht i)

theorem integrable_coord_mul_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) (i j : ι) :
    Integrable (fun w : ι → ℝ => affineFrame Q c w i * affineFrame Q c w j *
      Real.exp (-(t * rotatedAnharmonic Q c lam alpha gamma w))) := by
  have hc := continuous_separableAnharmonic lam alpha gamma
  have hm : AEStronglyMeasurable (fun u : ι → ℝ =>
      u i * u j * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) volume :=
    (by fun_prop : Continuous fun u : ι → ℝ =>
      u i * u j * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) |>.aestronglyMeasurable
  exact integrable_comp_affineFrame hQ c _ hm
    (integrable_coord_mul_separableAnharmonic hlam hgamma hdisc ht i j)

theorem partitionFunction_rotatedAnharmonic_pos (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction (rotatedAnharmonic Q c lam alpha gamma) t := by
  have hc := continuous_separableAnharmonic lam alpha gamma
  have hm : AEStronglyMeasurable
      (fun u => Real.exp (-(t * separableAnharmonic lam alpha gamma u))) volume :=
    (by fun_prop : Continuous fun u => Real.exp (-(t * separableAnharmonic lam alpha gamma u)))
      |>.aestronglyMeasurable
  rw [rotatedAnharmonic, partitionFunction_rotated hQ c (separableAnharmonic lam alpha gamma) t hm,
    separableAnharmonic, partitionFunction_separable]
  exact Finset.prod_pos fun i _ => partitionFunction_anharmonic_pos (hlam i) (hgamma i) (hdisc i) ht

end Transport

/-! ### The ambient mean and covariance -/

section Ambient

variable [DecidableEq ι] {lam alpha gamma : ι → ℝ} {Q : Matrix ι ι ℝ}

/-- `wⱼ = cⱼ + ∑ᵢ Qⱼᵢ (Aw)ᵢ`: the ambient coordinates are linear combinations of the new ones. -/
theorem coord_eq_sum_affineFrame (hQ : Qᵀ * Q = 1) (c w : ι → ℝ) (j : ι) :
    w j = c j + ∑ i, Q j i * affineFrame Q c w i := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hv : Q *ᵥ affineFrame Q c w = w - c := by
    unfold affineFrame
    rw [Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
  have h := congrFun hv j
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply] at h
  linarith

/-- **The ambient mean of the `anharm` potential**: `⟨wⱼ⟩ = cⱼ + ∑ᵢ Qⱼᵢ ⟨uᵢ⟩_{ℓᵢ}`. -/
theorem gibbsExpectation_coord_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) (j : ι) :
    gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) =
      c j + ∑ i, Q j i *
        gibbsExpectation (separableAnharmonic lam alpha gamma) t (fun u => u i) := by
  have hZ := (partitionFunction_rotatedAnharmonic_pos hQ c hlam hgamma hdisc ht).ne'
  have hL := integrable_exp_rotatedAnharmonic hQ c hlam hgamma hdisc ht
  have hA := integrable_coord_rotatedAnharmonic hQ c hlam hgamma hdisc ht
  have hQA : ∀ i, Integrable (fun w => Q j i * affineFrame Q c w i *
      Real.exp (-(t * rotatedAnharmonic Q c lam alpha gamma w))) := fun i =>
    ((hA i).const_mul (Q j i)).congr (Eventually.of_forall fun w => by ring)
  have hsum : Integrable (fun w => (∑ i, Q j i * affineFrame Q c w i) *
      Real.exp (-(t * rotatedAnharmonic Q c lam alpha gamma w))) :=
    (integrable_finsetSum Finset.univ fun i _ => hQA i).congr (Eventually.of_forall fun w => by
      simp only [Finset.sum_mul])
  have hfun : (fun w : ι → ℝ => w j) =
      fun w => (fun _ => c j) w + ∑ i, Q j i * affineFrame Q c w i := by
    funext w
    exact coord_eq_sum_affineFrame hQ c w j
  rw [hfun, gibbsExpectation_add_of_integrable _ _ _ _ (hL.const_mul _) hsum,
    gibbsExpectation_const_of_ne_zero _ _ _ hZ,
    gibbsExpectation_finsetSum _ _ Finset.univ _ (fun i _ => hQA i)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gibbsExpectation_const_mul, gibbsExpectation_rotatedAnharmonic_eq hQ c t i]

/-- **The ambient mean shift**: `t(⟨wⱼ⟩ − cⱼ) → −∑ᵢ Qⱼᵢ αᵢ/(2λᵢ²)`. -/
theorem rotatedAnharmonic_ambient_mean_asymptotic (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (j : ι) :
    Tendsto (fun t : ℝ => t * (gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t
        (fun w => w j) - c j)) atTop (𝓝 (∑ i, Q j i * (-alpha i / (2 * lam i ^ 2)))) := by
  have h : Tendsto (fun t : ℝ => ∑ i, Q j i *
      (t * gibbsExpectation (separableAnharmonic lam alpha gamma) t (fun u => u i))) atTop
      (𝓝 (∑ i, Q j i * (-alpha i / (2 * lam i ^ 2)))) :=
    tendsto_finsetSum _ fun i _ =>
      (separableAnharmonic_mean_asymptotic hlam hgamma hdisc i).const_mul (Q j i)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [gibbsExpectation_coord_rotatedAnharmonic hQ c hlam hgamma hdisc ht j, add_sub_cancel_left,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The ambient covariance of the `anharm` potential**: `Cov_w[wⱼ, wₖ] = ∑ᵢ Qⱼᵢ Qₖᵢ Var_{ℓᵢ}`. -/
theorem gibbsCov_coord_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (j k : ι) :
    gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) (fun w => w k) =
      ∑ i, Q j i * Q k i * gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => u i)
        (fun u => u i) := by
  set L := rotatedAnharmonic Q c lam alpha gamma with hLdef
  have hZ := (partitionFunction_rotatedAnharmonic_pos hQ c hlam hgamma hdisc ht).ne'
  have hL := integrable_exp_rotatedAnharmonic hQ c hlam hgamma hdisc ht
  have hA := integrable_coord_rotatedAnharmonic hQ c hlam hgamma hdisc ht
  have hAA := integrable_coord_mul_rotatedAnharmonic hQ c hlam hgamma hdisc ht
  have hQA : ∀ j i, Integrable (fun w => Q j i * affineFrame Q c w i *
      Real.exp (-(t * L w))) := fun j i =>
    ((hA i).const_mul (Q j i)).congr (Eventually.of_forall fun w => by ring)
  have hF : ∀ j, Integrable (fun w => (∑ i, Q j i * affineFrame Q c w i) *
      Real.exp (-(t * L w))) := fun j =>
    (integrable_finsetSum Finset.univ fun i _ => hQA j i).congr (Eventually.of_forall fun w => by
      simp only [Finset.sum_mul])
  have hterm : ∀ j k i i', Integrable (fun w => Q j i * affineFrame Q c w i *
      (Q k i' * affineFrame Q c w i') * Real.exp (-(t * L w))) := fun j k i i' =>
    ((hAA i i').const_mul (Q j i * Q k i')).congr (Eventually.of_forall fun w => by ring)
  have hFF : ∀ j k, Integrable (fun w => (∑ i, Q j i * affineFrame Q c w i) *
      (∑ i, Q k i * affineFrame Q c w i) * Real.exp (-(t * L w))) := fun j k =>
    (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun i' _ =>
      hterm j k i i').congr (Eventually.of_forall fun w => by
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm)
  have hfun : ∀ j, (fun w : ι → ℝ => w j) =
      fun w => c j + ∑ i, Q j i * affineFrame Q c w i := fun j => by
    funext w
    exact coord_eq_sum_affineFrame hQ c w j
  rw [hfun j, hfun k, gibbsCov_const_add_both L t (c j) (c k) _ _ hZ hL (hF j) (hF k) (hFF j k),
    gibbsCov_linear_combination L t (fun i w => affineFrame Q c w i) (Q j) (Q k) hA hAA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun i' _ hi' => ?_) (fun h => absurd (Finset.mem_univ i) h)]
  · rw [gibbsCov_rotatedAnharmonic_eq hQ c t i i]
  · rw [gibbsCov_rotatedAnharmonic hQ c hlam hgamma hdisc ht i i', if_neg (Ne.symm hi'), mul_zero]

/-- **`Cov_w = Q diag(Var) Qᵀ`** as a matrix identity. -/
theorem gibbsCovMatrix_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) :
    Matrix.of (fun j k => gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j)
        (fun w => w k)) =
      Q * diagonal (fun i => gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => u i)
        (fun u => u i)) * Qᵀ := by
  ext j k
  rw [Matrix.of_apply, gibbsCov_coord_rotatedAnharmonic hQ c hlam hgamma hdisc ht j k,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, transpose_apply]
  ring

end Ambient

/-! ### E2's first panel in Frobenius form -/

section Frobenius

variable [DecidableEq ι] [Nonempty ι] {lam alpha gamma : ι → ℝ} {Q : Matrix ι ι ℝ}

/-- **E2, the relative Frobenius error of the Laplace covariance**: for the exact Gibbs measure of
the note's `anharm` potential, with `P⁻¹ = Q diag(1/(λᵢt)) Qᵀ` the Laplace covariance,
`t² ‖Cov − P⁻¹‖_F² / ‖P⁻¹‖_F² → (a² − ½)²`: the relative Frobenius error is `|a² − ½|/t + o(1/t)`
whatever the spectrum (`2.5 × 10⁻²` at `a = ½`, `t = 10`, against the measured `2.7 × 10⁻²`). -/
theorem frobenius_rel_laplace_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c : ι → ℝ) {a : ℝ}
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, gamma i = lam i ^ 2)
    (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3) (ha : a ^ 2 < 3) :
    Tendsto (fun t : ℝ => t ^ 2 *
      ((∑ j, ∑ k, (gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j)
          (fun w => w k) - (Q * diagonal (fun i => 1 / (lam i * t)) * Qᵀ) j k) ^ 2) /
        ∑ j, ∑ k, (Q * diagonal (fun i => 1 / (lam i * t)) * Qᵀ) j k ^ 2)) atTop
      (𝓝 ((a ^ 2 - 1 / 2) ^ 2)) := by
  have hg : ∀ i, 0 < gamma i := fun i => by rw [hgamma i]; exact pow_pos (hlam i) 2
  have hd : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i := fun i => by
    rw [halpha i, hgamma i]
    nlinarith [pow_pos (hlam i) 3]
  have hUU : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  set V : ℝ → ι → ℝ := fun t i => gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => u i)
    (fun u => u i) with hV
  have hD : 0 < ∑ i, (1 / lam i) ^ 2 :=
    Finset.sum_pos (fun i _ => by have := hlam i; positivity) Finset.univ_nonempty
  -- the limit of the eigen-form
  have hlim : Tendsto (fun t : ℝ => (∑ i, (t * (lam i * t * V t i - 1)) ^ 2 * (1 / lam i) ^ 2) /
      ∑ i, (1 / lam i) ^ 2) atTop (𝓝 ((a ^ 2 - 1 / 2) ^ 2)) := by
    have h1 : Tendsto (fun t : ℝ => ∑ i, (t * (lam i * t * V t i - 1)) ^ 2 * (1 / lam i) ^ 2) atTop
        (𝓝 (∑ i, (a ^ 2 - 1 / 2) ^ 2 * (1 / lam i) ^ 2)) :=
      tendsto_finsetSum _ fun i _ =>
        ((separableAnharmonic_var_relative_rate_note hlam hgamma halpha ha i).pow 2).mul_const _
    have h2 := h1.div_const (∑ i, (1 / lam i) ^ 2)
    rwa [← Finset.mul_sum, mul_div_assoc, div_self hD.ne', mul_one] at h2
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  -- rewrite the ambient Frobenius sums in the eigenbasis
  have hcov := gibbsCovMatrix_rotatedAnharmonic hQ c hlam hg hd ht
  have hdiff : ∀ j k, gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j)
      (fun w => w k) - (Q * diagonal (fun i => 1 / (lam i * t)) * Qᵀ) j k =
      (Q * diagonal (fun i => V t i - 1 / (lam i * t)) * Qᵀ) j k := fun j k => by
    have := congrFun (congrFun hcov j) k
    rw [Matrix.of_apply] at this
    rw [this, ← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  simp_rw [hdiff]
  have hc1 := Laplace.Sampler.sum_sq_conj (diagonal (fun i => V t i - 1 / (lam i * t))) Qᵀ
    (by rw [transpose_transpose]; exact hQ)
  have hc2 := Laplace.Sampler.sum_sq_conj (diagonal (fun i => 1 / (lam i * t))) Qᵀ
    (by rw [transpose_transpose]; exact hQ)
  rw [transpose_transpose] at hc1 hc2
  rw [hc1, hc2, Laplace.Sampler.sum_sq_diagonal, Laplace.Sampler.sum_sq_diagonal]
  -- algebra: t² ∑(V − 1/(λt))² / ∑ (1/(λt))² = ∑ (t(λtV − 1))²/λ² / ∑ 1/λ²
  have hne := ht.ne'
  have hnum : ∀ i, (t * (lam i * t * V t i - 1)) ^ 2 * (1 / lam i) ^ 2 =
      t ^ 4 * (V t i - 1 / (lam i * t)) ^ 2 := fun i => by
    have := (hlam i).ne'
    field_simp
  have hden : ∀ i, (1 / lam i) ^ 2 = t ^ 2 * (1 / (lam i * t)) ^ 2 := fun i => by
    have := (hlam i).ne'
    field_simp
  simp_rw [hnum, hden]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hD' : 0 < ∑ i, (1 / (lam i * t)) ^ 2 :=
    Finset.sum_pos (fun i _ => by have := hlam i; positivity) Finset.univ_nonempty
  field_simp

end Frobenius

end Laplace.Multi
