/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedCentredDerivative

/-!
# The invariant centred quadratic probe on the localised measure

For every probe matrix `B`, on E2's exact localised measure, exactly

`−d/dt tr(B C(t)) = ∑ᵢ (QᵀBQ)ᵢᵢ Dᵢ(t) = Cov_loc,t[L∘A, (w − m(t))ᵀ B (w − m(t))]`,

`C(t)` the centred covariance, `m(t)` the mean,
`Dᵢ = Cov_loc[L∘A, uᵢ²] − 2⟨uᵢ⟩_loc Cov_loc[L∘A, uᵢ]` (`LocalisedCentredDerivative`); the centred
frame pair covariance `Cov_loc[L∘A, (uᵢ − μᵢ)(uⱼ − μⱼ)]` is `Dᵢ` on the diagonal and vanishes
identically off it. To second order

`t² (−∂ₜ tr(B C(t))) = tr(B H⁻¹) + 2 tr(B V)/t + O(t⁻²)`, `V = Q diag(vᵢ) Qᵀ`, `vᵢ = c₂',ᵢ − cᵢ²`,

and for `B = H` the leading coefficient is the dimension:
`−∂ₜ tr(H C(t)) = d/t² + 2(∑ᵢ λᵢvᵢ)/t³ + O(t⁻⁴)`.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section Algebra

variable {d : ℕ}

theorem sumsum_eq_dotProduct (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    ∑ j, ∑ k, M j k * x j * x k = x ⬝ᵥ (M *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem sumsum_eq_dotProduct' (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    ∑ j, ∑ k, M j k * (x j * x k) = x ⬝ᵥ (M *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- `∑ⱼₖ Bⱼₖ (Qy)ⱼ (Qy)ₖ = ∑ᵢᵢ' (QᵀBQ)ᵢᵢ' yᵢ yᵢ'`. -/
theorem sumsum_conj (B Q : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    ∑ j, ∑ k, B j k * (Q *ᵥ y) j * (Q *ᵥ y) k = ∑ i, ∑ i', (Qᵀ * B * Q) i i' * (y i * y i') := by
  rw [sumsum_eq_dotProduct, sumsum_eq_dotProduct', Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose Q y, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]

theorem sum_sum_eq_trace (B X : Matrix (Fin d) (Fin d) ℝ) :
    ∑ j, ∑ k, B j k * X j k = Matrix.trace (B * Xᵀ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

theorem conj_diagonal_entry (Q : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ) (j k : Fin d) :
    (Q * diagonal a * Qᵀ) j k = ∑ i, Q j i * Q k i * a i := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem conj_diagonal_transpose (Q : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ) :
    (Q * diagonal a * Qᵀ)ᵀ = Q * diagonal a * Qᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- `tr(B (Q diag(a) Qᵀ)) = ∑ᵢ (QᵀBQ)ᵢᵢ aᵢ`. -/
theorem trace_mul_conj_diagonal (B Q : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ) :
    Matrix.trace (B * (Q * diagonal a * Qᵀ)) = ∑ i, (Qᵀ * B * Q) i i * a i := by
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]

/-- `∑ⱼₖ Bⱼₖ ∑ᵢ QⱼᵢQₖᵢ fᵢ = ∑ᵢ (QᵀBQ)ᵢᵢ fᵢ`. -/
theorem sum_sum_conj_diag (B Q : Matrix (Fin d) (Fin d) ℝ) (f : Fin d → ℝ) :
    ∑ j, ∑ k, B j k * ∑ i, Q j i * Q k i * f i = ∑ i, (Qᵀ * B * Q) i i * f i := by
  have h : ∀ j k, ∑ i, Q j i * Q k i * f i = (Q * diagonal f * Qᵀ) j k := fun j k =>
    (conj_diagonal_entry Q f j k).symm
  simp only [h]
  rw [sum_sum_eq_trace, conj_diagonal_transpose, trace_mul_conj_diagonal]

theorem conj_conj {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1) (D : Matrix (Fin d) (Fin d) ℝ) :
    Qᵀ * (Q * D * Qᵀ) * Q = D := by
  rw [Matrix.mul_assoc Q D, ← Matrix.mul_assoc Qᵀ Q, hQ, Matrix.one_mul, Matrix.mul_assoc, hQ,
    Matrix.mul_one]

/-- `∑ⱼₖ Bⱼₖ Cov(wⱼ, wₖ) = tr(B C)`, `C` the (symmetric) covariance matrix. -/
theorem sum_sum_cov_eq_trace (L : (Fin d → ℝ) → ℝ) (t : ℝ) (B : Matrix (Fin d) (Fin d) ℝ) :
    ∑ j, ∑ k, B j k * gibbsCov L t (fun w => w j) (fun w => w k) =
      Matrix.trace (B * Matrix.of fun j k => gibbsCov L t (fun w => w j) (fun w => w k)) := by
  have hsym : (Matrix.of fun j k => gibbsCov L t (fun w => w j) (fun w => w k))ᵀ =
      Matrix.of fun j k => gibbsCov L t (fun w => w j) (fun w => w k) := by
    ext j k
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact gibbsCov_comm L t _ _
  rw [← hsym, ← sum_sum_eq_trace]
  simp only [Matrix.of_apply]

end Algebra

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- The localised frame mean `μᵢ(t) = ⟨uᵢ⟩_loc`. -/
noncomputable def locFrameMean (Q : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ)
    (lam alpha gamma : Fin d → ℝ) (g : ℝ) (w₀ : Fin d → ℝ) (t : ℝ) (i : Fin d) : ℝ :=
  gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
    (fun w => affineFrame Q c w i)

/-- `Dᵢ(t) = Cov_loc[L∘A, uᵢ²] − 2⟨uᵢ⟩_loc Cov_loc[L∘A, uᵢ] = −∂ₜ Var_loc(uᵢ)`
(`LocalisedCentredDerivative`). -/
noncomputable def locCentredD (Q : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ)
    (lam alpha gamma : Fin d → ℝ) (g : ℝ) (w₀ : Fin d → ℝ) (t : ℝ) (i : Fin d) : ℝ :=
  gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
    2 * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (fun w => affineFrame Q c w i) *
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-! ### A. The trace probe's exact derivative -/

/-- **The `B`-weighted centred covariance trace's exact derivative**:
`d/ds ∑ⱼₖ Bⱼₖ Cov_loc,s(wⱼ, wₖ) = −∑ᵢ (QᵀBQ)ᵢᵢ Dᵢ(t)` at `s = t`. -/
theorem hasDerivAt_localised_trace_cov (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (B : Matrix (Fin d) (Fin d) ℝ) :
    HasDerivAt (fun s => ∑ j, ∑ k, B j k *
        gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => w j)
          (fun w => w k))
      (-∑ i, (Qᵀ * B * Q) i i * locCentredD Q c lam alpha gamma g w₀ t i) t := by
  have h : HasDerivAt (fun s => ∑ j, ∑ k, B j k *
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => w j)
        (fun w => w k))
      (∑ j, ∑ k, B j k * -∑ i, Q j i * Q k i * locCentredD Q c lam alpha gamma g w₀ t i) t :=
    HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ =>
      (hasDerivAt_localised_cov_coord hlam hgamma hdisc hQ c w₀ hg ht j k).const_mul (B j k)
  refine h.congr_deriv ?_
  simp only [mul_neg, Finset.sum_neg_distrib]
  rw [sum_sum_conj_diag]

/-! ### B. The exact bridge to the centred quadratic probe -/

/-- `⟨wⱼ⟩_loc = cⱼ + ∑ᵢ Qⱼᵢ ⟨uᵢ⟩_loc`. -/
theorem localised_mean_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (j : Fin d) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j) =
      c j + ∑ i, Q j i * locFrameMean Q c lam alpha gamma g w₀ t i := by
  have hZ := (partitionFunction_localisedRotatedAnharmonic_pos hQ c w₀ hlam hgamma hdisc hg ht).ne'
  have hL := integrable_exp_localisedRotatedAnharmonic hQ c w₀ hlam hgamma hdisc hg ht
  have hA := integrable_frame_coord_localised hQ c w₀ hlam hgamma hdisc hg ht
  have hQA : ∀ i, Integrable (fun w => Q j i * affineFrame Q c w i *
      Real.exp (-(t * localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t w))) := fun i =>
    ((hA i).const_mul (Q j i)).congr (Eventually.of_forall fun w => by ring)
  have hF : Integrable (fun w => (∑ i, Q j i * affineFrame Q c w i) *
      Real.exp (-(t * localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t w))) :=
    (integrable_finsetSum Finset.univ fun i _ => hQA i).congr (Eventually.of_forall fun w => by
      simp only [Finset.sum_mul])
  have hfun : (fun w : Fin d → ℝ => w j) = fun w => c j + ∑ i, Q j i * affineFrame Q c w i :=
    funext fun w => coord_eq_sum_affineFrame hQ c w j
  rw [hfun, gibbsExpectation_add_of_integrable _ t (fun _ => c j) _ (hL.const_mul (c j)) hF,
    gibbsExpectation_const_of_ne_zero _ t (c j) hZ,
    gibbsExpectation_finsetSum_of_integrable Finset.univ (fun i w => Q j i * affineFrame Q c w i) t
      (fun i _ => hQA i)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => gibbsExpectation_const_mul _ t (Q j i) _

/-- Pointwise, `w − m(t) = Q (u − μ(t))`. -/
theorem coord_sub_mean_eq (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t)
    (w : Fin d → ℝ) (j : Fin d) :
    w j - gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => w j) =
      (Q *ᵥ fun i => affineFrame Q c w i - locFrameMean Q c lam alpha gamma g w₀ t i) j := by
  rw [localised_mean_coord hlam hgamma hdisc hQ c w₀ hg ht j, coord_eq_sum_affineFrame hQ c w j]
  simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Linearity on the frame family: for constants `a`,
`Cov[E, (uᵢ − aᵢ)(uⱼ − aⱼ)] = Cov[E, uᵢuⱼ] − aⱼ Cov[E, uᵢ] − aᵢ Cov[E, uⱼ]`. -/
theorem gibbsCov_energy_centred_pair_locFamily (hg : 0 ≤ g) (u₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (a : Fin d → ℝ) (i j : Fin d) :
    gibbsCov (separablePotential (locFamily lam alpha gamma g u₀ t)) t
        (separableAnharmonic lam alpha gamma) (fun u => (u i - a i) * (u j - a j)) =
      gibbsCov (separablePotential (locFamily lam alpha gamma g u₀ t)) t
          (separableAnharmonic lam alpha gamma) (fun u => u i * u j) -
        a j * gibbsCov (separablePotential (locFamily lam alpha gamma g u₀ t)) t
          (separableAnharmonic lam alpha gamma) (fun u => u i) -
        a i * gibbsCov (separablePotential (locFamily lam alpha gamma g u₀ t)) t
          (separableAnharmonic lam alpha gamma) (fun u => u j) := by
  have hcm : ∀ i j, Integrable (fun u : Fin d → ℝ => u i * u j *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) := fun i j =>
    integrable_locFamily_of_integrable hg u₀ ht (by fun_prop)
      (integrable_coord_mul_separableAnharmonic hlam hgamma hdisc ht i j)
  have hc : ∀ i, Integrable (fun u : Fin d → ℝ => u i *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) := fun i =>
    integrable_locFamily_of_integrable hg u₀ ht (by fun_prop)
      (integrable_coord_separableAnharmonic hlam hgamma hdisc ht i)
  have hexp0 : Integrable (fun u : Fin d → ℝ =>
      (1 : ℝ) * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) :=
    (integrable_exp_separableAnharmonic hlam hgamma hdisc ht).congr
      (Eventually.of_forall fun u => by simp)
  have hL1 : Integrable (fun u : Fin d → ℝ =>
      (1 : ℝ) * Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    integrable_locFamily_of_integrable hg u₀ ht (by fun_prop) hexp0
  have hL : Integrable (fun u : Fin d → ℝ =>
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    hL1.congr (Eventually.of_forall fun u => by simp)
  have hZ : partitionFunction (separablePotential (locFamily lam alpha gamma g u₀ t)) t ≠ 0 := by
    rw [partitionFunction_separable]
    exact Finset.prod_ne_zero_iff.mpr fun m _ =>
      partitionFunction_locFamily_ne hlam hgamma hdisc hg u₀ ht m
  have hEsum : ∀ (ψ : (Fin d → ℝ) → ℝ), (∀ k, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * ψ u *
        Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u)))) →
      Integrable (fun u : Fin d → ℝ => separableAnharmonic lam alpha gamma u * ψ u *
        Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    fun ψ hψk => by
      refine (integrable_finsetSum Finset.univ fun k _ => hψk k).congr
        (Eventually.of_forall fun u => ?_)
      simp only [separableAnharmonic, separablePotential, Finset.sum_mul]
  have hE : Integrable (fun u : Fin d → ℝ => separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    (integrable_finsetSum Finset.univ fun k _ =>
      integrable_energy_locFamily hlam hgamma hdisc hg u₀ ht k).congr
      (Eventually.of_forall fun u => by
        simp only [separableAnharmonic, separablePotential, Finset.sum_mul])
  have hLcm : ∀ i j, Integrable (fun u : Fin d → ℝ =>
      separableAnharmonic lam alpha gamma u * (u i * u j) *
        Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) := fun i j =>
    hEsum _ fun k => integrable_energy_mul_locFamily hlam hgamma hdisc hg u₀ ht k i j
  have hLc : ∀ i, Integrable (fun u : Fin d → ℝ => separableAnharmonic lam alpha gamma u * u i *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) := fun i =>
    hEsum (fun u => u i) fun k =>
      (integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 1).congr
        (Eventually.of_forall fun u => by simp only [pow_one])
  have hA₁E : Integrable (fun u : Fin d → ℝ => u i * u j * separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    (hLcm i j).congr (Eventually.of_forall fun u => by ring)
  have hA₂ : Integrable (fun u : Fin d → ℝ => -a j * u i *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    ((hc i).const_mul (-a j)).congr (Eventually.of_forall fun u => by ring)
  have hA₂E : Integrable (fun u : Fin d → ℝ => -a j * u i * separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    ((hLc i).const_mul (-a j)).congr (Eventually.of_forall fun u => by ring)
  have hA₃ : Integrable (fun u : Fin d → ℝ => -a i * u j *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    ((hc j).const_mul (-a i)).congr (Eventually.of_forall fun u => by ring)
  have hA₃E : Integrable (fun u : Fin d → ℝ => -a i * u j * separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    ((hLc j).const_mul (-a i)).congr (Eventually.of_forall fun u => by ring)
  have hA₁₂ : Integrable (fun u : Fin d → ℝ => (u i * u j + -a j * u i) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    ((hcm i j).add hA₂).congr (Eventually.of_forall fun u => by
      simp only [Pi.add_apply]; ring)
  have hA₁₂E : Integrable (fun u : Fin d → ℝ => (u i * u j + -a j * u i) *
      separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    (hA₁E.add hA₂E).congr (Eventually.of_forall fun u => by
      simp only [Pi.add_apply]; ring)
  have hP : Integrable (fun u : Fin d → ℝ => (u i * u j + -a j * u i + -a i * u j) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    (hA₁₂.add hA₃).congr (Eventually.of_forall fun u => by
      simp only [Pi.add_apply]; ring)
  have hPE : Integrable (fun u : Fin d → ℝ => (u i * u j + -a j * u i + -a i * u j) *
      separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
    (hA₁₂E.add hA₃E).congr (Eventually.of_forall fun u => by
      simp only [Pi.add_apply]; ring)
  have hexp : (fun u : Fin d → ℝ => (u i - a i) * (u j - a j)) =
      fun u => a i * a j + (u i * u j + -a j * u i + -a i * u j) := by
    funext u; ring
  rw [hexp, gibbsCov_comm, gibbsCov_const_add_left _ t (a i * a j) _ _ hZ hL hP hE hPE,
    gibbsCov_add_left_of_integrable _ t _ _ _ hA₁₂ hA₃ hA₁₂E hA₃E,
    gibbsCov_add_left_of_integrable _ t _ _ _ (hcm i j) hA₂ hA₁E hA₂E, gibbsCov_const_mul_left,
    gibbsCov_const_mul_left, gibbsCov_comm _ _ (fun u => u i * u j),
    gibbsCov_comm _ _ (fun u => u i), gibbsCov_comm _ _ (fun u => u j)]
  ring

/-- **The centred frame pair covariance**: `Cov_loc[L∘A, (uᵢ − μᵢ)(uⱼ − μⱼ)] = Dᵢ` for `i = j`
and `0` for `i ≠ j` — the off-diagonal centred pairs are exactly uncorrelated with the energy. -/
theorem localisedCovK_centred_pair (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (i j : Fin d) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => (affineFrame Q c w i - locFrameMean Q c lam alpha gamma g w₀ t i) *
          (affineFrame Q c w j - locFrameMean Q c lam alpha gamma g w₀ t j)) =
      if i = j then locCentredD Q c lam alpha gamma g w₀ t i else 0 := by
  have e : (fun w => (affineFrame Q c w i - locFrameMean Q c lam alpha gamma g w₀ t i) *
      (affineFrame Q c w j - locFrameMean Q c lam alpha gamma g w₀ t j)) =
      rotated Q c (fun u : Fin d → ℝ => (u i - locFrameMean Q c lam alpha gamma g w₀ t i) *
        (u j - locFrameMean Q c lam alpha gamma g w₀ t j)) := rfl
  have hp : gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i * affineFrame Q c w j) =
      gibbsCov (separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)) t
        (separableAnharmonic lam alpha gamma) (fun u => u i * u j) :=
    localisedRotated_gibbsCov_eq hQ c w₀ t (ψ := fun u => u i * u j) (by fun_prop)
  have hc' : ∀ i, gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) =
      gibbsCov (separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)) t
        (separableAnharmonic lam alpha gamma) (fun u => u i) := fun i =>
    localisedRotated_gibbsCov_eq hQ c w₀ t (ψ := fun u => u i) (by fun_prop)
  rw [e, localisedRotated_gibbsCov_eq hQ c w₀ t (by fun_prop),
    gibbsCov_energy_centred_pair_locFamily hlam hgamma hdisc hg (affineFrame Q c w₀) ht
      (locFrameMean Q c lam alpha gamma g w₀ t) i j, ← hp, ← hc' i, ← hc' j]
  split_ifs with hij
  · subst hij
    have e2 : (fun w => affineFrame Q c w i * affineFrame Q c w i) =
        fun w => affineFrame Q c w i ^ 2 := by funext w; ring
    rw [e2]
    unfold locCentredD locFrameMean
    ring
  · have h := centred_pair_offdiag_zero hlam hgamma hdisc hQ c w₀ hg ht hij
    unfold locFrameMean
    linear_combination h

/-- **The exact bridge**: for every probe matrix `B`, with `m(t) = ⟨w⟩_loc` frozen,
`Cov_loc,t[L∘A, (w − m)ᵀ B (w − m)] = ∑ᵢ (QᵀBQ)ᵢᵢ Dᵢ(t) = −∂ₜ tr(B C(t))`. -/
theorem localisedCovK_centred_quadratic_eq (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) (B : Matrix (Fin d) (Fin d) ℝ) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => ∑ j, ∑ k, B j k *
          (w j - gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
            (fun w => w j)) *
          (w k - gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
            (fun w => w k))) =
      ∑ i, (Qᵀ * B * Q) i i * locCentredD Q c lam alpha gamma g w₀ t i := by
  have hprobe : (fun w => ∑ j, ∑ k, B j k *
      (w j - gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => w j)) *
      (w k - gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => w k))) =
      rotated Q c (fun u : Fin d → ℝ => ∑ i, ∑ i', (Qᵀ * B * Q) i i' *
        ((u i - locFrameMean Q c lam alpha gamma g w₀ t i) *
          (u i' - locFrameMean Q c lam alpha gamma g w₀ t i'))) := by
    funext w
    simp only [rotated, coord_sub_mean_eq hlam hgamma hdisc hQ c w₀ hg ht w]
    exact sumsum_conj B Q _
  have hcont : Continuous fun u : Fin d → ℝ => ∑ i, ∑ i', (Qᵀ * B * Q) i i' *
      ((u i - locFrameMean Q c lam alpha gamma g w₀ t i) *
        (u i' - locFrameMean Q c lam alpha gamma g w₀ t i')) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun i' _ => by fun_prop
  rw [hprobe, localisedRotated_gibbsCov_eq hQ c w₀ t hcont]
  have hcm : ∀ i j, Integrable (fun u : Fin d → ℝ => u i * u j *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    fun i j => integrable_locFamily_of_integrable hg (affineFrame Q c w₀) ht (by fun_prop)
      (integrable_coord_mul_separableAnharmonic hlam hgamma hdisc ht i j)
  have hc : ∀ i, Integrable (fun u : Fin d → ℝ => u i *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    fun i => integrable_locFamily_of_integrable hg (affineFrame Q c w₀) ht (by fun_prop)
      (integrable_coord_separableAnharmonic hlam hgamma hdisc ht i)
  have hexp0 : Integrable (fun u : Fin d → ℝ =>
      (1 : ℝ) * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) :=
    (integrable_exp_separableAnharmonic hlam hgamma hdisc ht).congr
      (Eventually.of_forall fun u => by simp)
  have hL1 : Integrable (fun u : Fin d → ℝ => (1 : ℝ) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    integrable_locFamily_of_integrable hg (affineFrame Q c w₀) ht (by fun_prop) hexp0
  have hL : Integrable (fun u : Fin d → ℝ =>
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    hL1.congr (Eventually.of_forall fun u => by simp)
  have hEsum : ∀ (ψ : (Fin d → ℝ) → ℝ), (∀ k, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * ψ u *
        Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
          u)))) →
      Integrable (fun u : Fin d → ℝ => separableAnharmonic lam alpha gamma u * ψ u *
        Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
          u))) :=
    fun ψ hψk => by
      refine (integrable_finsetSum Finset.univ fun k _ => hψk k).congr
        (Eventually.of_forall fun u => ?_)
      simp only [separableAnharmonic, separablePotential, Finset.sum_mul]
  have hE : Integrable (fun u : Fin d → ℝ => separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    (integrable_finsetSum Finset.univ fun k _ =>
      integrable_energy_locFamily hlam hgamma hdisc hg (affineFrame Q c w₀) ht k).congr
      (Eventually.of_forall fun u => by
        simp only [separableAnharmonic, separablePotential, Finset.sum_mul])
  have hLcm : ∀ i j, Integrable (fun u : Fin d → ℝ =>
      separableAnharmonic lam alpha gamma u * (u i * u j) *
        Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
          u))) := fun i j =>
    hEsum _ fun k =>
      integrable_energy_mul_locFamily hlam hgamma hdisc hg (affineFrame Q c w₀) ht k i j
  have hLc : ∀ i, Integrable (fun u : Fin d → ℝ => separableAnharmonic lam alpha gamma u * u i *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    fun i => hEsum (fun u => u i) fun k =>
      (integrable_energy_pow_locFamily hlam hgamma hdisc hg (affineFrame Q c w₀) ht k i 1).congr
        (Eventually.of_forall fun u => by simp only [pow_one])
  have hcen : ∀ i i', Integrable (fun u : Fin d → ℝ => (Qᵀ * B * Q) i i' *
      ((u i - locFrameMean Q c lam alpha gamma g w₀ t i) *
        (u i' - locFrameMean Q c lam alpha gamma g w₀ t i')) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    fun i i' =>
      (((((hcm i i').sub ((hc i).const_mul (locFrameMean Q c lam alpha gamma g w₀ t i'))).sub
        ((hc i').const_mul (locFrameMean Q c lam alpha gamma g w₀ t i))).add
        (hL.const_mul (locFrameMean Q c lam alpha gamma g w₀ t i *
          locFrameMean Q c lam alpha gamma g w₀ t i'))).const_mul ((Qᵀ * B * Q) i i')).congr
        (Eventually.of_forall fun u => by
      (try simp only [Pi.add_apply, Pi.sub_apply]); ring)
  have hcenE : ∀ i i', Integrable (fun u : Fin d → ℝ => (Qᵀ * B * Q) i i' *
      ((u i - locFrameMean Q c lam alpha gamma g w₀ t i) *
        (u i' - locFrameMean Q c lam alpha gamma g w₀ t i')) *
      separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    fun i i' =>
      (((((hLcm i i').sub ((hLc i).const_mul (locFrameMean Q c lam alpha gamma g w₀ t i'))).sub
        ((hLc i').const_mul (locFrameMean Q c lam alpha gamma g w₀ t i))).add
        (hE.const_mul (locFrameMean Q c lam alpha gamma g w₀ t i *
          locFrameMean Q c lam alpha gamma g w₀ t i'))).const_mul ((Qᵀ * B * Q) i i')).congr
        (Eventually.of_forall fun u => by
      (try simp only [Pi.add_apply, Pi.sub_apply]); ring)
  have hrow : ∀ i, Integrable (fun u : Fin d → ℝ => (∑ i', (Qᵀ * B * Q) i i' *
      ((u i - locFrameMean Q c lam alpha gamma g w₀ t i) *
        (u i' - locFrameMean Q c lam alpha gamma g w₀ t i'))) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    fun i => (integrable_finsetSum Finset.univ fun i' _ => hcen i i').congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hrowE : ∀ i, Integrable (fun u : Fin d → ℝ => (∑ i', (Qᵀ * B * Q) i i' *
      ((u i - locFrameMean Q c lam alpha gamma g w₀ t i) *
        (u i' - locFrameMean Q c lam alpha gamma g w₀ t i'))) *
      separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) :=
    fun i => (integrable_finsetSum Finset.univ fun i' _ => hcenE i i').congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  rw [gibbsCov_comm, gibbsCov_finsetSum_left _ t Finset.univ _ _ (fun i _ => hrow i)
    (fun i _ => hrowE i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gibbsCov_finsetSum_left _ t Finset.univ _ _ (fun i' _ => hcen i i') (fun i' _ => hcenE i i')]
  have hpair : ∀ i', gibbsCov
      (separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)) t
      (fun u => (Qᵀ * B * Q) i i' * ((u i - locFrameMean Q c lam alpha gamma g w₀ t i) *
        (u i' - locFrameMean Q c lam alpha gamma g w₀ t i')))
      (separableAnharmonic lam alpha gamma) =
      (Qᵀ * B * Q) i i' * if i = i' then locCentredD Q c lam alpha gamma g w₀ t i else 0 :=
    fun i' => by
    rw [gibbsCov_const_mul_left, gibbsCov_comm,
      ← localisedRotated_gibbsCov_eq hQ c w₀ t (ψ := fun u : Fin d → ℝ =>
        (u i - locFrameMean Q c lam alpha gamma g w₀ t i) *
          (u i' - locFrameMean Q c lam alpha gamma g w₀ t i')) (by fun_prop)]
    exact congrArg _ (localisedCovK_centred_pair hlam hgamma hdisc hQ c w₀ hg ht i i')
  simp only [hpair, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

/-! ### C. Second order -/

/-- The weighted centred derivative sum to second order:
`|t² ∑ᵢ aᵢDᵢ − ∑ᵢ aᵢ/λᵢ − 2(∑ᵢ aᵢvᵢ)/t| ≤ K/t²`. -/
theorem localised_centredD_weighted_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (a : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * (∑ i, a i * locCentredD Q c lam alpha gamma g w₀ t i) - ∑ i, a i * (1 / lam i) -
        2 * (∑ i, a i * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sq a
    (fun i t => t ^ 2 * locCentredD Q c lam alpha gamma g w₀ t i - 1 / lam i -
      2 * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t)
    (fun i => localisedVar_neg_deriv_order2_rate hlam hgamma hdisc hQ c w₀ hg i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have key : t ^ 2 * (∑ i, a i * locCentredD Q c lam alpha gamma g w₀ t i) -
      ∑ i, a i * (1 / lam i) -
      2 * (∑ i, a i * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t =
      ∑ i, a i * (t ^ 2 * locCentredD Q c lam alpha gamma g w₀ t i - 1 / lam i -
        2 * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  exact h ht

/-- **The `B`-weighted centred covariance trace's derivative to second order**:
`|t²(−∂ₜ tr(B C(t))) − tr(B H⁻¹) − 2 tr(B V)/t| ≤ K/t²`, `V = Q diag(vᵢ) Qᵀ`. -/
theorem localisedTraceCov_neg_deriv_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (B : Matrix (Fin d) (Fin d) ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * (-deriv (fun s => ∑ j, ∑ k, B j k *
          gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => w j)
            (fun w => w k)) t) -
        Matrix.trace (B * (Q * diagonal (fun i => 1 / lam i) * Qᵀ)) -
        2 * Matrix.trace (B * (Q * diagonal (fun i =>
          varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) * Qᵀ)) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localised_centredD_weighted_order2_rate hlam hgamma hdisc hQ c w₀ hg
    (fun i => (Qᵀ * B * Q) i i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [(hasDerivAt_localised_trace_cov hlam hgamma hdisc hQ c w₀ hg ht0 B).deriv, neg_neg,
    trace_mul_conj_diagonal, trace_mul_conj_diagonal]
  exact h ht

/-- **The centred quadratic probe's energy covariance to second order**:
`|t² Cov_loc[L∘A, (w − m)ᵀ B (w − m)] − tr(B H⁻¹) − 2 tr(B V)/t| ≤ K/t²`. -/
theorem localisedCovK_centred_quadratic_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (B : Matrix (Fin d) (Fin d) ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => ∑ j, ∑ k, B j k *
            (w j - gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
              (fun w => w j)) *
            (w k - gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
              (fun w => w k))) -
        Matrix.trace (B * (Q * diagonal (fun i => 1 / lam i) * Qᵀ)) -
        2 * Matrix.trace (B * (Q * diagonal (fun i =>
          varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) * Qᵀ)) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localised_centredD_weighted_order2_rate hlam hgamma hdisc hQ c w₀ hg
    (fun i => (Qᵀ * B * Q) i i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedCovK_centred_quadratic_eq hlam hgamma hdisc hQ c w₀ hg ht0 B,
    trace_mul_conj_diagonal, trace_mul_conj_diagonal]
  exact h ht

/-- **`B = 1`: the total centred variance's derivative**:
`|t²(−∂ₜ ∑ⱼ Var_loc(wⱼ)) − ∑ᵢ 1/λᵢ − 2(∑ᵢ vᵢ)/t| ≤ K/t²`. -/
theorem localisedTotalVar_neg_deriv_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * (-deriv (fun s => ∑ j,
          gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => w j)
            (fun w => w j)) t) -
        ∑ i, 1 / lam i -
        2 * (∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localised_centredD_weighted_order2_rate hlam hgamma hdisc hQ c w₀ hg
    (fun _ => 1)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hfun : (fun s => ∑ j, ∑ k, (1 : Matrix (Fin d) (Fin d) ℝ) j k *
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => w j)
        (fun w => w k)) =
      fun s => ∑ j, gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => w j) (fun w => w j) := by
    funext s
    exact Finset.sum_congr rfl fun j _ => by
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
  have hd := hasDerivAt_localised_trace_cov hlam hgamma hdisc hQ c w₀ hg ht0
    (1 : Matrix (Fin d) (Fin d) ℝ)
  rw [hfun, Matrix.mul_one, hQ] at hd
  rw [hd.deriv, neg_neg]
  have h' := h ht
  simp only [Matrix.one_apply_eq, one_mul] at h' ⊢
  exact h'

/-- **`B = H`: the Hessian-weighted centred covariance trace's derivative**: the leading
coefficient is the dimension, `|t²(−∂ₜ tr(H C(t))) − d − 2(∑ᵢ λᵢvᵢ)/t| ≤ K/t²`. -/
theorem localisedTraceCov_hessian_neg_deriv_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * (-deriv (fun s => ∑ j, ∑ k, (Q * diagonal lam * Qᵀ) j k *
          gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => w j)
            (fun w => w k)) t) -
        (d : ℝ) -
        2 * (∑ i, lam i * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localised_centredD_weighted_order2_rate hlam hgamma hdisc hQ c w₀ hg
    lam
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hconj : ∀ i, (Qᵀ * (Q * diagonal lam * Qᵀ) * Q) i i = lam i := fun i => by
    rw [conj_conj hQ, Matrix.diagonal_apply_eq]
  have hsum : ∑ i, lam i * (1 / lam i) = (d : ℝ) := by
    rw [Finset.sum_congr rfl fun i _ => mul_one_div_cancel (hlam i).ne', Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [(hasDerivAt_localised_trace_cov hlam hgamma hdisc hQ c w₀ hg ht0 _).deriv, neg_neg]
  simp only [hconj]
  rw [← hsum]
  exact h ht

/-- **`B = H`, the frozen centred Gaussian quadratic energy**:
`|t² Cov_loc[L∘A, (w − m)ᵀ H (w − m)] − d − 2(∑ᵢ λᵢvᵢ)/t| ≤ K/t²`; for `Eₜ = ½(w − m)ᵀH(w − m)`
this reads `Cov_loc[L∘A, Eₜ] = d/(2t²) + (∑ᵢ λᵢvᵢ)/t³ + O(t⁻⁴)`. -/
theorem localisedCovK_hessian_centred_quadratic_order2_rate (hQ : Qᵀ * Q = 1)
    (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => ∑ j, ∑ k, (Q * diagonal lam * Qᵀ) j k *
            (w j - gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
              (fun w => w j)) *
            (w k - gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
              (fun w => w k))) -
        (d : ℝ) -
        2 * (∑ i, lam i * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localised_centredD_weighted_order2_rate hlam hgamma hdisc hQ c w₀ hg
    lam
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hconj : ∀ i, (Qᵀ * (Q * diagonal lam * Qᵀ) * Q) i i = lam i := fun i => by
    rw [conj_conj hQ, Matrix.diagonal_apply_eq]
  have hsum : ∑ i, lam i * (1 / lam i) = (d : ℝ) := by
    rw [Finset.sum_congr rfl fun i _ => mul_one_div_cancel (hlam i).ne', Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [localisedCovK_centred_quadratic_eq hlam hgamma hdisc hQ c w₀ hg ht0 _]
  simp only [hconj]
  rw [← hsum]
  exact h ht

end Multi

end Laplace.Multi
