/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.Minibatch
import Laplace.Multi.TiltedGaussian

/-!
# The exact one-step recursion of minibatch SGLD on linear regression (E8)

Quadratic per-sample losses have affine gradients `∇lᵢ(w) = Hᵢ w − gᵢ` (coordinates centred at the
least-squares point, so `∑ᵢ gᵢ = 0`). One SGLD step with a uniform batch `B` of `m` of the `n`
samples and a standard Gaussian draw `ξ` is `w' = w − h t (H_B w − g_B) + √(2h) ξ`. Averaging over
`ξ` (`stdExp`, density form) and over `B` (`batchAvg`):

* `sgld_mean_step`: `E[w'] = A w` with `A = 1 − h t H = ulaStep (t • H) h`;
* `sgld_second_moment_step`: `E[w' w'ᵀ] = A wwᵀ Aᵀ + 2h • 1 + h²t² c ∑ᵢ rᵢ rᵢᵀ`,
  `rᵢ = (Hᵢ − H) w − gᵢ`, `c = (1 − m/n)/(m(n−1))`: the single family `aᵢ = Hᵢ w − gᵢ` has
  `mean_B a − ā = (H_B − H) w − g_B`,
  so the whole quadratic term is one finite population correction (`fpc_bilinear`);
* `sgld_law_step`: integrated against a law with mean `q` and raw second moment `M`, the second
  moment becomes `e8FullStep (t • H) h t C_g Hs H m M − h²t² c ∑ᵢ (Dᵢ q gᵢᵀ + gᵢ qᵀ Dᵢᵀ)`, and for a
  centred law exactly `e8FullStep … M` (`sgld_law_step_centred`): the note's full law, with the
  derived constants, is the exact stationary equation of minibatch SGLD on linear regression.
-/

open Finset Matrix MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-! ### The standard Gaussian step -/

/-- The standard Gaussian expectation of a scalar observable, in density form. -/
noncomputable def stdExp (φ : (ι → ℝ) → ℝ) : ℝ :=
  (∫ ξ : ι → ℝ, φ ξ * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ) /
    gaussianZ (matCLM (1 : Matrix ι ι ℝ))

theorem stdExp_const (c : ℝ) : stdExp (fun _ : ι → ℝ => c) = c := by
  unfold stdExp
  rw [integral_const_mul]
  have hZ : ∫ ξ : ι → ℝ, gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ =
      gaussianZ (matCLM (1 : Matrix ι ι ℝ)) := rfl
  rw [hZ, mul_div_cancel_right₀ _ (gaussianZ_matCLM_pos Matrix.PosDef.one).ne']

theorem stdExp_coord (i : ι) : stdExp (fun ξ : ι → ℝ => ξ i) = 0 := by
  unfold stdExp
  rw [integral_coord_mul_gaussianWeight_matCLM_eq_zero Matrix.PosDef.one, zero_div]

theorem stdExp_coord_mul (i j : ι) :
    stdExp (fun ξ : ι → ℝ => ξ i * ξ j) = (1 : Matrix ι ι ℝ) i j := by
  unfold stdExp
  rw [integral_coord_mul_gaussianWeight_matCLM Matrix.PosDef.one, inv_one,
    mul_div_cancel_left₀ _ (gaussianZ_matCLM_pos Matrix.PosDef.one).ne']

/-- `E[c + s ξᵢ] = c`. -/
theorem stdExp_affine (c s : ℝ) (i : ι) : stdExp (fun ξ : ι → ℝ => c + s * ξ i) = c := by
  have hP : (1 : Matrix ι ι ℝ).PosDef := Matrix.PosDef.one
  unfold stdExp
  have hexp : ∀ ξ : ι → ℝ, (c + s * ξ i) * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ =
      c * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ +
        s * (ξ i * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ) := fun ξ => by ring
  simp_rw [hexp]
  rw [integral_add ((integrable_gaussianWeight_matCLM hP).const_mul _)
    ((integrable_coord_mul_gaussianWeight_matCLM' hP i).const_mul _), integral_const_mul,
    integral_const_mul, integral_coord_mul_gaussianWeight_matCLM_eq_zero hP, mul_zero, add_zero]
  have hZ : ∫ ξ : ι → ℝ, gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ =
      gaussianZ (matCLM (1 : Matrix ι ι ℝ)) := rfl
  rw [hZ, mul_div_cancel_right₀ _ (gaussianZ_matCLM_pos hP).ne']

/-- `E[(μᵢ + s ξᵢ)(μⱼ + s ξⱼ)] = μᵢ μⱼ + s² δᵢⱼ`. -/
theorem stdExp_affine_mul (μ : ι → ℝ) (s : ℝ) (i j : ι) :
    stdExp (fun ξ : ι → ℝ => (μ i + s * ξ i) * (μ j + s * ξ j)) =
      μ i * μ j + s ^ 2 * (1 : Matrix ι ι ℝ) i j := by
  have hP : (1 : Matrix ι ι ℝ).PosDef := Matrix.PosDef.one
  unfold stdExp
  have hexp : ∀ ξ : ι → ℝ,
      (μ i + s * ξ i) * (μ j + s * ξ j) * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ =
        μ i * μ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ +
          (s * μ i) * (ξ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ) +
          (s * μ j) * (ξ i * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ) +
          s ^ 2 * (ξ i * ξ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ) := fun ξ => by ring
  simp_rw [hexp]
  have h1 : Integrable (fun ξ : ι → ℝ =>
      μ i * μ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ) :=
    (integrable_gaussianWeight_matCLM hP).const_mul _
  have h2 : Integrable (fun ξ : ι → ℝ =>
      (s * μ i) * (ξ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ)) :=
    (integrable_coord_mul_gaussianWeight_matCLM' hP j).const_mul _
  have h3 : Integrable (fun ξ : ι → ℝ =>
      (s * μ j) * (ξ i * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ)) :=
    (integrable_coord_mul_gaussianWeight_matCLM' hP i).const_mul _
  have h4 : Integrable (fun ξ : ι → ℝ =>
      s ^ 2 * (ξ i * ξ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ)) :=
    (integrable_coord_mul_gaussianWeight_matCLM hP i j).const_mul _
  have h12 : Integrable (fun ξ : ι → ℝ =>
      μ i * μ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ +
        (s * μ i) * (ξ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ)) := h1.add h2
  have h123 : Integrable (fun ξ : ι → ℝ =>
      μ i * μ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ +
        (s * μ i) * (ξ j * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ) +
        (s * μ j) * (ξ i * gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ)) := h12.add h3
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_coord_mul_gaussianWeight_matCLM_eq_zero hP,
    integral_coord_mul_gaussianWeight_matCLM_eq_zero hP,
    integral_coord_mul_gaussianWeight_matCLM hP, inv_one]
  have hZ : ∫ ξ : ι → ℝ, gaussianWeight (matCLM (1 : Matrix ι ι ℝ)) ξ =
      gaussianZ (matCLM (1 : Matrix ι ι ℝ)) := rfl
  have hZ0 : gaussianZ (matCLM (1 : Matrix ι ι ℝ)) ≠ 0 := (gaussianZ_matCLM_pos hP).ne'
  rw [hZ]
  field_simp
  ring

/-- The entrywise standard Gaussian expectation of a vector-valued observable. -/
noncomputable def stdExpVec (F : (ι → ℝ) → ι → ℝ) : ι → ℝ := fun i => stdExp (fun ξ => F ξ i)

/-- The entrywise standard Gaussian expectation of a matrix-valued observable. -/
noncomputable def stdExpMat (F : (ι → ℝ) → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => stdExp (fun ξ => F ξ i j)

theorem stdExpVec_affine (μ : ι → ℝ) (s : ℝ) : stdExpVec (fun ξ => μ + s • ξ) = μ := by
  funext i
  simp only [stdExpVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact stdExp_affine (μ i) s i

/-- `E[(μ + sξ)(μ + sξ)ᵀ] = μμᵀ + s² • 1`. -/
theorem stdExpMat_affine (μ : ι → ℝ) (s : ℝ) :
    stdExpMat (fun ξ => vecMulVec (μ + s • ξ) (μ + s • ξ)) =
      vecMulVec μ μ + (s ^ 2) • (1 : Matrix ι ι ℝ) := by
  ext i j
  simp only [stdExpMat, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.smul_apply]
  exact stdExp_affine_mul μ s i j

/-! ### Batch averages -/

section BatchAvg

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- The uniform average over the `m`-subsets of the `n` samples. -/
noncomputable def batchAvg (m : ℕ) (F : Finset (Fin n) → X) : X :=
  (n.choose m : ℝ)⁻¹ • ∑ B ∈ powersetCard m (univ : Finset (Fin n)), F B

theorem batchAvg_const {m : ℕ} (hmn : m ≤ n) (x : X) :
    batchAvg m (fun _ : Finset (Fin n) => x) = x := by
  unfold batchAvg
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast (Nat.choose_pos hmn).ne' : (n.choose m : ℝ) ≠ 0), one_smul]

theorem batchAvg_add (m : ℕ) (F G : Finset (Fin n) → X) :
    batchAvg m (fun B => F B + G B) = batchAvg m F + batchAvg m G := by
  unfold batchAvg
  rw [Finset.sum_add_distrib, smul_add]

theorem batchAvg_sub (m : ℕ) (F G : Finset (Fin n) → X) :
    batchAvg m (fun B => F B - G B) = batchAvg m F - batchAvg m G := by
  unfold batchAvg
  rw [Finset.sum_sub_distrib, smul_sub]

theorem batchAvg_smul (m : ℕ) (c : ℝ) (F : Finset (Fin n) → X) :
    batchAvg m (fun B => c • F B) = c • batchAvg m F := by
  unfold batchAvg
  rw [← Finset.smul_sum, smul_comm]

/-- Unbiasedness: the average batch mean is the population mean. -/
theorem batchAvg_batchMean {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (a : Fin n → X) :
    batchAvg m (fun B => batchMean m a B) = popMean a := by
  unfold batchAvg batchMean popMean
  rw [← Finset.smul_sum, sum_powersetCard_sum hm, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  congr 1
  have h := choose_mul_eq_choose_pred hm hmn
  have hC : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hcast : (m : ℝ) * n.choose m = n * ((n - 1).choose (m - 1) : ℝ) := by exact_mod_cast h
  field_simp
  linarith [hcast]

theorem batchAvg_batchMean_sub {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (a : Fin n → X) :
    batchAvg m (fun B => batchMean m a B - popMean a) = 0 := by
  rw [batchAvg_sub, batchAvg_batchMean hm hmn, batchAvg_const hmn, sub_self]

end BatchAvg

/-! ### The SGLD step on quadratic per-sample losses -/

/-- The minibatch gradient `H_B w − g_B` of quadratic per-sample losses. -/
noncomputable def minibatchGrad (m : ℕ) (Hs : Fin n → Matrix ι ι ℝ) (gs : Fin n → ι → ℝ)
    (B : Finset (Fin n)) (w : ι → ℝ) : ι → ℝ :=
  batchMean m (fun i => Hs i *ᵥ w - gs i) B

/-- One SGLD step: `w − h t (H_B w − g_B) + √(2h) ξ`. -/
noncomputable def sgldStep (h t : ℝ) (m : ℕ) (Hs : Fin n → Matrix ι ι ℝ) (gs : Fin n → ι → ℝ)
    (B : Finset (Fin n)) (w ξ : ι → ℝ) : ι → ℝ :=
  w - (h * t) • minibatchGrad m Hs gs B w + Real.sqrt (2 * h) • ξ

omit [DecidableEq ι] in
theorem popMean_affine (Hs : Fin n → Matrix ι ι ℝ) (gs : Fin n → ι → ℝ) (w : ι → ℝ) :
    popMean (fun i => Hs i *ᵥ w - gs i) = popMean Hs *ᵥ w - popMean gs := by
  unfold popMean
  rw [Finset.sum_sub_distrib, smul_sub, Matrix.smul_mulVec, Matrix.sum_mulVec]

theorem ulaStep_mulVec (H : Matrix ι ι ℝ) (h t : ℝ) (w : ι → ℝ) :
    ulaStep (t • H) h *ᵥ w = w - (h * t) • (H *ᵥ w) := by
  unfold ulaStep
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, smul_smul]

/-- **E8, the mean step**: `E[w'] = A w`. -/
theorem sgld_mean_step {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (Hs : Fin n → Matrix ι ι ℝ)
    (gs : Fin n → ι → ℝ) (hg : popMean gs = 0) (h t : ℝ) (w : ι → ℝ) :
    batchAvg m (fun B => stdExpVec (fun ξ => sgldStep h t m Hs gs B w ξ)) =
      ulaStep (t • popMean Hs) h *ᵥ w := by
  have h1 : ∀ B, stdExpVec (fun ξ => sgldStep h t m Hs gs B w ξ) =
      w - (h * t) • minibatchGrad m Hs gs B w := fun B => stdExpVec_affine _ _
  simp_rw [h1]
  rw [batchAvg_sub, batchAvg_const hmn, batchAvg_smul]
  unfold minibatchGrad
  rw [batchAvg_batchMean hm hmn, popMean_affine, hg, sub_zero, ulaStep_mulVec]

omit [DecidableEq ι] in
/-- The centred residual family `rᵢ = (Hᵢ − H) w − gᵢ`. -/
theorem residual_eq (Hs : Fin n → Matrix ι ι ℝ) (gs : Fin n → ι → ℝ) (hg : popMean gs = 0)
    (w : ι → ℝ) (i : Fin n) :
    (Hs i *ᵥ w - gs i) - popMean (fun i => Hs i *ᵥ w - gs i) = (Hs i - popMean Hs) *ᵥ w - gs i := by
  rw [popMean_affine, hg, sub_zero, Matrix.sub_mulVec]
  abel

omit [DecidableEq ι] in
theorem vecMulVec_mulVec_mulVec (A : Matrix ι ι ℝ) (w : ι → ℝ) :
    vecMulVec (A *ᵥ w) (A *ᵥ w) = A * vecMulVec w w * Aᵀ := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- **E8, the second-moment step (pointwise)**:
`E[w' w'ᵀ] = A wwᵀ Aᵀ + 2h • 1 + h²t² c ∑ᵢ rᵢ rᵢᵀ`. -/
theorem sgld_second_moment_step {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (Hs : Fin n → Matrix ι ι ℝ) (gs : Fin n → ι → ℝ) (hg : popMean gs = 0) {h : ℝ} (hh : 0 ≤ h)
    (t : ℝ) (w : ι → ℝ) :
    batchAvg m (fun B => stdExpMat (fun ξ =>
        vecMulVec (sgldStep h t m Hs gs B w ξ) (sgldStep h t m Hs gs B w ξ))) =
      ulaStep (t • popMean Hs) h * vecMulVec w w * (ulaStep (t • popMean Hs) h)ᵀ +
        (2 * h) • (1 : Matrix ι ι ℝ) +
        (h ^ 2 * t ^ 2 * ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1)))) •
          ∑ i, vecMulVec ((Hs i - popMean Hs) *ᵥ w - gs i) ((Hs i - popMean Hs) *ᵥ w - gs i) := by
  set a : Fin n → ι → ℝ := fun i => Hs i *ᵥ w - gs i with ha
  set A := ulaStep (t • popMean Hs) h with hA
  -- the Gaussian step
  have hgauss : ∀ B, stdExpMat (fun ξ =>
      vecMulVec (sgldStep h t m Hs gs B w ξ) (sgldStep h t m Hs gs B w ξ)) =
      vecMulVec (w - (h * t) • batchMean m a B) (w - (h * t) • batchMean m a B) +
        (2 * h) • (1 : Matrix ι ι ℝ) := by
    intro B
    have := stdExpMat_affine (w - (h * t) • minibatchGrad m Hs gs B w) (Real.sqrt (2 * h))
    rw [Real.sq_sqrt (by linarith)] at this
    exact this
  simp_rw [hgauss]
  -- centre the batch mean
  have hcent : ∀ B, w - (h * t) • batchMean m a B =
      A *ᵥ w - (h * t) • (batchMean m a B - popMean a) := by
    intro B
    rw [hA, ulaStep_mulVec, ha, popMean_affine, hg, sub_zero, smul_sub]
    abel
  simp_rw [hcent]
  -- expand the outer product
  have hexpand : ∀ B, vecMulVec (A *ᵥ w - (h * t) • (batchMean m a B - popMean a))
      (A *ᵥ w - (h * t) • (batchMean m a B - popMean a)) =
      vecMulVec (A *ᵥ w) (A *ᵥ w)
        - (h * t) • vecMulVec (A *ᵥ w) (batchMean m a B - popMean a)
        - (h * t) • vecMulVec (batchMean m a B - popMean a) (A *ᵥ w)
        + ((h * t) * (h * t)) • vecMulVec (batchMean m a B - popMean a)
          (batchMean m a B - popMean a) := by
    intro B
    simp only [sub_vecMulVec, vecMulVec_sub, smul_vecMulVec, vecMulVec_smul]
    module
  simp_rw [hexpand]
  rw [batchAvg_add, batchAvg_const hmn, batchAvg_add, batchAvg_sub, batchAvg_sub,
    batchAvg_const hmn, batchAvg_smul, batchAvg_smul, batchAvg_smul]
  -- the linear terms vanish
  have h0 := batchAvg_batchMean_sub hm hmn a
  have hlin1 : batchAvg m (fun B => vecMulVec (A *ᵥ w) (batchMean m a B - popMean a)) = 0 := by
    have : batchAvg m (fun B => vecMulVec (A *ᵥ w) (batchMean m a B - popMean a)) =
        outerBilin (ι := ι) (A *ᵥ w) (batchAvg m (fun B => batchMean m a B - popMean a)) := by
      unfold batchAvg
      rw [map_smul, map_sum]
      simp only [outerBilin, LinearMap.mk₂_apply]
    rw [this, h0, map_zero]
  have hlin2 : batchAvg m (fun B => vecMulVec (batchMean m a B - popMean a) (A *ᵥ w)) = 0 := by
    have : batchAvg m (fun B => vecMulVec (batchMean m a B - popMean a) (A *ᵥ w)) =
        outerBilin (ι := ι) (batchAvg m (fun B => batchMean m a B - popMean a)) (A *ᵥ w) := by
      unfold batchAvg
      rw [LinearMap.map_smul₂, LinearMap.map_sum₂]
      simp only [outerBilin, LinearMap.mk₂_apply]
    rw [this, h0, map_zero, LinearMap.zero_apply]
  -- the quadratic term is the finite population correction
  have hquad : batchAvg m (fun B => vecMulVec (batchMean m a B - popMean a)
      (batchMean m a B - popMean a)) =
      ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) •
        ∑ i, vecMulVec (a i - popMean a) (a i - popMean a) := by
    have := fpc_bilinear hm hmn hn (outerBilin (ι := ι)) a
    simp only [outerBilin, LinearMap.mk₂_apply] at this
    exact this
  rw [hlin1, hlin2, hquad, vecMulVec_mulVec_mulVec]
  have hres : ∀ i, a i - popMean a = (Hs i - popMean Hs) *ᵥ w - gs i := fun i =>
    residual_eq Hs gs hg w i
  simp_rw [hres]
  simp only [smul_zero, sub_zero, smul_smul]
  rw [show h * t * (h * t) * ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) =
    h ^ 2 * t ^ 2 * ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) by ring]
  abel

/-! ### The law form -/

omit [DecidableEq ι] in
theorem mul_mul_transpose_apply (A X : Matrix ι ι ℝ) (i j : ι) :
    (A * X * Aᵀ) i j = ∑ k, ∑ l, A i k * A j l * X k l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [DecidableEq ι] in
theorem vecMulVec_mulVec_left_apply (D : Matrix ι ι ℝ) (g w : ι → ℝ) (i j : ι) :
    vecMulVec (D *ᵥ w) g i j = ∑ l, (D i l * g j) * w l := by
  simp only [vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

omit [DecidableEq ι] in
theorem vecMulVec_mulVec_right_apply (D : Matrix ι ι ℝ) (g w : ι → ℝ) (i j : ι) :
    vecMulVec g (D *ᵥ w) i j = ∑ l, (g i * D j l) * w l := by
  simp only [vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

omit [DecidableEq ι] in
/-- The residual outer product as a matrix identity. -/
theorem vecMulVec_residual (D : Matrix ι ι ℝ) (g w : ι → ℝ) :
    vecMulVec (D *ᵥ w - g) (D *ᵥ w - g) =
      D * vecMulVec w w * Dᵀ - vecMulVec (D *ᵥ w) g - vecMulVec g (D *ᵥ w) + vecMulVec g g := by
  rw [sub_vecMulVec, vecMulVec_sub, vecMulVec_sub, vecMulVec_mulVec_mulVec]
  abel

section Law

variable (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] {q : ι → ℝ} {M : Matrix ι ι ℝ}

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem integrable_quad_entry (hint2 : ∀ i j, Integrable (fun w : ι → ℝ => w i * w j) μ)
    (A : Matrix ι ι ℝ) (i j : ι) :
    Integrable (fun w : ι → ℝ => (A * vecMulVec w w * Aᵀ) i j) μ := by
  simp_rw [mul_mul_transpose_apply, vecMulVec_apply]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (hint2 k l).const_mul _

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem integral_quad_entry (hint2 : ∀ i j, Integrable (fun w : ι → ℝ => w i * w j) μ)
    (hM : ∀ i j, ∫ w, w i * w j ∂μ = M i j) (A : Matrix ι ι ℝ) (i j : ι) :
    ∫ w, (A * vecMulVec w w * Aᵀ) i j ∂μ = (A * M * Aᵀ) i j := by
  simp_rw [mul_mul_transpose_apply, vecMulVec_apply]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hint2 k l).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (hint2 k l).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, hM]

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem integrable_left_entry (hint1 : ∀ i, Integrable (fun w : ι → ℝ => w i) μ)
    (D : Matrix ι ι ℝ) (g : ι → ℝ) (i j : ι) :
    Integrable (fun w : ι → ℝ => vecMulVec (D *ᵥ w) g i j) μ := by
  simp_rw [vecMulVec_mulVec_left_apply]
  exact integrable_finsetSum _ fun l _ => (hint1 l).const_mul _

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem integral_left_entry (hint1 : ∀ i, Integrable (fun w : ι → ℝ => w i) μ)
    (hq : ∀ i, ∫ w, w i ∂μ = q i) (D : Matrix ι ι ℝ) (g : ι → ℝ) (i j : ι) :
    ∫ w, vecMulVec (D *ᵥ w) g i j ∂μ = vecMulVec (D *ᵥ q) g i j := by
  simp_rw [vecMulVec_mulVec_left_apply]
  rw [integral_finsetSum _ fun l _ => (hint1 l).const_mul _]
  simp_rw [integral_const_mul, hq]

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem integrable_right_entry (hint1 : ∀ i, Integrable (fun w : ι → ℝ => w i) μ)
    (D : Matrix ι ι ℝ) (g : ι → ℝ) (i j : ι) :
    Integrable (fun w : ι → ℝ => vecMulVec g (D *ᵥ w) i j) μ := by
  simp_rw [vecMulVec_mulVec_right_apply]
  exact integrable_finsetSum _ fun l _ => (hint1 l).const_mul _

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem integral_right_entry (hint1 : ∀ i, Integrable (fun w : ι → ℝ => w i) μ)
    (hq : ∀ i, ∫ w, w i ∂μ = q i) (D : Matrix ι ι ℝ) (g : ι → ℝ) (i j : ι) :
    ∫ w, vecMulVec g (D *ᵥ w) i j ∂μ = vecMulVec g (D *ᵥ q) i j := by
  simp_rw [vecMulVec_mulVec_right_apply]
  rw [integral_finsetSum _ fun l _ => (hint1 l).const_mul _]
  simp_rw [integral_const_mul, hq]

omit [DecidableEq ι] in
theorem integrable_residual_entry (hint1 : ∀ i, Integrable (fun w : ι → ℝ => w i) μ)
    (hint2 : ∀ i j, Integrable (fun w : ι → ℝ => w i * w j) μ) (D : Matrix ι ι ℝ) (g : ι → ℝ)
    (i j : ι) :
    Integrable (fun w : ι → ℝ => vecMulVec (D *ᵥ w - g) (D *ᵥ w - g) i j) μ := by
  simp_rw [vecMulVec_residual, Matrix.add_apply, Matrix.sub_apply]
  have h1 := integrable_quad_entry μ hint2 D i j
  have h2 := integrable_left_entry μ hint1 D g i j
  have h3 := integrable_right_entry μ hint1 D g i j
  have h12 : Integrable (fun w : ι → ℝ =>
      (D * vecMulVec w w * Dᵀ) i j - vecMulVec (D *ᵥ w) g i j) μ := h1.sub h2
  have h123 : Integrable (fun w : ι → ℝ =>
      (D * vecMulVec w w * Dᵀ) i j - vecMulVec (D *ᵥ w) g i j - vecMulVec g (D *ᵥ w) i j) μ :=
    h12.sub h3
  exact h123.add (integrable_const _)

omit [DecidableEq ι] in
/-- `∫ (D w − g)(D w − g)ᵀ = D M Dᵀ − (Dq)gᵀ − g(Dq)ᵀ + ggᵀ`, entrywise. -/
theorem integral_residual_entry (hint1 : ∀ i, Integrable (fun w : ι → ℝ => w i) μ)
    (hint2 : ∀ i j, Integrable (fun w : ι → ℝ => w i * w j) μ)
    (hq : ∀ i, ∫ w, w i ∂μ = q i) (hM : ∀ i j, ∫ w, w i * w j ∂μ = M i j)
    (D : Matrix ι ι ℝ) (g : ι → ℝ) (i j : ι) :
    ∫ w, vecMulVec (D *ᵥ w - g) (D *ᵥ w - g) i j ∂μ =
      (D * M * Dᵀ - vecMulVec (D *ᵥ q) g - vecMulVec g (D *ᵥ q) + vecMulVec g g) i j := by
  simp_rw [vecMulVec_residual, Matrix.add_apply, Matrix.sub_apply]
  have h1 := integrable_quad_entry μ hint2 D i j
  have h2 := integrable_left_entry μ hint1 D g i j
  have h3 := integrable_right_entry μ hint1 D g i j
  have h12 : Integrable (fun w : ι → ℝ =>
      (D * vecMulVec w w * Dᵀ) i j - vecMulVec (D *ᵥ w) g i j) μ := h1.sub h2
  have h123 : Integrable (fun w : ι → ℝ =>
      (D * vecMulVec w w * Dᵀ) i j - vecMulVec (D *ᵥ w) g i j - vecMulVec g (D *ᵥ w) i j) μ :=
    h12.sub h3
  rw [integral_add h123 (integrable_const _), integral_sub h12 h3, integral_sub h1 h2,
    integral_quad_entry μ hint2 hM, integral_left_entry μ hint1 hq, integral_right_entry μ hint1 hq,
    integral_const]
  simp

/-- **E8, the law form**: integrating the one-step second moment against a law with mean `q` and
raw second moment `M` gives the full law plus a mean correction:
`∫ E[w'w'ᵀ] = e8FullStep (t•H) h t C_g Hs H m M − h²t² c ∑ᵢ (Dᵢ q gᵢᵀ + gᵢ qᵀ Dᵢᵀ)`. -/
theorem sgld_law_step {m : ℕ} (Hs : Fin n → Matrix ι ι ℝ) (gs : Fin n → ι → ℝ) (h t : ℝ)
    (hint1 : ∀ i, Integrable (fun w : ι → ℝ => w i) μ)
    (hint2 : ∀ i j, Integrable (fun w : ι → ℝ => w i * w j) μ)
    (hq : ∀ i, ∫ w, w i ∂μ = q i) (hM : ∀ i j, ∫ w, w i * w j ∂μ = M i j) :
    Matrix.of (fun i j => ∫ w, (ulaStep (t • popMean Hs) h * vecMulVec w w *
        (ulaStep (t • popMean Hs) h)ᵀ + (2 * h) • (1 : Matrix ι ι ℝ) +
        (h ^ 2 * t ^ 2 * ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1)))) •
          ∑ k, vecMulVec ((Hs k - popMean Hs) *ᵥ w - gs k)
            ((Hs k - popMean Hs) *ᵥ w - gs k)) i j ∂μ)
      = e8FullStep (t • popMean Hs) h t
          (((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) • ∑ k, vecMulVec (gs k) (gs k))
          Hs (popMean Hs) m M
        - (h ^ 2 * t ^ 2 * ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1)))) •
          ∑ k, (vecMulVec ((Hs k - popMean Hs) *ᵥ q) (gs k) +
            vecMulVec (gs k) ((Hs k - popMean Hs) *ᵥ q)) := by
  set A := ulaStep (t • popMean Hs) h with hA
  set c : ℝ := (1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1)) with hc
  ext i j
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  have hres : ∀ k, Integrable (fun w : ι → ℝ =>
      vecMulVec ((Hs k - popMean Hs) *ᵥ w - gs k) ((Hs k - popMean Hs) *ᵥ w - gs k) i j) μ :=
    fun k => integrable_residual_entry μ hint1 hint2 (Hs k - popMean Hs) (gs k) i j
  have hsum : Integrable (fun w : ι → ℝ => h ^ 2 * t ^ 2 * c *
      ∑ k, vecMulVec ((Hs k - popMean Hs) *ᵥ w - gs k) ((Hs k - popMean Hs) *ᵥ w - gs k) i j) μ :=
    (integrable_finsetSum _ fun k _ => hres k).const_mul _
  have hquadI := integrable_quad_entry μ hint2 A i j
  have hconstI : Integrable (fun _ : ι → ℝ => 2 * h * (1 : Matrix ι ι ℝ) i j) μ :=
    integrable_const _
  have h12 : Integrable (fun w : ι → ℝ =>
      (A * vecMulVec w w * Aᵀ) i j + 2 * h * (1 : Matrix ι ι ℝ) i j) μ := hquadI.add hconstI
  rw [integral_add h12 hsum, integral_add hquadI hconstI, integral_quad_entry μ hint2 hM,
    integral_const, integral_const_mul, integral_finsetSum _ fun k _ => hres k]
  simp_rw [integral_residual_entry μ hint1 hint2 hq hM]
  simp only [e8FullStep, fullStep, fullLinear, stateTerm, minibatchNoise, minibatchCoeff_eq,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    measureReal_def, measure_univ, ENNReal.toReal_one, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [← hA, ← hc]
  simp only [← Finset.mul_sum]
  ring

/-- **E8 for a centred law**: `∫ E[w'w'ᵀ] = e8FullStep (t•H) h t C_g Hs H m M`; a centred
stationary law satisfies the note's full law exactly. -/
theorem sgld_law_step_centred {m : ℕ} (Hs : Fin n → Matrix ι ι ℝ) (gs : Fin n → ι → ℝ) (h t : ℝ)
    (hint1 : ∀ i, Integrable (fun w : ι → ℝ => w i) μ)
    (hint2 : ∀ i j, Integrable (fun w : ι → ℝ => w i * w j) μ)
    (hq : ∀ i, ∫ w, w i ∂μ = 0) (hM : ∀ i j, ∫ w, w i * w j ∂μ = M i j) :
    Matrix.of (fun i j => ∫ w, (ulaStep (t • popMean Hs) h * vecMulVec w w *
        (ulaStep (t • popMean Hs) h)ᵀ + (2 * h) • (1 : Matrix ι ι ℝ) +
        (h ^ 2 * t ^ 2 * ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1)))) •
          ∑ k, vecMulVec ((Hs k - popMean Hs) *ᵥ w - gs k)
            ((Hs k - popMean Hs) *ᵥ w - gs k)) i j ∂μ)
      = e8FullStep (t • popMean Hs) h t
          (((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) • ∑ k, vecMulVec (gs k) (gs k))
          Hs (popMean Hs) m M := by
  rw [sgld_law_step μ Hs gs h t hint1 hint2 (q := 0) (fun i => by rw [hq i]; rfl) hM]
  simp

end Law

/-- **E8 assembled**: the average over batch and noise of `w'w'ᵀ`, integrated against a centred
law with second moment `M`, is `e8FullStep … M`. -/
theorem sgld_step_law_centred {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (Hs : Fin n → Matrix ι ι ℝ) (gs : Fin n → ι → ℝ) (hg : popMean gs = 0) {h : ℝ} (hh : 0 ≤ h)
    (t : ℝ) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] {M : Matrix ι ι ℝ}
    (hint1 : ∀ i, Integrable (fun w : ι → ℝ => w i) μ)
    (hint2 : ∀ i j, Integrable (fun w : ι → ℝ => w i * w j) μ)
    (hq : ∀ i, ∫ w, w i ∂μ = 0) (hM : ∀ i j, ∫ w, w i * w j ∂μ = M i j) :
    Matrix.of (fun i j => ∫ w, (batchAvg m (fun B => stdExpMat (fun ξ =>
        vecMulVec (sgldStep h t m Hs gs B w ξ) (sgldStep h t m Hs gs B w ξ)))) i j ∂μ)
      = e8FullStep (t • popMean Hs) h t
          (((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) • ∑ k, vecMulVec (gs k) (gs k))
          Hs (popMean Hs) m M := by
  rw [← sgld_law_step_centred μ Hs gs h t hint1 hint2 hq hM]
  congr 1
  funext i j
  congr 1
  funext w
  rw [sgld_second_moment_step hm hmn hn Hs gs hg hh t w]

end Laplace.Sampler
