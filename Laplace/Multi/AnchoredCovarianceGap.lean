/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AnchoredVarianceGap
import Laplace.Multi.LocalisedCovKOrder2Multi

/-!
# The anchored Gaussian covariance gap: E3's susceptibilities of quadratic observables (E3/E2)

For a tilted Gaussian `N(m, Σ)`, `Σ = P⁻¹`, `m = P⁻¹v`, and symmetric `H`, `B`, the covariance of
the
quadratic energy with a quadratic-plus-linear probe is
**`Cov_{P,v}(½uᵀHu, ½uᵀBu + b·u) = ½tr(HΣBΣ) + (Hm)ᵀΣ(Bm) + (Hm)ᵀΣb`**
(`tiltedCov_quadForm_quadProbe`),
from the mixed Wick integral `∫(uᵀHu)(uᵀBu) gw = Z(tr(HΣ)tr(BΣ) + 2tr(HΣBΣ))`
(`integral_quadForm_mul_quadForm_mul_gaussianWeight_matCLM`); in particular
`Cov_{P,v}(uᵀHu, uᵀBu) = 2tr(HΣBΣ) + 4(Hm)ᵀΣ(Bm)` (`tiltedCov_quadForm`). For E3's anchored Gaussian
(`P = tH + gI`, `aᵢ = (Uᵀv)ᵢ`, `B̃ = UᵀBU`, `b̃ = Uᵀb`, `pᵢ = tλᵢ + g`) this is
**`t²Cov = ½t²∑ᵢλᵢB̃ᵢᵢ/pᵢ² + t²∑ᵢⱼλᵢaᵢB̃ᵢⱼaⱼ/(pᵢ²pⱼ) + t²∑ᵢb̃ᵢλᵢaᵢ/pᵢ²`**
(`anchoredGaussianCov_eq`), which expands as
`∑ᵢ(B̃ᵢᵢ/(2λᵢ) + b̃ᵢaᵢ/λᵢ) + (−g∑ᵢB̃ᵢᵢ/λᵢ² + ∑ᵢⱼB̃ᵢⱼaᵢaⱼ/(λᵢλⱼ) − 2g∑ᵢb̃ᵢaᵢ/λᵢ²)/t + O(t⁻²)`
(`anchoredGaussianCov_rate2`). Against E2's exact second-order susceptibility
(`localisedRotatedAnharmonic_covK_order2_rate`) the gap is
**`t²Cov_loc(L∘A, ψ) − t²Cov_anch = −∑ᵢb̃ᵢαᵢ/(2λᵢ²) + Γ_B/t + O(t⁻²)`**
(`localisedCov_anchoredGap`):
a probe with a linear part sees the cubic mean shift already at leading order, while for purely
quadratic
probes the anchored prediction is correct to leading order and off by `tr(B̃Γ)/t` with the purely
anharmonic
gap matrix `Γᵢᵢ = 5αᵢ²/(4λᵢ⁴) − 2aᵢαᵢ/λᵢ³ − γᵢ/(2λᵢ³)`, `Γᵢⱼ = cᵢcⱼ − aᵢaⱼ/(λᵢλⱼ)` (`i ≠ j`), plus
the linear part's
`2b̃ᵢ(m₂ᵢ + gaᵢ/λᵢ²)` (`locCovGapCoeff`).
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Integrand expansions and integrability (mixed forms) -/

omit [DecidableEq ι] in
theorem quadForm_mul_quadForm_mul_eq_sum (H B : Matrix ι ι ℝ) (u : ι → ℝ) (G : ℝ) :
    (u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) * G =
      ∑ a, ∑ c, ∑ b, ∑ d, H a b * B c d * (u a * u b * u c * u d * G) := by
  rw [dotProduct_mulVec_eq_sum H, dotProduct_mulVec_eq_sum B, Finset.sum_mul_sum]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring

omit [DecidableEq ι] in
theorem dotProduct_mul_dotProduct_mul_eq_sum (w₁ w₂ u : ι → ℝ) (G : ℝ) :
    (u ⬝ᵥ w₁) * (u ⬝ᵥ w₂) * G = ∑ a, ∑ b, w₁ a * w₂ b * (u a * u b * G) := by
  simp only [dotProduct]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem integrable_quadForm_mul_quadForm_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (H B : Matrix ι ι ℝ) :
    Integrable (fun u : ι → ℝ => (u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) * gaussianWeight (matCLM P) u) := by
  simp_rw [quadForm_mul_quadForm_mul_eq_sum]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun d _ =>
      ((laplaceCov4MomentHypotheses_matCLM hP).int_4moment a b c d).const_mul _

theorem integrable_dotProduct_mul_dotProduct_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (w₁ w₂ : ι → ℝ) :
    Integrable (fun u : ι → ℝ => (u ⬝ᵥ w₁) * (u ⬝ᵥ w₂) * gaussianWeight (matCLM P) u) := by
  simp_rw [dotProduct_mul_dotProduct_mul_eq_sum]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_coord_mul_gaussianWeight_matCLM hP a b).const_mul _

/-! ### The mixed centred Gaussian moments -/

/-- **Mixed Wick**: `∫(uᵀHu)(uᵀBu) gw = Z·(tr(HΣ)tr(BΣ) + 2·tr(HΣBΣ))`, `Σ = P⁻¹`. -/
theorem integral_quadForm_mul_quadForm_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (H : Matrix ι ι ℝ) {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    ∫ u : ι → ℝ, (u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) * ((∑ i, ∑ j, H i j * P⁻¹ i j) * (∑ i, ∑ j, B i j * P⁻¹ i j) +
        2 * ∑ a, ∑ c, (H * P⁻¹) a c * (B * P⁻¹) c a) := by
  have hI : ∀ a b c d : ι, Integrable (fun u : ι → ℝ =>
      H a b * B c d * (u a * u b * u c * u d * gaussianWeight (matCLM P) u)) :=
    fun a b c d => ((laplaceCov4MomentHypotheses_matCLM hP).int_4moment a b c d).const_mul _
  simp_rw [quadForm_mul_quadForm_mul_eq_sum]
  have key : ∫ u : ι → ℝ, ∑ a, ∑ c, ∑ b, ∑ d,
      H a b * B c d * (u a * u b * u c * u d * gaussianWeight (matCLM P) u) =
      ∑ a, ∑ c, ∑ b, ∑ d, H a b * B c d * (gaussianZ (matCLM P) *
        (P⁻¹ a d * P⁻¹ b c + P⁻¹ b d * P⁻¹ a c + P⁻¹ c d * P⁻¹ a b)) := by
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ =>
      integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun d _ => hI a b c d]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun d _ => hI a b c d]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun d _ => hI a b c d]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ fun d _ => hI a b c d]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_const_mul, gaussian_fourth_moment_matCLM hP]
  rw [key]
  have hsym := inv_apply_symm hP
  have hBs := apply_symm_of_isHermitian hB
  have h3 : ∑ a, ∑ c, ∑ b, ∑ d, H a b * B c d * (P⁻¹ c d * P⁻¹ a b) =
      (∑ i, ∑ j, H i j * P⁻¹ i j) * (∑ i, ∑ j, B i j * P⁻¹ i j) := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring
  have h1 : ∑ a, ∑ c, ∑ b, ∑ d, H a b * B c d * (P⁻¹ a d * P⁻¹ b c) =
      ∑ a, ∑ c, (H * P⁻¹) a c * (B * P⁻¹) c a := by
    simp only [Matrix.mul_apply, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [hsym d a]; ring
  have h2 : ∑ a, ∑ c, ∑ b, ∑ d, H a b * B c d * (P⁻¹ b d * P⁻¹ a c) =
      ∑ a, ∑ c, (H * P⁻¹) a c * (B * P⁻¹) c a := by
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ c, ∑ b, ∑ d, H a b * B c d * (P⁻¹ b d * P⁻¹ a c)
        = ∑ c, ∑ b, ∑ d, H a b * B d c * (P⁻¹ a c * P⁻¹ b d) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun d _ => by rw [hBs c d]; ring
      _ = ∑ b, ∑ c, ∑ d, H a b * B d c * (P⁻¹ a c * P⁻¹ b d) := Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ c, H a b * B d c * (P⁻¹ a c * P⁻¹ b d) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ d, ∑ b, ∑ c, H a b * B d c * (P⁻¹ a c * P⁻¹ b d) := Finset.sum_comm
  have hsplit : ∀ a c b d : ι, H a b * B c d * (gaussianZ (matCLM P) *
      (P⁻¹ a d * P⁻¹ b c + P⁻¹ b d * P⁻¹ a c + P⁻¹ c d * P⁻¹ a b)) =
      gaussianZ (matCLM P) * (H a b * B c d * (P⁻¹ a d * P⁻¹ b c)) +
        gaussianZ (matCLM P) * (H a b * B c d * (P⁻¹ b d * P⁻¹ a c)) +
        gaussianZ (matCLM P) * (H a b * B c d * (P⁻¹ c d * P⁻¹ a b)) := fun a c b d => by ring
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2, h3]
  ring

/-- `∫(uᵀw₁)(uᵀw₂) gw = Z·w₁ᵀΣw₂`. -/
theorem integral_dotProduct_mul_dotProduct_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (w₁ w₂ : ι → ℝ) :
    ∫ u : ι → ℝ, (u ⬝ᵥ w₁) * (u ⬝ᵥ w₂) * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) * (w₁ ⬝ᵥ P⁻¹ *ᵥ w₂) := by
  simp_rw [dotProduct_mul_dotProduct_mul_eq_sum]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_coord_mul_gaussianWeight_matCLM hP a b).const_mul _,
    dotProduct_mulVec_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (integrable_coord_mul_gaussianWeight_matCLM hP a b).const_mul
      _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, integral_coord_mul_gaussianWeight_matCLM hP]
  ring


/-! ### An orthogonal diagonalising frame `UᵀU = 1`, `UᵀHU = diag(λ)` -/

section Frame

variable {U H : Matrix ι ι ℝ} {lam : ι → ℝ}

theorem mul_transpose_eq_one_of (hU : Uᵀ * U = 1) : U * Uᵀ = 1 := mul_eq_one_comm.1 hU

theorem dotProduct_mulVec_orth (hU : Uᵀ * U = 1) (w z : ι → ℝ) :
    (U *ᵥ w) ⬝ᵥ (U *ᵥ z) = w ⬝ᵥ z := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

theorem frame_eq_conj (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam) :
    H = U * diagonal lam * Uᵀ := by
  have hU' := mul_transpose_eq_one_of hU
  rw [← hdiag]
  calc H = (U * Uᵀ) * H * (U * Uᵀ) := by rw [hU', Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᵀ * H * U) * Uᵀ := by simp only [Matrix.mul_assoc]

theorem mul_frame_eq_diag (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam) :
    H * U = U * diagonal lam := by
  rw [frame_eq_conj hU hdiag, Matrix.mul_assoc, hU, Matrix.mul_one]

theorem posDef_conj_diagonal (hU : Uᵀ * U = 1) {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    (U * diagonal v * Uᵀ).PosDef := by
  have hU' := mul_transpose_eq_one_of hU
  have hd : (diagonal v).PosDef := Matrix.PosDef.diagonal hv
  have hinj : Function.Injective Uᵀ.mulVec := by
    intro x y hxy
    have := congrArg U.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hU'] using this
  have := Matrix.PosDef.conjTranspose_mul_mul_same hd hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at this

theorem posDef_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam) (hlam : ∀ i, 0 < lam i) :
    H.PosDef := by
  rw [frame_eq_conj hU hdiag]
  exact posDef_conj_diagonal hU hlam

theorem localisedPrecision_eq_conj_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam)
    (t g : ℝ) :
    t • H + g • (1 : Matrix ι ι ℝ) = U * diagonal (fun i => t * lam i + g) * Uᵀ := by
  have hU' := mul_transpose_eq_one_of hU
  have e : diagonal (fun i => t * lam i + g) = t • diagonal lam + g • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [e]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU']
  rw [← frame_eq_conj hU hdiag]

theorem posDef_localisedPrecision_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 < lam i) {t g : ℝ} (ht : 0 < t) (hg : 0 ≤ g) :
    (t • H + g • (1 : Matrix ι ι ℝ)).PosDef := by
  rw [localisedPrecision_eq_conj_frame hU hdiag]
  exact posDef_conj_diagonal hU fun i => by have := hlam i; positivity

theorem inv_localisedPrecision_eq_conj_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 < lam i) {t g : ℝ} (ht : 0 < t) (hg : 0 ≤ g) :
    (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ = U * diagonal (fun i => 1 / (t * lam i + g)) * Uᵀ := by
  have hU' := mul_transpose_eq_one_of hU
  have e : (fun i => (t * lam i + g) * (1 / (t * lam i + g))) = fun _ => (1 : ℝ) := by
    funext i
    have : t * lam i + g ≠ 0 := by have := hlam i; positivity
    field_simp
  apply Matrix.inv_eq_right_inv
  rw [localisedPrecision_eq_conj_frame hU hdiag]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
    Matrix.diagonal_mul_diagonal, e, Matrix.diagonal_one, Matrix.one_mul, hU']

theorem mul_inv_localisedPrecision_eq_conj_frame (hU : Uᵀ * U = 1)
    (hdiag : Uᵀ * H * U = diagonal lam) (hlam : ∀ i, 0 < lam i) {t g : ℝ} (ht : 0 < t) (hg : 0 ≤ g)
        :
    H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ =
      U * diagonal (fun i => lam i / (t * lam i + g)) * Uᵀ := by
  have hd : (fun i => lam i * (1 / (t * lam i + g))) = fun i => lam i / (t * lam i + g) := by
    funext i
    ring
  rw [inv_localisedPrecision_eq_conj_frame hU hdiag hlam ht hg, ← Matrix.mul_assoc, ←
      Matrix.mul_assoc,
    mul_frame_eq_diag hU hdiag, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal, hd]

theorem tiltMean_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam) (hlam : ∀ i, 0 < lam i)
    {t g : ℝ} (ht : 0 < t) (hg : 0 ≤ g) (v : ι → ℝ) :
    tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v =
      U *ᵥ (diagonal (fun i => 1 / (t * lam i + g)) *ᵥ (Uᵀ *ᵥ v)) := by
  unfold tiltMean
  rw [inv_localisedPrecision_eq_conj_frame hU hdiag hlam ht hg, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]

theorem mulVec_tiltMean_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 < lam i) {t g : ℝ} (ht : 0 < t) (hg : 0 ≤ g) (v : ι → ℝ) :
    H *ᵥ tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v =
      U *ᵥ (diagonal (fun i => lam i / (t * lam i + g)) *ᵥ (Uᵀ *ᵥ v)) := by
  unfold tiltMean
  rw [Matrix.mulVec_mulVec, mul_inv_localisedPrecision_eq_conj_frame hU hdiag hlam ht hg,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

omit [DecidableEq ι] in
theorem mulVec_apply_eq_sum (M : Matrix ι ι ℝ) (y : ι → ℝ) (i : ι) :
    (M *ᵥ y) i = ∑ j, M i j * y j := by
  simp [Matrix.mulVec, dotProduct]

theorem dotProduct_diagonal_mulVec_mulVec (d : ι → ℝ) (M : Matrix ι ι ℝ) (x y : ι → ℝ) :
    x ⬝ᵥ (diagonal d *ᵥ (M *ᵥ y)) = ∑ i, ∑ j, x i * d i * (M i j * y j) := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  simp only [mulVec_apply_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `tr(H(tH+gI)⁻¹B(tH+gI)⁻¹) = ∑ᵢ (λᵢ/pᵢ)·B̃ᵢᵢ·(1/pᵢ)`, `B̃ = UᵀBU`. -/
theorem trace_frame_mixed (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 < lam i) {t g : ℝ} (ht : 0 < t) (hg : 0 ≤ g) (B : Matrix ι ι ℝ) :
    ∑ a, ∑ c, (H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) a c *
        (B * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) c a =
      ∑ i, lam i / (t * lam i + g) * (Uᵀ * B * U) i i * (1 / (t * lam i + g)) := by
  have e : ∑ a, ∑ c, (H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) a c *
      (B * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) c a =
      Matrix.trace ((H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) *
        (B * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [e, mul_inv_localisedPrecision_eq_conj_frame hU hdiag hlam ht hg,
    inv_localisedPrecision_eq_conj_frame hU hdiag hlam ht hg]
  have e2 : U * diagonal (fun i => lam i / (t * lam i + g)) * Uᵀ *
      (B * (U * diagonal (fun i => 1 / (t * lam i + g)) * Uᵀ)) =
      U * (diagonal (fun i => lam i / (t * lam i + g)) * (Uᵀ * B * U) *
        diagonal (fun i => 1 / (t * lam i + g))) * Uᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e2, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- `(Hm)ᵀ(tH+gI)⁻¹(Bm)` in the frame, `m = (tH+gI)⁻¹v`, `aᵢ = (Uᵀv)ᵢ`. -/
theorem cross_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam) (hlam : ∀ i, 0 < lam i)
    {t g : ℝ} (ht : 0 < t) (hg : 0 ≤ g) (v : ι → ℝ) (B : Matrix ι ι ℝ) :
    (H *ᵥ tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v) ⬝ᵥ (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ
        (B *ᵥ tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v) =
      ∑ i, ∑ j, lam i / (t * lam i + g) * (Uᵀ *ᵥ v) i * (1 / (t * lam i + g)) *
        ((Uᵀ * B * U) i j * (1 / (t * lam j + g) * (Uᵀ *ᵥ v) j)) := by
  rw [mulVec_tiltMean_frame hU hdiag hlam ht hg v, tiltMean_frame hU hdiag hlam ht hg v,
    inv_localisedPrecision_eq_conj_frame hU hdiag hlam ht hg]
  set a := Uᵀ *ᵥ v with ha
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec_orth hU,
    Matrix.mulVec_mulVec _ Uᵀ B, Matrix.mulVec_mulVec _ (Uᵀ * B) U,
    dotProduct_diagonal_mulVec_mulVec]
  simp only [Matrix.mulVec_diagonal]

/-- `(Hm)ᵀ(tH+gI)⁻¹b` in the frame. -/
theorem linear_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam) (hlam : ∀ i, 0 < lam i)
    {t g : ℝ} (ht : 0 < t) (hg : 0 ≤ g) (v b : ι → ℝ) :
    (H *ᵥ tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v) ⬝ᵥ (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ b =
      ∑ i, lam i / (t * lam i + g) * (Uᵀ *ᵥ v) i * (1 / (t * lam i + g) * (Uᵀ *ᵥ b) i) := by
  rw [mulVec_tiltMean_frame hU hdiag hlam ht hg v, inv_localisedPrecision_eq_conj_frame hU hdiag
      hlam ht hg,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec_orth hU]
  simp only [dotProduct, Matrix.mulVec_diagonal]

end Frame


/-! ### Tilted Gaussian covariances of the quadratic energy with quadratic-plus-linear probes -/

theorem integral_quadForm_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (H : Matrix ι ι ℝ) :
    ∫ u : ι → ℝ, (u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) * ∑ i, ∑ j, H i j * P⁻¹ i j := by
  have h := gaussian_quadForm_integral_posDef hP (matCLM H)
  simp_rw [quadForm_matCLM, hessInvPairing_matCLM] at h
  exact h

/-- The tilted mean of a quadratic-plus-linear probe: `⟨½uᵀBu + b·u⟩_{P,v} = ½(tr(BΣ) + mᵀBm) +
m·b`. -/
theorem tiltedExpectation_quadProbe {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ)
    {B : Matrix ι ι ℝ} (hB : B.IsHermitian) (b : ι → ℝ) :
    tiltedExpectation P v (fun u => 1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b) =
      1 / 2 * (∑ i, ∑ j, B i j * P⁻¹ i j + tiltMean P v ⬝ᵥ B *ᵥ tiltMean P v) + tiltMean P v ⬝ᵥ b
          := by
  rw [tiltedExpectation_eq hP v]
  set m := tiltMean P v with hm
  have hZ0 : gaussianZ (matCLM P) ≠ 0 := (gaussianZ_matCLM_pos hP).ne'
  have hZ : ∫ u : ι → ℝ, gaussianWeight (matCLM P) u = gaussianZ (matCLM P) := rfl
  have hlinB : ∀ u : ι → ℝ, (u + m) ⬝ᵥ B *ᵥ (u + m) =
      u ⬝ᵥ B *ᵥ u + 2 * (u ⬝ᵥ (B *ᵥ m)) + m ⬝ᵥ B *ᵥ m := by
    intro u
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_mulVec_symm_of_isHermitian hB m u]
    ring
  have hexp : ∀ u : ι → ℝ, (1 / 2 * ((u + m) ⬝ᵥ B *ᵥ (u + m)) + (u + m) ⬝ᵥ b) * gaussianWeight
      (matCLM P) u = (((1 / 2) * ((u ⬝ᵥ B *ᵥ u) * gaussianWeight (matCLM P) u) + (1) * ((u ⬝ᵥ (B *ᵥ
      m)) * gaussianWeight (matCLM P) u)) + ((1 / 2 * (m ⬝ᵥ B *ᵥ m)) * (gaussianWeight (matCLM P) u)
      + ((1) * ((u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) * (gaussianWeight (matCLM P)
      u)))) := by
    intro u
    rw [hlinB, add_dotProduct]
    ring
  simp_rw [hexp]
  have I1 := (integrable_quadForm_mul_gaussianWeight_matCLM hP B).const_mul (1 / 2)
  have I2 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (B *ᵥ m)).const_mul (1)
  have I3 : Integrable (fun u : ι → ℝ => (1 / 2) * ((u ⬝ᵥ B *ᵥ u) * gaussianWeight (matCLM P) u) +
      (1) * ((u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u)) := I1.add I2
  have I4 := (integrable_gaussianWeight_matCLM hP).const_mul (1 / 2 * (m ⬝ᵥ B *ᵥ m))
  have I5 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP b).const_mul (1)
  have I6 := (integrable_gaussianWeight_matCLM hP).const_mul (m ⬝ᵥ b)
  have I7 : Integrable (fun u : ι → ℝ => (1) * ((u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) *
      (gaussianWeight (matCLM P) u)) := I5.add I6
  have I8 : Integrable (fun u : ι → ℝ => (1 / 2 * (m ⬝ᵥ B *ᵥ m)) * (gaussianWeight (matCLM P) u) +
      ((1) * ((u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) * (gaussianWeight (matCLM P) u)))
      := I4.add I7
  have I9 : Integrable (fun u : ι → ℝ => ((1 / 2) * ((u ⬝ᵥ B *ᵥ u) * gaussianWeight (matCLM P) u) +
      (1) * ((u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u)) + ((1 / 2 * (m ⬝ᵥ B *ᵥ m)) *
      (gaussianWeight (matCLM P) u) + ((1) * ((u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) *
      (gaussianWeight (matCLM P) u)))) := I3.add I8
  rw [integral_add I3 I8, integral_add I1 I2, integral_add I4 I7, integral_add I5 I6]
  simp only [integral_const_mul]
  rw [integral_quadForm_mul_gaussianWeight_matCLM hP B,
    integral_dotProduct_mul_gaussianWeight_matCLM hP (B *ᵥ m), hZ,
    integral_dotProduct_mul_gaussianWeight_matCLM hP b]
  field_simp
  ring

/-- **The tilted Gaussian covariance of the quadratic energy with a quadratic-plus-linear probe**:
`Cov_{P,v}(½uᵀHu, ½uᵀBu + b·u) = ½tr(HΣBΣ) + (Hm)ᵀΣ(Bm) + (Hm)ᵀΣb`, `Σ = P⁻¹`, `m = P⁻¹v`. -/
theorem tiltedCov_quadForm_quadProbe {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ)
    {H B : Matrix ι ι ℝ} (hH : H.IsHermitian) (hB : B.IsHermitian) (b : ι → ℝ) :
    tiltedExpectation P v (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * (1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b)) -
      tiltedExpectation P v (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u)) *
        tiltedExpectation P v (fun u => 1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b) =
      1 / 2 * ∑ a, ∑ c, (H * P⁻¹) a c * (B * P⁻¹) c a +
        (H *ᵥ tiltMean P v) ⬝ᵥ P⁻¹ *ᵥ (B *ᵥ tiltMean P v) + (H *ᵥ tiltMean P v) ⬝ᵥ P⁻¹ *ᵥ b := by
  rw [tiltedExpectation_const_mul P v (1 / 2) (fun u => u ⬝ᵥ H *ᵥ u), tiltedExpectation_quadForm hP,
    tiltedExpectation_quadProbe hP v hB b, tiltedExpectation_eq hP v]
  set m := tiltMean P v with hm
  have hZ0 : gaussianZ (matCLM P) ≠ 0 := (gaussianZ_matCLM_pos hP).ne'
  have hZ : ∫ u : ι → ℝ, gaussianWeight (matCLM P) u = gaussianZ (matCLM P) := rfl
  have hlinH : ∀ u : ι → ℝ, (u + m) ⬝ᵥ H *ᵥ (u + m) =
      u ⬝ᵥ H *ᵥ u + 2 * (u ⬝ᵥ (H *ᵥ m)) + m ⬝ᵥ H *ᵥ m := by
    intro u
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_mulVec_symm_of_isHermitian hH m u]
    ring
  have hlinB : ∀ u : ι → ℝ, (u + m) ⬝ᵥ B *ᵥ (u + m) =
      u ⬝ᵥ B *ᵥ u + 2 * (u ⬝ᵥ (B *ᵥ m)) + m ⬝ᵥ B *ᵥ m := by
    intro u
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_mulVec_symm_of_isHermitian hB m u]
    ring
  have hexp : ∀ u : ι → ℝ, (1 / 2 * ((u + m) ⬝ᵥ H *ᵥ (u + m))) * (1 / 2 * ((u + m) ⬝ᵥ B *ᵥ (u + m))
      + (u + m) ⬝ᵥ b) * gaussianWeight (matCLM P) u = ((((1 / 4) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) *
      gaussianWeight (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u)) + ((1 / 4 * (m ⬝ᵥ B *ᵥ m)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u) + (1
      / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u))) + ((((1 / 2 * (m ⬝ᵥ b)) *
      ((u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) *
      gaussianWeight (matCLM P) u)) + ((1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u) + (1 / 2 * (m ⬝ᵥ B *ᵥ m)) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u))) +
      (((1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) * ((u ⬝ᵥ (H *ᵥ
      m)) * gaussianWeight (matCLM P) u)) + (((1 / 4 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ B *ᵥ u) *
      gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u)) + ((1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) * (gaussianWeight (matCLM P) u) +
      ((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m *
      (m ⬝ᵥ b))) * (gaussianWeight (matCLM P) u))))))) := by
    intro u
    rw [hlinH, hlinB, add_dotProduct]
    ring
  simp_rw [hexp]
  have I1 := (integrable_quadForm_mul_quadForm_mul_gaussianWeight_matCLM hP H B).const_mul (1 / 4)
  have I2 := (integrable_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM hP H (B *ᵥ m)).const_mul
      (1 / 2)
  have I3 : Integrable (fun u : ι → ℝ => (1 / 4) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) * gaussianWeight
      (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u)) :=
      I1.add I2
  have I4 := (integrable_quadForm_mul_gaussianWeight_matCLM hP H).const_mul (1 / 4 * (m ⬝ᵥ B *ᵥ m))
  have I5 := (integrable_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM hP H b).const_mul (1 / 2)
  have I6 : Integrable (fun u : ι → ℝ => (1 / 4 * (m ⬝ᵥ B *ᵥ m)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight
      (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u)) := I4.add
      I5
  have I7 : Integrable (fun u : ι → ℝ => ((1 / 4) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) * gaussianWeight
      (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u)) +
      ((1 / 4 * (m ⬝ᵥ B *ᵥ m)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ H
      *ᵥ u) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u))) := I3.add I6
  have I8 := (integrable_quadForm_mul_gaussianWeight_matCLM hP H).const_mul (1 / 2 * (m ⬝ᵥ b))
  have I9 := (integrable_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM hP B (H *ᵥ m)).const_mul
      (1 / 2)
  have I10 : Integrable (fun u : ι → ℝ => (1 / 2 * (m ⬝ᵥ b)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight
      (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u)) :=
      I8.add I9
  have I11 := (integrable_dotProduct_mul_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m) (B *ᵥ
      m)).const_mul (1)
  have I12 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m)).const_mul (1 / 2 * (m
      ⬝ᵥ B *ᵥ m))
  have I13 : Integrable (fun u : ι → ℝ => (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u) + (1 / 2 * (m ⬝ᵥ B *ᵥ m)) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u)) :=
      I11.add I12
  have I14 : Integrable (fun u : ι → ℝ => ((1 / 2 * (m ⬝ᵥ b)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight
      (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u)) +
      ((1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ B *ᵥ
      m)) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u))) := I10.add I13
  have I15 := (integrable_dotProduct_mul_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m)
      b).const_mul (1)
  have I16 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m)).const_mul (m ⬝ᵥ b)
  have I17 : Integrable (fun u : ι → ℝ => (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b) * gaussianWeight (matCLM
      P) u) + (m ⬝ᵥ b) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u)) := I15.add I16
  have I18 := (integrable_quadForm_mul_gaussianWeight_matCLM hP B).const_mul (1 / 4 * (m ⬝ᵥ H *ᵥ m))
  have I19 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (B *ᵥ m)).const_mul (1 / 2 * (m
      ⬝ᵥ H *ᵥ m))
  have I20 : Integrable (fun u : ι → ℝ => (1 / 4 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ B *ᵥ u) * gaussianWeight
      (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u)) :=
      I18.add I19
  have I21 := (integrable_gaussianWeight_matCLM hP).const_mul (1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ
      m)))
  have I22 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP b).const_mul (1 / 2 * (m ⬝ᵥ H *ᵥ
      m))
  have I23 := (integrable_gaussianWeight_matCLM hP).const_mul (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b)))
  have I24 : Integrable (fun u : ι → ℝ => (1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ b) * gaussianWeight
      (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b))) * (gaussianWeight (matCLM P) u)) := I22.add
      I23
  have I25 : Integrable (fun u : ι → ℝ => (1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) * (gaussianWeight
      (matCLM P) u) + ((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (1 / 2 *
      (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b))) * (gaussianWeight (matCLM P) u))) := I21.add I24
  have I26 : Integrable (fun u : ι → ℝ => ((1 / 4 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ B *ᵥ u) * gaussianWeight
      (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u)) +
      ((1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) * (gaussianWeight (matCLM P) u) + ((1 / 2 * (m ⬝ᵥ H
      *ᵥ m)) * ((u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b))) *
      (gaussianWeight (matCLM P) u)))) := I20.add I25
  have I27 : Integrable (fun u : ι → ℝ => ((1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b) * gaussianWeight
      (matCLM P) u) + (m ⬝ᵥ b) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u)) + (((1 / 4 * (m ⬝ᵥ
      H *ᵥ m)) * ((u ⬝ᵥ B *ᵥ u) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ (B
      *ᵥ m)) * gaussianWeight (matCLM P) u)) + ((1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) *
      (gaussianWeight (matCLM P) u) + ((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ b) * gaussianWeight (matCLM
      P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b))) * (gaussianWeight (matCLM P) u))))) := I17.add I26
  have I28 : Integrable (fun u : ι → ℝ => (((1 / 2 * (m ⬝ᵥ b)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight
      (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u)) +
      ((1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ B *ᵥ
      m)) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u))) + (((1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b)
      * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u)) +
      (((1 / 4 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ B *ᵥ u) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H
      *ᵥ m)) * ((u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u)) + ((1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B
      *ᵥ m))) * (gaussianWeight (matCLM P) u) + ((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ b) *
      gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b))) * (gaussianWeight (matCLM P)
      u)))))) := I14.add I27
  have I29 : Integrable (fun u : ι → ℝ => (((1 / 4) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) *
      gaussianWeight (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u)) + ((1 / 4 * (m ⬝ᵥ B *ᵥ m)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u) + (1
      / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u))) + ((((1 / 2 * (m ⬝ᵥ b)) *
      ((u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u) + (1 / 2) * ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) *
      gaussianWeight (matCLM P) u)) + ((1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u) + (1 / 2 * (m ⬝ᵥ B *ᵥ m)) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u))) +
      (((1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) * ((u ⬝ᵥ (H *ᵥ
      m)) * gaussianWeight (matCLM P) u)) + (((1 / 4 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ B *ᵥ u) *
      gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u)) + ((1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) * (gaussianWeight (matCLM P) u) +
      ((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m *
      (m ⬝ᵥ b))) * (gaussianWeight (matCLM P) u))))))) := I7.add I28
  rw [integral_add I7 I28, integral_add I3 I6, integral_add I1 I2, integral_add I4 I5, integral_add
    I14 I27, integral_add I10 I13, integral_add I8 I9, integral_add I11 I12, integral_add I17 I26,
    integral_add I15 I16, integral_add I20 I25, integral_add I18 I19, integral_add I21 I24,
    integral_add I22 I23]
  simp only [integral_const_mul]
  rw [integral_quadForm_mul_quadForm_mul_gaussianWeight_matCLM hP H hB,
    integral_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM P H (B *ᵥ m),
    integral_quadForm_mul_gaussianWeight_matCLM hP H,
    integral_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM P H b,
    integral_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM P B (H *ᵥ m),
    integral_dotProduct_mul_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m) (B *ᵥ m),
    integral_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m),
    integral_dotProduct_mul_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m) b,
    integral_quadForm_mul_gaussianWeight_matCLM hP B, integral_dotProduct_mul_gaussianWeight_matCLM
    hP (B *ᵥ m), hZ, integral_dotProduct_mul_gaussianWeight_matCLM hP b]
  field_simp
  ring

/-- **The tilted Gaussian covariance of two quadratic forms**:
`Cov_{P,v}(uᵀHu, uᵀBu) = 2·tr(HΣBΣ) + 4·(Hm)ᵀΣ(Bm)`. -/
theorem tiltedCov_quadForm {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) {H B : Matrix ι ι ℝ}
    (hH : H.IsHermitian) (hB : B.IsHermitian) :
    tiltedExpectation P v (fun u => (u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u)) -
      tiltedExpectation P v (fun u => u ⬝ᵥ H *ᵥ u) * tiltedExpectation P v (fun u => u ⬝ᵥ B *ᵥ u) =
      2 * ∑ a, ∑ c, (H * P⁻¹) a c * (B * P⁻¹) c a +
        4 * ((H *ᵥ tiltMean P v) ⬝ᵥ P⁻¹ *ᵥ (B *ᵥ tiltMean P v)) := by
  have h := tiltedCov_quadForm_quadProbe hP v hH hB 0
  have e1 : (fun u : ι → ℝ => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * (1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ 0)) =
      fun u => 1 / 4 * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u)) := by
    funext u
    rw [dotProduct_zero]
    ring
  have e2 : (fun u : ι → ℝ => 1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ 0) = fun u => 1 / 2 * (u ⬝ᵥ B *ᵥ u) := by
    funext u
    rw [dotProduct_zero, add_zero]
  rw [e1, e2, tiltedExpectation_const_mul, tiltedExpectation_const_mul, tiltedExpectation_const_mul,
    Matrix.mulVec_zero, dotProduct_zero, add_zero] at h
  linear_combination 4 * h

/-- **E3's anchored Gaussian covariance of the scaled energy with a quadratic-plus-linear probe**,
in
any orthogonal frame diagonalising `H` (`UᵀU = 1`, `UᵀHU = diag(λ)`): with `B̃ = UᵀBU`, `b̃ = Uᵀb`,
`aᵢ = (Uᵀv)ᵢ`, `pᵢ = tλᵢ + g`,
`t²Cov_{tH+gI,v}(½uᵀHu, ½uᵀBu + b·u) = ½t²∑ᵢλᵢB̃ᵢᵢ/pᵢ² + t²∑ᵢⱼλᵢaᵢB̃ᵢⱼaⱼ/(pᵢ²pⱼ) +
t²∑ᵢb̃ᵢλᵢaᵢ/pᵢ²`. -/
theorem anchoredGaussianCov_eq {U H : Matrix ι ι ℝ} {lam : ι → ℝ} (hU : Uᵀ * U = 1)
    (hdiag : Uᵀ * H * U = diagonal lam) (hlam : ∀ i, 0 < lam i) {t g : ℝ} (ht : 0 < t) (hg : 0 ≤ g)
    (v : ι → ℝ) {B : Matrix ι ι ℝ} (hB : B.IsHermitian) (b : ι → ℝ) :
    t ^ 2 * (tiltedExpectation (t • H + g • (1 : Matrix ι ι ℝ)) v
        (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * (1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b)) -
      tiltedExpectation (t • H + g • (1 : Matrix ι ι ℝ)) v (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u)) *
        tiltedExpectation (t • H + g • (1 : Matrix ι ι ℝ)) v
          (fun u => 1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b)) =
      1 / 2 * t ^ 2 * ∑ i, lam i * (Uᵀ * B * U) i i / (t * lam i + g) ^ 2 +
        t ^ 2 * ∑ i, ∑ j, lam i * (Uᵀ *ᵥ v) i * (Uᵀ * B * U) i j * (Uᵀ *ᵥ v) j /
          ((t * lam i + g) ^ 2 * (t * lam j + g)) +
        t ^ 2 * ∑ i, (Uᵀ *ᵥ b) i * lam i * (Uᵀ *ᵥ v) i / (t * lam i + g) ^ 2 := by
  have hP := posDef_localisedPrecision_frame hU hdiag hlam ht hg
  have hH : H.IsHermitian := (posDef_frame hU hdiag hlam).1
  rw [tiltedCov_quadForm_quadProbe hP v hH hB b, trace_frame_mixed hU hdiag hlam ht hg B,
    cross_frame hU hdiag hlam ht hg v B, linear_frame hU hdiag hlam ht hg v b]
  have e1 : ∑ i, lam i / (t * lam i + g) * (Uᵀ * B * U) i i * (1 / (t * lam i + g)) =
      ∑ i, lam i * (Uᵀ * B * U) i i / (t * lam i + g) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by
      simp only [div_eq_mul_inv, ← inv_pow]
      ring
  have e2 : ∑ i, ∑ j, lam i / (t * lam i + g) * (Uᵀ *ᵥ v) i * (1 / (t * lam i + g)) *
      ((Uᵀ * B * U) i j * (1 / (t * lam j + g) * (Uᵀ *ᵥ v) j)) =
      ∑ i, ∑ j, lam i * (Uᵀ *ᵥ v) i * (Uᵀ * B * U) i j * (Uᵀ *ᵥ v) j /
        ((t * lam i + g) ^ 2 * (t * lam j + g)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [div_eq_mul_inv, mul_inv, ← inv_pow]
      ring
  have e3 : ∑ i, lam i / (t * lam i + g) * (Uᵀ *ᵥ v) i * (1 / (t * lam i + g) * (Uᵀ *ᵥ b) i) =
      ∑ i, (Uᵀ *ᵥ b) i * lam i * (Uᵀ *ᵥ v) i / (t * lam i + g) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by
      simp only [div_eq_mul_inv, ← inv_pow]
      ring
  rw [e1, e2, e3]
  ring

end Laplace.Sampler


namespace Laplace.Multi

/-! ### The anchored covariance's finite-temperature correction (E2 frame data) -/

/-- `|(u/(u+g))² − 1| ≤ 2g/u`. -/
theorem sq_ratio_sub_one_bound {u g : ℝ} (hu : 0 < u) (hg : 0 ≤ g) :
    |(u / (u + g)) ^ 2 - 1| ≤ 2 * g / u := by
  have hug : 0 < u + g := by positivity
  have e : (u / (u + g)) ^ 2 - 1 = -(g * (2 * u + g) / (u + g) ^ 2) := by
    field_simp
    ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  have e2 : 2 * g / u - g * (2 * u + g) / (u + g) ^ 2 =
      g * (3 * u * g + 2 * g ^ 2) / (u * (u + g) ^ 2) := by
    field_simp
    ring
  have : 0 ≤ g * (3 * u * g + 2 * g ^ 2) / (u * (u + g) ^ 2) := by positivity
  linarith

/-- The diagonal (trace) term: `|½t²λ/p² − 1/(2λ) + g/(λ²t)| ≤ 3g²/(2λ³t²)`. -/
theorem central_cov_term_bound {t lam g : ℝ} (ht : 0 < t) (hl : 0 < lam) (hg : 0 ≤ g) :
    |1 / 2 * t ^ 2 * lam / (t * lam + g) ^ 2 - 1 / (2 * lam) + g / (lam ^ 2 * t)| ≤
      3 / 2 * g ^ 2 / lam ^ 3 / t ^ 2 := by
  have hu : 0 < t * lam := by positivity
  have hp : 0 < t * lam + g := by positivity
  have e : 1 / 2 * t ^ 2 * lam / (t * lam + g) ^ 2 - 1 / (2 * lam) + g / (lam ^ 2 * t) =
      1 / lam * (1 / 2 * (t * lam / (t * lam + g)) ^ 2 - 1 / 2 + g / (t * lam)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / lam)]
  calc 1 / lam * |1 / 2 * (t * lam / (t * lam + g)) ^ 2 - 1 / 2 + g / (t * lam)|
      ≤ 1 / lam * (3 / 2 * g ^ 2 / (t * lam) ^ 2) :=
        mul_le_mul_of_nonneg_left (central_var_term_bound hu hg) (by positivity)
    _ = 3 / 2 * g ^ 2 / lam ^ 3 / t ^ 2 := by
        field_simp

/-- The linear term: `|t²λ/p² − 1/λ + 2g/(λ²t)| ≤ 3g²/(λ³t²)`. -/
theorem linear_cov_term_bound {t lam g : ℝ} (ht : 0 < t) (hl : 0 < lam) (hg : 0 ≤ g) :
    |t ^ 2 * lam / (t * lam + g) ^ 2 - 1 / lam + 2 * g / (lam ^ 2 * t)| ≤ 3 * g ^ 2 / lam ^ 3 / t ^
        2 := by
  have hu : 0 < t * lam := by positivity
  have hp : 0 < t * lam + g := by positivity
  have e : t ^ 2 * lam / (t * lam + g) ^ 2 - 1 / lam + 2 * g / (lam ^ 2 * t) =
      2 / lam * (1 / 2 * (t * lam / (t * lam + g)) ^ 2 - 1 / 2 + g / (t * lam)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / lam)]
  calc 2 / lam * |1 / 2 * (t * lam / (t * lam + g)) ^ 2 - 1 / 2 + g / (t * lam)|
      ≤ 2 / lam * (3 / 2 * g ^ 2 / (t * lam) ^ 2) :=
        mul_le_mul_of_nonneg_left (central_var_term_bound hu hg) (by positivity)
    _ = 3 * g ^ 2 / lam ^ 3 / t ^ 2 := by
        field_simp

/-- The cross term: `|t²λ/(p²q) − 1/(λμt)| ≤ (2g/(λ²μ) + g/(λμ²))/t²`, `p = tλ+g`, `q = tμ+g`. -/
theorem cross_cov_term_bound {t lam mu g : ℝ} (ht : 0 < t) (hl : 0 < lam) (hm : 0 < mu)
    (hg : 0 ≤ g) :
    |t ^ 2 * lam / ((t * lam + g) ^ 2 * (t * mu + g)) - 1 / (lam * mu * t)| ≤
      (2 * g / (lam ^ 2 * mu) + g / (lam * mu ^ 2)) / t ^ 2 := by
  have hp : 0 < t * lam + g := by positivity
  have hq : 0 < t * mu + g := by positivity
  have hu : 0 < t * lam := by positivity
  have hw : 0 < t * mu := by positivity
  have e : t ^ 2 * lam / ((t * lam + g) ^ 2 * (t * mu + g)) - 1 / (lam * mu * t) =
      1 / lam * ((t * lam / (t * lam + g)) ^ 2 - 1) * (1 / (t * mu + g)) +
        1 / lam * (1 / (t * mu + g) - 1 / (t * mu)) := by
    field_simp
    ring
  rw [e]
  have h1 := sq_ratio_sub_one_bound hu hg
  have h2 := inv_shift_rate hw hg
  have hq' : 1 / (t * mu + g) ≤ 1 / (t * mu) := one_div_le_one_div_of_le hw (by linarith)
  calc _ ≤ |1 / lam * ((t * lam / (t * lam + g)) ^ 2 - 1) * (1 / (t * mu + g))| +
        |1 / lam * (1 / (t * mu + g) - 1 / (t * mu))| := abs_add_le _ _
    _ = 1 / lam * |(t * lam / (t * lam + g)) ^ 2 - 1| * (1 / (t * mu + g)) +
        1 / lam * |1 / (t * mu + g) - 1 / (t * mu)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / lam),
          abs_of_pos (by positivity : (0 : ℝ) < 1 / (t * mu + g))]
    _ ≤ 1 / lam * (2 * g / (t * lam)) * (1 / (t * mu)) + 1 / lam * (g / (t * mu) ^ 2) :=
        add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hq' (by positivity)
          (by positivity)) (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = (2 * g / (lam ^ 2 * mu) + g / (lam * mu ^ 2)) / t ^ 2 := by
        field_simp

/-- **The anchored covariance's correction** (frame data `B̃`, `b̃`, `a`): for every `t > 0`,
`𝒞_t = ∑ᵢ(B̃ᵢᵢ/(2λᵢ) + b̃ᵢaᵢ/λᵢ) + (−g∑ᵢB̃ᵢᵢ/λᵢ² + ∑ᵢⱼB̃ᵢⱼaᵢaⱼ/(λᵢλⱼ) − 2g∑ᵢb̃ᵢaᵢ/λᵢ²)/t + O(t⁻²)`
with an explicit constant. -/
theorem anchoredGaussianCov_rate2 {d : ℕ} {lam : Fin d → ℝ} {g : ℝ} (hlam : ∀ i, 0 < lam i)
    (hg : 0 ≤ g) (Bt : Fin d → Fin d → ℝ) (bt a : Fin d → ℝ) {t : ℝ} (ht : 0 < t) :
      |(1 / 2 * t ^ 2 * ∑ i, lam i * Bt i i / (t * lam i + g) ^ 2 + t ^ 2 * ∑ i, ∑ j, lam i * a i *
        Bt i j * a j / ((t * lam i + g) ^ 2 * (t * lam j + g)) + t ^ 2 * ∑ i, bt i * lam i * a i /
        (t * lam i + g) ^ 2) - ∑ i, (Bt i i / (2 * lam i) + bt i * a i / lam i) - (-g * ∑ i, Bt i i
        / lam i ^ 2 + ∑ i, ∑ j, Bt i j * a i * a j / (lam i * lam j) - 2 * g * ∑ i, bt i * a i / lam
        i ^ 2) / t| ≤ (∑ i, |Bt i i| * (3 / 2 * g ^ 2 / lam i ^ 3) + ∑ i, ∑ j, |Bt i j * a i * a j|
        * (2 * g / (lam i ^ 2 * lam j) + g / (lam i * lam j ^ 2)) + ∑ i, |bt i * a i| * (3 * g ^ 2 /
        lam i ^ 3)) / t ^ 2 := by
  have hT1 : ∑ i, (1 / 2 * t ^ 2 * (lam i * Bt i i / (t * lam i + g) ^ 2) - Bt i i / (2 * lam i) + g
      * (Bt i i / lam i ^ 2) / t) = 1 / 2 * t ^ 2 * ∑ i, lam i * Bt i i / (t * lam i + g) ^ 2 - ∑ i,
      Bt i i / (2 * lam i) + g * (∑ i, Bt i i / lam i ^ 2) / t := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  have hT2 : ∑ i, ∑ j, (t ^ 2 * (lam i * a i * Bt i j * a j / ((t * lam i + g) ^ 2 * (t * lam j +
      g))) - Bt i j * a i * a j / (lam i * lam j) / t) = t ^ 2 * ∑ i, ∑ j, lam i * a i * Bt i j * a
      j / ((t * lam i + g) ^ 2 * (t * lam j + g)) - (∑ i, ∑ j, Bt i j * a i * a j / (lam i * lam j))
      / t := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  have hT3 : ∑ i, (t ^ 2 * (bt i * lam i * a i / (t * lam i + g) ^ 2) - bt i * a i / lam i + 2 * g *
      (bt i * a i / lam i ^ 2) / t) = t ^ 2 * ∑ i, bt i * lam i * a i / (t * lam i + g) ^ 2 - ∑ i,
      bt i * a i / lam i + 2 * g * (∑ i, bt i * a i / lam i ^ 2) / t := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  have hlead : ∑ i, (Bt i i / (2 * lam i) + bt i * a i / lam i) =
      ∑ i, Bt i i / (2 * lam i) + ∑ i, bt i * a i / lam i := Finset.sum_add_distrib
  have e : (1 / 2 * t ^ 2 * ∑ i, lam i * Bt i i / (t * lam i + g) ^ 2 + t ^ 2 * ∑ i, ∑ j, lam i * a
      i * Bt i j * a j / ((t * lam i + g) ^ 2 * (t * lam j + g)) + t ^ 2 * ∑ i, bt i * lam i * a i /
      (t * lam i + g) ^ 2) - ∑ i, (Bt i i / (2 * lam i) + bt i * a i / lam i) - (-g * ∑ i, Bt i i /
      lam i ^ 2 + ∑ i, ∑ j, Bt i j * a i * a j / (lam i * lam j) - 2 * g * ∑ i, bt i * a i / lam i ^
      2) / t = ∑ i, (1 / 2 * t ^ 2 * (lam i * Bt i i / (t * lam i + g) ^ 2) - Bt i i / (2 * lam i) +
      g * (Bt i i / lam i ^ 2) / t) + (∑ i, ∑ j, (t ^ 2 * (lam i * a i * Bt i j * a j / ((t * lam i
      + g) ^ 2 * (t * lam j + g))) - Bt i j * a i * a j / (lam i * lam j) / t) + ∑ i, (t ^ 2 * (bt i
      * lam i * a i / (t * lam i + g) ^ 2) - bt i * a i / lam i + 2 * g * (bt i * a i / lam i ^ 2) /
      t)) := by
    rw [hT1, hT2, hT3, hlead]
    ring
  have hb1 : ∀ i, |1 / 2 * t ^ 2 * (lam i * Bt i i / (t * lam i + g) ^ 2) - Bt i i / (2 * lam i) +
      g * (Bt i i / lam i ^ 2) / t| ≤ |Bt i i| * (3 / 2 * g ^ 2 / lam i ^ 3 / t ^ 2) := fun i => by
    have hl := hlam i
    have key : 1 / 2 * t ^ 2 * (lam i * Bt i i / (t * lam i + g) ^ 2) - Bt i i / (2 * lam i) + g *
        (Bt i i / lam i ^ 2) / t =
        Bt i i * (1 / 2 * t ^ 2 * lam i / (t * lam i + g) ^ 2 - 1 / (2 * lam i) + g / (lam i ^ 2 *
            t)) := by
      ring
    rw [key, abs_mul]
    exact mul_le_mul_of_nonneg_left (central_cov_term_bound ht hl hg) (abs_nonneg _)
  have hb2 : ∀ i j, |t ^ 2 * (lam i * a i * Bt i j * a j / ((t * lam i + g) ^ 2 * (t * lam j + g)))
      - Bt i j * a i * a j / (lam i * lam j) / t| ≤
      |Bt i j * a i * a j| * ((2 * g / (lam i ^ 2 * lam j) + g / (lam i * lam j ^ 2)) / t ^ 2) :=
          fun i j => by
    have hl := hlam i
    have hm := hlam j
    have key : t ^ 2 * (lam i * a i * Bt i j * a j / ((t * lam i + g) ^ 2 * (t * lam j + g))) - Bt
        i j * a i * a j / (lam i * lam j) / t =
        Bt i j * a i * a j * (t ^ 2 * lam i / ((t * lam i + g) ^ 2 * (t * lam j + g)) - 1 / (lam i
            * lam j * t)) := by
      ring
    rw [key, abs_mul]
    exact mul_le_mul_of_nonneg_left (cross_cov_term_bound ht hl hm hg) (abs_nonneg _)
  have hb3 : ∀ i, |t ^ 2 * (bt i * lam i * a i / (t * lam i + g) ^ 2) - bt i * a i / lam i + 2 * g
      * (bt i * a i / lam i ^ 2) / t| ≤ |bt i * a i| * (3 * g ^ 2 / lam i ^ 3 / t ^ 2) := fun i =>
          by
    have hl := hlam i
    have key : t ^ 2 * (bt i * lam i * a i / (t * lam i + g) ^ 2) - bt i * a i / lam i + 2 * g *
        (bt i * a i / lam i ^ 2) / t =
        bt i * a i * (t ^ 2 * lam i / (t * lam i + g) ^ 2 - 1 / lam i + 2 * g / (lam i ^ 2 * t)) :=
            by
      ring
    rw [key, abs_mul]
    exact mul_le_mul_of_nonneg_left (linear_cov_term_bound ht hl hg) (abs_nonneg _)
  rw [e]
  calc _ ≤ |∑ i, (1 / 2 * t ^ 2 * (lam i * Bt i i / (t * lam i + g) ^ 2) - Bt i i / (2 * lam i) + g
      * (Bt i i / lam i ^ 2) / t)| + |∑ i, ∑ j, (t ^ 2 * (lam i * a i * Bt i j * a j / ((t * lam i
          + g) ^ 2 * (t * lam j + g))) - Bt i j * a i * a j / (lam i * lam j) / t) + ∑ i, (t ^ 2 *
              (bt i * lam i * a i / (t * lam i + g) ^ 2) - bt i * a i / lam i + 2 * g * (bt i * a i
                  / lam i ^ 2) / t)| :=
        abs_add_le _ _
    _ ≤ |∑ i, (1 / 2 * t ^ 2 * (lam i * Bt i i / (t * lam i + g) ^ 2) - Bt i i / (2 * lam i) + g *
        (Bt i i / lam i ^ 2) / t)| + (|∑ i, ∑ j, (t ^ 2 * (lam i * a i * Bt i j * a j / ((t * lam i
            + g) ^ 2 * (t * lam j + g))) - Bt i j * a i * a j / (lam i * lam j) / t)| + |∑ i, (t ^
                2 * (bt i * lam i * a i / (t * lam i + g) ^ 2) - bt i * a i / lam i + 2 * g * (bt i
                    * a i / lam i ^ 2) / t)|) :=
        add_le_add le_rfl (abs_add_le _ _)
    _ ≤ ∑ i, |Bt i i| * (3 / 2 * g ^ 2 / lam i ^ 3 / t ^ 2) +
        (∑ i, ∑ j, |Bt i j * a i * a j| * ((2 * g / (lam i ^ 2 * lam j) + g / (lam i * lam j ^ 2))
            / t ^ 2) +
          ∑ i, |bt i * a i| * (3 * g ^ 2 / lam i ^ 3 / t ^ 2)) := by
        refine add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hb1
            i))
          (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hb2 i j)))
            ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hb3 i)))
    _ = _ := by
        simp only [add_div, Finset.sum_div, mul_div_assoc]
        ring


/-! ### The gap coefficients -/

/-- The diagonal susceptibility-gap coefficient `Γᵢᵢ = c₂′ + g/λ² − a²/λ² = 5α²/(4λ⁴) − 2aα/λ³ −
γ/(2λ³)`,
`a = g x₀`. -/
noncomputable def locCovGapDiag (lam alpha gamma g x₀ : ℝ) : ℝ :=
  5 * alpha ^ 2 / (4 * lam ^ 4) - 2 * (g * x₀) * alpha / lam ^ 3 - gamma / (2 * lam ^ 3)

theorem locSecondCoeff2_gap_eq {lam alpha gamma g x₀ : ℝ} (hlam : 0 < lam) :
    locSecondCoeff2 lam alpha gamma g x₀ + g / lam ^ 2 - (g * x₀) ^ 2 / lam ^ 2 =
      locCovGapDiag lam alpha gamma g x₀ := by
  have h := varLocCoeff2_eq (lam := lam) (alpha := alpha) (gamma := gamma) (g := g) (x₀ := x₀) hlam
  unfold varLocCoeff2 at h
  unfold locCovGapDiag
  linear_combination h

theorem meanLocCoeff2_gap_eq {lam alpha gamma g x₀ : ℝ} (hlam : 0 < lam) :
    meanLocCoeff2 lam alpha gamma g x₀ + g * (g * x₀) / lam ^ 2 =
      meanCoeff2 lam alpha gamma + g * x₀ * alpha ^ 2 / lam ^ 4 - g * x₀ * gamma / (2 * lam ^ 3) +
        alpha * g / lam ^ 3 - alpha * (g * x₀) ^ 2 / (2 * lam ^ 3) := by
  rw [meanLocCoeff2_eq hlam]
  ring

/-- **The susceptibility-gap coefficient** `Γ_B = ∑ᵢB̃ᵢᵢΓᵢᵢ + ∑_{i≠j}B̃ᵢⱼ(cᵢcⱼ − aᵢaⱼ/(λᵢλⱼ)) +
2∑ᵢb̃ᵢ(m₂ᵢ + gaᵢ/λᵢ²)`,
`aᵢ = g u₀ᵢ`: the `1/t` coefficient of `t²Cov_loc − t²Cov_anch`. -/
noncomputable def locCovGapCoeff {d : ℕ} (lam alpha gamma : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ)
    (Bt : Fin d → Fin d → ℝ) (bt : Fin d → ℝ) : ℝ :=
  ∑ i, Bt i i * locCovGapDiag (lam i) (alpha i) (gamma i) g (u₀ i) +
    ∑ p : Fin d × Fin d, (if p.1 = p.2 then 0 else
      Bt p.1 p.2 * (locLeadMean lam alpha g u₀ p.1 * locLeadMean lam alpha g u₀ p.2 -
        g * u₀ p.1 * (g * u₀ p.2) / (lam p.1 * lam p.2))) +
    2 * ∑ i, bt i * (meanLocCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i) + g * (g * u₀ i) / lam i ^
        2)

theorem sum_sum_split_diag {d : ℕ} (F : Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, F i j = ∑ i, F i i + ∑ p : Fin d × Fin d, (if p.1 = p.2 then 0 else F p.1 p.2) := by
  have h1 : ∑ i, ∑ j, F i j = ∑ p : Fin d × Fin d, F p.1 p.2 := (Fintype.sum_prod_type' F).symm
  have h2 : ∑ p : Fin d × Fin d, F p.1 p.2 =
      ∑ p : Fin d × Fin d, ((if p.1 = p.2 then F p.1 p.2 else 0) + (if p.1 = p.2 then 0 else F p.1
          p.2)) :=
    Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
  have h3 : ∑ p : Fin d × Fin d, (if p.1 = p.2 then F p.1 p.2 else 0) = ∑ i, F i i := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [h1, h2, Finset.sum_add_distrib, h3]

/-- `C′_loc − C′_anch = Γ_B`: the E2 second-order covariance coefficient minus the anchored
Gaussian one. -/
theorem locCovGapCoeff_eq {d : ℕ} {lam alpha gamma : Fin d → ℝ} {g : ℝ} (hlam : ∀ i, 0 < lam i)
    (u₀ : Fin d → ℝ) (Bt : Fin d → Fin d → ℝ) (bt : Fin d → ℝ) :
    locCovKCoeff2Sep lam alpha gamma g u₀ Bt bt -
      (-g * ∑ i, Bt i i / lam i ^ 2 + ∑ i, ∑ j, Bt i j * (g * u₀ i) * (g * u₀ j) / (lam i * lam j) -
        2 * g * ∑ i, bt i * (g * u₀ i) / lam i ^ 2) =
      locCovGapCoeff lam alpha gamma g u₀ Bt bt := by
  rw [locCovKCoeff2Sep_eq, sum_sum_split_diag (fun i j => Bt i j * (g * u₀ i) * (g * u₀ j) / (lam i
      * lam j))]
  unfold locCovGapCoeff
  have hdiag : ∑ i, Bt i i * locCovGapDiag (lam i) (alpha i) (gamma i) g (u₀ i) =
      ∑ i, Bt i i * (locSecondCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i) + g / lam i ^ 2 -
        (g * u₀ i) ^ 2 / lam i ^ 2) :=
    Finset.sum_congr rfl fun i _ => by rw [locSecondCoeff2_gap_eq (hlam i)]
  have hoff : ∑ p : Fin d × Fin d, (if p.1 = p.2 then 0 else
      Bt p.1 p.2 * (locLeadMean lam alpha g u₀ p.1 * locLeadMean lam alpha g u₀ p.2 -
        g * u₀ p.1 * (g * u₀ p.2) / (lam p.1 * lam p.2))) =
      ∑ p : Fin d × Fin d, (if p.1 = p.2 then 0 else
        Bt p.1 p.2 * (locLeadMean lam alpha g u₀ p.1 * locLeadMean lam alpha g u₀ p.2)) -
      ∑ p : Fin d × Fin d, (if p.1 = p.2 then 0 else Bt p.1 p.2 * (g * u₀ p.1) * (g * u₀ p.2) /
        (lam p.1 * lam p.2)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs
    · ring
    · ring
  have hsingle : ∑ i, (Bt i i * locSecondCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i) +
        2 * bt i * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i)) +
      g * ∑ i, Bt i i / lam i ^ 2 - ∑ i, Bt i i * (g * u₀ i) * (g * u₀ i) / (lam i * lam i) +
      2 * g * ∑ i, bt i * (g * u₀ i) / lam i ^ 2 =
      ∑ i, Bt i i * (locSecondCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i) + g / lam i ^ 2 -
        (g * u₀ i) ^ 2 / lam i ^ 2) +
      2 * ∑ i, bt i * (meanLocCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i) + g * (g * u₀ i) / lam i
          ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdiag, hoff]
  linear_combination hsingle

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The anchored susceptibility gap for quadratic-plus-linear probes**: with `H = Q diag(λ) Qᵀ`,
`ψ(w) = ½(w−c)ᵀB(w−c) + b·(w−c)`, and E3's anchored Gaussian `N((tH+gI)⁻¹g(w₀−c), (tH+gI)⁻¹)`,
`t²Cov_loc(L∘A, ψ) − t²Cov_anch(½uᵀHu, ½uᵀBu + b·u) = −∑ᵢb̃ᵢαᵢ/(2λᵢ²) + Γ_B/t + O(t⁻²)`,
`B̃ = QᵀBQ`, `b̃ = Qᵀb`. -/
theorem localisedCov_anchoredGap (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.IsHermitian) (b : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotatedAnharmonic
        Q c lam alpha gamma) (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) - t ^ 2 *
        (tiltedExpectation (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (g •
        (w₀ - c)) (fun u => (1 / 2 * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u)) * (1 / 2 * (u ⬝ᵥ B *ᵥ u) +
        u ⬝ᵥ b)) - tiltedExpectation (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
        ℝ)) (g • (w₀ - c)) (fun u => 1 / 2 * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u)) *
        tiltedExpectation (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (g •
        (w₀ - c)) (fun u => 1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b)) - (-∑ i, (Qᵀ *ᵥ b) i * alpha i / (2 *
        lam i ^ 2)) - locCovGapCoeff lam alpha gamma g (affineFrame Q c w₀) (fun i j => (Qᵀ * B * Q)
        i j) (Qᵀ *ᵥ b) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ :=
    localisedRotatedAnharmonic_covK_order2_rate (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc)
        hQ c w₀
      hg B b
  have hdiagQ : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  have ha : Qᵀ *ᵥ (g • (w₀ - c)) = fun i => g * affineFrame Q c w₀ i := by
    funext i
    simp [Matrix.mulVec_smul, affineFrame]
  refine ⟨K₁ + (∑ i, |(Qᵀ * B * Q) i i| * (3 / 2 * g ^ 2 / lam i ^ 3) + ∑ i, ∑ j, |(Qᵀ * B * Q) i j
    * (g * affineFrame Q c w₀ i) * (g * affineFrame Q c w₀ j)| * (2 * g / (lam i ^ 2 * lam j) + g /
    (lam i * lam j ^ 2)) + ∑ i, |(Qᵀ *ᵥ b) i * (g * affineFrame Q c w₀ i)| * (3 * g ^ 2 / lam i ^
    3)), T₁, ?_, hT₁, fun {t} ht => ?_⟩
  · have : 0 ≤ ∑ i, |(Qᵀ * B * Q) i i| * (3 / 2 * g ^ 2 / lam i ^ 3) + ∑ i, ∑ j, |(Qᵀ * B * Q) i j *
        (g * affineFrame Q c w₀ i) * (g * affineFrame Q c w₀ j)| * (2 * g / (lam i ^ 2 * lam j) + g
        / (lam i * lam j ^ 2)) + ∑ i, |(Qᵀ *ᵥ b) i * (g * affineFrame Q c w₀ i)| * (3 * g ^ 2 / lam
        i ^ 3) := by
      refine add_nonneg (add_nonneg (Finset.sum_nonneg fun i _ => ?_) (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => ?_)) (Finset.sum_nonneg fun i _ => ?_)
      · have := hlam i
        positivity
      · have := hlam i
        have := hlam j
        positivity
      · have := hlam i
        positivity
    linarith
  have ht0 : 0 < t := by linarith
  have e₁ := h₁ ht
  rw [Laplace.Sampler.anchoredGaussianCov_eq hQ hdiagQ hlam ht0 hg (g • (w₀ - c)) hB b]
  simp only [ha]
  have e₂ := anchoredGaussianCov_rate2 hlam hg (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b) (fun i => g *
    affineFrame Q c w₀ i) ht0
  have hΓ := locCovGapCoeff_eq (alpha := alpha) (gamma := gamma) (g := g) hlam (affineFrame Q c w₀)
    (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b)
  have hlead : ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) + (Qᵀ *ᵥ b) i * locLeadMean lam alpha g
      (affineFrame Q c w₀) i) - ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) + (Qᵀ *ᵥ b) i * (g *
      affineFrame Q c w₀ i) / lam i) = -∑ i, (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold locLeadMean
    ring
  have e : t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ
      (w - c)) - (1 / 2 * t ^ 2 * ∑ i, lam i * (Qᵀ * B * Q) i i / (t * lam i + g) ^ 2 + t ^ 2 * ∑ i,
      ∑ j, lam i * (g * affineFrame Q c w₀ i) * (Qᵀ * B * Q) i j * (g * affineFrame Q c w₀ j) / ((t
      * lam i + g) ^ 2 * (t * lam j + g)) + t ^ 2 * ∑ i, (Qᵀ *ᵥ b) i * lam i * (g * affineFrame Q c
      w₀ i) / (t * lam i + g) ^ 2) - (-∑ i, (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2)) -
      locCovGapCoeff lam alpha gamma g (affineFrame Q c w₀) (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b)
      / t = (t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ
      (w - c)) - ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) + (Qᵀ *ᵥ b) i * locLeadMean lam alpha g
      (affineFrame Q c w₀) i) - locCovKCoeff2Sep lam alpha gamma g (affineFrame Q c w₀) (fun i j =>
      (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b) / t) - ((1 / 2 * t ^ 2 * ∑ i, lam i * (Qᵀ * B * Q) i i / (t * lam
      i + g) ^ 2 + t ^ 2 * ∑ i, ∑ j, lam i * (g * affineFrame Q c w₀ i) * (Qᵀ * B * Q) i j * (g *
      affineFrame Q c w₀ j) / ((t * lam i + g) ^ 2 * (t * lam j + g)) + t ^ 2 * ∑ i, (Qᵀ *ᵥ b) i *
      lam i * (g * affineFrame Q c w₀ i) / (t * lam i + g) ^ 2) - ∑ i, ((Qᵀ * B * Q) i i / (2 * lam
      i) + (Qᵀ *ᵥ b) i * (g * affineFrame Q c w₀ i) / lam i) - (-g * ∑ i, (Qᵀ * B * Q) i i / lam i ^
      2 + ∑ i, ∑ j, (Qᵀ * B * Q) i j * (g * affineFrame Q c w₀ i) * (g * affineFrame Q c w₀ j) /
      (lam i * lam j) - 2 * g * ∑ i, (Qᵀ *ᵥ b) i * (g * affineFrame Q c w₀ i) / lam i ^ 2) / t) :=
      by
    rw [← hΓ, ← hlead]
    ring
  rw [e]
  calc _ ≤ |_| + |_| := abs_sub _ _
    _ ≤ K₁ / t ^ 2 + (∑ i, |(Qᵀ * B * Q) i i| * (3 / 2 * g ^ 2 / lam i ^ 3) + ∑ i, ∑ j, |(Qᵀ * B *
        Q) i j * (g * affineFrame Q c w₀ i) * (g * affineFrame Q c w₀ j)| * (2 * g / (lam i ^ 2 *
            lam j) + g / (lam i * lam j ^ 2)) + ∑ i, |(Qᵀ *ᵥ b) i * (g * affineFrame Q c w₀ i)| *
                (3 * g ^ 2 / lam i ^ 3)) / t ^ 2 := add_le_add e₁ e₂
    _ = _ := by ring

end Multi

end Laplace.Multi
