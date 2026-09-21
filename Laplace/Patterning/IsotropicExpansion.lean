/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.GaussianFourth
import Laplace.Multi.Dilation

/-!
# The isotropic perturbation estimator: the scaling expansion of Proposition 8.1

Proposition 8.1 of the working note *Patterning flow* expands `Cov_δ[φ(w*+δ), ℓ(w*+δ)]` under
`δ ~ N(0, Σ_δ)` to leading orders in `‖Σ_δ‖`. Here the expansion is made exact for cubic
polynomial observables `obs c a A Q x = c + aᵀx + ½ xᵀAx + ⅙ Q(x,x,x)` and a family of
covariances `σ² Σ`, `Σ = H⁻¹`: with precision `σ⁻² H`,

  `Cov(obs c a A Q, obs c' g B R) = σ² aᵀΣg + σ⁴ C₄ + σ⁶ C₆`

exactly, where `C₄ = Cov_H(½xᵀAx, ½xᵀBx) + Cov_H(aᵀx, ⅙R(x,x,x)) + Cov_H(⅙Q(x,x,x), gᵀx)` and
`C₆ = Cov_H(⅙Q(x,x,x), ⅙R(x,x,x))`. The odd cross terms vanish by the symmetry `x ↦ -x`, and the
`σ²` and `σ⁴` coefficients are identified with `GaussianFourth.lean` (`C₄ = ½ tr(AΣBΣ) +
½ (Σg)ᵀ(Q:Σ) + ½ (Σa)ᵀ(R:Σ)` for symmetric `B, Q, R`). The note's `O(‖Σ_δ‖²)` and `O(‖Σ_δ‖³)`
statements follow as the explicit bounds `|Cov - σ² aᵀΣg| ≤ (|C₄| + |C₆|) σ⁴` and, for zero
gradients, `|Cov - σ⁴ C₄| ≤ |C₆| σ⁶` on `0 < σ ≤ 1`.

The main tools are the dilation change of variables (`gaussianExpectation_scaled`), the
bilinearity of `gaussianCovariance` on polynomial observables, and the parity lemma
`integral_odd_mul_quadKernel`.
-/

namespace Laplace.Patterning

open MeasureTheory Laplace.Multi

variable {d : ℕ}

/-! ### Scaling of the forms -/

lemma linForm_smul (a : Fin d → ℝ) (c : ℝ) (x : EuclidD d) :
    linForm a (c • x) = c * linForm a x := by
  unfold linForm
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma qform_smul_left (H : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (x : EuclidD d) :
    qform (c • H) x = c * qform H x := by
  rw [qform_eq_dotProduct, qform_eq_dotProduct, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma qform_smul_right (H : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (x : EuclidD d) :
    qform H (c • x) = c ^ 2 * qform H x := by
  rw [qform_eq_dotProduct, qform_eq_dotProduct, WithLp.ofLp_smul, Matrix.mulVec_smul,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

lemma cubicForm_smul (Q : Fin d → Fin d → Fin d → ℝ) (c : ℝ) (x : EuclidD d) :
    cubicForm Q (c • x) = c ^ 3 * cubicForm Q x := by
  unfold cubicForm
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

lemma quadKernel_inv_sq_smul (H : Matrix (Fin d) (Fin d) ℝ) (σ : ℝ) (x : EuclidD d) :
    quadKernel ((σ ^ 2)⁻¹ • H) x = quadKernel H (σ⁻¹ • x) := by
  unfold quadKernel
  rw [qform_smul_left, qform_smul_right, inv_pow]

lemma linForm_neg (a : Fin d → ℝ) (x : EuclidD d) : linForm a (-x) = -linForm a x := by
  rw [← neg_one_smul ℝ x, linForm_smul]
  ring

lemma qform_neg (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) : qform H (-x) = qform H x := by
  rw [← neg_one_smul ℝ x, qform_smul_right]
  ring

lemma cubicForm_neg (Q : Fin d → Fin d → Fin d → ℝ) (x : EuclidD d) :
    cubicForm Q (-x) = -cubicForm Q x := by
  rw [← neg_one_smul ℝ x, cubicForm_smul]
  ring

lemma quadKernel_neg (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    quadKernel H (-x) = quadKernel H x := by
  unfold quadKernel
  rw [qform_neg]

/-! ### The dilation identity for Gaussian expectations -/

/-- **Scaling.** The Gaussian with precision `σ⁻² H` (covariance `σ² Σ`) is the dilation by `σ`
of the Gaussian with precision `H`: `E_{σ⁻²H}[f] = E_H[f(σ·)]`. -/
theorem gaussianExpectation_scaled (H : Matrix (Fin d) (Fin d) ℝ) {σ : ℝ} (hσ : 0 < σ)
    (f : EuclidD d → ℝ) :
    gaussianExpectation ((σ ^ 2)⁻¹ • H) f = gaussianExpectation H (fun z => f (σ • z)) := by
  unfold gaussianExpectation
  simp_rw [quadKernel_inv_sq_smul]
  rw [integral_dilation (fun x => f x * quadKernel H (σ⁻¹ • x)) hσ,
    integral_dilation (fun x => quadKernel H (σ⁻¹ • x)) hσ]
  simp only [smul_smul, inv_mul_cancel₀ hσ.ne', one_smul]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ hσ.ne')]

theorem gaussianCovariance_scaled (H : Matrix (Fin d) (Fin d) ℝ) {σ : ℝ} (hσ : 0 < σ)
    (f g : EuclidD d → ℝ) :
    gaussianCovariance ((σ ^ 2)⁻¹ • H) f g
      = gaussianCovariance H (fun z => f (σ • z)) (fun z => g (σ • z)) := by
  unfold gaussianCovariance
  rw [gaussianExpectation_scaled H hσ, gaussianExpectation_scaled H hσ,
    gaussianExpectation_scaled H hσ]

/-! ### Parity -/

/-- The Lebesgue integral on `ℝᵈ` is invariant under `x ↦ -x`. -/
lemma integral_comp_neg (f : EuclidD d → ℝ) : ∫ x, f (-x) = ∫ x, f x := by
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (EuclidD d))) f
    (-1 : ℝ)
  simpa using h

/-- An odd function integrates to zero against the (even) Gaussian kernel. -/
theorem integral_odd_mul_quadKernel (H : Matrix (Fin d) (Fin d) ℝ) {g : EuclidD d → ℝ}
    (hodd : ∀ x, g (-x) = -g x) :
    ∫ x, g x * quadKernel H x = 0 := by
  have h := integral_comp_neg (fun x => g x * quadKernel H x)
  simp only [hodd, quadKernel_neg, neg_mul, integral_neg] at h
  linarith

/-- The covariance of an odd and an even observable vanishes. -/
theorem gaussianCovariance_odd_even (H : Matrix (Fin d) (Fin d) ℝ) {f g : EuclidD d → ℝ}
    (hf : ∀ x, f (-x) = -f x) (hg : ∀ x, g (-x) = g x) :
    gaussianCovariance H f g = 0 := by
  unfold gaussianCovariance gaussianExpectation
  have h1 : ∫ x, (fun x => f x * g x) x * quadKernel H x = 0 :=
    integral_odd_mul_quadKernel H fun x => by simp only [hf, hg, neg_mul]
  have h2 : ∫ x, f x * quadKernel H x = 0 := integral_odd_mul_quadKernel H hf
  rw [h1, h2]
  simp

theorem gaussianCovariance_even_odd (H : Matrix (Fin d) (Fin d) ℝ) {f g : EuclidD d → ℝ}
    (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = -g x) :
    gaussianCovariance H f g = 0 := by
  unfold gaussianCovariance gaussianExpectation
  have h1 : ∫ x, (fun x => f x * g x) x * quadKernel H x = 0 :=
    integral_odd_mul_quadKernel H fun x => by simp only [hf, hg, mul_neg]
  have h2 : ∫ x, g x * quadKernel H x = 0 := integral_odd_mul_quadKernel H hg
  rw [h1, h2]
  simp

/-! ### Polynomial observables and bilinearity -/

/-- A polynomial observable: `LowPoly` of some degree. -/
def IsPoly (f : EuclidD d → ℝ) : Prop := ∃ q, LowPoly q f

lemma IsPoly.const (c : ℝ) : IsPoly (fun _ : EuclidD d => c) := ⟨0, LowPoly.const 0 c⟩

lemma IsPoly.add {f g : EuclidD d → ℝ} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨max p q, LowPoly.add (hp.mono_le (le_max_left _ _)) (hq.mono_le (le_max_right _ _))⟩

lemma IsPoly.smul {f : EuclidD d → ℝ} (c : ℝ) (hf : IsPoly f) : IsPoly (fun x => c * f x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, LowPoly.smul c hp⟩

lemma IsPoly.continuous {f : EuclidD d → ℝ} (hf : IsPoly f) : Continuous f := by
  obtain ⟨p, hp⟩ := hf
  exact hp.contDiff.continuous

lemma IsPoly.growth {f : EuclidD d → ℝ} (hf : IsPoly f) : HasPolynomialGrowth f := by
  obtain ⟨p, hp⟩ := hf
  exact hp.growth

lemma IsPoly.integrable_mul_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {f : EuclidD d → ℝ} (hf : IsPoly f) :
    Integrable fun x : EuclidD d => f x * quadKernel H x :=
  integrable_mul_quadKernel_of_polynomialGrowth hH hf.continuous.aestronglyMeasurable hf.growth

lemma IsPoly.integrable_mul_mul_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {f g : EuclidD d → ℝ} (hf : IsPoly f) (hg : IsPoly g) :
    Integrable fun x : EuclidD d => f x * g x * quadKernel H x :=
  integrable_mul_quadKernel_of_polynomialGrowth hH
    (hf.continuous.mul hg.continuous).aestronglyMeasurable (hf.growth.mul hg.growth)

/-- Finite sums of `LowPoly` functions of a common degree. -/
lemma LowPoly.finset_sum {ι : Type*} (s : Finset ι) {q : ℕ} {F : ι → EuclidD d → ℝ}
    (h : ∀ i ∈ s, LowPoly q (F i)) : LowPoly q (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert LowPoly.const q 0 using 1
    funext x
    simp
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    convert LowPoly.add h1 h2 using 1
    funext x
    rw [Finset.sum_insert ha]

lemma lowPoly_linForm (a : Fin d → ℝ) : LowPoly 1 (linForm a) :=
  LowPoly.finset_sum Finset.univ fun m _ => LowPoly.smul (a m) (lowPoly_coord m)

lemma lowPoly_qform (A : Matrix (Fin d) (Fin d) ℝ) : LowPoly 2 (qform A) := by
  have h : qform A = fun x => ∑ i, ∑ j, A i j * (x i * x j) := by
    funext x
    exact qform_eq_sum A x
  rw [h]
  exact LowPoly.finset_sum Finset.univ fun i _ => LowPoly.finset_sum Finset.univ fun j _ =>
    LowPoly.smul (A i j) (LowPoly.coord_mul i (lowPoly_coord j))

lemma lowPoly_cubicForm (Q : Fin d → Fin d → Fin d → ℝ) : LowPoly 3 (cubicForm Q) :=
  LowPoly.finset_sum Finset.univ fun j _ => LowPoly.finset_sum Finset.univ fun k _ =>
    LowPoly.finset_sum Finset.univ fun l _ => LowPoly.smul (Q j k l) (lowPoly_coord3 j k l)

lemma IsPoly.linForm (a : Fin d → ℝ) : IsPoly (linForm a) := ⟨1, lowPoly_linForm a⟩

lemma IsPoly.qform_half (A : Matrix (Fin d) (Fin d) ℝ) : IsPoly (fun x => qform A x / 2) := by
  have := IsPoly.smul (1 / 2) ⟨2, lowPoly_qform A⟩
  convert this using 2
  ring

lemma IsPoly.cubicForm_sixth (Q : Fin d → Fin d → Fin d → ℝ) :
    IsPoly (fun x => cubicForm Q x / 6) := by
  have := IsPoly.smul (1 / 6) ⟨3, lowPoly_cubicForm Q⟩
  convert this using 2
  ring

theorem gaussianExpectation_const_mul (H : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (f : EuclidD d → ℝ) :
    gaussianExpectation H (fun x => c * f x) = c * gaussianExpectation H f := by
  unfold gaussianExpectation
  simp_rw [mul_assoc]
  rw [integral_const_mul, mul_div_assoc]

theorem gaussianExpectation_const {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (c : ℝ) :
    gaussianExpectation H (fun _ => c) = c := by
  unfold gaussianExpectation
  rw [integral_const_mul, mul_div_assoc, div_self (integral_quadKernel_pos hH).ne', mul_one]

theorem gaussianExpectation_sum {ι : Type*} (H : Matrix (Fin d) (Fin d) ℝ) (s : Finset ι)
    (F : ι → EuclidD d → ℝ)
    (hF : ∀ i ∈ s, Integrable fun x : EuclidD d => F i x * quadKernel H x) :
    gaussianExpectation H (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, gaussianExpectation H (F i) := by
  unfold gaussianExpectation
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ hF, Finset.sum_div]

/-- **Bilinearity of the covariance on polynomial observables.** -/
theorem gaussianCovariance_sum_sum {ι κ : Type*} {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (s : Finset ι) (t : Finset κ) (F : ι → EuclidD d → ℝ) (G : κ → EuclidD d → ℝ)
    (hF : ∀ i ∈ s, IsPoly (F i)) (hG : ∀ j ∈ t, IsPoly (G j)) :
    gaussianCovariance H (fun x => ∑ i ∈ s, F i x) (fun x => ∑ j ∈ t, G j x)
      = ∑ i ∈ s, ∑ j ∈ t, gaussianCovariance H (F i) (G j) := by
  unfold gaussianCovariance
  have hprod : (fun x => (∑ i ∈ s, F i x) * ∑ j ∈ t, G j x)
      = fun x => ∑ i ∈ s, ∑ j ∈ t, F i x * G j x := by
    funext x
    rw [Finset.sum_mul_sum]
  rw [hprod, gaussianExpectation_sum H s (fun i x => ∑ j ∈ t, F i x * G j x)
      (fun i hi => by
        simpa only [Finset.sum_mul] using integrable_finsetSum t fun j hj =>
          (hF i hi).integrable_mul_mul_quadKernel hH (hG j hj)),
    gaussianExpectation_sum H s F (fun i hi => (hF i hi).integrable_mul_quadKernel hH),
    gaussianExpectation_sum H t G (fun j hj => (hG j hj).integrable_mul_quadKernel hH),
    Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [gaussianExpectation_sum H t (fun j x => F i x * G j x)
    (fun j hj => (hF i hi).integrable_mul_mul_quadKernel hH (hG j hj)), ← Finset.sum_sub_distrib]

theorem gaussianCovariance_const_mul_left (H : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (f g : EuclidD d → ℝ) :
    gaussianCovariance H (fun x => c * f x) g = c * gaussianCovariance H f g := by
  unfold gaussianCovariance
  have h : (fun x => c * f x * g x) = fun x => c * (f x * g x) := by
    funext x
    ring
  rw [h, gaussianExpectation_const_mul, gaussianExpectation_const_mul]
  ring

theorem gaussianCovariance_const_mul_right (H : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (f g : EuclidD d → ℝ) :
    gaussianCovariance H f (fun x => c * g x) = c * gaussianCovariance H f g := by
  unfold gaussianCovariance
  have h : (fun x => f x * (c * g x)) = fun x => c * (f x * g x) := by
    funext x
    ring
  rw [h, gaussianExpectation_const_mul, gaussianExpectation_const_mul]
  ring

theorem gaussianCovariance_const_left {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (c : ℝ)
    (g : EuclidD d → ℝ) :
    gaussianCovariance H (fun _ => c) g = 0 := by
  unfold gaussianCovariance
  rw [gaussianExpectation_const_mul, gaussianExpectation_const hH]
  ring

theorem gaussianCovariance_const_right {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (c : ℝ)
    (f : EuclidD d → ℝ) :
    gaussianCovariance H f (fun _ => c) = 0 := by
  unfold gaussianCovariance
  have h : (fun x => f x * c) = fun x => c * f x := by
    funext x
    ring
  rw [h, gaussianExpectation_const_mul, gaussianExpectation_const hH]
  ring

theorem gaussianCovariance_comm (H : Matrix (Fin d) (Fin d) ℝ) (f g : EuclidD d → ℝ) :
    gaussianCovariance H f g = gaussianCovariance H g f := by
  unfold gaussianCovariance
  have h : (fun x => f x * g x) = fun x => g x * f x := by
    funext x
    ring
  rw [h]
  ring

theorem gaussianExpectation_odd (H : Matrix (Fin d) (Fin d) ℝ) {f : EuclidD d → ℝ}
    (hf : ∀ x, f (-x) = -f x) : gaussianExpectation H f = 0 := by
  unfold gaussianExpectation
  rw [integral_odd_mul_quadKernel H hf, zero_div]

/-- If `f` is odd its covariance with anything is the expectation of the product. -/
theorem gaussianCovariance_eq_expectation_of_odd (H : Matrix (Fin d) (Fin d) ℝ)
    {f g : EuclidD d → ℝ} (hf : ∀ x, f (-x) = -f x) :
    gaussianCovariance H f g = gaussianExpectation H (fun x => f x * g x) := by
  unfold gaussianCovariance
  rw [gaussianExpectation_odd H hf]
  ring

/-! ### Cubic polynomial observables and the exact expansion -/

/-- A cubic polynomial observable `c + aᵀx + ½ xᵀAx + ⅙ Q(x,x,x)`. -/
noncomputable def obs (c : ℝ) (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (Q : Fin d → Fin d → Fin d → ℝ) (x : EuclidD d) : ℝ :=
  c + linForm a x + qform A x / 2 + cubicForm Q x / 6

/-- The homogeneous pieces of `obs`, indexed by degree. -/
noncomputable def obsTerm (c : ℝ) (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (Q : Fin d → Fin d → Fin d → ℝ) : Fin 4 → EuclidD d → ℝ
  | 0 => fun _ => c
  | 1 => linForm a
  | 2 => fun x => qform A x / 2
  | 3 => fun x => cubicForm Q x / 6

lemma isPoly_obsTerm (c : ℝ) (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (Q : Fin d → Fin d → Fin d → ℝ) (i : Fin 4) : IsPoly (obsTerm c a A Q i) := by
  fin_cases i
  · exact IsPoly.const c
  · exact IsPoly.linForm a
  · exact IsPoly.qform_half A
  · exact IsPoly.cubicForm_sixth Q

/-- `obs(σz) = ∑_{k<4} σ^k · (degree-k piece)(z)`. -/
lemma obs_smul_eq_sum (c : ℝ) (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (Q : Fin d → Fin d → Fin d → ℝ) (σ : ℝ) (z : EuclidD d) :
    obs c a A Q (σ • z) = ∑ i : Fin 4, σ ^ (i : ℕ) * obsTerm c a A Q i z := by
  rw [Fin.sum_univ_four]
  unfold obs
  rw [linForm_smul, qform_smul_right, cubicForm_smul]
  simp only [obsTerm, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl]
  ring

/-! The four odd cross terms vanish. -/

lemma gaussianCovariance_linForm_qform_half (H : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) :
    gaussianCovariance H (linForm a) (fun x => qform B x / 2) = 0 :=
  gaussianCovariance_odd_even H (linForm_neg a) fun x => by simp only [qform_neg]

lemma gaussianCovariance_qform_half_linForm (H : Matrix (Fin d) (Fin d) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    gaussianCovariance H (fun x => qform A x / 2) (linForm g) = 0 :=
  gaussianCovariance_even_odd H (fun x => by simp only [qform_neg]) (linForm_neg g)

lemma gaussianCovariance_qform_half_cubicForm_sixth (H : Matrix (Fin d) (Fin d) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (R : Fin d → Fin d → Fin d → ℝ) :
    gaussianCovariance H (fun x => qform A x / 2) (fun x => cubicForm R x / 6) = 0 :=
  gaussianCovariance_even_odd H (fun x => by simp only [qform_neg]) fun x => by
    simp only [cubicForm_neg]
    ring

lemma gaussianCovariance_cubicForm_sixth_qform_half (H : Matrix (Fin d) (Fin d) ℝ)
    (Q : Fin d → Fin d → Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) :
    gaussianCovariance H (fun x => cubicForm Q x / 6) (fun x => qform B x / 2) = 0 :=
  gaussianCovariance_odd_even H (fun x => by simp only [cubicForm_neg]; ring) fun x => by
    simp only [qform_neg]

/-- **The exact scaling expansion of Proposition 8.1.** Under `N(0, σ²Σ)`, `Σ = H⁻¹`,
`Cov(obs c a A Q, obs c' g B R) = σ² aᵀΣg + σ⁴ C₄ + σ⁶ C₆` with
`C₄ = Cov_H(½xᵀAx, ½xᵀBx) + Cov_H(aᵀx, ⅙R(x,x,x)) + Cov_H(⅙Q(x,x,x), gᵀx)` and
`C₆ = Cov_H(⅙Q(x,x,x), ⅙R(x,x,x))`. -/
theorem gaussianCovariance_obs_scaled {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {σ : ℝ}
    (hσ : 0 < σ) (c : ℝ) (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (Q : Fin d → Fin d → Fin d → ℝ) (c' : ℝ) (g : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ)
    (R : Fin d → Fin d → Fin d → ℝ) :
    gaussianCovariance ((σ ^ 2)⁻¹ • H) (obs c a A Q) (obs c' g B R)
      = σ ^ 2 * (∑ m, ∑ n, a m * H⁻¹ m n * g n)
        + σ ^ 4 * (gaussianCovariance H (fun x => qform A x / 2) (fun x => qform B x / 2)
            + gaussianCovariance H (linForm a) (fun x => cubicForm R x / 6)
            + gaussianCovariance H (fun x => cubicForm Q x / 6) (linForm g))
        + σ ^ 6 * gaussianCovariance H (fun x => cubicForm Q x / 6)
            (fun x => cubicForm R x / 6) := by
  rw [gaussianCovariance_scaled H hσ]
  simp_rw [obs_smul_eq_sum]
  rw [gaussianCovariance_sum_sum hH Finset.univ Finset.univ _ _
    (fun i _ => (isPoly_obsTerm c a A Q i).smul _) (fun j _ => (isPoly_obsTerm c' g B R j).smul _)]
  simp only [Fin.sum_univ_four, gaussianCovariance_const_mul_left,
    gaussianCovariance_const_mul_right, obsTerm, Fin.isValue, Fin.val_zero, Fin.val_one,
    Fin.val_two, gaussianCovariance_const_left hH, gaussianCovariance_const_right hH,
    gaussianCovariance_linForm_qform_half, gaussianCovariance_qform_half_linForm,
    gaussianCovariance_qform_half_cubicForm_sixth, gaussianCovariance_cubicForm_sixth_qform_half,
    gaussianCovariance_linForm_linForm hH]
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl]
  ring

/-- **The `σ⁴` coefficient identified** (symmetric `B`, `Q`, `R`):
`C₄ = ½ tr(AΣBΣ) + ½ (Σa)ᵀ(R:Σ) + ½ (Σg)ᵀ(Q:Σ)`. -/
theorem gaussianCovariance_obs_scaled_symm {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {σ : ℝ}
    (hσ : 0 < σ) (c : ℝ) (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (Q : Fin d → Fin d → Fin d → ℝ) (c' : ℝ) (g : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ)
    (R : Fin d → Fin d → Fin d → ℝ) (hB : B.transpose = B)
    (hQ : ∀ j k l, Q j k l = Q j l k ∧ Q j k l = Q k j l)
    (hR : ∀ j k l, R j k l = R j l k ∧ R j k l = R k j l) :
    gaussianCovariance ((σ ^ 2)⁻¹ • H) (obs c a A Q) (obs c' g B R)
      = σ ^ 2 * (∑ m, ∑ n, a m * H⁻¹ m n * g n)
        + σ ^ 4 * ((1 / 2) * (A * H⁻¹ * B * H⁻¹).trace
            + (1 / 2) * ∑ j, (∑ m, H⁻¹ j m * a m) * contract R H⁻¹ j
            + (1 / 2) * ∑ j, (∑ m, H⁻¹ j m * g m) * contract Q H⁻¹ j)
        + σ ^ 6 * gaussianCovariance H (fun x => cubicForm Q x / 6)
            (fun x => cubicForm R x / 6) := by
  rw [gaussianCovariance_obs_scaled hH hσ, gaussianCovariance_half_qform hH A B hB,
    gaussianCovariance_eq_expectation_of_odd H (linForm_neg a),
    gaussianCovariance_comm H (fun x => cubicForm Q x / 6),
    gaussianCovariance_eq_expectation_of_odd H (linForm_neg g),
    gaussianExpectation_linForm_mul_cubicForm_div_six hH a R hR,
    gaussianExpectation_linForm_mul_cubicForm_div_six hH g Q hQ]

/-- **Proposition 8.1, first display, with an explicit remainder.** For `0 < σ ≤ 1`,
`|Cov - σ² aᵀΣg| ≤ (|C₄| + |C₆|) σ⁴`: the remainder is `O(‖Σ_δ‖²)` with `‖Σ_δ‖ ∝ σ²`. -/
theorem gaussianCovariance_obs_scaled_bound {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (c : ℝ) (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (Q : Fin d → Fin d → Fin d → ℝ) (c' : ℝ) (g : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ)
    (R : Fin d → Fin d → Fin d → ℝ) :
    |gaussianCovariance ((σ ^ 2)⁻¹ • H) (obs c a A Q) (obs c' g B R)
        - σ ^ 2 * (∑ m, ∑ n, a m * H⁻¹ m n * g n)|
      ≤ (|gaussianCovariance H (fun x => qform A x / 2) (fun x => qform B x / 2)
            + gaussianCovariance H (linForm a) (fun x => cubicForm R x / 6)
            + gaussianCovariance H (fun x => cubicForm Q x / 6) (linForm g)|
          + |gaussianCovariance H (fun x => cubicForm Q x / 6) (fun x => cubicForm R x / 6)|)
        * σ ^ 4 := by
  rw [gaussianCovariance_obs_scaled hH hσ]
  set S := ∑ m, ∑ n, a m * H⁻¹ m n * g n
  set C₄ := gaussianCovariance H (fun x => qform A x / 2) (fun x => qform B x / 2)
    + gaussianCovariance H (linForm a) (fun x => cubicForm R x / 6)
    + gaussianCovariance H (fun x => cubicForm Q x / 6) (linForm g)
  set C₆ := gaussianCovariance H (fun x => cubicForm Q x / 6) (fun x => cubicForm R x / 6)
  have h4 : 0 < σ ^ 4 := by positivity
  have h6 : σ ^ 6 ≤ σ ^ 4 := pow_le_pow_of_le_one hσ.le hσ1 (by norm_num)
  calc |σ ^ 2 * S + σ ^ 4 * C₄ + σ ^ 6 * C₆ - σ ^ 2 * S| = |σ ^ 4 * C₄ + σ ^ 6 * C₆| := by
        ring_nf
    _ ≤ |σ ^ 4 * C₄| + |σ ^ 6 * C₆| := abs_add_le _ _
    _ = σ ^ 4 * |C₄| + σ ^ 6 * |C₆| := by
        rw [abs_mul, abs_mul, abs_of_pos h4, abs_of_pos (pow_pos hσ 6)]
    _ ≤ σ ^ 4 * |C₄| + σ ^ 4 * |C₆| := by gcongr
    _ = (|C₄| + |C₆|) * σ ^ 4 := by ring

/-- **Proposition 8.1, second display.** For zero gradients the expansion starts at `σ⁴`:
`Cov = σ⁴ Cov_H(½xᵀAx, ½xᵀBx) + σ⁶ C₆`, so the remainder after the quadratic–quadratic term is
`O(‖Σ_δ‖³)`. -/
theorem gaussianCovariance_obs_scaled_zero_grad {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {σ : ℝ} (hσ : 0 < σ) (c : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (Q : Fin d → Fin d → Fin d → ℝ)
    (c' : ℝ) (B : Matrix (Fin d) (Fin d) ℝ) (R : Fin d → Fin d → Fin d → ℝ) :
    gaussianCovariance ((σ ^ 2)⁻¹ • H) (obs c (fun _ => 0) A Q) (obs c' (fun _ => 0) B R)
      = σ ^ 4 * gaussianCovariance H (fun x => qform A x / 2) (fun x => qform B x / 2)
        + σ ^ 6 * gaussianCovariance H (fun x => cubicForm Q x / 6)
            (fun x => cubicForm R x / 6) := by
  rw [gaussianCovariance_obs_scaled hH hσ]
  have hl : linForm (fun _ : Fin d => (0 : ℝ)) = fun _ => 0 := by
    funext x
    simp [linForm]
  simp only [hl, gaussianCovariance_const_left hH, gaussianCovariance_const_right hH, zero_mul,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add]

end Laplace.Patterning
