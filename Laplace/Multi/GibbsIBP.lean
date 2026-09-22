/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedAnharmonicSharp
import Laplace.OneD.MomentThirdOrder

/-!
# Integration by parts for the anharmonic Gibbs measure, and eq:mean to second order

For the one-dimensional anharmonic Gibbs measure `e^{−tℓ}`, `ℓ = λx²/2 + αx³/6 + γx⁴/24`, the
function `F_k = x^k e^{−tℓ}` and its derivative are integrable, so `∫ F_k' = 0`
(`integral_eq_zero_of_hasDerivAt_of_integrable`): the **Stein / integration-by-parts identity**
`k⟨x^{k−1}⟩ = t⟨x^k ℓ'(x)⟩` (`ibp_anharmonic`), i.e. the moment recursion
`(k+1)⟨x^k⟩ = t(λ⟨x^{k+2}⟩ + (α/2)⟨x^{k+3}⟩ + (γ/6)⟨x^{k+4}⟩)` (`moment_recursion`) and, at
`k = 0`, `λ⟨x⟩ + (α/2)⟨x²⟩ + (γ/6)⟨x³⟩ = 0` (`ibp_anharmonic_zero`).

Combined with the seabed's second moment to second order and third moment at leading order this
gives the **mean to second order**, `mean_anharmonic_order2_rate`:
`|t⟨x⟩ + α/(2λ²) − B₁/t| ≤ K/t²` with `B₁ = −5α³/(8λ⁵) + 2αγ/(3λ⁴)` (`meanCoeff2`), and on E2's
rotated oscillator eq:mean to second order, `meanShift_rot_order2_rate`:
`|⟨wⱼ⟩ − cⱼ − meanShift j − (meanShift₂)ⱼ/t²| ≤ K/t³` with `meanShift₂ = Q(B₁,ᵢ)ᵢ`. In the note's
scalar tensor language (`T = α`, `Q₄ = γ`, `S = 1/(λt)`):
`⟨x⟩ = −½tTS² + (2/3)t²TQ₄S⁴ − (5/8)t³T³S⁵ + O(t⁻³)`.
-/

open Real MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential cubicScale quarticScale)

/-! ### The derivative of the Boltzmann factor -/

section Deriv

variable {lam alpha gamma : ℝ}

/-- `ℓ'(x) = λx + (α/2)x² + (γ/6)x³`. -/
noncomputable def anharmonicDeriv (lam alpha gamma x : ℝ) : ℝ :=
  lam * x + alpha / 2 * x ^ 2 + gamma / 6 * x ^ 3

theorem hasDerivAt_anharmonicPotential (x : ℝ) :
    HasDerivAt (anharmonicPotential lam alpha gamma) (anharmonicDeriv lam alpha gamma x) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul (lam / 2)).add
    ((hasDerivAt_pow 3 x).const_mul (alpha / 6))).add ((hasDerivAt_pow 4 x).const_mul (gamma / 24))
  refine h.congr_deriv ?_
  unfold anharmonicDeriv
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem hasDerivAt_exp_neg_anharmonic (t x : ℝ) :
    HasDerivAt (fun y => Real.exp (-(t * anharmonicPotential lam alpha gamma y)))
      (-(t * anharmonicDeriv lam alpha gamma x) *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) x := by
  have h0 : HasDerivAt (fun y => -(t * anharmonicPotential lam alpha gamma y))
      (-(t * anharmonicDeriv lam alpha gamma x)) x :=
    ((hasDerivAt_anharmonicPotential (lam := lam) (alpha := alpha) (gamma := gamma) x).const_mul
      t).neg
  exact h0.exp.congr_deriv (by ring)

/-- `(x^k e^{−tℓ})' = k x^{k−1} e^{−tℓ} − t x^k ℓ'(x) e^{−tℓ}`. -/
theorem hasDerivAt_pow_mul_exp_neg_anharmonic (t : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => y ^ k * Real.exp (-(t * anharmonicPotential lam alpha gamma y)))
      ((k : ℝ) * (x ^ (k - 1) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) -
        t * (x ^ k * anharmonicDeriv lam alpha gamma x *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) x := by
  have h := (hasDerivAt_pow k x).mul
    (hasDerivAt_exp_neg_anharmonic (lam := lam) (alpha := alpha) (gamma := gamma) t x)
  exact h.congr_deriv (by ring)

end Deriv

/-! ### The integration-by-parts identity -/

section IBP

variable {lam alpha gamma : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

theorem integrable_pow_mul_deriv_exp {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * anharmonicDeriv lam alpha gamma x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  have h := (((integrable_pow_exp' hlam hgamma hdisc ht (k + 1)).const_mul lam).add
    ((integrable_pow_exp' hlam hgamma hdisc ht (k + 2)).const_mul (alpha / 2))).add
    ((integrable_pow_exp' hlam hgamma hdisc ht (k + 3)).const_mul (gamma / 6))
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  unfold anharmonicDeriv
  ring

theorem integral_deriv_pow_mul_exp_neg_anharmonic {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ∫ x : ℝ, ((k : ℝ) * (x ^ (k - 1) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) -
      t * (x ^ k * anharmonicDeriv lam alpha gamma x *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => hasDerivAt_pow_mul_exp_neg_anharmonic t k x)
    (((integrable_pow_exp' hlam hgamma hdisc ht (k - 1)).const_mul _).sub
      ((integrable_pow_mul_deriv_exp hlam hgamma hdisc ht k).const_mul _))
    (integrable_pow_exp' hlam hgamma hdisc ht k)

/-- **Integration by parts on the integrals**: `k ∫ x^{k−1} e^{−tℓ} = t ∫ x^k ℓ' e^{−tℓ}`. -/
theorem ibp_integral {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (k : ℝ) * ∫ x : ℝ, x ^ (k - 1) * Real.exp (-(t * anharmonicPotential lam alpha gamma x)) =
      t * ∫ x : ℝ, x ^ k * anharmonicDeriv lam alpha gamma x *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
  have h := integral_deriv_pow_mul_exp_neg_anharmonic hlam hgamma hdisc ht k
  rw [integral_sub ((integrable_pow_exp' hlam hgamma hdisc ht (k - 1)).const_mul _)
    ((integrable_pow_mul_deriv_exp hlam hgamma hdisc ht k).const_mul _), integral_const_mul,
    integral_const_mul, sub_eq_zero] at h
  exact h

omit hlam hgamma hdisc in
/-- **The Stein identity for a differentiable observable**: `⟨g'⟩ = t⟨g ℓ'⟩` whenever `g e^{−tℓ}`,
`g' e^{−tℓ}` and `g ℓ' e^{−tℓ}` are integrable. -/
theorem stein_anharmonic {t : ℝ} {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hgi : Integrable (fun x => g x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
    (hg'i : Integrable (fun x => g' x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
    (hgl : Integrable (fun x => g x * anharmonicDeriv lam alpha gamma x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) :
    _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t g' =
      t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => g x * anharmonicDeriv lam alpha gamma x) := by
  have hderiv : ∀ x, HasDerivAt
      (fun y => g y * Real.exp (-(t * anharmonicPotential lam alpha gamma y)))
      (g' x * Real.exp (-(t * anharmonicPotential lam alpha gamma x)) -
        t * (g x * anharmonicDeriv lam alpha gamma x *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) x := fun x =>
    ((hg x).mul (hasDerivAt_exp_neg_anharmonic (lam := lam) (alpha := alpha) (gamma := gamma)
      t x)).congr_deriv (by ring)
  have h := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (hg'i.sub (hgl.const_mul t)) hgi
  rw [integral_sub hg'i (hgl.const_mul t), integral_const_mul, sub_eq_zero] at h
  simp only [_root_.Laplace.gibbsExpectation]
  rw [← mul_div_assoc, h]

/-- **The Stein identity for the anharmonic Gibbs measure**: `k⟨x^{k−1}⟩ = t⟨x^k ℓ'(x)⟩`. -/
theorem ibp_anharmonic {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (k : ℝ) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (k - 1)) =
      t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ k * anharmonicDeriv lam alpha gamma x) := by
  simp only [_root_.Laplace.gibbsExpectation]
  rw [← mul_div_assoc, ← mul_div_assoc, ibp_integral hlam hgamma hdisc ht k]

/-- The moment recursion `(k+1)⟨x^k⟩ = t(λ⟨x^{k+2}⟩ + (α/2)⟨x^{k+3}⟩ + (γ/6)⟨x^{k+4}⟩)`. -/
theorem moment_recursion {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ((k : ℝ) + 1) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ k) =
      t * (lam * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ (k + 2)) +
          alpha / 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ (k + 3)) +
          gamma / 6 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ (k + 4))) := by
  have h := ibp_anharmonic hlam hgamma hdisc ht (k + 1)
  have e : (fun x : ℝ => x ^ (k + 1) * anharmonicDeriv lam alpha gamma x) =
      fun x => lam * x ^ (k + 2) + alpha / 2 * x ^ (k + 3) + gamma / 6 * x ^ (k + 4) := by
    funext x
    unfold anharmonicDeriv
    ring
  rw [e, gibbs_lin3 (integrable_pow_exp' hlam hgamma hdisc ht (k + 2))
    (integrable_pow_exp' hlam hgamma hdisc ht (k + 3))
    (integrable_pow_exp' hlam hgamma hdisc ht (k + 4))] at h
  simpa [Nat.add_sub_cancel] using h

/-- **`⟨ℓ'⟩ = 0`**: `λ⟨x⟩ + (α/2)⟨x²⟩ + (γ/6)⟨x³⟩ = 0`. -/
theorem ibp_anharmonic_zero {t : ℝ} (ht : 0 < t) :
    lam * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) +
        alpha / 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2) +
        gamma / 6 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) = 0 := by
  have h := ibp_anharmonic hlam hgamma hdisc ht 0
  have e : (fun x : ℝ => x ^ 0 * anharmonicDeriv lam alpha gamma x) =
      fun x => lam * x + alpha / 2 * x ^ 2 + gamma / 6 * x ^ 3 := by
    funext x
    unfold anharmonicDeriv
    ring
  have h1 := integrable_pow_exp' hlam hgamma hdisc ht 1
  simp only [pow_one] at h1
  rw [e, gibbs_lin3 h1 (integrable_pow_exp' hlam hgamma hdisc ht 2)
    (integrable_pow_exp' hlam hgamma hdisc ht 3)] at h
  simp only [Nat.cast_zero, zero_mul] at h
  rcases mul_eq_zero.mp h.symm with h0 | h0
  · exact absurd h0 ht.ne'
  · exact h0

end IBP

/-! ### The mean to second order -/

section Order2

variable {lam alpha gamma : ℝ}

/-- The second-order coefficient of the mean: `t⟨x⟩ = −α/(2λ²) + B₁/t + O(t⁻²)`. -/
noncomputable def meanCoeff2 (lam alpha gamma : ℝ) : ℝ :=
  -5 * alpha ^ 3 / (8 * lam ^ 5) + 2 * alpha * gamma / (3 * lam ^ 4)

/-- The seabed's second-moment coefficient in plain form. -/
theorem secondMoment_coeff_eq (hlam : 0 < lam) :
    45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma =
      5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2) := by
  unfold cubicScale quarticScale
  have hs : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
  have hs0 : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
  rw [div_pow, mul_pow, mul_pow, hs]
  field_simp
  ring

variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- **The mean to second order**: `|t⟨x⟩ + α/(2λ²) − B₁/t| ≤ K/t²`,
`B₁ = −5α³/(8λ⁵) + 2αγ/(3λ⁴)`. -/
theorem mean_anharmonic_order2_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) +
        alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t| ≤ K / t ^ 2 := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ :=
    Laplace.OneD.secondMoment_anharmonic_order3_rate hlam hgamma hdisc
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := Laplace.OneD.thirdMoment_anharmonic_rate_sharp hlam hgamma hdisc
  refine ⟨|alpha / (2 * lam)| * K₂ + |gamma / (6 * lam)| * K₃, T₂ + T₃, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have hT₂t : T₂ ≤ t := by linarith
  have hT₃t : T₃ ≤ t := by linarith
  have ht1 : 1 ≤ t := hT₂.trans hT₂t
  have ht0 : 0 < t := by linarith
  have hibp := ibp_anharmonic_zero hlam hgamma hdisc ht0
  have e₂ := h₂ hT₂t
  have e₃ := h₃ hT₃t
  rw [secondMoment_coeff_eq hlam] at e₂
  set M₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x) with hM₁
  set M₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2) with hM₂
  set M₃ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3) with hM₃
  have hM₁e : M₁ = -(alpha / (2 * lam)) * M₂ - gamma / (6 * lam) * M₃ := by
    field_simp
    linarith [hibp]
  have key : t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t =
      -(alpha / (2 * lam)) * (t * M₂ - 1 / lam -
          (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)) -
        gamma / (6 * lam) * ((t ^ 2 * M₃ + 5 * alpha / (2 * lam ^ 3)) / t) := by
    rw [hM₁e]
    unfold meanCoeff2
    field_simp
    ring
  rw [key]
  calc |-(alpha / (2 * lam)) * (t * M₂ - 1 / lam -
          (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)) -
        gamma / (6 * lam) * ((t ^ 2 * M₃ + 5 * alpha / (2 * lam ^ 3)) / t)|
      ≤ |-(alpha / (2 * lam)) * (t * M₂ - 1 / lam -
          (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t))| +
        |gamma / (6 * lam) * ((t ^ 2 * M₃ + 5 * alpha / (2 * lam ^ 3)) / t)| := abs_sub _ _
    _ = |alpha / (2 * lam)| * |t * M₂ - 1 / lam -
          (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)| +
        |gamma / (6 * lam)| * (|t ^ 2 * M₃ + 5 * alpha / (2 * lam ^ 3)| / t) := by
        rw [abs_mul, abs_neg, abs_mul, abs_div (t ^ 2 * M₃ + _), abs_of_pos ht0]
    _ ≤ |alpha / (2 * lam)| * (K₂ / t ^ 2) + |gamma / (6 * lam)| * (K₃ / t / t) := by gcongr
    _ = (|alpha / (2 * lam)| * K₂ + |gamma / (6 * lam)| * K₃) / t ^ 2 := by
        field_simp

end Order2

/-! ### eq:mean to second order on E2's rotated oscillator -/

section E2

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ}

/-- The second-order mean shift on E2's tensors: `Q (B₁,ᵢ)ᵢ`. -/
noncomputable def meanShift₂ (Q : Matrix (Fin d) (Fin d) ℝ) (lam alpha gamma : Fin d → ℝ) :
    Fin d → ℝ :=
  Q *ᵥ (fun i => meanCoeff2 (lam i) (alpha i) (gamma i))

/-- **eq:mean to second order, scaled**: for every ambient coordinate
`|t(⟨wⱼ⟩ − cⱼ) − (Q(−αᵢ/(2λᵢ²)))ⱼ − (meanShift₂)ⱼ/t| ≤ K/t²`. -/
theorem meanShift_rot_order2_scaled (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * (gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) - c j) -
        (Q *ᵥ fun i => -alpha i / (2 * lam i ^ 2)) j - meanShift₂ Q lam alpha gamma j / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sq (fun i => Q j i)
    (fun i t => t * _root_.Laplace.gibbsExpectation
        (anharmonicPotential (lam i) (alpha i) (gamma i)) t (fun x => x) +
      alpha i / (2 * lam i ^ 2) - meanCoeff2 (lam i) (alpha i) (gamma i) / t)
    (fun i => mean_anharmonic_order2_rate (hlam i) (hgamma i) (hdisc i))
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : t * (gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) -
        c j) - (Q *ᵥ fun i => -alpha i / (2 * lam i ^ 2)) j - meanShift₂ Q lam alpha gamma j / t =
      ∑ i, Q j i * (t * _root_.Laplace.gibbsExpectation
        (anharmonicPotential (lam i) (alpha i) (gamma i)) t (fun x => x) +
          alpha i / (2 * lam i ^ 2) - meanCoeff2 (lam i) (alpha i) (gamma i) / t) := by
    have hcoord : ∀ i, gibbsExpectation (separableAnharmonic lam alpha gamma) t (fun u => u i) =
        _root_.Laplace.gibbsExpectation (anharmonicPotential (lam i) (alpha i) (gamma i)) t
          (fun x => x) := fun i =>
      gibbsExpectation_coord_separableAnharmonic hlam hgamma hdisc ht0 i (fun x => x)
    rw [gibbsExpectation_coord_rotatedAnharmonic hQ c hlam hgamma hdisc ht0 j, add_sub_cancel_left]
    simp only [hcoord, meanShift₂, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  exact h ht

/-- **eq:mean to second order on E2's rotated oscillator**:
`|⟨wⱼ⟩ − cⱼ − meanShift t H T j − (meanShift₂)ⱼ/t²| ≤ K/t³`. -/
theorem meanShift_rot_order2_rate (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) - c j -
        meanShift t (Q * diagonal lam * Qᵀ) (rotT Q alpha) j -
        meanShift₂ Q lam alpha gamma j / t ^ 2| ≤ K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ := meanShift_rot_order2_scaled hQ c hlam hgamma hdisc j
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have hms : meanShift t (Q * diagonal lam * Qᵀ) (rotT Q alpha) j =
      (Q *ᵥ fun i => -alpha i / (2 * lam i ^ 2)) j / t := by
    rw [meanShift_rot hQ (fun i => (hlam i).ne') alpha ht0.ne']
    simp only [Matrix.mulVec, dotProduct, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by
      have := hlam i
      field_simp
  set E := gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) with hE
  have e : E - c j - (Q *ᵥ fun i => -alpha i / (2 * lam i ^ 2)) j / t -
      meanShift₂ Q lam alpha gamma j / t ^ 2 =
      (t * (E - c j) - (Q *ᵥ fun i => -alpha i / (2 * lam i ^ 2)) j -
        meanShift₂ Q lam alpha gamma j / t) / t := by
    field_simp
  rw [hms, e, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  calc |t * (E - c j) - (Q *ᵥ fun i => -alpha i / (2 * lam i ^ 2)) j -
        meanShift₂ Q lam alpha gamma j / t| ≤ K / t ^ 2 := h ht
    _ = K / t ^ 3 * t := by
        field_simp

end E2

end Laplace.Multi
