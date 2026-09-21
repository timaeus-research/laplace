/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Multi.MonomialVisibility

/-!
# The virial identity in `d` dimensions

Proposition 12.4 of the working note *Patterning flow* for a `C¹` potential on `ℝᵈ`: under the
Gibbs measure `∝ e^{-U}`, `E[δ·∇U] = d`. The proof is Mathlib's multivariate integration by parts
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) applied coordinatewise to `f = x_i`,
`g = e^{-U}`, summed over `i`, with `δ·∇U = ∑ᵢ δᵢ ∂ᵢU = DU(δ)[δ]`. The hypotheses are the note's:
`e^{-U}`, `δᵢ e^{-U}` and `δᵢ ∂ᵢU e^{-U}` integrable, and `U` differentiable (the note allows
locally Lipschitz `U`; here `U` is `C¹`).

`virial_localized` is the form `nβ E[δ·∇K] + γ E‖δ‖² = d` for `U = nβ K + (γ/2)‖δ‖²`.
-/

namespace Laplace.Patterning

open MeasureTheory Laplace.Multi

variable {d : ℕ}

/-- `DU(x)[x] = ∑ i, x_i ∂_i U(x)`. -/
lemma fderiv_apply_self_eq_sum (U : EuclidD d → ℝ) (x : EuclidD d) :
    fderiv ℝ U x x = ∑ i, x i * fderiv ℝ U x (EuclideanSpace.single i 1) := by
  have hx : ∑ i, x i • (EuclideanSpace.single i (1 : ℝ) : EuclidD d) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h : fderiv ℝ U x x = fderiv ℝ U x (∑ i, x i • (EuclideanSpace.single i (1 : ℝ) : EuclidD d)) := by
    rw [hx]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

/-- **Coordinate integration by parts against `e^{-U}`**: `∫ x_i ∂_iU e^{-U} = ∫ e^{-U}`. -/
theorem integral_coord_mul_fderiv_mul_exp_neg (U : EuclidD d → ℝ) (hU : Differentiable ℝ U)
    (i : Fin d) (hint : Integrable fun x : EuclidD d => Real.exp (-U x))
    (hint1 : Integrable fun x : EuclidD d => x i * Real.exp (-U x))
    (hint2 : Integrable fun x : EuclidD d =>
      x i * fderiv ℝ U x (EuclideanSpace.single i 1) * Real.exp (-U x)) :
    ∫ x, x i * fderiv ℝ U x (EuclideanSpace.single i 1) * Real.exp (-U x)
      = ∫ x, Real.exp (-U x) := by
  set v : EuclidD d := EuclideanSpace.single i 1 with hv
  have hg : ∀ x, HasFDerivAt (fun x : EuclidD d => Real.exp (-U x))
      (Real.exp (-U x) • (-(fderiv ℝ U x))) x :=
    fun x => ((hU x).hasFDerivAt.neg).exp
  have hg' : ∀ x, fderiv ℝ (fun x : EuclidD d => Real.exp (-U x)) x v
      = -(fderiv ℝ U x v * Real.exp (-U x)) := by
    intro x
    rw [(hg x).fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
    ring
  have hf : ∀ x, fderiv ℝ (fun x : EuclidD d => x i) x v = 1 := by
    intro x
    have hd : HasFDerivAt (fun x : EuclidD d => x i) (EuclideanSpace.proj (𝕜 := ℝ) i) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    rw [hd.fderiv]
    change v i = 1
    simp [hv]
  have hA : Integrable fun x : EuclidD d =>
      fderiv ℝ (fun x : EuclidD d => x i) x v * Real.exp (-U x) :=
    hint.congr (Filter.Eventually.of_forall fun x => by simp [hf x])
  have hB : Integrable fun x : EuclidD d =>
      x i * fderiv ℝ (fun x : EuclidD d => Real.exp (-U x)) x v :=
    hint2.neg.congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.neg_apply, hg' x]
      ring)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hA hB hint1
    (fun x _ => (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt)
    (fun x _ => (hg x).differentiableAt)
  simp_rw [hg', hf, one_mul] at key
  have : (fun x : EuclidD d => x i * -(fderiv ℝ U x v * Real.exp (-U x)))
      = fun x => -(x i * fderiv ℝ U x v * Real.exp (-U x)) := by
    funext x
    ring
  rw [this, integral_neg, neg_inj] at key
  exact key

/-- **The virial identity in `d` dimensions** (Proposition 12.4): `∫ (δ·∇U) e^{-U} = d ∫ e^{-U}`. -/
theorem virial_multi (U : EuclidD d → ℝ) (hU : Differentiable ℝ U)
    (hint : Integrable fun x : EuclidD d => Real.exp (-U x))
    (hint1 : ∀ i, Integrable fun x : EuclidD d => x i * Real.exp (-U x))
    (hint2 : ∀ i, Integrable fun x : EuclidD d =>
      x i * fderiv ℝ U x (EuclideanSpace.single i 1) * Real.exp (-U x)) :
    ∫ x, fderiv ℝ U x x * Real.exp (-U x) = d * ∫ x, Real.exp (-U x) := by
  simp_rw [fderiv_apply_self_eq_sum U, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => hint2 i]
  rw [Finset.sum_congr rfl fun i _ =>
    integral_coord_mul_fderiv_mul_exp_neg U hU i hint (hint1 i) (hint2 i)]
  simp

/-- **Normalised form.** `E[δ·∇U] = d` under the Gibbs measure `∝ e^{-U}`. -/
theorem virial_multi_normalized (U : EuclidD d → ℝ) (hU : Differentiable ℝ U)
    (hint : Integrable fun x : EuclidD d => Real.exp (-U x))
    (hint1 : ∀ i, Integrable fun x : EuclidD d => x i * Real.exp (-U x))
    (hint2 : ∀ i, Integrable fun x : EuclidD d =>
      x i * fderiv ℝ U x (EuclideanSpace.single i 1) * Real.exp (-U x)) :
    (∫ x, fderiv ℝ U x x * Real.exp (-U x)) / (∫ x, Real.exp (-U x)) = d := by
  have hZ : 0 < ∫ x : EuclidD d, Real.exp (-U x) := integral_exp_pos hint
  rw [virial_multi U hU hint hint1 hint2, mul_div_assoc, div_self hZ.ne', mul_one]

/-- The localised potential `U = t K + (γ/2)‖δ‖²` has `DU(δ)[δ] = t DK(δ)[δ] + γ ‖δ‖²`. -/
lemma fderiv_localized_apply_self (K : EuclidD d → ℝ) (hK : Differentiable ℝ K) (t γ : ℝ)
    (x : EuclidD d) :
    fderiv ℝ (fun y : EuclidD d => t * K y + γ / 2 * ‖y‖ ^ 2) x x
      = t * fderiv ℝ K x x + γ * ‖x‖ ^ 2 := by
  have hd : HasFDerivAt (fun y : EuclidD d => t * K y + γ / 2 * ‖y‖ ^ 2)
      (t • fderiv ℝ K x + (γ / 2) • (2 • (innerSL ℝ x).comp (ContinuousLinearMap.id ℝ _))) x :=
    ((hK x).hasFDerivAt.const_mul t).add ((hasFDerivAt_id x).norm_sq.const_mul (γ / 2))
  rw [hd.fderiv]
  have hinner : ((innerSL ℝ) x) x = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, hinner]
  ring

/-- **Equation (virial) of the note**: for `U = nβ K + (γ/2)‖δ‖²`,
`nβ ∫ (δ·∇K) e^{-U} + γ ∫ ‖δ‖² e^{-U} = d ∫ e^{-U}`. -/
theorem virial_localized (K : EuclidD d → ℝ) (hK : Differentiable ℝ K) (t γ : ℝ)
    (hint : Integrable fun x : EuclidD d => Real.exp (-(t * K x + γ / 2 * ‖x‖ ^ 2)))
    (hint1 : ∀ i, Integrable fun x : EuclidD d =>
      x i * Real.exp (-(t * K x + γ / 2 * ‖x‖ ^ 2)))
    (hint2 : ∀ i, Integrable fun x : EuclidD d =>
      x i * fderiv ℝ (fun y : EuclidD d => t * K y + γ / 2 * ‖y‖ ^ 2) x (EuclideanSpace.single i 1)
        * Real.exp (-(t * K x + γ / 2 * ‖x‖ ^ 2)))
    (hintK : Integrable fun x : EuclidD d =>
      fderiv ℝ K x x * Real.exp (-(t * K x + γ / 2 * ‖x‖ ^ 2)))
    (hintN : Integrable fun x : EuclidD d => ‖x‖ ^ 2 * Real.exp (-(t * K x + γ / 2 * ‖x‖ ^ 2))) :
    t * (∫ x, fderiv ℝ K x x * Real.exp (-(t * K x + γ / 2 * ‖x‖ ^ 2)))
      + γ * (∫ x, ‖x‖ ^ 2 * Real.exp (-(t * K x + γ / 2 * ‖x‖ ^ 2)))
      = d * ∫ x, Real.exp (-(t * K x + γ / 2 * ‖x‖ ^ 2)) := by
  have hU : Differentiable ℝ (fun y : EuclidD d => t * K y + γ / 2 * ‖y‖ ^ 2) := fun x =>
    (((hK x).hasFDerivAt.const_mul t).add
      ((hasFDerivAt_id x).norm_sq.const_mul (γ / 2))).differentiableAt
  have h := virial_multi _ hU hint hint1 hint2
  simp_rw [fderiv_localized_apply_self K hK t γ] at h
  rw [← h, ← integral_const_mul, ← integral_const_mul, ← integral_add (hintK.const_mul t)
    (hintN.const_mul γ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

end Laplace.Patterning
