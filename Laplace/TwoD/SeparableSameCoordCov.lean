/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.TwoD.AddSeparable

/-!
# Same-coordinate covariance under a separable 2D Gibbs measure

Companion to `gibbsCov_addSeparable_fst_snd_eq_zero` (mixed-covariance vanishing).
For a separable potential `L(x, y) = U(x) + V(y)` the covariance of two
observables of the *same* coordinate is inherited unchanged from the corresponding
1D marginal:

* `gibbsCov_addSeparable_fst_fst_eq`: `Cov_2D(f∘fst, g∘fst) = Cov_U(f, g)`.
* `gibbsCov_addSeparable_snd_snd_eq`: `Cov_2D(f∘snd, g∘snd) = Cov_V(f, g)`.

Together with the cross-covariance vanishing, this makes the covariance matrix of
`(f∘fst, g∘snd)` block-diagonal for separable potentials — the structural input for
the multivariate `Cov_t[φ, ψ] = (1/t)⟨∇φ, Σ ∇ψ⟩` story (Stage 3), where the
separable `Σ` is exactly this block-diagonal.

The proof reuses the separable-observable factorisation, collapsing the free
coordinate with the constant observable `1` (whose Gibbs expectation is `1`).
-/

open MeasureTheory

namespace Laplace.TwoD

/-- **Same-coordinate covariance inherited from 1D (first factor)**: under a
separable Gibbs measure, the covariance of two first-coordinate observables
equals their 1D covariance under `U`. With `gibbsCov_addSeparable_fst_snd_eq_zero`
this makes the covariance matrix block-diagonal for separable potentials. -/
theorem gibbsCov_addSeparable_fst_fst_eq
    {U V : ℝ → ℝ} {t : ℝ} (f g : ℝ → ℝ)
    (hZU_ne : Laplace.partitionFunction U t ≠ 0)
    (hZV_ne : Laplace.partitionFunction V t ≠ 0)
    (hU : Integrable (fun x : ℝ => Real.exp (-(t * U x))))
    (hV : Integrable (fun y : ℝ => Real.exp (-(t * V y))))
    (hf : Integrable (fun x : ℝ => f x * Real.exp (-(t * U x))))
    (hg : Integrable (fun x : ℝ => g x * Real.exp (-(t * U x))))
    (hfg : Integrable (fun x : ℝ => f x * g x * Real.exp (-(t * U x)))) :
    gibbsCov (addSeparable U V) t (fun z => f z.1) (fun z => g z.1) =
      Laplace.gibbsCov U t f g := by
  unfold gibbsCov Laplace.gibbsCov
  have hg1 : Laplace.gibbsExpectation V t (fun _ => (1 : ℝ)) = 1 :=
    Laplace.gibbsExpectation_const V t 1 hZV_ne
  -- The product observable `f(z.1)·g(z.1)` is `(f·g)(z.1)`, collapsing with the
  -- second factor `1`.
  have hExp_fg : gibbsExpectation (addSeparable U V) t (fun z => f z.1 * g z.1) =
      Laplace.gibbsExpectation U t (fun x => f x * g x) := by
    have h := gibbsExpectation_separable_addSeparable (fun x => f x * g x)
      (fun _ => (1 : ℝ)) hZU_ne hZV_ne hU hV hfg (Integrable.const_mul hV 1)
    rw [show (fun z : ℝ × ℝ => f z.1 * g z.1 * (1 : ℝ)) =
          (fun z : ℝ × ℝ => f z.1 * g z.1) from by
          funext z; exact MulOneClass.mul_one _] at h
    rw [h, hg1, mul_one]
  have hExp_f : gibbsExpectation (addSeparable U V) t (fun z => f z.1) =
      Laplace.gibbsExpectation U t f := by
    have h := gibbsExpectation_separable_addSeparable f (fun _ => (1 : ℝ))
      hZU_ne hZV_ne hU hV hf (Integrable.const_mul hV 1)
    rw [show (fun z : ℝ × ℝ => f z.1 * (1 : ℝ)) = (fun z : ℝ × ℝ => f z.1) from by
          funext z; exact MulOneClass.mul_one (f z.1)] at h
    rw [h, hg1, mul_one]
  have hExp_g : gibbsExpectation (addSeparable U V) t (fun z => g z.1) =
      Laplace.gibbsExpectation U t g := by
    have h := gibbsExpectation_separable_addSeparable g (fun _ => (1 : ℝ))
      hZU_ne hZV_ne hU hV hg (Integrable.const_mul hV 1)
    rw [show (fun z : ℝ × ℝ => g z.1 * (1 : ℝ)) = (fun z : ℝ × ℝ => g z.1) from by
          funext z; exact MulOneClass.mul_one (g z.1)] at h
    rw [h, hg1, mul_one]
  rw [hExp_fg, hExp_f, hExp_g]

/-- **Same-coordinate covariance inherited from 1D (second factor)**: the
covariance of two second-coordinate observables equals their 1D covariance
under `V`. -/
theorem gibbsCov_addSeparable_snd_snd_eq
    {U V : ℝ → ℝ} {t : ℝ} (f g : ℝ → ℝ)
    (hZU_ne : Laplace.partitionFunction U t ≠ 0)
    (hZV_ne : Laplace.partitionFunction V t ≠ 0)
    (hU : Integrable (fun x : ℝ => Real.exp (-(t * U x))))
    (hV : Integrable (fun y : ℝ => Real.exp (-(t * V y))))
    (hf : Integrable (fun y : ℝ => f y * Real.exp (-(t * V y))))
    (hg : Integrable (fun y : ℝ => g y * Real.exp (-(t * V y))))
    (hfg : Integrable (fun y : ℝ => f y * g y * Real.exp (-(t * V y)))) :
    gibbsCov (addSeparable U V) t (fun z => f z.2) (fun z => g z.2) =
      Laplace.gibbsCov V t f g := by
  unfold gibbsCov Laplace.gibbsCov
  have hf1 : Laplace.gibbsExpectation U t (fun _ => (1 : ℝ)) = 1 :=
    Laplace.gibbsExpectation_const U t 1 hZU_ne
  have hExp_fg : gibbsExpectation (addSeparable U V) t (fun z => f z.2 * g z.2) =
      Laplace.gibbsExpectation V t (fun y => f y * g y) := by
    have h := gibbsExpectation_separable_addSeparable (fun _ => (1 : ℝ))
      (fun y => f y * g y) hZU_ne hZV_ne hU hV (Integrable.const_mul hU 1) hfg
    rw [show (fun z : ℝ × ℝ => (1 : ℝ) * (f z.2 * g z.2)) =
          (fun z : ℝ × ℝ => f z.2 * g z.2) from by
          funext z; exact one_mul _] at h
    rw [h, hf1, one_mul]
  have hExp_f : gibbsExpectation (addSeparable U V) t (fun z => f z.2) =
      Laplace.gibbsExpectation V t f := by
    have h := gibbsExpectation_separable_addSeparable (fun _ => (1 : ℝ)) f
      hZU_ne hZV_ne hU hV (Integrable.const_mul hU 1) hf
    rw [show (fun z : ℝ × ℝ => (1 : ℝ) * f z.2) = (fun z : ℝ × ℝ => f z.2) from by
          funext z; exact one_mul (f z.2)] at h
    rw [h, hf1, one_mul]
  have hExp_g : gibbsExpectation (addSeparable U V) t (fun z => g z.2) =
      Laplace.gibbsExpectation V t g := by
    have h := gibbsExpectation_separable_addSeparable (fun _ => (1 : ℝ)) g
      hZU_ne hZV_ne hU hV (Integrable.const_mul hU 1) hg
    rw [show (fun z : ℝ × ℝ => (1 : ℝ) * g z.2) = (fun z : ℝ × ℝ => g z.2) from by
          funext z; exact one_mul (g z.2)] at h
    rw [h, hf1, one_mul]
  rw [hExp_fg, hExp_f, hExp_g]

end Laplace.TwoD
