/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Sampler.ULA
import Laplace.Gibbs

/-!
# The virial identity and the effective degree

Proposition 12.4 of the working note *Patterning flow* and the ULA remark that follows it.

* `ula_virial_trace`: for any `X` with `(P - (h/2) P²) X = 1` (in particular the ULA law
  `ulaCov P h`), `tr(P X) = d + (h/2) tr(P² X)`. For the Gaussian potential `U = ½ δᵀ P δ`
  with second moment `X` this reads `E[δ·∇U] = d + (h/2) E‖∇U‖²`, the finite-step
  correction to the virial identity; `h = 0` is the Gibbs virial identity `E[δ·∇U] = d`.
* `virial_one_dim`: the genuine one-dimensional virial identity `∫ x U'(x) e^{-U} = ∫ e^{-U}`,
  from the whole-line fundamental theorem of calculus applied to `x e^{-U(x)}`; and the
  normalised form `⟨x U'(x)⟩ = 1` under the Gibbs measure.
* `degree_decomposition`: the algebra `nβ E[K] = (d - γ E|δ|²)/p_eff`.
-/

namespace Laplace.Patterning

open Matrix Laplace.Sampler MeasureTheory Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **ULA virial balance.** If `(P - (h/2) P²) X = 1` then
`tr(P X) = d + (h/2) tr(P² X)`. -/
theorem ula_virial_trace (P X : Matrix ι ι ℝ) (h : ℝ)
    (hX : (P - (h / 2) • (P * P)) * X = 1) :
    (P * X).trace = Fintype.card ι + (h / 2) * (P * P * X).trace := by
  have ht := congrArg Matrix.trace hX
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_one,
    smul_eq_mul] at ht
  linarith

/-- The ULA law satisfies the virial balance whenever it exists. -/
theorem ulaCov_virial (P : Matrix ι ι ℝ) (h : ℝ) (hdet : IsUnit (P - (h / 2) • (P * P)).det) :
    (P * ulaCov P h).trace = Fintype.card ι + (h / 2) * (P * P * ulaCov P h).trace :=
  ula_virial_trace P (ulaCov P h) h (Matrix.mul_nonsing_inv _ hdet)

/-- **Gibbs virial balance (Gaussian).** `tr(P P⁻¹) = d`: the `h = 0` case. -/
theorem gaussian_virial (P : Matrix ι ι ℝ) (hdet : IsUnit P.det) :
    (P * P⁻¹).trace = Fintype.card ι := by
  rw [Matrix.mul_nonsing_inv _ hdet, Matrix.trace_one]

/-- **Degree decomposition.** From `nβ E[δ·∇K] + γ E|δ|² = d` and
`p_eff = E[δ·∇K]/E[K]` (with `E[K] ≠ 0`, `p_eff ≠ 0`), `nβ E[K] = (d - γ E|δ|²)/p_eff`. -/
theorem degree_decomposition (t γ d a b K p : ℝ) (hvir : t * a + γ * b = d)
    (hK : K ≠ 0) (hp : p = a / K) (hp0 : p ≠ 0) :
    t * K = (d - γ * b) / p := by
  have ha : a = p * K := by rw [hp]; field_simp
  rw [eq_div_iff hp0]
  rw [ha] at hvir
  linarith

/-! ### The one-dimensional virial identity -/

/-- `x ↦ x e^{-U(x)}` has derivative `e^{-U} - x U' e^{-U}`. -/
lemma hasDerivAt_mul_exp_neg (U U' : ℝ → ℝ) (x : ℝ) (hU : HasDerivAt U (U' x) x) :
    HasDerivAt (fun y => y * Real.exp (-U y))
      (Real.exp (-U x) - x * U' x * Real.exp (-U x)) x := by
  have h := (hasDerivAt_id x).mul (hU.neg.exp)
  refine h.congr_deriv ?_
  simp only [id_eq, Pi.neg_apply]
  ring

/-- **One-dimensional virial identity.** `∫ x U'(x) e^{-U(x)} dx = ∫ e^{-U(x)} dx` when
`x e^{-U(x)} → 0` at both ends and both integrands are integrable. -/
theorem virial_one_dim (U U' : ℝ → ℝ) (hU : ∀ x, HasDerivAt U (U' x) x)
    (hint : Integrable (fun x => Real.exp (-U x)))
    (hint' : Integrable (fun x => x * U' x * Real.exp (-U x)))
    (hbot : Tendsto (fun x => x * Real.exp (-U x)) atBot (𝓝 0))
    (htop : Tendsto (fun x => x * Real.exp (-U x)) atTop (𝓝 0)) :
    ∫ x, x * U' x * Real.exp (-U x) = ∫ x, Real.exp (-U x) := by
  have hderiv : ∀ x, HasDerivAt (fun y => y * Real.exp (-U y))
      (Real.exp (-U x) - x * U' x * Real.exp (-U x)) x :=
    fun x => hasDerivAt_mul_exp_neg U U' x (hU x)
  have h := integral_of_hasDerivAt_of_tendsto hderiv (hint.sub hint') hbot htop
  rw [integral_sub hint hint'] at h
  linarith

/-- The positivity of the partition function `∫ e^{-U}`. -/
lemma integral_exp_neg_pos (U : ℝ → ℝ) (hint : Integrable (fun x => Real.exp (-U x))) :
    0 < ∫ x, Real.exp (-U x) :=
  integral_exp_pos hint

/-- **Normalised virial identity.** Under the Gibbs measure `∝ e^{-U}` (temperature `1`),
`⟨x U'(x)⟩ = 1`. -/
theorem gibbs_virial_one_dim (U U' : ℝ → ℝ) (hU : ∀ x, HasDerivAt U (U' x) x)
    (hint : Integrable (fun x => Real.exp (-U x)))
    (hint' : Integrable (fun x => x * U' x * Real.exp (-U x)))
    (hbot : Tendsto (fun x => x * Real.exp (-U x)) atBot (𝓝 0))
    (htop : Tendsto (fun x => x * Real.exp (-U x)) atTop (𝓝 0)) :
    Laplace.gibbsExpectation U 1 (fun x => x * U' x) = 1 := by
  unfold Laplace.gibbsExpectation Laplace.partitionFunction
  simp only [one_mul]
  rw [div_eq_one_iff_eq (integral_exp_neg_pos U hint).ne']
  exact virial_one_dim U U' hU hint hint' hbot htop

end Laplace.Patterning
