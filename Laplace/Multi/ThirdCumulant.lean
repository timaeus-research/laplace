/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AnnealingRay

/-!
# Second-order response: the third cumulant and the Amari–Chentsov tensor

The posterior covariance changes along the data manifold at the rate of the third cumulant.
With `κ₃(φ, ψ, χ) = ⟨φψχ⟩ − ⟨φψ⟩⟨χ⟩ − ⟨φχ⟩⟨ψ⟩ − ⟨ψχ⟩⟨φ⟩ + 2⟨φ⟩⟨ψ⟩⟨χ⟩` (`priorCum3`):

* along a data line, `d/ds Cov_{a+sv}(φ, ψ) = −t κ₃(φ, ψ, R_v)` (`hasDerivAt_priorCov_line`);
* hence the **second-order response** `D²m(a)[u, v]ᵢ = t² κ₃(Rᵢ, R_u, R_v)`
  (`hasDerivAt_meanMapDeriv_line`), symmetric in `u, v`;
* the response form (Fisher metric) changes by the totally symmetric cubic tensor
  `d/ds G_{a+sw}(u, v) = −t³ κ₃(R_u, R_v, R_w)` (`hasDerivAt_responseForm_line`), the
  Amari–Chentsov tensor of the family (`priorCum3` is symmetric in all three slots);
* in the temperature, `d/dt Cov_{t,a}(φ, ψ) = −κ₃(φ, ψ, L_a)` (`hasDerivAt_priorCov_temp`).

All of these follow from one algebraic lemma: whenever every bounded expectation moves by
`−c Cov(·, D)`, every covariance moves by `−c κ₃(·, ·, D)` (`hasDerivAt_cov_of_hasDerivAt_exp`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The third posterior cumulant `κ₃(φ, ψ, χ)`. -/
noncomputable def priorCum3 (μ : Measure X) (π L φ ψ χ : X → ℝ) (t : ℝ) : ℝ :=
  priorExp μ π L (fun x ↦ φ x * ψ x * χ x) t -
    priorExp μ π L (fun x ↦ φ x * ψ x) t * priorExp μ π L χ t -
    priorExp μ π L (fun x ↦ φ x * χ x) t * priorExp μ π L ψ t -
    priorExp μ π L (fun x ↦ ψ x * χ x) t * priorExp μ π L φ t +
    2 * priorExp μ π L φ t * priorExp μ π L ψ t * priorExp μ π L χ t

theorem priorCum3_swap₁₂ (π L φ ψ χ : X → ℝ) (t : ℝ) :
    priorCum3 μ π L φ ψ χ t = priorCum3 μ π L ψ φ χ t := by
  unfold priorCum3
  have e1 : (fun x ↦ φ x * ψ x * χ x) = fun x ↦ ψ x * φ x * χ x := funext fun x ↦ by ring
  have e2 : (fun x ↦ φ x * ψ x) = fun x ↦ ψ x * φ x := funext fun x ↦ by ring
  rw [e1, e2]
  ring

theorem priorCum3_swap₂₃ (π L φ ψ χ : X → ℝ) (t : ℝ) :
    priorCum3 μ π L φ ψ χ t = priorCum3 μ π L φ χ ψ t := by
  unfold priorCum3
  have e1 : (fun x ↦ φ x * ψ x * χ x) = fun x ↦ φ x * χ x * ψ x := funext fun x ↦ by ring
  have e2 : (fun x ↦ ψ x * χ x) = fun x ↦ χ x * ψ x := funext fun x ↦ by ring
  rw [e1, e2]
  ring

/-- **The covariance moves by the third cumulant**: if every bounded expectation along a
one-parameter family satisfies `d/ds E_s[f] = −c Cov_{s₀}(f, D)` at `s₀`, then
`d/ds Cov_s(φ, ψ) = −c κ₃(φ, ψ, D)` there. -/
theorem hasDerivAt_cov_of_hasDerivAt_exp {π : X → ℝ} {L : ℝ → X → ℝ} {D : X → ℝ} {c s₀ : ℝ}
    {τ : ℝ → ℝ}
    (hE : ∀ f : X → ℝ, Bdd f → HasDerivAt (fun s ↦ priorExp μ π (L s) f (τ s))
      (-c * priorCov μ π (L s₀) f D (τ s₀)) s₀)
    {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ) :
    HasDerivAt (fun s ↦ priorCov μ π (L s) φ ψ (τ s))
      (-c * priorCum3 μ π (L s₀) φ ψ D (τ s₀)) s₀ := by
  have h := (hE _ (hφ.mul hψ)).sub ((hE φ hφ).mul (hE ψ hψ))
  refine h.congr_deriv ?_
  simp only [priorCov, priorCum3]
  ring

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- The expectation of a bounded observable along a data line:
`d/ds ⟨f⟩_{a+sv} = −t Cov(f, R_v)`. -/
theorem hasDerivAt_priorExp_line (ht : 0 < t) (a v : ι → ℝ) (s₀ : ℝ) {f : X → ℝ} (hf : Bdd f) :
    HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a + s • v)) f t)
      (-t * priorCov μ π (affLoss L₀ R (a + s₀ • v)) f (dirLoss R v) t) s₀ := by
  obtain ⟨hfm, Mf, hfb⟩ := hf
  have h := (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hfm hfb ht
    (a + s₀ • v)).comp_hasDerivAt s₀ (hasDerivAt_affineLine a v s₀)
  refine h.congr_deriv ?_
  exact obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hfm hfb ht (a + s₀ • v) v

/-- **Second-order response, covariance form**: `d/ds Cov_{a+sv}(φ, ψ) = −t κ₃(φ, ψ, R_v)`. -/
theorem hasDerivAt_priorCov_line (ht : 0 < t) (a v : ι → ℝ) (s₀ : ℝ) {φ ψ : X → ℝ} (hφ : Bdd φ)
    (hψ : Bdd ψ) :
    HasDerivAt (fun s ↦ priorCov μ π (affLoss L₀ R (a + s • v)) φ ψ t)
      (-t * priorCum3 μ π (affLoss L₀ R (a + s₀ • v)) φ ψ (dirLoss R v) t) s₀ :=
  hasDerivAt_cov_of_hasDerivAt_exp (L := fun s : ℝ ↦ affLoss L₀ R (a + s • v)) (τ := fun _ ↦ t)
    (fun _ hf ↦ hasDerivAt_priorExp_line hπm hπi hπ hπpos hL₀m hL₀ hR ht a v s₀ hf) hφ hψ

/-- **The second derivative of the mean map**: `d/ds Dm(a+sv)[u]ᵢ = t² κ₃(Rᵢ, R_u, R_v)`. -/
theorem hasDerivAt_meanMapDeriv_line (ht : 0 < t) (a u v : ι → ℝ) (s₀ : ℝ) (i : ι) :
    HasDerivAt (fun s ↦ meanMapDeriv μ π L₀ R t (a + s • v) u i)
      (t ^ 2 * priorCum3 μ π (affLoss L₀ R (a + s₀ • v)) (R i) (dirLoss R u) (dirLoss R v) t)
      s₀ := by
  have e : (fun s : ℝ ↦ meanMapDeriv μ π L₀ R t (a + s • v) u i) =
      fun s : ℝ ↦ -t * priorCov μ π (affLoss L₀ R (a + s • v)) (R i) (dirLoss R u) t := by
    funext s
    exact meanMapDeriv_apply hπm hπi (fun x ↦ (hπ x).le) hL₀m hL₀ hR ht
      (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) (a + s • v)).ne' u i
  rw [e]
  refine ((hasDerivAt_priorCov_line hπm hπi hπ hπpos hL₀m hL₀ hR ht a v s₀ (hR i)
    (bdd_dirLoss hR u)).const_mul (-t)).congr_deriv ?_
  ring

/-- **The derivative of the response form is the Amari–Chentsov tensor**:
`d/ds G_{a+sw}(u, v) = −t³ κ₃(R_u, R_v, R_w)`. -/
theorem hasDerivAt_responseForm_line (ht : 0 < t) (a u v w : ι → ℝ) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ responseForm μ π L₀ R (a + s • w) t u v)
      (-t ^ 3 * priorCum3 μ π (affLoss L₀ R (a + s₀ • w)) (dirLoss R u) (dirLoss R v)
        (dirLoss R w) t) s₀ := by
  unfold responseForm
  refine ((hasDerivAt_priorCov_line hπm hπi hπ hπpos hL₀m hL₀ hR ht a w s₀ (bdd_dirLoss hR u)
    (bdd_dirLoss hR v)).const_mul (t ^ 2)).congr_deriv ?_
  ring

/-- The third derivative of the free energy along a line:
`d/ds Var_{a+sv}(R_v) = −t κ₃(R_v, R_v, R_v)`. -/
theorem hasDerivAt_segVar_line (ht : 0 < t) (a v : ι → ℝ) (s₀ : ℝ) :
    HasDerivAt (segVar μ π L₀ R t a v)
      (-t * priorCum3 μ π (affLoss L₀ R (a + s₀ • v)) (dirLoss R v) (dirLoss R v) (dirLoss R v) t)
      s₀ :=
  hasDerivAt_priorCov_line hπm hπi hπ hπpos hL₀m hL₀ hR ht a v s₀ (bdd_dirLoss hR v)
    (bdd_dirLoss hR v)

/-- **The temperature derivative of the covariance**: `d/dt Cov_{t,a}(φ, ψ) = −κ₃(φ, ψ, L_a)`. -/
theorem hasDerivAt_priorCov_temp (a : ι → ℝ) (t₀ : ℝ) {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ) :
    HasDerivAt (fun t ↦ priorCov μ π (affLoss L₀ R a) φ ψ t)
      (-priorCum3 μ π (affLoss L₀ R a) φ ψ (affLoss L₀ R a) t₀) t₀ := by
  have h := hasDerivAt_cov_of_hasDerivAt_exp (L := fun _ ↦ affLoss L₀ R a) (τ := fun t ↦ t)
    (c := 1) (D := affLoss L₀ R a) (s₀ := t₀)
    (fun f hf ↦ ((hasDerivAt_priorExp_temp hπm hπi hπ hπpos hL₀m hL₀ hR a t₀ hf).congr_deriv
      (by ring))) hφ hψ
  exact h.congr_deriv (by ring)

end

end Laplace.Multi
