/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ThirdCumulant

/-!
# The two-axis response and its integrability

Temperature `t` and data `a` are the two axes of the map. For a bounded observable `φ` along the
data line `a + s v`, with `L_s = L_{a+sv}` and `D = R_v`,

  `∂_t ⟨φ⟩ = −Cov(φ, L_s)`,   `∂_s ⟨φ⟩ = −t Cov(φ, D)`,

and the two mixed partials agree,

  `∂_s ∂_t ⟨φ⟩ = ∂_t ∂_s ⟨φ⟩ = −Cov(φ, D) + t κ₃(φ, D, L_s)`

(`hasDerivAt_exp_temp_line`, `hasDerivAt_exp_line_temp`): the response one-form
`d⟨φ⟩ = −Cov(φ, L_s) dt − t Cov(φ, D) ds` is exact, with `⟨φ⟩` its potential. Likewise the
free energy `A = log Z` is the potential of the loss-conjugate one-form
`dA = −⟨L_s⟩ dt − t ⟨D⟩ ds`, with mixed partial `−⟨D⟩ + t Cov(D, L_s)` in both orders
(`hasDerivAt_affLogZ_temp_line`, `hasDerivAt_affLogZ_line_temp`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

omit [MeasurableSpace X] in
theorem affLoss_add_smul_eq (L₀ : X → ℝ) (R : ι → X → ℝ) (a v : ι → ℝ) (s : ℝ) :
    affLoss L₀ R (a + s • v) = fun x ↦ affLoss L₀ R a x + s * dirLoss R v x := by
  funext x
  simp only [affLoss, dirLoss, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  ring

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

theorem priorExp_add_bdd (a : ι → ℝ) {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    priorExp μ π (affLoss L₀ R a) (fun x ↦ f x + g x) t =
      priorExp μ π (affLoss L₀ R a) f t + priorExp μ π (affLoss L₀ R a) g t :=
  priorExp_add_of_integrable (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a hf)
    (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a hg)

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem priorExp_const_mul_bdd (L f : X → ℝ) (c : ℝ) :
    priorExp μ π L (fun x ↦ c * f x) t = c * priorExp μ π L f t := by
  unfold priorExp
  simp only [mul_assoc]
  rw [integral_const_mul, mul_div_assoc]

theorem priorCov_add_right_bdd (a : ι → ℝ) {f g ψ : X → ℝ} (hf : Bdd f) (hg : Bdd g)
    (hψ : Bdd ψ) :
    priorCov μ π (affLoss L₀ R a) ψ (fun x ↦ f x + g x) t =
      priorCov μ π (affLoss L₀ R a) ψ f t + priorCov μ π (affLoss L₀ R a) ψ g t := by
  have e : (fun x ↦ ψ x * (f x + g x)) = fun x ↦ ψ x * f x + ψ x * g x :=
    funext fun x ↦ by ring
  simp only [priorCov]
  rw [e, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hψ.mul hf) (hψ.mul hg),
    priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a hf hg]
  ring

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem priorCov_const_mul_right' (L ψ f : X → ℝ) (c : ℝ) :
    priorCov μ π L ψ (fun x ↦ c * f x) t = c * priorCov μ π L ψ f t := by
  rw [priorCov_comm π L ψ _ t, priorCov_const_mul_left, priorCov_comm π L f ψ t]

/-- The covariance with the moving loss `L_{a+sv} = L_a + s R_v`. -/
theorem priorCov_affLoss_line (a v : ι → ℝ) (s : ℝ) {φ : X → ℝ} (hφ : Bdd φ) (b : ι → ℝ) :
    priorCov μ π (affLoss L₀ R b) φ (affLoss L₀ R (a + s • v)) t =
      priorCov μ π (affLoss L₀ R b) φ (affLoss L₀ R a) t +
        s * priorCov μ π (affLoss L₀ R b) φ (dirLoss R v) t := by
  rw [affLoss_add_smul_eq, priorCov_add_right_bdd hπm hπi hπ hπpos hL₀m hL₀ hR b
    (bdd_affLoss hL₀m hL₀ hR a) ((bdd_dirLoss hR v).const_mul s) hφ, priorCov_const_mul_right']

/-- The expectation of the moving loss `L_{a+sv} = L_a + s R_v`. -/
theorem priorExp_affLoss_line (a v : ι → ℝ) (s : ℝ) (b : ι → ℝ) :
    priorExp μ π (affLoss L₀ R b) (affLoss L₀ R (a + s • v)) t =
      priorExp μ π (affLoss L₀ R b) (affLoss L₀ R a) t +
        s * priorExp μ π (affLoss L₀ R b) (dirLoss R v) t := by
  rw [affLoss_add_smul_eq L₀ R a v s, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR b
    (bdd_affLoss hL₀m hL₀ hR a) ((bdd_dirLoss hR v).const_mul s), priorExp_const_mul_bdd]

/-- The third cumulant with the moving loss in the last slot. -/
theorem priorCum3_affLoss_line (a v : ι → ℝ) (s : ℝ) {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ)
    (b : ι → ℝ) :
    priorCum3 μ π (affLoss L₀ R b) φ ψ (affLoss L₀ R (a + s • v)) t =
      priorCum3 μ π (affLoss L₀ R b) φ ψ (affLoss L₀ R a) t +
        s * priorCum3 μ π (affLoss L₀ R b) φ ψ (dirLoss R v) t := by
  have hLa := bdd_affLoss hL₀m hL₀ hR a
  have hv := bdd_dirLoss hR v
  rw [affLoss_add_smul_eq]
  simp only [priorCum3]
  have e1 : (fun x ↦ φ x * ψ x * (affLoss L₀ R a x + s * dirLoss R v x)) =
      fun x ↦ φ x * ψ x * affLoss L₀ R a x + s * (φ x * ψ x * dirLoss R v x) :=
    funext fun x ↦ by ring
  have e2 : (fun x ↦ φ x * (affLoss L₀ R a x + s * dirLoss R v x)) =
      fun x ↦ φ x * affLoss L₀ R a x + s * (φ x * dirLoss R v x) := funext fun x ↦ by ring
  have e3 : (fun x ↦ ψ x * (affLoss L₀ R a x + s * dirLoss R v x)) =
      fun x ↦ ψ x * affLoss L₀ R a x + s * (ψ x * dirLoss R v x) := funext fun x ↦ by ring
  rw [e1, e2, e3, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR b ((hφ.mul hψ).mul hLa)
    (((hφ.mul hψ).mul hv).const_mul s), priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR b
    (hφ.mul hLa) ((hφ.mul hv).const_mul s), priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR b
    (hψ.mul hLa) ((hψ.mul hv).const_mul s), priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR b hLa
    (hv.const_mul s), priorExp_const_mul_bdd, priorExp_const_mul_bdd, priorExp_const_mul_bdd,
    priorExp_const_mul_bdd]
  ring

/-- **The mixed partial `∂_s ∂_t ⟨φ⟩`**: differentiating `∂_t⟨φ⟩ = −Cov(φ, L_{a+sv})` in `s`
gives `−Cov(φ, R_v) + t κ₃(φ, R_v, L_{a+sv})`. -/
theorem hasDerivAt_exp_temp_line (ht : 0 < t) (a v : ι → ℝ) (s₀ : ℝ) {φ : X → ℝ}
    (hφ : Bdd φ) :
    HasDerivAt (fun s ↦ -priorCov μ π (affLoss L₀ R (a + s • v)) φ (affLoss L₀ R (a + s • v)) t)
      (-priorCov μ π (affLoss L₀ R (a + s₀ • v)) φ (dirLoss R v) t +
        t * priorCum3 μ π (affLoss L₀ R (a + s₀ • v)) φ (dirLoss R v)
          (affLoss L₀ R (a + s₀ • v)) t) s₀ := by
  have hLa := bdd_affLoss hL₀m hL₀ hR a
  have hv := bdd_dirLoss hR v
  have e : (fun s ↦ -priorCov μ π (affLoss L₀ R (a + s • v)) φ (affLoss L₀ R (a + s • v)) t) =
      fun s ↦ -(priorCov μ π (affLoss L₀ R (a + s • v)) φ (affLoss L₀ R a) t +
        s * priorCov μ π (affLoss L₀ R (a + s • v)) φ (dirLoss R v) t) :=
    funext fun s ↦ by rw [priorCov_affLoss_line hπm hπi hπ hπpos hL₀m hL₀ hR a v s hφ]
  rw [e]
  have h1 := hasDerivAt_priorCov_line hπm hπi hπ hπpos hL₀m hL₀ hR ht a v s₀ hφ hLa
  have h2 := hasDerivAt_priorCov_line hπm hπi hπ hπpos hL₀m hL₀ hR ht a v s₀ hφ hv
  refine ((h1.add ((hasDerivAt_id s₀).mul h2)).neg).congr_deriv ?_
  rw [priorCum3_affLoss_line hπm hπi hπ hπpos hL₀m hL₀ hR a v s₀ hφ hv,
    priorCum3_swap₂₃ π _ φ (dirLoss R v) (affLoss L₀ R a) t]
  simp only [id_eq]
  ring

/-- **The mixed partial `∂_t ∂_s ⟨φ⟩`**: differentiating `∂_s⟨φ⟩ = −t Cov(φ, R_v)` in `t` gives
the same `−Cov(φ, R_v) + t κ₃(φ, R_v, L_{a+sv})`. -/
theorem hasDerivAt_exp_line_temp (a v : ι → ℝ) (s : ℝ) (t₀ : ℝ) {φ : X → ℝ} (hφ : Bdd φ) :
    HasDerivAt (fun t ↦ -t * priorCov μ π (affLoss L₀ R (a + s • v)) φ (dirLoss R v) t)
      (-priorCov μ π (affLoss L₀ R (a + s • v)) φ (dirLoss R v) t₀ +
        t₀ * priorCum3 μ π (affLoss L₀ R (a + s • v)) φ (dirLoss R v)
          (affLoss L₀ R (a + s • v)) t₀) t₀ := by
  have h := ((hasDerivAt_id t₀).neg).mul
    (hasDerivAt_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR (a + s • v) t₀ hφ (bdd_dirLoss hR v))
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, id_eq]
  ring

/-- **The mixed partial of the free energy, `∂_s ∂_t A`**: `−⟨R_v⟩ + t Cov(R_v, L_{a+sv})`. -/
theorem hasDerivAt_affLogZ_temp_line (ht : 0 < t) (a v : ι → ℝ) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ -priorExp μ π (affLoss L₀ R (a + s • v)) (affLoss L₀ R (a + s • v)) t)
      (-priorExp μ π (affLoss L₀ R (a + s₀ • v)) (dirLoss R v) t +
        t * priorCov μ π (affLoss L₀ R (a + s₀ • v)) (dirLoss R v)
          (affLoss L₀ R (a + s₀ • v)) t) s₀ := by
  have hLa := bdd_affLoss hL₀m hL₀ hR a
  have hv := bdd_dirLoss hR v
  have e : (fun s ↦ -priorExp μ π (affLoss L₀ R (a + s • v)) (affLoss L₀ R (a + s • v)) t) =
      fun s ↦ -(priorExp μ π (affLoss L₀ R (a + s • v)) (affLoss L₀ R a) t +
        s * priorExp μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) t) :=
    funext fun s ↦ by rw [priorExp_affLoss_line hπm hπi hπ hπpos hL₀m hL₀ hR a v s]
  rw [e]
  have h1 := hasDerivAt_priorExp_line hπm hπi hπ hπpos hL₀m hL₀ hR ht a v s₀ hLa
  have h2 := hasDerivAt_priorExp_line hπm hπi hπ hπpos hL₀m hL₀ hR ht a v s₀ hv
  refine ((h1.add ((hasDerivAt_id s₀).mul h2)).neg).congr_deriv ?_
  rw [priorCov_affLoss_line hπm hπi hπ hπpos hL₀m hL₀ hR a v s₀ hv,
    priorCov_comm π _ (affLoss L₀ R a) (dirLoss R v) t]
  simp only [id_eq]
  ring

/-- **The mixed partial of the free energy, `∂_t ∂_s A`**: the same
`−⟨R_v⟩ + t Cov(R_v, L_{a+sv})`. (`∂_t A = −⟨L_{a+sv}⟩` is `hasDerivAt_affLogZ_temp`,
`∂_s A = −t ⟨R_v⟩` is `hasDerivAt_affLogZ_line`.) -/
theorem hasDerivAt_affLogZ_line_temp (a v : ι → ℝ) (s : ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ -t * priorExp μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) t)
      (-priorExp μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) t₀ +
        t₀ * priorCov μ π (affLoss L₀ R (a + s • v)) (dirLoss R v)
          (affLoss L₀ R (a + s • v)) t₀) t₀ := by
  have h := ((hasDerivAt_id t₀).neg).mul
    (hasDerivAt_priorExp_temp hπm hπi hπ hπpos hL₀m hL₀ hR (a + s • v) t₀ (bdd_dirLoss hR v))
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, id_eq]
  ring

end

end Laplace.Multi
