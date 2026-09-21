/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.OrnsteinUhlenbeck

/-!
# The Ornstein–Uhlenbeck equation driven by a continuous path

The deterministic half of the identification of the OU semigroup with the SDE
`dX = -HX ds + σ dW`. For a continuous driving path `w : ℝ → ℝᵈ` the equation is understood in
its integral form `X_s = x₀ - ∫₀ˢ H X_u du + σ w_s`, and the stochastic integral
`∫₀ˢ e^{-(s-u)H} σ dW_u` of a `C¹` deterministic integrand is written by integration by parts:

  `ouSol H σ x₀ w s = E_s x₀ + σ w_s - ∫₀ˢ E_{s-u} H σ w_u du`,   `E_s = e^{-sH}`.

* `ouSol_integral_equation`: `ouSol` solves the integral equation for every continuous path;
* `ouSol_unique`: it is the only continuous solution;
* `ouCovInt_eq_ouCov`: the covariance integral `∫₀ˢ E_u D E_u du` equals `Σ_s = Σ - E_s Σ E_s`
  whenever `HΣ + ΣH = D`.

Everything here is ordinary calculus; the probabilistic half (the law of `ouSol` driven by
Brownian motion) is in `OUBrownian.lean`.
-/

namespace Laplace.Patterning

open Matrix NormedSpace MeasureTheory Filter Topology intervalIntegral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

/-! ### Calculus of matrix paths applied to vector paths -/

/-- Entries of a differentiable matrix path are differentiable. -/
theorem hasDerivAt_entry {M : ℝ → Matrix ι ι ℝ} {M' : Matrix ι ι ℝ} {s : ℝ}
    (h : HasDerivAt M M' s) (i j : ι) : HasDerivAt (fun s => M s i j) (M' i j) s := by
  let L : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := fun A B => by simp
      map_smul' := fun c A => by simp }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt s h

/-- Product rule for a matrix path applied to a vector path. -/
theorem hasDerivAt_matrix_mulVec {M : ℝ → Matrix ι ι ℝ} {M' : Matrix ι ι ℝ}
    {v : ℝ → ι → ℝ} {v' : ι → ℝ} {s : ℝ} (hM : HasDerivAt M M' s) (hv : HasDerivAt v v' s) :
    HasDerivAt (fun s => M s *ᵥ v s) (M' *ᵥ v s + M s *ᵥ v') s := by
  rw [hasDerivAt_pi]
  intro i
  have hv' : ∀ j, HasDerivAt (fun s => v s j) (v' j) s := fun j => (hasDerivAt_pi.mp hv) j
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_entry hM i j).mul (hv' j)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp [Matrix.mulVec, dotProduct]
  · simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib]

/-- `M ↦ (v ↦ M *ᵥ v)` as a continuous linear map. -/
def mulVecCLM (M : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

@[simp] lemma mulVecCLM_apply (M : Matrix ι ι ℝ) (v : ι → ℝ) : mulVecCLM M v = M *ᵥ v := by
  simp [mulVecCLM]

/-- Pulling a constant matrix out of an interval integral. -/
theorem intervalIntegral_mulVec (M : Matrix ι ι ℝ) {f : ℝ → ι → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    ∫ u in a..b, M *ᵥ f u = M *ᵥ ∫ u in a..b, f u := by
  have := (mulVecCLM M).intervalIntegral_comp_comm hf
  simpa using this

theorem continuous_ouFlow (H : Matrix ι ι ℝ) : Continuous (ouFlow H) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_ouFlow H s).continuousAt

theorem ouFlow_neg (H : Matrix ι ι ℝ) (u : ℝ) : ouFlow H (-u) = exp (u • H) := by
  unfold ouFlow
  rw [neg_smul_neg]

/-- `d/du E_{-u} = H E_{-u}`. -/
theorem hasDerivAt_ouFlow_neg (H : Matrix ι ι ℝ) (u : ℝ) :
    HasDerivAt (fun u => ouFlow H (-u)) (H * ouFlow H (-u)) u := by
  have h := hasDerivAt_exp_smul_const' H u
  have h' : HasDerivAt (fun u => ouFlow H (-u)) (H * exp (u • H)) u :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ouFlow_neg H t)
  exact h'.congr_deriv (by rw [ouFlow_neg])

/-! ### The variation-of-constants solution -/

variable (H σ : Matrix ι ι ℝ) (x₀ : ι → ℝ) (w : ℝ → ι → ℝ)

/-- The OU solution driven by the path `w`: `E_s x₀ + σ w_s - ∫₀ˢ E_{s-u} H σ w_u du`. -/
def ouSol (s : ℝ) : ι → ℝ :=
  ouFlow H s *ᵥ x₀ + σ *ᵥ w s - ∫ u in (0 : ℝ)..s, (ouFlow H (s - u) * H * σ) *ᵥ w u

/-- The auxiliary integral `J s = ∫₀ˢ E_{-u} H σ w_u du`. -/
def ouAux (s : ℝ) : ι → ℝ := ∫ u in (0 : ℝ)..s, ouFlow H (-u) *ᵥ ((H * σ) *ᵥ w u)

variable {H σ x₀ w}

theorem continuous_ouAux_integrand (hw : Continuous w) :
    Continuous fun u => ouFlow H (-u) *ᵥ ((H * σ) *ᵥ w u) :=
  ((continuous_ouFlow H).comp continuous_neg).matrix_mulVec (continuous_const.matrix_mulVec hw)

theorem hasDerivAt_ouAux (hw : Continuous w) (s : ℝ) :
    HasDerivAt (ouAux H σ w) (ouFlow H (-s) *ᵥ ((H * σ) *ᵥ w s)) s :=
  ((continuous_ouAux_integrand (H := H) (σ := σ) hw).integral_hasStrictDerivAt 0 s).hasDerivAt

/-- The convolution term of `ouSol` factors through the flow: `∫₀ˢ E_{s-u} Hσ w_u = E_s J s`. -/
theorem ouSol_conv_eq (hw : Continuous w) (s : ℝ) :
    ∫ u in (0 : ℝ)..s, (ouFlow H (s - u) * H * σ) *ᵥ w u = ouFlow H s *ᵥ ouAux H σ w s := by
  unfold ouAux
  rw [← intervalIntegral_mulVec _ ((continuous_ouAux_integrand hw).intervalIntegrable 0 s)]
  refine integral_congr fun u _ => ?_
  rw [sub_eq_add_neg, ouFlow_add]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem ouSol_eq (hw : Continuous w) (s : ℝ) :
    ouSol H σ x₀ w s = ouFlow H s *ᵥ (x₀ - ouAux H σ w s) + σ *ᵥ w s := by
  unfold ouSol
  rw [ouSol_conv_eq hw, Matrix.mulVec_sub]
  abel

/-- The drift part `Y s = E_s (x₀ - J s)` satisfies `Y' = -H Y - H σ w`. -/
theorem hasDerivAt_ouDrift (hw : Continuous w) (s : ℝ) :
    HasDerivAt (fun s => ouFlow H s *ᵥ (x₀ - ouAux H σ w s))
      (-(H *ᵥ (ouFlow H s *ᵥ (x₀ - ouAux H σ w s))) - (H * σ) *ᵥ w s) s := by
  have h : HasDerivAt (fun s => ouFlow H s *ᵥ (x₀ - ouAux H σ w s))
      ((-H * ouFlow H s) *ᵥ (x₀ - ouAux H σ w s)
        + ouFlow H s *ᵥ (0 - ouFlow H (-s) *ᵥ ((H * σ) *ᵥ w s))) s :=
    hasDerivAt_matrix_mulVec (hasDerivAt_ouFlow H s)
      ((hasDerivAt_const s x₀).sub (hasDerivAt_ouAux (H := H) (σ := σ) hw s))
  refine h.congr_deriv ?_
  have h1 : (-H * ouFlow H s) *ᵥ (x₀ - ouAux H σ w s)
      = -(H *ᵥ (ouFlow H s *ᵥ (x₀ - ouAux H σ w s))) := by
    rw [Matrix.neg_mul, Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  have h2 : ouFlow H s *ᵥ (0 - ouFlow H (-s) *ᵥ ((H * σ) *ᵥ w s)) = -((H * σ) *ᵥ w s) := by
    rw [zero_sub, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← ouFlow_add, add_neg_cancel,
      ouFlow_zero, Matrix.one_mulVec]
  rw [h1, h2]
  abel

theorem continuous_ouDrift (hw : Continuous w) :
    Continuous fun s => ouFlow H s *ᵥ (x₀ - ouAux H σ w s) :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_ouDrift (x₀ := x₀) hw u).continuousAt

theorem continuous_ouSol (hw : Continuous w) : Continuous (ouSol H σ x₀ w) := by
  have : ouSol H σ x₀ w = fun s => ouFlow H s *ᵥ (x₀ - ouAux H σ w s) + σ *ᵥ w s :=
    funext (ouSol_eq hw)
  rw [this]
  exact (continuous_ouDrift hw).add (continuous_const.matrix_mulVec hw)

/-- **The integral equation.** For every continuous path, `ouSol` solves
`X_s = x₀ - ∫₀ˢ H X_u du + σ w_s`. -/
theorem ouSol_integral_equation (hw : Continuous w) (s : ℝ) :
    ouSol H σ x₀ w s = x₀ - (∫ u in (0 : ℝ)..s, H *ᵥ ouSol H σ x₀ w u) + σ *ᵥ w s := by
  set Y : ℝ → ι → ℝ := fun s => ouFlow H s *ᵥ (x₀ - ouAux H σ w s) with hY
  have hderiv : ∀ u, HasDerivAt Y (-(H *ᵥ Y u) - (H * σ) *ᵥ w u) u := fun u =>
    hasDerivAt_ouDrift hw u
  have hYc : Continuous Y := continuous_ouDrift hw
  have hint : IntervalIntegrable (fun u => -(H *ᵥ Y u) - (H * σ) *ᵥ w u) volume 0 s :=
    ((continuous_const.matrix_mulVec hYc).neg.sub (continuous_const.matrix_mulVec hw))
      |>.intervalIntegrable 0 s
  have hftc := integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hint
  have hY0 : Y 0 = x₀ := by simp [hY, ouAux, ouFlow_zero]
  rw [hY0] at hftc
  have hsol : ∀ u, ouSol H σ x₀ w u = Y u + σ *ᵥ w u := fun u => ouSol_eq hw u
  have hHsol : ∀ u, H *ᵥ ouSol H σ x₀ w u = -(-(H *ᵥ Y u) - (H * σ) *ᵥ w u) := by
    intro u
    rw [hsol, Matrix.mulVec_add, Matrix.mulVec_mulVec (w u) H σ]
    abel
  simp_rw [hHsol]
  rw [intervalIntegral.integral_neg, hftc, hsol s]
  abel

/-- **Uniqueness.** A continuous solution of the integral equation is `ouSol`. -/
theorem ouSol_unique (hw : Continuous w) {x : ℝ → ι → ℝ} (hx : Continuous x)
    (heq : ∀ s, x s = x₀ - (∫ u in (0 : ℝ)..s, H *ᵥ x u) + σ *ᵥ w s) (s : ℝ) :
    x s = ouSol H σ x₀ w s := by
  have hsolc : Continuous (ouSol H σ x₀ w) := continuous_ouSol hw
  set z : ℝ → ι → ℝ := fun s => x s - ouSol H σ x₀ w s with hz
  have hzc : Continuous z := hx.sub hsolc
  have hzeq : ∀ s, z s = -∫ u in (0 : ℝ)..s, H *ᵥ z u := by
    intro s
    have hi : IntervalIntegrable (fun u => H *ᵥ x u) volume 0 s :=
      (continuous_const.matrix_mulVec hx).intervalIntegrable 0 s
    have hi' : IntervalIntegrable (fun u => H *ᵥ ouSol H σ x₀ w u) volume 0 s :=
      (continuous_const.matrix_mulVec hsolc).intervalIntegrable 0 s
    have hsplit : (fun u => H *ᵥ z u) = fun u => H *ᵥ x u - H *ᵥ ouSol H σ x₀ w u :=
      funext fun u => Matrix.mulVec_sub _ _ _
    simp only [hz]
    rw [hsplit, integral_sub hi hi', heq s, ouSol_integral_equation hw s]
    abel
  have hzd : ∀ u, HasDerivAt z (-(H *ᵥ z u)) u := by
    intro u
    have hcont : Continuous fun u => H *ᵥ z u := continuous_const.matrix_mulVec hzc
    have h := ((hcont.integral_hasStrictDerivAt 0 u).hasDerivAt).neg
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => hzeq u)
  have hd : ∀ u, HasDerivAt (fun u => ouFlow H (-u) *ᵥ z u) 0 u := by
    intro u
    have h := hasDerivAt_matrix_mulVec (hasDerivAt_ouFlow_neg H u) (hzd u)
    refine h.congr_deriv ?_
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← ouFlow_comm, add_neg_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) s 0
  have h0 : z 0 = 0 := by
    rw [hzeq 0]
    simp
  rw [h0, Matrix.mulVec_zero] at hconst
  have h2 := congrArg (fun v => ouFlow H s *ᵥ v) hconst
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
  rw [← ouFlow_add, add_neg_cancel, ouFlow_zero, Matrix.one_mulVec] at h2
  exact sub_eq_zero.mp h2

/-! ### The covariance integral -/

/-- The covariance of the OU solution at time `s`: `∫₀ˢ E_u D E_u du`. -/
def ouCovInt (H D : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  ∫ u in (0 : ℝ)..s, ouFlow H u * D * ouFlow H u

theorem continuous_ouCovInt_integrand (H D : Matrix ι ι ℝ) :
    Continuous fun u => ouFlow H u * D * ouFlow H u :=
  ((continuous_ouFlow H).mul continuous_const).mul (continuous_ouFlow H)

theorem hasDerivAt_ouCovInt (H D : Matrix ι ι ℝ) (s : ℝ) :
    HasDerivAt (ouCovInt H D) (ouFlow H s * D * ouFlow H s) s :=
  ((continuous_ouCovInt_integrand H D).integral_hasStrictDerivAt 0 s).hasDerivAt

theorem ouCovInt_zero (H D : Matrix ι ι ℝ) : ouCovInt H D 0 = 0 := by
  simp [ouCovInt]

/-- **The covariance integral is the Lyapunov path.** If `HΣ + ΣH = D` then
`∫₀ˢ E_u D E_u du = Σ - E_s Σ E_s` for every `s`. -/
theorem ouCovInt_eq_ouCov (H S D : Matrix ι ι ℝ) (hLyap : H * S + S * H = D) (s : ℝ) :
    ouCovInt H D s = ouCov H S s := by
  have hd : ∀ u, HasDerivAt (fun u => ouCovInt H D u - ouCov H S u) 0 u := fun u =>
    ((hasDerivAt_ouCovInt H D u).sub (hasDerivAt_ouCov H S D hLyap u)).congr_deriv (sub_self _)
  have hconst := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) s 0
  simp only [ouCovInt_zero, ouCov_zero, sub_zero] at hconst
  exact sub_eq_zero.mp hconst

end

end Laplace.Patterning
