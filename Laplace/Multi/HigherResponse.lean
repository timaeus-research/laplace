/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMap

/-!
# All-orders derivatives along a mixture path

Along the mixture path `L_s = L₀ + sΔ` the unnormalised numerators `N_φ(s) = ∫ φ e^{-tL_s} π` are
infinitely differentiable with

  `N_φ^{(n)}(s) = (−t)^n ∫ φ Δ^n e^{-tL_s} π`   (`TiltData.iteratedDeriv_tiltNum`,
  `TiltData.iteratedDeriv_mixNum`, `TiltData.iteratedDeriv_priorZ_pathLoss`),

so every derivative of the response map along the path is a moment of the loss contrast under
the moving posterior: the whole path is determined by the joint moments of `(φ, Δ)` under the base
posterior (round-19/20 package `HigherResponse`, unnormalised layer). The normalised derivatives
are the cumulants `(−t)^n κ_{n+1}(φ, Δ, …, Δ)`; the first two are in `ResponseMap`.

We also record the endpoint of the map: for a loss-neutral base the posterior at `s = 0` is the
prior itself (`priorExp_const`), so the mixture path runs from the prior mean of `φ` to its
posterior mean.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A bounded observable times a power of the bounded residual is bounded. -/
theorem TiltData.bdd_mul_pow {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f : X → ℝ}
    (hf : Bdd f) (n : ℕ) : Bdd fun x ↦ f x * R x ^ n := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have e : (fun x ↦ f x * R x ^ (n + 1)) = fun x ↦ (f x * R x ^ n) * R x := by
      funext x
      ring
    rw [e]
    exact ih.mul h.bdd_R

/-- `(d/du)^n (c ∫ f e^{-tuR} ν) = c (−t)^n ∫ f R^n e^{-tuR} ν`. -/
theorem TiltData.iteratedDeriv_const_mul_tiltNum [Nonempty X] {ν R : X → ℝ} {M : ℝ}
    (h : TiltData μ ν R M) (t : ℝ) (n : ℕ) :
    ∀ (c : ℝ) {f : X → ℝ}, Bdd f →
      iteratedDeriv n (fun u ↦ c * tiltNum μ ν f R t u) =
        fun u ↦ c * (-t) ^ n * tiltNum μ ν (fun x ↦ f x * R x ^ n) R t u := by
  induction n with
  | zero =>
    intro c f _
    funext u
    simp
  | succ n ih =>
    intro c f hf
    rw [iteratedDeriv_succ']
    have hd : deriv (fun u ↦ c * tiltNum μ ν f R t u) =
        fun u ↦ (c * -t) * tiltNum μ ν (fun x ↦ f x * R x) R t u := by
      funext u
      obtain ⟨hfm, Mf, hfb⟩ := hf
      rw [((h.hasDerivAt_tiltNum hfm hfb t u).const_mul c).deriv]
      ring
    rw [hd, ih (c * -t) (hf.mul h.bdd_R)]
    funext u
    have e : (fun x ↦ f x * R x * R x ^ n) = fun x ↦ f x * R x ^ (n + 1) := by
      funext x
      ring
    rw [e]
    ring

/-- **All-orders derivatives of the tilted numerator**:
`(d/du)^n ∫ f e^{-tuR} ν = (−t)^n ∫ f R^n e^{-tuR} ν`. -/
theorem TiltData.iteratedDeriv_tiltNum [Nonempty X] {ν R : X → ℝ} {M : ℝ}
    (h : TiltData μ ν R M) {f : X → ℝ} (hf : Bdd f) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (fun u ↦ tiltNum μ ν f R t u) =
      fun u ↦ (-t) ^ n * tiltNum μ ν (fun x ↦ f x * R x ^ n) R t u := by
  have := h.iteratedDeriv_const_mul_tiltNum t n 1 hf
  simpa only [one_mul] using this

/-- The mixture numerator `∫ φ e^{-tL_s} π` is the tilted numerator of the base weight. -/
theorem mixNum_eq_tiltNum (π L₀ Δ φ : X → ℝ) (t s : ℝ) :
    (∫ x, φ x * Real.exp (-(t * pathLoss L₀ Δ s x)) * π x ∂μ) =
      tiltNum μ (baseWeight π L₀ t) φ Δ t s := by
  unfold tiltNum
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
    simp only [mul_assoc, exp_pathLoss_mul])

/-- **All-orders derivatives along the mixture path**:
`(d/ds)^n ∫ φ e^{-tL_s} π = (−t)^n ∫ φ Δ^n e^{-tL_s} π`. -/
theorem TiltData.iteratedDeriv_mixNum [Nonempty X] {π L₀ Δ : X → ℝ} {t M : ℝ}
    (h : TiltData μ (baseWeight π L₀ t) Δ M) {φ : X → ℝ} (hφ : Bdd φ) (n : ℕ) :
    iteratedDeriv n (fun s ↦ ∫ x, φ x * Real.exp (-(t * pathLoss L₀ Δ s x)) * π x ∂μ) =
      fun s ↦ (-t) ^ n * ∫ x, φ x * Δ x ^ n * Real.exp (-(t * pathLoss L₀ Δ s x)) * π x ∂μ := by
  simp only [mixNum_eq_tiltNum]
  exact h.iteratedDeriv_tiltNum hφ t n

/-- **All-orders derivatives of the partition function along the mixture path**:
`Z^{(n)}(s) = (−t)^n ∫ Δ^n e^{-tL_s} π` — the raw moments of the loss contrast. -/
theorem TiltData.iteratedDeriv_priorZ_pathLoss [Nonempty X] {π L₀ Δ : X → ℝ} {t M : ℝ}
    (h : TiltData μ (baseWeight π L₀ t) Δ M) (n : ℕ) :
    iteratedDeriv n (fun s ↦ priorZ μ π (pathLoss L₀ Δ s) t) =
      fun s ↦ (-t) ^ n * ∫ x, Δ x ^ n * Real.exp (-(t * pathLoss L₀ Δ s x)) * π x ∂μ := by
  have := h.iteratedDeriv_mixNum (φ := fun _ ↦ (1 : ℝ)) (Bdd.const 1) n
  simp only [one_mul] at this
  unfold priorZ
  exact this

/-- **The endpoint of the map**: for a loss-neutral base `L₀ = c` the posterior is the prior,
`⟨φ⟩ = ∫ φ π / ∫ π`. -/
theorem priorExp_const (π φ : X → ℝ) (c t : ℝ) :
    priorExp μ π (fun _ ↦ c) φ t = (∫ x, φ x * π x ∂μ) / ∫ x, π x ∂μ := by
  unfold priorExp priorZ
  have h1 : (∫ x, φ x * Real.exp (-(t * c)) * π x ∂μ) =
      Real.exp (-(t * c)) * ∫ x, φ x * π x ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  have h2 : (∫ x, Real.exp (-(t * c)) * π x ∂μ) = Real.exp (-(t * c)) * ∫ x, π x ∂μ :=
    integral_const_mul _ _
  rw [h1, h2, mul_div_mul_left _ _ (Real.exp_pos _).ne']

end Laplace.Multi
