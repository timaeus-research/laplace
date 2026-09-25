/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The envelope derivative of a residual quadratic form

For a symmetric matrix path `C t`, a vector path `c t`, and `b t` solving the normal equations
`C t *ᵥ b t = c t`, the residual `s t = v t − ⟨c t, b t⟩` is differentiable at `t₀` as soon as `v`,
`c`, `C` are differentiable there and `b` is merely *continuous* there, with

  `s'(t₀) = v' − 2 ⟨b, c'⟩ + ⟨b, C' b⟩`   (`hasDerivAt_residual_form`),

no derivative of `b` being needed: the exact identity
`s(t) − s(t₀) = Δv − ⟨b(t), Δc⟩ − ⟨Δc, b(t₀)⟩ + ⟨b(t), ΔC b(t₀)⟩` (`residual_form_sub`) has a
difference quotient whose limit only involves `b(t) → b(t₀)`. This is the finite-dimensional
envelope theorem behind the curvature of the loss surface.
-/

open Filter Topology

namespace Laplace.Multi

variable {κ : Type*} [Fintype κ]

/-- The exact difference identity for the residual form, from the normal equations and symmetry. -/
theorem residual_form_sub (v : ℝ → ℝ) (c : ℝ → κ → ℝ) (C : ℝ → Matrix κ κ ℝ) (b : ℝ → κ → ℝ)
    (hsym : ∀ t i j, C t i j = C t j i) (hCb : ∀ t, (C t).mulVec (b t) = c t) (t t₀ : ℝ) :
    (v t - dotProduct (c t) (b t)) - (v t₀ - dotProduct (c t₀) (b t₀)) =
      (v t - v t₀) - ∑ i, b t i * (c t i - c t₀ i) - ∑ i, (c t i - c t₀ i) * b t₀ i +
        ∑ i, b t i * ∑ j, (C t i j - C t₀ i j) * b t₀ j := by
  have hCb' : ∀ s i, ∑ j, C s i j * b s j = c s i := fun s i ↦ by
    have := congrFun (hCb s) i
    simpa [Matrix.mulVec, dotProduct] using this
  have e1 : ∑ i, b t i * ∑ j, C t i j * b t₀ j = ∑ j, b t₀ j * c t j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hCb' t j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hsym t i j]
    ring
  have e2 : ∑ i, b t i * ∑ j, C t₀ i j * b t₀ j = ∑ i, b t i * c t₀ i :=
    Finset.sum_congr rfl fun i _ ↦ by rw [hCb' t₀ i]
  have e3 : ∑ i, b t i * ∑ j, (C t i j - C t₀ i j) * b t₀ j =
      ∑ i, b t i * ∑ j, C t i j * b t₀ j - ∑ i, b t i * ∑ j, C t₀ i j * b t₀ j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [e3, e1, e2]
  simp only [dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have e4 : ∑ j, b t₀ j * c t j = ∑ i, c t i * b t₀ i := Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have e5 : ∑ i, b t i * c t i = ∑ i, c t i * b t i := Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [e4, e5]
  ring

/-- Distributing a scalar through the difference identity. -/
theorem slope_form_aux (h A : ℝ) (p q r : κ → ℝ) (M : κ → κ → ℝ) :
    h⁻¹ * (A - ∑ i, p i * q i - ∑ i, q i * r i + ∑ i, p i * ∑ j, M i j * r j) =
      h⁻¹ * A - ∑ i, p i * (h⁻¹ * q i) - ∑ i, (h⁻¹ * q i) * r i +
        ∑ i, p i * ∑ j, (h⁻¹ * M i j) * r j := by
  have e1 : ∑ i, p i * (h⁻¹ * q i) = h⁻¹ * ∑ i, p i * q i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e2 : ∑ i, (h⁻¹ * q i) * r i = h⁻¹ * ∑ i, q i * r i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e3 : ∑ i, p i * ∑ j, (h⁻¹ * M i j) * r j = h⁻¹ * ∑ i, p i * ∑ j, M i j * r j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [e1, e2, e3]
  ring

/-- **The envelope derivative of the residual form**: with `C t *ᵥ b t = c t`, `C` symmetric,
`v, c, C` differentiable at `t₀` and `b` continuous at `t₀`,
`d/dt (v − ⟨c, b⟩) = v' − 2⟨b, c'⟩ + ⟨b, C' b⟩` at `t₀`. -/
theorem hasDerivAt_residual_form {v : ℝ → ℝ} {c : ℝ → κ → ℝ} {C : ℝ → Matrix κ κ ℝ}
    {b : ℝ → κ → ℝ} {v' : ℝ} {c' : κ → ℝ} {C' : Matrix κ κ ℝ} {t₀ : ℝ}
    (hv : HasDerivAt v v' t₀) (hc : ∀ i, HasDerivAt (fun t ↦ c t i) (c' i) t₀)
    (hC : ∀ i j, HasDerivAt (fun t ↦ C t i j) (C' i j) t₀) (hb : ContinuousAt b t₀)
    (hsym : ∀ t i j, C t i j = C t j i) (hCb : ∀ t, (C t).mulVec (b t) = c t) :
    HasDerivAt (fun t ↦ v t - dotProduct (c t) (b t))
      (v' - 2 * dotProduct (b t₀) c' + dotProduct (b t₀) (C'.mulVec (b t₀))) t₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  -- the slope of the residual form in terms of the slopes of the data
  have hkey : ∀ t, t ≠ t₀ →
      slope (fun t ↦ v t - dotProduct (c t) (b t)) t₀ t =
        slope v t₀ t - ∑ i, b t i * slope (fun t ↦ c t i) t₀ t -
          ∑ i, slope (fun t ↦ c t i) t₀ t * b t₀ i +
          ∑ i, b t i * ∑ j, slope (fun t ↦ C t i j) t₀ t * b t₀ j := by
    intro t _
    have hs : ∀ f : ℝ → ℝ, slope f t₀ t = (t - t₀)⁻¹ * (f t - f t₀) := fun f ↦ by
      rw [slope_def_field, div_eq_inv_mul]
    simp only [hs]
    rw [residual_form_sub v c C b hsym hCb t t₀]
    exact slope_form_aux (t - t₀) (v t - v t₀) (b t) (fun i ↦ c t i - c t₀ i) (b t₀)
      (fun i j ↦ C t i j - C t₀ i j)
  -- the limits
  have hbt : Tendsto b (𝓝[≠] t₀) (𝓝 (b t₀)) := hb.tendsto.mono_left nhdsWithin_le_nhds
  have hbi : ∀ i, Tendsto (fun t ↦ b t i) (𝓝[≠] t₀) (𝓝 (b t₀ i)) := fun i ↦
    tendsto_pi_nhds.1 hbt i
  have hlim : Tendsto (fun t ↦ slope v t₀ t - ∑ i, b t i * slope (fun t ↦ c t i) t₀ t -
      ∑ i, slope (fun t ↦ c t i) t₀ t * b t₀ i +
      ∑ i, b t i * ∑ j, slope (fun t ↦ C t i j) t₀ t * b t₀ j) (𝓝[≠] t₀)
      (𝓝 (v' - ∑ i, b t₀ i * c' i - ∑ i, c' i * b t₀ i +
        ∑ i, b t₀ i * ∑ j, C' i j * b t₀ j)) :=
    ((hv.tendsto_slope.sub (tendsto_finsetSum _ fun i _ ↦ (hbi i).mul (hc i).tendsto_slope)).sub
      (tendsto_finsetSum _ fun i _ ↦ (hc i).tendsto_slope.mul tendsto_const_nhds)).add
      (tendsto_finsetSum _ fun i _ ↦ (hbi i).mul
        (tendsto_finsetSum _ fun j _ ↦ (hC i j).tendsto_slope.mul tendsto_const_nhds))
  have hval : v' - ∑ i, b t₀ i * c' i - ∑ i, c' i * b t₀ i + ∑ i, b t₀ i * ∑ j, C' i j * b t₀ j =
      v' - 2 * dotProduct (b t₀) c' + dotProduct (b t₀) (C'.mulVec (b t₀)) := by
    simp only [dotProduct, Matrix.mulVec]
    have : ∑ i, c' i * b t₀ i = ∑ i, b t₀ i * c' i := Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    rw [this]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hkey t ht).symm

end Laplace.Multi
