/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# The score-function identity for reweighting by resampling

Patterning implemented by *resampling* draws the minibatch indices of a training run independently
from the tilted law `h_ε(i) = q(i)(1 + ε ω(i))` on the data index set `ι`, with `∑ᵢ q(i) ω(i) = 0`
so that `h_ε` is a probability law for every small `ε`. The trained parameters, and any observable
`φ` of them, are then a function of the drawn index path `s : Fin T → ι` (the batch size is folded
into `T`; randomness independent of the indices, such as an initial kick, is absorbed by
conditioning on it). This file proves the exact identity

  `d/dε E_ε[φ] |_{ε = 0} = E_0[φ · ∑ₖ ω(sₖ)] = ∑ᵢ ω(i) Cov_0(φ, Nᵢ)`,   `Nᵢ = #{k : sₖ = i}`,

the score-function (REINFORCE) form of the response of a training run to a resampling of its data:
the *path-space susceptibility* `Cov_0(φ(w_T), Nᵢ)` is the covariance of the terminal observable
with the number of times sample `i` was drawn, over ordinary training runs. It is the exact discrete
counterpart of the Girsanov response of the working note *Patterning flow* (Prop. "Girsanov
response"), with the score `∑ₖ ω(sₖ)` in place of the stochastic integral `∫ uᵀ dW`, and it needs no
fixed-diffusion approximation: the resampled run's own randomness is the index sequence. No
differentiability of `φ`, of the loss, or of the update rule in `w` is assumed, so the identity
holds at a degenerate point where the checkpoint-frozen force vanishes.

Everything is a finite sum, so the statements are exact identities about derivatives of polynomials
in `ε`.
-/

namespace Laplace.Patterning

open Finset

variable {ι : Type*} {T : ℕ}

/-! ### The path probability and its score -/

/-- Probability of the index path `s` when the `T` draws are independent with law
`i ↦ q(i)(1 + ε ω(i))`. -/
def pathProb (q ω : ι → ℝ) (ε : ℝ) (s : Fin T → ι) : ℝ :=
  ∏ k, q (s k) * (1 + ε * ω (s k))

theorem pathProb_zero (q ω : ι → ℝ) (s : Fin T → ι) : pathProb q ω 0 s = ∏ k, q (s k) := by
  simp [pathProb]

/-- `d/dε ∏_{k ∈ u} (1 + ε cₖ) = ∑_{k ∈ u} cₖ` at `ε = 0`. -/
theorem hasDerivAt_prod_one_add {α : Type*} (u : Finset α) (c : α → ℝ) :
    HasDerivAt (fun ε : ℝ => ∏ k ∈ u, (1 + ε * c k)) (∑ k ∈ u, c k) 0 := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | insert a u ha ih =>
    have h1 : HasDerivAt (fun ε : ℝ => 1 + ε * c a) (c a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (c a)).const_add 1
    have h := h1.mul ih
    simp only [prod_insert ha, sum_insert ha]
    refine h.congr_deriv ?_
    simp

/-- The path probability is differentiable in the tilt, with derivative the base probability times
the score `∑ₖ ω(sₖ)`. -/
theorem hasDerivAt_pathProb (q ω : ι → ℝ) (s : Fin T → ι) :
    HasDerivAt (fun ε => pathProb q ω ε s) ((∏ k, q (s k)) * ∑ k, ω (s k)) 0 := by
  have h := (hasDerivAt_prod_one_add (univ : Finset (Fin T)) (fun k => ω (s k))).const_mul
    (∏ k, q (s k))
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => ?_)
  simp only [pathProb, prod_mul_distrib]

/-! ### Expectations over paths -/

variable [Fintype ι]

/-- The expectation `E_ε[φ] = ∑ₛ φ(s) P_ε(s)` of a path functional under the tilted law. -/
def pathExpect (q ω : ι → ℝ) (ε : ℝ) (φ : (Fin T → ι) → ℝ) : ℝ :=
  ∑ s, φ s * pathProb q ω ε s

/-- The expectation under the base law `ε = 0`. -/
def baseExpect (q : ι → ℝ) (φ : (Fin T → ι) → ℝ) : ℝ :=
  ∑ s, φ s * ∏ k, q (s k)

/-- The covariance under the base law. -/
def baseCov (q : ι → ℝ) (φ ψ : (Fin T → ι) → ℝ) : ℝ :=
  baseExpect q (fun s => φ s * ψ s) - baseExpect q φ * baseExpect q ψ

theorem pathExpect_zero (q ω : ι → ℝ) (φ : (Fin T → ι) → ℝ) :
    pathExpect q ω 0 φ = baseExpect q φ := by
  simp [pathExpect, baseExpect, pathProb_zero]

/-- **The score-function identity, expectation form.**
`d/dε E_ε[φ] |₀ = E_0[φ · ∑ₖ ω(sₖ)]`. -/
theorem hasDerivAt_pathExpect_score (q ω : ι → ℝ) (φ : (Fin T → ι) → ℝ) :
    HasDerivAt (fun ε => pathExpect q ω ε φ) (baseExpect q fun s => φ s * ∑ k, ω (s k)) 0 := by
  unfold pathExpect baseExpect
  refine (HasDerivAt.fun_sum fun s _ => (hasDerivAt_pathProb q ω s).const_mul (φ s)).congr_deriv ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- `∑ₛ P_ε(s) = (1 + ε ∑ᵢ q(i) ω(i))^T` when `q` is a probability law. -/
theorem sum_pathProb_eq_pow (q ω : ι → ℝ) (hq : ∑ i, q i = 1) (ε : ℝ) :
    ∑ s : Fin T → ι, pathProb q ω ε s = (1 + ε * ∑ i, q i * ω i) ^ T := by
  have hin : ∑ i, q i * (1 + ε * ω i) = 1 + ε * ∑ i, q i * ω i := by
    calc ∑ i, q i * (1 + ε * ω i) = ∑ i, (q i + ε * (q i * ω i)) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, q i + ε * ∑ i, q i * ω i := by rw [sum_add_distrib, mul_sum]
      _ = 1 + ε * ∑ i, q i * ω i := by rw [hq]
  have h := Fintype.prod_sum (fun (_ : Fin T) (i : ι) => q i * (1 + ε * ω i))
  unfold pathProb
  rw [← h, hin, prod_const, card_univ, Fintype.card_fin]

/-- The tilted law is normalised for every `ε` when `∑ᵢ q(i) ω(i) = 0`. -/
theorem sum_pathProb_eq_one (q ω : ι → ℝ) (hq : ∑ i, q i = 1) (hqω : ∑ i, q i * ω i = 0)
    (ε : ℝ) : ∑ s : Fin T → ι, pathProb q ω ε s = 1 := by
  rw [sum_pathProb_eq_pow q ω hq, hqω]
  simp

/-! ### Sample counts -/

variable [DecidableEq ι]

/-- The number of times sample `i` is drawn along the path `s`. -/
def count (i : ι) (s : Fin T → ι) : ℕ := (Finset.univ.filter fun k => s k = i).card

/-- The score regrouped by sample: `∑ₖ ω(sₖ) = ∑ᵢ ω(i) Nᵢ(s)`. -/
theorem sum_comp_eq_sum_count (ω : ι → ℝ) (s : Fin T → ι) :
    ∑ k, ω (s k) = ∑ i, ω i * (count i s : ℝ) := by
  have h := Finset.sum_fiberwise (univ : Finset (Fin T)) s (fun k => ω (s k))
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), sum_const,
    nsmul_eq_mul, mul_comm]
  rfl

/-- `d/dε E_ε[φ] |₀ = ∑ₛ φ(s) (∏ₖ q(sₖ)) ∑ᵢ ω(i) Nᵢ(s)`. -/
theorem hasDerivAt_pathExpect (q ω : ι → ℝ) (φ : (Fin T → ι) → ℝ) :
    HasDerivAt (fun ε => pathExpect q ω ε φ)
      (∑ s, φ s * ((∏ k, q (s k)) * ∑ i, ω i * (count i s : ℝ))) 0 := by
  refine (hasDerivAt_pathExpect_score q ω φ).congr_deriv ?_
  unfold baseExpect
  refine Finset.sum_congr rfl fun s _ => ?_
  beta_reduce
  rw [sum_comp_eq_sum_count]
  ring

/-- The base probability that the `k`-th draw is sample `i` is `q(i)`. -/
theorem baseExpect_indicator (q : ι → ℝ) (hq : ∑ i, q i = 1) (k : Fin T) (i : ι) :
    ∑ s : Fin T → ι, (∏ j, q (s j)) * (if s k = i then (1 : ℝ) else 0) = q i := by
  have h := Fintype.prod_sum
    (fun (j : Fin T) (x : ι) => q x * (if j = k then (if x = i then (1 : ℝ) else 0) else 1))
  have hR : ∀ s : Fin T → ι,
      ∏ j, q (s j) * (if j = k then (if s j = i then (1 : ℝ) else 0) else 1)
        = (∏ j, q (s j)) * (if s k = i then (1 : ℝ) else 0) := by
    intro s
    rw [prod_mul_distrib, Finset.prod_ite_eq' univ k (fun j => if s j = i then (1 : ℝ) else 0)]
    simp
  have hL : ∀ j : Fin T,
      ∑ x, q x * (if j = k then (if x = i then (1 : ℝ) else 0) else 1)
        = if j = k then q i else 1 := by
    intro j
    by_cases hj : j = k <;> simp [hj, hq]
  calc ∑ s : Fin T → ι, (∏ j, q (s j)) * (if s k = i then (1 : ℝ) else 0)
      = ∑ s : Fin T → ι, ∏ j, q (s j) * (if j = k then (if s j = i then (1 : ℝ) else 0) else 1) :=
        Finset.sum_congr rfl fun s _ => (hR s).symm
    _ = ∏ j, ∑ x, q x * (if j = k then (if x = i then (1 : ℝ) else 0) else 1) := h.symm
    _ = ∏ j : Fin T, (if j = k then q i else 1) := Finset.prod_congr rfl fun j _ => hL j
    _ = q i := by simp

/-- `E_0[Nᵢ] = T q(i)`. -/
theorem baseExpect_count (q : ι → ℝ) (hq : ∑ i, q i = 1) (i : ι) :
    baseExpect q (fun s : Fin T → ι => (count i s : ℝ)) = T * q i := by
  have hc : ∀ s : Fin T → ι, (count i s : ℝ) = ∑ k, if s k = i then (1 : ℝ) else 0 := by
    intro s
    simp [count]
  unfold baseExpect
  simp_rw [hc, sum_mul]
  rw [sum_comm]
  have : ∀ k : Fin T, ∑ s : Fin T → ι, (if s k = i then (1 : ℝ) else 0) * ∏ j, q (s j) = q i := by
    intro k
    rw [← baseExpect_indicator q hq k i]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  simp_rw [this]
  simp

/-! ### The covariance form -/

/-- **The score-function identity, covariance form.** For a probability law `q` and a tilt `ω`
with `∑ᵢ q(i) ω(i) = 0`,
`d/dε E_ε[φ] |₀ = ∑ᵢ ω(i) Cov_0(φ, Nᵢ)`: the response of any path functional to the resampling tilt
is the tilt contracted with the covariances of the functional and the sample counts under the base
law. -/
theorem score_deriv_eq_cov (q ω : ι → ℝ) (hq : ∑ i, q i = 1) (hqω : ∑ i, q i * ω i = 0)
    (φ : (Fin T → ι) → ℝ) :
    HasDerivAt (fun ε => pathExpect q ω ε φ)
      (∑ i, ω i * baseCov q φ (fun s => (count i s : ℝ))) 0 := by
  refine (hasDerivAt_pathExpect q ω φ).congr_deriv ?_
  have hE : ∑ i, ω i * baseExpect q (fun s : Fin T → ι => (count i s : ℝ)) = 0 := by
    simp_rw [baseExpect_count q hq]
    rw [show ∑ i, ω i * ((T : ℝ) * q i) = (T : ℝ) * ∑ i, q i * ω i by
      rw [mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hqω, mul_zero]
  have hcov : ∑ i, ω i * baseCov q φ (fun s => (count i s : ℝ))
      = ∑ i, ω i * baseExpect q (fun s => φ s * (count i s : ℝ)) := by
    simp only [baseCov, mul_sub, sum_sub_distrib]
    rw [show ∑ i, ω i * (baseExpect q φ * baseExpect q (fun s : Fin T → ι => (count i s : ℝ)))
        = baseExpect q φ * ∑ i, ω i * baseExpect q (fun s : Fin T → ι => (count i s : ℝ)) by
      rw [mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hE, mul_zero, sub_zero]
  rw [hcov]
  unfold baseExpect
  simp_rw [mul_sum]
  rw [sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The uniform base law `q ≡ 1/n` with a mean-zero tilt `∑ᵢ ω(i) = 0`: the setting of the
working note, where `h_ε = (1 + ε ω)/n`. -/
theorem score_deriv_eq_cov_uniform [Nonempty ι] (ω : ι → ℝ) (hω : ∑ i, ω i = 0)
    (φ : (Fin T → ι) → ℝ) :
    HasDerivAt (fun ε => pathExpect (fun _ => (1 : ℝ) / Fintype.card ι) ω ε φ)
      (∑ i, ω i * baseCov (fun _ => (1 : ℝ) / Fintype.card ι) φ (fun s => (count i s : ℝ))) 0 := by
  apply score_deriv_eq_cov
  · rw [sum_const, card_univ, nsmul_eq_mul, mul_one_div_cancel]
    exact_mod_cast Fintype.card_ne_zero
  · rw [← mul_sum, hω, mul_zero]

end Laplace.Patterning
