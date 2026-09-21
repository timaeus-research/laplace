/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite AR(1) chains: the second-moment structure of a sampler started at the mode

An AR(1) chain `x (k+1) = ρ • x k + η (k+1)`, `x 0 = 0`, driven by *white noise*
`⟪η j, η k⟫ = v δ_jk`, in a real inner product space `E`. With `E = L²(Ω)` and
`⟪X, Y⟫ = 𝔼[XY]` this is exactly the second-moment structure of the Langevin chain of the note
*Sanity on Sampling* along one eigendirection of the precision (`ρ = 1 - h p_i`, `v = 2h`), started
at the mode. Everything below is a statement about Gram matrices; no probability is used.

* `AR1Chain.inner_x_x`: `⟪x k, x l⟫ = v/(1-ρ²) (ρ^(l-k) - ρ^(k+l))` for `k ≤ l`.
* `AR1Chain.sum_norm_sq_window`, `AR1Chain.norm_sum_window_sq`: the window sums over the draws
  `x (b+1+i)`, `i < N`.
* `sum_sum_pow_dist`: the Toeplitz identity `∑_{i,j<N} ρ^|i-j| = N + 2 ∑_{m<N} (N-(m+1)) ρ^(m+1)`.
* `AR1Chain.pooled_sample_variance`: the note's *finite-chain prediction*, the expected pooled
  sample variance of `C` independent chains with divisor `CN`.
-/

open Finset

namespace Laplace.Sampler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An AR(1) chain in a real inner product space started at the origin and driven by white noise
of variance `v`. -/
structure AR1Chain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ v : ℝ) where
  x : ℕ → E
  η : ℕ → E
  x_zero : x 0 = 0
  step : ∀ k, x (k + 1) = ρ • x k + η (k + 1)
  white : ∀ j k, inner ℝ (η j) (η k) = if j = k then v else 0

namespace AR1Chain

variable {ρ v : ℝ} (X : AR1Chain E ρ v)

/-- Explicit form of the chain: `x k = ∑_{j < k} ρ^j • η (k - j)`. -/
theorem x_eq_sum (k : ℕ) : X.x k = ∑ j ∈ range k, ρ ^ j • X.η (k - j) := by
  induction k with
  | zero => simp [X.x_zero]
  | succ k ih =>
    rw [X.step, ih, Finset.sum_range_succ', Finset.smul_sum]
    simp only [pow_zero, one_smul, Nat.sub_zero, pow_succ, smul_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.add_sub_add_right, mul_comm]

/-- Inner products of the noise with the chain: `⟪η m, x k⟫ = ρ^(k-m) v` if `1 ≤ m ≤ k`,
else `0`. -/
theorem inner_η_x (m k : ℕ) :
    inner ℝ (X.η m) (X.x k) = if 1 ≤ m ∧ m ≤ k then ρ ^ (k - m) * v else 0 := by
  rw [X.x_eq_sum, inner_sum]
  simp_rw [real_inner_smul_right, X.white]
  split_ifs with hm
  · rw [Finset.sum_eq_single (k - m)]
    · rw [if_pos (by omega)]
    · intro j hj hne
      rw [Finset.mem_range] at hj
      rw [if_neg (by omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [if_neg (by omega), mul_zero]


/-- **Second-moment (Gram) table** for `k ≤ l`. -/
theorem inner_x_x (hρ : ρ ^ 2 ≠ 1) {k l : ℕ} (hkl : k ≤ l) :
    inner ℝ (X.x k) (X.x l) = v / (1 - ρ ^ 2) * (ρ ^ (l - k) - ρ ^ (k + l)) := by
  rw [X.x_eq_sum k, sum_inner]
  simp_rw [real_inner_smul_left, X.inner_η_x]
  have hsum : ∀ i ∈ range k,
      ρ ^ i * (if 1 ≤ k - i ∧ k - i ≤ l then ρ ^ (l - (k - i)) * v else 0) =
        v * ρ ^ (l - k) * (ρ ^ 2) ^ i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos ⟨by omega, by omega⟩, show l - (k - i) = (l - k) + i by omega, pow_add, ← pow_mul]
    ring
  rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum, geom_sum_eq hρ]
  have h1 : ρ ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hρ
  have h2 : 1 - ρ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  rw [show k + l = (l - k) + 2 * k by omega, pow_add, pow_mul]
  field_simp
  ring


/-- `‖x k‖² = v/(1-ρ²) (1 - ρ^(2k))`. -/
theorem norm_x_sq (hρ : ρ ^ 2 ≠ 1) (k : ℕ) :
    ‖X.x k‖ ^ 2 = v / (1 - ρ ^ 2) * (1 - ρ ^ (2 * k)) := by
  rw [← real_inner_self_eq_norm_sq, X.inner_x_x hρ le_rfl]
  simp only [Nat.sub_self, pow_zero, two_mul]

/-- The Gram table in the symmetric form, with `Nat.dist`. -/
theorem inner_x_x_dist (hρ : ρ ^ 2 ≠ 1) (k l : ℕ) :
    inner ℝ (X.x k) (X.x l) = v / (1 - ρ ^ 2) * (ρ ^ Nat.dist k l - ρ ^ (k + l)) := by
  rcases le_total k l with hkl | hlk
  · rw [X.inner_x_x hρ hkl, Nat.dist_eq_sub_of_le hkl]
  · rw [real_inner_comm, X.inner_x_x hρ hlk, Nat.dist_eq_sub_of_le_right hlk, add_comm]

/-! ### Window sums -/

/-- `∑_{i<N} ‖x (b+1+i)‖² = v/(1-ρ²) (N - ∑_{i<N} ρ^(2(b+1+i)))`. -/
theorem sum_norm_sq_window (hρ : ρ ^ 2 ≠ 1) (b N : ℕ) :
    ∑ i ∈ range N, ‖X.x (b + 1 + i)‖ ^ 2 =
      v / (1 - ρ ^ 2) * (N - ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i))) := by
  simp only [X.norm_x_sq hρ, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]

/-- `‖∑_{i<N} x (b+1+i)‖² = v/(1-ρ²) (∑_{i,j<N} ρ^|i-j| - (∑_{i<N} ρ^(b+1+i))²)`. -/
theorem norm_sum_window_sq (hρ : ρ ^ 2 ≠ 1) (b N : ℕ) :
    ‖∑ i ∈ range N, X.x (b + 1 + i)‖ ^ 2 =
      v / (1 - ρ ^ 2) * ((∑ i ∈ range N, ∑ j ∈ range N, ρ ^ Nat.dist i j) -
        (∑ i ∈ range N, ρ ^ (b + 1 + i)) ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, X.inner_x_x_dist hρ]
  have hdist : ∀ i j : ℕ, Nat.dist (b + 1 + i) (b + 1 + j) = Nat.dist i j := by
    intro i j; unfold Nat.dist; omega
  simp_rw [hdist]
  rw [sq (∑ i ∈ range N, ρ ^ (b + 1 + i)), Finset.sum_mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


end AR1Chain

/-! ### The Toeplitz sum -/

/-- **Toeplitz identity**: `∑_{i,j<N} ρ^|i-j| = N + 2 ∑_{m<N} (N - (m+1)) ρ^(m+1)`. -/
theorem sum_sum_pow_dist (ρ : ℝ) (N : ℕ) :
    ∑ i ∈ range N, ∑ j ∈ range N, ρ ^ Nat.dist i j =
      N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hdiag : ∀ i ∈ range N, ρ ^ Nat.dist i N = ρ ^ (N - i) := fun i hi => by
      rw [Nat.dist_eq_sub_of_le (Finset.mem_range.mp hi).le]
    have hdiag' : ∀ j ∈ range N, ρ ^ Nat.dist N j = ρ ^ (N - j) := fun j hj => by
      rw [Nat.dist_eq_sub_of_le_right (Finset.mem_range.mp hj).le]
    have hrefl : ∑ i ∈ range N, ρ ^ (N - i) = ∑ m ∈ range N, ρ ^ (m + 1) := by
      rw [← Finset.sum_range_reflect (fun m => ρ ^ (m + 1)) N]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      congr 1; omega
    have hsplit : ∑ m ∈ range N, ((N : ℝ) + 1 - (m + 1)) * ρ ^ (m + 1) =
        ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1) + ∑ m ∈ range N, ρ ^ (m + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih, Finset.sum_congr rfl hdiag, Finset.sum_congr rfl hdiag', hrefl, Nat.dist_self, pow_zero]
    push_cast
    rw [hsplit]
    ring


/-! ### Pooling independent chains -/

namespace AR1Chain

variable {ρ v : ℝ}

/-- Chains with mutually orthogonal noise have orthogonal states. -/
theorem inner_x_x_of_orthogonal (X Y : AR1Chain E ρ v)
    (h : ∀ j k, inner ℝ (X.η j) (Y.η k) = 0) (k l : ℕ) : inner ℝ (X.x k) (Y.x l) = 0 := by
  rw [X.x_eq_sum, Y.x_eq_sum, sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right, h, mul_zero, mul_zero]

/-- **The finite-chain prediction.** For `C` chains with mutually orthogonal noise and the draws
`x^c (b+1+i)`, `i < N`, the expected pooled sample variance (divisor `CN`, grand mean subtracted) is
`σ² (N - R₂)/N - σ² (T_N - R₁²)/(C N²)` with `σ² = v/(1-ρ²)`, `R₁ = ∑ ρ^(b+1+i)`,
`R₂ = ∑ ρ^(2(b+1+i))` and `T_N` the Toeplitz sum. -/
theorem pooled_sample_variance {C : ℕ} (X : Fin C → AR1Chain E ρ v)
    (hcross : ∀ c c', c ≠ c' → ∀ j k, inner ℝ ((X c).η j) ((X c').η k) = 0)
    (hρ : ρ ^ 2 ≠ 1) {N : ℕ} (hN : 0 < N) (hC : 0 < C) (b : ℕ) :
    (1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, ‖(X c).x (b + 1 + i)‖ ^ 2 -
      ‖(1 / ((C : ℝ) * N)) • ∑ c, ∑ i ∈ range N, (X c).x (b + 1 + i)‖ ^ 2 =
      v / (1 - ρ ^ 2) * (N - ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i))) / N -
        v / (1 - ρ ^ 2) * ((N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1)) -
          (∑ i ∈ range N, ρ ^ (b + 1 + i)) ^ 2) / (C * N ^ 2) := by
  set S : Fin C → E := fun c => ∑ i ∈ range N, (X c).x (b + 1 + i) with hS
  have horth : ∀ c c', c ≠ c' → inner ℝ (S c) (S c') = 0 := fun c c' hcc' => by
    simp only [hS, sum_inner, inner_sum]
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      inner_x_x_of_orthogonal (X c) (X c') (hcross c c' hcc') _ _
  have hpyth : ‖∑ c, S c‖ ^ 2 = ∑ c, ‖S c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_sum, Finset.sum_eq_single c (fun c' _ hne => horth c c' (Ne.symm hne))
      (fun h => absurd (Finset.mem_univ c) h), real_inner_self_eq_norm_sq]
  have hCN : (0 : ℝ) < (C : ℝ) * N := by positivity
  have hnorm : ‖(1 / ((C : ℝ) * N)) • ∑ c, S c‖ ^ 2 = (1 / ((C : ℝ) * N)) ^ 2 * ‖∑ c, S c‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ∑ c, ∑ i ∈ range N, ‖(X c).x (b + 1 + i)‖ ^ 2 =
      C * (v / (1 - ρ ^ 2) * (N - ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i)))) := by
    rw [Finset.sum_congr rfl fun c _ => (X c).sum_norm_sq_window hρ b N, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ∑ c, ‖S c‖ ^ 2 =
      C * (v / (1 - ρ ^ 2) * ((N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1)) -
        (∑ i ∈ range N, ρ ^ (b + 1 + i)) ^ 2)) := by
    rw [Finset.sum_congr rfl fun c _ => (X c).norm_sum_window_sq hρ b N, sum_sum_pow_dist,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hnorm, hpyth, h1, h2]
  have hC : (C : ℝ) ≠ 0 := by positivity
  have hN' : (N : ℝ) ≠ 0 := by positivity
  field_simp


end AR1Chain

end Laplace.Sampler
