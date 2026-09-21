/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Integration
import Laplace.Sampler.AR1

/-!
# The finite-chain prediction for real random variables

`Laplace/Sampler/AR1.lean` proves the note's finite-chain prediction for an AR(1) chain in an
abstract real inner product space. Here the chain is realised: `Ω` is a probability space, the
innovations `η c k : Ω → ℝ` are square-integrable with second-moment table
`∫ η c j · η c' k = v` if `(c, j) = (c', k)` and `0` otherwise, and the chains are the pointwise
recursions `x c 0 = 0`, `x c (k+1) = ρ x c k + η c (k+1)`. Packaging them into `L²(Ω)` gives an
`AR1Chain`, and the Gram theorem becomes a statement about the expectation of the pooled sample
variance of the realised chains (`expected_pooled_sample_variance`). Centred pairwise independent
innovations with variance `v` satisfy the moment table (`white_of_indep`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace Laplace.Sampler

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### `L²` identification lemmas -/

theorem inner_toLp_eq_integral {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  rw [hfω, hgω]
  simp [mul_comm]

theorem norm_toLp_sq_eq_integral {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_integral hf hf]
  simp [sq]

/-- `toLp` of a finite sum is the sum of the `toLp`s. -/
theorem toLp_finset_sum {α : Type*} (s : Finset α) (f : α → Ω → ℝ) (hf : ∀ a, MemLp (f a) 2 P) :
    (memLp_finsetSum s fun a _ => hf a).toLp (fun ω => ∑ a ∈ s, f a ω) =
      ∑ a ∈ s, (hf a).toLp (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MemLp.toLp_zero _
  | insert a s has ih =>
    simp only [Finset.sum_insert has]
    rw [← ih, ← MemLp.toLp_add]
    rfl

/-! ### The realised chain -/

variable (ρ : ℝ)

/-- The realised AR(1) chain driven by the innovations `η`, started at `0`. -/
def realChain (η : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun ω => ρ * realChain η k ω + η (k + 1) ω

omit [MeasurableSpace Ω] in
theorem realChain_zero (η : ℕ → Ω → ℝ) : realChain ρ η 0 = fun _ => 0 := rfl

omit [MeasurableSpace Ω] in
theorem realChain_succ (η : ℕ → Ω → ℝ) (k : ℕ) :
    realChain ρ η (k + 1) = fun ω => ρ * realChain ρ η k ω + η (k + 1) ω := rfl

theorem memLp_realChain {η : ℕ → Ω → ℝ} (hη : ∀ k, MemLp (η k) 2 P) (k : ℕ) :
    MemLp (realChain ρ η k) 2 P := by
  induction k with
  | zero => exact MemLp.zero
  | succ k ih => exact (ih.const_mul ρ).add (hη (k + 1))

/-- The realised chain as an `AR1Chain` in `L²(Ω)`. -/
noncomputable def toAR1Chain {v : ℝ} {η : ℕ → Ω → ℝ} (hη : ∀ k, MemLp (η k) 2 P)
    (hwhite : ∀ j k, ∫ ω, η j ω * η k ω ∂P = if j = k then v else 0) :
    AR1Chain (Lp ℝ 2 P) ρ v where
  x k := (memLp_realChain ρ hη k).toLp _
  η k := (hη k).toLp _
  x_zero := MemLp.toLp_zero _
  step k := by
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_add]
    rfl
  white j k := by rw [inner_toLp_eq_integral, hwhite]

/-! ### The expected quadratic statistic of a finite family -/

/-- For square-integrable `f a`, the expectation of `q ∑ f_a² - (q ∑ f_a)²` is the Hilbert-space
statistic of the `toLp`s. -/
theorem integral_pooled_statistic {α : Type*} (s : Finset α) (f : α → Ω → ℝ)
    (hf : ∀ a, MemLp (f a) 2 P) (q : ℝ) :
    ∫ ω, (q * ∑ a ∈ s, f a ω ^ 2 - (q * ∑ a ∈ s, f a ω) ^ 2) ∂P =
      q * ∑ a ∈ s, ‖(hf a).toLp (f a)‖ ^ 2 - ‖q • ∑ a ∈ s, (hf a).toLp (f a)‖ ^ 2 := by
  have hsq : ∀ a, Integrable (fun ω => f a ω ^ 2) P := fun a => by
    have := (hf a).integrable_mul (hf a)
    simp only [sq]
    exact this
  have hsum : MemLp (fun ω => ∑ a ∈ s, f a ω) 2 P := memLp_finsetSum s fun a _ => hf a
  have hsumsq : Integrable (fun ω => (q * ∑ a ∈ s, f a ω) ^ 2) P := by
    have := (hsum.const_mul q).integrable_mul (hsum.const_mul q)
    simp only [sq]
    exact this
  rw [integral_sub ((integrable_finsetSum s fun a _ => hsq a).const_mul q) hsumsq]
  congr 1
  · rw [integral_const_mul, integral_finsetSum s fun a _ => hsq a]
    simp only [norm_toLp_sq_eq_integral]
  · rw [← toLp_finset_sum s f hf, ← MemLp.toLp_const_smul, norm_toLp_sq_eq_integral]
    congr 1

/-! ### The finite-chain prediction as an expectation -/

/-- **Expected pooled sample variance of realised AR(1) chains.** `C` chains driven by innovations
with the white-noise moment table, draws `b+1, …, b+N`, divisor `CN`, grand mean subtracted. -/
theorem expected_pooled_sample_variance {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    {v : ℝ} (hρ : ρ ^ 2 ≠ 1) (η : Fin C → ℕ → Ω → ℝ) (hη : ∀ c k, MemLp (η c k) 2 P)
    (hwhite : ∀ c c' j k, ∫ ω, η c j ω * η c' k ω ∂P = if c = c' ∧ j = k then v else 0) :
    ∫ ω, ((1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, realChain ρ (η c) (b + 1 + i) ω ^ 2 -
        ((1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, realChain ρ (η c) (b + 1 + i) ω) ^ 2) ∂P =
      v / (1 - ρ ^ 2) * (N - ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i))) / N -
        v / (1 - ρ ^ 2) * ((N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1)) -
          (∑ i ∈ range N, ρ ^ (b + 1 + i)) ^ 2) / (C * N ^ 2) := by
  classical
  let f : Fin C × ℕ → Ω → ℝ := fun a => realChain ρ (η a.1) (b + 1 + a.2)
  have hf : ∀ a, MemLp (f a) 2 P := fun a => memLp_realChain ρ (hη a.1) _
  have hstat := integral_pooled_statistic (Finset.univ ×ˢ range N) f hf (1 / ((C : ℝ) * N))
  have h1 : ∀ ω, ∑ c, ∑ i ∈ range N, realChain ρ (η c) (b + 1 + i) ω ^ 2 =
      ∑ a ∈ Finset.univ ×ˢ range N, f a ω ^ 2 := fun ω => by rw [Finset.sum_product]
  have h2 : ∀ ω, ∑ c, ∑ i ∈ range N, realChain ρ (η c) (b + 1 + i) ω =
      ∑ a ∈ Finset.univ ×ˢ range N, f a ω := fun ω => by rw [Finset.sum_product]
  simp_rw [h1, h2]
  rw [hstat]
  have hw : ∀ c j k, ∫ ω, η c j ω * η c k ω ∂P = if j = k then v else 0 := fun c j k => by
    rw [hwhite]; simp
  let X : Fin C → AR1Chain (Lp ℝ 2 P) ρ v := fun c => toAR1Chain ρ (hη c) (hw c)
  have hcross : ∀ c c', c ≠ c' → ∀ j k, inner ℝ ((X c).η j) ((X c').η k) = 0 := by
    intro c c' hcc' j k
    change inner ℝ ((hη c j).toLp _) ((hη c' k).toLp _) = 0
    rw [inner_toLp_eq_integral, hwhite]
    simp [hcc']
  have hps := AR1Chain.pooled_sample_variance X hcross hρ hN hC b
  rw [Finset.sum_product, Finset.sum_product]
  exact hps

/-! ### White noise from independence -/

/-- Centred, pairwise independent innovations with second moment `v` have the white-noise moment
table. -/
theorem white_of_indep [IsProbabilityMeasure P] {α : Type*} [DecidableEq α] {v : ℝ}
    (η : α → Ω → ℝ)
    (hη : ∀ a, MemLp (η a) 2 P) (hmean : ∀ a, ∫ ω, η a ω ∂P = 0)
    (hvar : ∀ a, ∫ ω, η a ω ^ 2 ∂P = v) (hindep : ∀ a a', a ≠ a' → IndepFun (η a) (η a') P)
    (a a' : α) : ∫ ω, η a ω * η a' ω ∂P = if a = a' then v else 0 := by
  split_ifs with h
  · subst h; simpa [sq] using hvar a
  · have := (hindep a a' h).integral_mul_eq_mul_integral (hη a).aestronglyMeasurable
      (hη a').aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hmean, zero_mul]

end Laplace.Sampler
