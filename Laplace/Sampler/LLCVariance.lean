/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.GaussianTable
import Laplace.Sampler.LLCClosures

/-!
# The variance of the pooled LLC estimator (E4, LLC side)

The Sanity on Sampling note's E4 finds that "the LLC is far cheaper than the covariance": the
pooled covariance's relative Frobenius error follows `√(d/(CN))` (`frobenius_ula_le`) while the LLC
is within a few percent of `d/2` for every budget above `10⁴` draws. This file gives the variance
of the pooled LLC statistic on the same footing.

* `cov_pooledSecondMoment`: the cross-covariance of two entries of the pooled second-moment matrix,
  `Cov(Σ̂ᵢⱼ, Σ̂ᵢ'ⱼ') = (δᵢᵢ'δⱼⱼ' + δᵢⱼ'δⱼᵢ')/(C N²) ∑_{k,l<N} Gᵢ Gⱼ`, from the four-way Wick
  identity `cov_mul_mul_of_isLinComb`; `variance_pooledSecondMoment` is the case `i' = i, j' = j`;
* `variance_weighted_diag`: `Var(∑ᵢ wᵢ Σ̂ᵢᵢ) = 2/(C N²) ∑ᵢ wᵢ² ∑_{k,l<N} Gᵢ(k,l)²` (the diagonal
  entries are uncorrelated across directions), with the stationary envelope
  `variance_weighted_diag_le`: `≤ 2/(CN) ∑ᵢ wᵢ² s₂ᵢ² (1 + ρᵢ²)/(1 - ρᵢ²)`;
* `llc_statistic_eq_weighted_diag`: the pooled loss-based LLC statistic
  `t (1/(CN)) ∑_c ∑_k ½⟨x, Hx⟩` is `∑ᵢ (pᵢ/2) Σ̂ᵢᵢ` in the eigenbasis of `P = tH`;
* `variance_llc_ula`, `variance_llc_ula_le`: **E4 for the LLC**: on the ULA chain driven by iid
  standard Gaussians, with `0 < h pᵢ ≤ 1`, `Var(LLĈ) = 1/(2 C N²) ∑ᵢ pᵢ² ∑_{k,l} Hᵢ(k,l)²` and
  `Var(LLĈ) ≤ 1/(2CN) ∑ᵢ (1 + ρᵢ²)/((1 - ρᵢ²)(1 - h pᵢ/2)²)`, `ρᵢ = 1 - h pᵢ`;
* `llc_vs_frobenius_isotropic`: for an isotropic spectrum the LLC bound relative to the stationary
  LLC mean squared is `2/(d(d+1))` times the Frobenius bound relative to the stationary Frobenius
  norm squared: "the LLC is far cheaper than the covariance".
-/

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Laplace.Sampler

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **The covariance of two weighted sums** as a double sum of covariances. -/
theorem cov_sum_eq_sum_cov {α : Type*} (s : Finset α) (f f' : α → Ω → ℝ)
    (h1 : ∀ a ∈ s, Integrable (f a) P) (h1' : ∀ a ∈ s, Integrable (f' a) P)
    (h2 : ∀ a ∈ s, ∀ b ∈ s, Integrable (fun ω => f a ω * f' b ω) P) (q : ℝ) :
    ∫ ω, (q * ∑ a ∈ s, f a ω) * (q * ∑ a ∈ s, f' a ω) ∂P -
        (∫ ω, q * ∑ a ∈ s, f a ω ∂P) * ∫ ω, q * ∑ a ∈ s, f' a ω ∂P =
      q ^ 2 * ∑ a ∈ s, ∑ b ∈ s,
        (∫ ω, f a ω * f' b ω ∂P - (∫ ω, f a ω ∂P) * ∫ ω, f' b ω ∂P) := by
  have hsq : ∀ ω, (q * ∑ a ∈ s, f a ω) * (q * ∑ a ∈ s, f' a ω) =
      q ^ 2 * ∑ a ∈ s, ∑ b ∈ s, f a ω * f' b ω := by
    intro ω
    rw [mul_mul_mul_comm, Finset.sum_mul_sum, ← sq]
  simp_rw [hsq]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun a ha => h1 a ha, integral_finsetSum _ fun a ha => h1' a ha,
    integral_finsetSum _ fun a ha => integrable_finsetSum _ fun b hb => h2 a ha b hb,
    Finset.sum_congr rfl fun a ha => integral_finsetSum _ fun b hb => h2 a ha b hb]
  have key : ∀ (I : α → α → ℝ) (m m' : α → ℝ),
      ∑ a ∈ s, ∑ b ∈ s, (I a b - m a * m' b) =
        ∑ a ∈ s, ∑ b ∈ s, I a b - (∑ a ∈ s, m a) * ∑ b ∈ s, m' b := by
    intro I m m'
    rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
  rw [key]
  ring

variable {κ : Type*} {g : κ → Ω → ℝ} {v : ℝ}

omit [IsProbabilityMeasure P] in
theorem integrable_pooledSecondMoment_mul {ι : Type*} {C : ℕ} {x : Fin C → ι → ℕ → Ω → ℝ}
    {N b : ℕ} (hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P) (i j i' j' : ι) :
    Integrable (fun ω => pooledSecondMoment x N b i j ω * pooledSecondMoment x N b i' j' ω) P := by
  have hsum : ∀ i j ω, pooledSecondMoment x N b i j ω =
      (1 / ((C : ℝ) * N)) * ∑ a ∈ (univ : Finset (Fin C)) ×ˢ range N,
        x a.1 i (b + 1 + a.2) ω * x a.1 j (b + 1 + a.2) ω := fun i j ω => by
    rw [pooledSecondMoment, Finset.sum_product]
  have hmul : ∀ ω, pooledSecondMoment x N b i j ω * pooledSecondMoment x N b i' j' ω =
      (1 / ((C : ℝ) * N)) ^ 2 *
      ∑ a ∈ (univ : Finset (Fin C)) ×ˢ range N, ∑ a' ∈ (univ : Finset (Fin C)) ×ˢ range N,
        x a.1 i (b + 1 + a.2) ω * x a.1 j (b + 1 + a.2) ω *
          (x a'.1 i' (b + 1 + a'.2) ω * x a'.1 j' (b + 1 + a'.2) ω) := by
    intro ω
    rw [hsum i j ω, hsum i' j' ω, mul_mul_mul_comm, Finset.sum_mul_sum, ← sq]
  simp_rw [hmul]
  refine (integrable_finsetSum _ fun a ha => integrable_finsetSum _ fun a' ha' => ?_).const_mul _
  have hk := (Finset.mem_product.mp ha).2
  have hk' := (Finset.mem_product.mp ha').2
  exact integrable_mul_mul_mul_of_memLp_four (hL4 _ _ _ hk) (hL4 _ _ _ hk) (hL4 _ _ _ hk')
    (hL4 _ _ _ hk')

/-- The two Wick pairings of `E[x_i x_j · x_i' x_j']` collapse to the delta pattern
`δᵢᵢ'δⱼⱼ' + δᵢⱼ'δⱼᵢ'`. -/
theorem ite_pair_expand {ι : Type*} [DecidableEq ι] (i j i' j' : ι) (A B : ℝ) :
    (if i = i' then A else 0) * (if j = j' then B else 0) +
        (if i = j' then A else 0) * (if j = i' then B else 0) =
      ((if i = i' ∧ j = j' then 1 else 0) + (if i = j' ∧ j = i' then 1 else 0)) * (A * B) := by
  split_ifs <;> (simp_all; try ring)

/-- **The cross-covariance of two entries of the pooled second-moment matrix.** For chains that
are linear combinations of a `FourthMomentTable` family with the Gram table
`E[x^c_i(k) x^{c'}_j(l)] = δ_{cc'} δ_{ij} Gᵢ(k,l)`,
`Cov(Σ̂ᵢⱼ, Σ̂ᵢ'ⱼ') = (δᵢᵢ'δⱼⱼ' + δᵢⱼ'δⱼᵢ')/(C N²) ∑_{k,l<N} Gᵢ(b+1+k, b+1+l) Gⱼ(b+1+k, b+1+l)`. -/
theorem cov_pooledSecondMoment {ι : Type*} [DecidableEq ι] (hT : FourthMomentTable g P v)
    {s : Finset κ} {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (x : Fin C → ι → ℕ → Ω → ℝ) (hx : ∀ c i k, k ∈ range N → IsLinComb g s (x c i (b + 1 + k)))
    (G : ι → ℕ → ℕ → ℝ)
    (hG : ∀ c c' i j k l, ∫ ω, x c i k ω * x c' j l ω ∂P = if c = c' ∧ i = j then G i k l else 0)
    (i j i' j' : ι) :
    ∫ ω, pooledSecondMoment x N b i j ω * pooledSecondMoment x N b i' j' ω ∂P -
        (∫ ω, pooledSecondMoment x N b i j ω ∂P) * ∫ ω, pooledSecondMoment x N b i' j' ω ∂P =
      ((if i = i' ∧ j = j' then 1 else 0) + (if i = j' ∧ j = i' then 1 else 0)) / (C * N ^ 2) *
        ∑ k ∈ range N, ∑ l ∈ range N,
          G i (b + 1 + k) (b + 1 + l) * G j (b + 1 + k) (b + 1 + l) := by
  have hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P :=
    fun c i k hk => memLp_of_isLinComb hT.memLp (hx c i k hk)
  set f : Fin C × ℕ → Ω → ℝ := fun a ω => x a.1 i (b + 1 + a.2) ω * x a.1 j (b + 1 + a.2) ω
    with hf
  set f' : Fin C × ℕ → Ω → ℝ := fun a ω => x a.1 i' (b + 1 + a.2) ω * x a.1 j' (b + 1 + a.2) ω
    with hf'
  have hsum : ∀ ω, pooledSecondMoment x N b i j ω =
      (1 / ((C : ℝ) * N)) * ∑ a ∈ (univ : Finset (Fin C)) ×ˢ range N, f a ω := fun ω => by
    rw [pooledSecondMoment, Finset.sum_product]
  have hsum' : ∀ ω, pooledSecondMoment x N b i' j' ω =
      (1 / ((C : ℝ) * N)) * ∑ a ∈ (univ : Finset (Fin C)) ×ˢ range N, f' a ω := fun ω => by
    rw [pooledSecondMoment, Finset.sum_product]
  simp_rw [hsum, hsum']
  rw [cov_sum_eq_sum_cov _ f f'
    (fun a ha => integrable_mul_of_memLp_four (hL4 _ _ _ (Finset.mem_product.mp ha).2)
      (hL4 _ _ _ (Finset.mem_product.mp ha).2))
    (fun a ha => integrable_mul_of_memLp_four (hL4 _ _ _ (Finset.mem_product.mp ha).2)
      (hL4 _ _ _ (Finset.mem_product.mp ha).2))
    (fun a ha a' ha' => integrable_mul_mul_mul_of_memLp_four
      (hL4 _ _ _ (Finset.mem_product.mp ha).2) (hL4 _ _ _ (Finset.mem_product.mp ha).2)
      (hL4 _ _ _ (Finset.mem_product.mp ha').2) (hL4 _ _ _ (Finset.mem_product.mp ha').2))]
  have hcov : ∀ a ∈ (univ : Finset (Fin C)) ×ˢ range N, ∀ a' ∈ (univ : Finset (Fin C)) ×ˢ range N,
      ∫ ω, f a ω * f' a' ω ∂P - (∫ ω, f a ω ∂P) * ∫ ω, f' a' ω ∂P =
        if a.1 = a'.1 then
          ((if i = i' ∧ j = j' then 1 else 0) + (if i = j' ∧ j = i' then 1 else 0)) *
            (G i (b + 1 + a.2) (b + 1 + a'.2) * G j (b + 1 + a.2) (b + 1 + a'.2))
        else 0 := by
    intro a ha a' ha'
    have hk := (Finset.mem_product.mp ha).2
    have hk' := (Finset.mem_product.mp ha').2
    rw [hf, hf']
    dsimp only
    rw [cov_mul_mul_of_isLinComb hT (hx _ _ _ hk) (hx _ _ _ hk) (hx _ _ _ hk') (hx _ _ _ hk'),
      hG, hG, hG, hG]
    by_cases hc : a.1 = a'.1
    · simp only [hc, true_and, if_true]
      exact ite_pair_expand i j i' j' _ _
    · simp only [hc, false_and, if_false, mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun a' ha' => hcov a ha a' ha']
  simp_rw [Finset.sum_product_right (s := (univ : Finset (Fin C))) (t := range N)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **The variance of a weighted diagonal statistic** `∑ᵢ wᵢ Σ̂ᵢᵢ` (the pooled LLC once
`wᵢ = pᵢ/2`): the diagonal entries are uncorrelated across directions, so
`Var(∑ᵢ wᵢ Σ̂ᵢᵢ) = 2/(C N²) ∑ᵢ wᵢ² ∑_{k,l<N} Gᵢ(b+1+k, b+1+l)²`. -/
theorem variance_weighted_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hT : FourthMomentTable g P v) {s : Finset κ} {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (x : Fin C → ι → ℕ → Ω → ℝ)
    (hx : ∀ c i k, k ∈ range N → IsLinComb g s (x c i (b + 1 + k))) (G : ι → ℕ → ℕ → ℝ)
    (hG : ∀ c c' i j k l, ∫ ω, x c i k ω * x c' j l ω ∂P = if c = c' ∧ i = j then G i k l else 0)
    (w : ι → ℝ) :
    ∫ ω, (∑ i, w i * pooledSecondMoment x N b i i ω) ^ 2 ∂P -
        (∫ ω, ∑ i, w i * pooledSecondMoment x N b i i ω ∂P) ^ 2 =
      2 / (C * N ^ 2) * ∑ i, w i ^ 2 *
        ∑ k ∈ range N, ∑ l ∈ range N, G i (b + 1 + k) (b + 1 + l) ^ 2 := by
  have hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P :=
    fun c i k hk => memLp_of_isLinComb hT.memLp (hx c i k hk)
  have h1 : ∀ i ∈ (univ : Finset ι),
      Integrable (fun ω => w i * pooledSecondMoment x N b i i ω) P :=
    fun i _ => (integrable_pooledSecondMoment hL4 i i).const_mul _
  have h2 : ∀ i ∈ (univ : Finset ι), ∀ j ∈ (univ : Finset ι), Integrable
      (fun ω => (w i * pooledSecondMoment x N b i i ω) * (w j * pooledSecondMoment x N b j j ω))
      P := by
    intro i _ j _
    have hI : Integrable (fun ω => (w i * w j) *
        (pooledSecondMoment x N b i i ω * pooledSecondMoment x N b j j ω)) P :=
      (integrable_pooledSecondMoment_mul hL4 i i j j).const_mul _
    refine hI.congr (ae_of_all _ fun ω => ?_)
    ring
  have hvar := variance_sum_eq_sum_cov univ (fun i ω => w i * pooledSecondMoment x N b i i ω)
    h1 h2 1
  simp only [one_mul, one_pow] at hvar
  rw [hvar]
  have hcov : ∀ i j : ι,
      ∫ ω, (w i * pooledSecondMoment x N b i i ω) * (w j * pooledSecondMoment x N b j j ω) ∂P -
        (∫ ω, w i * pooledSecondMoment x N b i i ω ∂P) *
          ∫ ω, w j * pooledSecondMoment x N b j j ω ∂P =
      if i = j then 2 / (C * N ^ 2) *
        (w i ^ 2 * ∑ k ∈ range N, ∑ l ∈ range N, G i (b + 1 + k) (b + 1 + l) ^ 2) else 0 := by
    intro i j
    have hprod : (fun ω => (w i * pooledSecondMoment x N b i i ω) *
        (w j * pooledSecondMoment x N b j j ω)) =
        fun ω => (w i * w j) *
          (pooledSecondMoment x N b i i ω * pooledSecondMoment x N b j j ω) := by
      funext ω
      ring
    rw [hprod, integral_const_mul, integral_const_mul, integral_const_mul]
    have hfac : (w i * w j) *
        (∫ ω, pooledSecondMoment x N b i i ω * pooledSecondMoment x N b j j ω ∂P) -
        (w i * ∫ ω, pooledSecondMoment x N b i i ω ∂P) *
          (w j * ∫ ω, pooledSecondMoment x N b j j ω ∂P) =
        (w i * w j) * (∫ ω, pooledSecondMoment x N b i i ω * pooledSecondMoment x N b j j ω ∂P -
          (∫ ω, pooledSecondMoment x N b i i ω ∂P) * ∫ ω, pooledSecondMoment x N b j j ω ∂P) := by
      ring
    rw [hfac, cov_pooledSecondMoment hT hC hN b x hx G hG i i j j]
    by_cases hij : i = j
    · subst hij
      simp only [and_self, if_true, ← sq]
      ring
    · simp [hij]
  simp_rw [hcov]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]

/-- The squared zero-start AR(1) Gram kernel summed over a window of `N` draws is bounded by the
stationary autocorrelation time of the *squared* chain:
`∑_{k,l<N} (s₂ (ρ^{|k-l|} - ρ^{k+l}))² ≤ s₂² N (1 + ρ²)/(1 - ρ²)`. -/
theorem gram_sq_sum_le {ρ s₂ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (b N : ℕ) :
    ∑ k ∈ range N, ∑ l ∈ range N,
        (s₂ * (ρ ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ ^ (b + 1 + k + (b + 1 + l)))) ^ 2 ≤
      s₂ ^ 2 * (N * (1 + ρ ^ 2) / (1 - ρ ^ 2)) := by
  have hρ20 : 0 ≤ ρ ^ 2 := by positivity
  have hρ21 : ρ ^ 2 < 1 := by nlinarith
  have hterm : ∀ k ∈ range N, ∀ l ∈ range N,
      (s₂ * (ρ ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ ^ (b + 1 + k + (b + 1 + l)))) ^ 2 ≤
        s₂ ^ 2 * (ρ ^ 2) ^ Nat.dist k l := by
    intro k _ l _
    have hd : Nat.dist (b + 1 + k) (b + 1 + l) = Nat.dist k l := by unfold Nat.dist; omega
    have hdle : Nat.dist k l ≤ b + 1 + k + (b + 1 + l) := by unfold Nat.dist; omega
    have hle : ρ ^ (b + 1 + k + (b + 1 + l)) ≤ ρ ^ Nat.dist k l :=
      pow_le_pow_of_le_one hρ0 hρ1.le hdle
    have h0 : 0 ≤ ρ ^ Nat.dist k l - ρ ^ (b + 1 + k + (b + 1 + l)) := by linarith
    have h1 : ρ ^ Nat.dist k l - ρ ^ (b + 1 + k + (b + 1 + l)) ≤ ρ ^ Nat.dist k l := by
      linarith [pow_nonneg hρ0 (b + 1 + k + (b + 1 + l))]
    rw [hd, mul_pow, ← pow_mul, mul_comm 2, pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) (by positivity)
  calc _ ≤ ∑ k ∈ range N, ∑ l ∈ range N, s₂ ^ 2 * (ρ ^ 2) ^ Nat.dist k l :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hterm k hk l hl
    _ = s₂ ^ 2 * ∑ k ∈ range N, ∑ l ∈ range N, (ρ ^ 2) ^ Nat.dist k l := by
        simp_rw [Finset.mul_sum]
    _ = s₂ ^ 2 * (N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * (ρ ^ 2) ^ (m + 1)) := by
        rw [sum_sum_pow_dist]
    _ ≤ s₂ ^ 2 * (N * (1 + ρ ^ 2) / (1 - ρ ^ 2)) :=
        mul_le_mul_of_nonneg_left (toeplitz_sum_le hρ20 hρ21 N) (by positivity)

/-- **The stationary envelope of the weighted-diagonal variance.** With AR(1) Gram tables
`Gᵢ(k,l) = s₂ᵢ (ρᵢ^{|k-l|} - ρᵢ^{k+l})`, `0 ≤ ρᵢ < 1`,
`Var(∑ᵢ wᵢ Σ̂ᵢᵢ) ≤ 2/(CN) ∑ᵢ wᵢ² s₂ᵢ² (1 + ρᵢ²)/(1 - ρᵢ²)`. -/
theorem variance_weighted_diag_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hT : FourthMomentTable g P v) {s : Finset κ} {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (x : Fin C → ι → ℕ → Ω → ℝ)
    (hx : ∀ c i k, k ∈ range N → IsLinComb g s (x c i (b + 1 + k)))
    (ρ s₂ : ι → ℝ) (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i < 1)
    (hG : ∀ c c' i j k l, ∫ ω, x c i k ω * x c' j l ω ∂P =
      if c = c' ∧ i = j then s₂ i * (ρ i ^ Nat.dist k l - ρ i ^ (k + l)) else 0)
    (w : ι → ℝ) :
    ∫ ω, (∑ i, w i * pooledSecondMoment x N b i i ω) ^ 2 ∂P -
        (∫ ω, ∑ i, w i * pooledSecondMoment x N b i i ω ∂P) ^ 2 ≤
      2 / (C * N) * ∑ i, w i ^ 2 * (s₂ i ^ 2 * (1 + ρ i ^ 2) / (1 - ρ i ^ 2)) := by
  rw [variance_weighted_diag hT hC hN b x hx _ hG w]
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoef : (0 : ℝ) ≤ 2 / (C * N ^ 2) := by positivity
  calc 2 / (C * N ^ 2) * ∑ i, w i ^ 2 * ∑ k ∈ range N, ∑ l ∈ range N,
        (s₂ i * (ρ i ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ i ^ (b + 1 + k + (b + 1 + l)))) ^ 2
      ≤ 2 / (C * N ^ 2) * ∑ i, w i ^ 2 * (s₂ i ^ 2 * (N * (1 + ρ i ^ 2) / (1 - ρ i ^ 2))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (gram_sq_sum_le (hρ0 i) (hρ1 i) b N)
            (by positivity)) hcoef
    _ = 2 / (C * N) * ∑ i, w i ^ 2 * (s₂ i ^ 2 * (1 + ρ i ^ 2) / (1 - ρ i ^ 2)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp

end Abstract

/-! ### Realised chains along several directions -/

section Realised

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ℕ}

omit [DecidableEq ι] in
/-- **The weighted-diagonal variance of realised multi-direction chains** driven by a
`FourthMomentTable` family of innovations:
`Var(∑ᵢ wᵢ Σ̂ᵢᵢ) ≤ 2/(CN) ∑ᵢ wᵢ² (v/(1 - ρᵢ²))² (1 + ρᵢ²)/(1 - ρᵢ²)`. -/
theorem variance_weighted_diag_realChain_le (η : Fin C → ℕ → ι → Ω → ℝ) {v : ℝ}
    (hT : FourthMomentTable (fun a : Fin C × ℕ × ι => η a.1 a.2.1 a.2.2) P v)
    (ρ : ι → ℝ) (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i < 1) (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (w : ι → ℝ) :
    ∫ ω, (∑ i, w i *
        pooledSecondMoment (fun c i k => realChain (ρ i) (fun m => η c m i) k) N b i i ω) ^ 2 ∂P -
      (∫ ω, ∑ i, w i *
        pooledSecondMoment (fun c i k => realChain (ρ i) (fun m => η c m i) k) N b i i ω ∂P) ^ 2
      ≤ 2 / (C * N) * ∑ i, w i ^ 2 * ((v / (1 - ρ i ^ 2)) ^ 2 * (1 + ρ i ^ 2) / (1 - ρ i ^ 2)) := by
  classical
  have hρ : ∀ i, ρ i ^ 2 ≠ 1 := fun i => by nlinarith [hρ0 i, hρ1 i]
  have hwhite : ∀ c c' k l i j, ∫ ω, η c k i ω * η c' l j ω ∂P =
      if c = c' ∧ k = l ∧ i = j then v else 0 := fun c c' k l i j => by
    simpa [Prod.ext_iff] using hT.white (c, k, i) (c', l, j)
  refine variance_weighted_diag_le hT (s := (univ : Finset (Fin C)) ×ˢ range (b + N + 1) ×ˢ
    (univ : Finset ι)) hC hN b _ (fun c i k hk => ?_) ρ (fun i => v / (1 - ρ i ^ 2)) hρ0 hρ1
    (fun c c' i j k l => ?_) w
  · exact isLinComb_realChain_dir (ρ i) η c i (b + N) (b + 1 + k)
      (by have := Finset.mem_range.mp hk; omega)
  · exact gram_realChain_dir η ρ hρ (fun c k i => (hT.memLp (c, k, i)).mono_exponent (by norm_num))
      hwhite c c' i j k l

omit [DecidableEq ι] in
/-- **The exact weighted-diagonal variance of realised chains**:
`Var(∑ᵢ wᵢ Σ̂ᵢᵢ) = 2/(C N²) ∑ᵢ wᵢ² ∑_{k,l<N} (s₂ᵢ (ρᵢ^{|k-l|} - ρᵢ^{k+l}))²` at the window times. -/
theorem variance_weighted_diag_realChain (η : Fin C → ℕ → ι → Ω → ℝ) {v : ℝ}
    (hT : FourthMomentTable (fun a : Fin C × ℕ × ι => η a.1 a.2.1 a.2.2) P v)
    (ρ : ι → ℝ) (hρ : ∀ i, ρ i ^ 2 ≠ 1) (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ) (w : ι → ℝ) :
    ∫ ω, (∑ i, w i *
        pooledSecondMoment (fun c i k => realChain (ρ i) (fun m => η c m i) k) N b i i ω) ^ 2 ∂P -
      (∫ ω, ∑ i, w i *
        pooledSecondMoment (fun c i k => realChain (ρ i) (fun m => η c m i) k) N b i i ω ∂P) ^ 2
      = 2 / (C * N ^ 2) * ∑ i, w i ^ 2 * ∑ k ∈ range N, ∑ l ∈ range N,
          (v / (1 - ρ i ^ 2) *
            (ρ i ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ i ^ (b + 1 + k + (b + 1 + l)))) ^ 2 := by
  classical
  have hwhite : ∀ c c' k l i j, ∫ ω, η c k i ω * η c' l j ω ∂P =
      if c = c' ∧ k = l ∧ i = j then v else 0 := fun c c' k l i j => by
    simpa [Prod.ext_iff] using hT.white (c, k, i) (c', l, j)
  refine variance_weighted_diag hT (s := (univ : Finset (Fin C)) ×ˢ range (b + N + 1) ×ˢ
    (univ : Finset ι)) hC hN b _ (fun c i k hk => ?_)
    (fun i k l => v / (1 - ρ i ^ 2) * (ρ i ^ Nat.dist k l - ρ i ^ (k + l)))
    (fun c c' i j k l => ?_) w
  · exact isLinComb_realChain_dir (ρ i) η c i (b + N) (b + 1 + k)
      (by have := Finset.mem_range.mp hk; omega)
  · exact gram_realChain_dir η ρ hρ (fun c k i => (hT.memLp (c, k, i)).mono_exponent (by norm_num))
      hwhite c c' i j k l

end Realised

/-! ### The ULA chain -/

section Statistic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}

/-- **The pooled loss-based LLC statistic is a weighted diagonal statistic**: in the eigenbasis of
`P = tH`, `t (1/(CN)) ∑_c ∑_{k<N} ½⟨x, H x⟩ = ∑ᵢ (pᵢ/2) Σ̂ᵢᵢ`. -/
theorem llc_statistic_eq_weighted_diag {H : Matrix ι ι ℝ} {t : ℝ} (ht : 0 < t)
    (hP : (t • H).PosDef) {C : ℕ} (N b : ℕ) (y : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (ω : Ω) :
    t * ((1 / ((C : ℝ) * N)) * ∑ c, ∑ k ∈ range N,
        1 / 2 * inner ℝ (y c (b + 1 + k) ω) (euclid H (y c (b + 1 + k) ω))) =
      ∑ i, hP.1.eigenvalues i / 2 *
        pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hP.1 i) (y c k ω)) N b i i ω := by
  simp_rw [half_inner_euclid_eq_sum_eigen ht hP]
  have key : ∑ c, ∑ k ∈ range N, ∑ i, 1 / (2 * t) * hP.1.eigenvalues i *
        inner ℝ (orthoCol hP.1 i) (y c (b + 1 + k) ω) ^ 2 =
      ∑ i, ∑ c, ∑ k ∈ range N, 1 / (2 * t) * hP.1.eigenvalues i *
        inner ℝ (orthoCol hP.1 i) (y c (b + 1 + k) ω) ^ 2 := by
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]
    exact Finset.sum_comm
  rw [key]
  simp_rw [pooledSecondMoment, Finset.mul_sum, ← sq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun k _ => ?_
  field_simp

end Statistic

section ULA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **E4 for the LLC, exact.** On the ULA chain for `P = tH` driven by iid standard Gaussians,
`Var(t (1/(CN)) ∑_c ∑_k ½⟨x, Hx⟩) = 1/(2 C N²) ∑ᵢ pᵢ² ∑_{k,l<N} Hᵢ(b+1+k, b+1+l)²` with
`Hᵢ(k,l) = 2h/(1 - ρᵢ²) (ρᵢ^{|k-l|} - ρᵢ^{k+l})`, `ρᵢ = 1 - h pᵢ`. -/
theorem variance_llc_ula {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hev : ∀ i, h * hP.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, (t * ((1 / ((C : ℝ) * N)) * ∑ c, ∑ k ∈ range N, 1 / 2 *
        inner ℝ (ulaChain (t • H) h (ξ c) (b + 1 + k) ω)
          (euclid H (ulaChain (t • H) h (ξ c) (b + 1 + k) ω)))) ^ 2 ∂P -
      (∫ ω, t * ((1 / ((C : ℝ) * N)) * ∑ c, ∑ k ∈ range N, 1 / 2 *
        inner ℝ (ulaChain (t • H) h (ξ c) (b + 1 + k) ω)
          (euclid H (ulaChain (t • H) h (ξ c) (b + 1 + k) ω))) ∂P) ^ 2 =
      1 / (2 * C * N ^ 2) * ∑ i, hP.1.eigenvalues i ^ 2 * ∑ k ∈ range N, ∑ l ∈ range N,
        (2 * h / (1 - (1 - h * hP.1.eigenvalues i) ^ 2) *
          ((1 - h * hP.1.eigenvalues i) ^ Nat.dist (b + 1 + k) (b + 1 + l) -
            (1 - h * hP.1.eigenvalues i) ^ (b + 1 + k + (b + 1 + l)))) ^ 2 := by
  have hPt : (t • H)ᵀ = t • H := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  simp_rw [llc_statistic_eq_weighted_diag ht hP N b (fun c k => ulaChain (t • H) h (ξ c) k)]
  have hx : (fun c i k ω => inner ℝ (orthoCol hP.1 i) (ulaChain (t • H) h (ξ c) k ω)) =
      fun c i k => realChain (1 - h * hP.1.eigenvalues i)
        (fun m => projNoise h (orthoCol hP.1 i) (ξ c) m) k := by
    funext c i k ω
    exact inner_ulaChain_eq_realChain hPt h (mulVec_orthoCol hP.1 i) (ξ c) k ω
  rw [hx, variance_weighted_diag_realChain (fun c k i => projNoise h (orthoCol hP.1 i) (ξ c) k)
    (fourthMomentTable_projNoise_dir hh.le (orthonormal_orthoCol hP.1) ξ hmeas hlaw hind)
    (fun i => 1 - h * hP.1.eigenvalues i)
    (fun i => by
      have hp := hP.eigenvalues_pos i
      have hhp := hev i
      intro heq
      nlinarith [mul_pos hh hp])
    hC hN b (fun i => hP.1.eigenvalues i / 2)]
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- **E4 for the LLC, envelope.** With `0 < h pᵢ ≤ 1`,
`Var(t (1/(CN)) ∑_c ∑_k ½⟨x, Hx⟩) ≤ 1/(2CN) ∑ᵢ (1 + ρᵢ²)/((1 - ρᵢ²)(1 - h pᵢ/2)²)`,
`ρᵢ = 1 - h pᵢ`: the LLC's Monte Carlo error is `O(√(d/(CN)))` with the autocorrelation times of
the squared coordinates as prefactor, and no `d²` from off-diagonal entries. -/
theorem variance_llc_ula_le {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hstab : ∀ i, h * hP.1.eigenvalues i ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, (t * ((1 / ((C : ℝ) * N)) * ∑ c, ∑ k ∈ range N, 1 / 2 *
        inner ℝ (ulaChain (t • H) h (ξ c) (b + 1 + k) ω)
          (euclid H (ulaChain (t • H) h (ξ c) (b + 1 + k) ω)))) ^ 2 ∂P -
      (∫ ω, t * ((1 / ((C : ℝ) * N)) * ∑ c, ∑ k ∈ range N, 1 / 2 *
        inner ℝ (ulaChain (t • H) h (ξ c) (b + 1 + k) ω)
          (euclid H (ulaChain (t • H) h (ξ c) (b + 1 + k) ω))) ∂P) ^ 2 ≤
      1 / (2 * C * N) * ∑ i, (1 + (1 - h * hP.1.eigenvalues i) ^ 2) /
        ((1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2) ^ 2) := by
  have hPt : (t • H)ᵀ = t • H := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  simp_rw [llc_statistic_eq_weighted_diag ht hP N b (fun c k => ulaChain (t • H) h (ξ c) k)]
  have hx : (fun c i k ω => inner ℝ (orthoCol hP.1 i) (ulaChain (t • H) h (ξ c) k ω)) =
      fun c i k => realChain (1 - h * hP.1.eigenvalues i)
        (fun m => projNoise h (orthoCol hP.1 i) (ξ c) m) k := by
    funext c i k ω
    exact inner_ulaChain_eq_realChain hPt h (mulVec_orthoCol hP.1 i) (ξ c) k ω
  rw [hx]
  refine le_trans (variance_weighted_diag_realChain_le
    (fun c k i => projNoise h (orthoCol hP.1 i) (ξ c) k)
    (fourthMomentTable_projNoise_dir hh.le (orthonormal_orthoCol hP.1) ξ hmeas hlaw hind)
    (fun i => 1 - h * hP.1.eigenvalues i) (fun i => by linarith [hstab i])
    (fun i => by nlinarith [mul_pos hh (hP.eigenvalues_pos i)]) hC hN b
    (fun i => hP.1.eigenvalues i / 2)) (le_of_eq ?_)
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp := hP.eigenvalues_pos i
  have hhp := hstab i
  rw [ula_variance_eq hh hp (by linarith)]
  have hne1 : 1 - (1 - h * hP.1.eigenvalues i) ^ 2 ≠ 0 := by nlinarith [mul_pos hh hp]
  have hne2 : 1 - h * hP.1.eigenvalues i / 2 ≠ 0 := by linarith
  field_simp

end ULA

/-! ### "The LLC is far cheaper than the covariance" -/

section Isotropic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑ᵢ ∑ⱼ (1 + δᵢⱼ) = d² + d`. -/
theorem sum_sum_ite_two_one :
    ∑ i : ι, ∑ j : ι, (if i = j then (2 : ℝ) else 1) =
      (Fintype.card ι : ℝ) ^ 2 + Fintype.card ι := by
  have hinner : ∀ i : ι, ∑ j : ι, (if i = j then (2 : ℝ) else 1) = Fintype.card ι + 1 := by
    intro i
    have : ∀ j : ι, (if i = j then (2 : ℝ) else 1) = 1 + if i = j then 1 else 0 := fun j => by
      split_ifs <;> norm_num
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **"The LLC is far cheaper than the covariance."** For an isotropic spectrum `pᵢ = p` with
`0 < hp ≤ 1`, the E4 LLC-variance bound (`variance_llc_ula_le`) divided by the square of the
stationary ULA LLC `½ ∑ᵢ 1/(1 - hp/2)` (`ula_llc`) is exactly `2/(d(d+1))` times the E4 Frobenius
bound (`frobenius_ula_le`) divided by the stationary Frobenius norm `∑ᵢ s₂ᵢ²` of the ULA
covariance: the relative LLC variance is `2τ/(d·CN)` against `(d+1)τ/(CN)` for the covariance. -/
theorem llc_vs_frobenius_isotropic [Nonempty ι] {C N h p : ℝ} (hC : 0 < C) (hN : 0 < N)
    (hh : 0 < h) (hp : 0 < p) (hhp : h * p ≤ 1) :
    (1 / (2 * C * N) * ∑ _i : ι, (1 + (1 - h * p) ^ 2) /
          ((1 - (1 - h * p) ^ 2) * (1 - h * p / 2) ^ 2)) /
        (1 / 2 * ∑ _i : ι, 1 / (1 - h * p / 2)) ^ 2 =
      2 / (Fintype.card ι * (Fintype.card ι + 1)) *
        ((∑ i : ι, ∑ j : ι, (if i = j then 2 else 1) / (C * N) *
            (2 * h / (1 - (1 - h * p) ^ 2) * (2 * h / (1 - (1 - h * p) ^ 2)) *
              (1 + (1 - h * p) * (1 - h * p)) / (1 - (1 - h * p) * (1 - h * p)))) /
          ∑ _i : ι, (2 * h / (1 - (1 - h * p) ^ 2)) ^ 2) := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hρ : 1 - (1 - h * p) ^ 2 ≠ 0 := by nlinarith [mul_pos hh hp]
  have hq : 1 - h * p / 2 ≠ 0 := by linarith
  have hsum : ∑ i : ι, ∑ j : ι, (if i = j then (2 : ℝ) else 1) / (C * N) *
      (2 * h / (1 - (1 - h * p) ^ 2) * (2 * h / (1 - (1 - h * p) ^ 2)) *
        (1 + (1 - h * p) * (1 - h * p)) / (1 - (1 - h * p) * (1 - h * p))) =
      ((Fintype.card ι : ℝ) ^ 2 + Fintype.card ι) / (C * N) *
      (2 * h / (1 - (1 - h * p) ^ 2) * (2 * h / (1 - (1 - h * p) ^ 2)) *
        (1 + (1 - h * p) * (1 - h * p)) / (1 - (1 - h * p) * (1 - h * p))) := by
    simp_rw [← Finset.sum_mul, ← Finset.sum_div]
    rw [sum_sum_ite_two_one]
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hρ' : 1 - (1 - h * p) * (1 - h * p) ≠ 0 := by rwa [← sq]
  have h2 : 2 - h * p ≠ 0 := by linarith
  have h2' : 2 - p * h ≠ 0 := by linarith
  field_simp

end Isotropic

end Laplace.Sampler
