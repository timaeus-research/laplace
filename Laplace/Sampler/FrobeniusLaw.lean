/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.Wick4
import Laplace.Sampler.DirectionClosures

/-!
# The whole-covariance error law (E4)

The Sanity on Sampling note's E4 says the Monte Carlo error of the pooled covariance "follows
`√(d/(CN))` with a prefactor set by the autocorrelation times". For chains whose innovations form a
`FourthMomentTable` across chains, times and directions (in particular Gaussian chains), the pooled
uncentred second-moment matrix `Σ̂ᵢⱼ = (1/(CN)) ∑_c ∑_k x^c_i(k) x^c_j(k)` over the draws
`b+1, …, b+N` satisfies

* `integral_sum_sq_sub_eq` (the Frobenius decomposition):
  `E ∑ᵢⱼ (Sᵢⱼ - Σᵢⱼ)² = ∑ Var Sᵢⱼ + ∑ bias²`;
* `variance_pooledSecondMoment`: `Var Σ̂ᵢⱼ = (1 + δᵢⱼ)/(C N²) ∑_{k,l<N} Gᵢ(k,l) Gⱼ(k,l)` where
  `Gᵢ(k,l) = E[x_i(k) x_i(l)]` is the Gram table of direction `i` (cross-chain and
  cross-direction second moments vanish), via `cov_mul_mul_of_isLinComb`;
* `frobenius_pooledSecondMoment`: `E ‖Σ̂ - E Σ̂‖_F² = (1/(C N²)) ∑ᵢⱼ (1 + δᵢⱼ) ∑_{k,l} Gᵢ Gⱼ`
  (exact); `frobenius_pooledSecondMoment_target` adds the explicit zero-start bias against the
  stationary target `diag(s₂)`;
* `frobenius_pooledSecondMoment_le`: for AR(1) Gram tables `Gᵢ(k,l) = s₂ᵢ (ρᵢ^{|k-l|} - ρᵢ^{k+l})`
  with `0 ≤ ρᵢ < 1`, `E ‖Σ̂ - E Σ̂‖_F² ≤ (1/(CN)) ∑ᵢⱼ (1 + δᵢⱼ) s₂ᵢ s₂ⱼ (1 + ρᵢρⱼ)/(1 - ρᵢρⱼ)`:
  the autocorrelation times of the *products* along pairs of directions;
* the realised multi-direction chains `realChain (ρ i) (η c · i)` with a `FourthMomentTable`
  family of innovations satisfy the hypotheses (`gram_realChain_dir`, `isLinComb_realChain_dir`,
  `frobenius_realChain_le`).

The Gaussian discharge of the four-moment hypothesis for the ULA chain (independence of the
projected innovations across eigendirections) is the next tide; here the statements are
conditional on it and labelled as such.
-/

open MeasureTheory ProbabilityTheory Finset

namespace Laplace.Sampler

section Frobenius

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The Frobenius decomposition**: `E ∑ᵢⱼ (Sᵢⱼ - Σᵢⱼ)² = ∑ᵢⱼ Var Sᵢⱼ + ∑ᵢⱼ (E Sᵢⱼ - Σᵢⱼ)²`. -/
theorem integral_sum_sq_sub_eq {ι : Type*} [Fintype ι] (S : ι → ι → Ω → ℝ) (M : ι → ι → ℝ)
    (h1 : ∀ i j, Integrable (S i j) P) (h2 : ∀ i j, Integrable (fun ω => S i j ω ^ 2) P) :
    ∫ ω, ∑ i, ∑ j, (S i j ω - M i j) ^ 2 ∂P =
      ∑ i, ∑ j, (∫ ω, S i j ω ^ 2 ∂P - (∫ ω, S i j ω ∂P) ^ 2) +
        ∑ i, ∑ j, (∫ ω, S i j ω ∂P - M i j) ^ 2 := by
  have hexp : ∀ i j ω, (S i j ω - M i j) ^ 2 = S i j ω ^ 2 - 2 * M i j * S i j ω + M i j ^ 2 :=
    fun i j ω => by ring
  have hint : ∀ i j, Integrable (fun ω => (S i j ω - M i j) ^ 2) P := fun i j => by
    simp_rw [hexp]
    exact ((h2 i j).sub ((h1 i j).const_mul _)).add (integrable_const _)
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j,
    Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [hexp]
  have hA : Integrable (fun ω => S i j ω ^ 2 - 2 * M i j * S i j ω) P :=
    (h2 i j).sub ((h1 i j).const_mul _)
  rw [integral_add hA (integrable_const _), integral_sub (h2 i j) ((h1 i j).const_mul _),
    integral_const_mul, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring

omit [IsProbabilityMeasure P] in
/-- **The variance of a weighted sum** as a double sum of covariances. -/
theorem variance_sum_eq_sum_cov {α : Type*} (s : Finset α) (f : α → Ω → ℝ)
    (h1 : ∀ a ∈ s, Integrable (f a) P)
    (h2 : ∀ a ∈ s, ∀ b ∈ s, Integrable (fun ω => f a ω * f b ω) P) (q : ℝ) :
    ∫ ω, (q * ∑ a ∈ s, f a ω) ^ 2 ∂P - (∫ ω, q * ∑ a ∈ s, f a ω ∂P) ^ 2 =
      q ^ 2 * ∑ a ∈ s, ∑ b ∈ s,
        (∫ ω, f a ω * f b ω ∂P - (∫ ω, f a ω ∂P) * ∫ ω, f b ω ∂P) := by
  have hsq : ∀ ω, (q * ∑ a ∈ s, f a ω) ^ 2 = q ^ 2 * ∑ a ∈ s, ∑ b ∈ s, f a ω * f b ω := by
    intro ω
    rw [mul_pow, sq (∑ a ∈ s, f a ω), Finset.sum_mul_sum]
  simp_rw [hsq]
  rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun a ha => h1 a ha,
    integral_finsetSum _ fun a ha => integrable_finsetSum _ fun b hb => h2 a ha b hb,
    Finset.sum_congr rfl fun a ha => integral_finsetSum _ fun b hb => h2 a ha b hb]
  have key : ∀ (I : α → α → ℝ) (m : α → ℝ),
      ∑ a ∈ s, ∑ b ∈ s, (I a b - m a * m b) = ∑ a ∈ s, ∑ b ∈ s, I a b - (∑ a ∈ s, m a) ^ 2 := by
    intro I m
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
  rw [key]
  ring

variable {κ : Type*} {g : κ → Ω → ℝ} {v : ℝ}

/-- The pooled uncentred second-moment matrix of `C` chains along directions `ι` over the draws
`b+1, …, b+N`. -/
noncomputable def pooledSecondMoment {ι : Type*} {C : ℕ} (x : Fin C → ι → ℕ → Ω → ℝ) (N b : ℕ)
    (i j : ι) (ω : Ω) : ℝ :=
  (1 / ((C : ℝ) * N)) * ∑ c, ∑ k ∈ range N, x c i (b + 1 + k) ω * x c j (b + 1 + k) ω

theorem integrable_pooledSecondMoment {ι : Type*} {C : ℕ} {x : Fin C → ι → ℕ → Ω → ℝ} {N b : ℕ}
    (hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P) (i j : ι) :
    Integrable (pooledSecondMoment x N b i j) P := by
  unfold pooledSecondMoment
  exact (integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun k hk =>
    integrable_mul_of_memLp_four (hL4 _ _ _ hk) (hL4 _ _ _ hk)).const_mul _

omit [IsProbabilityMeasure P] in
theorem integrable_pooledSecondMoment_sq {ι : Type*} {C : ℕ} {x : Fin C → ι → ℕ → Ω → ℝ} {N b : ℕ}
    (hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P) (i j : ι) :
    Integrable (fun ω => pooledSecondMoment x N b i j ω ^ 2) P := by
  set f : Fin C × ℕ → Ω → ℝ := fun a ω => x a.1 i (b + 1 + a.2) ω * x a.1 j (b + 1 + a.2) ω with hf
  have hsum : ∀ ω, pooledSecondMoment x N b i j ω =
      (1 / ((C : ℝ) * N)) * ∑ a ∈ (univ : Finset (Fin C)) ×ˢ range N, f a ω := fun ω => by
    rw [pooledSecondMoment, Finset.sum_product]
  have hsq : ∀ ω, pooledSecondMoment x N b i j ω ^ 2 = (1 / ((C : ℝ) * N)) ^ 2 *
      ∑ a ∈ (univ : Finset (Fin C)) ×ˢ range N, ∑ a' ∈ (univ : Finset (Fin C)) ×ˢ range N,
        f a ω * f a' ω := by
    intro ω
    rw [hsum ω, mul_pow, sq (∑ a ∈ (univ : Finset (Fin C)) ×ˢ range N, f a ω), Finset.sum_mul_sum]
  simp_rw [hsq]
  refine (integrable_finsetSum _ fun a ha => integrable_finsetSum _ fun a' ha' => ?_).const_mul _
  have hk := (Finset.mem_product.mp ha).2
  have hk' := (Finset.mem_product.mp ha').2
  exact integrable_mul_mul_mul_of_memLp_four (hL4 _ _ _ hk) (hL4 _ _ _ hk) (hL4 _ _ _ hk')
    (hL4 _ _ _ hk')

/-- **The per-entry variance of the pooled second-moment matrix.** For chains that are linear
combinations of a `FourthMomentTable` family with the Gram table
`E[x^c_i(k) x^{c'}_j(l)] = δ_{cc'} δ_{ij} Gᵢ(k,l)`,
`Var Σ̂ᵢⱼ = (1 + δᵢⱼ)/(C N²) ∑_{k,l<N} Gᵢ(b+1+k, b+1+l) Gⱼ(b+1+k, b+1+l)`. -/
theorem variance_pooledSecondMoment {ι : Type*} [DecidableEq ι] (hT : FourthMomentTable g P v)
    {s : Finset κ} {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (x : Fin C → ι → ℕ → Ω → ℝ) (hx : ∀ c i k, k ∈ range N → IsLinComb g s (x c i (b + 1 + k)))
    (G : ι → ℕ → ℕ → ℝ)
    (hG : ∀ c c' i j k l, ∫ ω, x c i k ω * x c' j l ω ∂P = if c = c' ∧ i = j then G i k l else 0)
    (i j : ι) :
    ∫ ω, pooledSecondMoment x N b i j ω ^ 2 ∂P - (∫ ω, pooledSecondMoment x N b i j ω ∂P) ^ 2 =
      (if i = j then 2 else 1) / (C * N ^ 2) *
        ∑ k ∈ range N, ∑ l ∈ range N,
          G i (b + 1 + k) (b + 1 + l) * G j (b + 1 + k) (b + 1 + l) := by
  have hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P :=
    fun c i k hk => memLp_of_isLinComb hT.memLp (hx c i k hk)
  set f : Fin C × ℕ → Ω → ℝ := fun a ω => x a.1 i (b + 1 + a.2) ω * x a.1 j (b + 1 + a.2) ω with hf
  have hsum : ∀ ω, pooledSecondMoment x N b i j ω =
      (1 / ((C : ℝ) * N)) * ∑ a ∈ (univ : Finset (Fin C)) ×ˢ range N, f a ω := fun ω => by
    rw [pooledSecondMoment, Finset.sum_product]
  simp_rw [hsum]
  rw [variance_sum_eq_sum_cov _ f
    (fun a ha => integrable_mul_of_memLp_four (hL4 _ _ _ (Finset.mem_product.mp ha).2)
      (hL4 _ _ _ (Finset.mem_product.mp ha).2))
    (fun a ha a' ha' => integrable_mul_mul_mul_of_memLp_four
      (hL4 _ _ _ (Finset.mem_product.mp ha).2) (hL4 _ _ _ (Finset.mem_product.mp ha).2)
      (hL4 _ _ _ (Finset.mem_product.mp ha').2) (hL4 _ _ _ (Finset.mem_product.mp ha').2))]
  have hcov : ∀ a ∈ (univ : Finset (Fin C)) ×ˢ range N, ∀ a' ∈ (univ : Finset (Fin C)) ×ˢ range N,
      ∫ ω, f a ω * f a' ω ∂P - (∫ ω, f a ω ∂P) * ∫ ω, f a' ω ∂P =
        if a.1 = a'.1 then
          (if i = j then 2 else 1) *
            (G i (b + 1 + a.2) (b + 1 + a'.2) * G j (b + 1 + a.2) (b + 1 + a'.2))
        else 0 := by
    intro a ha a' ha'
    have hk := (Finset.mem_product.mp ha).2
    have hk' := (Finset.mem_product.mp ha').2
    rw [hf]
    dsimp only
    rw [cov_mul_mul_of_isLinComb hT (hx _ _ _ hk) (hx _ _ _ hk) (hx _ _ _ hk') (hx _ _ _ hk'),
      hG, hG, hG, hG]
    by_cases hij : i = j
    · subst hij
      simp only [and_true, if_true]
      split_ifs <;> ring
    · simp only [hij, Ne.symm hij, and_false, if_false, and_true, mul_zero, add_zero]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun a' ha' => hcov a ha a' ha']
  simp_rw [Finset.sum_product_right (s := (univ : Finset (Fin C))) (t := range N)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **The whole-covariance law (exact, zero start)**:
`E ‖Σ̂ - E Σ̂‖_F² = (1/(C N²)) ∑ᵢⱼ (1 + δᵢⱼ) ∑_{k,l<N} Gᵢ Gⱼ`. -/
theorem frobenius_pooledSecondMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hT : FourthMomentTable g P v) {s : Finset κ} {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (x : Fin C → ι → ℕ → Ω → ℝ)
    (hx : ∀ c i k, k ∈ range N → IsLinComb g s (x c i (b + 1 + k))) (G : ι → ℕ → ℕ → ℝ)
    (hG : ∀ c c' i j k l, ∫ ω, x c i k ω * x c' j l ω ∂P = if c = c' ∧ i = j then G i k l else 0) :
    ∫ ω, ∑ i, ∑ j, (pooledSecondMoment x N b i j ω -
        ∫ ω', pooledSecondMoment x N b i j ω' ∂P) ^ 2 ∂P =
      ∑ i, ∑ j, (if i = j then 2 else 1) / (C * N ^ 2) *
        ∑ k ∈ range N, ∑ l ∈ range N,
          G i (b + 1 + k) (b + 1 + l) * G j (b + 1 + k) (b + 1 + l) := by
  have hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P :=
    fun c i k hk => memLp_of_isLinComb hT.memLp (hx c i k hk)
  rw [integral_sum_sq_sub_eq _ _ (fun i j => integrable_pooledSecondMoment hL4 i j)
    (fun i j => integrable_pooledSecondMoment_sq hL4 i j)]
  simp only [sub_self, zero_pow two_ne_zero, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    variance_pooledSecondMoment hT hC hN b x hx G hG i j

/-- **The stationary envelope of the whole-covariance law.** With AR(1) Gram tables
`Gᵢ(k,l) = s₂ᵢ (ρᵢ^{|k-l|} - ρᵢ^{k+l})`, `0 ≤ ρᵢ < 1`,
`E ‖Σ̂ - E Σ̂‖_F² ≤ (1/(CN)) ∑ᵢⱼ (1 + δᵢⱼ) s₂ᵢ s₂ⱼ (1 + ρᵢρⱼ)/(1 - ρᵢρⱼ)`. -/
theorem frobenius_pooledSecondMoment_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hT : FourthMomentTable g P v) {s : Finset κ} {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (x : Fin C → ι → ℕ → Ω → ℝ)
    (hx : ∀ c i k, k ∈ range N → IsLinComb g s (x c i (b + 1 + k)))
    (ρ s₂ : ι → ℝ) (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i < 1) (hs₂ : ∀ i, 0 ≤ s₂ i)
    (hG : ∀ c c' i j k l, ∫ ω, x c i k ω * x c' j l ω ∂P =
      if c = c' ∧ i = j then s₂ i * (ρ i ^ Nat.dist k l - ρ i ^ (k + l)) else 0) :
    ∫ ω, ∑ i, ∑ j, (pooledSecondMoment x N b i j ω -
        ∫ ω', pooledSecondMoment x N b i j ω' ∂P) ^ 2 ∂P ≤
      ∑ i, ∑ j, (if i = j then 2 else 1) / (C * N) *
        (s₂ i * s₂ j * (1 + ρ i * ρ j) / (1 - ρ i * ρ j)) := by
  rw [frobenius_pooledSecondMoment hT hC hN b x hx _ hG]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hρij0 : 0 ≤ ρ i * ρ j := mul_nonneg (hρ0 i) (hρ0 j)
  have hρij1 : ρ i * ρ j < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (hρ0 i) (hρ1 i) (hρ1 j).le
  have hterm : ∀ k ∈ range N, ∀ l ∈ range N,
      s₂ i * (ρ i ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ i ^ (b + 1 + k + (b + 1 + l))) *
        (s₂ j * (ρ j ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ j ^ (b + 1 + k + (b + 1 + l)))) ≤
      s₂ i * s₂ j * (ρ i * ρ j) ^ Nat.dist k l := by
    intro k _ l _
    have hd : Nat.dist (b + 1 + k) (b + 1 + l) = Nat.dist k l := by unfold Nat.dist; omega
    have hle : ∀ m, Nat.dist k l ≤ b + 1 + k + (b + 1 + l) → ρ m ^ (b + 1 + k + (b + 1 + l)) ≤
        ρ m ^ Nat.dist k l := fun m h => pow_le_pow_of_le_one (hρ0 m) (hρ1 m).le h
    have hdle : Nat.dist k l ≤ b + 1 + k + (b + 1 + l) := by unfold Nat.dist; omega
    have hi0 : 0 ≤ ρ i ^ Nat.dist k l - ρ i ^ (b + 1 + k + (b + 1 + l)) := by
      linarith [hle i hdle]
    have hj0 : 0 ≤ ρ j ^ Nat.dist k l - ρ j ^ (b + 1 + k + (b + 1 + l)) := by
      linarith [hle j hdle]
    have hi1 : ρ i ^ Nat.dist k l - ρ i ^ (b + 1 + k + (b + 1 + l)) ≤ ρ i ^ Nat.dist k l := by
      linarith [pow_nonneg (hρ0 i) (b + 1 + k + (b + 1 + l))]
    have hj1 : ρ j ^ Nat.dist k l - ρ j ^ (b + 1 + k + (b + 1 + l)) ≤ ρ j ^ Nat.dist k l := by
      linarith [pow_nonneg (hρ0 j) (b + 1 + k + (b + 1 + l))]
    rw [hd, mul_pow]
    calc s₂ i * (ρ i ^ Nat.dist k l - ρ i ^ (b + 1 + k + (b + 1 + l))) *
          (s₂ j * (ρ j ^ Nat.dist k l - ρ j ^ (b + 1 + k + (b + 1 + l))))
        ≤ s₂ i * ρ i ^ Nat.dist k l * (s₂ j * ρ j ^ Nat.dist k l) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hi1 (hs₂ i))
            (mul_le_mul_of_nonneg_left hj1 (hs₂ j)) (mul_nonneg (hs₂ j) hj0)
            (mul_nonneg (hs₂ i) (pow_nonneg (hρ0 i) _))
      _ = s₂ i * s₂ j * (ρ i ^ Nat.dist k l * ρ j ^ Nat.dist k l) := by ring
  have hsum : ∑ k ∈ range N, ∑ l ∈ range N,
      s₂ i * (ρ i ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ i ^ (b + 1 + k + (b + 1 + l))) *
        (s₂ j * (ρ j ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ j ^ (b + 1 + k + (b + 1 + l)))) ≤
      s₂ i * s₂ j * (N * (1 + ρ i * ρ j) / (1 - ρ i * ρ j)) := by
    calc _ ≤ ∑ k ∈ range N, ∑ l ∈ range N, s₂ i * s₂ j * (ρ i * ρ j) ^ Nat.dist k l :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hterm k hk l hl
      _ = s₂ i * s₂ j * ∑ k ∈ range N, ∑ l ∈ range N, (ρ i * ρ j) ^ Nat.dist k l := by
          simp_rw [Finset.mul_sum]
      _ = s₂ i * s₂ j * (N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * (ρ i * ρ j) ^ (m + 1)) := by
          rw [sum_sum_pow_dist]
      _ ≤ s₂ i * s₂ j * (N * (1 + ρ i * ρ j) / (1 - ρ i * ρ j)) :=
          mul_le_mul_of_nonneg_left (toeplitz_sum_le hρij0 hρij1 N)
            (mul_nonneg (hs₂ i) (hs₂ j))
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoef : 0 ≤ (if i = j then (2 : ℝ) else 1) / (C * N ^ 2) := by
    split_ifs <;> positivity
  calc (if i = j then (2 : ℝ) else 1) / (C * N ^ 2) * ∑ k ∈ range N, ∑ l ∈ range N,
        s₂ i * (ρ i ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ i ^ (b + 1 + k + (b + 1 + l))) *
          (s₂ j * (ρ j ^ Nat.dist (b + 1 + k) (b + 1 + l) - ρ j ^ (b + 1 + k + (b + 1 + l))))
      ≤ (if i = j then (2 : ℝ) else 1) / (C * N ^ 2) *
          (s₂ i * s₂ j * (N * (1 + ρ i * ρ j) / (1 - ρ i * ρ j))) :=
        mul_le_mul_of_nonneg_left hsum hcoef
    _ = (if i = j then (2 : ℝ) else 1) / (C * N) *
          (s₂ i * s₂ j * (1 + ρ i * ρ j) / (1 - ρ i * ρ j)) := by
        field_simp

/-- **The mean of the pooled second-moment matrix**: diagonal,
`E Σ̂ᵢᵢ = (1/N) ∑_{k<N} Gᵢ(b+1+k, b+1+k)`. -/
theorem integral_pooledSecondMoment {ι : Type*} [DecidableEq ι] {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) {x : Fin C → ι → ℕ → Ω → ℝ}
    (hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P) (G : ι → ℕ → ℕ → ℝ)
    (hG : ∀ c c' i j k l, ∫ ω, x c i k ω * x c' j l ω ∂P = if c = c' ∧ i = j then G i k l else 0)
    (i j : ι) :
    ∫ ω, pooledSecondMoment x N b i j ω ∂P =
      if i = j then (1 / (N : ℝ)) * ∑ k ∈ range N, G i (b + 1 + k) (b + 1 + k) else 0 := by
  unfold pooledSecondMoment
  rw [integral_const_mul, integral_finsetSum _ fun c _ => integrable_finsetSum _ fun k hk =>
    integrable_mul_of_memLp_four (hL4 _ _ _ hk) (hL4 _ _ _ hk),
    Finset.sum_congr rfl fun c _ => integral_finsetSum _ fun k hk =>
      integrable_mul_of_memLp_four (hL4 _ _ _ hk) (hL4 _ _ _ hk),
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => hG c c i j _ _]
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  by_cases hij : i = j
  · subst hij
    simp only [and_self, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  · simp [hij]

/-- **The whole-covariance law against the stationary target** `Σ_∞ = diag(s₂)`: the centred law
plus the explicit zero-start bias `∑ᵢ (s₂ᵢ aᵢ)²`, `aᵢ = (1/N) ∑_{k<N} ρᵢ^{2(b+1+k)}`. -/
theorem frobenius_pooledSecondMoment_target {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hT : FourthMomentTable g P v) {s : Finset κ} {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (x : Fin C → ι → ℕ → Ω → ℝ)
    (hx : ∀ c i k, k ∈ range N → IsLinComb g s (x c i (b + 1 + k))) (ρ s₂ : ι → ℝ)
    (hG : ∀ c c' i j k l, ∫ ω, x c i k ω * x c' j l ω ∂P =
      if c = c' ∧ i = j then s₂ i * (ρ i ^ Nat.dist k l - ρ i ^ (k + l)) else 0) :
    ∫ ω, ∑ i, ∑ j, (pooledSecondMoment x N b i j ω - if i = j then s₂ i else 0) ^ 2 ∂P =
      ∫ ω, ∑ i, ∑ j, (pooledSecondMoment x N b i j ω -
          ∫ ω', pooledSecondMoment x N b i j ω' ∂P) ^ 2 ∂P +
        ∑ i, (s₂ i * ((1 / (N : ℝ)) * ∑ k ∈ range N, ρ i ^ (2 * (b + 1 + k)))) ^ 2 := by
  have hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P :=
    fun c i k hk => memLp_of_isLinComb hT.memLp (hx c i k hk)
  rw [integral_sum_sq_sub_eq _ _ (fun i j => integrable_pooledSecondMoment hL4 i j)
    (fun i j => integrable_pooledSecondMoment_sq hL4 i j),
    integral_sum_sq_sub_eq _ _ (fun i j => integrable_pooledSecondMoment hL4 i j)
    (fun i j => integrable_pooledSecondMoment_sq hL4 i j)]
  simp only [sub_self, zero_pow two_ne_zero, Finset.sum_const_zero, add_zero]
  congr 1
  simp_rw [integral_pooledSecondMoment hC hN b hL4 _ hG]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [Ne.symm hji])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp only [if_true, Nat.dist_self, pow_zero, ← two_mul]
  have hsum : 1 / (N : ℝ) * ∑ k ∈ range N, s₂ i * (1 - ρ i ^ (2 * (b + 1 + k))) =
      s₂ i * (1 - 1 / (N : ℝ) * ∑ k ∈ range N, ρ i ^ (2 * (b + 1 + k))) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    field_simp
  rw [hsum]
  ring

end Frobenius

/-! ### Realised chains along several directions -/

section Realised

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Chains with mutually orthogonal noise have orthogonal states, whatever their coefficients. -/
theorem AR1Chain.inner_x_x_of_orthogonal' {ρ ρ' v v' : ℝ} (X : AR1Chain E ρ v)
    (Y : AR1Chain E ρ' v') (h : ∀ j k, inner ℝ (X.η j) (Y.η k) = 0) (k l : ℕ) :
    inner ℝ (X.x k) (Y.x l) = 0 := by
  rw [X.x_eq_sum, Y.x_eq_sum, sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right, h, mul_zero, mul_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ℕ}

omit [Fintype ι] [IsProbabilityMeasure P] in
/-- **The Gram table of realised chains along several directions** driven by a white family of
innovations: `E[x^c_i(k) x^{c'}_j(l)] = δ_{cc'} δ_{ij} s₂ᵢ (ρᵢ^{|k-l|} - ρᵢ^{k+l})`. -/
theorem gram_realChain_dir (η : Fin C → ℕ → ι → Ω → ℝ) (ρ : ι → ℝ) (hρ : ∀ i, ρ i ^ 2 ≠ 1) {v : ℝ}
    (hη : ∀ c k i, MemLp (η c k i) 2 P)
    (hwhite : ∀ c c' k l i j, ∫ ω, η c k i ω * η c' l j ω ∂P =
      if c = c' ∧ k = l ∧ i = j then v else 0)
    (c c' : Fin C) (i j : ι) (k l : ℕ) :
    ∫ ω, realChain (ρ i) (fun m => η c m i) k ω * realChain (ρ j) (fun m => η c' m j) l ω ∂P =
      if c = c' ∧ i = j then v / (1 - ρ i ^ 2) * (ρ i ^ Nat.dist k l - ρ i ^ (k + l)) else 0 := by
  have hw : ∀ c i, ∀ m m', ∫ ω, η c m i ω * η c m' i ω ∂P = if m = m' then v else 0 :=
    fun c i m m' => by rw [hwhite]; simp
  rw [← inner_toLp_eq_integral (memLp_realChain (ρ i) (hη c · i) k)
    (memLp_realChain (ρ j) (hη c' · j) l)]
  change inner ℝ ((toAR1Chain (ρ i) (hη c · i) (hw c i)).x k)
    ((toAR1Chain (ρ j) (hη c' · j) (hw c' j)).x l) = _
  split_ifs with hcc'
  · obtain ⟨rfl, rfl⟩ := hcc'
    exact (toAR1Chain (ρ i) (hη c · i) (hw c i)).inner_x_x_dist (hρ i) k l
  · refine AR1Chain.inner_x_x_of_orthogonal' _ _ (fun m m' => ?_) k l
    change inner ℝ ((hη c m i).toLp _) ((hη c' m' j).toLp _) = 0
    rw [inner_toLp_eq_integral, hwhite, if_neg (fun h => hcc' ⟨h.1, h.2.2⟩)]

omit [MeasurableSpace Ω] [DecidableEq ι] in
/-- The realised chain along direction `i` up to time `T` is a linear combination of the
innovations `η c' m j`, `m ≤ T`, of all chains and directions. -/
theorem isLinComb_realChain_dir (ρ : ℝ) (η : Fin C → ℕ → ι → Ω → ℝ) (c : Fin C) (i : ι) (T : ℕ)
    (k : ℕ) (hk : k ≤ T) :
    IsLinComb (fun a : Fin C × ℕ × ι => η a.1 a.2.1 a.2.2)
      ((univ : Finset (Fin C)) ×ˢ range (T + 1) ×ˢ (univ : Finset ι))
      (realChain ρ (fun m => η c m i) k) := by
  induction k with
  | zero => exact IsLinComb.zero _ _
  | succ k ih =>
    have h1 := (ih (by omega)).const_mul ρ
    have hmem : (c, k + 1, i) ∈ (univ : Finset (Fin C)) ×ˢ range (T + 1) ×ˢ (univ : Finset ι) := by
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and, and_true]
      omega
    exact h1.add (IsLinComb.of_mem hmem)

/-- **E4 for realised multi-direction chains.** If the innovations `η c k i` form a
`FourthMomentTable` with variance `v` across chains, times and directions, the chains
`x^c_i = realChain (ρ i) (η c · i)` have
`E ‖Σ̂ - E Σ̂‖_F² ≤ (1/(CN)) ∑ᵢⱼ (1 + δᵢⱼ) s₂ᵢ s₂ⱼ (1 + ρᵢρⱼ)/(1 - ρᵢρⱼ)`, `s₂ᵢ = v/(1 - ρᵢ²)`. -/
theorem frobenius_realChain_le (η : Fin C → ℕ → ι → Ω → ℝ) {v : ℝ}
    (hT : FourthMomentTable (fun a : Fin C × ℕ × ι => η a.1 a.2.1 a.2.2) P v) (hv : 0 ≤ v)
    (ρ : ι → ℝ) (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i < 1) (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) :
    ∫ ω, ∑ i, ∑ j,
        (pooledSecondMoment (fun c i k => realChain (ρ i) (fun m => η c m i) k) N b i j ω -
          ∫ ω', pooledSecondMoment (fun c i k => realChain (ρ i) (fun m => η c m i) k) N b i j ω'
            ∂P) ^ 2 ∂P
      ≤ ∑ i, ∑ j, (if i = j then 2 else 1) / (C * N) *
        (v / (1 - ρ i ^ 2) * (v / (1 - ρ j ^ 2)) * (1 + ρ i * ρ j) / (1 - ρ i * ρ j)) := by
  have hρ : ∀ i, ρ i ^ 2 ≠ 1 := fun i => by nlinarith [hρ0 i, hρ1 i]
  have hs₂ : ∀ i, 0 ≤ v / (1 - ρ i ^ 2) := fun i => div_nonneg hv (by nlinarith [hρ0 i, hρ1 i])
  have hwhite : ∀ c c' k l i j, ∫ ω, η c k i ω * η c' l j ω ∂P =
      if c = c' ∧ k = l ∧ i = j then v else 0 := fun c c' k l i j => by
    simpa [Prod.ext_iff] using hT.white (c, k, i) (c', l, j)
  refine frobenius_pooledSecondMoment_le hT (s := (univ : Finset (Fin C)) ×ˢ range (b + N + 1) ×ˢ
    (univ : Finset ι)) hC hN b _ (fun c i k hk => ?_) ρ (fun i => v / (1 - ρ i ^ 2)) hρ0 hρ1 hs₂
    (fun c c' i j k l => ?_)
  · exact isLinComb_realChain_dir (ρ i) η c i (b + N) (b + 1 + k)
      (by have := Finset.mem_range.mp hk; omega)
  · exact gram_realChain_dir η ρ hρ (fun c k i => (hT.memLp (c, k, i)).mono_exponent (by norm_num))
      hwhite c c' i j k l

end Realised

end Laplace.Sampler
