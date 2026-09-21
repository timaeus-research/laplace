/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.DirectionClosures
import Laplace.Sampler.ULAEigen
import Laplace.OneD.GaussianMoments

/-!
# The variance of the directional second-moment estimator (E4)

The Sanity on Sampling note's E4 says the Monte Carlo error of the pooled covariance follows
`√(d/(CN))` "with a prefactor set by the autocorrelation times". Along one eigendirection the
ULA chain is a Gaussian AR(1) chain, so the variance of the pooled *uncentred* second moment
`S = (1/(CN)) ∑_c ∑_{i<N} (x^c_{b+1+i})²` is governed by the Gaussian fourth-moment (Isserlis)
identity `E[f_a² f_b²] = E[f_a²] E[f_b²] + 2 E[f_a f_b]²`:

* `variance_sum_sq_of_isserlis`: for any finite family satisfying the identity,
  `Var(q ∑ f_a²) = 2 q² ∑_{a,b} E[f_a f_b]²`;
* `pooled_second_moment_variance`: for realised AR(1) chains with white innovations the exact
  zero-start formula `Var S = 2 s₂²/(C N²) ∑_{i,j<N} (ρ^{|i-j|} - ρ^{2(b+1)+i+j})²`,
  `s₂ = v/(1-ρ²)`;
* `pooled_second_moment_variance_le`: `Var S ≤ 2 s₂² (1+ρ²)/(C N (1-ρ²))`, the integrated
  autocorrelation time `(1+ρ²)/(1-ρ²)` of the squared chain divided by the number of pooled draws;
* `integral_linComb_sq_mul_sq`: the Isserlis identity for finite linear combinations of independent
  innovations with the centred moment table `(0, v, 0, 3v²)`, by induction on the index set;
* the ULA realisation along a unit eigenvector with `(1+ρ²)/(1-ρ²) ≤ 1/(hp)`:
  `Var S ≤ 2 s₂²/(h p C N)`, i.e. a relative standard error of at most `√(τ_flat/(CN))`.

`S` is the uncentred second moment (the mean of the chain is known to be zero), not the sample
variance with the grand mean subtracted; the bound is relative to the stationary variance `s₂`
and is a variance bound, the (burn-in) bias being a separate statement.
-/

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Laplace.Sampler

/-! ### Products of `L⁴` functions -/

section Holder

/-- `4⁻¹ + 4⁻¹ = 2⁻¹`: the product of two `L⁴` functions is in `L²`. -/
instance holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 where
  inv_add_inv_eq_inv := by
    rw [show (4 : ENNReal) = 2 * 2 by norm_num,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← mul_add,
      ENNReal.inv_two_add_inv_two, mul_one]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem memLp_two_mul_of_memLp_four {f g : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P) :
    MemLp (fun ω => f ω * g ω) 2 P :=
  hg.mul hf

omit [IsProbabilityMeasure P] in
theorem integrable_mul_mul_mul_of_memLp_four {f g k l : Ω → ℝ} (hf : MemLp f 4 P)
    (hg : MemLp g 4 P) (hk : MemLp k 4 P) (hl : MemLp l 4 P) :
    Integrable (fun ω => f ω * g ω * (k ω * l ω)) P :=
  (memLp_two_mul_of_memLp_four hf hg).integrable_mul (memLp_two_mul_of_memLp_four hk hl)

omit [IsProbabilityMeasure P] in
theorem integrable_sq_mul_sq_of_memLp_four {f g : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P) :
    Integrable (fun ω => f ω ^ 2 * g ω ^ 2) P := by
  simpa only [sq] using integrable_mul_mul_mul_of_memLp_four hf hf hg hg

theorem integrable_mul_of_memLp_four {f g : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P) :
    Integrable (fun ω => f ω * g ω) P :=
  (memLp_two_mul_of_memLp_four hf hg).integrable one_le_two

theorem integrable_sq_of_memLp_four {f : Ω → ℝ} (hf : MemLp f 4 P) :
    Integrable (fun ω => f ω ^ 2) P := by
  simpa only [sq] using integrable_mul_of_memLp_four hf hf

end Holder

/-! ### The variance of a sum of squares under the Isserlis identity -/

section Isserlis

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The **Gaussian fourth-moment (Isserlis) identity** on a finite family:
`E[f_a² f_b²] = E[f_a²] E[f_b²] + 2 E[f_a f_b]²`. -/
def IsserlisFamily {α : Type*} (s : Finset α) (f : α → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∫ ω, f a ω ^ 2 * f b ω ^ 2 ∂P =
    (∫ ω, f a ω ^ 2 ∂P) * (∫ ω, f b ω ^ 2 ∂P) + 2 * (∫ ω, f a ω * f b ω ∂P) ^ 2

/-- **Variance of a quadratic statistic**: under the Isserlis identity,
`E[(q ∑ f_a²)²] - (E[q ∑ f_a²])² = 2 q² ∑_{a,b} E[f_a f_b]²`. -/
theorem variance_sum_sq_of_isserlis {α : Type*} (s : Finset α) (f : α → Ω → ℝ)
    (hf : ∀ a ∈ s, MemLp (f a) 4 P) (hW : IsserlisFamily s f P) (q : ℝ) :
    ∫ ω, (q * ∑ a ∈ s, f a ω ^ 2) ^ 2 ∂P - (∫ ω, q * ∑ a ∈ s, f a ω ^ 2 ∂P) ^ 2 =
      2 * q ^ 2 * ∑ a ∈ s, ∑ b ∈ s, (∫ ω, f a ω * f b ω ∂P) ^ 2 := by
  have h1 : ∀ ω, (q * ∑ a ∈ s, f a ω ^ 2) ^ 2 =
      q ^ 2 * ∑ a ∈ s, ∑ b ∈ s, f a ω ^ 2 * f b ω ^ 2 := by
    intro ω
    rw [mul_pow, sq (∑ a ∈ s, f a ω ^ 2), Finset.sum_mul_sum]
  simp_rw [h1]
  rw [integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun a ha => integrable_sq_of_memLp_four (hf a ha),
    integral_finsetSum _ fun a ha =>
      integrable_finsetSum _ fun b hb => integrable_sq_mul_sq_of_memLp_four (hf a ha) (hf b hb),
    Finset.sum_congr rfl fun a ha =>
      integral_finsetSum _ fun b hb => integrable_sq_mul_sq_of_memLp_four (hf a ha) (hf b hb),
    Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hW a ha b hb]
  have key : ∀ (I : α → ℝ) (M : α → α → ℝ),
      ∑ a ∈ s, ∑ b ∈ s, (I a * I b + 2 * M a b ^ 2) =
        (∑ a ∈ s, I a) ^ 2 + 2 * ∑ a ∈ s, ∑ b ∈ s, M a b ^ 2 := by
    intro I M
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [key]
  ring

end Isserlis

/-! ### Realised AR(1) chains: the Gram table and the exact variance -/

section RealChain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `realChain` stays in `Lᵖ` for any exponent the innovations are in. -/
theorem memLp_realChain_of_memLp {p : ENNReal} (ρ : ℝ) {η : ℕ → Ω → ℝ}
    (hη : ∀ k, MemLp (η k) p P) (k : ℕ) : MemLp (realChain ρ η k) p P := by
  induction k with
  | zero => exact memLp_const 0
  | succ k ih => exact (ih.const_mul ρ).add (hη (k + 1))

omit [IsProbabilityMeasure P] in
/-- **The Gram table of realised chains**: `∫ x^c_k x^{c'}_l = δ_{cc'} s₂ (ρ^{|k-l|} - ρ^{k+l})`. -/
theorem integral_realChain_mul_realChain {C : ℕ} (ρ : ℝ) (hρ : ρ ^ 2 ≠ 1) {v : ℝ}
    (η : Fin C → ℕ → Ω → ℝ) (hη : ∀ c k, MemLp (η c k) 2 P)
    (hwhite : ∀ c c' j k, ∫ ω, η c j ω * η c' k ω ∂P = if c = c' ∧ j = k then v else 0)
    (c c' : Fin C) (k l : ℕ) :
    ∫ ω, realChain ρ (η c) k ω * realChain ρ (η c') l ω ∂P =
      if c = c' then v / (1 - ρ ^ 2) * (ρ ^ Nat.dist k l - ρ ^ (k + l)) else 0 := by
  have hw : ∀ c, ∀ j k, ∫ ω, η c j ω * η c k ω ∂P = if j = k then v else 0 := fun c j k => by
    rw [hwhite]; simp
  rw [← inner_toLp_eq_integral (memLp_realChain ρ (hη c) k) (memLp_realChain ρ (hη c') l)]
  change inner ℝ ((toAR1Chain ρ (hη c) (hw c)).x k) ((toAR1Chain ρ (hη c') (hw c')).x l) = _
  split_ifs with hcc'
  · subst hcc'
    exact (toAR1Chain ρ (hη c) (hw c)).inner_x_x_dist hρ k l
  · refine AR1Chain.inner_x_x_of_orthogonal _ _ (fun j k => ?_) k l
    change inner ℝ ((hη c j).toLp _) ((hη c' k).toLp _) = 0
    rw [inner_toLp_eq_integral, hwhite, if_neg (fun h => hcc' h.1)]

/-- **The exact variance of the pooled uncentred second moment.** For `C` realised chains with
white innovations of variance `v`, draws `b+1, …, b+N`, under the Isserlis identity on the window,
`Var S = 2 s₂²/(C N²) ∑_{i,j<N} (ρ^{|i-j|} - ρ^{2(b+1)+i+j})²` with `s₂ = v/(1-ρ²)`. -/
theorem pooled_second_moment_variance {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ) (ρ : ℝ)
    (hρ : ρ ^ 2 ≠ 1) {v : ℝ} (η : Fin C → ℕ → Ω → ℝ) (hη : ∀ c k, MemLp (η c k) 4 P)
    (hwhite : ∀ c c' j k, ∫ ω, η c j ω * η c' k ω ∂P = if c = c' ∧ j = k then v else 0)
    (hW : IsserlisFamily (univ ×ˢ range N)
      (fun a : Fin C × ℕ => realChain ρ (η a.1) (b + 1 + a.2)) P) :
    ∫ ω, ((1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, realChain ρ (η c) (b + 1 + i) ω ^ 2) ^ 2 ∂P -
      (∫ ω, (1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, realChain ρ (η c) (b + 1 + i) ω ^ 2 ∂P) ^ 2 =
      2 * (v / (1 - ρ ^ 2)) ^ 2 / (C * N ^ 2) *
        ∑ i ∈ range N, ∑ j ∈ range N, (ρ ^ Nat.dist i j - ρ ^ (2 * (b + 1) + i + j)) ^ 2 := by
  set f : Fin C × ℕ → Ω → ℝ := fun a => realChain ρ (η a.1) (b + 1 + a.2) with hf
  have hsum : ∀ ω, ∑ c, ∑ i ∈ range N, realChain ρ (η c) (b + 1 + i) ω ^ 2 =
      ∑ a ∈ univ ×ˢ range N, f a ω ^ 2 := fun ω => by rw [Finset.sum_product]
  simp_rw [hsum]
  rw [variance_sum_sq_of_isserlis _ f (fun a _ => memLp_realChain_of_memLp ρ (hη a.1) _) hW]
  have hG : ∀ a ∈ univ ×ˢ range N, ∀ a' ∈ univ ×ˢ range N, (∫ ω, f a ω * f a' ω ∂P) ^ 2 =
      if a.1 = a'.1 then
        (v / (1 - ρ ^ 2)) ^ 2 * (ρ ^ Nat.dist a.2 a'.2 - ρ ^ (2 * (b + 1) + a.2 + a'.2)) ^ 2
      else 0 := by
    intro a _ a' _
    rw [hf]
    dsimp only
    rw [integral_realChain_mul_realChain ρ hρ η (fun c k => (hη c k).mono_exponent (by norm_num))
      hwhite]
    split_ifs
    · have hd : Nat.dist (b + 1 + a.2) (b + 1 + a'.2) = Nat.dist a.2 a'.2 := by
        unfold Nat.dist; omega
      have he : b + 1 + a.2 + (b + 1 + a'.2) = 2 * (b + 1) + a.2 + a'.2 := by ring
      rw [hd, he, mul_pow]
    · simp
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun a' ha' => hG a ha a' ha']
  simp_rw [Finset.sum_product_right (s := (univ : Finset (Fin C))) (t := range N)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **The stationary envelope**: `Var S ≤ 2 s₂² (1+ρ²)/(C N (1-ρ²))` for `0 ≤ ρ < 1`. -/
theorem pooled_second_moment_variance_le {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v : ℝ} (η : Fin C → ℕ → Ω → ℝ) (hη : ∀ c k, MemLp (η c k) 4 P)
    (hwhite : ∀ c c' j k, ∫ ω, η c j ω * η c' k ω ∂P = if c = c' ∧ j = k then v else 0)
    (hW : IsserlisFamily (univ ×ˢ range N)
      (fun a : Fin C × ℕ => realChain ρ (η a.1) (b + 1 + a.2)) P) :
    ∫ ω, ((1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, realChain ρ (η c) (b + 1 + i) ω ^ 2) ^ 2 ∂P -
      (∫ ω, (1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, realChain ρ (η c) (b + 1 + i) ω ^ 2 ∂P) ^ 2 ≤
      2 * (v / (1 - ρ ^ 2)) ^ 2 * (1 + ρ ^ 2) / (C * N * (1 - ρ ^ 2)) := by
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hρ : ρ ^ 2 ≠ 1 := hρ2.ne
  rw [pooled_second_moment_variance hC hN b ρ hρ η hη hwhite hW]
  have hterm : ∀ i ∈ range N, ∀ j ∈ range N,
      (ρ ^ Nat.dist i j - ρ ^ (2 * (b + 1) + i + j)) ^ 2 ≤ (ρ ^ 2) ^ Nat.dist i j := by
    intro i _ j _
    have h1 : ρ ^ (2 * (b + 1) + i + j) ≤ ρ ^ Nat.dist i j :=
      pow_le_pow_of_le_one hρ0 hρ1.le (by unfold Nat.dist; omega)
    have h2 : 0 ≤ ρ ^ (2 * (b + 1) + i + j) := pow_nonneg hρ0 _
    have h3 : (ρ ^ 2) ^ Nat.dist i j = (ρ ^ Nat.dist i j) ^ 2 := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h3]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hsum : ∑ i ∈ range N, ∑ j ∈ range N, (ρ ^ Nat.dist i j - ρ ^ (2 * (b + 1) + i + j)) ^ 2 ≤
      N * (1 + ρ ^ 2) / (1 - ρ ^ 2) := by
    calc ∑ i ∈ range N, ∑ j ∈ range N, (ρ ^ Nat.dist i j - ρ ^ (2 * (b + 1) + i + j)) ^ 2
        ≤ ∑ i ∈ range N, ∑ j ∈ range N, (ρ ^ 2) ^ Nat.dist i j :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
      _ = N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * (ρ ^ 2) ^ (m + 1) :=
          sum_sum_pow_dist (ρ ^ 2) N
      _ ≤ N * (1 + ρ ^ 2) / (1 - ρ ^ 2) := toeplitz_sum_le (by positivity) hρ2 N
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1ρ : 1 - ρ ^ 2 ≠ 0 := by linarith
  calc 2 * (v / (1 - ρ ^ 2)) ^ 2 / (C * N ^ 2) *
        ∑ i ∈ range N, ∑ j ∈ range N, (ρ ^ Nat.dist i j - ρ ^ (2 * (b + 1) + i + j)) ^ 2
      ≤ 2 * (v / (1 - ρ ^ 2)) ^ 2 / (C * N ^ 2) * (N * (1 + ρ ^ 2) / (1 - ρ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * (v / (1 - ρ ^ 2)) ^ 2 * (1 + ρ ^ 2) / (C * N * (1 - ρ ^ 2)) := by
        field_simp

end RealChain

/-! ### The Isserlis identity for linear combinations of independent innovations -/

section LinComb

variable {Ω : Type*} {κ : Type*}

/-- `f` is a finite linear combination `∑_{i ∈ s} a i • g i`. -/
def IsLinComb (g : κ → Ω → ℝ) (s : Finset κ) (f : Ω → ℝ) : Prop :=
  ∃ a : κ → ℝ, ∀ ω, f ω = ∑ i ∈ s, a i * g i ω

theorem IsLinComb.zero (g : κ → Ω → ℝ) (s : Finset κ) : IsLinComb g s (fun _ => 0) :=
  ⟨fun _ => 0, fun ω => by simp⟩

theorem IsLinComb.add {g : κ → Ω → ℝ} {s : Finset κ} {f₁ f₂ : Ω → ℝ} (h₁ : IsLinComb g s f₁)
    (h₂ : IsLinComb g s f₂) : IsLinComb g s (fun ω => f₁ ω + f₂ ω) := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  refine ⟨fun i => a i + b i, fun ω => ?_⟩
  change f₁ ω + f₂ ω = ∑ i ∈ s, (a i + b i) * g i ω
  rw [ha, hb, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem IsLinComb.const_mul {g : κ → Ω → ℝ} {s : Finset κ} {f : Ω → ℝ} (c : ℝ)
    (h : IsLinComb g s f) : IsLinComb g s (fun ω => c * f ω) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun i => c * a i, fun ω => ?_⟩
  change c * f ω = ∑ i ∈ s, (c * a i) * g i ω
  rw [ha, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem IsLinComb.of_mem {g : κ → Ω → ℝ} {s : Finset κ} {i : κ} (hi : i ∈ s) :
    IsLinComb g s (g i) := by
  classical
  exact ⟨fun j => if j = i then 1 else 0, fun ω => by simp [Finset.sum_ite_eq', hi]⟩

end LinComb

section Independent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {κ : Type*}

theorem measurable_of_isLinComb {g : κ → Ω → ℝ} (hmeas : ∀ i, Measurable (g i)) {s : Finset κ}
    {f : Ω → ℝ} (hf : IsLinComb g s f) : Measurable f := by
  obtain ⟨a, ha⟩ := hf
  rw [funext ha]
  exact Finset.measurable_sum _ fun i _ => (hmeas i).const_mul _

omit [IsProbabilityMeasure P] in
theorem memLp_of_isLinComb {p : ENNReal} {g : κ → Ω → ℝ} (hg : ∀ i, MemLp (g i) p P)
    {s : Finset κ} {f : Ω → ℝ} (hf : IsLinComb g s f) : MemLp f p P := by
  obtain ⟨a, ha⟩ := hf
  rw [funext ha]
  exact memLp_finsetSum _ fun i _ => (hg i).const_mul _


/-- Independent innovations with the centred moment table `(0, v, 0, 3v²)`, in `L⁴`. -/
structure FourthMomentTable (g : κ → Ω → ℝ) (P : Measure Ω) (v : ℝ) : Prop where
  memLp : ∀ i, MemLp (g i) 4 P
  meas : ∀ i, Measurable (g i)
  indep : iIndepFun g P
  m1 : ∀ i, ∫ ω, g i ω ∂P = 0
  m2 : ∀ i, ∫ ω, g i ω ^ 2 ∂P = v
  m3 : ∀ i, ∫ ω, g i ω ^ 3 ∂P = 0
  m4 : ∀ i, ∫ ω, g i ω ^ 4 ∂P = 3 * v ^ 2

omit [IsProbabilityMeasure P] in
/-- The pair `(X, Y)` of linear combinations over `s` is independent of `g n` for `n ∉ s`. -/
theorem indepFun_pair_of_isLinComb {g : κ → Ω → ℝ} (hind : iIndepFun g P)
    (hmeas : ∀ i, Measurable (g i)) {s : Finset κ} {n : κ} (hn : n ∉ s) {X Y : Ω → ℝ}
    (hX : IsLinComb g s X) (hY : IsLinComb g s Y) :
    IndepFun (fun ω => (X ω, Y ω)) (g n) P := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  have h := hind.indepFun_finset s {n} (Finset.disjoint_singleton_right.mpr hn) hmeas
  have hF : Measurable (fun z : s → ℝ => (∑ i : s, a i * z i, ∑ i : s, b i * z i)) := by
    fun_prop
  have hG : Measurable (fun z : ({n} : Finset κ) → ℝ => z ⟨n, Finset.mem_singleton_self n⟩) :=
    measurable_pi_apply _
  have := h.comp hF hG
  convert this using 1
  · funext ω
    simp only [Function.comp_apply, ha, hb]
    rw [Finset.sum_coe_sort s (fun i => a i * g i ω),
      Finset.sum_coe_sort s (fun i => b i * g i ω)]
  · rfl

omit [IsProbabilityMeasure P] in
/-- **Factorisation**: `E[φ(X, Y) gₙᵏ] = E[φ(X, Y)] E[gₙᵏ]` for `X, Y` linear combinations over
`s ∌ n`. -/
theorem integral_mul_pow_of_isLinComb {g : κ → Ω → ℝ} {v : ℝ} (hT : FourthMomentTable g P v)
    {s : Finset κ} {n : κ} (hn : n ∉ s) {X Y : Ω → ℝ} (hX : IsLinComb g s X)
    (hY : IsLinComb g s Y) (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (k : ℕ) :
    ∫ ω, φ (X ω, Y ω) * g n ω ^ k ∂P =
      (∫ ω, φ (X ω, Y ω) ∂P) * ∫ ω, g n ω ^ k ∂P := by
  have h := (indepFun_pair_of_isLinComb hT.indep hT.meas hn hX hY).comp hφ
    (measurable_id.pow_const k)
  exact h.integral_fun_mul_eq_mul_integral
    (hφ.comp ((measurable_of_isLinComb hT.meas hX).prodMk
      (measurable_of_isLinComb hT.meas hY))).aestronglyMeasurable
    ((hT.meas n).pow_const k).aestronglyMeasurable

/-- **Second moments of linear combinations**: `E[(∑ aᵢ gᵢ)(∑ bᵢ gᵢ)] = v ∑ aᵢ bᵢ`. -/
theorem integral_linComb_mul {g : κ → Ω → ℝ} {v : ℝ} (hT : FourthMomentTable g P v)
    (s : Finset κ) (a b : κ → ℝ) :
    ∫ ω, (∑ i ∈ s, a i * g i ω) * (∑ i ∈ s, b i * g i ω) ∂P = v * ∑ i ∈ s, a i * b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    obtain ⟨X, hXd⟩ : ∃ X : Ω → ℝ, X = fun ω => ∑ i ∈ s, a i * g i ω := ⟨_, rfl⟩
    obtain ⟨Y, hYd⟩ : ∃ Y : Ω → ℝ, Y = fun ω => ∑ i ∈ s, b i * g i ω := ⟨_, rfl⟩
    have hXl : IsLinComb g s X := ⟨a, fun ω => by rw [hXd]⟩
    have hYl : IsLinComb g s Y := ⟨b, fun ω => by rw [hYd]⟩
    have hX4 := memLp_of_isLinComb hT.memLp hXl
    have hY4 := memLp_of_isLinComb hT.memLp hYl
    have hG4 := hT.memLp n
    have hexp : ∀ ω, (a n * g n ω + ∑ i ∈ s, a i * g i ω) * (b n * g n ω + ∑ i ∈ s, b i * g i ω) =
        X ω * Y ω + b n * (X ω * g n ω ^ 1) + a n * (Y ω * g n ω ^ 1) +
          a n * b n * g n ω ^ 2 := by
      intro ω
      simp only [hXd, hYd]
      ring
    simp_rw [hexp]
    have h1 : Integrable (fun ω => X ω * Y ω) P := integrable_mul_of_memLp_four hX4 hY4
    have h2 : Integrable (fun ω => b n * (X ω * g n ω ^ 1)) P := by
      simpa only [pow_one] using (integrable_mul_of_memLp_four hX4 hG4).const_mul (b n)
    have h3 : Integrable (fun ω => a n * (Y ω * g n ω ^ 1)) P := by
      simpa only [pow_one] using (integrable_mul_of_memLp_four hY4 hG4).const_mul (a n)
    have h4 : Integrable (fun ω => a n * b n * g n ω ^ 2) P :=
      (integrable_sq_of_memLp_four hG4).const_mul _
    have h12 : Integrable (fun ω => X ω * Y ω + b n * (X ω * g n ω ^ 1)) P := h1.add h2
    have h123 : Integrable (fun ω => X ω * Y ω + b n * (X ω * g n ω ^ 1) +
        a n * (Y ω * g n ω ^ 1)) P := h12.add h3
    rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_mul_pow_of_isLinComb hT hn hXl hYl Prod.fst measurable_fst 1,
      integral_mul_pow_of_isLinComb hT hn hXl hYl Prod.snd measurable_snd 1]
    simp only [pow_one]
    rw [hT.m1 n, hT.m2 n]
    have hXY : ∫ ω, X ω * Y ω ∂P = v * ∑ i ∈ s, a i * b i := by
      rw [← ih]
      congr 1
      funext ω
      simp only [hXd, hYd]
    rw [hXY]
    ring

/-- **The Isserlis identity for linear combinations**: for independent innovations with the
centred moment table `(0, v, 0, 3v²)`,
`E[(∑ aᵢ gᵢ)² (∑ bᵢ gᵢ)²] = v² ((∑ aᵢ²)(∑ bᵢ²) + 2 (∑ aᵢ bᵢ)²)`. -/
theorem integral_linComb_sq_mul_sq {g : κ → Ω → ℝ} {v : ℝ} (hT : FourthMomentTable g P v)
    (s : Finset κ) (a b : κ → ℝ) :
    ∫ ω, (∑ i ∈ s, a i * g i ω) ^ 2 * (∑ i ∈ s, b i * g i ω) ^ 2 ∂P =
      v ^ 2 * ((∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) + 2 * (∑ i ∈ s, a i * b i) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    obtain ⟨X, hXd⟩ : ∃ X : Ω → ℝ, X = fun ω => ∑ i ∈ s, a i * g i ω := ⟨_, rfl⟩
    obtain ⟨Y, hYd⟩ : ∃ Y : Ω → ℝ, Y = fun ω => ∑ i ∈ s, b i * g i ω := ⟨_, rfl⟩
    have hXl : IsLinComb g s X := ⟨a, fun ω => by rw [hXd]⟩
    have hYl : IsLinComb g s Y := ⟨b, fun ω => by rw [hYd]⟩
    have hX4 := memLp_of_isLinComb hT.memLp hXl
    have hY4 := memLp_of_isLinComb hT.memLp hYl
    have hG4 := hT.memLp n
    set α := a n with hα
    set β := b n with hβ
    have hW4 : MemLp (fun ω => β * X ω + α * Y ω) 4 P := (hX4.const_mul β).add (hY4.const_mul α)
    have hexp : ∀ ω,
        (α * g n ω + ∑ i ∈ s, a i * g i ω) ^ 2 * (β * g n ω + ∑ i ∈ s, b i * g i ω) ^ 2 =
          X ω * Y ω * (X ω * Y ω) +
            2 * (X ω * Y ω * (β * X ω + α * Y ω) * g n ω ^ 1) +
            ((β * X ω + α * Y ω) * (β * X ω + α * Y ω) * g n ω ^ 2 +
              2 * (α * β) * (X ω * Y ω * g n ω ^ 2)) +
            2 * (α * β) * ((β * X ω + α * Y ω) * g n ω ^ 3) +
            α ^ 2 * β ^ 2 * g n ω ^ 4 := by
      intro ω
      simp only [hXd, hYd]
      ring
    simp_rw [hexp]
    have h0 : Integrable (fun ω => X ω * Y ω * (X ω * Y ω)) P :=
      integrable_mul_mul_mul_of_memLp_four hX4 hY4 hX4 hY4
    have h1 : Integrable (fun ω => 2 * (X ω * Y ω * (β * X ω + α * Y ω) * g n ω ^ 1)) P := by
      simpa only [pow_one, mul_assoc] using
        (integrable_mul_mul_mul_of_memLp_four hX4 hY4 hW4 hG4).const_mul 2
    have h2a : Integrable (fun ω => (β * X ω + α * Y ω) * (β * X ω + α * Y ω) * g n ω ^ 2) P := by
      simpa only [sq] using integrable_mul_mul_mul_of_memLp_four hW4 hW4 hG4 hG4
    have h2b : Integrable (fun ω => 2 * (α * β) * (X ω * Y ω * g n ω ^ 2)) P := by
      simpa only [sq] using (integrable_mul_mul_mul_of_memLp_four hX4 hY4 hG4 hG4).const_mul _
    have h3 : Integrable (fun ω => 2 * (α * β) * ((β * X ω + α * Y ω) * g n ω ^ 3)) P := by
      have := (integrable_mul_mul_mul_of_memLp_four hW4 hG4 hG4 hG4).const_mul (2 * (α * β))
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      ring
    have h4 : Integrable (fun ω => α ^ 2 * β ^ 2 * g n ω ^ 4) P := by
      have := (integrable_mul_mul_mul_of_memLp_four hG4 hG4 hG4 hG4).const_mul (α ^ 2 * β ^ 2)
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      ring
    have h01 : Integrable (fun ω => X ω * Y ω * (X ω * Y ω) +
        2 * (X ω * Y ω * (β * X ω + α * Y ω) * g n ω ^ 1)) P := h0.add h1
    have h2 : Integrable (fun ω => (β * X ω + α * Y ω) * (β * X ω + α * Y ω) * g n ω ^ 2 +
        2 * (α * β) * (X ω * Y ω * g n ω ^ 2)) P := h2a.add h2b
    have h012 : Integrable (fun ω => X ω * Y ω * (X ω * Y ω) +
        2 * (X ω * Y ω * (β * X ω + α * Y ω) * g n ω ^ 1) +
        ((β * X ω + α * Y ω) * (β * X ω + α * Y ω) * g n ω ^ 2 +
          2 * (α * β) * (X ω * Y ω * g n ω ^ 2))) P := h01.add h2
    have h0123 : Integrable (fun ω => X ω * Y ω * (X ω * Y ω) +
        2 * (X ω * Y ω * (β * X ω + α * Y ω) * g n ω ^ 1) +
        ((β * X ω + α * Y ω) * (β * X ω + α * Y ω) * g n ω ^ 2 +
          2 * (α * β) * (X ω * Y ω * g n ω ^ 2)) +
        2 * (α * β) * ((β * X ω + α * Y ω) * g n ω ^ 3)) P := h012.add h3
    rw [integral_add h0123 h4, integral_add h012 h3, integral_add h01 h2,
      integral_add h0 h1, integral_add h2a h2b, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul,
      integral_mul_pow_of_isLinComb hT hn hXl hYl
        (fun p : ℝ × ℝ => p.1 * p.2 * (β * p.1 + α * p.2)) (by fun_prop) 1,
      integral_mul_pow_of_isLinComb hT hn hXl hYl
        (fun p : ℝ × ℝ => (β * p.1 + α * p.2) * (β * p.1 + α * p.2)) (by fun_prop) 2,
      integral_mul_pow_of_isLinComb hT hn hXl hYl (fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) 2,
      integral_mul_pow_of_isLinComb hT hn hXl hYl (fun p : ℝ × ℝ => β * p.1 + α * p.2)
        (by fun_prop) 3]
    simp only [pow_one]
    rw [hT.m1 n, hT.m2 n, hT.m3 n, hT.m4 n]
    have hT0 : ∫ ω, X ω * Y ω * (X ω * Y ω) ∂P =
        v ^ 2 * ((∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) + 2 * (∑ i ∈ s, a i * b i) ^ 2) := by
      rw [← ih]
      congr 1
      funext ω
      simp only [hXd, hYd]
      ring
    have hWsum : ∀ ω, β * X ω + α * Y ω = ∑ i ∈ s, (β * a i + α * b i) * g i ω := by
      intro ω
      simp only [hXd, hYd, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hWW : ∫ ω, (β * X ω + α * Y ω) * (β * X ω + α * Y ω) ∂P =
        v * (β ^ 2 * ∑ i ∈ s, a i ^ 2 + 2 * α * β * ∑ i ∈ s, a i * b i +
          α ^ 2 * ∑ i ∈ s, b i ^ 2) := by
      simp_rw [hWsum]
      rw [integral_linComb_mul hT s]
      congr 1
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hXY : ∫ ω, X ω * Y ω ∂P = v * ∑ i ∈ s, a i * b i := by
      rw [← integral_linComb_mul hT s a b]
      congr 1
      funext ω
      simp only [hXd, hYd]
    rw [hT0, hWW, hXY]
    ring

/-- The white-noise table of a `FourthMomentTable`. -/
theorem FourthMomentTable.white [DecidableEq κ] {g : κ → Ω → ℝ} {v : ℝ}
    (hT : FourthMomentTable g P v) (a a' : κ) :
    ∫ ω, g a ω * g a' ω ∂P = if a = a' then v else 0 :=
  white_of_indep g (fun a => (hT.memLp a).mono_exponent (by norm_num)) hT.m1 hT.m2
    (fun a a' h => hT.indep.indepFun h) a a'

/-- A family of linear combinations of a `FourthMomentTable` satisfies the Isserlis identity. -/
theorem isserlisFamily_of_isLinComb {g : κ → Ω → ℝ} {v : ℝ} (hT : FourthMomentTable g P v)
    {α : Type*} (t : Finset α) (f : α → Ω → ℝ) (s : Finset κ)
    (hf : ∀ a ∈ t, IsLinComb g s (f a)) : IsserlisFamily t f P := by
  intro a ha b hb
  obtain ⟨ca, hca⟩ := hf a ha
  obtain ⟨cb, hcb⟩ := hf b hb
  have h2 : ∀ c : κ → ℝ, ∫ ω, (∑ i ∈ s, c i * g i ω) ^ 2 ∂P = v * ∑ i ∈ s, c i ^ 2 := fun c => by
    have := integral_linComb_mul hT s c c
    simp only [← sq] at this
    exact this
  simp only [funext hca, funext hcb]
  rw [integral_linComb_sq_mul_sq hT s ca cb, integral_linComb_mul hT s ca cb, h2, h2]
  ring

omit [MeasurableSpace Ω] in
/-- The realised chain `realChain ρ (η c) k`, `k ≤ T`, is a linear combination of the innovations
`η c' m`, `m ≤ T`. -/
theorem isLinComb_realChain {C : ℕ} (ρ : ℝ) (η : Fin C → ℕ → Ω → ℝ) (c : Fin C) (T : ℕ)
    (k : ℕ) (hk : k ≤ T) :
    IsLinComb (fun a : Fin C × ℕ => η a.1 a.2) (univ ×ˢ range (T + 1)) (realChain ρ (η c) k) := by
  induction k with
  | zero => exact IsLinComb.zero _ _
  | succ k ih =>
    have h1 := (ih (by omega)).const_mul ρ
    have hmem : (c, k + 1) ∈ univ ×ˢ range (T + 1) := by
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
      omega
    exact h1.add (IsLinComb.of_mem hmem)

end Independent

/-! ### Third and fourth moments of a Gaussian projection -/

section GaussianProjection

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Moments of `gaussianReal 0 1` as standard Gaussian integrals. -/
theorem integral_pow_gaussianReal_zero_one (n : ℕ) :
    ∫ x, x ^ n ∂gaussianReal 0 1 = (√(2 * Real.pi))⁻¹ * ∫ x, x ^ n * Real.exp (-x ^ 2 / 2) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem integral_pow_three_gaussianReal : ∫ x, x ^ 3 ∂gaussianReal 0 1 = 0 := by
  rw [integral_pow_gaussianReal_zero_one, show (3 : ℕ) = 2 * 1 + 1 by norm_num,
    Laplace.OneD.integral_pow_mul_exp_neg_sq_odd 1, mul_zero]

theorem integral_pow_four_gaussianReal : ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  rw [integral_pow_gaussianReal_zero_one, show (4 : ℕ) = 2 * 2 by norm_num,
    Laplace.OneD.integral_pow_mul_exp_neg_sq_half 2]
  have h : √(2 * Real.pi) ≠ 0 := by positivity
  norm_num [Nat.doubleFactorial]
  field_simp

omit [IsProbabilityMeasure P] in
/-- **The projection of a standard Gaussian on a unit vector is a standard real Gaussian.** -/
theorem map_innerSL_eq_gaussianReal {ξ : Ω → E} (hmeas : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian E) {u : E} (hunit : ‖u‖ = 1) :
    P.map (fun ω => innerSL ℝ u (ξ ω)) = gaussianReal 0 1 := by
  have : IsGaussian (P.map ξ) := by rw [hlaw]; infer_instance
  have hX : HasGaussianLaw ξ P := IsGaussian.hasGaussianLaw
  have hL := hX.map_fun (innerSL ℝ u)
  have hmean : P[fun ω => innerSL ℝ u (ξ ω)] = 0 := by
    rw [← integral_map hmeas.aemeasurable (innerSL ℝ u).continuous.aestronglyMeasurable, hlaw]
    exact integral_innerSL_stdGaussian u
  have hvar : Var[fun ω => innerSL ℝ u (ξ ω); P] = 1 := by
    have := variance_map (X := ⇑(innerSL ℝ u)) (μ := P) (Y := ξ)
      (innerSL ℝ u).continuous.measurable.aemeasurable hmeas.aemeasurable
    rw [Function.comp_def] at this
    rw [← this, hlaw, variance_dual_stdGaussian, innerSL_apply_norm, hunit, one_pow]
  have := hL.map_eq_gaussianReal
  rwa [hmean, hvar, Real.toNNReal_one] at this

omit [IsProbabilityMeasure P] in
theorem integral_inner_pow_of_stdGaussian {ξ : Ω → E} (hmeas : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian E) {u : E} (hunit : ‖u‖ = 1) (n : ℕ) :
    ∫ ω, inner ℝ u (ξ ω) ^ n ∂P = ∫ x, x ^ n ∂gaussianReal 0 1 := by
  have hφ : Measurable (fun ω => innerSL ℝ u (ξ ω)) :=
    (innerSL ℝ u).continuous.measurable.comp hmeas
  rw [← map_innerSL_eq_gaussianReal hmeas hlaw hunit,
    integral_map hφ.aemeasurable (measurable_id'.pow_const n).aestronglyMeasurable]
  rfl

omit [IsProbabilityMeasure P] in
theorem memLp_four_inner_of_stdGaussian {ξ : Ω → E} (hmeas : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian E) {u : E} (hunit : ‖u‖ = 1) :
    MemLp (fun ω => inner ℝ u (ξ ω)) 4 P := by
  have hφ : Measurable (fun ω => innerSL ℝ u (ξ ω)) :=
    (innerSL ℝ u).continuous.measurable.comp hmeas
  have h := memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by simp)
  rw [← map_innerSL_eq_gaussianReal hmeas hlaw hunit,
    memLp_map_measure_iff aestronglyMeasurable_id hφ.aemeasurable] at h
  exact h

end GaussianProjection

/-! ### The ULA chain along a unit eigenvector -/

section ULA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [DecidableEq ι] [IsProbabilityMeasure P] in
/-- The projected innovations `√(2h) ⟨u, ξ^c_k⟩` of independent standard Gaussians form a
`FourthMomentTable` with `v = 2h`. -/
theorem fourthMomentTable_projNoise {h : ℝ} (hh : 0 ≤ h) {u : EuclideanSpace ℝ ι}
    (hunit : ‖u‖ = 1) {C : ℕ} (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    FourthMomentTable (fun a : Fin C × ℕ => projNoise h u (ξ a.1) a.2) P (2 * h) where
  memLp a := (memLp_four_inner_of_stdGaussian (hmeas a.1 a.2) (hlaw a.1 a.2) hunit).const_mul _
  meas a := measurable_const.mul ((innerSL ℝ u).continuous.measurable.comp (hmeas a.1 a.2))
  indep := hind.comp (fun _ z => Real.sqrt (2 * h) * inner ℝ u z)
    (fun _ => measurable_const.mul (innerSL ℝ u).continuous.measurable)
  m1 a := integral_projNoise h u (ξ a.1) (hmeas a.1) (hlaw a.1) a.2
  m2 a := by rw [integral_projNoise_sq hh u (ξ a.1) (hmeas a.1) (hlaw a.1) a.2, hunit]; ring
  m3 a := by
    unfold projNoise
    simp only [mul_pow]
    rw [integral_const_mul,
      integral_inner_pow_of_stdGaussian (hmeas a.1 a.2) (hlaw a.1 a.2) hunit 3,
      integral_pow_three_gaussianReal, mul_zero]
  m4 a := by
    unfold projNoise
    simp only [mul_pow]
    rw [integral_const_mul,
      integral_inner_pow_of_stdGaussian (hmeas a.1 a.2) (hlaw a.1 a.2) hunit 4,
      integral_pow_four_gaussianReal,
      show Real.sqrt (2 * h) ^ 4 = (2 * h) ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]]
    ring

/-- **E4 along an eigendirection, exact form.** For the ULA chain along a unit eigenvector `u`
(`Q u = p u`) driven by independent standard Gaussian noise, the variance of the pooled uncentred
second moment of the projections over the draws `b+1, …, b+N` of `C` chains is
`2 s₂²/(C N²) ∑_{i,j<N} (ρ^{|i-j|} - ρ^{2(b+1)+i+j})²` with `ρ = 1 - hp`, `s₂ = 2h/(1-ρ²)`. -/
theorem ula_second_moment_variance {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) {h : ℝ} (hh : 0 ≤ h)
    {u : EuclideanSpace ℝ ι} {p : ℝ} (hu : Q *ᵥ u.ofLp = p • u.ofLp) (hunit : ‖u‖ = 1)
    (hρ : (1 - h * p) ^ 2 ≠ 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ((1 / ((C : ℝ) * N)) *
        ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω) ^ 2) ^ 2 ∂P -
      (∫ ω, (1 / ((C : ℝ) * N)) *
        ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω) ^ 2 ∂P) ^ 2 =
      2 * ((2 * h) / (1 - (1 - h * p) ^ 2)) ^ 2 / (C * N ^ 2) *
        ∑ i ∈ range N, ∑ j ∈ range N,
          ((1 - h * p) ^ Nat.dist i j - (1 - h * p) ^ (2 * (b + 1) + i + j)) ^ 2 := by
  simp_rw [inner_ulaChain_eq_realChain hsym h hu]
  have hT := fourthMomentTable_projNoise hh hunit ξ hmeas hlaw hind
  refine pooled_second_moment_variance hC hN b (1 - h * p) hρ (fun c => projNoise h u (ξ c))
    (fun c k => hT.memLp (c, k))
    (fun c c' j k => by simpa [Prod.ext_iff] using hT.white (c, j) (c', k))
    (isserlisFamily_of_isLinComb hT _ _ (univ ×ˢ range (b + N + 1)) fun a ha => ?_)
  have ha2 : a.2 < N := (Finset.mem_product.mp ha).2 |> Finset.mem_range.mp
  exact isLinComb_realChain (1 - h * p) (fun c => projNoise h u (ξ c)) a.1 (b + N) (b + 1 + a.2)
    (by omega)

/-- **E4 along an eigendirection**: with `0 < hp ≤ 1`, `(1+ρ²)/(1-ρ²) ≤ 1/(hp)`, so the variance of
the pooled uncentred second moment is at most `2 s₂²/(h p C N)`, `s₂ = 2h/(1-(1-hp)²)` the ULA
variance: the relative standard error of a directional variance estimate is at most
`√(2/(h p C N)) = √(τ_flat/(CN))`, the "prefactor set by the autocorrelation times". -/
theorem ula_second_moment_variance_le {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) {h : ℝ} (hh : 0 < h)
    {u : EuclideanSpace ℝ ι} {p : ℝ} (hp : 0 < p) (hhp : h * p ≤ 1)
    (hu : Q *ᵥ u.ofLp = p • u.ofLp) (hunit : ‖u‖ = 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ((1 / ((C : ℝ) * N)) *
        ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω) ^ 2) ^ 2 ∂P -
      (∫ ω, (1 / ((C : ℝ) * N)) *
        ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω) ^ 2 ∂P) ^ 2 ≤
      2 * ((2 * h) / (1 - (1 - h * p) ^ 2)) ^ 2 / (h * p * C * N) := by
  simp_rw [inner_ulaChain_eq_realChain hsym h hu]
  have hT := fourthMomentTable_projNoise hh.le hunit ξ hmeas hlaw hind
  have hhp0 : 0 < h * p := mul_pos hh hp
  have hbound := pooled_second_moment_variance_le hC hN b (ρ := 1 - h * p) (by linarith)
    (by linarith) (fun c => projNoise h u (ξ c)) (fun c k => hT.memLp (c, k))
    (fun c c' j k => by simpa [Prod.ext_iff] using hT.white (c, j) (c', k))
    (isserlisFamily_of_isLinComb hT _ _ (univ ×ˢ range (b + N + 1)) fun a ha => by
      have ha2 : a.2 < N := (Finset.mem_product.mp ha).2 |> Finset.mem_range.mp
      exact isLinComb_realChain (1 - h * p) (fun c => projNoise h u (ξ c)) a.1 (b + N)
        (b + 1 + a.2) (by omega))
  refine hbound.trans ?_
  have h1 : 0 < 1 - (1 - h * p) ^ 2 := by nlinarith
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (1 + (1 - h * p) ^ 2) / (1 - (1 - h * p) ^ 2) ≤ 1 / (h * p) := by
    rw [div_le_div_iff₀ h1 hhp0]
    nlinarith [mul_nonneg hhp0.le (mul_nonneg hhp0.le (sub_nonneg.mpr hhp)),
      mul_nonneg hhp0.le (sub_nonneg.mpr hhp)]
  have hs : 0 ≤ 2 * ((2 * h) / (1 - (1 - h * p) ^ 2)) ^ 2 / (C * N) := by positivity
  calc 2 * ((2 * h) / (1 - (1 - h * p) ^ 2)) ^ 2 * (1 + (1 - h * p) ^ 2) /
        (C * N * (1 - (1 - h * p) ^ 2))
      = 2 * ((2 * h) / (1 - (1 - h * p) ^ 2)) ^ 2 / (C * N) *
          ((1 + (1 - h * p) ^ 2) / (1 - (1 - h * p) ^ 2)) := by
        field_simp
    _ ≤ 2 * ((2 * h) / (1 - (1 - h * p) ^ 2)) ^ 2 / (C * N) * (1 / (h * p)) :=
        mul_le_mul_of_nonneg_left key hs
    _ = 2 * ((2 * h) / (1 - (1 - h * p) ^ 2)) ^ 2 / (h * p * C * N) := by
        field_simp

end ULA

end Laplace.Sampler
