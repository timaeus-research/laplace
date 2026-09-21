/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.EstimatorVariance

/-!
# The four-way Isserlis identity for linear combinations of independent innovations

For independent innovations `gᵢ` with the centred moment table `(0, v, 0, 3v²)` (a
`FourthMomentTable`) and finite linear combinations `X = ∑ aᵢ gᵢ`, `Y = ∑ bᵢ gᵢ`, `Z = ∑ cᵢ gᵢ`,
`W = ∑ dᵢ gᵢ`,

`E[X Y Z W] = v² (⟨a,b⟩⟨c,d⟩ + ⟨a,c⟩⟨b,d⟩ + ⟨a,d⟩⟨b,c⟩)`   (`integral_linComb_four`),

by induction on the index set, the quadruple `(X, Y, Z, W)` being independent of the new
innovation; hence the covariance of two products,

`E[(XY)(ZW)] - E[XY] E[ZW] = v² (⟨a,c⟩⟨b,d⟩ + ⟨a,d⟩⟨b,c⟩)`   (`cov_linComb_mul_mul`).

This is the probabilistic core of the Sanity on Sampling note's E4 claim about the *whole*
covariance ("the covariance error follows `√(d/(CN))` with a prefactor set by the autocorrelation
times"): the per-entry variance of the pooled second-moment matrix of a Gaussian chain is a sum of
such terms. The two-way identity `∫ X² Y²` of `EstimatorVariance` is the diagonal case.
-/

open MeasureTheory ProbabilityTheory Finset

namespace Laplace.Sampler

section Wick4

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {κ : Type*}

omit [IsProbabilityMeasure P] in
/-- **Block independence**: any measurable function of the block `(gᵢ)_{i∈s}` is independent of
`gₙ` for `n ∉ s`. -/
theorem indepFun_block_of_notMem {g : κ → Ω → ℝ} (hind : iIndepFun g P)
    (hmeas : ∀ i, Measurable (g i)) {s : Finset κ} {n : κ} (hn : n ∉ s) {β : Type*}
    [MeasurableSpace β] {F : (s → ℝ) → β} (hF : Measurable F) :
    IndepFun (fun ω => F fun i : s => g i ω) (g n) P := by
  have h := hind.indepFun_finset s {n} (Finset.disjoint_singleton_right.mpr hn) hmeas
  have hG : Measurable (fun z : ({n} : Finset κ) → ℝ => z ⟨n, Finset.mem_singleton_self n⟩) :=
    measurable_pi_apply _
  exact h.comp hF hG

omit [IsProbabilityMeasure P] in
/-- The quadruple `((X, Y), (Z, W))` of linear combinations over `s` is independent of `gₙ`. -/
theorem indepFun_quad_of_isLinComb {g : κ → Ω → ℝ} (hind : iIndepFun g P)
    (hmeas : ∀ i, Measurable (g i)) {s : Finset κ} {n : κ} (hn : n ∉ s) {X Y Z W : Ω → ℝ}
    (hX : IsLinComb g s X) (hY : IsLinComb g s Y) (hZ : IsLinComb g s Z) (hW : IsLinComb g s W) :
    IndepFun (fun ω => ((X ω, Y ω), (Z ω, W ω))) (g n) P := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  obtain ⟨c, hc⟩ := hZ
  obtain ⟨d, hd⟩ := hW
  have hF : Measurable (fun z : s → ℝ =>
      ((∑ i : s, a i * z i, ∑ i : s, b i * z i), (∑ i : s, c i * z i, ∑ i : s, d i * z i))) := by
    fun_prop
  convert indepFun_block_of_notMem hind hmeas hn hF using 1
  funext ω
  simp only [ha, hb, hc, hd]
  rw [Finset.sum_coe_sort s (fun i => a i * g i ω), Finset.sum_coe_sort s (fun i => b i * g i ω),
    Finset.sum_coe_sort s (fun i => c i * g i ω), Finset.sum_coe_sort s (fun i => d i * g i ω)]

omit [IsProbabilityMeasure P] in
/-- **Factorisation**: `E[φ(X, Y, Z, W) gₙᵏ] = E[φ(X, Y, Z, W)] E[gₙᵏ]`. -/
theorem integral_quad_mul_pow_of_isLinComb {g : κ → Ω → ℝ} {v : ℝ} (hT : FourthMomentTable g P v)
    {s : Finset κ} {n : κ} (hn : n ∉ s) {X Y Z W : Ω → ℝ} (hX : IsLinComb g s X)
    (hY : IsLinComb g s Y) (hZ : IsLinComb g s Z) (hW : IsLinComb g s W)
    (φ : (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hφ : Measurable φ) (k : ℕ) :
    ∫ ω, φ ((X ω, Y ω), (Z ω, W ω)) * g n ω ^ k ∂P =
      (∫ ω, φ ((X ω, Y ω), (Z ω, W ω)) ∂P) * ∫ ω, g n ω ^ k ∂P := by
  have h := (indepFun_quad_of_isLinComb hT.indep hT.meas hn hX hY hZ hW).comp hφ
    (measurable_id.pow_const k)
  exact h.integral_fun_mul_eq_mul_integral
    (hφ.comp (((measurable_of_isLinComb hT.meas hX).prodMk
      (measurable_of_isLinComb hT.meas hY)).prodMk
      ((measurable_of_isLinComb hT.meas hZ).prodMk
        (measurable_of_isLinComb hT.meas hW)))).aestronglyMeasurable
    ((hT.meas n).pow_const k).aestronglyMeasurable

omit [IsProbabilityMeasure P] in
theorem integrable_mul_mul_mul_pow_one {f g k l : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P)
    (hk : MemLp k 4 P) (hl : MemLp l 4 P) :
    Integrable (fun ω => f ω * g ω * k ω * l ω ^ 1) P := by
  simpa only [pow_one, mul_assoc] using integrable_mul_mul_mul_of_memLp_four hf hg hk hl

omit [IsProbabilityMeasure P] in
theorem integrable_mul_mul_pow_two {f g l : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P)
    (hl : MemLp l 4 P) : Integrable (fun ω => f ω * g ω * l ω ^ 2) P := by
  simpa only [sq, mul_assoc] using integrable_mul_mul_mul_of_memLp_four hf hg hl hl

omit [IsProbabilityMeasure P] in
theorem integrable_mul_pow_three {f l : Ω → ℝ} (hf : MemLp f 4 P) (hl : MemLp l 4 P) :
    Integrable (fun ω => f ω * l ω ^ 3) P := by
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using
    integrable_mul_mul_mul_of_memLp_four hf hl hl hl

omit [IsProbabilityMeasure P] in
theorem integrable_pow_four {l : Ω → ℝ} (hl : MemLp l 4 P) :
    Integrable (fun ω => l ω ^ 4) P := by
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using
    integrable_mul_mul_mul_of_memLp_four hl hl hl hl

/-- **The four-way Isserlis identity for linear combinations**:
`E[X Y Z W] = v² (⟨a,b⟩⟨c,d⟩ + ⟨a,c⟩⟨b,d⟩ + ⟨a,d⟩⟨b,c⟩)`. -/
theorem integral_linComb_four {g : κ → Ω → ℝ} {v : ℝ} (hT : FourthMomentTable g P v)
    (s : Finset κ) (a b c d : κ → ℝ) :
    ∫ ω, (∑ i ∈ s, a i * g i ω) * (∑ i ∈ s, b i * g i ω) *
        ((∑ i ∈ s, c i * g i ω) * (∑ i ∈ s, d i * g i ω)) ∂P =
      v ^ 2 * ((∑ i ∈ s, a i * b i) * (∑ i ∈ s, c i * d i) +
        (∑ i ∈ s, a i * c i) * (∑ i ∈ s, b i * d i) +
        (∑ i ∈ s, a i * d i) * (∑ i ∈ s, b i * c i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    obtain ⟨X, hXd⟩ : ∃ X : Ω → ℝ, X = fun ω => ∑ i ∈ s, a i * g i ω := ⟨_, rfl⟩
    obtain ⟨Y, hYd⟩ : ∃ Y : Ω → ℝ, Y = fun ω => ∑ i ∈ s, b i * g i ω := ⟨_, rfl⟩
    obtain ⟨Z, hZd⟩ : ∃ Z : Ω → ℝ, Z = fun ω => ∑ i ∈ s, c i * g i ω := ⟨_, rfl⟩
    obtain ⟨W, hWd⟩ : ∃ W : Ω → ℝ, W = fun ω => ∑ i ∈ s, d i * g i ω := ⟨_, rfl⟩
    have hXl : IsLinComb g s X := ⟨a, fun ω => by rw [hXd]⟩
    have hYl : IsLinComb g s Y := ⟨b, fun ω => by rw [hYd]⟩
    have hZl : IsLinComb g s Z := ⟨c, fun ω => by rw [hZd]⟩
    have hWl : IsLinComb g s W := ⟨d, fun ω => by rw [hWd]⟩
    have hX4 := memLp_of_isLinComb hT.memLp hXl
    have hY4 := memLp_of_isLinComb hT.memLp hYl
    have hZ4 := memLp_of_isLinComb hT.memLp hZl
    have hW4 := memLp_of_isLinComb hT.memLp hWl
    have hG4 := hT.memLp n
    set α := a n with hα
    set β := b n with hβ
    set γ := c n with hγ
    set δ := d n with hδ
    have hexp : (fun ω => (α * g n ω + ∑ i ∈ s, a i * g i ω) * (β * g n ω + ∑ i ∈ s, b i * g i ω) *
        ((γ * g n ω + ∑ i ∈ s, c i * g i ω) * (δ * g n ω + ∑ i ∈ s, d i * g i ω))) =
        (fun ω => X ω * Y ω * (Z ω * W ω)) +
        ((fun ω => α * (Y ω * Z ω * W ω * g n ω ^ 1)) +
          (fun ω => β * (X ω * Z ω * W ω * g n ω ^ 1)) +
          (fun ω => γ * (X ω * Y ω * W ω * g n ω ^ 1)) +
          (fun ω => δ * (X ω * Y ω * Z ω * g n ω ^ 1))) +
        ((fun ω => α * β * (Z ω * W ω * g n ω ^ 2)) +
          (fun ω => α * γ * (Y ω * W ω * g n ω ^ 2)) +
          (fun ω => α * δ * (Y ω * Z ω * g n ω ^ 2)) +
          (fun ω => β * γ * (X ω * W ω * g n ω ^ 2)) +
          (fun ω => β * δ * (X ω * Z ω * g n ω ^ 2)) +
          (fun ω => γ * δ * (X ω * Y ω * g n ω ^ 2))) +
        ((fun ω => α * β * γ * (W ω * g n ω ^ 3)) +
          (fun ω => α * β * δ * (Z ω * g n ω ^ 3)) +
          (fun ω => α * γ * δ * (Y ω * g n ω ^ 3)) +
          (fun ω => β * γ * δ * (X ω * g n ω ^ 3))) +
        (fun ω => α * β * γ * δ * g n ω ^ 4) := by
      funext ω
      simp only [Pi.add_apply, hXd, hYd, hZd, hWd]
      ring
    have h0 : Integrable (fun ω => X ω * Y ω * (Z ω * W ω)) P :=
      integrable_mul_mul_mul_of_memLp_four hX4 hY4 hZ4 hW4
    have h1a : Integrable (fun ω => α * (Y ω * Z ω * W ω * g n ω ^ 1)) P :=
      (integrable_mul_mul_mul_pow_one hY4 hZ4 hW4 hG4).const_mul _
    have h1b : Integrable (fun ω => β * (X ω * Z ω * W ω * g n ω ^ 1)) P :=
      (integrable_mul_mul_mul_pow_one hX4 hZ4 hW4 hG4).const_mul _
    have h1c : Integrable (fun ω => γ * (X ω * Y ω * W ω * g n ω ^ 1)) P :=
      (integrable_mul_mul_mul_pow_one hX4 hY4 hW4 hG4).const_mul _
    have h1d : Integrable (fun ω => δ * (X ω * Y ω * Z ω * g n ω ^ 1)) P :=
      (integrable_mul_mul_mul_pow_one hX4 hY4 hZ4 hG4).const_mul _
    have h2a : Integrable (fun ω => α * β * (Z ω * W ω * g n ω ^ 2)) P :=
      (integrable_mul_mul_pow_two hZ4 hW4 hG4).const_mul _
    have h2b : Integrable (fun ω => α * γ * (Y ω * W ω * g n ω ^ 2)) P :=
      (integrable_mul_mul_pow_two hY4 hW4 hG4).const_mul _
    have h2c : Integrable (fun ω => α * δ * (Y ω * Z ω * g n ω ^ 2)) P :=
      (integrable_mul_mul_pow_two hY4 hZ4 hG4).const_mul _
    have h2d : Integrable (fun ω => β * γ * (X ω * W ω * g n ω ^ 2)) P :=
      (integrable_mul_mul_pow_two hX4 hW4 hG4).const_mul _
    have h2e : Integrable (fun ω => β * δ * (X ω * Z ω * g n ω ^ 2)) P :=
      (integrable_mul_mul_pow_two hX4 hZ4 hG4).const_mul _
    have h2f : Integrable (fun ω => γ * δ * (X ω * Y ω * g n ω ^ 2)) P :=
      (integrable_mul_mul_pow_two hX4 hY4 hG4).const_mul _
    have h3a : Integrable (fun ω => α * β * γ * (W ω * g n ω ^ 3)) P :=
      (integrable_mul_pow_three hW4 hG4).const_mul _
    have h3b : Integrable (fun ω => α * β * δ * (Z ω * g n ω ^ 3)) P :=
      (integrable_mul_pow_three hZ4 hG4).const_mul _
    have h3c : Integrable (fun ω => α * γ * δ * (Y ω * g n ω ^ 3)) P :=
      (integrable_mul_pow_three hY4 hG4).const_mul _
    have h3d : Integrable (fun ω => β * γ * δ * (X ω * g n ω ^ 3)) P :=
      (integrable_mul_pow_three hX4 hG4).const_mul _
    have h4 : Integrable (fun ω => α * β * γ * δ * g n ω ^ 4) P :=
      (integrable_pow_four hG4).const_mul _
    have h1 := ((h1a.add h1b).add h1c).add h1d
    have h2 := ((((h2a.add h2b).add h2c).add h2d).add h2e).add h2f
    have h3 := ((h3a.add h3b).add h3c).add h3d
    rw [hexp, integral_add' (((h0.add h1).add h2).add h3) h4,
      integral_add' ((h0.add h1).add h2) h3, integral_add' (h0.add h1) h2, integral_add' h0 h1,
      integral_add' ((h1a.add h1b).add h1c) h1d, integral_add' (h1a.add h1b) h1c,
      integral_add' h1a h1b, integral_add' ((((h2a.add h2b).add h2c).add h2d).add h2e) h2f,
      integral_add' (((h2a.add h2b).add h2c).add h2d) h2e,
      integral_add' ((h2a.add h2b).add h2c) h2d, integral_add' (h2a.add h2b) h2c,
      integral_add' h2a h2b,
      integral_add' ((h3a.add h3b).add h3c) h3d, integral_add' (h3a.add h3b) h3c,
      integral_add' h3a h3b]
    simp only [integral_const_mul]
    rw [integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.2 * p.2.1 * p.2.2) (by fun_prop) 1,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1 * p.2.1 * p.2.2) (by fun_prop) 1,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1 * p.1.2 * p.2.2) (by fun_prop) 1,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1 * p.1.2 * p.2.1) (by fun_prop) 1,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.1 * p.2.2) (by fun_prop) 2,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.2 * p.2.2) (by fun_prop) 2,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.2 * p.2.1) (by fun_prop) 2,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1 * p.2.2) (by fun_prop) 2,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1 * p.2.1) (by fun_prop) 2,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1 * p.1.2) (by fun_prop) 2,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.2) (by fun_prop) 3,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.1) (by fun_prop) 3,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.2) (by fun_prop) 3,
      integral_quad_mul_pow_of_isLinComb hT hn hXl hYl hZl hWl
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1) (by fun_prop) 3]
    simp only [pow_one]
    rw [hT.m1 n, hT.m2 n, hT.m3 n, hT.m4 n]
    have hXYZW : ∫ ω, X ω * Y ω * (Z ω * W ω) ∂P =
        v ^ 2 * ((∑ i ∈ s, a i * b i) * (∑ i ∈ s, c i * d i) +
          (∑ i ∈ s, a i * c i) * (∑ i ∈ s, b i * d i) +
          (∑ i ∈ s, a i * d i) * (∑ i ∈ s, b i * c i)) := by
      rw [← ih]
      congr 1
      funext ω
      simp only [hXd, hYd, hZd, hWd]
    have hpair : ∀ (U V : Ω → ℝ) (u w : κ → ℝ), U = (fun ω => ∑ i ∈ s, u i * g i ω) →
        V = (fun ω => ∑ i ∈ s, w i * g i ω) → ∫ ω, U ω * V ω ∂P = v * ∑ i ∈ s, u i * w i := by
      intro U V u w hU hV
      rw [← integral_linComb_mul hT s u w]
      congr 1
      funext ω
      simp only [hU, hV]
    rw [hXYZW, hpair Z W c d hZd hWd, hpair Y W b d hYd hWd, hpair Y Z b c hYd hZd,
      hpair X W a d hXd hWd, hpair X Z a c hXd hZd, hpair X Y a b hXd hYd]
    ring

/-- **The covariance of two products** of linear combinations:
`E[(XY)(ZW)] - E[XY] E[ZW] = v² (⟨a,c⟩⟨b,d⟩ + ⟨a,d⟩⟨b,c⟩)`. -/
theorem cov_linComb_mul_mul {g : κ → Ω → ℝ} {v : ℝ} (hT : FourthMomentTable g P v) (s : Finset κ)
    (a b c d : κ → ℝ) :
    ∫ ω, (∑ i ∈ s, a i * g i ω) * (∑ i ∈ s, b i * g i ω) *
        ((∑ i ∈ s, c i * g i ω) * (∑ i ∈ s, d i * g i ω)) ∂P -
      (∫ ω, (∑ i ∈ s, a i * g i ω) * (∑ i ∈ s, b i * g i ω) ∂P) *
        ∫ ω, (∑ i ∈ s, c i * g i ω) * (∑ i ∈ s, d i * g i ω) ∂P =
      v ^ 2 * ((∑ i ∈ s, a i * c i) * (∑ i ∈ s, b i * d i) +
        (∑ i ∈ s, a i * d i) * (∑ i ∈ s, b i * c i)) := by
  rw [integral_linComb_four hT s a b c d, integral_linComb_mul hT s a b,
    integral_linComb_mul hT s c d]
  ring

/-- **Isserlis in moment form**: for linear combinations `X, Y, Z, W` of the innovations,
`E[XYZW] = E[XY] E[ZW] + E[XZ] E[YW] + E[XW] E[YZ]`. -/
theorem integral_four_of_isLinComb {g : κ → Ω → ℝ} {v : ℝ} (hT : FourthMomentTable g P v)
    {s : Finset κ} {X Y Z W : Ω → ℝ} (hX : IsLinComb g s X) (hY : IsLinComb g s Y)
    (hZ : IsLinComb g s Z) (hW : IsLinComb g s W) :
    ∫ ω, X ω * Y ω * (Z ω * W ω) ∂P =
      (∫ ω, X ω * Y ω ∂P) * (∫ ω, Z ω * W ω ∂P) + (∫ ω, X ω * Z ω ∂P) * (∫ ω, Y ω * W ω ∂P) +
        (∫ ω, X ω * W ω ∂P) * (∫ ω, Y ω * Z ω ∂P) := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  obtain ⟨c, hc⟩ := hZ
  obtain ⟨d, hd⟩ := hW
  simp only [funext ha, funext hb, funext hc, funext hd]
  rw [integral_linComb_four hT s a b c d, integral_linComb_mul hT s a b,
    integral_linComb_mul hT s c d, integral_linComb_mul hT s a c, integral_linComb_mul hT s b d,
    integral_linComb_mul hT s a d, integral_linComb_mul hT s b c]
  ring

/-- **The covariance of two products in moment form**:
`E[(XY)(ZW)] - E[XY] E[ZW] = E[XZ] E[YW] + E[XW] E[YZ]`. -/
theorem cov_mul_mul_of_isLinComb {g : κ → Ω → ℝ} {v : ℝ} (hT : FourthMomentTable g P v)
    {s : Finset κ} {X Y Z W : Ω → ℝ} (hX : IsLinComb g s X) (hY : IsLinComb g s Y)
    (hZ : IsLinComb g s Z) (hW : IsLinComb g s W) :
    ∫ ω, X ω * Y ω * (Z ω * W ω) ∂P - (∫ ω, X ω * Y ω ∂P) * (∫ ω, Z ω * W ω ∂P) =
      (∫ ω, X ω * Z ω ∂P) * (∫ ω, Y ω * W ω ∂P) + (∫ ω, X ω * W ω ∂P) * (∫ ω, Y ω * Z ω ∂P) := by
  rw [integral_four_of_isLinComb hT hX hY hZ hW]
  ring

end Wick4

end Laplace.Sampler
