/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Laplace.Grammar.CoeffSpace

/-!
# Convergence in distribution of the canonical coefficients (grammar §4.3, Astra #11 rank 3)

If the random Taylor data `X n : Ω n → CoeffPair` converge in distribution to `Z`, then every
finite vector of canonical coefficients `(A_{α_i}(X n), B_{α_i}(X n))_i` converges in distribution
to the corresponding vector at `Z` (`tendstoInDistribution_coeffVec`), and so do the individual
coefficients (`tendstoInDistribution_coeffA/B`). This is the continuous mapping theorem
(`TendstoInDistribution.continuous_comp`) applied to the continuous maps of unit 146; it is the
`d = 2` chart-level form of the convergence `C_{μ,m}(ξ_n) → C_{μ,m}(G)` asserted in
thm:strataempiricalexpansion. The represented-array form `coeffA_ofPair`/`coeffB_ofPair` rewrites
the conclusions in terms of `canonA`/`canonB` of the amplitude of the random arrays.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter

namespace Laplace.Grammar

theorem coeffA_ofPair (β ρ : ℝ) (hρ : 0 < ρ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) (x y : ℕ × ℕ → ℝ)
    (hx : WSummable ρ x) (hy : WSummable ρ y) :
    coeffA β ρ h₁ h₂ k₁ k₂ α (ofPair ρ hρ x y hx hy)
      = canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) α := by
  unfold coeffA
  rw [toX_ofPair, toY_ofPair]

theorem coeffB_ofPair (β b ρ : ℝ) (hρ : 0 < ρ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) (x y : ℕ × ℕ → ℝ)
    (hx : WSummable ρ x) (hy : WSummable ρ y) :
    coeffB β b ρ h₁ h₂ k₁ k₂ α (ofPair ρ hρ x y hx hy)
      = canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
          (fun i j s => ampCoeff β x y (i, j) s) α := by
  unfold coeffB
  rw [toX_ofPair, toY_ofPair]

/-- The finite vector of canonical coefficients `(A_{α_i}, B_{α_i})_{i < m}`. -/
noncomputable def coeffVec (β b ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) {m : ℕ} (αs : Fin m → ℝ)
    (a : CoeffPair) : Fin m → ℝ × ℝ :=
  fun i => (coeffA β ρ h₁ h₂ k₁ k₂ (αs i) a, coeffB β b ρ h₁ h₂ k₁ k₂ (αs i) a)

theorem continuous_coeffVec (β b ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) {m : ℕ}
    (αs : Fin m → ℝ) (hαs : ∀ i, 0 < αs i) :
    Continuous (coeffVec β b ρ h₁ h₂ k₁ k₂ αs) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  refine continuous_pi fun i => ?_
  exact (continuous_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ (αs i) (hαs i)).prodMk
    (continuous_coeffB β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ (αs i) (hαs i))

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
  [∀ i, IsProbabilityMeasure (μ i)] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
  [IsProbabilityMeasure μ'] {l : Filter ι}

/-- **Convergence in distribution of the log coefficient `A_α`.** -/
theorem tendstoInDistribution_coeffA (β ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hρ : 0 < ρ)
    (hr0 : 0 < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α : ℝ) (hα : 0 < α)
    (X : (i : ι) → Ω i → CoeffPair) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n => coeffA β ρ h₁ h₂ k₁ k₂ α ∘ X n) l
      (coeffA β ρ h₁ h₂ k₁ k₂ α ∘ Z) μ μ' :=
  hX.continuous_comp (continuous_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ α hα)

/-- **Convergence in distribution of the constant coefficient `B_α`.** -/
theorem tendstoInDistribution_coeffB (β b ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α : ℝ) (hα : 0 < α)
    (X : (i : ι) → Ω i → CoeffPair) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n => coeffB β b ρ h₁ h₂ k₁ k₂ α ∘ X n) l
      (coeffB β b ρ h₁ h₂ k₁ k₂ α ∘ Z) μ μ' :=
  hX.continuous_comp (continuous_coeffB β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α hα)

/-- **Joint convergence in distribution of finite coefficient vectors.** -/
theorem tendstoInDistribution_coeffVec (β b ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) {m : ℕ}
    (αs : Fin m → ℝ) (hαs : ∀ i, 0 < αs i) (X : (i : ι) → Ω i → CoeffPair) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n => coeffVec β b ρ h₁ h₂ k₁ k₂ αs ∘ X n) l
      (coeffVec β b ρ h₁ h₂ k₁ k₂ αs ∘ Z) μ μ' :=
  hX.continuous_comp (continuous_coeffVec β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ αs hαs)

/-- Represented-array form: if the random Taylor data are arrays `x n ω, y n ω` with a common
summability radius, the canonical coefficients of the amplitude `η e^{βsξ}` converge in
distribution whenever the lifted data converge in distribution in `CoeffPair`. -/
theorem tendstoInDistribution_canonA_of_arrays (β ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hρ : 0 < ρ) (hr0 : 0 < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α : ℝ) (hα : 0 < α)
    (x y : (i : ι) → Ω i → ℕ × ℕ → ℝ) (hx : ∀ i ω, WSummable ρ (x i ω))
    (hy : ∀ i ω, WSummable ρ (y i ω)) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution (fun i ω => ofPair ρ hρ (x i ω) (y i ω) (hx i ω) (hy i ω)) l Z
      μ μ') :
    TendstoInDistribution
      (fun n ω => canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β (x n ω) (y n ω) (i, j) s) α) l
      (coeffA β ρ h₁ h₂ k₁ k₂ α ∘ Z) μ μ' := by
  have h := tendstoInDistribution_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ α hα _ Z hX
  refine h.congr (fun n => Filter.Eventually.of_forall fun ω => ?_) (Filter.Eventually.of_forall
    fun ω => rfl)
  simp only [Function.comp]
  rw [coeffA_ofPair]

end Laplace.Grammar
