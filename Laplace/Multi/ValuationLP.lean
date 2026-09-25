/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.CoupledPhaseDiagram

/-!
# The valuation LP: the coupled-limit exponent as a parametric linear programme

In a positive monomial chart the loss of a data distribution approaching a stratum reads
`L_{q(t)}(x) ≍ ∑_j t^{-σ_j} x^{α_j}` with density `x^{b-1} dx`, and the leading order of the
partition function is governed by the chart LP with valuation offsets `σ`:

  `λ(σ) = inf { b·r : r ≥ 0, α_j·r + σ_j ≥ 1 ∀ j }`   (`offsetLP`).

This module records the polyhedral facts about the value function that make the phase diagram
over the data manifold piecewise affine: `λ` is **convex** in `σ` (`offsetLP_convexOn`, from the
joint affinity of the constraints in `(r, σ)`: convex combinations of feasible points are
feasible for the convex combination of offsets) and **antitone** (`offsetLP_antitone`, larger
offsets relax the constraints). The coupled quartic example of `CoupledPhaseDiagram` is the
instance `d = 1`, `α = (4, 2)`, `b = 1`, `σ = (0, σ)`: its LP value is exactly the exponent
`max (1/4, (1 − σ)/2)` of the analytic phase diagram (`offsetLP_quartic`), closing the loop
between the LP and the asymptotics.
-/

open Filter Topology

namespace Laplace.Multi

variable {d N : ℕ}

/-- The feasible polyhedron `P_σ = {r ≥ 0 : α_j·r + σ_j ≥ 1}` of the chart LP. -/
def offsetFeasible (α : Fin N → Fin d → ℝ) (σ : Fin N → ℝ) : Set (Fin d → ℝ) :=
  {r | (∀ i, 0 ≤ r i) ∧ ∀ j, 1 ≤ ∑ i, α j i * r i + σ j}

/-- The LP value `λ(σ) = inf {b·r : r ∈ P_σ}`. -/
noncomputable def offsetLP (α : Fin N → Fin d → ℝ) (b : Fin d → ℝ) (σ : Fin N → ℝ) : ℝ :=
  sInf ((fun r ↦ ∑ i, b i * r i) '' offsetFeasible α σ)

theorem sum_mul_combo (c r₁ r₂ : Fin d → ℝ) (θ₁ θ₂ : ℝ) :
    ∑ i, c i * (θ₁ • r₁ + θ₂ • r₂) i = θ₁ * ∑ i, c i * r₁ i + θ₂ * ∑ i, c i * r₂ i := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem offsetFeasible_convex_combo {α : Fin N → Fin d → ℝ} {σ₁ σ₂ : Fin N → ℝ}
    {r₁ r₂ : Fin d → ℝ} (h₁ : r₁ ∈ offsetFeasible α σ₁) (h₂ : r₂ ∈ offsetFeasible α σ₂) {θ₁ θ₂ : ℝ}
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hθ : θ₁ + θ₂ = 1) :
    θ₁ • r₁ + θ₂ • r₂ ∈ offsetFeasible α (θ₁ • σ₁ + θ₂ • σ₂) := by
  refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hθ₁ (h₁.1 i)) (mul_nonneg hθ₂ (h₂.1 i))
  · rw [sum_mul_combo]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (h₁.2 j) hθ₁, mul_le_mul_of_nonneg_left (h₂.2 j) hθ₂]

theorem offsetLP_nonneg_mem {α : Fin N → Fin d → ℝ} {b : Fin d → ℝ} (hb : ∀ i, 0 ≤ b i)
    {σ : Fin N → ℝ} {x : ℝ} (hx : x ∈ (fun r ↦ ∑ i, b i * r i) '' offsetFeasible α σ) : 0 ≤ x := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hb i) (hr.1 i)

theorem offsetLP_bddBelow {α : Fin N → Fin d → ℝ} {b : Fin d → ℝ} (hb : ∀ i, 0 ≤ b i)
    (σ : Fin N → ℝ) : BddBelow ((fun r ↦ ∑ i, b i * r i) '' offsetFeasible α σ) :=
  ⟨0, fun _ hx ↦ offsetLP_nonneg_mem hb hx⟩

theorem offsetLP_le {α : Fin N → Fin d → ℝ} {b : Fin d → ℝ} (hb : ∀ i, 0 ≤ b i) {σ : Fin N → ℝ}
    {r : Fin d → ℝ} (hr : r ∈ offsetFeasible α σ) : offsetLP α b σ ≤ ∑ i, b i * r i :=
  csInf_le (offsetLP_bddBelow hb σ) ⟨r, hr, rfl⟩

theorem le_offsetLP {α : Fin N → Fin d → ℝ} {b : Fin d → ℝ} {σ : Fin N → ℝ}
    (hne : (offsetFeasible α σ).Nonempty) {x : ℝ}
    (hx : ∀ r ∈ offsetFeasible α σ, x ≤ ∑ i, b i * r i) :
    x ≤ offsetLP α b σ :=
  le_csInf (hne.image _) fun _ ⟨r, hr, hr'⟩ ↦ hr' ▸ hx r hr

/-- **The LP value is antitone in the offsets**: larger `σ` relaxes the constraints. -/
theorem offsetLP_antitone {α : Fin N → Fin d → ℝ} {b : Fin d → ℝ} (hb : ∀ i, 0 ≤ b i)
    (hne : ∀ σ, (offsetFeasible α σ).Nonempty) : Antitone (offsetLP α b) := by
  intro σ₁ σ₂ hσ
  refine le_offsetLP (hne σ₁) fun r hr ↦ offsetLP_le hb ⟨hr.1, fun j ↦ ?_⟩
  linarith [hr.2 j, hσ j]

/-- **The LP value is convex in the offsets**: the phase diagram's exponent is a convex
piecewise affine function of the valuations of the data path. -/
theorem offsetLP_convexOn {α : Fin N → Fin d → ℝ} {b : Fin d → ℝ} (hb : ∀ i, 0 ≤ b i)
    (hne : ∀ σ, (offsetFeasible α σ).Nonempty) : ConvexOn ℝ Set.univ (offsetLP α b) := by
  refine ⟨convex_univ, fun σ₁ _ σ₂ _ θ₁ θ₂ hθ₁ hθ₂ hθ ↦ ?_⟩
  simp only [smul_eq_mul]
  -- for every pair of feasible points the value at the mixture is below the mixed value
  have key : ∀ r₁ ∈ offsetFeasible α σ₁, ∀ r₂ ∈ offsetFeasible α σ₂,
      offsetLP α b (θ₁ • σ₁ + θ₂ • σ₂) ≤ θ₁ * (∑ i, b i * r₁ i) + θ₂ * (∑ i, b i * r₂ i) := by
    intro r₁ h₁ r₂ h₂
    exact (offsetLP_le hb (offsetFeasible_convex_combo h₁ h₂ hθ₁ hθ₂ hθ)).trans_eq
      (sum_mul_combo _ _ _ _ _)
  rcases hθ₁.lt_or_eq with hθ₁ | hθ₁
  · rcases hθ₂.lt_or_eq with hθ₂ | hθ₂
    · -- both weights positive: take the infimum in `r₂`, then in `r₁`
      have step1 : ∀ r₁ ∈ offsetFeasible α σ₁,
          offsetLP α b (θ₁ • σ₁ + θ₂ • σ₂) ≤ θ₁ * (∑ i, b i * r₁ i) + θ₂ * offsetLP α b σ₂ := by
        intro r₁ h₁
        have : (offsetLP α b (θ₁ • σ₁ + θ₂ • σ₂) - θ₁ * (∑ i, b i * r₁ i)) / θ₂ ≤
            offsetLP α b σ₂ := by
          refine le_offsetLP (hne σ₂) fun r₂ h₂ ↦ ?_
          rw [div_le_iff₀ hθ₂]
          linarith [key r₁ h₁ r₂ h₂]
        rw [div_le_iff₀ hθ₂] at this
        linarith
      have : (offsetLP α b (θ₁ • σ₁ + θ₂ • σ₂) - θ₂ * offsetLP α b σ₂) / θ₁ ≤ offsetLP α b σ₁ := by
        refine le_offsetLP (hne σ₁) fun r₁ h₁ ↦ ?_
        rw [div_le_iff₀ hθ₁]
        linarith [step1 r₁ h₁]
      rw [div_le_iff₀ hθ₁] at this
      linarith
    · subst hθ₂
      have h1 : θ₁ = 1 := by linarith
      subst h1
      simp
  · subst hθ₁
    have h2 : θ₂ = 1 := by linarith
    subst h2
    simp

/-! ### The quartic instance -/

/-- The chart data of the coupled quartic example: `α = (4, 2)`, `b = 1`, `σ = (0, σ)`. -/
theorem offsetLP_quartic (σ : ℝ) :
    offsetLP (![![4], ![2]] : Fin 2 → Fin 1 → ℝ) (![1] : Fin 1 → ℝ) ![0, σ] =
      coupledExponent σ := by
  have himage : (fun r : Fin 1 → ℝ ↦ ∑ i, (![1] : Fin 1 → ℝ) i * r i) ''
      offsetFeasible (![![4], ![2]] : Fin 2 → Fin 1 → ℝ) ![0, σ] = Set.Ici (coupledExponent σ) := by
    ext x
    constructor
    · rintro ⟨r, ⟨hr0, hr⟩, rfl⟩
      have h1 := hr 0
      have h2 := hr 1
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, one_mul] at h1 h2 ⊢
      rw [Set.mem_Ici, coupledExponent, max_le_iff]
      constructor <;> linarith
    · intro hx
      rw [Set.mem_Ici, coupledExponent, max_le_iff] at hx
      refine ⟨fun _ ↦ x, ⟨fun _ ↦ by linarith [hx.1], fun j ↦ ?_⟩, by simp⟩
      fin_cases j <;> simp <;> linarith [hx.1, hx.2]
  unfold offsetLP
  rw [himage, csInf_Ici]

end Laplace.Multi
