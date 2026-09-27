/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseJourneyResolution

/-!
# Chamber clearance certificates

The resolution theorems carry a **frozen-margin hypothesis**: the frozen Fisher ellipsoid
`{z ∈ W : q_θ(z) < r²}` of the response `θ = θ(m_D)` stays inside the coercive chamber `U` in
mean coordinates. This file discharges it from a genuine geometric clearance.

* **Euclidean clearance discharges the frozen margin** (`frozen_margin_of_euclidean_clearance`): if
  the Euclidean `r`-ball about `m_D` (in the visible directions `W`) lies in the chamber and the
  Fisher form at `θ` is bounded by `Λ`, then the frozen ellipsoid of radius `r/√Λ` lies in the
  chamber, because `‖z‖₂² ≤ Λ q_θ(z)`.
* **The explicit exit bound** (`measureReal_sampleResponse_notMem_fisherBall_le_of_clearance`):
  under Euclidean clearance `r`, coercivity `λ` on the chamber and the bound `Λ` at the response,
  the empirical response leaves the intrinsic Fisher ball of radius `r/√λ` about `θ(m_D)` with
  probability at most `Λ tr(R C_D)/(n r²)` — every hypothesis is a stated geometric quantity.
* **Fisher clearance in coefficient space** (`mem_of_fisherClearance`): if the Fisher `δ`-ball
  about `θ` lies in a coefficient-space chamber and the Fisher form is bounded by `Λ` along
  segments, then `√Λ r < δ` puts the Euclidean `r`-ball in the chamber.

Metric closeness alone does not prove a sign margin: the clearance is assumed, and then converted.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Coefficient

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty J] in
/-- **Fisher clearance in coefficient space**: a chamber containing the Fisher `δ`-ball about `θ`
contains the Euclidean `r`-ball whenever `√Λ r < δ` and the Fisher form is bounded by `Λ` along
segments. -/
theorem mem_of_fisherClearance {𝒞 : Set 𝕍} {θ : 𝕍} {δ : ℝ}
    (hC : ∀ η, fisherDist S ν θ η < δ → η ∈ 𝒞) {Λ r : ℝ} (hΛ0 : 0 ≤ Λ) (hr : 0 ≤ r)
    (hrδ : √Λ * r < δ) {y : 𝕍}
    (hΛ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : J → ℝ,
      fisherVar S ν ((θ + t • (y - θ) : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) w ≤
        Λ * dotJ w w)
    (hy : dotJ ((y - θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)
      ((y - θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) < r ^ 2) :
    y ∈ 𝒞 :=
  hC y (fisherDist_lt_of_dotJ_lt hS ν hΛ0 hr hrδ θ y hΛ hy)

end Coefficient

section Frozen

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **Euclidean clearance discharges the frozen margin**: if the visible Euclidean `r`-ball about
`M` lies in the chamber `U` and the Fisher form at `θ` is bounded by `Λ > 0`, then the frozen
ellipsoid of radius `r/√Λ` lies in `U`. -/
theorem frozen_margin_of_euclidean_clearance {U : Set (J → ℝ)} {M : J → ℝ} {r : ℝ}
    (hclear : ∀ z ∈ 𝕍, dotJ z z < r ^ 2 → M + z ∈ U) (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {Λ : ℝ} (hΛ : 0 < Λ)
    (hΛ' : ∀ w : J → ℝ, fisherVar S ν (θ : J → ℝ) w ≤ Λ * dotJ w w) :
    ∀ z ∈ 𝕍, samplingEnergy hS ν θ p z < (r / √Λ) ^ 2 → M + z ∈ U := by
  intro z hz hlt
  refine hclear z hz ?_
  have h := dotJ_self_le_mul_samplingEnergy hS ν θ p hp hΛ.le hΛ' hz
  have hsq : (r / √Λ) ^ 2 = r ^ 2 / Λ := by
    rw [div_pow, Real.sq_sqrt hΛ.le]
  rw [hsq, lt_div_iff₀ hΛ] at hlt
  linarith

end Frozen

section Exit

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
  {U : Set (J → ℝ)} (hU : Convex ℝ U)
  (hUint : U ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hS hDν hXm hid hlaw hind hU hUint

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The explicit exit bound under Euclidean clearance**: with the visible Euclidean `r`-ball
about `m_D` inside the coercive chamber, coercivity `λ` on the chamber and the Fisher bound `Λ` at
the response, the empirical response leaves the intrinsic Fisher ball of radius `r/√λ` about
`θ(m_D)` with probability at most `Λ tr(R C_D)/(n r²)`. -/
theorem measureReal_sampleResponse_notMem_fisherBall_le_of_clearance {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    (hm : (fun j ↦ ∫ x, S j x ∂D) ∈ U) {Λ : ℝ} (hΛ : 0 < Λ)
    (hΛ' : ∀ w : J → ℝ, fisherVar S ν (θr (fun j ↦ ∫ x, S j x ∂D) : J → ℝ) w ≤ Λ * dotJ w w)
    (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {r : ℝ} (hr : 0 < r)
    (hclear : ∀ z ∈ 𝕍, dotJ z z < r ^ 2 → (fun j ↦ ∫ x, S j x ∂D) + z ∈ U) {n : ℕ} (hn : 0 < n) :
    P.real {ω | sampleResponse S Xs n ω ∉
        {M' | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D)) (θr M') < r / √lam}} ≤
      Λ * (-(∑ a, ∑ b, samplingOp hS ν (θr (fun j ↦ ∫ x, S j x ∂D)) p (Pi.single b 1) a *
        lawCov D (S a) (S b)) / n / r ^ 2) := by
  have hsΛ : 0 < √Λ := Real.sqrt_pos.2 hΛ
  have hr' : 0 < r / √Λ := div_pos hr hsΛ
  have h := measureReal_sampleResponse_notMem_fisherBall_le hS ν P D hDν Xs hXm hid hlaw hind hU
    hUint hlam hcoer hm hΛ hΛ' p hp hr'
    (frozen_margin_of_euclidean_clearance hS ν hclear _ p hp hΛ hΛ') hn
  have e1 : √(Λ / lam) * (r / √Λ) = r / √lam := by
    rw [Real.sqrt_div hΛ.le]
    field_simp
  have e2 : -(∑ a, ∑ b, samplingOp hS ν (θr (fun j ↦ ∫ x, S j x ∂D)) p (Pi.single b 1) a *
      lawCov D (S a) (S b)) / n / (r / √Λ) ^ 2 =
      Λ * (-(∑ a, ∑ b, samplingOp hS ν (θr (fun j ↦ ∫ x, S j x ∂D)) p (Pi.single b 1) a *
        lawCov D (S a) (S b)) / n / r ^ 2) := by
    rw [div_pow, Real.sq_sqrt hΛ.le]
    field_simp
  rw [e1, e2] at h
  exact h

end Exit

end Laplace.Multi
