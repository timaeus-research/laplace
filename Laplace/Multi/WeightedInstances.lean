/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedLocalization
import Laplace.OneD.MonomialPotential

/-!
# Instances of the weighted-jet recovery theorem

The hypothesis package of `weightedPolynomial_recovery_of_superPoly` is satisfiable: the
separable even leading part `P w = ∑ i, w i ^ (2 k i)` with integerized weights `a i` such
that `a i · 2 k i = D` is continuous, nonnegative, quasi-homogeneous of degree `D`, coercive
with `κ = 1` (`|w i|^D = (w i^{2k i})^{a i} ≤ P^{a i}`), and `e^{-P}` is integrable as a
product of one-dimensional even-power Gibbs factors. Hence every semi-quasi-homogeneous
polynomial `∑ w i^{2k i} + (higher weighted degree)` is identified by its localized monomial
moments beyond all orders. The concrete case `x⁴ + y⁶` (weights `3, 2`, `D = 12`) is spelled
out.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

namespace IntWeights

variable {ι : Type*} [Fintype ι] (W : IntWeights ι)

/-- The separable even leading part `∑ i, w i ^ (2 k i)`. -/
noncomputable def evenSum (k : ι → ℕ) (w : ι → ℝ) : ℝ := ∑ i, w i ^ (2 * k i)

theorem continuous_evenSum (k : ι → ℕ) : Continuous (evenSum (ι := ι) k) := by
  unfold evenSum
  fun_prop

theorem evenSum_nonneg (k : ι → ℕ) (w : ι → ℝ) : 0 ≤ evenSum k w :=
  Finset.sum_nonneg fun i _ ↦ (even_two_mul (k i)).pow_nonneg (w i)

/-- Quasi-homogeneity of the separable even part when `a i · 2 k i = D`. -/
theorem evenSum_dil {k : ι → ℕ} (hm : ∀ i, W.a i * (2 * k i) = W.D) {ε : ℝ} (_hε : 0 < ε)
    (w : ι → ℝ) : evenSum k (W.dil ε w) = ε ^ W.D * evenSum k w := by
  unfold evenSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dil_apply, mul_pow, ← pow_mul, hm i]

/-- Coercivity with `κ = 1`: `|w i|^D ≤ (evenSum k w)^{a i}`. -/
theorem evenSum_coercive {k : ι → ℕ} (hm : ∀ i, W.a i * (2 * k i) = W.D) (w : ι → ℝ) (i : ι) :
    |w i| ^ W.D ≤ 1 * evenSum k w ^ W.a i := by
  rw [one_mul, ← hm i, mul_comm (W.a i), pow_mul, (even_two_mul (k i)).pow_abs]
  refine pow_le_pow_left₀ ((even_two_mul (k i)).pow_nonneg _) ?_ _
  exact Finset.single_le_sum (f := fun j ↦ w j ^ (2 * k j))
    (fun j _ ↦ (even_two_mul (k j)).pow_nonneg (w j)) (Finset.mem_univ i)

/-- Integrability of `e^{-evenSum}` as a product of one-dimensional Gibbs factors. -/
theorem integrable_exp_neg_evenSum {k : ι → ℕ} (hk : ∀ i, 1 ≤ k i) :
    Integrable fun w : ι → ℝ ↦ Real.exp (-evenSum k w) := by
  have hprod : (fun w : ι → ℝ ↦ Real.exp (-evenSum k w)) =
      fun w ↦ ∏ i, Real.exp (-(w i ^ (2 * k i))) := by
    funext w
    rw [← Real.exp_sum]
    congr 1
    unfold evenSum
    rw [← Finset.sum_neg_distrib]
  rw [hprod]
  have hfactor : ∀ i, Integrable (fun x : ℝ ↦ Real.exp (-(x ^ (2 * k i)))) := by
    intro i
    have hfac : (0 : ℝ) < (Nat.factorial (2 * k i) : ℝ) := by positivity
    have h := OneD.kth_integrable_pow (hk i) 0 hfac
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [pow_zero, one_mul]
    congr 2
    field_simp
  have := Integrable.fintype_prod (𝕜 := ℝ) (f := fun i (x : ℝ) ↦ Real.exp (-(x ^ (2 * k i))))
    (μ := fun _ ↦ (volume : Measure ℝ)) hfactor
  exact this

/-- **Recovery for separable even leading parts**: the polynomials
`∑ i, w i ^ (2 k i) + ∑_{α ∈ S} c_j α w^α` (all `α` of weighted degree `> D`) are identified by
their localized monomial moments beyond all orders, for every sufficiently small sublevel
localization. -/
theorem evenSum_recovery_of_superPoly {k : ι → ℕ} (hk : ∀ i, 1 ≤ k i)
    (hm : ∀ i, W.a i * (2 * k i) = W.D)
    (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (∀ α ∈ S, Laplace.SuperPoly fun t : ℝ ↦
        tempMoment {x : ι → ℝ | evenSum k x ≤ δ} (wLoss (evenSum k) S c₂) (mvMonomial α) t -
          tempMoment {x : ι → ℝ | evenSum k x ≤ δ} (wLoss (evenSum k) S c₁) (mvMonomial α) t) →
      ∀ α ∈ S, c₁ α = c₂ α :=
  W.weightedPolynomial_recovery_of_superPoly (continuous_evenSum k) (evenSum_nonneg k)
    (fun _ hε w ↦ W.evenSum_dil hm hε w) (integrable_exp_neg_evenSum hk) zero_le_one
    (fun w i ↦ W.evenSum_coercive hm w i) S c₁ c₂ hS

/-! ### The concrete case `x⁴ + y⁶` -/

/-- Weights `(3, 2)` with `D = 12`: `x` has weight `1/4`, `y` has weight `1/6`. -/
def quarticSexticWeights : IntWeights (Fin 2) where
  D := 12
  D_pos := by norm_num
  a := ![3, 2]
  a_pos := by decide

theorem quarticSexticWeights_hm : ∀ i, quarticSexticWeights.a i * (2 * (![2, 3] : Fin 2 → ℕ) i) =
    quarticSexticWeights.D := by
  decide

/-- **`x⁴ + y⁶` plus higher weighted-degree terms is identifiable**: for every sufficiently
small sublevel localization, two losses `x⁴ + y⁶ + ∑_{α ∈ S} c_j α x^{α₀} y^{α₁}` with all
`3 α₀ + 2 α₁ > 12` whose localized monomial moments agree beyond all orders in the temperature
have equal coefficients. -/
theorem quarticSextic_recovery_of_superPoly (S : Finset (Fin 2 → ℕ)) (c₁ c₂ : (Fin 2 → ℕ) → ℝ)
    (hS : ∀ α ∈ S, 12 < 3 * α 0 + 2 * α 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (∀ α ∈ S, Laplace.SuperPoly fun t : ℝ ↦
        tempMoment {x : Fin 2 → ℝ | evenSum ![2, 3] x ≤ δ}
          (wLoss (evenSum ![2, 3]) S c₂) (mvMonomial α) t -
        tempMoment {x : Fin 2 → ℝ | evenSum ![2, 3] x ≤ δ}
          (wLoss (evenSum ![2, 3]) S c₁) (mvMonomial α) t) →
      ∀ α ∈ S, c₁ α = c₂ α := by
  refine quarticSexticWeights.evenSum_recovery_of_superPoly (k := ![2, 3]) (by decide)
    quarticSexticWeights_hm S c₁ c₂ fun α hα ↦ ?_
  have h := hS α hα
  change 12 < ∑ i : Fin 2, quarticSexticWeights.a i * α i
  simp [Fin.sum_univ_two, quarticSexticWeights]
  omega

end IntWeights

end Laplace.Multi
