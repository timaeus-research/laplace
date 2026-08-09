/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Decay

/-!
# Anchor cancellation for normalized asymptotic families

The pure asymptotic algebra of the germbij note's one-point
anchoring (Proposition 7.6). Two Laplace families whose normalized
expansions agree are, at the function level, related by a common
scalar gauge `C(t)` up to superpolynomially small error. If one
observable anchors the gauge — its two moments agree exactly while
its reference moment has a positive polynomial lower bound — then
`C ≃ 1`, and the gauge disappears from every other observable whose
reference moment is bounded. The statements here are measure-free:
`SuperPoly` is the "beyond all orders" vocabulary of `Laplace.Decay`,
`C` is an arbitrary function with no regularity whatsoever (it is
never integrated or differentiated), and the Laplace moments enter
only through their asymptotic bounds.
-/

open Asymptotics Filter

namespace Laplace

/-- A function is superpolynomially small at infinity: smaller than
every negative power. This is the "beyond all orders" vocabulary of
`Laplace.Decay`, named. -/
def SuperPoly (f : ℝ → ℝ) : Prop :=
  ∀ N : ℕ, f =o[atTop] fun t : ℝ ↦ t ^ (-(N : ℝ))

/-- **Anchor cancellation**: if `(C - 1) · A` is beyond all orders
and `A` has a positive polynomial lower bound, then `C - 1` is
beyond all orders — dividing by the anchor loses only a polynomial
factor. -/
theorem superPoly_of_mul_anchor {C A : ℝ → ℝ} {κ : ℝ} {n : ℕ}
    (hκ : 0 < κ)
    (hlow : ∀ᶠ t in atTop, κ * t ^ (-(n : ℝ)) ≤ A t)
    (hflat : SuperPoly fun t ↦ (C t - 1) * A t) :
    SuperPoly fun t ↦ C t - 1 := by
  intro N
  rw [isLittleO_iff]
  intro ε hε
  have h := (isLittleO_iff.mp (hflat (N + n))) (mul_pos hε hκ)
  filter_upwards [h, hlow, eventually_gt_atTop (0 : ℝ)]
    with t hft hlt ht0
  have htn : (0 : ℝ) < t ^ (-(n : ℝ)) := Real.rpow_pos_of_pos ht0 _
  have htN : (0 : ℝ) < t ^ (-(N : ℝ)) := Real.rpow_pos_of_pos ht0 _
  have hApos : (0 : ℝ) < A t :=
    lt_of_lt_of_le (mul_pos hκ htn) hlt
  have hsplit : t ^ (-((N + n : ℕ) : ℝ)) =
      t ^ (-(N : ℝ)) * t ^ (-(n : ℝ)) := by
    rw [← Real.rpow_add ht0]
    congr 1
    push_cast
    ring
  rw [Real.norm_eq_abs, abs_mul,
    Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht0 (-((N + n : ℕ) : ℝ))),
    hsplit] at hft
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htN]
  have hchain : |C t - 1| * (κ * t ^ (-(n : ℝ))) ≤
      (ε * t ^ (-(N : ℝ))) * (κ * t ^ (-(n : ℝ))) := by
    calc |C t - 1| * (κ * t ^ (-(n : ℝ)))
        ≤ |C t - 1| * |A t| := by
          rw [abs_of_pos hApos]
          exact mul_le_mul_of_nonneg_left hlt (abs_nonneg _)
      _ ≤ ε * κ * (t ^ (-(N : ℝ)) * t ^ (-(n : ℝ))) := hft
      _ = (ε * t ^ (-(N : ℝ))) * (κ * t ^ (-(n : ℝ))) := by ring
  exact le_of_mul_le_mul_right hchain (mul_pos hκ htn)

/-- **Gauge removal**: a superpolynomially small gauge deviation
disappears against a bounded reference moment. -/
theorem superPoly_sub_of_scalar_gauge {C B J : ℝ → ℝ}
    (hC : SuperPoly fun t ↦ C t - 1)
    (hJ : J =O[atTop] fun _ : ℝ ↦ (1 : ℝ))
    (hprop : SuperPoly fun t ↦ B t - C t * J t) :
    SuperPoly fun t ↦ B t - J t := by
  intro N
  have h2 : (fun t : ℝ ↦ (C t - 1) * J t) =o[atTop]
      fun t : ℝ ↦ t ^ (-(N : ℝ)) := by
    have := (hC N).mul_isBigO hJ
    refine this.congr' (Filter.EventuallyEq.refl _ _) ?_
    filter_upwards with t
    rw [mul_one]
  have hsum := (hprop N).add h2
  refine hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with t
  ring

/-- **Anchored gauge removal, packaged**: one anchoring observable
(exact moment equality plus a positive polynomial lower bound on its
reference moment) forces the common gauge to one, so the moment
difference of every boundedly-referenced observable is beyond all
orders. This is the asymptotic core of germbij Proposition 7.6. -/
theorem anchored_proportionality_remove_scalar
    {C I₁₀ I₂₀ I₁ I₂ : ℝ → ℝ} {κ : ℝ} {n : ℕ}
    (hκ : 0 < κ)
    (hlow : ∀ᶠ t in atTop, κ * t ^ (-(n : ℝ)) ≤ I₁₀ t)
    (hanchor : ∀ᶠ t in atTop, I₂₀ t = I₁₀ t)
    (hprop₀ : SuperPoly fun t ↦ I₂₀ t - C t * I₁₀ t)
    (hprop : SuperPoly fun t ↦ I₂ t - C t * I₁ t)
    (hbounded : I₁ =O[atTop] fun _ : ℝ ↦ (1 : ℝ)) :
    SuperPoly fun t ↦ I₂ t - I₁ t := by
  have hflat : SuperPoly fun t ↦ (C t - 1) * I₁₀ t := by
    intro N
    have heq : (fun t : ℝ ↦ I₂₀ t - C t * I₁₀ t) =ᶠ[atTop]
        fun t : ℝ ↦ -((C t - 1) * I₁₀ t) := by
      filter_upwards [hanchor] with t ht
      rw [ht]
      ring
    have hneg := (hprop₀ N).congr' heq
      (Filter.EventuallyEq.refl _ _)
    have := hneg.neg_left
    refine this.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with t
    ring
  exact superPoly_sub_of_scalar_gauge
    (superPoly_of_mul_anchor hκ hlow hflat) hbounded hprop

end Laplace
