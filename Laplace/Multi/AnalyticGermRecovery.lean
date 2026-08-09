/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.ExpansionBridge

/-!
# The analytic germ corollary

For analytic losses the jet is the germ. This file supplies the
identity-theorem step the germbij Corollary 3.2 needs: two functions
analytic at the minimum with equal iterated derivatives at every
positive order agree modulo an additive constant on a neighborhood
(`analytic_germ_eq_of_jet_eq`), via the diagonal reconstruction of
power-series coefficients from iterated derivatives. Composed with
the expansion bridge, `analytic_germ_recovery_of_superPoly_moments`
states the corollary in the note's own data language: localized
monomial moment families agreeing beyond all orders determine the
germ of an analytic loss at the minimum, modulo the additive
constant the normalization must lose.
-/

open Filter Topology Asymptotics Equiv

namespace Laplace.Multi

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The diagonal of a power-series coefficient is recovered from the
diagonal of the corresponding iterated derivative: on a constant
vector every permutation acts trivially, so the symmetrization sum
collapses to `n!` copies. -/
theorem hasFPowerSeries_diag_eq {f : E → ℝ}
    {p : FormalMultilinearSeries ℝ E ℝ} {r : ENNReal}
    (hf : HasFPowerSeriesOnBall f p 0 r) (n : ℕ) (y : E) :
    p n (fun _ ↦ y) =
      (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n f 0 (fun _ ↦ y) := by
  have hsum := hf.iteratedFDeriv_eq_sum_of_completeSpace
    (v := fun _ : Fin n ↦ y)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hfac : ((n.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  rw [hsum, inv_mul_cancel_left₀ hfac]

/-- **The analytic germ step**: two functions analytic at a point
with equal iterated derivatives at every positive order agree modulo
an additive constant on a neighborhood. -/
theorem analytic_germ_eq_of_jet_eq {f g : E → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0)
    (hjet : ∀ n : ℕ, 0 < n →
      iteratedFDeriv ℝ n f 0 = iteratedFDeriv ℝ n g 0) :
    ∀ᶠ y in 𝓝 (0 : E), f y - f 0 = g y - g 0 := by
  obtain ⟨p, rp, hp⟩ := hf
  obtain ⟨q, rq, hq⟩ := hg
  have hr : (0 : ENNReal) < min rp rq := lt_min hp.r_pos hq.r_pos
  have hball : Metric.eball (0 : E) (min rp rq) ∈ 𝓝 (0 : E) :=
    Metric.eball_mem_nhds _ hr
  filter_upwards [hball] with y hy
  have hyp : y ∈ Metric.eball (0 : E) rp :=
    Metric.eball_subset_eball (min_le_left _ _) hy
  have hyq : y ∈ Metric.eball (0 : E) rq :=
    Metric.eball_subset_eball (min_le_right _ _) hy
  have hsf : HasSum (fun n : ℕ ↦ p n fun _ ↦ y) (f y) := by
    have := hp.hasSum_sub (y := y) (by simpa using hyp)
    simpa using this
  have hsg : HasSum (fun n : ℕ ↦ q n fun _ ↦ y) (g y) := by
    have := hq.hasSum_sub (y := y) (by simpa using hyq)
    simpa using this
  have hdiff := hsf.sub hsg
  have hterm : ∀ n : ℕ, n ≠ 0 →
      (p n fun _ ↦ y) - (q n fun _ ↦ y) = 0 := by
    intro n hn
    rw [hasFPowerSeries_diag_eq hp, hasFPowerSeries_diag_eq hq,
      hjet n (Nat.pos_of_ne_zero hn)]
    ring
  have hsingle : HasSum
      (fun n : ℕ ↦ (p n fun _ ↦ y) - (q n fun _ ↦ y))
      ((p 0 fun _ ↦ y) - (q 0 fun _ ↦ y)) :=
    hasSum_single 0 hterm
  have huniq := hdiff.unique hsingle
  have hp0 : (p 0 fun _ ↦ y) = f 0 := hp.coeff_zero _
  have hq0 : (q 0 fun _ ↦ y) = g 0 := hq.coeff_zero _
  rw [hp0, hq0] at huniq
  linarith

end General

/-! ## Corollary 3.2 in the note's data language -/

namespace HigherLaplaceDomain

variable {d : ℕ} {L₁ L₂ : EuclidD d → ℝ}
  {H : Matrix (Fin d) (Fin d) ℝ}

/-- **The analytic germ corollary** (germbij Corollary 3.2, inverse
direction): for losses analytic at the minimum, localized monomial
moment families agreeing beyond all orders in the temperature
determine the germ modulo the additive constant. -/
theorem analytic_germ_recovery_of_superPoly_moments
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H)
    (hbase : ∀ j < 3,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ k (h2 : 2 < k), ∀ m : Fin k → Fin d,
      Laplace.SuperPoly (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t -
        (B k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t))
    (hL₁ : AnalyticAt ℝ L₁ 0) (hL₂ : AnalyticAt ℝ L₂ 0) :
    ∀ᶠ y in 𝓝 (0 : EuclidD d), L₁ y - L₁ 0 = L₂ y - L₂ 0 := by
  have hjet := smooth_jet_recovery_of_superPoly_moments A B hbase
    hsymm₁ hsymm₂ hdata
  exact analytic_germ_eq_of_jet_eq hL₁ hL₂ fun n _ ↦ hjet n

end HigherLaplaceDomain

end Laplace.Multi
