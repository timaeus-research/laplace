/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ConstrainedLP
import Laplace.Multi.LogCoordinates
import Laplace.Multi.PolytopeFibre

/-!
# The constant-unit model kernel in logarithmic coordinates

Step 1 of the transverse active-truth face theorem (`notes/active_truth_handoff.md`): under
`x = ρ e^{-z}` the constant-unit model integrand on the box with the truth cut becomes
`w₀ ρ^{∑(r+1)} e^{-c·z} e^{-B' e^{-κ·z}}` on the half-space
`Q·z < q log(ρ/D) + γ log t + (∑Q) log ρ` (`modelIntegrand_const_negExp`, `c = r + 1`,
`B' = B t^δ a₀ ρ^{∑κ}`), so the model kernel is
`A t^{-γp} w₀ ρ^{∑(r+1)}` times the orthant integral of that expression
(`modelKernel_const_eq_log`).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- The truth cut in logarithmic coordinates. -/
def logCut (ρ D γ q t : ℝ) (Q : ι → ℝ) : Set (ι → ℝ) :=
  {z | ∑ i, Q i * z i < q * log (ρ / D) + γ * log t + (∑ i, Q i) * log ρ}

/-- The cutoff variable at `ρ e^{-z}`. -/
theorem cutVar_negExp {ρ D γ q t : ℝ} (hρ : 0 < ρ) (Q : ι → ℝ) (z : ι → ℝ) :
    cutVar D γ q Q t (negExpMap ρ z) =
      D * t ^ (-(γ / q)) * (ρ ^ (-(∑ i, Q i) / q) * exp ((∑ i, Q i * z i) / q)) := by
  unfold cutVar negExpMap
  congr 1
  have e : ∀ i, (ρ * exp (-z i)) ^ (-(Q i / q)) = ρ ^ (-(Q i / q)) * exp (Q i * z i / q) := by
    intro i
    rw [Real.mul_rpow hρ.le (exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  simp_rw [e]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.rpow_sum_of_pos hρ]
  congr 2
  · rw [Finset.sum_neg_distrib, ← Finset.sum_div, neg_div]
  · rw [Finset.sum_div]

/-- Membership in the cut: `D t^{-γ/q} ∏ x^{-Q/q} < ρ ↔ Q·z < q log(ρ/D) + γ log t + (∑Q) log ρ`. -/
theorem cutVar_negExp_lt_iff {ρ D γ q t : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (ht : 0 < t)
    (Q : ι → ℝ) (z : ι → ℝ) :
    cutVar D γ q Q t (negExpMap ρ z) < ρ ↔ z ∈ logCut ρ D γ q t Q := by
  rw [cutVar_negExp (D := D) (γ := γ) (t := t) hρ Q z]
  simp only [logCut, Set.mem_ofPred_eq]
  have hpos : 0 < D * t ^ (-(γ / q)) * ρ ^ (-(∑ i, Q i) / q) := by positivity
  rw [← mul_assoc, ← Real.log_lt_log_iff (by positivity) hρ, Real.log_mul hpos.ne' (exp_pos _).ne',
    Real.log_exp, Real.log_mul (by positivity) (rpow_pos_of_pos hρ _).ne',
    Real.log_mul hD.ne' (rpow_pos_of_pos ht _).ne', Real.log_rpow ht, Real.log_rpow hρ,
    Real.log_div hρ.ne' hD.ne']
  have e1 : (-∑ i, Q i) / q * log ρ = -((∑ i, Q i) / q * log ρ) := by ring
  have e2 : -(γ / q) * log t = -(γ / q * log t) := by ring
  have e3 : (log ρ - log D + γ / q * log t + (∑ i, Q i) / q * log ρ) * q =
      q * (log ρ - log D) + γ * log t + (∑ i, Q i) * log ρ := by field_simp
  rw [e1, e2]
  constructor
  · intro h
    have := (div_lt_iff₀ hq).mp (by linarith : (∑ i, Q i * z i) / q < log ρ - log D +
      γ / q * log t + (∑ i, Q i) / q * log ρ)
    rw [e3] at this
    exact this
  · intro h
    have : (∑ i, Q i * z i) / q < log ρ - log D + γ / q * log t + (∑ i, Q i) / q * log ρ := by
      rw [div_lt_iff₀ hq, e3]
      exact h
    linarith

/-- The constant-unit integrand at `ρ e^{-z}`, `z > 0`, with the Jacobian. -/
theorem modelIntegrand_const_negExp {ρ B D γ q δ : ℝ} {Q κ r : ι → ℝ} {w₀ a₀ t : ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (ht : 0 < t) {z : ι → ℝ} (hz : ∀ i, 0 < z i) :
    (∏ i, ρ * exp (-z i)) *
        modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t (negExpMap ρ z) =
      (logCut ρ D γ q t Q).indicator (fun z ↦ w₀ * ρ ^ (∑ i, (r i + 1)) *
        exp (-(∑ i, (r i + 1) * z i)) *
        exp (-(B * t ^ δ * a₀ * ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i))))) z := by
  unfold modelIntegrand modelDomain
  have hbox : negExpMap ρ z ∈ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ := by
    rw [← image_negExpMap_orthant hρ]
    exact ⟨z, fun i _ ↦ hz i, rfl⟩
  by_cases hcut : z ∈ logCut ρ D γ q t Q
  · rw [Set.indicator_of_mem hcut, Set.indicator_of_mem
      (show negExpMap ρ z ∈ (Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ) ∩
        {x | cutVar D γ q Q t x < ρ} from ⟨hbox, (cutVar_negExp_lt_iff hρ hD hq ht Q z).mpr hcut⟩)]
    -- the monomials at ρ e^{-z}
    have er : ∏ i, (negExpMap ρ z) i ^ r i = ρ ^ (∑ i, r i) * exp (-(∑ i, r i * z i)) := by
      simp only [negExpMap]
      have e : ∀ i, (ρ * exp (-z i)) ^ r i = ρ ^ r i * exp (-(r i * z i)) := fun i ↦ by
        rw [Real.mul_rpow hρ.le (exp_pos _).le, ← Real.exp_mul]
        congr 2
        ring
      simp_rw [e]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.rpow_sum_of_pos hρ,
        Finset.sum_neg_distrib]
    have eκ : ∏ i, (negExpMap ρ z) i ^ κ i = ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i)) := by
      simp only [negExpMap]
      have e : ∀ i, (ρ * exp (-z i)) ^ κ i = ρ ^ κ i * exp (-(κ i * z i)) := fun i ↦ by
        rw [Real.mul_rpow hρ.le (exp_pos _).le, ← Real.exp_mul]
        congr 2
        ring
      simp_rw [e]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.rpow_sum_of_pos hρ,
        Finset.sum_neg_distrib]
    have eJ : ∏ i, ρ * exp (-z i) = ρ ^ (Fintype.card ι : ℝ) * exp (-(∑ i, z i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum,
        Finset.sum_neg_distrib, Real.rpow_natCast]
    rw [er, eκ, eJ]
    have e1 : ρ ^ (∑ i, (r i + 1)) = ρ ^ (∑ i, r i) * ρ ^ (Fintype.card ι : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Real.rpow_add hρ]
    have e2 : exp (-(∑ i, (r i + 1) * z i)) = exp (-(∑ i, r i * z i)) * exp (-(∑ i, z i)) := by
      rw [← Real.exp_add]
      congr 1
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
      ring
    rw [e1, e2, show B * t ^ δ * a₀ * (ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i))) =
      B * t ^ δ * a₀ * ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i)) by ring]
    ring
  · rw [Set.indicator_of_notMem hcut, Set.indicator_of_notMem
      (fun h ↦ hcut ((cutVar_negExp_lt_iff hρ hD hq ht Q z).mp h.2)), mul_zero]

/-- **The constant-unit model kernel in logarithmic coordinates.** -/
theorem modelKernel_const_eq_log {ρ A B D γ p q δ : ℝ} {Q κ r : ι → ℝ} {w₀ a₀ t : ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (ht : 0 < t) :
    modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t =
      A * t ^ (-(γ * p)) * (w₀ * ρ ^ (∑ i, (r i + 1)) *
        ∫ z in Set.pi univ (fun _ : ι ↦ Ioi (0 : ℝ)), (logCut ρ D γ q t Q).indicator
          (fun z ↦ exp (-(∑ i, (r i + 1) * z i)) *
            exp (-(B * t ^ δ * a₀ * ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i))))) z) := by
  unfold modelKernel
  have hsupp : ∀ x, modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t x ≠ 0 →
      x ∈ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ := fun x hx ↦ by
    by_contra h
    apply hx
    unfold modelIntegrand
    exact Set.indicator_of_notMem (fun h' ↦ h h'.1) _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
    by_contra h; exact hx (hsupp x h)), integral_box_eq_orthant hρ]
  congr 1
  rw [← integral_const_mul]
  refine setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ : ι ↦ (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))))
    fun z hz ↦ ?_
  rw [modelIntegrand_const_negExp hρ hD hq ht (fun i ↦ (Set.mem_univ_pi.mp hz) i)]
  by_cases hcut : z ∈ logCut ρ D γ q t Q
  · rw [Set.indicator_of_mem hcut, Set.indicator_of_mem hcut]
    ring
  · rw [Set.indicator_of_notMem hcut, Set.indicator_of_notMem hcut, mul_zero]

end Laplace.Multi
