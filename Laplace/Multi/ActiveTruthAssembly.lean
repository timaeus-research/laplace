/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthModel
import Laplace.Multi.LintegralChange

/-!
# The transverse coordinates of an active-truth face

Step 2 of the transverse active-truth face theorem (`notes/active_truth_handoff.md`), on the index
`Fin k ⊕ Fin 2` with the two solved coordinates last. The transverse matrix
`M = [[κ_a, κ_b], [−Q_a, −Q_b]]` (`transMat`) and the shift `(κ'·z' − δL, γL − Q'·z')`
(`transShift`) turn the solved pair `y` into `v = (s, h) = My + shift(z')` with
`κ·z = s + δL`, `Q·z = γL − h` (`transMat_mulVec_add_shift`). The inner integral over `y` of the
log-form integrand becomes `|det M|⁻¹` times an integral over `v` of the factor
`1_{h > h₀} e^{-βs − ηh − mL} e^{-c₀ e^{-s}}` times the indicator of the image of the orthant
(`lintegral_inner_subst`): the `t`-dependence is now only in `e^{-mL}` and in the fibre set.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-- Sums over `Fin k ⊕ Fin 2` split into the free and the solved parts. -/
theorem sum_elim_mul (f : Fin k ⊕ Fin 2 → ℝ) (z' : Fin k → ℝ) (y : Fin 2 → ℝ) :
    ∑ i, f i * Sum.elim z' y i = ∑ j, f (Sum.inl j) * z' j + ∑ j, f (Sum.inr j) * y j := by
  rw [Fintype.sum_sum_type]
  rfl

/-- The transverse matrix `[[κ_a, κ_b], [−Q_a, −Q_b]]`. -/
def transMat (κ Q : Fin k ⊕ Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![fun j ↦ κ (Sum.inr j), fun j ↦ -Q (Sum.inr j)]

theorem transMat_det (κ Q : Fin k ⊕ Fin 2 → ℝ) :
    (transMat κ Q).det =
      -(κ (Sum.inr 0) * Q (Sum.inr 1) - κ (Sum.inr 1) * Q (Sum.inr 0)) := by
  rw [Matrix.det_fin_two]
  simp [transMat]
  ring

/-- The affine map `y ↦ My + b` is injective for `det M ≠ 0`. -/
theorem injective_mulVec_add {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) (b : Fin 2 → ℝ) :
    Function.Injective fun y : Fin 2 → ℝ ↦ M *ᵥ y + b := by
  intro y₁ y₂ h
  have h' := congrArg (fun v ↦ M⁻¹ *ᵥ (v - b)) h
  simp only [add_sub_cancel_right, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec] at h'
  exact h'

/-- The image of the open orthant under `y ↦ My + b` is the preimage of the orthant under the
inverse affine map, hence measurable. -/
theorem image_mulVec_add_orthant {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0)
    (b : Fin 2 → ℝ) :
    (fun y : Fin 2 → ℝ ↦ M *ᵥ y + b) '' {y | ∀ j, 0 < y j} =
      (fun v : Fin 2 → ℝ ↦ M⁻¹ *ᵥ (v - b)) ⁻¹' {y | ∀ j, 0 < y j} := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [mem_preimage, add_sub_cancel_right, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
    exact hy
  · intro hv
    refine ⟨M⁻¹ *ᵥ (v - b), hv, ?_⟩
    simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec, sub_add_cancel]

theorem measurableSet_image_mulVec_add_orthant {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0)
    (b : Fin 2 → ℝ) :
    MeasurableSet ((fun y : Fin 2 → ℝ ↦ M *ᵥ y + b) '' {y | ∀ j, 0 < y j}) := by
  rw [image_mulVec_add_orthant hM]
  have hS : MeasurableSet {y : Fin 2 → ℝ | ∀ j, 0 < y j} := by
    have : {y : Fin 2 → ℝ | ∀ j, 0 < y j} = Set.pi univ fun _ ↦ Ioi (0 : ℝ) := by
      ext y
      simp only [Set.mem_univ_pi, mem_Ioi, Set.mem_ofPred_eq]
    rw [this]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioi
  exact hS.preimage ((Matrix.toLin' M⁻¹).toContinuousLinearMap.continuous.measurable.comp
    (measurable_id.sub_const b))

theorem transMat_mulVec (κ Q : Fin k ⊕ Fin 2 → ℝ) (y : Fin 2 → ℝ) :
    transMat κ Q *ᵥ y = ![∑ j, κ (Sum.inr j) * y j, -∑ j, Q (Sum.inr j) * y j] := by
  ext i
  fin_cases i <;> simp [transMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The shift `(κ'·z' − δL, γL − Q'·z')`. -/
def transShift (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L : ℝ) (z' : Fin k → ℝ) : Fin 2 → ℝ :=
  ![∑ j, κ (Sum.inl j) * z' j - δ * L, γ * L - ∑ j, Q (Sum.inl j) * z' j]

/-- `M y + shift(z') = (κ·z − δL, γL − Q·z)` for `z = (z', y)`. -/
theorem transMat_mulVec_add_shift (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L : ℝ) (z' : Fin k → ℝ)
    (y : Fin 2 → ℝ) :
    transMat κ Q *ᵥ y + transShift κ Q δ γ L z' =
      ![∑ i, κ i * Sum.elim z' y i - δ * L, γ * L - ∑ i, Q i * Sum.elim z' y i] := by
  rw [transMat_mulVec, sum_elim_mul, sum_elim_mul]
  ext i
  fin_cases i <;> simp [transShift] <;> ring

/-- The integrand in the transverse coordinates `v = (s, h)`: the truth cut `h > h₀`, the
weight `e^{-βs − ηh − mL}`, the Boltzmann factor `e^{-c₀ e^{-s}}`, and the orthant conditions on
`z'` and on the solved pair (as the image of the orthant under `y ↦ My + shift(z')`). -/
noncomputable def innerKv (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L β η mL c₀ h₀ : ℝ) (z' : Fin k → ℝ)
    (v : Fin 2 → ℝ) : ℝ≥0∞ :=
  {z' : Fin k → ℝ | ∀ j, 0 < z' j}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z' *
    ((fun y ↦ transMat κ Q *ᵥ y + transShift κ Q δ γ L z') ''
      {y : Fin 2 → ℝ | ∀ j, 0 < y j}).indicator (fun _ ↦ (1 : ℝ≥0∞)) v *
    (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
    ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + mL)) * exp (-(c₀ * exp (-v 0))))

/-- The log-form integrand of the constant-unit kernel, in `lintegral` form, at `z = (z', y)`. -/
noncomputable def logIntegrand (ρ D γ q t : ℝ) (Q c κ : Fin k ⊕ Fin 2 → ℝ) (B' : ℝ)
    (z : Fin k ⊕ Fin 2 → ℝ) : ℝ≥0∞ :=
  {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z *
    (logCut ρ D γ q t Q).indicator (fun _ ↦ (1 : ℝ≥0∞)) z *
    ENNReal.ofReal (exp (-(∑ i, c i * z i)) * exp (-(B' * exp (-(∑ i, κ i * z i)))))

/-- **The inner substitution.** With `c = βκ − ηQ`, `B' = c₀ e^{δL}`, `L = log t` and
`h₀ = −(q log(ρ/D) + (∑Q) log ρ)`, the integral over the solved pair is `|det M|⁻¹` times the
integral of `innerKv` over `v`. -/
theorem lintegral_inner_subst {ρ D γ q t δ β η c₀ : ℝ} {Q c κ : Fin k ⊕ Fin 2 → ℝ}
    (hc : ∀ i, c i = β * κ i - η * Q i) (hΔ : (transMat κ Q).det ≠ 0) (z' : Fin k → ℝ) :
    ∫⁻ y : Fin 2 → ℝ, logIntegrand ρ D γ q t Q c κ (c₀ * exp (δ * log t)) (Sum.elim z' y) =
      ENNReal.ofReal |(transMat κ Q).det|⁻¹ *
        ∫⁻ v, innerKv κ Q δ γ (log t) β η ((β * δ - η * γ) * log t) c₀
          (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) z' v := by
  have hmeasK : Measurable (innerKv κ Q δ γ (log t) β η ((β * δ - η * γ) * log t) c₀
      (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) z') := by
    unfold innerKv
    refine ((measurable_const.mul ?_).mul ?_).mul ?_
    · exact measurable_const.indicator (measurableSet_image_mulVec_add_orthant hΔ _)
    · exact (measurable_const.indicator measurableSet_Ioi).comp (measurable_pi_apply 1)
    · exact ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
        (((measurable_const.mul (measurable_pi_apply 0)).add
          (measurable_const.mul (measurable_pi_apply 1))).add measurable_const).neg).mul
        (Real.measurable_exp.comp ((measurable_const.mul
          (Real.measurable_exp.comp (measurable_pi_apply 0).neg)).neg)))
  rw [← lintegral_comp_mulVec_add (transMat κ Q) hΔ (transShift κ Q δ γ (log t) z') hmeasK]
  refine lintegral_congr fun y ↦ ?_
  set sh := transShift κ Q δ γ (log t) z' with hsh
  set v := transMat κ Q *ᵥ y + sh with hvdef
  have hv := transMat_mulVec_add_shift κ Q δ γ (log t) z' y
  rw [← hsh, ← hvdef] at hv
  have hs : v 0 = ∑ i, κ i * Sum.elim z' y i - δ * log t := by rw [hv]; rfl
  have hh : v 1 = γ * log t - ∑ i, Q i * Sum.elim z' y i := by rw [hv]; rfl
  -- the orthant indicator splits
  have horth : {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}.indicator (fun _ ↦ (1 : ℝ≥0∞))
      (Sum.elim z' y) =
      {z' : Fin k → ℝ | ∀ j, 0 < z' j}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z' *
        ((fun y ↦ transMat κ Q *ᵥ y + sh) '' {y : Fin 2 → ℝ | ∀ j, 0 < y j}).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) v := by
    have hmem : v ∈ (fun y ↦ transMat κ Q *ᵥ y + sh) '' {y : Fin 2 → ℝ | ∀ j, 0 < y j} ↔
        ∀ j, 0 < y j := (injective_mulVec_add hΔ sh).mem_set_image
    by_cases hz : ∀ j, 0 < z' j
    · by_cases hy : ∀ j, 0 < y j
      · rw [Set.indicator_of_mem (show Sum.elim z' y ∈ {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}
          from Sum.forall.mpr ⟨hz, hy⟩),
          Set.indicator_of_mem (show z' ∈ {z' : Fin k → ℝ | ∀ j, 0 < z' j} from hz),
          Set.indicator_of_mem (hmem.mpr hy), one_mul]
      · rw [Set.indicator_of_notMem (show Sum.elim z' y ∉ {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}
          from fun h ↦ hy (Sum.forall.mp h).2), Set.indicator_of_notMem (fun h ↦ hy (hmem.mp h)),
          mul_zero]
    · rw [Set.indicator_of_notMem (show Sum.elim z' y ∉ {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}
        from fun h ↦ hz (Sum.forall.mp h).1),
        Set.indicator_of_notMem (show z' ∉ {z' : Fin k → ℝ | ∀ j, 0 < z' j} from hz), zero_mul]
  -- the truth cut is the half-line in `h`
  have hcut : (logCut ρ D γ q t Q).indicator (fun _ ↦ (1 : ℝ≥0∞)) (Sum.elim z' y) =
      (Ioi (-(q * log (ρ / D) + (∑ i, Q i) * log ρ))).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) := by
    have hiff : Sum.elim z' y ∈ logCut ρ D γ q t Q ↔
        v 1 ∈ Ioi (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) := by
      rw [hh]
      simp only [logCut, Set.mem_ofPred_eq, mem_Ioi]
      constructor <;> intro h <;> linarith
    by_cases hcz : Sum.elim z' y ∈ logCut ρ D γ q t Q
    · rw [Set.indicator_of_mem hcz, Set.indicator_of_mem (hiff.mp hcz)]
    · rw [Set.indicator_of_notMem hcz, Set.indicator_of_notMem (fun h ↦ hcz (hiff.mpr h))]
  -- the weight
  have hexp1 : exp (-(∑ i, c i * Sum.elim z' y i)) =
      exp (-(β * v 0 + η * v 1 + (β * δ - η * γ) * log t)) := by
    congr 1
    rw [hs, hh]
    simp only [hc]
    have e : ∑ i, (β * κ i - η * Q i) * Sum.elim z' y i =
        β * ∑ i, κ i * Sum.elim z' y i - η * ∑ i, Q i * Sum.elim z' y i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [e]
    ring
  -- the Boltzmann factor
  have hexp2 : exp (-(c₀ * exp (δ * log t) * exp (-(∑ i, κ i * Sum.elim z' y i)))) =
      exp (-(c₀ * exp (-v 0))) := by
    congr 1
    rw [hs, neg_sub, Real.exp_sub, Real.exp_neg]
    ring
  unfold logIntegrand innerKv
  rw [horth, hcut, hexp1, hexp2]

end Laplace.Multi
