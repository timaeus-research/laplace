/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthLP
import Laplace.Multi.ActiveTruthFacePositive
import Laplace.Multi.ActiveTruthChartSpectator

/-!
# The LP-to-chart interface of the active-truth term

Astra round 10, item (b). The analytic active-truth theorems take the dual certificate as data:
the exponent identity `r_j + 1 = βκ_j − ηQ_j` on the active coordinates and positive reduced
costs `d_l > 0` on the spectators. This file ties that data to the chart's linear programme
`min ∑ (r_j + 1) α_j` over `α ≥ 0`, `Q·α ≤ γ`, `κ·α ≥ δ`:

* a positive face polytope yields a face point with positive free coordinates
  (`exists_face_point_of_volume_pos`);
* under the certificate the optimal set of the LP is exactly the active face
  `{α ≥ 0 | κ·α = δ, Q·α = γ, α_I = 0}` (`lpOptimal_activeTruth_spectator_iff`, chart form
  `lpOptimal_iff_activeFace`), and the active-truth power `γp + βδ − ηγ` is the LP exponent of
  every face point (`activeTruth_lam_eq_lpExponent`);
* the active-truth measure is nonzero when the face polytope has positive volume and the chart
  weight `wt |b|` is positive somewhere on the truth segment (`activeTruthMeasure_ne_zero`,
  `activeTruthSpecMeasure_ne_zero`) — the guard against misidentifying the leading order by a
  vanishing coefficient measure.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {m k n : ℕ}

/-- A positive face polytope contains a face point with positive free coordinates. -/
theorem exists_face_point_of_volume_pos {κ Q : Fin k ⊕ Fin 2 → ℝ} {δ γ : ℝ}
    (hΔ : (transMat κ Q).det ≠ 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hvol : 0 < volume (facePolytope κ Q δ γ)) :
    ∃ α : Fin k ⊕ Fin 2 → ℝ, (∀ j, 0 ≤ α j) ∧ (∀ i, 0 < α (Sum.inl i)) ∧
      ∑ j, κ j * α j = δ ∧ ∑ j, Q j * α j = γ := by
  obtain ⟨w, hw, h0, h1⟩ := (volume_poly2_pos_iff hc₀ hc₁).mp hvol
  have hlt : ∀ j, fibreCoef κ Q j ⬝ᵥ w < fibreA κ Q δ γ j := Fin.forall_fin_two.mpr ⟨h0, h1⟩
  set y : Fin 2 → ℝ := (transMat κ Q)⁻¹ *ᵥ (0 - transShift κ Q δ γ 1 w) with hy
  have hyj : ∀ j, y j = fibreA κ Q δ γ j - fibreCoef κ Q j ⬝ᵥ w := by
    intro j
    rw [hy, inv_mulVec_sub_shift, mul_one]
    simp [fibreB]
  have hM : transMat κ Q *ᵥ y + transShift κ Q δ γ 1 w = 0 := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΔ),
      Matrix.one_mulVec]
    simp
  rw [transMat_mulVec_add_shift] at hM
  have h0' := congrFun hM 0
  have h1' := congrFun hM 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, mul_one] at h0' h1'
  refine ⟨Sum.elim w y, fun j ↦ ?_, fun i ↦ by simpa using hw i, by linarith, by linarith⟩
  cases j with
  | inl i => exact (hw i).le
  | inr j =>
    rw [Sum.elim_inr, hyj]
    exact (sub_pos.mpr (hlt j)).le

/-- The cost of a face point under a certificate: `∑ c_i α_i = βδ − ηγ` when the reduced costs
vanish wherever `α` does not. -/
theorem sum_cost_eq_of_face {ι : Type*} [Fintype ι] {Q κ c α : ι → ℝ} {γ δ β η : ℝ}
    (h0 : ∀ i, 0 < c i - β * κ i + η * Q i → α i = 0)
    (hzero : ∀ i, c i - β * κ i + η * Q i = 0 ∨ 0 < c i - β * κ i + η * Q i)
    (hκ : ∑ i, κ i * α i = δ) (hQ : ∑ i, Q i * α i = γ) :
    ∑ i, c i * α i = β * δ - η * γ := by
  have hid := dual_identity Q κ c γ δ β η α
  rw [hκ, hQ, sub_self, sub_self, mul_zero, mul_zero, zero_add, zero_add] at hid
  have hs : ∑ i, (c i - β * κ i + η * Q i) * α i = 0 := Finset.sum_eq_zero fun i _ ↦ by
    rcases hzero i with h | h
    · rw [h, zero_mul]
    · rw [h0 i h, mul_zero]
  rw [hs] at hid
  linarith

section Spectator

variable {ι : Type*} [Fintype ι] (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ ι) {Q κ r : ι → ℝ}
  {γ δ β η : ℝ}

omit [Fintype ι] in
/-- The reduced costs of an active-truth certificate along the splitting `e`: the spectator
reduced costs on `I`, zero on the active coordinates. -/
theorem reducedCost_eq (hr : ∀ j, r (e (Sum.inr j)) + 1 = β * κ (e (Sum.inr j)) -
      η * Q (e (Sum.inr j))) (j : ι) :
    r j + 1 - β * κ j + η * Q j =
      Sum.elim (fun l ↦ specd β η (Q ∘ e) (κ ∘ e) (r ∘ e) l) (fun _ ↦ 0) (e.symm j) := by
  have key : ∀ s : Fin n ⊕ (Fin k ⊕ Fin 2), r (e s) + 1 - β * κ (e s) + η * Q (e s) =
      Sum.elim (fun l ↦ specd β η (Q ∘ e) (κ ∘ e) (r ∘ e) l) (fun _ ↦ 0) s := by
    intro s
    cases s with
    | inl l => simp only [Sum.elim_inl, specd, Function.comp]
    | inr j =>
      simp only [Sum.elim_inr]
      linarith [hr j]
  have := key (e.symm j)
  simpa using this

/-- **The optimal set of the chart LP under an active-truth certificate** is the active face:
nonnegative `α` with both constraints active and vanishing spectator coordinates. -/
theorem lpOptimal_activeTruth_spectator_iff (hβ : 0 < β) (hη : 0 < η)
    (hr : ∀ j, r (e (Sum.inr j)) + 1 = β * κ (e (Sum.inr j)) - η * Q (e (Sum.inr j)))
    (hd : ∀ l, 0 < specd β η (Q ∘ e) (κ ∘ e) (r ∘ e) l)
    (hne : ∃ α₀ : Fin k ⊕ Fin 2 → ℝ, (∀ j, 0 ≤ α₀ j) ∧
      ∑ j, κ (e (Sum.inr j)) * α₀ j = δ ∧ ∑ j, Q (e (Sum.inr j)) * α₀ j = γ)
    (α : ι → ℝ) :
    LPOptimal Q κ γ δ (fun j ↦ r j + 1) α ↔
      (∀ j, 0 ≤ α j) ∧ ∑ j, κ j * α j = δ ∧ ∑ j, Q j * α j = γ ∧
        ∀ l, α (e (Sum.inl l)) = 0 := by
  have hred := reducedCost_eq e hr
  have hd' : ∀ j, 0 ≤ r j + 1 - β * κ j + η * Q j := fun j ↦ by
    rw [hred]
    rcases e.symm j with l | j'
    · exact (hd l).le
    · exact le_rfl
  have hne' : ∃ α₀ : ι → ℝ, (∀ j, 0 ≤ α₀ j) ∧ ∑ j, κ j * α₀ j = δ ∧ ∑ j, Q j * α₀ j = γ ∧
      ∀ j, 0 < r j + 1 - β * κ j + η * Q j → α₀ j = 0 := by
    obtain ⟨α₀, h0, hκ, hQ⟩ := hne
    refine ⟨fun j ↦ Sum.elim 0 α₀ (e.symm j), fun j ↦ ?_, ?_, ?_, fun j hj ↦ ?_⟩
    · change (0 : ℝ) ≤ Sum.elim (0 : Fin n → ℝ) α₀ (e.symm j)
      rcases e.symm j with l | j'
      · exact le_rfl
      · exact h0 j'
    · rw [← Equiv.sum_comp e]
      simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
      rw [Fintype.sum_sum_type] at hκ
      exact hκ
    · rw [← Equiv.sum_comp e]
      simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
      rw [Fintype.sum_sum_type] at hQ
      exact hQ
    · change Sum.elim (0 : Fin n → ℝ) α₀ (e.symm j) = (0 : ℝ)
      rw [hred] at hj
      revert hj
      rcases e.symm j with l | j'
      · intro _
        rfl
      · intro hj
        simp only [Sum.elim_inr] at hj
        exact absurd hj (lt_irrefl _)
  rw [lpOptimal_activeTruth_iff hβ hη hd' hne']
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h l ↦ ?_, fun h j hj ↦ ?_⟩
  · refine h (e (Sum.inl l)) ?_
    rw [hred]
    simp only [Equiv.symm_apply_apply, Sum.elim_inl]
    exact hd l
  · rw [hred] at hj
    rcases hs : e.symm j with l | j'
    · have := h l
      rwa [← hs, Equiv.apply_symm_apply] at this
    · rw [hs] at hj
      simp only [Sum.elim_inr] at hj
      exact absurd hj (lt_irrefl _)

/-- The active-truth power is the LP exponent of every face point. -/
theorem activeTruth_lam_eq_lpExponent (p : ℝ)
    (hr : ∀ j, r (e (Sum.inr j)) + 1 = β * κ (e (Sum.inr j)) - η * Q (e (Sum.inr j)))
    (hd : ∀ l, 0 < specd β η (Q ∘ e) (κ ∘ e) (r ∘ e) l) {α : ι → ℝ}
    (hκ : ∑ j, κ j * α j = δ) (hQ : ∑ j, Q j * α j = γ) (hI : ∀ l, α (e (Sum.inl l)) = 0) :
    γ * p + (β * δ - η * γ) = lpExponent γ p (fun j ↦ r j + 1) α := by
  have hred := reducedCost_eq e hr
  unfold lpExponent
  rw [sum_cost_eq_of_face (c := fun j ↦ r j + 1) (β := β) (η := η) ?_ ?_ hκ hQ]
  · intro j hj
    rw [hred] at hj
    rcases hs : e.symm j with l | j'
    · have := hI l
      rwa [← hs, Equiv.apply_symm_apply] at this
    · rw [hs] at hj
      simp only [Sum.elim_inr] at hj
      exact absurd hj (lt_irrefl _)
  · intro j
    rw [hred]
    rcases e.symm j with l | j'
    · exact Or.inr (hd l)
    · exact Or.inl rfl

end Spectator

namespace TruthChartsData.Phase

variable {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ} {D : TruthChartsData m T L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {i : D.ι} {ε : Fin m → Bool} {b : Bool}
  {σ γ β η : ℝ}

/-- **The chart LP under an active-truth certificate**: the optimal set is the active face. -/
theorem lpOptimal_iff_activeFace (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) (hβ : 0 < β) (hη : 0 < η)
    (hr : ∀ j, P.rExp i (e (Sum.inr j)) + 1 =
      β * P.kappa i (e (Sum.inr j)) - η * D.Qexp i (e (Sum.inr j)))
    (hd : ∀ l, 0 < specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l)
    (hΔ : (transMat (fun j ↦ (P.kappa i ∘ e) (Sum.inr j))
      (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))
        0 ≠ 0 ∨
      fibreA (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))
        (P.phaseExp i γ) γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))
        1 ≠ 0 ∨
      fibreA (fun j ↦ (P.kappa i ∘ e) (Sum.inr j)) (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))
        (P.phaseExp i γ) γ 1 ≠ 0)
    (hvol : 0 < volume (facePolytope (fun j ↦ (P.kappa i ∘ e) (Sum.inr j))
      (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j)) (P.phaseExp i γ) γ)) (α : Fin m → ℝ) :
    LPOptimal (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) (fun j ↦ P.rExp i j + 1) α ↔
      (∀ j, 0 ≤ α j) ∧ ∑ j, P.kappa i j * α j = P.phaseExp i γ ∧
        ∑ j, D.Qexp i j * α j = γ ∧ ∀ l, α (e (Sum.inl l)) = 0 := by
  obtain ⟨α₀, h0, -, hκ, hQ⟩ := exists_face_point_of_volume_pos hΔ hc₀ hc₁ hvol
  exact lpOptimal_activeTruth_spectator_iff e hβ hη hr hd ⟨α₀, h0, hκ, hQ⟩ α

/-- The face constant is positive when the face polytope has positive volume. -/
theorem faceConstSpec_pos (i : D.ι) (γ : ℝ) (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m)
    (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (fun j ↦ (P.kappa i ∘ e) (Sum.inr j))
      (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))).det ≠ 0)
    (hvol : 0 < volume (facePolytope (fun j ↦ (P.kappa i ∘ e) (Sum.inr j))
      (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j)) (P.phaseExp i γ) γ)) :
    0 < P.faceConstSpec i γ e := by
  unfold faceConstSpec
  exact div_pos (ENNReal.toReal_pos hvol.ne' (volume_facePolytope_ne_top hΔ
    (fun j ↦ hκ _) _ _)) (abs_pos.mpr hΔ)

theorem faceConst_pos (i : D.ι) (γ : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0)
    (hvol : 0 < volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ)) :
    0 < P.faceConst i γ e := by
  unfold faceConst
  exact div_pos (ENNReal.toReal_pos hvol.ne' (volume_facePolytope_ne_top hΔ
    (fun j ↦ hκ _) _ _)) (abs_pos.mpr hΔ)

theorem constA_pos (hσ : σ ≠ 0) : 0 < P.constA i σ := by
  unfold constA
  exact div_pos (Real.rpow_pos_of_pos (abs_pos.mpr hσ) _) (Nat.cast_pos.mpr (D.q_pos i))

/-- **Nonvanishing of the active-truth measure**: a positive face polytope and a point of the
truth segment where the chart weight `wt |b|` is positive give a nonzero coefficient measure. -/
theorem activeTruthMeasure_ne_zero (i : D.ι) (ε : Fin m → Bool) (b : Bool) (hσ : σ ≠ 0)
    (hβ : 0 < β) (hη : 0 < η) (e : Fin k ⊕ Fin 2 ≃ Fin m) (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0)
    (hvol : 0 < volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ))
    {u₀ : ℝ} (hu₀ : u₀ ∈ Ioo (0 : ℝ) (D.ρ i))
    (hpos : 0 < P.wt i (D.bridgePt i ε b 0 u₀) * |P.b i (D.bridgePt i ε b 0 u₀)|) :
    P.activeTruthMeasure i ε b σ γ β η e ≠ 0 := by
  intro h0
  have h1 : ∫ x, (1 : ℝ) ∂(P.activeTruthMeasure i ε b σ γ β η e) = 0 := by
    rw [h0]
    exact integral_zero_measure _
  rw [P.integral_activeTruthMeasure i ε b σ γ η hβ e measurable_const] at h1
  simp only [one_mul] at h1
  have hint := P.integrable_activeTruthDensity i ε b σ γ hβ hη e
  have hnn : 0 ≤ P.activeTruthDensity i ε b σ γ β η e := fun u ↦
    P.activeTruthDensity_nonneg i ε b σ γ η hβ e u
  have hpos' : 0 < ∫ u, P.activeTruthDensity i ε b σ γ β η e u := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hpt := continuous_truthPt (D := D) i ε b
    have hg : Continuous fun u ↦ P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)| :=
      ((P.wt_cont i).comp hpt).mul (continuous_abs.comp ((P.b_cont i).comp hpt))
    have hU : IsOpen {u | 0 < P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)|} :=
      isOpen_lt continuous_const hg
    refine lt_of_lt_of_le ((hU.inter isOpen_Ioo).measure_pos volume ⟨u₀, hpos, hu₀⟩)
      (measure_mono fun u hu ↦ ?_)
    obtain ⟨hu1, hu2⟩ := hu
    have hu1' : 0 < P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)| := hu1
    rw [Function.mem_support]
    unfold activeTruthDensity
    rw [Set.indicator_of_mem hu2]
    unfold activeTruthDensityFn
    have hA := P.constA_pos (i := i) hσ
    have hΓ := Real.Gamma_pos_of_pos hβ
    have hB : 0 < P.constB i σ ^ (-β) := Real.rpow_pos_of_pos (P.constB_pos hσ) _
    have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
    have hD : 0 < D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) :=
      Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (abs_pos.mpr hσ) _) _
    have hF := P.faceConst_pos i γ e hκ hΔ hvol
    have hu : 0 < u ^ ((D.q i (D.k i) : ℝ) * η - 1) := Real.rpow_pos_of_pos hu2.1 _
    have ha : 0 < |P.a i (D.bridgePt i ε b 0 u)| ^ (-β) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le (P.ma_pos i)
        (P.ma_le_unitFn_of_mem_ball (truthPt_mem_ball (D := D) i ε b hu2))) _
    exact (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hA hΓ) hB) hq) hD) hF)
      (mul_pos hu (mul_pos hu1' ha))).ne'
  exact absurd h1 hpos'.ne'

/-- **Nonvanishing of the spectator active-truth measure.** -/
theorem activeTruthSpecMeasure_ne_zero (i : D.ι) (ε : Fin m → Bool) (b : Bool) (hσ : σ ≠ 0)
    (hβ : 0 < β) (hη : 0 < η) (e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m) (hκ : ∀ j, 0 < P.kappa i j)
    (hd : ∀ l, 0 < specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l)
    (hΔ : (transMat (fun j ↦ (P.kappa i ∘ e) (Sum.inr j))
      (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j))).det ≠ 0)
    (hvol : 0 < volume (facePolytope (fun j ↦ (P.kappa i ∘ e) (Sum.inr j))
      (fun j ↦ (D.Qexp i ∘ e) (Sum.inr j)) (P.phaseExp i γ) γ))
    {ξ₀ : Fin n → ℝ} (hξ₀ : ξ₀ ∈ specBox n (D.ρ i)) {u₀ : ℝ} (hu₀ : u₀ ∈ Ioo (0 : ℝ) (D.ρ i))
    (hpos : 0 < P.wt i (D.bridgePt i ε b (specPt e ξ₀) u₀) *
      |P.b i (D.bridgePt i ε b (specPt e ξ₀) u₀)|) :
    P.activeTruthSpecMeasure i ε b σ γ β η e ≠ 0 := by
  intro h0
  have h1 : ∫ x, (1 : ℝ) ∂(P.activeTruthSpecMeasure i ε b σ γ β η e) = 0 := by
    rw [h0]
    exact integral_zero_measure _
  rw [P.integral_activeTruthSpecMeasure i ε b σ γ η hβ e measurable_const] at h1
  simp only [one_mul] at h1
  have hint := P.integrable_activeTruthSpecDensity i ε b σ γ hβ hη e hd
  have hnn : 0 ≤ P.activeTruthSpecDensity i ε b σ γ β η e := fun p ↦
    P.activeTruthSpecDensity_nonneg i ε b σ γ η hβ e p
  have hpos' : 0 < ∫ p, P.activeTruthSpecDensity i ε b σ γ β η e p := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hpt := continuous_specTruthPt (D := D) i ε b e
    have hg : Continuous fun p : (Fin n → ℝ) × ℝ ↦ P.wt i (D.bridgePt i ε b (specPt e p.1) p.2) *
        |P.b i (D.bridgePt i ε b (specPt e p.1) p.2)| :=
      ((P.wt_cont i).comp hpt).mul (continuous_abs.comp ((P.b_cont i).comp hpt))
    have hU : IsOpen {p : (Fin n → ℝ) × ℝ | 0 < P.wt i (D.bridgePt i ε b (specPt e p.1) p.2) *
        |P.b i (D.bridgePt i ε b (specPt e p.1) p.2)|} := isOpen_lt continuous_const hg
    have hbox : IsOpen (specBox n (D.ρ i) ×ˢ Ioo (0 : ℝ) (D.ρ i)) :=
      (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo).prod isOpen_Ioo
    refine lt_of_lt_of_le ((hU.inter hbox).measure_pos volume ⟨(ξ₀, u₀), hpos, hξ₀, hu₀⟩)
      (measure_mono fun p hp ↦ ?_)
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : 0 < P.wt i (D.bridgePt i ε b (specPt e p.1) p.2) *
        |P.b i (D.bridgePt i ε b (specPt e p.1) p.2)| := hp1
    have hξ : p.1 ∈ specBox n (D.ρ i) := hp2.1
    have hu : p.2 ∈ Ioo (0 : ℝ) (D.ρ i) := hp2.2
    rw [Function.mem_support]
    unfold activeTruthSpecDensity
    rw [Set.indicator_of_mem hp2, Function.uncurry_apply_pair]
    unfold activeTruthSpecDensityFn
    have hA := P.constA_pos (i := i) hσ
    have hΓ := Real.Gamma_pos_of_pos hβ
    have hB : 0 < P.constB i σ ^ (-β) := Real.rpow_pos_of_pos (P.constB_pos hσ) _
    have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
    have hD : 0 < D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) :=
      Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (abs_pos.mpr hσ) _) _
    have hF := P.faceConstSpec_pos i γ e hκ hΔ hvol
    have hP : 0 < ∏ l, p.1 l ^ (specd β η (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) l - 1) :=
      Finset.prod_pos fun l _ ↦ Real.rpow_pos_of_pos ((Set.mem_univ_pi.mp hξ) l).1 _
    have hu' : 0 < p.2 ^ ((D.q i (D.k i) : ℝ) * η - 1) := Real.rpow_pos_of_pos hu.1 _
    have ha : 0 < |P.a i (D.bridgePt i ε b (specPt e p.1) p.2)| ^ (-β) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le (P.ma_pos i)
        (P.ma_le_unitFn_of_mem_ball (specTruthPt_mem_ball (D := D) i ε b e hξ hu))) _
    exact (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hA hΓ) hB) hq) hD) hF)
      (mul_pos hP (mul_pos hu' (mul_pos hp1' ha)))).ne'
  exact absurd h1 hpos'.ne'

end TruthChartsData.Phase

end Laplace.Multi
