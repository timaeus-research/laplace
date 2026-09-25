/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthGeneralUniform
import Laplace.Multi.ActiveTruthSpectator

/-!
# The face theorem with spectators and general units

Astra round 10, item (a). On `Fin m ⊕ (Fin k ⊕ Fin 2)` (spectators `ξ` first) with general units
`W(ξ, x', u)`, `a(ξ, x', u)`: freezing `ξ` gives the active-coordinate kernel with the constants
`B_ξ, D_ξ` and the units `specW W ξ = W(ξ, ·, ·)` (`modelIntegrand_sum_elim_general`), the
general-unit face theorem applies pointwise in `ξ` with the traces `W_tr(ξ, u)`, `a_tr(ξ, u)`,
and the outer dominated convergence uses the uniform bound of `ActiveTruthGeneralUniform` and
the spectator envelope. The limit is
`A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M|` times
`∫_{(0,ρ)^m} ∏ ξ^{d−1} ∫_0^ρ u^{qη−1} W_tr(ξ,u) a_tr(ξ,u)^{-β}`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {m k : ℕ}

/-- The units with the spectators frozen at `ξ`. -/
def specW (W : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ) (ξ : Fin m → ℝ)
    (x' : Fin k ⊕ Fin 2 → ℝ) (u : ℝ) : ℝ :=
  W (Sum.elim ξ x') u

theorem measurable_specW_uncurry {W : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ}
    (hW : Measurable (Function.uncurry W)) (ξ : Fin m → ℝ) :
    Measurable (Function.uncurry (specW W ξ)) := by
  have e : Function.uncurry (specW W ξ) = Function.uncurry W ∘
      fun p : (Fin k ⊕ Fin 2 → ℝ) × ℝ ↦ (Sum.elim ξ p.1, p.2) := by
    funext p
    rfl
  rw [e]
  refine hW.comp (Measurable.prodMk ?_ measurable_snd)
  refine measurable_pi_iff.mpr fun i ↦ ?_
  cases i with
  | inl i => exact measurable_const
  | inr j => exact (measurable_pi_apply j).comp measurable_fst

/-- **Freezing the spectators** with general units. -/
theorem modelIntegrand_sum_elim_general (ρ B D γ q δ t : ℝ)
    (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) (W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ)
    (ξ : Fin m → ℝ) (x' : Fin k ⊕ Fin 2 → ℝ) :
    modelIntegrand ρ B D γ q δ Q κ r W a t (Sum.elim ξ x') =
      (specBox m ρ).indicator (fun ξ ↦ ∏ i, ξ i ^ r (Sum.inl i)) ξ *
        modelIntegrand ρ (specB B κ ξ) (specD D q Q ξ) γ q δ (fun j ↦ Q (Sum.inr j))
          (fun j ↦ κ (Sum.inr j)) (fun j ↦ r (Sum.inr j)) (specW W ξ) (specW a ξ) t x' := by
  unfold modelIntegrand modelDomain
  have hmem : Sum.elim ξ x' ∈ Set.pi univ (fun _ : Fin m ⊕ (Fin k ⊕ Fin 2) ↦ Ioo (0 : ℝ) ρ) ↔
      ξ ∈ specBox m ρ ∧ x' ∈ Set.pi univ (fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ) := by
    simp only [Set.mem_univ_pi, Sum.forall, Sum.elim_inl, Sum.elim_inr, specBox]
  have hprod : ∀ e : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ,
      ∏ i, Sum.elim ξ x' i ^ e i = (∏ i, ξ i ^ e (Sum.inl i)) * ∏ j, x' j ^ e (Sum.inr j) := by
    intro e
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
  by_cases hξ : ξ ∈ specBox m ρ
  · rw [Set.indicator_of_mem hξ]
    by_cases hx : x' ∈ Set.pi univ (fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ) ∩
        {x | cutVar (specD D q Q ξ) γ q (fun j ↦ Q (Sum.inr j)) t x < ρ}
    · have hx' : Sum.elim ξ x' ∈ Set.pi univ (fun _ : Fin m ⊕ (Fin k ⊕ Fin 2) ↦ Ioo (0 : ℝ) ρ) ∩
          {x | cutVar D γ q Q t x < ρ} := by
        refine ⟨hmem.mpr ⟨hξ, hx.1⟩, ?_⟩
        change cutVar D γ q Q t (Sum.elim ξ x') < ρ
        rw [cutVar_sum_elim]
        exact hx.2
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, hprod, hprod, cutVar_sum_elim]
      unfold specB specW
      rw [show B * t ^ δ *
          a (Sum.elim ξ x') (cutVar (specD D q Q ξ) γ q (fun j ↦ Q (Sum.inr j)) t x') *
          ((∏ i, ξ i ^ κ (Sum.inl i)) * ∏ j, x' j ^ κ (Sum.inr j)) =
        (B * ∏ i, ξ i ^ κ (Sum.inl i)) * t ^ δ *
          a (Sum.elim ξ x') (cutVar (specD D q Q ξ) γ q (fun j ↦ Q (Sum.inr j)) t x') *
          ∏ j, x' j ^ κ (Sum.inr j) by ring]
      ring
    · have hx' : Sum.elim ξ x' ∉ Set.pi univ (fun _ : Fin m ⊕ (Fin k ⊕ Fin 2) ↦ Ioo (0 : ℝ) ρ) ∩
          {x | cutVar D γ q Q t x < ρ} := by
        intro h
        refine hx ⟨(hmem.mp h.1).2, ?_⟩
        have := h.2
        simp only [Set.mem_ofPred_eq, cutVar_sum_elim] at this
        exact this
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  · rw [Set.indicator_of_notMem hξ, zero_mul]
    have hx' : Sum.elim ξ x' ∉ Set.pi univ (fun _ : Fin m ⊕ (Fin k ⊕ Fin 2) ↦ Ioo (0 : ℝ) ρ) ∩
        {x | cutVar D γ q Q t x < ρ} := fun h ↦ hξ (hmem.mp h.1).1
    rw [Set.indicator_of_notMem hx']

/-- The normalised active-coordinate integral with the spectators frozen at `ξ`, general units. -/
noncomputable def specInnerG (ρ B D γ q δ β η : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    (W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ) (ξ : Fin m → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
    ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal (modelIntegrand ρ (specB B κ ξ) (specD D q Q ξ)
      γ q δ (fun j ↦ Q (Sum.inr j)) (fun j ↦ κ (Sum.inr j)) (fun j ↦ r (Sum.inr j))
      (specW W ξ) (specW a ξ) t x')

/-- The spectator integrand with general units. -/
noncomputable def specFG (ρ B D γ q δ β η : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    (W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ) (t : ℝ) (ξ : Fin m → ℝ) : ℝ≥0∞ :=
  (specBox m ρ).indicator (fun ξ ↦ ENNReal.ofReal (∏ i, ξ i ^ r (Sum.inl i))) ξ *
    specInnerG ρ B D γ q δ β η Q κ r W a ξ t

theorem specFG_eq (ρ B D γ q δ β η : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    (W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ) (t : ℝ) (ξ : Fin m → ℝ) :
    specFG ρ B D γ q δ β η Q κ r W a t ξ = ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
      ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r W a t (Sum.elim ξ x')) := by
  unfold specFG specInnerG
  simp_rw [modelIntegrand_sum_elim_general]
  by_cases hξ : ξ ∈ specBox m ρ
  · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
    have hnn : 0 ≤ ∏ i, ξ i ^ r (Sum.inl i) := Finset.prod_nonneg fun i _ ↦
      Real.rpow_nonneg ((Set.mem_univ_pi.mp hξ) i).1.le _
    simp_rw [ENNReal.ofReal_mul hnn]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring
  · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, zero_mul]
    simp

theorem measurable_specFG (ρ B D γ q δ β η : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    {W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ} (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) (t : ℝ) :
    Measurable (specFG ρ B D γ q δ β η Q κ r W a t) := by
  rw [show specFG ρ B D γ q δ β η Q κ r W a t = fun ξ ↦ _ from
    funext fun ξ ↦ specFG_eq ρ B D γ q δ β η Q κ r W a t ξ]
  refine Measurable.const_mul ?_ _
  refine Measurable.lintegral_prod_right (f := fun (ξ : Fin m → ℝ) (x' : Fin k ⊕ Fin 2 → ℝ) ↦
    ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t (Sum.elim ξ x'))) ?_
  have e : (Function.uncurry fun (ξ : Fin m → ℝ) (x' : Fin k ⊕ Fin 2 → ℝ) ↦
      ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t (Sum.elim ξ x'))) =
      (fun x ↦ ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x)) ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ (Fin k ⊕ Fin 2) ↦ ℝ)).symm := by
    funext p
    rfl
  rw [e]
  exact (ENNReal.measurable_ofReal.comp (measurable_modelIntegrand hW ha t)).comp
    (MeasurableEquiv.measurable _)

/-- Fubini over the spectators with general units. -/
theorem lintegral_modelIntegrand_spectator_general (ρ B D γ q δ t : ℝ)
    (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) {W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ}
    (hW : Measurable (Function.uncurry W)) (ha : Measurable (Function.uncurry a)) :
    ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x) =
      ∫⁻ ξ : Fin m → ℝ, ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r W a t (Sum.elim ξ x')) :=
  lintegral_sum_split (F := fun x ↦ ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x))
    (ENNReal.measurable_ofReal.comp (measurable_modelIntegrand hW ha t))

/-! ### Domination -/

theorem modelIntegrand_nonneg_of_nonneg {ι : Type*} [Fintype ι] {ρ B D γ q δ t : ℝ}
    {Q κ r : ι → ℝ} {W a : (ι → ℝ) → ℝ → ℝ} (hW : ∀ x u, 0 ≤ W x u) (x : ι → ℝ) :
    0 ≤ modelIntegrand ρ B D γ q δ Q κ r W a t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q Q t
  · rw [Set.indicator_of_mem hx]
    have hx0 : ∀ i, 0 < x i := fun i ↦ ((Set.mem_univ_pi.mp hx.1) i).1
    exact mul_nonneg (mul_nonneg (hW _ _) (Finset.prod_nonneg fun i _ ↦
      Real.rpow_nonneg (hx0 i).le _)) (exp_pos _).le
  · rw [Set.indicator_of_notMem hx]

/-- Pointwise domination of the general integrand by `W_*` times the constant-unit integrand at
`a₀ = a_-`. -/
theorem modelIntegrand_le_const_units {ι : Type*} [Fintype ι] {ρ B D γ q δ t : ℝ} {Q κ r : ι → ℝ}
    {W a : (ι → ℝ) → ℝ → ℝ} {Wstar amin : ℝ} (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u) (x : ι → ℝ) :
    modelIntegrand ρ B D γ q δ Q κ r W a t x ≤
      Wstar * modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ amin) t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q Q t
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have hx0 : ∀ i, 0 < x i := fun i ↦ ((Set.mem_univ_pi.mp hx.1) i).1
    have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _
    have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _
    have hBt : 0 ≤ B * t ^ δ := mul_nonneg hB (Real.rpow_nonneg ht _)
    have hexp : exp (-(B * t ^ δ * a x (cutVar D γ q Q t x) * ∏ j, x j ^ κ j)) ≤
        exp (-(B * t ^ δ * amin * ∏ j, x j ^ κ j)) := by
      refine Real.exp_le_exp.mpr (neg_le_neg ?_)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hab _ _) hBt) hκ0
    calc W x (cutVar D γ q Q t x) * (∏ j, x j ^ r j) *
          exp (-(B * t ^ δ * a x (cutVar D γ q Q t x) * ∏ j, x j ^ κ j))
        ≤ Wstar * (∏ j, x j ^ r j) * exp (-(B * t ^ δ * amin * ∏ j, x j ^ κ j)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hWb _ _).2 hr0) hexp (exp_pos _).le ?_
          exact mul_nonneg ((hWb x 0).1.trans (hWb x 0).2) hr0
      _ = Wstar * (1 * (∏ j, x j ^ r j) * exp (-(B * t ^ δ * amin * ∏ j, x j ^ κ j))) := by
          ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

/-- The spectator integrand with general units is dominated by `W_*` times the constant-unit
dominating function at `a₀ = a_-`. -/
theorem specFG_le {ρ B D γ q δ β η t : ℝ} {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    {W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ} {Wstar amin : ℝ} (hamin : 0 < amin)
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u) (ht : exp 1 ≤ t)
    (ξ : Fin m → ℝ) :
    specFG ρ B D γ q δ β η Q κ r W a t ξ ≤
      ENNReal.ofReal Wstar * ENNReal.ofReal (specG ρ B D q δ β η amin Q κ r ξ) := by
  have hW0 : 0 ≤ Wstar := (hWb 0 0).1.trans (hWb 0 0).2
  have ht0 : 0 ≤ t := (exp_pos 1).le.trans ht
  by_cases hξ : ξ ∈ specBox m ρ
  · have hξ' : ∀ i, 0 < ξ i := fun i ↦ ((Set.mem_univ_pi.mp hξ) i).1
    have hint : ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal (modelIntegrand ρ (specB B κ ξ)
        (specD D q Q ξ) γ q δ (fun j ↦ Q (Sum.inr j)) (fun j ↦ κ (Sum.inr j))
        (fun j ↦ r (Sum.inr j)) (specW W ξ) (specW a ξ) t x') ≤
        ENNReal.ofReal Wstar * ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal (modelIntegrand ρ
          (specB B κ ξ) (specD D q Q ξ) γ q δ (fun j ↦ Q (Sum.inr j)) (fun j ↦ κ (Sum.inr j))
          (fun j ↦ r (Sum.inr j)) (fun _ _ ↦ 1) (fun _ _ ↦ amin) t x') := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x' ↦ ?_
      rw [← ENNReal.ofReal_mul hW0]
      exact ENNReal.ofReal_le_ofReal (modelIntegrand_le_const_units (specB_pos hB κ hξ').le ht0
        (fun x u ↦ hWb _ _) (fun x u ↦ hab _ _) x')
    have h1 : specFG ρ B D γ q δ β η Q κ r W a t ξ ≤
        ENNReal.ofReal Wstar * specF ρ B D γ q δ β η amin Q κ r t ξ := by
      unfold specFG specInnerG specF specInner
      calc _ ≤ (specBox m ρ).indicator (fun ξ ↦ ENNReal.ofReal (∏ i, ξ i ^ r (Sum.inl i))) ξ *
            (ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) * (ENNReal.ofReal Wstar *
              ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal (modelIntegrand ρ (specB B κ ξ)
                (specD D q Q ξ) γ q δ (fun j ↦ Q (Sum.inr j)) (fun j ↦ κ (Sum.inr j))
                (fun j ↦ r (Sum.inr j)) (fun _ _ ↦ 1) (fun _ _ ↦ amin) t x'))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hint zero_le) zero_le
        _ = _ := by ring
    exact h1.trans (mul_le_mul_of_nonneg_left
      (specF_le hρ hD hq hB hamin hβ hη hδ hκ hΔ hrJ ht ξ) zero_le)
  · unfold specFG
    rw [Set.indicator_of_notMem hξ, zero_mul]
    exact zero_le

/-! ### The pointwise limit -/

/-- The pointwise limit of the spectator integrand with general units: the general-unit face
limit at the frozen constants `B_ξ`, `D_ξ` with the traces `W_tr(ξ, ·)`, `a_tr(ξ, ·)`. -/
noncomputable def specFGlim (ρ B D γ q δ β η : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    (Wtr atr : (Fin m → ℝ) → ℝ → ℝ) (ξ : Fin m → ℝ) : ℝ≥0∞ :=
  (specBox m ρ).indicator (fun ξ ↦ ENNReal.ofReal (∏ i, ξ i ^ r (Sum.inl i))) ξ *
    (ENNReal.ofReal (ρ ^ (∑ j, (r (Sum.inr j) + 1)) *
        |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹) *
      ∫⁻ v : Fin 2 → ℝ, vWeightT β η 0 (specB B κ ξ * ρ ^ (∑ j, κ (Sum.inr j)))
        (-(q * log (ρ / specD D q Q ξ) + (∑ j, Q (Sum.inr j)) * log ρ))
        (fun h ↦ Wtr ξ (truthOf ρ (specD D q Q ξ) q (fun j ↦ Q (Sum.inr j)) h))
        (fun h ↦ atr ξ (truthOf ρ (specD D q Q ξ) q (fun j ↦ Q (Sum.inr j)) h)) v *
        volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ))

theorem specFG_tendsto {ρ B D γ q δ β η : ℝ} {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 0 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 1 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 1 ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    {W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ} {Wstar amin : ℝ} (hamin : 0 < amin)
    (hWm : Measurable (Function.uncurry W)) (ham : Measurable (Function.uncurry a))
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u)
    {Wtr atr : (Fin m → ℝ) → ℝ → ℝ} (ξ : Fin m → ℝ)
    (hWtr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x' ↦ W (Sum.elim ξ x') u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr ξ u)))
    (hatr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x' ↦ a (Sum.elim ξ x') u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr ξ u))) :
    Tendsto (fun t ↦ specFG ρ B D γ q δ β η Q κ r W a t ξ) atTop
      (𝓝 (specFGlim ρ B D γ q δ β η Q κ r Wtr atr ξ)) := by
  by_cases hξ : ξ ∈ specBox m ρ
  · have hξ' : ∀ i, 0 < ξ i := fun i ↦ ((Set.mem_univ_pi.mp hξ) i).1
    unfold specFG specFGlim specInnerG
    rw [Set.indicator_of_mem hξ]
    exact ENNReal.Tendsto.const_mul (tendsto_normalised_lintegralG (Q := fun j ↦ Q (Sum.inr j))
      (κ := fun j ↦ κ (Sum.inr j)) (r := fun j ↦ r (Sum.inr j)) hρ (specD_pos hD q Q hξ') hq
      (specB_pos hB κ hξ') hβ hη hδ (fun j ↦ hκ _) hΔ hc₀ hc₁ hrJ hamin
      (measurable_specW_uncurry hWm ξ) (measurable_specW_uncurry ham ξ) (fun x u ↦ hWb _ _)
      (fun x u ↦ hab _ _) hWtr hatr) (Or.inr ENNReal.ofReal_ne_top)
  · simp only [specFG, specFGlim, Set.indicator_of_notMem hξ, zero_mul]
    exact tendsto_const_nhds

/-! ### Evaluating the limit -/

/-- The spectator constant factor in the `B^{-β} D^{-qη}` form. -/
theorem spec_const_factor' {B D q β η : ℝ} (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) {ξ : Fin m → ℝ} (hξ : ∀ i, 0 < ξ i) :
    (∏ i, ξ i ^ r (Sum.inl i)) * (specB B κ ξ ^ (-β) * specD D q Q ξ ^ (-(q * η))) =
      B ^ (-β) * D ^ (-(q * η)) * ∏ i, ξ i ^ (specd β η Q κ r i - 1) := by
  have hPκ : 0 < ∏ i, ξ i ^ κ (Sum.inl i) :=
    Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hξ i) _
  have hPQ : 0 < ∏ i, ξ i ^ (-(Q (Sum.inl i) / q)) :=
    Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hξ i) _
  have e1 : specB B κ ξ ^ (-β) = B ^ (-β) * ∏ i, ξ i ^ (-(β * κ (Sum.inl i))) := by
    unfold specB
    rw [Real.mul_rpow hB.le hPκ.le, ← Real.finsetProd_rpow _ _ fun i _ ↦
      (Real.rpow_pos_of_pos (hξ i) _).le]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← Real.rpow_mul (hξ i).le]
    congr 1
    ring
  have e2 : specD D q Q ξ ^ (-(q * η)) = D ^ (-(q * η)) * ∏ i, ξ i ^ (η * Q (Sum.inl i)) := by
    unfold specD
    rw [Real.mul_rpow hD.le hPQ.le, ← Real.finsetProd_rpow _ _ fun i _ ↦
      (Real.rpow_pos_of_pos (hξ i) _).le]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← Real.rpow_mul (hξ i).le]
    congr 1
    field_simp
  have e3 : ∀ i, ξ i ^ r (Sum.inl i) * (ξ i ^ (-(β * κ (Sum.inl i))) * ξ i ^ (η * Q (Sum.inl i)))
      = ξ i ^ (specd β η Q κ r i - 1) := fun i ↦ by
    rw [← Real.rpow_add (hξ i), ← Real.rpow_add (hξ i)]
    congr 1
    unfold specd
    ring
  rw [e1, e2]
  calc (∏ i, ξ i ^ r (Sum.inl i)) * (B ^ (-β) * (∏ i, ξ i ^ (-(β * κ (Sum.inl i)))) *
        (D ^ (-(q * η)) * ∏ i, ξ i ^ (η * Q (Sum.inl i))))
      = B ^ (-β) * D ^ (-(q * η)) * ∏ i, ξ i ^ r (Sum.inl i) *
          (ξ i ^ (-(β * κ (Sum.inl i))) * ξ i ^ (η * Q (Sum.inl i))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ring
    _ = _ := by rw [Finset.prod_congr rfl fun i _ ↦ e3 i]

/-- The limit integral, evaluated: `|det M|⁻¹ Γ(β) B^{-β} q D^{-qη}` times the double integral
`∫_{(0,ρ)^m} ∏ ξ^{d−1} ∫_0^ρ u^{qη−1} W_tr(ξ,u) a_tr(ξ,u)^{-β}`, times `vol(F')`. -/
theorem lintegral_specFGlim {ρ B D γ q δ β η : ℝ} {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β) (hη : 0 < η)
    (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i) {Wtr atr : (Fin m → ℝ) → ℝ → ℝ} {Wstar amin : ℝ}
    (hamin : 0 < amin) (hWtrm : Measurable (Function.uncurry Wtr))
    (hatrm : Measurable (Function.uncurry atr))
    (hWtrb : ∀ ξ, ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ Wtr ξ u ∧ Wtr ξ u ≤ Wstar)
    (hatrb : ∀ ξ, ∀ u ∈ Ioo (0 : ℝ) ρ, amin ≤ atr ξ u) :
    ∫⁻ ξ, specFGlim ρ B D γ q δ β η Q κ r Wtr atr ξ =
      ENNReal.ofReal (|(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ *
        (Gamma β * (B ^ (-β) * (q * D ^ (-(q * η))))) *
        ∫ ξ in specBox m ρ, (∏ i, ξ i ^ (specd β η Q κ r i - 1)) *
          ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr ξ u * atr ξ u ^ (-β))) *
      volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ) := by
  set V := volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ) with hV
  have hVne : V ≠ ⊤ := volume_facePolytope_ne_top hΔ (fun j ↦ hκ _) δ γ
  set K := |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ *
    (Gamma β * (B ^ (-β) * (q * D ^ (-(q * η))))) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := Real.Gamma_pos_of_pos hβ
    positivity
  set I : (Fin m → ℝ) → ℝ := fun ξ ↦
    ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr ξ u * atr ξ u ^ (-β)) with hI
  have hW0 : 0 ≤ Wstar := by
    have := hWtrb 0 (ρ / 2) ⟨by positivity, by linarith⟩
    exact this.1.trans this.2
  have hgq : IntegrableOn (fun u : ℝ ↦ u ^ (q * η - 1)) (Ioo (0 : ℝ) ρ) := by
    have := integrableOn_rpow_mul_log_pow (mul_pos hq hη) zero_le_one le_rfl hρ 0
    refine this.congr_fun (fun x _ ↦ ?_) measurableSet_Ioo
    simp
  have hI0 : ∀ ξ, 0 ≤ I ξ := fun ξ ↦ by
    rw [hI]
    refine setIntegral_nonneg measurableSet_Ioo fun u hu ↦ ?_
    exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (mul_nonneg (hWtrb ξ u hu).1
      (Real.rpow_nonneg (hamin.le.trans (hatrb ξ u hu)) _))
  have hIb : ∀ ξ, I ξ ≤ Wstar * amin ^ (-β) * (ρ ^ (q * η) / (q * η)) := fun ξ ↦ by
    rw [hI]
    have hbound : ∀ u ∈ Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr ξ u * atr ξ u ^ (-β)) ≤
        Wstar * amin ^ (-β) * u ^ (q * η - 1) := by
      intro u hu
      have hu0 : 0 ≤ u ^ (q * η - 1) := Real.rpow_nonneg hu.1.le _
      have ha := hatrb ξ u hu
      have hapow : atr ξ u ^ (-β) ≤ amin ^ (-β) := by
        rw [Real.rpow_neg hamin.le, Real.rpow_neg (hamin.le.trans ha)]
        exact inv_anti₀ (Real.rpow_pos_of_pos hamin _) (Real.rpow_le_rpow hamin.le ha hβ.le)
      calc u ^ (q * η - 1) * (Wtr ξ u * atr ξ u ^ (-β))
          ≤ u ^ (q * η - 1) * (Wstar * amin ^ (-β)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hWtrb ξ u hu).2 hapow
              (Real.rpow_nonneg (hamin.le.trans ha) _) hW0) hu0
        _ = _ := by ring
    calc (∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr ξ u * atr ξ u ^ (-β)))
        ≤ ∫ u in Ioo (0 : ℝ) ρ, Wstar * amin ^ (-β) * u ^ (q * η - 1) := by
          refine integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Ioo).mpr
            (Eventually.of_forall fun u hu ↦ ?_)) (hgq.const_mul _)
            ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall hbound))
          exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (mul_nonneg (hWtrb ξ u hu).1
            (Real.rpow_nonneg (hamin.le.trans (hatrb ξ u hu)) _))
      _ = Wstar * amin ^ (-β) * (ρ ^ (q * η) / (q * η)) := by
          rw [integral_const_mul, integral_Ioo_rpow_sub_one (mul_pos hq hη) hρ]
  have hIm : Measurable I := by
    rw [hI]
    have hf : Measurable (Function.uncurry fun (ξ : Fin m → ℝ) (u : ℝ) ↦
        u ^ (q * η - 1) * (Wtr ξ u * atr ξ u ^ (-β))) :=
      (measurable_snd.pow_const _).mul (hWtrm.mul (hatrm.pow_const _))
    exact (hf.stronglyMeasurable.integral_prod_right
      (ν := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) ρ))).measurable
  -- the product density
  have hg : ∀ i, IntegrableOn (fun x : ℝ ↦ x ^ (specd β η Q κ r i - 1)) (Ioo (0 : ℝ) ρ) := by
    intro i
    have := integrableOn_rpow_mul_log_pow (hd i) zero_le_one le_rfl hρ 0
    refine this.congr_fun (fun x _ ↦ ?_) measurableSet_Ioo
    simp
  have hP : Integrable fun ξ : Fin m → ℝ ↦
      ∏ i, (Ioo (0 : ℝ) ρ).indicator (fun x ↦ x ^ (specd β η Q κ r i - 1)) (ξ i) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin m ↦ (volume : Measure ℝ))
      (f := fun i x ↦ (Ioo (0 : ℝ) ρ).indicator (fun x ↦ x ^ (specd β η Q κ r i - 1)) x)
      (fun i ↦ (hg i).integrable_indicator measurableSet_Ioo)
    rw [volume_pi]
    exact this
  have hPind : ∀ ξ : Fin m → ℝ,
      ∏ i, (Ioo (0 : ℝ) ρ).indicator (fun x ↦ x ^ (specd β η Q κ r i - 1)) (ξ i) =
        (specBox m ρ).indicator (fun ξ ↦ ∏ i, ξ i ^ (specd β η Q κ r i - 1)) ξ := fun ξ ↦ by
    by_cases hξ : ξ ∈ specBox m ρ
    · rw [prod_indicator_Ioo_of_mem _ hξ, Set.indicator_of_mem hξ]
    · rw [prod_indicator_Ioo_of_notMem _ hξ, Set.indicator_of_notMem hξ]
  have hPnn : ∀ ξ : Fin m → ℝ,
      0 ≤ (specBox m ρ).indicator (fun ξ ↦ ∏ i, ξ i ^ (specd β η Q κ r i - 1)) ξ := fun ξ ↦
    Set.indicator_nonneg (fun ξ hξ ↦ Finset.prod_nonneg fun i _ ↦
      Real.rpow_nonneg ((Set.mem_univ_pi.mp hξ) i).1.le _) _
  simp_rw [hPind] at hP
  -- the pointwise evaluation
  have hpt : ∀ ξ, specFGlim ρ B D γ q δ β η Q κ r Wtr atr ξ = ENNReal.ofReal (I ξ *
      (K * (specBox m ρ).indicator (fun ξ ↦ ∏ i, ξ i ^ (specd β η Q κ r i - 1)) ξ)) * V := by
    intro ξ
    unfold specFGlim
    by_cases hξ : ξ ∈ specBox m ρ
    · have hξ' : ∀ i, 0 < ξ i := fun i ↦ ((Set.mem_univ_pi.mp hξ) i).1
      rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
      have hDξ := specD_pos hD q Q hξ'
      set cξ := specB B κ ξ * ρ ^ (∑ j, κ (Sum.inr j)) with hcξ
      set h₀ := -(q * log (ρ / specD D q Q ξ) + (∑ j, Q (Sum.inr j)) * log ρ) with hh₀
      set wh : ℝ → ℝ := fun h ↦ Wtr ξ (truthOf ρ (specD D q Q ξ) q (fun j ↦ Q (Sum.inr j)) h)
        with hwh
      set ah : ℝ → ℝ := fun h ↦ atr ξ (truthOf ρ (specD D q Q ξ) q (fun j ↦ Q (Sum.inr j)) h)
        with hah
      have hc : 0 < cξ := mul_pos (specB_pos hB κ hξ') (Real.rpow_pos_of_pos hρ _)
      have hwhm : Measurable wh := hWtrm.comp (measurable_const.prodMk
        (continuous_truthOf ρ (specD D q Q ξ) q (fun j ↦ Q (Sum.inr j))).measurable)
      have hahm : Measurable ah := hatrm.comp (measurable_const.prodMk
        (continuous_truthOf ρ (specD D q Q ξ) q (fun j ↦ Q (Sum.inr j))).measurable)
      have hwb : ∀ h, h₀ < h → 0 ≤ wh h ∧ wh h ≤ Wstar := fun h hh ↦
        hWtrb ξ _ (truthOf_mem_Ioo hρ hDξ hq (fun j ↦ Q (Sum.inr j)) hh)
      have hab' : ∀ h, h₀ < h → amin ≤ ah h := fun h hh ↦
        hatrb ξ _ (truthOf_mem_Ioo hρ hDξ hq (fun j ↦ Q (Sum.inr j)) hh)
      rw [lintegral_mul_const _ (measurable_vWeightT _ _ _ _ _ hwhm hahm),
        lintegral_vWeightT_zero hβ hη hc hamin hwhm hahm hwb hab']
      have hint : ∫ h in Ioi h₀, Gamma β * (cξ * ah h) ^ (-β) * (exp (-(η * h)) * wh h) =
          Gamma β * cξ ^ (-β) *
            (q * (specD D q Q ξ * ρ ^ (-(∑ j, Q (Sum.inr j)) / q)) ^ (-(q * η)) * I ξ) := by
        rw [hI]
        dsimp only
        rw [← integral_Ioi_truthOf hρ hDξ hq (fun j ↦ Q (Sum.inr j))
          (fun u ↦ Wtr ξ u * atr ξ u ^ (-β)), ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun h hh ↦ ?_
        have hu := truthOf_mem_Ioo hρ hDξ hq (fun j ↦ Q (Sum.inr j)) hh
        have ha0 : 0 ≤ atr ξ (truthOf ρ (specD D q Q ξ) q (fun j ↦ Q (Sum.inr j)) h) :=
          hamin.le.trans (hatrb ξ _ hu)
        simp only [hwh, hah]
        rw [Real.mul_rpow hc.le ha0]
        ring
      rw [hint]
      have hconst := trace_const_eq (q := q) (η := η) (Q := fun j ↦ Q (Sum.inr j))
        (κ := fun j ↦ κ (Sum.inr j)) (r := fun j ↦ r (Sum.inr j)) hρ hDξ hq
        (specB_pos hB κ hξ') hrJ
      beta_reduce at hconst
      rw [← hcξ] at hconst
      have hfac := spec_const_factor' (β := β) (η := η) hD hq hB Q κ r hξ'
      have hnn : 0 ≤ ∏ i, ξ i ^ r (Sum.inl i) :=
        Finset.prod_nonneg fun i _ ↦ (Real.rpow_pos_of_pos (hξ' i) _).le
      have hS0 : 0 ≤ ρ ^ (∑ j, (r (Sum.inr j) + 1)) *
          |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ := by positivity
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hnn,
        ← ENNReal.ofReal_mul (mul_nonneg hnn hS0)]
      congr 2
      rw [hK]
      linear_combination (|(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ *
        Gamma β * q * I ξ * ∏ i, ξ i ^ r (Sum.inl i)) * hconst +
        (|(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ * Gamma β * q *
          I ξ) * hfac
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, zero_mul, mul_zero, mul_zero,
        ENNReal.ofReal_zero, zero_mul]
  simp_rw [hpt]
  rw [lintegral_mul_const' _ _ hVne]
  congr 1
  have hint : Integrable fun ξ : Fin m → ℝ ↦ I ξ *
      (K * (specBox m ρ).indicator (fun ξ ↦ ∏ i, ξ i ^ (specd β η Q κ r i - 1)) ξ) :=
    Integrable.bdd_mul (hP.const_mul K) hIm.aestronglyMeasurable (Eventually.of_forall fun ξ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hI0 ξ)]
      exact hIb ξ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ξ ↦
    mul_nonneg (hI0 ξ) (mul_nonneg hK0 (hPnn ξ)))]
  congr 1
  rw [← integral_const_mul, ← integral_indicator (measurableSet_specBox m ρ)]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  beta_reduce
  by_cases hξ : ξ ∈ specBox m ρ
  · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
    simp only [hI]
    ring
  · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]
    ring

/-! ### Dominated convergence and the theorem -/

theorem tendsto_lintegral_specFG {ρ B D γ q δ β η : ℝ} {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 0 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 1 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 1 ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i)
    {W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ} {Wstar amin : ℝ} (hamin : 0 < amin)
    (hWm : Measurable (Function.uncurry W)) (ham : Measurable (Function.uncurry a))
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u)
    {Wtr atr : (Fin m → ℝ) → ℝ → ℝ}
    (hWtr : ∀ᵐ ξ : Fin m → ℝ, ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x' ↦ W (Sum.elim ξ x') u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr ξ u)))
    (hatr : ∀ᵐ ξ : Fin m → ℝ, ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x' ↦ a (Sum.elim ξ x') u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr ξ u))) :
    Tendsto (fun t ↦ ∫⁻ ξ, specFG ρ B D γ q δ β η Q κ r W a t ξ) atTop
      (𝓝 (∫⁻ ξ, specFGlim ρ B D γ q δ β η Q κ r Wtr atr ξ)) :=
  tendsto_lintegral_filter_of_dominated_convergence
    (fun ξ ↦ ENNReal.ofReal Wstar * ENNReal.ofReal (specG ρ B D q δ β η amin Q κ r ξ))
    (Eventually.of_forall fun t ↦ measurable_specFG _ _ _ _ _ _ _ _ _ _ _ hWm ham t)
    (by
      filter_upwards [eventually_ge_atTop (exp 1)] with t ht
      exact Eventually.of_forall fun ξ ↦
        specFG_le hρ hD hq hB hβ hη hδ hκ hΔ hrJ hamin hWb hab ht ξ)
    (by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (lintegral_specG_ne_top hρ hB hamin hη hδ hκ hd))
    (by
      filter_upwards [hWtr, hatr] with ξ hW ha
      exact specFG_tendsto hρ hD hq hB hβ hη hδ hκ hΔ hc₀ hc₁ hrJ hamin hWm ham hWb hab ξ hW ha)

/-- **The transverse active-truth face theorem with spectators and general units.** On
`Fin m ⊕ (Fin k ⊕ Fin 2)` (spectators first) with jointly measurable units `W`, `a` bounded by
`0 ≤ W ≤ W_*`, `a ≥ a_- > 0`, with a.e.-spectator traces `W_tr(ξ, u)`, `a_tr(ξ, u)` as the active
coordinates tend to `0` in the box (jointly measurable, same bounds on `(0, ρ)`), the reduced
spectator costs `d_i = r_i + 1 − βκ_i + ηQ_i > 0`, and the active exponent identity
`r_j + 1 = βκ_j − ηQ_j`:
`t^{γp + βδ − ηγ}/(log t)^k · K(t) → A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ·
∫_{(0,ρ)^m} ∏ ξ_i^{d_i − 1} ∫_0^ρ u^{qη−1} W_tr(ξ,u) a_tr(ξ,u)^{-β} du dξ`. -/
theorem tendsto_modelKernel_general_spectator {ρ A B D γ p q δ β η : ℝ}
    {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 0 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 1 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 1 ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i)
    {W a : (Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) → ℝ → ℝ} {Wstar amin : ℝ} (hamin : 0 < amin)
    (hWm : Measurable (Function.uncurry W)) (ham : Measurable (Function.uncurry a))
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u)
    {Wtr atr : (Fin m → ℝ) → ℝ → ℝ} (hWtrm : Measurable (Function.uncurry Wtr))
    (hatrm : Measurable (Function.uncurry atr))
    (hWtrb : ∀ ξ, ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ Wtr ξ u ∧ Wtr ξ u ≤ Wstar)
    (hatrb : ∀ ξ, ∀ u ∈ Ioo (0 : ℝ) ρ, amin ≤ atr ξ u)
    (hWtr : ∀ᵐ ξ : Fin m → ℝ, ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x' ↦ W (Sum.elim ξ x') u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr ξ u)))
    (hatr : ∀ᵐ ξ : Fin m → ℝ, ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x' ↦ a (Sum.elim ξ x') u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr ξ u))) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r W a t) atTop
      (𝓝 (A * Gamma β * B ^ (-β) * q * D ^ (-(q * η)) *
        (volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ)).toReal /
        |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det| *
        ∫ ξ in specBox m ρ, (∏ i, ξ i ^ (specd β η Q κ r i - 1)) *
          ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr ξ u * atr ξ u ^ (-β)))) := by
  have hlim := tendsto_lintegral_specFG hρ hD hq hB hβ hη hδ hκ hΔ hc₀ hc₁ hrJ hd hamin hWm ham
    hWb hab hWtr hatr
  rw [lintegral_specFGlim hρ hD hq hB hβ hη hκ hΔ hrJ hd hamin hWtrm hatrm hWtrb hatrb] at hlim
  set V := volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ) with hV
  have hVne : V ≠ ⊤ := volume_facePolytope_ne_top hΔ (fun j ↦ hκ _) δ γ
  set J := ∫ ξ in specBox m ρ, (∏ i, ξ i ^ (specd β η Q κ r i - 1)) *
    ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr ξ u * atr ξ u ^ (-β)) with hJ
  have hJ0 : 0 ≤ J := by
    rw [hJ]
    refine setIntegral_nonneg (measurableSet_specBox m ρ) fun ξ hξ ↦ ?_
    have hξ' : ∀ i, 0 < ξ i := fun i ↦ ((Set.mem_univ_pi.mp hξ) i).1
    refine mul_nonneg (Finset.prod_nonneg fun i _ ↦ (Real.rpow_pos_of_pos (hξ' i) _).le) ?_
    refine setIntegral_nonneg measurableSet_Ioo fun u hu ↦ ?_
    exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (mul_nonneg (hWtrb ξ u hu).1
      (Real.rpow_nonneg (hamin.le.trans (hatrb ξ u hu)) _))
  set K := |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ *
    (Gamma β * (B ^ (-β) * (q * D ^ (-(q * η))))) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := Real.Gamma_pos_of_pos hβ
    positivity
  have hne : ENNReal.ofReal (K * J) * V ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVne
  have hlim2 := ((ENNReal.tendsto_toReal hne).comp hlim).const_mul A
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hK0 hJ0)] at hlim2
  have hval : A * (K * J * V.toReal) = A * Gamma β * B ^ (-β) * q * D ^ (-(q * η)) * V.toReal /
      |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det| * J := by
    rw [hK]
    ring
  rw [hval] at hlim2
  refine hlim2.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hL : 0 < log t := Real.log_pos ht
  simp only [Function.comp]
  have hKer : modelKernel ρ A B D γ p q δ Q κ r W a t =
      A * t ^ (-(γ * p)) * (∫⁻ x, ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r W a t x)).toReal := by
    unfold modelKernel
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (modelIntegrand_nonneg_of_nonneg (fun x u ↦ (hWb x u).1)))
      (measurable_modelIntegrand hWm ham t).aestronglyMeasurable]
  rw [hKer, lintegral_modelIntegrand_spectator_general _ _ _ _ _ _ _ _ _ _ hWm ham]
  have hF : ∫⁻ ξ, specFG ρ B D γ q δ β η Q κ r W a t ξ =
      ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        ∫⁻ ξ : Fin m → ℝ, ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal
          (modelIntegrand ρ B D γ q δ Q κ r W a t (Sum.elim ξ x')) := by
    simp_rw [specFG_eq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hF, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have e1 : t ^ (γ * p + (β * δ - η * γ)) = t ^ (γ * p) * t ^ (β * δ - η * γ) :=
    Real.rpow_add ht0 _ _
  have e2 : t ^ (-(γ * p)) = (t ^ (γ * p))⁻¹ := Real.rpow_neg ht0.le _
  rw [e1, e2]
  have hpos : t ^ (γ * p) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  have hLk : log t ^ k ≠ 0 := (pow_pos hL k).ne'
  field_simp

end Laplace.Multi
