/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SpectatorEnvelope

/-!
# The transverse active-truth face theorem with spectator coordinates

Astra round 8, item 2. On the index `Fin m ⊕ (Fin k ⊕ Fin 2)` the first `m` coordinates are
spectators `ξ` with positive reduced costs `d_i = r_i + 1 − βκ_i + ηQ_i`, and the last `k + 2`
are the active coordinates of the face. Freezing `ξ`, the model integrand is `∏ ξ^{r_I}` times the
active-coordinate integrand with the Boltzmann constant `B_ξ = B ∏ ξ^{κ_I}` and the truth constant
`D_ξ = D ∏ ξ^{−Q_I/q}` (`modelIntegrand_sum_elim`); the constant-unit face theorem applies pointwise
in `ξ` and its uniform bound (`normalised_lintegral_le`) gives the domination
`C ∏ ξ_i^{d_i − 1} (1 + κ_i |log ξ_i|)^k` (`spec_const_factor`, `abs_log_specC_le`), so an outer
dominated convergence yields the extra factor `∏ ρ^{d_i}/d_i`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {m k : ℕ}

/-- The Boltzmann constant with the spectators frozen: `B ∏ ξ^{κ_I}`. -/
noncomputable def specB (B : ℝ) (κ : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) (ξ : Fin m → ℝ) : ℝ :=
  B * ∏ i, ξ i ^ κ (Sum.inl i)

/-- The truth constant with the spectators frozen: `D ∏ ξ^{−Q_I/q}`. -/
noncomputable def specD (D q : ℝ) (Q : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) (ξ : Fin m → ℝ) : ℝ :=
  D * ∏ i, ξ i ^ (-(Q (Sum.inl i) / q))

theorem specB_pos {B : ℝ} (hB : 0 < B) (κ : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) {ξ : Fin m → ℝ}
    (hξ : ∀ i, 0 < ξ i) : 0 < specB B κ ξ :=
  mul_pos hB (Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hξ i) _)

theorem specD_pos {D : ℝ} (hD : 0 < D) (q : ℝ) (Q : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) {ξ : Fin m → ℝ}
    (hξ : ∀ i, 0 < ξ i) : 0 < specD D q Q ξ :=
  mul_pos hD (Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hξ i) _)

/-- The spectator box `(0, ρ)^m`. -/
abbrev specBox (m : ℕ) (ρ : ℝ) : Set (Fin m → ℝ) := Set.pi univ fun _ : Fin m ↦ Ioo (0 : ℝ) ρ

theorem measurableSet_specBox (m : ℕ) (ρ : ℝ) : MeasurableSet (specBox m ρ) :=
  MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo

theorem cutVar_sum_elim (D γ q t : ℝ) (Q : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) (ξ : Fin m → ℝ)
    (x' : Fin k ⊕ Fin 2 → ℝ) :
    cutVar D γ q Q t (Sum.elim ξ x') = cutVar (specD D q Q ξ) γ q (fun j ↦ Q (Sum.inr j)) t x' := by
  unfold cutVar specD
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

/-- **Freezing the spectators**: the model integrand factors as `1_{ξ ∈ (0,ρ)^m} ∏ ξ^{r_I}` times
the active-coordinate integrand with `B_ξ`, `D_ξ`. -/
theorem modelIntegrand_sum_elim (ρ B D γ q δ a₀ t : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    (ξ : Fin m → ℝ) (x' : Fin k ⊕ Fin 2 → ℝ) :
    modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t (Sum.elim ξ x') =
      (specBox m ρ).indicator (fun ξ ↦ ∏ i, ξ i ^ r (Sum.inl i)) ξ *
        modelIntegrand ρ (specB B κ ξ) (specD D q Q ξ) γ q δ (fun j ↦ Q (Sum.inr j))
          (fun j ↦ κ (Sum.inr j)) (fun j ↦ r (Sum.inr j)) (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x' := by
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
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, hprod, hprod]
      unfold specB
      rw [show B * t ^ δ * a₀ * ((∏ i, ξ i ^ κ (Sum.inl i)) * ∏ j, x' j ^ κ (Sum.inr j)) =
        (B * ∏ i, ξ i ^ κ (Sum.inl i)) * t ^ δ * a₀ * ∏ j, x' j ^ κ (Sum.inr j) by ring]
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

/-- Fubini over the spectators. -/
theorem lintegral_modelIntegrand_spectator (ρ B D γ q δ a₀ t : ℝ)
    (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) :
    ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x) =
      ∫⁻ ξ : Fin m → ℝ, (specBox m ρ).indicator
        (fun ξ ↦ ENNReal.ofReal (∏ i, ξ i ^ r (Sum.inl i))) ξ *
        ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal (modelIntegrand ρ (specB B κ ξ) (specD D q Q ξ)
          γ q δ (fun j ↦ Q (Sum.inr j)) (fun j ↦ κ (Sum.inr j)) (fun j ↦ r (Sum.inr j))
          (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x') := by
  rw [lintegral_sum_split (F := fun x ↦ ENNReal.ofReal
    (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x))
    (ENNReal.measurable_ofReal.comp
      (measurable_modelIntegrand measurable_const measurable_const t))]
  refine lintegral_congr fun ξ ↦ ?_
  simp_rw [modelIntegrand_sum_elim]
  by_cases hξ : ξ ∈ specBox m ρ
  · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x' ↦ ?_
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ ↦
      Real.rpow_nonneg ((Set.mem_univ_pi.mp hξ) i).1.le _)]
  · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, zero_mul]
    simp

/-- The factor `∏ ξ^{r_I} c₀(ξ)^{-β} e^{-ηh₀(ξ)}` in closed form. -/
theorem spec_const_factor {ρ B D q β η a₀ : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    (hB : 0 < B) (ha₀ : 0 < a₀) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) {ξ : Fin m → ℝ}
    (hξ : ∀ i, 0 < ξ i) :
    (∏ i, ξ i ^ r (Sum.inl i)) *
      ((specB B κ ξ * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) *
        exp (-(η * -(q * log (ρ / specD D q Q ξ) + (∑ j, Q (Sum.inr j)) * log ρ)))) =
      (B * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) *
        exp (-(η * -(q * log (ρ / D) + (∑ j, Q (Sum.inr j)) * log ρ))) *
        ∏ i, ξ i ^ (r (Sum.inl i) - β * κ (Sum.inl i) + η * Q (Sum.inl i)) := by
  have hPκ : 0 < ∏ i, ξ i ^ κ (Sum.inl i) :=
    Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hξ i) _
  have hPQ : 0 < ∏ i, ξ i ^ (-(Q (Sum.inl i) / q)) :=
    Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hξ i) _
  have e1 : (specB B κ ξ * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) =
      (B * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) * ∏ i, ξ i ^ (-(β * κ (Sum.inl i))) := by
    unfold specB
    rw [show (B * ∏ i, ξ i ^ κ (Sum.inl i)) * a₀ * ρ ^ (∑ j, κ (Sum.inr j)) =
      (B * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) * ∏ i, ξ i ^ κ (Sum.inl i) by ring,
      Real.mul_rpow (by positivity) hPκ.le, ← Real.finsetProd_rpow _ _ fun i _ ↦
        (Real.rpow_pos_of_pos (hξ i) _).le]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← Real.rpow_mul (hξ i).le]
    congr 1
    ring
  have e2 : exp (-(η * -(q * log (ρ / specD D q Q ξ) + (∑ j, Q (Sum.inr j)) * log ρ))) =
      exp (-(η * -(q * log (ρ / D) + (∑ j, Q (Sum.inr j)) * log ρ))) *
        ∏ i, ξ i ^ (η * Q (Sum.inl i)) := by
    have hlog : log (ρ / specD D q Q ξ) =
        log (ρ / D) + (1 / q) * ∑ i, Q (Sum.inl i) * log (ξ i) := by
      unfold specD
      rw [div_mul_eq_div_div, Real.log_div (div_pos hρ hD).ne' hPQ.ne',
        Real.log_prod fun i _ ↦ (Real.rpow_pos_of_pos (hξ i) _).ne',
        Finset.sum_congr rfl fun i _ ↦ Real.log_rpow (hξ i) _, sub_eq_add_neg,
        ← Finset.sum_neg_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      field_simp
    have hS : ∑ i, log (ξ i) * (η * Q (Sum.inl i)) = η * ∑ i, Q (Sum.inl i) * log (ξ i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hlog, Finset.prod_congr rfl fun i _ ↦ Real.rpow_def_of_pos (hξ i) (η * Q (Sum.inl i)),
      ← Real.exp_sum, ← Real.exp_add, hS]
    congr 1
    field_simp
    ring
  rw [e1, e2]
  have e3 : ∀ i, ξ i ^ r (Sum.inl i) * (ξ i ^ (-(β * κ (Sum.inl i))) * ξ i ^ (η * Q (Sum.inl i)))
      = ξ i ^ (r (Sum.inl i) - β * κ (Sum.inl i) + η * Q (Sum.inl i)) := fun i ↦ by
    rw [← Real.rpow_add (hξ i), ← Real.rpow_add (hξ i)]
    congr 1
    ring
  calc (∏ i, ξ i ^ r (Sum.inl i)) *
        ((B * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) * (∏ i, ξ i ^ (-(β * κ (Sum.inl i)))) *
          (exp (-(η * -(q * log (ρ / D) + (∑ j, Q (Sum.inr j)) * log ρ))) *
            ∏ i, ξ i ^ (η * Q (Sum.inl i))))
      = (B * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) *
          exp (-(η * -(q * log (ρ / D) + (∑ j, Q (Sum.inr j)) * log ρ))) *
          ∏ i, ξ i ^ r (Sum.inl i) *
            (ξ i ^ (-(β * κ (Sum.inl i))) * ξ i ^ (η * Q (Sum.inl i))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ring
    _ = _ := by rw [Finset.prod_congr rfl fun i _ ↦ e3 i]

/-- `|log c₀(ξ)| ≤ |log c₀| + ∑ κ_i |log ξ_i|`. -/
theorem abs_log_specC_le {ρ B a₀ : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (ha₀ : 0 < a₀)
    (κ : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) {ξ : Fin m → ℝ} (hξ : ∀ i, 0 < ξ i) :
    |log (specB B κ ξ * a₀ * ρ ^ (∑ j, κ (Sum.inr j)))| ≤
      |log (B * a₀ * ρ ^ (∑ j, κ (Sum.inr j)))| + ∑ i, |κ (Sum.inl i)| * |log (ξ i)| := by
  have hPκ : 0 < ∏ i, ξ i ^ κ (Sum.inl i) :=
    Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hξ i) _
  have hc : 0 < B * a₀ * ρ ^ (∑ j, κ (Sum.inr j)) := by positivity
  unfold specB
  rw [show (B * ∏ i, ξ i ^ κ (Sum.inl i)) * a₀ * ρ ^ (∑ j, κ (Sum.inr j)) =
    (B * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) * ∏ i, ξ i ^ κ (Sum.inl i) by ring,
    Real.log_mul hc.ne' hPκ.ne', Real.log_prod fun i _ ↦ (Real.rpow_pos_of_pos (hξ i) _).ne',
    Finset.sum_congr rfl fun i _ ↦ Real.log_rpow (hξ i) _]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ((Finset.abs_sum_le_sum_abs _ _).trans ?_))
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [abs_mul]

/-! ### The frozen-spectator normalised integral -/

/-- The unit-weight integrand is nonnegative. -/
theorem modelIntegrand_one_nonneg {ι : Type*} [Fintype ι] (ρ B D γ q δ a₀ t : ℝ)
    (Q κ r : ι → ℝ) (x : ι → ℝ) :
    0 ≤ modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q Q t
  · rw [Set.indicator_of_mem hx]
    have hx0 : ∀ i, 0 ≤ x i := fun i ↦ ((Set.mem_univ_pi.mp hx.1) i).1.le
    exact mul_nonneg (mul_nonneg zero_le_one (Finset.prod_nonneg fun i _ ↦
      Real.rpow_nonneg (hx0 i) _)) (exp_pos _).le
  · rw [Set.indicator_of_notMem hx]

/-- The weight `w₀` factors out of the model integrand. -/
theorem modelIntegrand_const_weight {ι : Type*} [Fintype ι] (ρ B D γ q δ w₀ a₀ t : ℝ)
    (Q κ r : ι → ℝ) (x : ι → ℝ) :
    modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t x =
      w₀ * modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q Q t
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

/-- The normalised active-coordinate integral with the spectators frozen at `ξ`. -/
noncomputable def specInner (ρ B D γ q δ β η a₀ : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    (ξ : Fin m → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
    ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal (modelIntegrand ρ (specB B κ ξ) (specD D q Q ξ)
      γ q δ (fun j ↦ Q (Sum.inr j)) (fun j ↦ κ (Sum.inr j)) (fun j ↦ r (Sum.inr j))
      (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x')

/-- The spectator integrand: `1_{(0,ρ)^m}(ξ) ∏ ξ^{r_I}` times the frozen normalised integral. -/
noncomputable def specF (ρ B D γ q δ β η a₀ : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) (t : ℝ)
    (ξ : Fin m → ℝ) : ℝ≥0∞ :=
  (specBox m ρ).indicator (fun ξ ↦ ENNReal.ofReal (∏ i, ξ i ^ r (Sum.inl i))) ξ *
    specInner ρ B D γ q δ β η a₀ Q κ r ξ t

theorem specF_eq (ρ B D γ q δ β η a₀ : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) (t : ℝ)
    (ξ : Fin m → ℝ) :
    specF ρ B D γ q δ β η a₀ Q κ r t ξ = ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
      ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t (Sum.elim ξ x')) := by
  unfold specF specInner
  simp_rw [modelIntegrand_sum_elim]
  by_cases hξ : ξ ∈ specBox m ρ
  · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
    have hnn : 0 ≤ ∏ i, ξ i ^ r (Sum.inl i) := Finset.prod_nonneg fun i _ ↦
      Real.rpow_nonneg ((Set.mem_univ_pi.mp hξ) i).1.le _
    simp_rw [ENNReal.ofReal_mul hnn]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring
  · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, zero_mul]
    simp

theorem measurable_specF (ρ B D γ q δ β η a₀ : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    (t : ℝ) : Measurable (specF ρ B D γ q δ β η a₀ Q κ r t) := by
  rw [show specF ρ B D γ q δ β η a₀ Q κ r t = fun ξ ↦ _ from
    funext (specF_eq _ _ _ _ _ _ _ _ _ _ _ _ t)]
  refine Measurable.const_mul ?_ _
  refine Measurable.lintegral_prod_right (f := fun (ξ : Fin m → ℝ) (x' : Fin k ⊕ Fin 2 → ℝ) ↦
    ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t
      (Sum.elim ξ x'))) ?_
  have e : (Function.uncurry fun (ξ : Fin m → ℝ) (x' : Fin k ⊕ Fin 2 → ℝ) ↦
      ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t
        (Sum.elim ξ x'))) =
      (fun x ↦ ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x))
        ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ (Fin k ⊕ Fin 2) ↦ ℝ)).symm := by
    funext p
    rfl
  rw [e]
  exact (ENNReal.measurable_ofReal.comp
    (measurable_modelIntegrand measurable_const measurable_const t)).comp
    (MeasurableEquiv.measurable _)


/-! ### Domination and the pointwise limit -/

/-- The reduced cost of a spectator: `d_i = r_i + 1 − βκ_i + ηQ_i`. -/
noncomputable def specd (β η : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) (i : Fin m) : ℝ :=
  r (Sum.inl i) + 1 - β * κ (Sum.inl i) + η * Q (Sum.inl i)

/-- The dominating constant of the spectator integrand. -/
noncomputable def specK (ρ B D q δ β η a₀ : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) : ℝ :=
  ρ ^ (∑ j, (r (Sum.inr j) + 1)) *
    |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ *
    ((B * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) *
      (1 + δ + |log (B * a₀ * ρ ^ (∑ j, κ (Sum.inr j)))|) ^ k *
      (∫ s, sWeight β 1 s * (|s| + 1) ^ k) / (∏ i : Fin k, κ (Sum.inr (Sum.inl i))) *
      (exp (-(η * -(q * log (ρ / D) + (∑ j, Q (Sum.inr j)) * log ρ))) / η))

/-- The dominating function: `K ∏ 1_{(0,ρ)}(ξ_i) ξ_i^{d_i − 1} (1 + |κ_i| |log ξ_i|)^k`. -/
noncomputable def specG (ρ B D q δ β η a₀ : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    (ξ : Fin m → ℝ) : ℝ :=
  specK ρ B D q δ β η a₀ Q κ r * ∏ i, (Ioo (0 : ℝ) ρ).indicator
    (fun x ↦ x ^ (specd β η Q κ r i - 1) * (1 + |κ (Sum.inl i)| * |log x|) ^ k) (ξ i)

theorem prod_indicator_Ioo_of_mem {ρ : ℝ} (g : Fin m → ℝ → ℝ) {ξ : Fin m → ℝ}
    (hξ : ξ ∈ specBox m ρ) :
    ∏ i, (Ioo (0 : ℝ) ρ).indicator (g i) (ξ i) = ∏ i, g i (ξ i) :=
  Finset.prod_congr rfl fun i _ ↦ Set.indicator_of_mem ((Set.mem_univ_pi.mp hξ) i) _

theorem prod_indicator_Ioo_of_notMem {ρ : ℝ} (g : Fin m → ℝ → ℝ) {ξ : Fin m → ℝ}
    (hξ : ξ ∉ specBox m ρ) :
    ∏ i, (Ioo (0 : ℝ) ρ).indicator (g i) (ξ i) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, ξ i ∉ Ioo (0 : ℝ) ρ := by
    by_contra h
    push Not at h
    exact hξ (Set.mem_univ_pi.mpr h)
  exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

theorem specK_nonneg {ρ B D q δ β η a₀ : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (ha₀ : 0 < a₀)
    (hη : 0 < η) (hδ : 0 ≤ δ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) (hκ : ∀ i, 0 < κ i) :
    0 ≤ specK ρ B D q δ β η a₀ Q κ r := by
  unfold specK
  have hP : 0 < ∏ i : Fin k, κ (Sum.inr (Sum.inl i)) := Finset.prod_pos fun i _ ↦ hκ _
  have hCk : 0 ≤ ∫ s, sWeight β 1 s * (|s| + 1) ^ k :=
    integral_nonneg fun s ↦ mul_nonneg (sWeight_nonneg _ _ _) (by positivity)
  have hc : 0 < B * a₀ * ρ ^ (∑ j, κ (Sum.inr j)) := by positivity
  have h1 : 0 ≤ (B * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) := (Real.rpow_pos_of_pos hc _).le
  refine mul_nonneg (mul_nonneg (Real.rpow_nonneg hρ.le _) (inv_nonneg.mpr (abs_nonneg _))) ?_
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg h1 (pow_nonneg ?_ _)) hCk) hP.le)
    (div_nonneg (exp_pos _).le hη.le)
  positivity

theorem specG_nonneg {ρ B D q δ β η a₀ : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (ha₀ : 0 < a₀)
    (hη : 0 < η) (hδ : 0 ≤ δ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ) (hκ : ∀ i, 0 < κ i)
    (ξ : Fin m → ℝ) : 0 ≤ specG ρ B D q δ β η a₀ Q κ r ξ := by
  unfold specG
  refine mul_nonneg (specK_nonneg hρ hB ha₀ hη hδ Q κ r hκ) (Finset.prod_nonneg fun i _ ↦ ?_)
  exact Set.indicator_nonneg (fun x hx ↦ mul_nonneg (Real.rpow_nonneg hx.1.le _)
    (by positivity)) _

/-- **Domination**: for `t ≥ e`, `specF t ξ ≤ specG ξ`. -/
theorem specF_le {ρ B D γ q δ β η a₀ t : ℝ} {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (ha₀ : 0 < a₀) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j)) (ht : exp 1 ≤ t)
    (ξ : Fin m → ℝ) :
    specF ρ B D γ q δ β η a₀ Q κ r t ξ ≤ ENNReal.ofReal (specG ρ B D q δ β η a₀ Q κ r ξ) := by
  by_cases hξ : ξ ∈ specBox m ρ
  · have hξ' : ∀ i, 0 < ξ i := fun i ↦ ((Set.mem_univ_pi.mp hξ) i).1
    unfold specF specInner
    rw [Set.indicator_of_mem hξ]
    have hb := normalised_lintegral_le (γ := γ) (Q := fun j ↦ Q (Sum.inr j))
      (κ := fun j ↦ κ (Sum.inr j)) (r := fun j ↦ r (Sum.inr j)) hρ (specD_pos hD q Q hξ') hq
      (specB_pos hB κ hξ') ha₀ hβ hη hδ (fun j ↦ hκ _) hΔ hrJ ht
    beta_reduce at hb
    have hnn : 0 ≤ ∏ i, ξ i ^ r (Sum.inl i) :=
      Finset.prod_nonneg fun i _ ↦ (Real.rpow_pos_of_pos (hξ' i) _).le
    refine (mul_le_mul_of_nonneg_left hb zero_le).trans ?_
    rw [← ENNReal.ofReal_mul hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [specG, prod_indicator_Ioo_of_mem _ hξ]
    unfold specK
    set cξ := specB B κ ξ * a₀ * ρ ^ (∑ j, κ (Sum.inr j)) with hcξ
    set cJ := B * a₀ * ρ ^ (∑ j, κ (Sum.inr j)) with hcJ
    set Eξ := exp (-(η * -(q * log (ρ / specD D q Q ξ) + (∑ j, Q (Sum.inr j)) * log ρ)))
      with hEξ
    set EJ := exp (-(η * -(q * log (ρ / D) + (∑ j, Q (Sum.inr j)) * log ρ))) with hEJ
    set P := ∏ i : Fin k, κ (Sum.inr (Sum.inl i)) with hP
    set Ck := ∫ s, sWeight β 1 s * (|s| + 1) ^ k with hCk
    set C₁ := 1 + δ + |log cJ| with hC₁
    set S := ρ ^ (∑ j, (r (Sum.inr j) + 1)) *
      |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ with hS
    have hcξ0 : 0 < cξ := by
      rw [hcξ]; exact mul_pos (mul_pos (specB_pos hB κ hξ') ha₀) (Real.rpow_pos_of_pos hρ _)
    have hP0 : 0 < P := Finset.prod_pos fun i _ ↦ hκ _
    have hCk0 : 0 ≤ Ck := integral_nonneg fun s ↦ mul_nonneg (sWeight_nonneg _ _ _) (by positivity)
    have hC₁1 : 1 ≤ C₁ := by rw [hC₁]; linarith [abs_nonneg (log cJ)]
    have hS0 : 0 ≤ S := by rw [hS]; positivity
    have hEξ0 : 0 < Eξ := exp_pos _
    have hI := integral_sWeight_mul_pow_le hβ hcξ0 hδ k
    have hlog : 1 + δ + |log cξ| ≤ C₁ + ∑ i, |κ (Sum.inl i)| * |log (ξ i)| := by
      have := abs_log_specC_le hρ hB ha₀ κ hξ'
      rw [hC₁]
      linarith
    have hprod := add_sum_le_prod Finset.univ hC₁1
      (fun i ↦ mul_nonneg (abs_nonneg (κ (Sum.inl i))) (abs_nonneg (log (ξ i))))
    have hpow : (1 + δ + |log cξ|) ^ k ≤ C₁ ^ k * ∏ i, (1 + |κ (Sum.inl i)| * |log (ξ i)|) ^ k := by
      rw [Finset.prod_pow, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (hlog.trans hprod) k
    have hfac := spec_const_factor (β := β) (η := η) hρ hD hq hB ha₀ Q κ r hξ'
    have hcξβ : 0 ≤ cξ ^ (-β) := (Real.rpow_pos_of_pos hcξ0 _).le
    calc (∏ i, ξ i ^ r (Sum.inl i)) * (S * ((∫ s, sWeight β cξ s * (|s| + δ) ^ k) / P * (Eξ / η)))
        ≤ (∏ i, ξ i ^ r (Sum.inl i)) *
          (S * ((cξ ^ (-β) * (C₁ ^ k * ∏ i, (1 + |κ (Sum.inl i)| * |log (ξ i)|) ^ k) * Ck) / P *
            (Eξ / η))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hP0.le)
              (div_pos hEξ0 hη).le) hS0) hnn
          refine hI.trans ?_
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hCk0) hcξβ
      _ = S * (C₁ ^ k * Ck / P * (1 / η)) * (∏ i, (1 + |κ (Sum.inl i)| * |log (ξ i)|) ^ k) *
          ((∏ i, ξ i ^ r (Sum.inl i)) * (cξ ^ (-β) * Eξ)) := by ring
      _ = S * (C₁ ^ k * Ck / P * (1 / η)) * (∏ i, (1 + |κ (Sum.inl i)| * |log (ξ i)|) ^ k) *
          (cJ ^ (-β) * EJ *
            ∏ i, ξ i ^ (r (Sum.inl i) - β * κ (Sum.inl i) + η * Q (Sum.inl i))) := by
          rw [hfac]
      _ = S * (cJ ^ (-β) * C₁ ^ k * Ck / P * (EJ / η)) *
          ∏ i, ξ i ^ (specd β η Q κ r i - 1) * (1 + |κ (Sum.inl i)| * |log (ξ i)|) ^ k := by
          rw [Finset.prod_mul_distrib]
          have e : ∀ i, ξ i ^ (r (Sum.inl i) - β * κ (Sum.inl i) + η * Q (Sum.inl i)) =
              ξ i ^ (specd β η Q κ r i - 1) := fun i ↦ by
            congr 1
            unfold specd
            ring
          simp_rw [e]
          ring
  · unfold specF
    rw [Set.indicator_of_notMem hξ, zero_mul]
    exact zero_le

/-- The pointwise limit of the spectator integrand. -/
noncomputable def specFlim (ρ B D γ q δ β η a₀ : ℝ) (Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ)
    (ξ : Fin m → ℝ) : ℝ≥0∞ :=
  (specBox m ρ).indicator (fun ξ ↦ ENNReal.ofReal (∏ i, ξ i ^ r (Sum.inl i))) ξ *
    (ENNReal.ofReal (ρ ^ (∑ j, (r (Sum.inr j) + 1)) *
        |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹) *
      (ENNReal.ofReal (Gamma β * (specB B κ ξ * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) *
          (exp (-(η * -(q * log (ρ / specD D q Q ξ) + (∑ j, Q (Sum.inr j)) * log ρ))) / η)) *
        volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ)))

theorem specF_tendsto {ρ B D γ q δ β η a₀ : ℝ} {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (ha₀ : 0 < a₀) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 0 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 1 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 1 ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j)) (ξ : Fin m → ℝ) :
    Tendsto (fun t ↦ specF ρ B D γ q δ β η a₀ Q κ r t ξ) atTop
      (𝓝 (specFlim ρ B D γ q δ β η a₀ Q κ r ξ)) := by
  by_cases hξ : ξ ∈ specBox m ρ
  · have hξ' : ∀ i, 0 < ξ i := fun i ↦ ((Set.mem_univ_pi.mp hξ) i).1
    unfold specF specFlim specInner
    rw [Set.indicator_of_mem hξ]
    exact ENNReal.Tendsto.const_mul (tendsto_normalised_lintegral (Q := fun j ↦ Q (Sum.inr j))
      (κ := fun j ↦ κ (Sum.inr j)) (r := fun j ↦ r (Sum.inr j)) hρ (specD_pos hD q Q hξ') hq
      (specB_pos hB κ hξ') ha₀ hβ hη hδ (fun j ↦ hκ _) hΔ hc₀ hc₁ hrJ)
      (Or.inr ENNReal.ofReal_ne_top)
  · simp only [specF, specFlim, Set.indicator_of_notMem hξ, zero_mul]
    exact tendsto_const_nhds

theorem integrable_specG {ρ B D q δ β η a₀ : ℝ} (hρ : 0 < ρ) {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ}
    (hd : ∀ i, 0 < specd β η Q κ r i) : Integrable (specG ρ B D q δ β η a₀ Q κ r) := by
  unfold specG
  refine Integrable.const_mul ?_ _
  have := Integrable.fintype_prod (μ := fun _ : Fin m ↦ (volume : Measure ℝ))
    (f := fun i x ↦ (Ioo (0 : ℝ) ρ).indicator
      (fun x ↦ x ^ (specd β η Q κ r i - 1) * (1 + |κ (Sum.inl i)| * |log x|) ^ k) x)
    (fun i ↦ (integrableOn_rpow_mul_log_pow (hd i) zero_le_one (abs_nonneg _) hρ
      k).integrable_indicator measurableSet_Ioo)
  rw [volume_pi]
  exact this

theorem lintegral_specG_ne_top {ρ B D q δ β η a₀ : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (ha₀ : 0 < a₀)
    (hη : 0 < η) (hδ : 0 ≤ δ) {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ} (hκ : ∀ i, 0 < κ i)
    (hd : ∀ i, 0 < specd β η Q κ r i) :
    ∫⁻ ξ, ENNReal.ofReal (specG ρ B D q δ β η a₀ Q κ r ξ) ≠ ⊤ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_specG hρ hd)
    (Eventually.of_forall (specG_nonneg hρ hB ha₀ hη hδ Q κ r hκ))]
  exact ENNReal.ofReal_ne_top


/-! ### Dominated convergence over the spectators, and the theorem -/

theorem tendsto_lintegral_specF {ρ B D γ q δ β η a₀ : ℝ} {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (ha₀ : 0 < a₀) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 0 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 1 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 1 ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i) :
    Tendsto (fun t ↦ ∫⁻ ξ, specF ρ B D γ q δ β η a₀ Q κ r t ξ) atTop
      (𝓝 (∫⁻ ξ, specFlim ρ B D γ q δ β η a₀ Q κ r ξ)) :=
  tendsto_lintegral_filter_of_dominated_convergence
    (fun ξ ↦ ENNReal.ofReal (specG ρ B D q δ β η a₀ Q κ r ξ))
    (Eventually.of_forall fun t ↦ measurable_specF _ _ _ _ _ _ _ _ _ _ _ _ t)
    (by
      filter_upwards [eventually_ge_atTop (exp 1)] with t ht
      exact Eventually.of_forall fun ξ ↦ specF_le hρ hD hq hB ha₀ hβ hη hδ hκ hΔ hrJ ht ξ)
    (lintegral_specG_ne_top hρ hB ha₀ hη hδ hκ hd)
    (Eventually.of_forall fun ξ ↦ specF_tendsto hρ hD hq hB ha₀ hβ hη hδ hκ hΔ hc₀ hc₁ hrJ ξ)

/-- The limit integral, evaluated: the face constant times `∏ ρ^{d_i}/d_i`. -/
theorem lintegral_specFlim {ρ B D γ q δ β η a₀ : ℝ} {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (ha₀ : 0 < a₀) (hβ : 0 < β)
    (hη : 0 < η) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hd : ∀ i, 0 < specd β η Q κ r i) :
    ∫⁻ ξ, specFlim ρ B D γ q δ β η a₀ Q κ r ξ =
      ENNReal.ofReal (ρ ^ (∑ j, (r (Sum.inr j) + 1)) *
        |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ *
        (Gamma β * ((B * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) *
          (exp (-(η * -(q * log (ρ / D) + (∑ j, Q (Sum.inr j)) * log ρ))) / η))) *
        ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i) *
      volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ) := by
  set S := ρ ^ (∑ j, (r (Sum.inr j) + 1)) *
    |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ with hS
  set cJ := B * a₀ * ρ ^ (∑ j, κ (Sum.inr j)) with hcJ
  set EJ := exp (-(η * -(q * log (ρ / D) + (∑ j, Q (Sum.inr j)) * log ρ))) with hEJ
  set V := volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ) with hV
  have hVne : V ≠ ⊤ := volume_facePolytope_ne_top hΔ (fun j ↦ hκ _) δ γ
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hcJ0 : 0 < cJ := by rw [hcJ]; positivity
  have hK0 : 0 ≤ S * (Gamma β * (cJ ^ (-β) * (EJ / η))) :=
    mul_nonneg hS0 (mul_nonneg (Real.Gamma_pos_of_pos hβ).le
      (mul_nonneg (Real.rpow_pos_of_pos hcJ0 _).le (div_pos (exp_pos _) hη).le))
  have hg : ∀ i, IntegrableOn (fun x : ℝ ↦ x ^ (specd β η Q κ r i - 1)) (Ioo (0 : ℝ) ρ) := by
    intro i
    have := integrableOn_rpow_mul_log_pow (hd i) zero_le_one le_rfl hρ 0
    refine this.congr_fun (fun x _ ↦ ?_) measurableSet_Ioo
    simp
  have hpt : ∀ ξ, specFlim ρ B D γ q δ β η a₀ Q κ r ξ =
      ENNReal.ofReal (S * (Gamma β * (cJ ^ (-β) * (EJ / η))) *
        ∏ i, (Ioo (0 : ℝ) ρ).indicator (fun x ↦ x ^ (specd β η Q κ r i - 1)) (ξ i)) * V := by
    intro ξ
    unfold specFlim
    by_cases hξ : ξ ∈ specBox m ρ
    · have hξ' : ∀ i, 0 < ξ i := fun i ↦ ((Set.mem_univ_pi.mp hξ) i).1
      rw [Set.indicator_of_mem hξ, prod_indicator_Ioo_of_mem _ hξ]
      have hnn : 0 ≤ ∏ i, ξ i ^ r (Sum.inl i) :=
        Finset.prod_nonneg fun i _ ↦ (Real.rpow_pos_of_pos (hξ' i) _).le
      have hfac := spec_const_factor (q := q) (β := β) (η := η) hρ hD hq hB ha₀ Q κ r hξ'
      have e : ∀ i, ξ i ^ (r (Sum.inl i) - β * κ (Sum.inl i) + η * Q (Sum.inl i)) =
          ξ i ^ (specd β η Q κ r i - 1) := fun i ↦ by
        congr 1
        unfold specd
        ring
      simp_rw [e] at hfac
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hnn,
        ← ENNReal.ofReal_mul (mul_nonneg hnn hS0)]
      congr 2
      calc (∏ i, ξ i ^ r (Sum.inl i)) * S *
            (Gamma β * (specB B κ ξ * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) *
              (exp (-(η * -(q * log (ρ / specD D q Q ξ) + (∑ j, Q (Sum.inr j)) * log ρ))) / η))
          = S * (Gamma β / η) * ((∏ i, ξ i ^ r (Sum.inl i)) *
              ((specB B κ ξ * a₀ * ρ ^ (∑ j, κ (Sum.inr j))) ^ (-β) *
                exp (-(η * -(q * log (ρ / specD D q Q ξ) + (∑ j, Q (Sum.inr j)) * log ρ))))) := by
            ring
        _ = _ := by rw [hfac]; ring
    · rw [Set.indicator_of_notMem hξ, prod_indicator_Ioo_of_notMem _ hξ, zero_mul, mul_zero,
        ENNReal.ofReal_zero, zero_mul]
  simp_rw [hpt]
  rw [lintegral_mul_const' _ _ hVne]
  congr 1
  have hint : Integrable fun ξ : Fin m → ℝ ↦
      ∏ i, (Ioo (0 : ℝ) ρ).indicator (fun x ↦ x ^ (specd β η Q κ r i - 1)) (ξ i) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin m ↦ (volume : Measure ℝ))
      (f := fun i x ↦ (Ioo (0 : ℝ) ρ).indicator (fun x ↦ x ^ (specd β η Q κ r i - 1)) x)
      (fun i ↦ (hg i).integrable_indicator measurableSet_Ioo)
    rw [volume_pi]
    exact this
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) (Eventually.of_forall fun ξ ↦
    mul_nonneg hK0 (Finset.prod_nonneg fun i _ ↦
      Set.indicator_nonneg (fun x hx ↦ Real.rpow_nonneg hx.1.le _) _)),
    integral_const_mul, integral_fintype_prod_volume_eq_prod
      (fun i x ↦ (Ioo (0 : ℝ) ρ).indicator (fun x ↦ x ^ (specd β η Q κ r i - 1)) x)]
  congr 2
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [integral_indicator measurableSet_Ioo, integral_Ioo_rpow_sub_one (hd i) hρ]

/-- The model kernel with weight `w₀` as `A w₀ t^{-γp}` times the `lintegral` of the unit-weight
integrand. -/
theorem modelKernel_const_eq_toReal {ι : Type*} [Fintype ι] (ρ A B D γ p q δ w₀ a₀ t : ℝ)
    (Q κ r : ι → ℝ) :
    modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t =
      A * t ^ (-(γ * p)) * (w₀ * (∫⁻ x, ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x)).toReal) := by
  unfold modelKernel
  congr 1
  simp_rw [modelIntegrand_const_weight ρ B D γ q δ w₀ a₀ t Q κ r]
  rw [integral_const_mul, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (modelIntegrand_one_nonneg ρ B D γ q δ a₀ t Q κ r))
    (measurable_modelIntegrand measurable_const measurable_const t).aestronglyMeasurable]

/-- **The transverse active-truth face theorem with spectators** (constant units): with `m`
spectator coordinates of positive reduced costs `d_i = r_i + 1 − βκ_i + ηQ_i`,
`t^{γp + βδ − ηγ}/(log t)^k · K(t) → A w₀ Γ(β) (Ba₀)^{-β} (ρ/D)^{qη}/η · vol(F')/|det M| ·
∏ ρ^{d_i}/d_i`. -/
theorem tendsto_modelKernel_activeTruth_spectator {ρ A B D γ p q δ β η w₀ a₀ : ℝ}
    {Q κ r : Fin m ⊕ (Fin k ⊕ Fin 2) → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det ≠ 0)
    (hc₀ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 0 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 0 ≠ 0)
    (hc₁ : fibreCoef (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) 1 ≠ 0 ∨
      fibreA (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ 1 ≠ 0)
    (hrJ : ∀ j, r (Sum.inr j) + 1 = β * κ (Sum.inr j) - η * Q (Sum.inr j))
    (hd : ∀ i, 0 < specd β η Q κ r i) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop
      (𝓝 (A * w₀ * Gamma β * (B * a₀) ^ (-β) * (ρ / D) ^ (q * η) / η *
        (volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ)).toReal /
        |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det| *
        ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i)) := by
  have hlim := tendsto_lintegral_specF hρ hD hq hB ha₀ hβ hη hδ hκ hΔ hc₀ hc₁ hrJ hd
  rw [lintegral_specFlim hρ hD hq hB ha₀ hβ hη hκ hΔ hd] at hlim
  set V := volume (facePolytope (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j)) δ γ) with hV
  have hVne : V ≠ ⊤ := volume_facePolytope_ne_top hΔ (fun j ↦ hκ _) δ γ
  set cJ := B * a₀ * ρ ^ (∑ j, κ (Sum.inr j)) with hcJ
  set EJ := exp (-(η * -(q * log (ρ / D) + (∑ j, Q (Sum.inr j)) * log ρ))) with hEJ
  set S := ρ ^ (∑ j, (r (Sum.inr j) + 1)) *
    |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹ with hS
  have hcJ0 : 0 < cJ := by rw [hcJ]; positivity
  have hK0 : 0 ≤ S * (Gamma β * (cJ ^ (-β) * (EJ / η))) * ∏ i, ρ ^ specd β η Q κ r i /
      specd β η Q κ r i := by
    have := Real.Gamma_pos_of_pos hβ
    have h1 : 0 ≤ S := by rw [hS]; positivity
    have h2 : 0 ≤ cJ ^ (-β) := (Real.rpow_pos_of_pos hcJ0 _).le
    have h3 : 0 ≤ ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i :=
      Finset.prod_nonneg fun i _ ↦ div_nonneg (Real.rpow_nonneg hρ.le _) (hd i).le
    positivity
  have hne : ENNReal.ofReal (S * (Gamma β * (cJ ^ (-β) * (EJ / η))) *
      ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i) * V ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVne
  have hlim2 := ((ENNReal.tendsto_toReal hne).comp hlim).const_mul (A * w₀)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at hlim2
  have hconst := activeTruth_const_eq (q := q) (Q := fun j ↦ Q (Sum.inr j))
    (κ := fun j ↦ κ (Sum.inr j)) (r := fun j ↦ r (Sum.inr j)) hρ hD hB ha₀ hrJ
  beta_reduce at hconst
  rw [← hcJ, ← hEJ] at hconst
  have hval : A * w₀ * (S * (Gamma β * (cJ ^ (-β) * (EJ / η))) *
      ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i) * V.toReal =
      A * w₀ * Gamma β * (B * a₀) ^ (-β) * (ρ / D) ^ (q * η) / η * V.toReal /
        |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det| *
        ∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i := by
    rw [hS]
    linear_combination (A * w₀ * Gamma β / η * (∏ i, ρ ^ specd β η Q κ r i / specd β η Q κ r i) *
      V.toReal * |(transMat (fun j ↦ κ (Sum.inr j)) (fun j ↦ Q (Sum.inr j))).det|⁻¹) * hconst
  rw [← mul_assoc, hval] at hlim2
  refine hlim2.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hL : 0 < log t := Real.log_pos ht
  simp only [Function.comp]
  rw [modelKernel_const_eq_toReal, lintegral_modelIntegrand_spectator]
  have hF : ∀ ξ, specF ρ B D γ q δ β η a₀ Q κ r t ξ =
      ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        ((specBox m ρ).indicator (fun ξ ↦ ENNReal.ofReal (∏ i, ξ i ^ r (Sum.inl i))) ξ *
          ∫⁻ x' : Fin k ⊕ Fin 2 → ℝ, ENNReal.ofReal (modelIntegrand ρ (specB B κ ξ) (specD D q Q ξ)
            γ q δ (fun j ↦ Q (Sum.inr j)) (fun j ↦ κ (Sum.inr j)) (fun j ↦ r (Sum.inr j))
            (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x')) := fun ξ ↦ by
    unfold specF specInner
    ring
  simp_rw [hF]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  have e1 : t ^ (γ * p + (β * δ - η * γ)) = t ^ (γ * p) * t ^ (β * δ - η * γ) :=
    Real.rpow_add ht0 _ _
  have e2 : t ^ (-(γ * p)) = (t ^ (γ * p))⁻¹ := Real.rpow_neg ht0.le _
  rw [e1, e2]
  have hpos : t ^ (γ * p) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  have hLk : log t ^ k ≠ 0 := (pow_pos hL k).ne'
  field_simp

end Laplace.Multi
