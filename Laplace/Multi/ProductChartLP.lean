/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CertificateLP

/-!
# The LP of a product chart: the optimal face

For a product-like chart (`Q = 0`) with positive `κ`, positive `a = r + 1` and `δ > 0`, the
constrained LP `min a·α` over `α ≥ 0`, `κ·α ≥ δ` is solved in closed form. With
`λ = min_i a_i/κ_i` and the tied set `T = {i | a_i/κ_i = λ}`, the optimal set is
`Opt = {α ≥ 0 | α_N = 0, κ_T·α_T = δ} = conv{(δ/κ_i) e_i : i ∈ T}` (`lpOptimal_product_iff`,
`lpOptimal_iff_exists_weights`), the optimal value is `λδ` (`lpOptimal_value`), and the LP
minimiser is unique exactly when `|T| = 1` (`uniqueLPMin_iff_card_eq_one`). In the index shape of
the partially tied theorem (`Fin (k+1) ⊕ ν`, tied block `inl`, gap on `inr`) the optimal set is the
simplex on the tied block and `|T| − 1 = k` is the logarithmic exponent of the coefficient
(`lpOptimal_partial_iff`, `card_image_inl`): the LP face dimension is the log multiplicity, and a
unique LP vertex (`|T| = 1`) leaves a face density in the untied coordinates, not a point mass
(Astra, round 4, target 2).
-/

open Finset

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Q κ a α : ι → ℝ} {γ δ : ℝ}

/-- An optimal point of the constrained LP `min a·α` over `P_γ`. -/
def LPOptimal (Q κ : ι → ℝ) (γ δ : ℝ) (a α : ι → ℝ) : Prop :=
  ConstrainedFeasible Q κ γ δ α ∧
    ∀ β, ConstrainedFeasible Q κ γ δ β → ∑ i, a i * α i ≤ ∑ i, a i * β i

omit [DecidableEq ι] in
/-- A unique LP minimiser is an optimal point that is the only optimal point. -/
theorem uniqueLPMin_iff_lpOptimal_unique :
    UniqueLPMin Q κ γ δ a α ↔ LPOptimal Q κ γ δ a α ∧ ∀ β, LPOptimal Q κ γ δ a β → β = α := by
  constructor
  · rintro ⟨hfeas, hstrict⟩
    refine ⟨⟨hfeas, fun β hβ ↦ ?_⟩, fun β hβ ↦ ?_⟩
    · by_cases hβα : β = α
      · rw [hβα]
      · exact (hstrict β hβ hβα).le
    · by_contra hne
      exact absurd (hβ.2 α hfeas) (not_le.mpr (hstrict β hβ.1 hne))
  · rintro ⟨⟨hfeas, hopt⟩, huniq⟩
    refine ⟨hfeas, fun β hβ hne ↦ lt_of_le_of_ne (hopt β hβ) fun heq ↦ hne ?_⟩
    exact huniq β ⟨hβ, fun β' hβ' ↦ heq ▸ hopt β' hβ'⟩

omit [DecidableEq ι] in
/-- The weighted bound `λ κ·α ≤ a·α` for nonnegative `α` when `λ κ ≤ a`. -/
theorem lam_mul_sum_le {lam : ℝ} (hlam : ∀ i, lam * κ i ≤ a i) (hα : ∀ i, 0 ≤ α i) :
    lam * ∑ i, κ i * α i ≤ ∑ i, a i * α i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hlam i) (hα i)

omit [DecidableEq ι] in
/-- On the tied set the objective is `λ` times the constraint. -/
theorem sum_mul_eq_lam_mul_of_supported {lam : ℝ} {T : Finset ι} (hT : ∀ i ∈ T, a i = lam * κ i)
    (hα : ∀ i ∉ T, α i = 0) : ∑ i, a i * α i = lam * ∑ i, κ i * α i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ T
  · rw [hT i hi]
    ring
  · rw [hα i hi]
    ring

section Product

variable (hQ : ∀ i, Q i = 0) (hγ : 0 ≤ γ) (hκ : ∀ i, 0 < κ i) (hδ : 0 < δ) {lam : ℝ}
  (hlam : 0 < lam) {T : Finset ι} (hne : T.Nonempty) (hT : ∀ i ∈ T, a i = lam * κ i)
  (hN : ∀ i ∉ T, lam * κ i < a i)
include hQ hγ hκ hδ hlam hne hT hN

omit [DecidableEq ι] in
/-- **The optimal set of a product chart.** With `Q = 0`, `κ > 0`, `δ > 0` and
`λ = min a_i/κ_i` attained exactly on `T`, the optimal points are the nonnegative `α` supported on
`T` with `κ·α = δ`. -/
theorem lpOptimal_product_iff :
    LPOptimal Q κ γ δ a α ↔ (∀ i, 0 ≤ α i) ∧ (∀ i ∉ T, α i = 0) ∧ ∑ i, κ i * α i = δ := by
  classical
  have hlam' : ∀ i, lam * κ i ≤ a i := fun i ↦ by
    by_cases hi : i ∈ T
    · exact (hT i hi).ge
    · exact (hN i hi).le
  have hQsum : ∀ β : ι → ℝ, ∑ i, Q i * β i = 0 := fun β ↦ by simp [hQ]
  constructor
  · rintro ⟨⟨hα0, -, hκα⟩, hopt⟩
    obtain ⟨s, hs⟩ := hne
    have hκs := (hκ s).ne'
    -- the tied vertex at `s` is feasible with value `λδ`
    have hfeas : ConstrainedFeasible Q κ γ δ (Pi.single s (δ / κ s)) := by
      refine ⟨fun i ↦ ?_, by rw [hQsum]; exact hγ, ?_⟩
      · by_cases hi : i = s
        · subst hi
          rw [Pi.single_eq_same]
          exact div_nonneg hδ.le (hκ i).le
        · rw [Pi.single_eq_of_ne hi]
      · rw [sum_mul_pi_single, mul_div_cancel₀ _ hκs]
    have hval : ∑ i, a i * (Pi.single s (δ / κ s) : ι → ℝ) i = lam * δ := by
      rw [sum_mul_pi_single, hT s hs]
      field_simp
    have hle : ∑ i, a i * α i ≤ lam * δ := hval ▸ hopt _ hfeas
    have hge : lam * ∑ i, κ i * α i ≤ ∑ i, a i * α i := lam_mul_sum_le hlam' hα0
    have hδle : lam * δ ≤ lam * ∑ i, κ i * α i := mul_le_mul_of_nonneg_left hκα hlam.le
    have hκeq : ∑ i, κ i * α i = δ :=
      mul_left_cancel₀ hlam.ne' (le_antisymm (by linarith) hδle)
    refine ⟨hα0, fun i hi ↦ ?_, hκeq⟩
    -- the excess `∑ (a_i − λκ_i) α_i` vanishes termwise
    have hsum : ∑ i, (a i - lam * κ i) * α i = 0 := by
      have : ∑ i, (a i - lam * κ i) * α i = ∑ i, a i * α i - lam * ∑ i, κ i * α i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [this, hκeq]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
      mul_nonneg (sub_nonneg.mpr (hlam' i)) (hα0 i)).mp hsum i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h (sub_pos.mpr (hN i hi)).ne'
    · exact h
  · rintro ⟨hα0, hαT, hκα⟩
    refine ⟨⟨hα0, by rw [hQsum]; exact hγ, hκα.ge⟩, fun β hβ ↦ ?_⟩
    rw [sum_mul_eq_lam_mul_of_supported hT hαT, hκα]
    exact (mul_le_mul_of_nonneg_left hβ.2.2 hlam.le).trans (lam_mul_sum_le hlam' hβ.1)

omit [DecidableEq ι] in
/-- The optimal value is `λδ`. -/
theorem lpOptimal_value (h : LPOptimal Q κ γ δ a α) : ∑ i, a i * α i = lam * δ := by
  obtain ⟨-, hαT, hκα⟩ := (lpOptimal_product_iff hQ hγ hκ hδ hlam hne hT hN).mp h
  rw [sum_mul_eq_lam_mul_of_supported hT hαT, hκα]

/-- Every tied vertex `(δ/κ_s) e_s`, `s ∈ T`, is optimal. -/
theorem lpOptimal_single {s : ι} (hs : s ∈ T) :
    LPOptimal Q κ γ δ a (Pi.single s (δ / κ s)) := by
  rw [lpOptimal_product_iff hQ hγ hκ hδ hlam hne hT hN]
  refine ⟨fun i ↦ ?_, fun i hi ↦ Pi.single_eq_of_ne (fun h ↦ hi (by rw [h]; exact hs)) _, ?_⟩
  · by_cases hi : i = s
    · rw [hi, Pi.single_eq_same]
      exact div_nonneg hδ.le (hκ s).le
    · rw [Pi.single_eq_of_ne hi]
  · rw [sum_mul_pi_single, mul_div_cancel₀ _ (hκ s).ne']

omit [DecidableEq ι] in
/-- **The optimal set is the simplex `conv{(δ/κ_i) e_i : i ∈ T}`**: the optimal points are exactly
the barycentric combinations `α_i = (δ/κ_i) w_i` with weights `w ≥ 0` supported on `T` summing to
one. -/
theorem lpOptimal_iff_exists_weights :
    LPOptimal Q κ γ δ a α ↔ ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i ∉ T, w i = 0) ∧ ∑ i, w i = 1 ∧
      ∀ i, α i = δ / κ i * w i := by
  rw [lpOptimal_product_iff hQ hγ hκ hδ hlam hne hT hN]
  constructor
  · rintro ⟨hα0, hαT, hκα⟩
    refine ⟨fun i ↦ κ i * α i / δ, ?_, ?_, ?_, ?_⟩
    · intro i
      exact div_nonneg (mul_nonneg (hκ i).le (hα0 i)) hδ.le
    · intro i hi
      change κ i * α i / δ = 0
      rw [hαT i hi, mul_zero, zero_div]
    · change ∑ i, κ i * α i / δ = 1
      rw [← Finset.sum_div, hκα, div_self hδ.ne']
    · intro i
      change α i = δ / κ i * (κ i * α i / δ)
      have := (hκ i).ne'
      field_simp
  · rintro ⟨w, hw0, hwT, hw1, hαw⟩
    refine ⟨fun i ↦ by rw [hαw]; exact mul_nonneg (div_nonneg hδ.le (hκ i).le) (hw0 i),
      fun i hi ↦ by rw [hαw, hwT i hi, mul_zero], ?_⟩
    calc ∑ i, κ i * α i = ∑ i, δ * w i := Finset.sum_congr rfl fun i _ ↦ by
          rw [hαw, ← mul_assoc, mul_div_cancel₀ _ (hκ i).ne']
      _ = δ := by rw [← Finset.mul_sum, hw1, mul_one]

omit [Fintype ι] hQ hγ hlam hne hT hN in
/-- Two distinct tied vertices differ. -/
theorem single_ne_single {s s' : ι} (hss' : s ≠ s') :
    (Pi.single s (δ / κ s) : ι → ℝ) ≠ Pi.single s' (δ / κ s') := fun h ↦ by
  have := congrFun h s
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hss'] at this
  exact (div_pos hδ (hκ s)).ne' this

/-- **Uniqueness of the LP minimiser is `|T| = 1`.** The LP minimiser is unique exactly when a
single coordinate is tied, and then it is the tied vertex. -/
theorem uniqueLPMin_iff_card_eq_one :
    UniqueLPMin Q κ γ δ a α ↔ T.card = 1 ∧ ∀ i, α i = if i ∈ T then δ / κ i else 0 := by
  rw [uniqueLPMin_iff_lpOptimal_unique]
  constructor
  · rintro ⟨hopt, huniq⟩
    have hcard : T.card = 1 := by
      by_contra hc
      have h1 : 1 < T.card := lt_of_le_of_ne hne.card_pos (Ne.symm hc)
      obtain ⟨s, hs, s', hs', hss'⟩ := Finset.one_lt_card.mp h1
      have e1 := huniq _ (lpOptimal_single hQ hγ hκ hδ hlam hne hT hN hs)
      have e2 := huniq _ (lpOptimal_single hQ hγ hκ hδ hlam hne hT hN hs')
      exact single_ne_single hκ hδ hss' (e1.trans e2.symm)
    obtain ⟨s, hTs⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨hα0, hαT, hκα⟩ := (lpOptimal_product_iff hQ hγ hκ hδ hlam hne hT hN).mp hopt
    refine ⟨hcard, fun i ↦ ?_⟩
    by_cases hi : i ∈ T
    · rw [if_pos hi]
      rw [hTs, Finset.mem_singleton] at hi
      subst hi
      have : ∑ j, κ j * α j = κ i * α i := by
        rw [Finset.sum_eq_single i (fun j _ hj ↦ by
          rw [hαT j (by rw [hTs, Finset.mem_singleton]; exact hj), mul_zero])
          (fun h ↦ absurd (Finset.mem_univ i) h)]
      rw [this] at hκα
      rw [eq_div_iff (hκ i).ne', mul_comm]
      exact hκα
    · rw [if_neg hi]
      exact hαT i hi
  · rintro ⟨hcard, hα⟩
    obtain ⟨s, hTs⟩ := Finset.card_eq_one.mp hcard
    have hmem : ∀ i, i ∈ T ↔ i = s := fun i ↦ by rw [hTs, Finset.mem_singleton]
    have hopt : ∀ β, LPOptimal Q κ γ δ a β ↔ ∀ i, β i = if i ∈ T then δ / κ i else 0 := by
      intro β
      rw [lpOptimal_product_iff hQ hγ hκ hδ hlam hne hT hN]
      constructor
      · rintro ⟨-, hβT, hκβ⟩ i
        by_cases hi : i ∈ T
        · rw [if_pos hi]
          have hi' := (hmem i).mp hi
          subst hi'
          have : ∑ j, κ j * β j = κ i * β i := by
            rw [Finset.sum_eq_single i (fun j _ hj ↦ by
              rw [hβT j (fun h ↦ hj ((hmem j).mp h)), mul_zero])
              (fun h ↦ absurd (Finset.mem_univ i) h)]
          rw [this] at hκβ
          rw [eq_div_iff (hκ i).ne', mul_comm]
          exact hκβ
        · rw [if_neg hi]
          exact hβT i hi
      · intro hβ
        refine ⟨fun i ↦ ?_, fun i hi ↦ by rw [hβ i, if_neg hi], ?_⟩
        · rw [hβ i]
          split_ifs
          · exact div_nonneg hδ.le (hκ i).le
          · exact le_rfl
        · have hβs : ∀ i, β i = (Pi.single s (δ / κ s) : ι → ℝ) i := fun i ↦ by
            rw [hβ i]
            by_cases hi : i = s
            · subst hi
              rw [if_pos ((hmem i).mpr rfl), Pi.single_eq_same]
            · rw [if_neg (fun h ↦ hi ((hmem i).mp h)), Pi.single_eq_of_ne hi]
          simp only [hβs]
          rw [sum_mul_pi_single, mul_div_cancel₀ _ (hκ s).ne']
    refine ⟨(hopt α).mpr hα, fun β hβ ↦ funext fun i ↦ ?_⟩
    rw [(hopt β).mp hβ i, hα i]

end Product

/-! ### The index shape of the partially tied theorem -/

section Partial

variable {k : ℕ} {ν : Type*} [Fintype ν] [DecidableEq ν]

omit [Fintype ν] in
/-- The tied block has `k + 1` coordinates: the LP face dimension `|T| − 1` is the logarithmic
exponent `k` of the partially tied coefficient. -/
theorem card_image_inl :
    (Finset.univ.image (Sum.inl : Fin (k + 1) → Fin (k + 1) ⊕ ν)).card = k + 1 := by
  rw [Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ, Fintype.card_fin]

omit [DecidableEq ν] in
/-- **The optimal set of a partially tied chart** (hypotheses of `tendsto_modelKernel_partial`,
`a = r + 1`): the nonnegative `α` vanishing on the untied block `inr` with `κ_T·α_T = δ`, the
simplex on the tied block. -/
theorem lpOptimal_partial_iff {κ r α : Fin (k + 1) ⊕ ν → ℝ} {γ δ : ℝ} (hγ : 0 ≤ γ)
    (hκ : ∀ i, 0 < κ i) (hδ : 0 < δ) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ i, (r (Sum.inl i) + 1) / κ (Sum.inl i) = lam)
    (hgap : ∀ j, lam * κ (Sum.inr j) < r (Sum.inr j) + 1) :
    LPOptimal 0 κ γ δ (fun i ↦ r i + 1) α ↔
      (∀ i, 0 ≤ α i) ∧ (∀ j, α (Sum.inr j) = 0) ∧ ∑ i, κ i * α i = δ := by
  classical
  have hmem : ∀ i : Fin (k + 1) ⊕ ν,
      i ∈ Finset.univ.image (Sum.inl : Fin (k + 1) → Fin (k + 1) ⊕ ν) ↔ ∃ i', Sum.inl i' = i :=
    fun i ↦ by simp
  rw [lpOptimal_product_iff (Q := 0) (fun _ ↦ rfl) hγ hκ hδ hlam
    ⟨Sum.inl 0, (hmem _).mpr ⟨0, rfl⟩⟩ (T := Finset.univ.image Sum.inl)
    (fun i hi ↦ by
      obtain ⟨i', rfl⟩ := (hmem i).mp hi
      have h := htied i'
      rw [div_eq_iff (hκ _).ne'] at h
      exact h)
    (fun i hi ↦ by
      rcases i with i' | j
      · exact absurd ((hmem _).mpr ⟨i', rfl⟩) hi
      · exact hgap j)]
  refine and_congr_right fun _ ↦ and_congr_left fun _ ↦ ?_
  constructor
  · intro h j
    exact h (Sum.inr j) fun hj ↦ by
      obtain ⟨i', hi'⟩ := (hmem _).mp hj
      exact Sum.inl_ne_inr hi'
  · rintro h (i' | j) hi
    · exact absurd ((hmem _).mpr ⟨i', rfl⟩) hi
    · exact h j

end Partial

end Laplace.Multi
