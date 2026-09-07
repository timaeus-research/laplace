/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoeffStability
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Coefficient families and their box truncations (Stage 4c)

Unit 243 (Taylor-tree programme, Stage 4; Astra #28 §2.1–2.2). Analytic data enter through their
Taylor coefficients: a **coefficient family** `c : (Fin d → ℕ) → ℝ` with `∑_γ |c_γ| < ∞`
(`AbsSummable`), of **mass** `∑_γ |c_γ|` and **evaluation** `∑_γ c_γ u^γ`, absolutely convergent on
the
closed unit cube with `|eval c u| ≤ mass c`. The **box truncation** at level `m` is the finite
monomial list of the coefficients with all `γᵢ ≤ m` (`truncList`), a genuine `MonoRep` to which all
of
Stage 3 applies; it keeps the constant term (`eval_truncList_zero`), has list mass at most `mass c`,
and successive truncations differ by an appended list (`truncList_perm`) whose mass is at most the
**tail mass** `∑_{γ ∉ box m} |c_γ|`, which tends to `0` (`tailMass_tendsto_zero`); the truncations
converge to the family uniformly on the cube (`abs_evalF_sub_truncList_le`). No `sorry` and no
additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology
open scoped List

namespace Laplace.Grammar

open MonoRep

/-- Coefficient families: real coefficients indexed by multi-indices. -/
abbrev CoeffFamily (d : ℕ) := (Fin d → ℕ) → ℝ

namespace CoeffFamily

variable {d : ℕ}

/-- Absolute summability `∑_γ |c_γ| < ∞`. -/
def AbsSummable (c : CoeffFamily d) : Prop := Summable fun γ => |c γ|

/-- The mass `∑_γ |c_γ|`. -/
noncomputable def mass (c : CoeffFamily d) : ℝ := ∑' γ, |c γ|

/-- Evaluation `∑_γ c_γ u^γ`. -/
noncomputable def evalF (c : CoeffFamily d) (u : Fin d → ℝ) : ℝ := ∑' γ, c γ * mono γ u

theorem mass_nonneg (c : CoeffFamily d) : 0 ≤ mass c := tsum_nonneg fun _ => abs_nonneg _

theorem abs_term_le {c : CoeffFamily d} {u : Fin d → ℝ} (hu : u ∈ closedCube d) (γ : Fin d → ℕ) :
    |c γ * mono γ u| ≤ |c γ| := by
  rw [abs_mul, abs_of_nonneg (mono_nonneg hu)]
  exact mul_le_of_le_one_right (abs_nonneg _) (mono_le_one hu)

theorem summable_term {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) : Summable fun γ => c γ * mono γ u :=
  Summable.of_norm_bounded hc fun γ => by rw [Real.norm_eq_abs]; exact abs_term_le hu γ

theorem summable_abs_term {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) : Summable fun γ => |c γ * mono γ u| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_term_le hu) hc

/-- `|eval c u| ≤ mass c` on the closed cube. -/
theorem abs_evalF_le {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) : |evalF c u| ≤ mass c := by
  unfold evalF mass
  have h1 := norm_tsum_le_tsum_norm (f := fun γ => c γ * mono γ u)
    (by simpa [Real.norm_eq_abs] using summable_abs_term hc hu)
  simp only [Real.norm_eq_abs] at h1
  exact h1.trans (Summable.tsum_le_tsum (abs_term_le hu) (summable_abs_term hc hu) hc)

/-! ### Box truncations -/

/-- The box `{γ | ∀ i, γᵢ ≤ m}` of multi-indices. -/
def boxSet (d m : ℕ) : Finset (Fin d → ℕ) := Fintype.piFinset fun _ => Finset.range (m + 1)

theorem mem_boxSet {m : ℕ} {γ : Fin d → ℕ} : γ ∈ boxSet d m ↔ ∀ i, γ i ≤ m := by
  unfold boxSet
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

theorem boxSet_mono {m m' : ℕ} (h : m ≤ m') : boxSet d m ⊆ boxSet d m' := fun _ hγ =>
  mem_boxSet.2 fun i => (mem_boxSet.1 hγ i).trans h

theorem zero_mem_boxSet (m : ℕ) : (0 : Fin d → ℕ) ∈ boxSet d m :=
  mem_boxSet.2 fun _ => Nat.zero_le _

/-- The box truncation as a monomial list. -/
noncomputable def truncList (c : CoeffFamily d) (m : ℕ) : MonoRep d :=
  (boxSet d m).toList.map fun γ => (γ, c γ)

theorem sum_map_toList {α : Type*} (s : Finset α) (f : α → ℝ) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList s, Multiset.map_coe, Multiset.sum_coe]

theorem eval_truncList (c : CoeffFamily d) (m : ℕ) (u : Fin d → ℝ) :
    eval (truncList c m) u = ∑ γ ∈ boxSet d m, c γ * mono γ u := by
  unfold eval truncList
  rw [List.map_map]
  exact sum_map_toList _ _

theorem l1_truncList (c : CoeffFamily d) (m : ℕ) :
    l1 (truncList c m) = ∑ γ ∈ boxSet d m, |c γ| := by
  unfold l1 truncList
  rw [List.map_map]
  exact sum_map_toList _ _

theorem l1_truncList_le_mass {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    l1 (truncList c m) ≤ mass c := by
  rw [l1_truncList]
  exact hc.sum_le_tsum _ fun _ _ => abs_nonneg _

/-- The truncation keeps the constant term: `eval (truncList c m) 0 = c 0`. -/
theorem eval_truncList_zero (c : CoeffFamily d) (m : ℕ) : eval (truncList c m) 0 = c 0 := by
  rw [eval_truncList]
  simp_rw [mono_zero_apply]
  rw [Finset.sum_eq_single (0 : Fin d → ℕ)]
  · simp
  · intro γ _ hγ; simp [hγ]
  · intro h; exact absurd (zero_mem_boxSet m) h

/-! ### Tail mass -/

/-- The tail mass `∑_{γ ∉ box m} |c_γ|` (as a sum with an indicator). -/
noncomputable def tailMass (c : CoeffFamily d) (m : ℕ) : ℝ :=
  ∑' γ, if γ ∈ boxSet d m then 0 else |c γ|

theorem tail_term_nonneg (c : CoeffFamily d) (m : ℕ) (γ : Fin d → ℕ) :
    0 ≤ if γ ∈ boxSet d m then 0 else |c γ| := by
  split_ifs <;> simp

theorem tail_term_le (c : CoeffFamily d) (m : ℕ) (γ : Fin d → ℕ) :
    (if γ ∈ boxSet d m then 0 else |c γ|) ≤ |c γ| := by
  split_ifs <;> simp

theorem summable_tail_term {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    Summable fun γ => if γ ∈ boxSet d m then 0 else |c γ| :=
  Summable.of_nonneg_of_le (tail_term_nonneg c m) (tail_term_le c m) hc

theorem tailMass_nonneg (c : CoeffFamily d) (m : ℕ) : 0 ≤ tailMass c m :=
  tsum_nonneg (tail_term_nonneg c m)

/-- Every multi-index is eventually in the box. -/
theorem eventually_mem_boxSet (γ : Fin d → ℕ) : ∀ᶠ m in atTop, γ ∈ boxSet d m := by
  refine eventually_atTop.2 ⟨∑ i, γ i, fun m hm => mem_boxSet.2 fun i => ?_⟩
  exact (Finset.single_le_sum (fun i _ => Nat.zero_le (γ i)) (Finset.mem_univ i)).trans hm

/-- **The tail mass tends to zero.** -/
theorem tailMass_tendsto_zero {c : CoeffFamily d} (hc : AbsSummable c) :
    Tendsto (tailMass c) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun m γ => if γ ∈ boxSet d m then (0 : ℝ) else |c γ|) (g := fun _ => 0) hc
    (fun γ => ?_) (Eventually.of_forall fun m γ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tail_term_nonneg c m γ)]; exact tail_term_le c m γ)
  · have h0 : ∑' _ : Fin d → ℕ, (0 : ℝ) = 0 := tsum_zero
    rw [h0] at h
    exact h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_boxSet γ] with m hm
    simp [hm]

/-- Finite sums outside the box are bounded by the tail mass. -/
theorem sum_abs_le_tailMass {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ)
    (S : Finset (Fin d → ℕ)) (hS : ∀ γ ∈ S, γ ∉ boxSet d m) :
    ∑ γ ∈ S, |c γ| ≤ tailMass c m := by
  have : ∑ γ ∈ S, |c γ| = ∑ γ ∈ S, if γ ∈ boxSet d m then 0 else |c γ| :=
    Finset.sum_congr rfl fun γ hγ => by rw [if_neg (hS γ hγ)]
  rw [this]
  exact (summable_tail_term hc m).sum_le_tsum _ fun γ _ => tail_term_nonneg c m γ

/-! ### Successive truncations differ by an appended list -/

/-- The new monomials between levels `m ≤ m'`. -/
noncomputable def restList (c : CoeffFamily d) (m m' : ℕ) : MonoRep d :=
  ((boxSet d m').filter fun γ => γ ∉ boxSet d m).toList.map fun γ => (γ, c γ)

theorem l1_restList (c : CoeffFamily d) (m m' : ℕ) :
    l1 (restList c m m') = ∑ γ ∈ (boxSet d m').filter (fun γ => γ ∉ boxSet d m), |c γ| := by
  unfold l1 restList
  rw [List.map_map]
  exact sum_map_toList _ _

theorem l1_restList_le_tailMass {c : CoeffFamily d} (hc : AbsSummable c) (m m' : ℕ) :
    l1 (restList c m m') ≤ tailMass c m := by
  rw [l1_restList]
  exact sum_abs_le_tailMass hc m _ fun γ hγ => (Finset.mem_filter.1 hγ).2

/-- `truncList c m' ~ truncList c m ++ restList c m m'` for `m ≤ m'`. -/
theorem truncList_perm (c : CoeffFamily d) {m m' : ℕ} (h : m ≤ m') :
    (truncList c m').Perm (truncList c m ++ restList c m m') := by
  unfold truncList restList
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  refine List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) ?_ ?_
  · refine (Finset.nodup_toList _).append (Finset.nodup_toList _) ?_
    intro γ h1 h2
    rw [Finset.mem_toList] at h1 h2
    exact (Finset.mem_filter.1 h2).2 h1
  · ext γ
    simp only [List.mem_toFinset, List.mem_append, Finset.mem_toList, Finset.mem_filter]
    constructor
    · intro hγ
      by_cases hm : γ ∈ boxSet d m
      · exact Or.inl hm
      · exact Or.inr ⟨hγ, hm⟩
    · rintro (hγ | ⟨hγ, -⟩)
      · exact boxSet_mono h hγ
      · exact hγ

/-- The fluctuation parts of successive truncations differ by an appended list of mass at most
the tail mass. -/
theorem fluct_truncList_perm (c : CoeffFamily d) {m m' : ℕ} (h : m ≤ m') :
    (fluct (truncList c m')).Perm (fluct (truncList c m) ++ fluct (restList c m m')) := by
  unfold fluct
  rw [← List.filter_append]
  exact (truncList_perm c h).filter _

/-! ### Uniform convergence of the truncations on the cube -/

/-- `|eval c u − eval (truncList c m) u| ≤ tailMass c m` on the closed cube. -/
theorem abs_evalF_sub_truncList_le {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    |evalF c u - eval (truncList c m) u| ≤ tailMass c m := by
  rw [eval_truncList]
  have hs := summable_term hc hu
  have hsplit := hs.sum_add_tsum_compl (s := boxSet d m)
  unfold evalF
  rw [← hsplit, add_sub_cancel_left]
  -- the complement sum is bounded by the tail mass
  have hind : ∀ γ : Fin d → ℕ, ‖(if γ ∈ boxSet d m then (0 : ℝ) else c γ * mono γ u)‖ ≤
      if γ ∈ boxSet d m then 0 else |c γ| := fun γ => by
    split_ifs
    · simp
    · rw [Real.norm_eq_abs]; exact abs_term_le hu γ
  have hcompl : ∑' γ : ((boxSet d m : Set (Fin d → ℕ))ᶜ : Set _), c γ * mono (γ : Fin d → ℕ) u =
      ∑' γ, if γ ∈ boxSet d m then (0 : ℝ) else c γ * mono γ u := by
    refine (tsum_subtype ((boxSet d m : Set (Fin d → ℕ))ᶜ) fun γ => c γ * mono γ u).trans ?_
    refine tsum_congr fun γ => ?_
    simp only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe]
    split_ifs <;> simp_all
  rw [hcompl, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hind (summable_tail_term hc m)
  · exact Summable.tsum_le_tsum hind
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hind (summable_tail_term hc m))
      (summable_tail_term hc m)

end CoeffFamily

end Laplace.Grammar
