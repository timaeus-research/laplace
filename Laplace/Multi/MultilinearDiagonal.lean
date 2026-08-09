/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.Dilation

/-!
# Symmetric multilinear maps are determined by their diagonals

Stage J3 of the tensor programme, the consult's "genuinely new versus
one dimension" stage: the subset-sum polarization identity
`k! • A(v₁,…,v_k) = ∑_{S ⊆ [k]} (-1)^(k-|S|) • A(∑_{i∈S} vᵢ, …)`
for permutation-symmetric continuous multilinear maps, and its
consequences: a symmetric map with vanishing diagonal is zero, two
symmetric maps with equal diagonals are equal, and the
iterated-derivative wrapper (symmetry supplied by
`ContDiffAt.iteratedFDeriv_comp_perm` at `ω` regularity). Per the
shape consult, polarization is stated abstractly — how symmetry was
obtained is the caller's business.
-/

open Finset
open scoped ContDiff

namespace ContinuousMultilinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Pointwise permutation symmetry of a continuous multilinear map. -/
def IsSymm (A : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F) :
    Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E),
    (A fun i ↦ v (σ i)) = A v

/-- `(-1)^(a-b) = (-1)^a·(-1)^b` for natural subtraction. -/
private theorem neg_one_pow_sub {a b : ℕ} (h : b ≤ a) :
    (-1 : ℝ) ^ (a - b) = (-1) ^ a * (-1) ^ b := by
  have h1 : (-1 : ℝ) ^ (a - b) * (-1) ^ (2 * b) = (-1) ^ (a + b) := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : (-1 : ℝ) ^ (2 * b) = 1 := by
    rw [pow_mul]
    norm_num
  rw [h2, mul_one] at h1
  rw [h1, pow_add]

/-- The alternating powerset sum over `ℝ` (Mathlib's
`Finset.sum_powerset_neg_one_pow_card` is stated over `ℤ`). -/
private theorem sum_powerset_neg_one {ι : Type*} [DecidableEq ι]
    (D : Finset ι) :
    (∑ T ∈ D.powerset, (-1 : ℝ) ^ T.card) = if D = ∅ then 1 else 0 := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a D ha ih =>
      have h2 : (∑ t ∈ D.powerset, (-1 : ℝ) ^ (insert a t).card) =
          ∑ t ∈ D.powerset, (-1) * (-1 : ℝ) ^ t.card := by
        refine Finset.sum_congr rfl fun t ht ↦ ?_
        rw [Finset.mem_powerset] at ht
        rw [Finset.card_insert_of_notMem (fun hat ↦ ha (ht hat)),
          pow_succ]
        ring
      rw [Finset.sum_powerset_insert ha, h2, ← Finset.mul_sum, ih,
        if_neg (Finset.insert_ne_empty a D)]
      by_cases hD : D = ∅ <;> simp [hD]

/-- The alternating sum over supersets of `R` inside a finite type
collapses to the indicator of `R` being everything. -/
theorem sum_neg_one_pow_supersets {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : Finset ι) :
    (∑ S ∈ (Finset.univ : Finset ι).powerset.filter (fun S ↦ R ⊆ S),
      (-1 : ℝ) ^ (Fintype.card ι - S.card)) =
    if R = Finset.univ then 1 else 0 := by
  classical
  have hreindex :
      (∑ S ∈ (Finset.univ : Finset ι).powerset.filter (fun S ↦ R ⊆ S),
        (-1 : ℝ) ^ (Fintype.card ι - S.card)) =
      ∑ T ∈ Rᶜ.powerset, (-1 : ℝ) ^ (Rᶜ.card - T.card) := by
    refine Finset.sum_nbij' (i := fun S ↦ S \ R) (j := fun T ↦ R ∪ T)
      ?_ ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_filter] at hS
      rw [Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_compl]
      exact hx.2
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, Finset.subset_union_left⟩
    · intro S hS
      rw [Finset.mem_filter] at hS
      exact Finset.union_sdiff_of_subset hS.2
    · intro T hT
      rw [Finset.mem_powerset] at hT
      apply Finset.union_sdiff_cancel_left
      rw [Finset.disjoint_left]
      intro a haR haT
      exact (Finset.mem_compl.mp (hT haT)) haR
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      simp only []
      congr 1
      have hsd : (S \ R).card = S.card - R.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS.2]
      have hcompl : Rᶜ.card = Fintype.card ι - R.card :=
        Finset.card_compl R
      have hRS : R.card ≤ S.card := Finset.card_le_card hS.2
      have hSle : S.card ≤ Fintype.card ι := S.card_le_univ
      omega
  rw [hreindex]
  have hfactor : (∑ T ∈ Rᶜ.powerset, (-1 : ℝ) ^ (Rᶜ.card - T.card)) =
      (-1 : ℝ) ^ Rᶜ.card *
        ∑ T ∈ Rᶜ.powerset, (-1 : ℝ) ^ T.card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT ↦ ?_
    rw [Finset.mem_powerset] at hT
    exact neg_one_pow_sub (Finset.card_le_card hT)
  rw [hfactor, sum_powerset_neg_one]
  by_cases hR : R = Finset.univ
  · have hcompl : Rᶜ = (∅ : Finset ι) := by
      rw [hR, Finset.compl_univ]
    rw [if_pos hR, hcompl, if_pos rfl]
    simp
  · have hcompl : Rᶜ ≠ (∅ : Finset ι) := by
      intro h
      apply hR
      have := congrArg (·ᶜ) h
      simpa using this
    rw [if_neg hR, if_neg hcompl, mul_zero]

/-- **The subset-sum polarization identity**: a symmetric continuous
multilinear map is recovered from its diagonal. -/
theorem factorial_smul_eq_sum_diag
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F)
    (hA : A.IsSymm) (v : Fin k → E) :
    (k.factorial : ℝ) • A v =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        ((-1 : ℝ) ^ (k - S.card)) • A (fun _ ↦ ∑ i ∈ S, v i) := by
  classical
  -- Step 1: expand each diagonal term by multilinearity.
  have hexpand : ∀ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      ((-1 : ℝ) ^ (k - S.card)) • A (fun _ ↦ ∑ i ∈ S, v i) =
        ∑ r ∈ Fintype.piFinset (fun _ : Fin k ↦ S),
          ((-1 : ℝ) ^ (k - S.card)) • A (fun i ↦ v (r i)) := by
    intro S _
    rw [← Finset.smul_sum]
    congr 1
    exact A.toMultilinearMap.map_sum_finset
      (fun (_ : Fin k) (j : Fin k) ↦ v j) (fun _ : Fin k ↦ S)
  rw [Finset.sum_congr rfl hexpand]
  -- Step 2: the selector finset is a filter over all endofunctions.
  have hset : ∀ S : Finset (Fin k),
      Fintype.piFinset (fun _ : Fin k ↦ S) =
        (Finset.univ : Finset (Fin k → Fin k)).filter
          (fun r ↦ Finset.image r Finset.univ ⊆ S) := by
    intro S
    ext r
    simp [Fintype.mem_piFinset, Finset.image_subset_iff]
  have hextend : ∀ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      (∑ r ∈ Fintype.piFinset (fun _ : Fin k ↦ S),
        ((-1 : ℝ) ^ (k - S.card)) • A (fun i ↦ v (r i))) =
      ∑ r : Fin k → Fin k,
        (if Finset.image r Finset.univ ⊆ S
          then (-1 : ℝ) ^ (k - S.card) else 0) •
            A (fun i ↦ v (r i)) := by
    intro S _
    rw [hset S, Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    by_cases hr : Finset.image r Finset.univ ⊆ S
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, zero_smul]
  rw [Finset.sum_congr rfl hextend, Finset.sum_comm]
  -- Step 3: collapse the coefficient for each endofunction.
  have hcoeff : ∀ r : Fin k → Fin k,
      (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (if Finset.image r Finset.univ ⊆ S
          then (-1 : ℝ) ^ (k - S.card) else 0) •
            A (fun i ↦ v (r i))) =
      (if Finset.image r Finset.univ = Finset.univ then (1 : ℝ)
        else 0) • A (fun i ↦ v (r i)) := by
    intro r
    rw [← Finset.sum_smul]
    congr 1
    rw [← Finset.sum_filter]
    have := sum_neg_one_pow_supersets (ι := Fin k)
      (Finset.image r Finset.univ)
    rwa [Fintype.card_fin] at this
  rw [Finset.sum_congr rfl fun r _ ↦ hcoeff r]
  -- Step 4: only surjective (hence bijective) endofunctions remain.
  have hsimp : (∑ r : Fin k → Fin k,
      (if Finset.image r Finset.univ = Finset.univ then (1 : ℝ)
        else 0) • A (fun i ↦ v (r i))) =
      ∑ r ∈ (Finset.univ : Finset (Fin k → Fin k)).filter
        (fun r ↦ Finset.image r Finset.univ = Finset.univ),
        A (fun i ↦ v (r i)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    by_cases hr : Finset.image r Finset.univ = Finset.univ
    · rw [if_pos hr, if_pos hr, one_smul]
    · rw [if_neg hr, if_neg hr, zero_smul]
  rw [hsimp]
  -- Step 5: each remaining term equals `A v` by symmetry.
  have hbij : ∀ r : Fin k → Fin k,
      Finset.image r Finset.univ = Finset.univ →
        Function.Bijective r := by
    intro r hr
    have hsurj : Function.Surjective r := by
      intro y
      have hy : y ∈ Finset.image r Finset.univ := by
        rw [hr]
        exact Finset.mem_univ y
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx⟩
    exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have hterm : ∀ r ∈ (Finset.univ : Finset (Fin k → Fin k)).filter
      (fun r ↦ Finset.image r Finset.univ = Finset.univ),
      A (fun i ↦ v (r i)) = A v := by
    intro r hr
    rw [Finset.mem_filter] at hr
    exact hA (Equiv.ofBijective r (hbij r hr.2)) v
  rw [Finset.sum_congr rfl hterm, Finset.sum_const]
  -- Step 6: count the bijections.
  have hcard : ((Finset.univ : Finset (Fin k → Fin k)).filter
      (fun r ↦ Finset.image r Finset.univ = Finset.univ)).card =
      k.factorial := by
    have hpred : ∀ r : Fin k → Fin k,
        (Finset.image r Finset.univ = Finset.univ) ↔
          Function.Bijective r := by
      intro r
      constructor
      · exact hbij r
      · intro hb
        apply Finset.eq_univ_of_forall
        intro y
        obtain ⟨x, hx⟩ := hb.2 y
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩
    rw [Finset.filter_congr fun r _ ↦ hpred r]
    have hsub : Fintype.card
        {r : Fin k → Fin k // Function.Bijective r} =
        ((Finset.univ : Finset (Fin k → Fin k)).filter
          (fun r ↦ Function.Bijective r)).card :=
      Fintype.card_subtype _
    rw [← hsub]
    have hequiv : {r : Fin k → Fin k // Function.Bijective r} ≃
        Equiv.Perm (Fin k) :=
      { toFun := fun r ↦ Equiv.ofBijective r.1 r.2
        invFun := fun σ ↦ ⟨σ, σ.bijective⟩
        left_inv := fun r ↦ by
          ext i
          rfl
        right_inv := fun σ ↦ by
          ext i
          rfl }
    rw [Fintype.card_congr hequiv]
    simp [Fintype.card_perm]
  rw [hcard, Nat.cast_smul_eq_nsmul]

/-- A symmetric map with vanishing diagonal is zero. -/
theorem eq_zero_of_diag_eq_zero
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F)
    (hA : A.IsSymm) (hdiag : ∀ x : E, A (fun _ ↦ x) = 0) :
    A = 0 := by
  ext v
  have hpol := A.factorial_smul_eq_sum_diag hA v
  rw [Finset.sum_eq_zero (fun S _ ↦ by rw [hdiag, smul_zero])] at hpol
  have hk : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero k)
  have hAv : A v = 0 := (smul_eq_zero.mp hpol).resolve_left hk
  rw [hAv, ContinuousMultilinearMap.zero_apply]

/-- Two symmetric maps with equal diagonals are equal. -/
theorem eq_of_diag_eq
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F)
    (hA : A.IsSymm) (hB : B.IsSymm)
    (hdiag : ∀ x : E, A (fun _ ↦ x) = B (fun _ ↦ x)) :
    A = B := by
  ext v
  have hApol := A.factorial_smul_eq_sum_diag hA v
  have hBpol := B.factorial_smul_eq_sum_diag hB v
  have hsum : (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      ((-1 : ℝ) ^ (k - S.card)) • A (fun _ ↦ ∑ i ∈ S, v i)) =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        ((-1 : ℝ) ^ (k - S.card)) • B (fun _ ↦ ∑ i ∈ S, v i) :=
    Finset.sum_congr rfl fun S _ ↦ by rw [hdiag]
  have hk : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero k)
  have hAB : (k.factorial : ℝ) • A v = (k.factorial : ℝ) • B v := by
    rw [hApol, hBpol, hsum]
  exact smul_right_injective F hk hAB

end ContinuousMultilinearMap

namespace Laplace.Multi

variable {d : ℕ}

/-- **The germbij application**: two losses whose `k`-th derivatives
have symmetric tensors and equal diagonals at the origin have equal
`k`-th derivative tensors. -/
theorem iteratedFDeriv_eq_of_diag_eq {k : ℕ}
    {L₁ L₂ : EuclidD d → ℝ}
    (h₁symm : (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (h₂symm : (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdiag : ∀ x : EuclidD d,
      iteratedFDeriv ℝ k L₁ 0 (fun _ ↦ x) =
        iteratedFDeriv ℝ k L₂ 0 (fun _ ↦ x)) :
    iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0 :=
  ContinuousMultilinearMap.eq_of_diag_eq _ _ h₁symm h₂symm hdiag

/-- Convenience wrapper at `ω` regularity: Mathlib's
`ContDiffAt.iteratedFDeriv_comp_perm` supplies the symmetry. -/
theorem iteratedFDeriv_eq_of_diag_eq_of_contDiffAt_omega {k : ℕ}
    {L₁ L₂ : EuclidD d → ℝ}
    (h₁ : ContDiffAt ℝ ω L₁ 0) (h₂ : ContDiffAt ℝ ω L₂ 0)
    (hdiag : ∀ x : EuclidD d,
      iteratedFDeriv ℝ k L₁ 0 (fun _ ↦ x) =
        iteratedFDeriv ℝ k L₂ 0 (fun _ ↦ x)) :
    iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0 := by
  refine iteratedFDeriv_eq_of_diag_eq ?_ ?_ hdiag
  · intro σ v
    exact h₁.iteratedFDeriv_comp_perm v σ
  · intro σ v
    exact h₂.iteratedFDeriv_comp_perm v σ

end Laplace.Multi
