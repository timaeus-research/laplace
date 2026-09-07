/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CanonicalCoefficients

/-!
# Regrouping the merged expansion by exponent (grammar §4.2, Taylor tree `d = 2`)

The merged sum of `LogMerge` is indexed by face indices `i < M₁`, `j < M₂`. Here it is regrouped
over the finite pole set `poleSet = uExp(range M₁) ∪ vExp(range M₂)` as

  `mergedSum = ∑_{α ∈ poleSet} N^{−α} (canonA α · log N + canonB α)`   (`mergedSum_eq_canon`)

with the canonical, cutoff-independent coefficients of `CanonicalCoefficients`. The compatibility
inequalities `(M₁−1)/k₁ < M₂/k₂`, `(M₂−1)/k₂ < M₁/k₁` guarantee that a `v`-pole `δ_j` (`j < M₂`)
colliding with some `u`-pole `α_i` has `i < M₁` (and symmetrically), so no canonical coefficient is
supported outside the retained index ranges. Analytic corollaries: `twoD_cutoff_canon`,
`twoD_cutoff_amplitude_canon`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

theorem vExp_injective (h₂ k₂ : ℕ) (hk₂ : 0 < k₂) (j j' : ℕ) (h : vExp h₂ k₂ j = vExp h₂ k₂ j') :
    j = j' := by
  unfold vExp at h
  have hk : (k₂ : ℝ) ≠ 0 := by positivity
  rw [div_left_inj' hk] at h
  push_cast at h
  exact_mod_cast (by linarith : (j : ℝ) = j')

/-- Under the compatibility inequality `(M₁−1)/k₁ < M₂/k₂`, retained `u`-poles lie strictly below
all discarded `v`-poles. -/
theorem uExp_lt_vExp_of (p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (i j : ℕ) (hi : i < M₁) (hj : M₂ ≤ j) :
    uExp h₁ k₁ i < vExp h₂ k₂ j := by
  unfold uExp vExp
  push_cast
  rw [show ((h₁ : ℝ) + i + 1) / k₁ = ((h₁ : ℝ) + 1) / k₁ + i / k₁ by ring,
    show ((h₂ : ℝ) + j + 1) / k₂ = ((h₂ : ℝ) + 1) / k₂ + j / k₂ by ring, hp₁, hp₂]
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hk₂' : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
  have hi' : (i : ℝ) + 1 ≤ M₁ := by exact_mod_cast hi
  have hj' : (M₂ : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : (i : ℝ) / k₁ ≤ ((M₁ : ℝ) - 1) / k₁ := by gcongr; linarith
  have h2 : (M₂ : ℝ) / k₂ ≤ (j : ℝ) / k₂ := by gcongr
  linarith

theorem vExp_lt_uExp_of (p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁) (i j : ℕ) (hj : j < M₂) (hi : M₁ ≤ i) :
    vExp h₂ k₂ j < uExp h₁ k₁ i := by
  unfold uExp vExp
  push_cast
  rw [show ((h₁ : ℝ) + i + 1) / k₁ = ((h₁ : ℝ) + 1) / k₁ + i / k₁ by ring,
    show ((h₂ : ℝ) + j + 1) / k₂ = ((h₂ : ℝ) + 1) / k₂ + j / k₂ by ring, hp₁, hp₂]
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hk₂' : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
  have hj' : (j : ℝ) + 1 ≤ M₂ := by exact_mod_cast hj
  have hi' : (M₁ : ℝ) ≤ i := by exact_mod_cast hi
  have h1 : (j : ℝ) / k₂ ≤ ((M₂ : ℝ) - 1) / k₂ := by gcongr; linarith
  have h2 : (M₁ : ℝ) / k₁ ≤ (i : ℝ) / k₁ := by gcongr
  linarith

/-- A retained `v`-pole not hit by a retained `u`-pole is hit by no `u`-pole at all. -/
theorem not_uPole_of_vExp (p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁) (j : ℕ) (hj : j < M₂)
    (hno : ∀ i ∈ Finset.range M₁, uExp h₁ k₁ i ≠ vExp h₂ k₂ j) :
    ∀ i, uExp h₁ k₁ i ≠ vExp h₂ k₂ j := by
  intro i h
  by_cases hi : i < M₁
  · exact hno i (Finset.mem_range.2 hi) h
  · push Not at hi
    have := vExp_lt_uExp_of p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ i j hj hi
    rw [h] at this
    exact lt_irrefl _ this

theorem not_vPole_of_uExp (p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (i : ℕ) (hi : i < M₁)
    (hno : ∀ j ∈ Finset.range M₂, uExp h₁ k₁ i ≠ vExp h₂ k₂ j) :
    ∀ j, vExp h₂ k₂ j ≠ uExp h₁ k₁ i := by
  intro j h
  by_cases hj : j < M₂
  · exact hno j (Finset.mem_range.2 hj) h.symm
  · push Not at hj
    have := uExp_lt_vExp_of p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i j hi hj
    rw [h] at this
    exact lt_irrefl _ this

/-- The retained `u`-face parameter `γ_i = k₂α_i − h₂ − 1` is below the `v`-truncation `M₂`. -/
theorem uface_gamma_lt_of (p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (i : ℕ) (hi : i < M₁) :
    (k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1 < M₂ := by
  have h := uExp_lt_vExp_of p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i M₂ hi le_rfl
  unfold vExp at h
  push_cast at h
  have hk₂' : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
  rw [lt_div_iff₀ hk₂'] at h
  linarith

theorem vface_gamma_lt_of (p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁) (j : ℕ) (hj : j < M₂) :
    (k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1 < M₁ := by
  have h := vExp_lt_uExp_of p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ M₁ j hj le_rfl
  unfold uExp at h
  push_cast at h
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  rw [lt_div_iff₀ hk₁'] at h
  linarith

/-- The finite pole set of the truncated expansion. -/
noncomputable def poleSet (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) : Finset ℝ :=
  (Finset.range M₁).image (uExp h₁ k₁) ∪ (Finset.range M₂).image (vExp h₂ k₂)

/-- The `u`-face block of the canonical sum. -/
theorem canonU_sum_eq (β b p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁) (a : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (hU : ∀ i, i < M₁ →
      faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (a i) (fun m => c i m)
          (canonicalM ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1))
        = faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (a i) (fun m => c i m) M₂)
    (N : ℝ) :
    ∑ α ∈ poleSet h₁ h₂ k₁ k₂ M₁ M₂, N ^ (-α) * logMoment β α 0 (canonU b h₁ h₂ k₁ k₂ a c α)
      = ∑ i ∈ Finset.range M₁, N ^ (-uExp h₁ k₁ i) * logMoment β (uExp h₁ k₁ i) 0
          (faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (a i) (fun m => c i m) M₂) := by
  unfold poleSet
  refine ((Finset.sum_subset Finset.subset_union_left ?_).symm).trans ?_
  · intro α hα hαu
    rw [Finset.mem_union] at hα
    rcases hα with h | h
    · exact absurd h hαu
    rw [Finset.mem_image] at h
    obtain ⟨j, hj, rfl⟩ := h
    have hno : ∀ i, uExp h₁ k₁ i ≠ vExp h₂ k₂ j :=
      not_uPole_of_vExp p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j (Finset.mem_range.1 hj)
        fun i hi h => hαu (Finset.mem_image.2 ⟨i, hi, h⟩)
    rw [canonU_of_not b h₁ h₂ k₁ k₂ a c _ hno, logMoment_zero_fun, mul_zero]
  · rw [Finset.sum_image fun i _ i' _ h => uExp_injective h₁ k₁ hk₁ i i' h]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [canonU_uExp b h₁ h₂ k₁ k₂ hk₁ a c i, hU i (Finset.mem_range.1 hi)]

/-- The `v`-face block of the canonical sum. -/
theorem canonV_sum_eq (β b p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (hV : ∀ j, j < M₂ →
      faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (bj j) (fun m => c m j)
          (canonicalM ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1))
        = faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (bj j) (fun m => c m j) M₁)
    (N : ℝ) :
    ∑ α ∈ poleSet h₁ h₂ k₁ k₂ M₁ M₂, N ^ (-α) * logMoment β α 0 (canonV b h₁ h₂ k₁ k₂ bj c α)
      = ∑ j ∈ Finset.range M₂, N ^ (-vExp h₂ k₂ j) * logMoment β (vExp h₂ k₂ j) 0
          (faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (bj j) (fun m => c m j) M₁) := by
  unfold poleSet
  refine ((Finset.sum_subset Finset.subset_union_right ?_).symm).trans ?_
  · intro α hα hαv
    rw [Finset.mem_union] at hα
    rcases hα with h | h
    · rw [Finset.mem_image] at h
      obtain ⟨i, hi, rfl⟩ := h
      have hno : ∀ j, vExp h₂ k₂ j ≠ uExp h₁ k₁ i :=
        not_vPole_of_uExp p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i (Finset.mem_range.1 hi)
          fun j hj h => hαv (Finset.mem_image.2 ⟨j, hj, h.symm⟩)
      rw [canonV_of_not b h₁ h₂ k₁ k₂ bj c _ hno, logMoment_zero_fun, mul_zero]
    · exact absurd h hαv
  · rw [Finset.sum_image fun j _ j' _ h => vExp_injective h₂ k₂ hk₂ j j' h]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [canonV_vExp b h₁ h₂ k₁ k₂ hk₂ bj c j, hV j (Finset.mem_range.1 hj)]

/-- The collision block of the canonical sum is the merged log family. -/
theorem canonC_sum_eq (β p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁)
    (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) :
    ∑ α ∈ poleSet h₁ h₂ k₁ k₂ M₁ M₂, transferTerm β α 1 (canonC h₁ h₂ k₁ k₂ c α) N
      = mergedLog β h₁ h₂ k₁ k₂ M₁ M₂ c N := by
  unfold poleSet mergedLog
  refine ((Finset.sum_subset Finset.subset_union_left ?_).symm).trans ?_
  · intro α hα hαu
    rw [Finset.mem_union] at hα
    rcases hα with h | h
    · exact absurd h hαu
    rw [Finset.mem_image] at h
    obtain ⟨j, hj, rfl⟩ := h
    have hno : ∀ i, uExp h₁ k₁ i ≠ vExp h₂ k₂ j :=
      not_uPole_of_vExp p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j (Finset.mem_range.1 hj)
        fun i hi h => hαu (Finset.mem_image.2 ⟨i, hi, h⟩)
    rw [canonC_of_not h₁ h₂ k₁ k₂ c _ hno, transferTerm_zero_fun]
  · rw [Finset.sum_image fun i _ i' _ h => uExp_injective h₁ k₁ hk₁ i i' h]
    refine Finset.sum_congr rfl fun i hi => ?_
    change transferTerm β (uExp h₁ k₁ i) 1 (canonC h₁ h₂ k₁ k₂ c (uExp h₁ k₁ i)) N
      = ∑ j ∈ Finset.range M₂, if uExp h₁ k₁ i = vExp h₂ k₂ j then
          transferTerm β (uExp h₁ k₁ i) 1 (fun s => c i j s / ((k₁ : ℝ) * k₂)) N else 0
    by_cases hex : ∃ j ∈ Finset.range M₂, uExp h₁ k₁ i = vExp h₂ k₂ j
    · obtain ⟨j₀, hj₀, hcol⟩ := hex
      rw [Finset.sum_eq_single j₀
        (fun j _ hne => if_neg fun h => hne (vExp_injective h₂ k₂ hk₂ j j₀ (h.symm.trans hcol)))
        (fun h => absurd hj₀ h), if_pos hcol, canonC_collision h₁ h₂ k₁ k₂ hk₁ hk₂ c i j₀ hcol]
    · push Not at hex
      rw [Finset.sum_eq_zero fun j hj => if_neg (hex j hj),
        canonC_uExp_of_not h₁ h₂ k₁ k₂ c i
          (not_vPole_of_uExp p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i (Finset.mem_range.1 hi)
            hex),
        transferTerm_zero_fun]

/-- **The merged sum regrouped by exponent**: canonical pole terms over `poleSet`. -/
theorem mergedSum_eq_canon (β b p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁)
    (a bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (hU : ∀ i, i < M₁ →
      faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (a i) (fun m => c i m)
          (canonicalM ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1))
        = faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (a i) (fun m => c i m) M₂)
    (hV : ∀ j, j < M₂ →
      faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (bj j) (fun m => c m j)
          (canonicalM ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1))
        = faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (bj j) (fun m => c m j) M₁)
    (N : ℝ) :
    mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N
      = ∑ α ∈ poleSet h₁ h₂ k₁ k₂ M₁ M₂,
          N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ c α * Real.log N + canonB β b h₁ h₂ k₁ k₂ a bj c α) := by
  rw [Finset.sum_congr rfl fun α _ => canon_term_eq β b h₁ h₂ k₁ k₂ a bj c α N,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    canonU_sum_eq β b p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ a c hU N,
    canonV_sum_eq β b p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ bj c hV N,
    canonC_sum_eq β p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ c N]
  rfl

/-- The analytic `d = 2` cutoff theorem in canonical pole form. -/
theorem twoD_cutoff_canon (β b p ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁)
    (c : ℕ × ℕ → ℝ → ℝ) (hcc : ∀ ij, Continuous (c ij)) (H : ℝ → ℝ) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp c b)
        - ∑ α ∈ poleSet h₁ h₂ k₁ k₂ M₁ M₂,
            N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α * Real.log N
              + canonB β b h₁ h₂ k₁ k₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) α))
      =O[atTop] fun N : ℝ =>
        N ^ (-(p + min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have hU : ∀ i, i < M₁ →
      faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (anaFaceU c b i) (fun m => c (i, m))
          (canonicalM ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1))
        = faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (anaFaceU c b i)
            (fun m => c (i, m)) M₂ := fun i hi =>
    (faceFPCoeff_anaFaceU_canonical c b ρ _ H hb hbρ hcc hH hc k₁ i M₂
      (uface_gamma_lt_of p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i hi)).symm
  have hV : ∀ j, j < M₂ →
      faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (anaFaceV c b j) (fun m => c (m, j))
          (canonicalM ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1))
        = faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (anaFaceV c b j)
            (fun m => c (m, j)) M₁ := fun j hj =>
    (faceFPCoeff_anaFaceV_canonical c b ρ _ H hb hbρ hcc hH hc k₂ j M₁
      (vface_gamma_lt_of p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j hj)).symm
  exact (twoD_cutoff_analytic_merged β b p ρ C₀ L h₁ h₂ k₁ k₂ M₁ M₂ D hβ hb hbρ hk₁ hk₂ hp₁ hp₂
    hM₁ hM₂ c hcc H hH hc hC₀ henv).congr_left fun N => by
      rw [mergedSum_eq_canon β b p h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ _ _ _ hU hV N]

/-- **The analytic `d = 2` cutoff theorem for `η e^{βsξ}` in canonical pole form.** -/
theorem twoD_cutoff_amplitude_canon (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁)
    (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hy : WSummable ρ y) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - ∑ α ∈ poleSet h₁ h₂ k₁ k₂ M₁ M₂,
            N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) α * Real.log N
              + canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
                  (fun i j s => ampCoeff β x y (i, j) s) α))
      =O[atTop] fun N : ℝ =>
        N ^ (-(p + min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  exact twoD_cutoff_canon β b p ρ (wnorm ρ y) (x (0, 0) + wnorm ρ (dropConst x)) h₁ h₂ k₁ k₂
    M₁ M₂ 0 hβ hb hbρ hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ (ampCoeff β x y) (ampCoeff_continuous β x y)
    (ampEnv β ρ x y) (ampEnv_continuous β ρ x y)
    (fun ij s => ampCoeff_abs_le β ρ hρ x y hx hy ij s) (wnorm_nonneg ρ hρ.le y)
    (fun s hs => ampEnv_le β ρ hβ x y s hs)

end Laplace.Grammar
