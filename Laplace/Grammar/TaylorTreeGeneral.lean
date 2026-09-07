/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDCutoffGeneralAnalytic

/-!
# The Taylor tree for `d = 2` with arbitrary starting exponents (grammar §4.2, `thm:TaylorTree`)

Regrouping and the "for every `T`" statement of `TaylorTreeRegroup`/`TaylorTreeEqual`, with the
two starting exponents `p₁ = (h₁+1)/k₁`, `p₂ = (h₂+1)/k₂` independent. The compatibility
consequences (retained poles of one axis lie strictly below discarded poles of the other) now come
from the shifted inequalities; the cutoffs are `q = max(2T, p₁, p₂) + 1`,
`M_ℓ = ⌈k_ℓ (q − p_ℓ)⌉₊` (Astra #9). Main result `twoD_taylor_tree_general`:

  `∀ T, Z(N) − ∑_{α ∈ Λ(h,k), α < 2T} N^{−α} (A_α log N + B_α) = O(N^{−2T} (1 + log N))`

for the chart amplitude `η e^{βsξ}` of analytic `ξ, η`, with the canonical coefficients
`A_α = canonA`, `B_α = canonB` unchanged and independent of `T`. The leading candidate exponent is
`min(p₁, p₂)`; a leading logarithm requires `p₁ = p₂`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- Retained `u`-poles lie strictly below discarded `v`-poles (shifted compatibility). -/
theorem uExp_lt_vExp_general (p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂) (i j : ℕ) (hi : i < M₁) (hj : M₂ ≤ j) :
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

theorem vExp_lt_uExp_general (p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁) (i j : ℕ) (hj : j < M₂) (hi : M₁ ≤ i) :
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

theorem not_uPole_of_vExp_general (p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁) (j : ℕ) (hj : j < M₂)
    (hno : ∀ i ∈ Finset.range M₁, uExp h₁ k₁ i ≠ vExp h₂ k₂ j) :
    ∀ i, uExp h₁ k₁ i ≠ vExp h₂ k₂ j := by
  intro i h
  by_cases hi : i < M₁
  · exact hno i (Finset.mem_range.2 hi) h
  · push Not at hi
    have := vExp_lt_uExp_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ i j hj hi
    rw [h] at this
    exact lt_irrefl _ this

theorem not_vPole_of_uExp_general (p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂) (i : ℕ) (hi : i < M₁)
    (hno : ∀ j ∈ Finset.range M₂, uExp h₁ k₁ i ≠ vExp h₂ k₂ j) :
    ∀ j, vExp h₂ k₂ j ≠ uExp h₁ k₁ i := by
  intro j h
  by_cases hj : j < M₂
  · exact hno j (Finset.mem_range.2 hj) h.symm
  · push Not at hj
    have := uExp_lt_vExp_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i j hi hj
    rw [h] at this
    exact lt_irrefl _ this

theorem uface_gamma_lt_general_uExp (p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂) (i : ℕ) (hi : i < M₁) :
    (k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1 < M₂ :=
  uface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i hi

theorem vface_gamma_lt_general_vExp (p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁) (j : ℕ) (hj : j < M₂) :
    (k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1 < M₁ :=
  vface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j hj

/-- The `u`-face block of the canonical sum (general starts). -/
theorem canonU_sum_eq_general (β b p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁) (a : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ)
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
      not_uPole_of_vExp_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j
        (Finset.mem_range.1 hj) fun i hi h => hαu (Finset.mem_image.2 ⟨i, hi, h⟩)
    rw [canonU_of_not b h₁ h₂ k₁ k₂ a c _ hno, logMoment_zero_fun, mul_zero]
  · rw [Finset.sum_image fun i _ i' _ h => uExp_injective h₁ k₁ hk₁ i i' h]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [canonU_uExp b h₁ h₂ k₁ k₂ hk₁ a c i, hU i (Finset.mem_range.1 hi)]

/-- The `v`-face block of the canonical sum (general starts). -/
theorem canonV_sum_eq_general (β b p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂) (bj : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ)
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
        not_vPole_of_uExp_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i
          (Finset.mem_range.1 hi) fun j hj h => hαv (Finset.mem_image.2 ⟨j, hj, h.symm⟩)
      rw [canonV_of_not b h₁ h₂ k₁ k₂ bj c _ hno, logMoment_zero_fun, mul_zero]
    · exact absurd h hαv
  · rw [Finset.sum_image fun j _ j' _ h => vExp_injective h₂ k₂ hk₂ j j' h]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [canonV_vExp b h₁ h₂ k₁ k₂ hk₂ bj c j, hV j (Finset.mem_range.1 hj)]

/-- The collision block of the canonical sum (general starts). -/
theorem canonC_sum_eq_general (β p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁)
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
      not_uPole_of_vExp_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j
        (Finset.mem_range.1 hj) fun i hi h => hαu (Finset.mem_image.2 ⟨i, hi, h⟩)
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
          (not_vPole_of_uExp_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i
            (Finset.mem_range.1 hi) hex),
        transferTerm_zero_fun]

/-- **The merged sum regrouped by exponent (general starts).** -/
theorem mergedSum_eq_canon_general (β b p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁)
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
    canonU_sum_eq_general β b p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ a c hU N,
    canonV_sum_eq_general β b p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ bj c hV N,
    canonC_sum_eq_general β p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ c N]
  rfl

/-- The analytic cutoff theorem in canonical pole form (general starts). -/
theorem twoD_cutoff_general_canon (β b p₁ p₂ ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁)
    (c : ℕ × ℕ → ℝ → ℝ) (hcc : ∀ ij, Continuous (c ij)) (H : ℝ → ℝ) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp c b)
        - ∑ α ∈ poleSet h₁ h₂ k₁ k₂ M₁ M₂,
            N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α * Real.log N
              + canonB β b h₁ h₂ k₁ k₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) α))
      =O[atTop] fun N : ℝ =>
        N ^ (-(min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have hU : ∀ i, i < M₁ →
      faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (anaFaceU c b i) (fun m => c (i, m))
          (canonicalM ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1))
        = faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (anaFaceU c b i)
            (fun m => c (i, m)) M₂ := fun i hi =>
    (faceFPCoeff_anaFaceU_canonical c b ρ _ H hb hbρ hcc hH hc k₁ i M₂
      (uface_gamma_lt_general_uExp p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i hi)).symm
  have hV : ∀ j, j < M₂ →
      faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (anaFaceV c b j) (fun m => c (m, j))
          (canonicalM ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1))
        = faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (anaFaceV c b j)
            (fun m => c (m, j)) M₁ := fun j hj =>
    (faceFPCoeff_anaFaceV_canonical c b ρ _ H hb hbρ hcc hH hc k₂ j M₁
      (vface_gamma_lt_general_vExp p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j hj)).symm
  exact (twoD_cutoff_general_analytic β b p₁ p₂ ρ C₀ L h₁ h₂ k₁ k₂ M₁ M₂ D hβ hb hbρ hk₁ hk₂ hp₁
    hp₂ hM₁ hM₂ c hcc H hH hc hC₀ henv).congr_left fun N => by
      rw [mergedSum_eq_canon_general β b p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ _ _ _
        hU hV N]

/-- The analytic cutoff theorem for `η e^{βsξ}` in canonical pole form (general starts). -/
theorem twoD_cutoff_general_amplitude_canon (β b p₁ p₂ ρ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ)
    (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁)
    (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hy : WSummable ρ y) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - ∑ α ∈ poleSet h₁ h₂ k₁ k₂ M₁ M₂,
            N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) α * Real.log N
              + canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
                  (fun i j s => ampCoeff β x y (i, j) s) α))
      =O[atTop] fun N : ℝ =>
        N ^ (-(min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  exact twoD_cutoff_general_canon β b p₁ p₂ ρ (wnorm ρ y) (x (0, 0) + wnorm ρ (dropConst x))
    h₁ h₂ k₁ k₂ M₁ M₂ 0 hβ hb hbρ hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ (ampCoeff β x y)
    (ampCoeff_continuous β x y) (ampEnv β ρ x y) (ampEnv_continuous β ρ x y)
    (fun ij s => ampCoeff_abs_le β ρ hρ x y hx hy ij s) (wnorm_nonneg ρ hρ.le y)
    (fun s hs => ampEnv_le β ρ hβ x y s hs)

/-- The auxiliary target `q = max(2T, p₁, p₂) + 1`. -/
noncomputable def cutoffQ (p₁ p₂ T : ℝ) : ℝ := max (2 * T) (max p₁ p₂) + 1

/-- The truncation order `M = ⌈k (q − p)⌉₊`. -/
noncomputable def cutoffMg (k : ℕ) (p q : ℝ) : ℕ := ⌈(k : ℝ) * (q - p)⌉₊

theorem cutoffQ_ge₁ (p₁ p₂ T : ℝ) : p₁ + 1 ≤ cutoffQ p₁ p₂ T := by
  unfold cutoffQ; linarith [le_max_right (2 * T) (max p₁ p₂), le_max_left p₁ p₂]

theorem cutoffQ_ge₂ (p₁ p₂ T : ℝ) : p₂ + 1 ≤ cutoffQ p₁ p₂ T := by
  unfold cutoffQ; linarith [le_max_right (2 * T) (max p₁ p₂), le_max_right p₁ p₂]

theorem two_mul_lt_cutoffQ (p₁ p₂ T : ℝ) : 2 * T < cutoffQ p₁ p₂ T := by
  unfold cutoffQ; linarith [le_max_left (2 * T) (max p₁ p₂)]

/-- `p + (M − 1)/k < q ≤ p + M/k` for `M = ⌈k(q − p)⌉₊`, `q ≥ p + 1`. -/
theorem cutoffMg_bounds (k : ℕ) (hk : 0 < k) (p q : ℝ) (hq : p + 1 ≤ q) :
    p + ((cutoffMg k p q : ℝ) - 1) / k < q ∧ q ≤ p + (cutoffMg k p q : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hR : 0 ≤ (k : ℝ) * (q - p) := by
    have : 0 ≤ q - p := by linarith
    positivity
  have h1 := Nat.le_ceil ((k : ℝ) * (q - p))
  have h2 := Nat.ceil_lt_add_one hR
  unfold cutoffMg
  constructor
  · have : ((⌈(k : ℝ) * (q - p)⌉₊ : ℝ) - 1) / k < q - p := by
      rw [div_lt_iff₀ hk']; linarith
    linarith
  · have : q - p ≤ (⌈(k : ℝ) * (q - p)⌉₊ : ℝ) / k := by
      rw [le_div_iff₀ hk']; linarith
    linarith

theorem cutoff_compat_general₁ (p₁ p₂ T : ℝ) (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    p₁ + ((cutoffMg k₁ p₁ (cutoffQ p₁ p₂ T) : ℝ) - 1) / k₁
      < p₂ + (cutoffMg k₂ p₂ (cutoffQ p₁ p₂ T) : ℝ) / k₂ :=
  lt_of_lt_of_le (cutoffMg_bounds k₁ hk₁ p₁ _ (cutoffQ_ge₁ p₁ p₂ T)).1
    (cutoffMg_bounds k₂ hk₂ p₂ _ (cutoffQ_ge₂ p₁ p₂ T)).2

theorem cutoff_compat_general₂ (p₁ p₂ T : ℝ) (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    p₂ + ((cutoffMg k₂ p₂ (cutoffQ p₁ p₂ T) : ℝ) - 1) / k₂
      < p₁ + (cutoffMg k₁ p₁ (cutoffQ p₁ p₂ T) : ℝ) / k₁ :=
  lt_of_lt_of_le (cutoffMg_bounds k₂ hk₂ p₂ _ (cutoffQ_ge₂ p₁ p₂ T)).1
    (cutoffMg_bounds k₁ hk₁ p₁ _ (cutoffQ_ge₁ p₁ p₂ T)).2

theorem cutoff_ge_general (p₁ p₂ T : ℝ) (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    2 * T ≤ min (p₁ + (cutoffMg k₁ p₁ (cutoffQ p₁ p₂ T) : ℝ) / k₁)
      (p₂ + (cutoffMg k₂ p₂ (cutoffQ p₁ p₂ T) : ℝ) / k₂) := by
  have h1 := (cutoffMg_bounds k₁ hk₁ p₁ _ (cutoffQ_ge₁ p₁ p₂ T)).2
  have h2 := (cutoffMg_bounds k₂ hk₂ p₂ _ (cutoffQ_ge₂ p₁ p₂ T)).2
  have h3 := two_mul_lt_cutoffQ p₁ p₂ T
  exact le_min (by linarith) (by linarith)

/-- The poles below `2T` (general starts). -/
noncomputable def polesBelowGen (h₁ h₂ k₁ k₂ : ℕ) (p₁ p₂ T : ℝ) : Finset ℝ :=
  (poleSet h₁ h₂ k₁ k₂ (cutoffMg k₁ p₁ (cutoffQ p₁ p₂ T))
    (cutoffMg k₂ p₂ (cutoffQ p₁ p₂ T))).filter (· < 2 * T)

theorem uExp_index_lt_general (h₁ k₁ : ℕ) (hk₁ : 0 < k₁) (p₁ p₂ T : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (i : ℕ) (hi : uExp h₁ k₁ i < 2 * T) :
    i < cutoffMg k₁ p₁ (cutoffQ p₁ p₂ T) := by
  have hk' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  unfold uExp at hi
  push_cast at hi
  rw [show ((h₁ : ℝ) + i + 1) / k₁ = ((h₁ : ℝ) + 1) / k₁ + i / k₁ by ring, hp₁] at hi
  have h1 := (cutoffMg_bounds k₁ hk₁ p₁ _ (cutoffQ_ge₁ p₁ p₂ T)).2
  have h3 := two_mul_lt_cutoffQ p₁ p₂ T
  have : (i : ℝ) / k₁ < (cutoffMg k₁ p₁ (cutoffQ p₁ p₂ T) : ℝ) / k₁ := by linarith
  rw [div_lt_div_iff_of_pos_right hk'] at this
  exact_mod_cast this

theorem vExp_index_lt_general (h₂ k₂ : ℕ) (hk₂ : 0 < k₂) (p₁ p₂ T : ℝ)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (j : ℕ) (hj : vExp h₂ k₂ j < 2 * T) :
    j < cutoffMg k₂ p₂ (cutoffQ p₁ p₂ T) := by
  have hk' : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
  unfold vExp at hj
  push_cast at hj
  rw [show ((h₂ : ℝ) + j + 1) / k₂ = ((h₂ : ℝ) + 1) / k₂ + j / k₂ by ring, hp₂] at hj
  have h1 := (cutoffMg_bounds k₂ hk₂ p₂ _ (cutoffQ_ge₂ p₁ p₂ T)).2
  have h3 := two_mul_lt_cutoffQ p₁ p₂ T
  have : (j : ℝ) / k₂ < (cutoffMg k₂ p₂ (cutoffQ p₁ p₂ T) : ℝ) / k₂ := by linarith
  rw [div_lt_div_iff_of_pos_right hk'] at this
  exact_mod_cast this

/-- **Cutoff-free characterisation** of the retained poles (general starts). -/
theorem mem_polesBelowGen_iff (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p₁ p₂ T : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (α : ℝ) :
    α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T
      ↔ α < 2 * T ∧ ((∃ i, uExp h₁ k₁ i = α) ∨ ∃ j, vExp h₂ k₂ j = α) := by
  unfold polesBelowGen poleSet
  rw [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨h | h, hT⟩
    · obtain ⟨i, -, rfl⟩ := h
      exact ⟨hT, Or.inl ⟨i, rfl⟩⟩
    · obtain ⟨j, -, rfl⟩ := h
      exact ⟨hT, Or.inr ⟨j, rfl⟩⟩
  · rintro ⟨hT, ⟨i, rfl⟩ | ⟨j, rfl⟩⟩
    · exact ⟨Or.inl ⟨i, Finset.mem_range.2 (uExp_index_lt_general h₁ k₁ hk₁ p₁ p₂ T hp₁ i hT),
        rfl⟩, hT⟩
    · exact ⟨Or.inr ⟨j, Finset.mem_range.2 (vExp_index_lt_general h₂ k₂ hk₂ p₁ p₂ T hp₂ j hT),
        rfl⟩, hT⟩

/-- **The Taylor tree for `d = 2` with arbitrary starting exponents** (`thm:TaylorTree`): for
every `T`, `Z(N) − ∑_{α ∈ Λ(h,k), α < 2T} N^{−α}(A_α log N + B_α) = O(N^{−2T}(1 + log N))`. -/
theorem twoD_taylor_tree_general (β b p₁ p₂ ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) (T : ℝ) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) α * Real.log N
              + canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
                  (fun i j s => ampCoeff β x y (i, j) s) α))
      =O[atTop] fun N : ℝ => N ^ (-(2 * T)) * (1 + Real.log N) := by
  set q := cutoffQ p₁ p₂ T with hq
  set M₁ := cutoffMg k₁ p₁ q with hM₁def
  set M₂ := cutoffMg k₂ p₂ q with hM₂def
  set A : ℝ → ℝ := canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) with hA
  set B : ℝ → ℝ := canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b)
    (anaFaceV (ampCoeff β x y) b) (fun i j s => ampCoeff β x y (i, j) s) with hB
  set Z : ℝ → ℝ := fun N => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b) with hZ
  have hmain := twoD_cutoff_general_amplitude_canon β b p₁ p₂ ρ h₁ h₂ k₁ k₂ M₁ M₂ hβ hb hbρ hk₁
    hk₂ hp₁ hp₂ (cutoff_compat_general₁ p₁ p₂ T k₁ k₂ hk₁ hk₂)
    (cutoff_compat_general₂ p₁ p₂ T k₁ k₂ hk₁ hk₂) x y hx hy
  have hrem : (fun N : ℝ => N ^ (-(min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂)))
      * (1 + Real.log N)) =O[atTop] fun N : ℝ => N ^ (-(2 * T)) * (1 + Real.log N) :=
    isBigO_rpow_log_mono _ _ (cutoff_ge_general p₁ p₂ T k₁ k₂ hk₁ hk₂)
  set S := poleSet h₁ h₂ k₁ k₂ M₁ M₂ with hS
  have hsplit : ∀ N : ℝ,
      Z N - ∑ α ∈ S.filter (· < 2 * T), N ^ (-α) * (A α * Real.log N + B α)
        = (Z N - ∑ α ∈ S, N ^ (-α) * (A α * Real.log N + B α))
          + ∑ α ∈ S.filter (fun α => ¬ α < 2 * T), N ^ (-α) * (A α * Real.log N + B α) := by
    intro N
    rw [← Finset.sum_filter_add_sum_filter_not S (· < 2 * T)]
    ring
  have hdisc : (fun N : ℝ => ∑ α ∈ S.filter (fun α => ¬ α < 2 * T),
      N ^ (-α) * (A α * Real.log N + B α)) =O[atTop]
        fun N : ℝ => N ^ (-(2 * T)) * (1 + Real.log N) := by
    have := IsBigO.sum (s := S.filter (fun α => ¬ α < 2 * T)) (l := atTop)
      (A := fun α (N : ℝ) => N ^ (-α) * (A α * Real.log N + B α))
      (g := fun N : ℝ => N ^ (-(2 * T)) * (1 + Real.log N))
      (fun α hα => discard_isBigO T (A α) (B α) α (not_lt.1 (Finset.mem_filter.1 hα).2))
    exact this.congr_left fun N => by simp only [Finset.sum_apply]
  have hfull : (fun N : ℝ => Z N - ∑ α ∈ S, N ^ (-α) * (A α * Real.log N + B α)) =O[atTop]
      fun N : ℝ => N ^ (-(2 * T)) * (1 + Real.log N) := hmain.trans hrem
  exact (hfull.add hdisc).congr_left fun N => (hsplit N).symm

/-- Every retained pole is at least the smallest candidate exponent `min(p₁, p₂)`. -/
theorem min_le_of_mem_polesBelowGen (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (p₁ p₂ T : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (α : ℝ)
    (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) : min p₁ p₂ ≤ α := by
  obtain ⟨-, ⟨i, rfl⟩ | ⟨j, rfl⟩⟩ :=
    (mem_polesBelowGen_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T hp₁ hp₂ α).1 hα
  · refine (min_le_left _ _).trans ?_
    unfold uExp
    push_cast
    rw [← hp₁]
    have hk : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
    gcongr
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  · refine (min_le_right _ _).trans ?_
    unfold vExp
    push_cast
    rw [← hp₂]
    have hk : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
    gcongr
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

end Laplace.Grammar
