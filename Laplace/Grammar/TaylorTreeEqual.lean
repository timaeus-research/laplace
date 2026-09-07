/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TaylorTreeRegroup

/-!
# The Taylor tree for `d = 2`, equal starting exponents (grammar §4.2, `thm:TaylorTree`)

For every target exponent `T` we choose the truncation orders `M_ℓ = ⌈k_ℓ R⌉₊` with
`R = max 1 (2T − p)`; these satisfy both compatibility inequalities and push the remainder below
`N^{−2T}`. The poles below `2T` form the finite set `polesBelow`, which is characterised without
reference to the cutoff (`mem_polesBelow_iff`: `α < 2T` and `α` is a `u`- or `v`-pole), and the
retained poles `≥ 2T` are discarded into the remainder (`discard_isBigO`). The result is

  `∀ T, Z(N) − ∑_{α ∈ Λ, α < 2T} N^{−α} (A_α log N + B_α) = O(N^{−2T} (1 + log N))`

(`twoD_taylor_tree_equal`) with the coefficients `A_α = canonA`, `B_α = canonB` defined once,
independently of `T`, for the chart amplitude `η e^{βsξ}` of two analytic functions with
weighted-summable coefficient arrays. In the paper's normalisation `n = N²`, `α = 2μ` and
`P_μ(X) = A_α X/2 + B_α`. Astra #8 rank 2. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- The auxiliary order `R = max 1 (2T − p)`. -/
noncomputable def cutoffR (p T : ℝ) : ℝ := max 1 (2 * T - p)

/-- The truncation order `M_ℓ = ⌈k_ℓ R⌉₊`. -/
noncomputable def cutoffM (k : ℕ) (p T : ℝ) : ℕ := ⌈(k : ℝ) * cutoffR p T⌉₊

theorem one_le_cutoffR (p T : ℝ) : 1 ≤ cutoffR p T := le_max_left _ _

theorem two_mul_sub_le_cutoffR (p T : ℝ) : 2 * T - p ≤ cutoffR p T := le_max_right _ _

/-- `(M_ℓ − 1)/k_ℓ < R ≤ M_ℓ/k_ℓ`. -/
theorem cutoffM_bounds (k : ℕ) (hk : 0 < k) (p T : ℝ) :
    ((cutoffM k p T : ℝ) - 1) / k < cutoffR p T ∧ cutoffR p T ≤ (cutoffM k p T : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hR : 0 ≤ (k : ℝ) * cutoffR p T := by
    have := one_le_cutoffR p T; positivity
  have h1 := Nat.le_ceil ((k : ℝ) * cutoffR p T)
  have h2 := Nat.ceil_lt_add_one hR
  unfold cutoffM
  constructor
  · rw [div_lt_iff₀ hk']; linarith
  · rw [le_div_iff₀ hk']; linarith

theorem cutoff_compat₁ (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p T : ℝ) :
    ((cutoffM k₁ p T : ℝ) - 1) / k₁ < (cutoffM k₂ p T : ℝ) / k₂ :=
  lt_of_lt_of_le (cutoffM_bounds k₁ hk₁ p T).1 (cutoffM_bounds k₂ hk₂ p T).2

theorem cutoff_compat₂ (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p T : ℝ) :
    ((cutoffM k₂ p T : ℝ) - 1) / k₂ < (cutoffM k₁ p T : ℝ) / k₁ :=
  lt_of_lt_of_le (cutoffM_bounds k₂ hk₂ p T).1 (cutoffM_bounds k₁ hk₁ p T).2

/-- The remainder exponent reaches `2T`. -/
theorem cutoff_ge (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p T : ℝ) :
    2 * T ≤ p + min ((cutoffM k₁ p T : ℝ) / k₁) ((cutoffM k₂ p T : ℝ) / k₂) := by
  have h1 := (cutoffM_bounds k₁ hk₁ p T).2
  have h2 := (cutoffM_bounds k₂ hk₂ p T).2
  have h3 := two_mul_sub_le_cutoffR p T
  have : cutoffR p T ≤ min ((cutoffM k₁ p T : ℝ) / k₁) ((cutoffM k₂ p T : ℝ) / k₂) :=
    le_min h1 h2
  linarith

/-- The poles below `2T`. -/
noncomputable def polesBelow (h₁ h₂ k₁ k₂ : ℕ) (p T : ℝ) : Finset ℝ :=
  (poleSet h₁ h₂ k₁ k₂ (cutoffM k₁ p T) (cutoffM k₂ p T)).filter (· < 2 * T)

/-- A `u`-pole below `2T` has index below the cutoff. -/
theorem uExp_index_lt (h₁ k₁ : ℕ) (hk₁ : 0 < k₁) (p T : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (i : ℕ) (hi : uExp h₁ k₁ i < 2 * T) : i < cutoffM k₁ p T := by
  have hk' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  unfold uExp at hi
  push_cast at hi
  rw [show ((h₁ : ℝ) + i + 1) / k₁ = ((h₁ : ℝ) + 1) / k₁ + i / k₁ by ring, hp₁] at hi
  have hi' : (i : ℝ) / k₁ < 2 * T - p := by linarith
  rw [div_lt_iff₀ hk'] at hi'
  have h1 := (cutoffM_bounds k₁ hk₁ p T).2
  rw [le_div_iff₀ hk'] at h1
  have h3 := mul_le_mul_of_nonneg_right (two_mul_sub_le_cutoffR p T) hk'.le
  have : (i : ℝ) < cutoffM k₁ p T := by linarith
  exact_mod_cast this

theorem vExp_index_lt (h₂ k₂ : ℕ) (hk₂ : 0 < k₂) (p T : ℝ) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (j : ℕ) (hj : vExp h₂ k₂ j < 2 * T) : j < cutoffM k₂ p T := by
  have hk' : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
  unfold vExp at hj
  push_cast at hj
  rw [show ((h₂ : ℝ) + j + 1) / k₂ = ((h₂ : ℝ) + 1) / k₂ + j / k₂ by ring, hp₂] at hj
  have hj' : (j : ℝ) / k₂ < 2 * T - p := by linarith
  rw [div_lt_iff₀ hk'] at hj'
  have h1 := (cutoffM_bounds k₂ hk₂ p T).2
  rw [le_div_iff₀ hk'] at h1
  have h3 := mul_le_mul_of_nonneg_right (two_mul_sub_le_cutoffR p T) hk'.le
  have : (j : ℝ) < cutoffM k₂ p T := by linarith
  exact_mod_cast this

/-- **Cutoff-free characterisation**: `α ∈ polesBelow ↔ α < 2T ∧ α ∈ Λ(h,k)`. -/
theorem mem_polesBelow_iff (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p T : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (α : ℝ) :
    α ∈ polesBelow h₁ h₂ k₁ k₂ p T
      ↔ α < 2 * T ∧ ((∃ i, uExp h₁ k₁ i = α) ∨ ∃ j, vExp h₂ k₂ j = α) := by
  unfold polesBelow poleSet
  rw [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨h | h, hT⟩
    · obtain ⟨i, -, rfl⟩ := h
      exact ⟨hT, Or.inl ⟨i, rfl⟩⟩
    · obtain ⟨j, -, rfl⟩ := h
      exact ⟨hT, Or.inr ⟨j, rfl⟩⟩
  · rintro ⟨hT, ⟨i, rfl⟩ | ⟨j, rfl⟩⟩
    · exact ⟨Or.inl ⟨i, Finset.mem_range.2 (uExp_index_lt h₁ k₁ hk₁ p T hp₁ i hT), rfl⟩, hT⟩
    · exact ⟨Or.inr ⟨j, Finset.mem_range.2 (vExp_index_lt h₂ k₂ hk₂ p T hp₂ j hT), rfl⟩, hT⟩

/-- A retained pole term with exponent `α ≥ 2T` is absorbed by the remainder. -/
theorem discard_isBigO (T A B α : ℝ) (hα : 2 * T ≤ α) :
    (fun N : ℝ => N ^ (-α) * (A * Real.log N + B)) =O[atTop]
      fun N : ℝ => N ^ (-(2 * T)) * (1 + Real.log N) := by
  refine IsBigO.of_bound (|A| + |B|) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hpow : N ^ (-α) ≤ N ^ (-(2 * T)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hpos : 0 ≤ N ^ (-α) := by positivity
  have hpos' : 0 ≤ N ^ (-(2 * T)) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos,
    abs_of_nonneg (by positivity : 0 ≤ N ^ (-(2 * T)) * (1 + Real.log N))]
  have h1 : |A * Real.log N + B| ≤ (|A| + |B|) * (1 + Real.log N) := by
    calc |A * Real.log N + B| ≤ |A * Real.log N| + |B| := abs_add_le _ _
      _ = |A| * Real.log N + |B| := by rw [abs_mul, abs_of_nonneg hlog]
      _ ≤ (|A| + |B|) * (1 + Real.log N) := by nlinarith [abs_nonneg A, abs_nonneg B]
  calc N ^ (-α) * |A * Real.log N + B|
      ≤ N ^ (-(2 * T)) * ((|A| + |B|) * (1 + Real.log N)) := by
        gcongr
    _ = (|A| + |B|) * (N ^ (-(2 * T)) * (1 + Real.log N)) := by ring

/-- **The Taylor tree for `d = 2` with equal starting exponents** (`thm:TaylorTree`, analytic
`ξ, η` with weighted-summable coefficient arrays `x, y` at a radius `ρ > b`): for every `T`,
`Z(N) − ∑_{α ∈ Λ(h,k), α < 2T} N^{−α}(A_α log N + B_α) = O(N^{−2T}(1 + log N))`, with the
coefficients `A_α = canonA`, `B_α = canonB` independent of `T`. -/
theorem twoD_taylor_tree_equal (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hy : WSummable ρ y)
    (T : ℝ) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - ∑ α ∈ polesBelow h₁ h₂ k₁ k₂ p T,
            N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) α * Real.log N
              + canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
                  (fun i j s => ampCoeff β x y (i, j) s) α))
      =O[atTop] fun N : ℝ => N ^ (-(2 * T)) * (1 + Real.log N) := by
  set M₁ := cutoffM k₁ p T with hM₁def
  set M₂ := cutoffM k₂ p T with hM₂def
  set A : ℝ → ℝ := canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) with hA
  set B : ℝ → ℝ := canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b)
    (anaFaceV (ampCoeff β x y) b) (fun i j s => ampCoeff β x y (i, j) s) with hB
  set Z : ℝ → ℝ := fun N => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b) with hZ
  have hmain := twoD_cutoff_amplitude_canon β b p ρ h₁ h₂ k₁ k₂ M₁ M₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂
    (cutoff_compat₁ k₁ k₂ hk₁ hk₂ p T) (cutoff_compat₂ k₁ k₂ hk₁ hk₂ p T) x y hx hy
  have hrem : (fun N : ℝ => N ^ (-(p + min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂))) * (1 + Real.log N))
      =O[atTop] fun N : ℝ => N ^ (-(2 * T)) * (1 + Real.log N) :=
    isBigO_rpow_log_mono _ _ (cutoff_ge k₁ k₂ hk₁ hk₂ p T)
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

end Laplace.Grammar
