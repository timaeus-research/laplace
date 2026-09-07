/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CanonCoeffEnvelope

/-!
# The uniform Taylor tree for `d = 2` (grammar §4.2, Astra #9 R5 completed)

For the analytic family with common envelope `(C₀, L, D, ρ)` and every target `T`, there is a
constant `uniformTreeConst` depending only on `(β, b, ρ, C₀, L, p₁, p₂, T, h, k, D)` such that for
EVERY member `c` of the family and EVERY `N ≥ 1`,

  `|Z_c(N) − ∑_{α ∈ Λ(h,k), α < 2T} N^{−α}(A_α log N + B_α)|`
  `  ≤ uniformTreeConst · N^{−2T}(1 + log N)`

(`twoD_taylor_tree_uniform`). The constant is the uniform cutoff constant of unit 133 at the
cutoffs of unit 129 plus the envelope bounds of unit 134 on the discarded pole terms. Zero
`sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- Every pole is positive. -/
theorem pos_of_mem_poleSet (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α : ℝ)
    (hα : α ∈ poleSet h₁ h₂ k₁ k₂ M₁ M₂) : 0 < α := by
  unfold poleSet at hα
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hα
  rcases hα with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩
  · unfold uExp; positivity
  · unfold vExp; positivity

/-- The envelope bound on `|A_α| + |B_α|`. -/
noncomputable def coeffEnv (b ρ C₀ L β : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (α : ℝ) : ℝ :=
  canonCEnv ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 0 (gaussEnv β L D)
    + (canonUEnv b ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 0 (gaussEnv β L D)
      + canonVEnv b ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 0 (gaussEnv β L D)
      + canonCEnv ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 1 (gaussEnv β L D))

/-- **The uniform Taylor-tree constant** at target `T`. -/
noncomputable def uniformTreeConst (β b ρ C₀ L p₁ p₂ T : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) : ℝ :=
  uniformConst β b ρ C₀ L h₁ h₂ k₁ k₂ (cutoffMg k₁ p₁ (cutoffQ p₁ p₂ T))
      (cutoffMg k₂ p₂ (cutoffQ p₁ p₂ T)) D
    + ∑ α ∈ (poleSet h₁ h₂ k₁ k₂ (cutoffMg k₁ p₁ (cutoffQ p₁ p₂ T))
        (cutoffMg k₂ p₂ (cutoffQ p₁ p₂ T))).filter (fun α => ¬ α < 2 * T),
      coeffEnv b ρ C₀ L β h₁ h₂ k₁ k₂ D α

/-- **The uniform Taylor tree**: one constant for the whole analytic family and every `N ≥ 1`. -/
theorem twoD_taylor_tree_uniform (β b p₁ p₂ ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (c : ℕ × ℕ → ℝ → ℝ) (hcc : ∀ ij, Continuous (c ij))
    (H : ℝ → ℝ) (hH : Continuous H) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (hC₀ : 0 ≤ C₀) (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (T N : ℝ) (hN : 1 ≤ N) :
    |twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp c b)
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α * Real.log N
              + canonB β b h₁ h₂ k₁ k₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) α)|
      ≤ uniformTreeConst β b ρ C₀ L p₁ p₂ T h₁ h₂ k₁ k₂ D
        * (N ^ (-(2 * T)) * (1 + Real.log N)) := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  set q := cutoffQ p₁ p₂ T with hq
  set M₁ := cutoffMg k₁ p₁ q with hM₁def
  set M₂ := cutoffMg k₂ p₂ q with hM₂def
  have hM₁c := cutoff_compat_general₁ p₁ p₂ T k₁ k₂ hk₁ hk₂
  have hM₂c := cutoff_compat_general₂ p₁ p₂ T k₁ k₂ hk₁ hk₂
  set A : ℝ → ℝ := canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) with hA
  set B : ℝ → ℝ := canonB β b h₁ h₂ k₁ k₂ (anaFaceU c b) (anaFaceV c b)
    (fun i j s => c (i, j) s) with hB
  set Z : ℝ := twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp c b) with hZ
  set S := poleSet h₁ h₂ k₁ k₂ M₁ M₂ with hS
  set R : ℝ := N ^ (-(2 * T)) * (1 + Real.log N) with hR
  have hR0 : 0 ≤ R := mul_nonneg (Real.rpow_nonneg hN0.le _) (by linarith)
  -- the cutoff bound, pushed to exponent 2T
  have h1 : |Z - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU c b) (anaFaceV c b)
      (fun i j s => c (i, j) s) N| ≤ uniformConst β b ρ C₀ L h₁ h₂ k₁ k₂ M₁ M₂ D * R := by
    have h := twoD_cutoff_uniform β b p₁ p₂ ρ C₀ L h₁ h₂ k₁ k₂ M₁ M₂ D hβ hb hbρ hk₁ hk₂ hp₁ hp₂
      hM₁c hM₂c c hcc H hH hc hC₀ henv N hN
    have hE := cutoff_ge_general p₁ p₂ T k₁ k₂ hk₁ hk₂
    have h' := bound_mono_exp _ _ _ (2 * T) N hN hE h
    rw [hR, ← mul_assoc]
    exact h'
  -- the merged sum in canonical form
  have hU : ∀ i, i < M₁ →
      faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (anaFaceU c b i) (fun m => c (i, m))
          (canonicalM ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1))
        = faceFPCoeff ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b k₁ (anaFaceU c b i)
            (fun m => c (i, m)) M₂ := fun i hi =>
    (faceFPCoeff_anaFaceU_canonical c b ρ _ H hb hbρ hcc hH hc k₁ i M₂
      (uface_gamma_lt_general_uExp p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁c i hi)).symm
  have hV : ∀ j, j < M₂ →
      faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (anaFaceV c b j) (fun m => c (m, j))
          (canonicalM ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1))
        = faceFPCoeff ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b k₂ (anaFaceV c b j)
            (fun m => c (m, j)) M₁ := fun j hj =>
    (faceFPCoeff_anaFaceV_canonical c b ρ _ H hb hbρ hcc hH hc k₂ j M₁
      (vface_gamma_lt_general_vExp p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂c j hj)).symm
  have hmerge : mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU c b) (anaFaceV c b)
      (fun i j s => c (i, j) s) N = ∑ α ∈ S, N ^ (-α) * (A α * Real.log N + B α) :=
    mergedSum_eq_canon_general β b p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁c hM₂c _ _ _ hU hV N
  -- the discarded terms
  have hdisc : |∑ α ∈ S.filter (fun α => ¬ α < 2 * T), N ^ (-α) * (A α * Real.log N + B α)|
      ≤ (∑ α ∈ S.filter (fun α => ¬ α < 2 * T), coeffEnv b ρ C₀ L β h₁ h₂ k₁ k₂ D α) * R := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α hα => ?_)
    have hα2T : 2 * T ≤ α := not_lt.1 (Finset.mem_filter.1 hα).2
    have hαpos : 0 < α := pos_of_mem_poleSet h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ α
      (Finset.mem_filter.1 hα).1
    refine (discard_explicit T (A α) (B α) α N hα2T hN).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hR0
    unfold coeffEnv
    exact add_le_add
      (canonA_abs_le_env c b ρ C₀ L β H h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ hcc hc henv α hαpos)
      (canonB_abs_le_env c b ρ C₀ L β H h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ hC₀ hcc hH hc henv α
        hαpos)
  -- assemble
  have hsplit : Z - ∑ α ∈ S.filter (· < 2 * T), N ^ (-α) * (A α * Real.log N + B α)
      = (Z - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU c b) (anaFaceV c b)
          (fun i j s => c (i, j) s) N)
        + ∑ α ∈ S.filter (fun α => ¬ α < 2 * T), N ^ (-α) * (A α * Real.log N + B α) := by
    rw [hmerge, ← Finset.sum_filter_add_sum_filter_not S (· < 2 * T)]
    ring
  show |Z - ∑ α ∈ S.filter (· < 2 * T), N ^ (-α) * (A α * Real.log N + B α)|
    ≤ uniformTreeConst β b ρ C₀ L p₁ p₂ T h₁ h₂ k₁ k₂ D * R
  rw [hsplit]
  unfold uniformTreeConst
  calc |(Z - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU c b) (anaFaceV c b)
          (fun i j s => c (i, j) s) N)
        + ∑ α ∈ S.filter (fun α => ¬ α < 2 * T), N ^ (-α) * (A α * Real.log N + B α)|
      ≤ |Z - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU c b) (anaFaceV c b)
          (fun i j s => c (i, j) s) N|
        + |∑ α ∈ S.filter (fun α => ¬ α < 2 * T), N ^ (-α) * (A α * Real.log N + B α)| :=
        abs_add_le _ _
    _ ≤ uniformConst β b ρ C₀ L h₁ h₂ k₁ k₂ M₁ M₂ D * R
        + (∑ α ∈ S.filter (fun α => ¬ α < 2 * T), coeffEnv b ρ C₀ L β h₁ h₂ k₁ k₂ D α) * R :=
        add_le_add h1 hdisc
    _ = _ := by ring

end Laplace.Grammar
