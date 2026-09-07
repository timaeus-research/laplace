/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AmplitudeAdapter

/-!
# Merging the log families of the reduced cutoff expansion (grammar §4.2)

The reduced sum of `TwoDCutoffReduced` lists three log families: the `u`-face logs, the `v`-face
logs and (subtracted) the corner logs. Each is supported on the collision predicate
`(h₁+i+1)/k₁ = (h₂+j+1)/k₂`, and for fixed `i` (resp. `j`) at most one partner collides. Hence
the `v`-face family equals the corner family exactly, and the reduced sum equals the merged sum

  `mergedSum = (face finite parts) + ∑_{i<M₁} ∑_{j<M₂} [collision] transferTerm(α_i, c_ij/(k₁k₂))`

with ONE log term per collision (`reducedSum_eq_merged`). The proof is integrability-free: it uses
only that `transferTerm` of the zero function vanishes and finite-sum manipulations. The analytic
cutoff theorems are restated in merged form (`twoD_cutoff_analytic_merged`,
`twoD_cutoff_amplitude_merged`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

theorem transferTerm_zero_fun (β α : ℝ) (j : ℕ) (N : ℝ) :
    transferTerm β α j (fun _ => (0 : ℝ)) N = 0 := by
  simp [transferTerm, logMoment_zero_fun]

/-- `transferTerm` commutes with an `if`. -/
theorem transferTerm_ite (β α : ℝ) (n : ℕ) (P : Prop) [Decidable P] (g : ℝ → ℝ) (N : ℝ) :
    transferTerm β α n (fun s => if P then g s else 0) N
      = if P then transferTerm β α n g N else 0 := by
  by_cases hP : P
  · simp only [hP, if_true]
  · simp only [hP, if_false]
    exact transferTerm_zero_fun β α n N

/-- `transferTerm` of a sum of `if`s over a predicate with at most one witness. -/
theorem transferTerm_sum_ite_unique {ι : Type*} (β α : ℝ) (n : ℕ) (t : Finset ι) (Q : ι → Prop)
    [DecidablePred Q] (huniq : ∀ i ∈ t, ∀ j ∈ t, Q i → Q j → i = j) (g : ι → ℝ → ℝ) (N : ℝ) :
    transferTerm β α n (fun x => ∑ i ∈ t, if Q i then g i x else 0) N
      = ∑ i ∈ t, if Q i then transferTerm β α n (g i) N else 0 := by
  by_cases h : ∃ i ∈ t, Q i
  · obtain ⟨i₀, hi₀, hQ⟩ := h
    have hother : ∀ j ∈ t, j ≠ i₀ → ¬ Q j := fun j hj hne hQj => hne (huniq j hj i₀ hi₀ hQj hQ)
    have hfun : (fun x => ∑ i ∈ t, if Q i then g i x else 0) = g i₀ := by
      funext x
      rw [Finset.sum_eq_single i₀ (fun j hj hne => if_neg (hother j hj hne))
        (fun h => absurd hi₀ h), if_pos hQ]
    rw [hfun, Finset.sum_eq_single i₀ (fun j hj hne => if_neg (hother j hj hne))
      (fun h => absurd hi₀ h), if_pos hQ]
  · push Not at h
    have hfun : (fun x => ∑ i ∈ t, if Q i then g i x else 0) = fun _ => 0 := by
      funext x
      exact Finset.sum_eq_zero fun i hi => if_neg (h i hi)
    rw [hfun, transferTerm_zero_fun, Finset.sum_eq_zero fun i hi => if_neg (h i hi)]

/-- The log coefficient of a corner is a single `if`. -/
theorem faceLogCoeff_cornerData (γ : ℝ) (k₁ k₂ : ℕ) (c : ℝ → ℝ) (M : ℕ) (hM : 0 < M) :
    faceLogCoeff γ k₁ k₂ (cornerData c) M
      = fun s => if (0 : ℝ) = γ then 1 / ((k₁ : ℝ) * k₂) * c s else 0 := by
  funext s
  unfold faceLogCoeff
  rw [Finset.sum_eq_single 0]
  · simp [cornerData]
  · intro m _ hm
    simp [cornerData, hm]
  · intro h
    exact absurd (Finset.mem_range.2 hM) h

/-- The `u`-face exponent `(h₁+i+1)/k₁`. -/
noncomputable def uExp (h₁ k₁ i : ℕ) : ℝ := (((h₁ + i : ℕ) : ℝ) + 1) / k₁

theorem uExp_injective (h₁ k₁ : ℕ) (hk₁ : 0 < k₁) (i i' : ℕ) (h : uExp h₁ k₁ i = uExp h₁ k₁ i') :
    i = i' := by
  unfold uExp at h
  have hk : (k₁ : ℝ) ≠ 0 := by positivity
  rw [div_left_inj' hk] at h
  push_cast at h
  exact_mod_cast (by linarith : (i : ℝ) = i')

/-- The `u`-face resonance predicate `m = k₂ α_i − h₂ − 1` is the collision `α_i = α'_m`. -/
theorem uface_resonance_iff (h₁ h₂ k₁ k₂ i m : ℕ) (hk₂ : 0 < k₂) :
    ((m : ℝ) = (k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1)
      ↔ (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + m : ℕ) : ℝ) + 1) / k₂ := by
  have hk : (k₂ : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hk]
  push_cast
  constructor <;> intro h <;> linarith

/-- The `v`-face resonance predicate `m = k₁ α'_j − h₁ − 1` is the collision `α_m = α'_j`. -/
theorem vface_resonance_iff (h₁ h₂ k₁ k₂ m j : ℕ) (hk₁ : 0 < k₁) :
    ((m : ℝ) = (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1)
      ↔ (((h₁ + m : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ := by
  have hk : (k₁ : ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hk]
  push_cast
  constructor <;> intro h <;> linarith

/-- The corner resonance predicate `0 = k₁ α'_j − (h₁+i) − 1` is the collision `α_i = α'_j`. -/
theorem corner_resonance_iff (h₁ h₂ k₁ k₂ i j : ℕ) (hk₁ : 0 < k₁) :
    ((0 : ℝ) = (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)
      ↔ (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ := by
  have hk : (k₁ : ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hk]
  push_cast
  constructor <;> intro h <;> linarith

/-- The merged log family: one transferred log term per collision `(i, j)`. -/
noncomputable def mergedLog (β : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
    if (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ then
      transferTerm β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) 1 (fun s => c i j s / ((k₁ : ℝ) * k₂)) N
    else 0

/-- The merged transferred sum: face finite parts plus the merged log family. -/
noncomputable def mergedSum (β b : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (a bj : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) : ℝ :=
  (∑ i ∈ Finset.range M₁, N ^ (-((((h₁ + i : ℕ) : ℝ) + 1) / k₁))
      * logMoment β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) 0
        (faceFPCoeff ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) b k₁ (a i)
          (fun m => c i m) M₂))
  + (∑ j ∈ Finset.range M₂, N ^ (-((((h₂ + j : ℕ) : ℝ) + 1) / k₂))
      * logMoment β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 0
        (faceFPCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1) b k₂ (bj j)
          (fun m => c m j) M₁))
  + mergedLog β h₁ h₂ k₁ k₂ M₁ M₂ c N

/-- The `u`-face log family equals the merged log family. -/
theorem uface_log_eq_merged (β : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₂ : 0 < k₂)
    (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) :
    (∑ i ∈ Finset.range M₁, transferTerm β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) 1
      (faceLogCoeff ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) k₂ k₁
        (fun m => c i m) M₂) N)
      = mergedLog β h₁ h₂ k₁ k₂ M₁ M₂ c N := by
  unfold mergedLog
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : faceLogCoeff ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) k₂ k₁
      (fun m => c i m) M₂
      = fun s => ∑ j ∈ Finset.range M₂,
        if (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ then
          c i j s / ((k₁ : ℝ) * k₂) else 0 := by
    funext s
    unfold faceLogCoeff
    refine Finset.sum_congr rfl fun j _ => ?_
    exact if_congr (uface_resonance_iff h₁ h₂ k₁ k₂ i j hk₂) (by ring) rfl
  rw [hfun]
  refine transferTerm_sum_ite_unique β _ 1 (Finset.range M₂) _ ?_ (fun j s => c i j s / _) N
  intro j _ j' _ hj hj'
  have hk : (k₂ : ℝ) ≠ 0 := by positivity
  have h := hj.symm.trans hj'
  rw [div_left_inj' hk] at h
  push_cast at h
  exact_mod_cast (by linarith : (j : ℝ) = j')

/-- The `v`-face log family, rewritten over collisions. -/
theorem vface_log_eq (β : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁)
    (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) :
    (∑ j ∈ Finset.range M₂, transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
      (faceLogCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1) k₁ k₂
        (fun m => c m j) M₁) N)
      = ∑ j ∈ Finset.range M₂, ∑ i ∈ Finset.range M₁,
        if (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ then
          transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
            (fun s => c i j s / ((k₁ : ℝ) * k₂)) N
        else 0 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfun : faceLogCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1) k₁ k₂
      (fun m => c m j) M₁
      = fun s => ∑ i ∈ Finset.range M₁,
        if (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ then
          c i j s / ((k₁ : ℝ) * k₂) else 0 := by
    funext s
    unfold faceLogCoeff
    refine Finset.sum_congr rfl fun i _ => ?_
    exact if_congr (vface_resonance_iff h₁ h₂ k₁ k₂ i j hk₁) (by ring) rfl
  rw [hfun]
  refine transferTerm_sum_ite_unique β _ 1 (Finset.range M₁) _ ?_ (fun i s => c i j s / _) N
  intro i _ i' _ hi hi'
  exact uExp_injective h₁ k₁ hk₁ i i' (hi.trans hi'.symm)

/-- The corner log family, rewritten over collisions. -/
theorem corner_log_eq (β : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁)
    (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) :
    (∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
      transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
        (faceLogCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ k₂
          (cornerData (c i j)) (M₁ + k₁ * M₂)) N)
      = ∑ j ∈ Finset.range M₂, ∑ i ∈ Finset.range M₁,
        if (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ then
          transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
            (fun s => c i j s / ((k₁ : ℝ) * k₂)) N
        else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
  have hM : 0 < M₁ + k₁ * M₂ := by
    have := Finset.mem_range.1 hi; omega
  rw [faceLogCoeff_cornerData _ k₁ k₂ (c i j) _ hM]
  have hfun : (fun s => if (0 : ℝ) = (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
        - ((h₁ + i : ℕ) : ℝ) - 1 then 1 / ((k₁ : ℝ) * k₂) * c i j s else 0)
      = fun s => if (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ then
          c i j s / ((k₁ : ℝ) * k₂) else 0 := by
    funext s
    exact if_congr (corner_resonance_iff h₁ h₂ k₁ k₂ i j hk₁) (by ring) rfl
  rw [hfun, transferTerm_ite]

/-- **The reduced sum equals the merged sum** (exact, for every `N`, integrability-free). -/
theorem reducedSum_eq_merged (β b : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (a bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) :
    reducedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N = mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N := by
  unfold reducedSum mergedSum
  rw [uface_log_eq_merged β h₁ h₂ k₁ k₂ M₁ M₂ hk₂ c N, vface_log_eq β h₁ h₂ k₁ k₂ M₁ M₂ hk₁ c N,
    corner_log_eq β h₁ h₂ k₁ k₂ M₁ M₂ hk₁ c N]
  ring

/-- The analytic `d = 2` cutoff theorem in merged form. -/
theorem twoD_cutoff_analytic_merged (β b p ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁)
    (c : ℕ × ℕ → ℝ → ℝ) (hcc : ∀ ij, Continuous (c ij)) (H : ℝ → ℝ) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp c b)
        - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i,
    j) s) N)
      =O[atTop] fun N : ℝ =>
        N ^ (-(p + min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂))) * (1 + Real.log N) :=
  (twoD_cutoff_analytic β b p ρ C₀ L h₁ h₂ k₁ k₂ M₁ M₂ D hβ hb hbρ hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ c hcc
    H hH hc hC₀ henv).congr_left fun N => by
      rw [reducedSum_eq_merged β b h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂]

/-- **The analytic `d = 2` cutoff theorem for `η e^{βsξ}` in merged form**: one log term per
collision. -/
theorem twoD_cutoff_amplitude_merged (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁)
    (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hy : WSummable ρ y) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU (ampCoeff β x y) b)
            (anaFaceV (ampCoeff β x y) b) (fun i j s => ampCoeff β x y (i, j) s) N)
      =O[atTop] fun N : ℝ =>
        N ^ (-(p + min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂))) * (1 + Real.log N) :=
  (twoD_cutoff_amplitude β b p ρ h₁ h₂ k₁ k₂ M₁ M₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ x y hx
    hy).congr_left fun N => by
      rw [reducedSum_eq_merged β b h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂]

end Laplace.Grammar
