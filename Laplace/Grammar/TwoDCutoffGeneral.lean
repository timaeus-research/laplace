/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MomentSeries

/-!
# The `d = 2` cutoff expansion with unequal starting exponents (grammar §4.2, Astra #8 rank 3)

The equal-exponent assembly `twoD_cutoff_isBigO` used `(h₁+1)/k₁ = (h₂+1)/k₂ = p` only for
exponent bookkeeping. Here the two starting exponents `p₁ = (h₁+1)/k₁`, `p₂ = (h₂+1)/k₂` are
independent. With `α_i = (h₁+i+1)/k₁`, `δ_j = (h₂+j+1)/k₂` and `D = δ_j − α_i`:

* the face-vs-corner cancellations are identities in `D` alone (`uface_coeff_eq_corner_fp'`,
  `uface_exp_eq'`), so the over-complete sum equals the merged sum for ANY corner truncation order
  `Mc > 0` (`overcomplete_eq_merged`);
* the `u`-face `i` remainder exponent is `p₂ + M₂/k₂` (independent of `i`), the `v`-face one is
  `p₁ + M₁/k₁`, the mixed remainder exponent is `q_M = min(p₁ + M₁/k₁, p₂ + M₂/k₂)`;
* the admissibility `γ_i < M₂` of the `u`-face expansions follows from the shifted compatibility
  `p₁ + (M₁−1)/k₁ < p₂ + M₂/k₂`; the corner admissibility `k₁δ_j − (h₁+i) − 1 < Mc` is a
  hypothesis on `Mc` (discharged by an explicit choice in the analytic adapter).

Main result: `twoD_cutoff_general_merged`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- `j − γ_i = k₂ (δ_j − α_i)`. -/
theorem sub_gamma_u (h₁ h₂ k₁ k₂ i j : ℕ) (hk₂ : 0 < k₂) :
    (j : ℝ) - ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1)
      = (k₂ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂ - (((h₁ + i : ℕ) : ℝ) + 1) / k₁) := by
  have hk : (k₂ : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `0 − γ_c = −k₁ (δ_j − α_i)`. -/
theorem sub_gamma_c (h₁ h₂ k₁ k₂ i j : ℕ) (hk₁ : 0 < k₁) :
    (0 : ℝ) - ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)
      = -((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂ - (((h₁ + i : ℕ) : ℝ) + 1) / k₁)) := by
  have hk : (k₁ : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Cancellation (u-face vs corner), general starting exponents.** -/
theorem uface_coeff_eq_corner_fp' (b : ℝ) (h₁ h₂ k₁ k₂ i j Mc : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hMc : 0 < Mc) (c : ℕ → ℕ → ℝ → ℝ) :
    faceCoeff ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) (b ^ k₁) k₂ k₁
        (fun m => c i m) j
      = faceFPCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) b k₂
        (fun _ s => c i j s) (cornerData (c i j)) Mc := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  funext s
  rw [faceFPCoeff_corner _ b k₂ (c i j) Mc hMc s]
  set γu : ℝ := (k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1 with hγu
  set γc : ℝ := (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1 with hγc
  set D : ℝ := (((h₂ + j : ℕ) : ℝ) + 1) / k₂ - (((h₁ + i : ℕ) : ℝ) + 1) / k₁ with hD
  have hu : (j : ℝ) - γu = k₂ * D := sub_gamma_u h₁ h₂ k₁ k₂ i j hk₂
  have hc0 : (0 : ℝ) - γc = -(k₁ * D) := sub_gamma_c h₁ h₂ k₁ k₂ i j hk₁
  have hcN : ((0 : ℕ) : ℝ) - γc = -(k₁ * D) := by rw [Nat.cast_zero]; exact hc0
  have hiff : ((j : ℝ) = γu) ↔ (((0 : ℕ) : ℝ) = γc) := by
    rw [Nat.cast_zero]
    constructor
    · intro h
      have h1 : (k₂ : ℝ) * D = 0 := by linarith
      have hD0 : D = 0 := (mul_eq_zero.1 h1).resolve_left hk₂'.ne'
      rw [hD0, mul_zero, neg_zero] at hc0
      linarith
    · intro h
      have h1 : (k₁ : ℝ) * D = 0 := by linarith
      have hD0 : D = 0 := (mul_eq_zero.1 h1).resolve_left hk₁'.ne'
      rw [hD0, mul_zero] at hu
      linarith
  unfold faceCoeff axisPrim
  by_cases h : (j : ℝ) = γu
  · rw [if_pos h, if_pos (hiff.1 h), Real.log_pow]
    push_cast
    field_simp
    try ring
  · have h' : ¬ (((0 : ℕ) : ℝ) = γc) := fun h' => h (hiff.2 h')
    rw [if_neg h, if_neg h']
    have hD0 : D ≠ 0 := by
      intro hD0
      apply h
      rw [hD0, mul_zero] at hu
      linarith
    have hpow : ((b : ℝ) ^ k₁) ^ (-(((j : ℝ) - γu) / k₂)) = b ^ (((0 : ℕ) : ℝ) - γc) := by
      rw [← Real.rpow_natCast b k₁, ← Real.rpow_mul hb.le]
      congr 1
      rw [hu, hcN]
      field_simp
    rw [hpow, hu, hcN]
    field_simp

/-- The `u`-face monomial exponent `m = j` is the `v`-pole `δ_j` (general starting exponents). -/
theorem uface_exp_eq' (h₁ h₂ k₁ k₂ i j : ℕ) (hk₂ : 0 < k₂) :
    faceExp ((((h₁ + i : ℕ) : ℝ) + 1) / k₁)
        ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) k₂ j
      = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ := by
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  unfold faceExp
  rw [sub_gamma_u h₁ h₂ k₁ k₂ i j hk₂, mul_div_cancel_left₀ _ hk₂'.ne']
  ring

/-- The corner log family at an arbitrary corner order `Mc > 0`, over collisions. -/
theorem corner_log_eq' (β : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ Mc : ℕ) (hk₁ : 0 < k₁) (hMc : 0 < Mc)
    (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) :
    (∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
      transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
        (faceLogCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ k₂
          (cornerData (c i j)) Mc) N)
      = ∑ j ∈ Finset.range M₂, ∑ i ∈ Finset.range M₁,
        if (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ then
          transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
            (fun s => c i j s / ((k₁ : ℝ) * k₂)) N
        else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [faceLogCoeff_cornerData _ k₁ k₂ (c i j) _ hMc]
  have hfun : (fun s => if (0 : ℝ) = (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
        - ((h₁ + i : ℕ) : ℝ) - 1 then 1 / ((k₁ : ℝ) * k₂) * c i j s else 0)
      = fun s => if (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ then
          c i j s / ((k₁ : ℝ) * k₂) else 0 := by
    funext s
    exact if_congr (corner_resonance_iff h₁ h₂ k₁ k₂ i j hk₁) (by ring) rfl
  rw [hfun, transferTerm_ite]

/-- **The over-complete sum equals the merged sum** for any corner order `Mc > 0` and arbitrary
starting exponents. -/
theorem overcomplete_eq_merged (β b : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ Mc : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hMc : 0 < Mc) (a bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) :
    (∑ i ∈ Finset.range M₁,
        faceSum β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) N)
      + (∑ j ∈ Finset.range M₂,
          faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) N)
      - ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
          faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ Mc
            (fun _ s => c i j s) (cornerData (c i j)) N
      = mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N := by
  -- the u-faces
  have hu : ∀ i ∈ Finset.range M₁,
      faceSum β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) N
        = (∑ j ∈ Finset.range M₂, N ^ (-((((h₂ + j : ℕ) : ℝ) + 1) / k₂))
            * logMoment β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 0
              (faceFPCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)
                b k₂ (fun _ s => c i j s) (cornerData (c i j)) Mc))
          + N ^ (-((((h₁ + i : ℕ) : ℝ) + 1) / k₁))
            * logMoment β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) 0
              (faceFPCoeff ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) b k₁ (a i)
                (fun m => c i m) M₂)
          + transferTerm β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) 1
              (faceLogCoeff ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) k₂ k₁
                (fun m => c i m) M₂) N := by
    intro i _
    unfold faceSum
    rw [face_transfer_sum_eq, transferTerm_one]
    congr 1
    congr 1
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [uface_exp_eq' h₁ h₂ k₁ k₂ i j hk₂,
      uface_coeff_eq_corner_fp' b h₁ h₂ k₁ k₂ i j Mc hb hk₁ hk₂ hMc c]
  -- the v-faces
  have hv : ∀ j ∈ Finset.range M₂,
      faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) N
        = (∑ i ∈ Finset.range M₁, N ^ (-(faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
            ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ 0))
            * logMoment β (faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
              ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ 0) 0
              (faceCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)
                (b ^ k₂) k₁ k₂ (cornerData (c i j)) 0))
          + N ^ (-((((h₂ + j : ℕ) : ℝ) + 1) / k₂))
            * logMoment β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 0
              (faceFPCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1) b k₂ (bj j)
                (fun m => c m j) M₁)
          + transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
              (faceLogCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1) k₁ k₂
                (fun m => c m j) M₁) N := by
    intro j _
    unfold faceSum
    rw [face_transfer_sum_eq, transferTerm_one]
    congr 1
    congr 1
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vface_exp_eq h₁ h₂ k₁ k₂ i j, vface_coeff_eq_corner_coeff b h₁ h₂ k₁ k₂ i j c]
  -- the corners
  have hc : ∀ i ∈ Finset.range M₁, ∀ j ∈ Finset.range M₂,
      faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ Mc
          (fun _ s => c i j s) (cornerData (c i j)) N
        = N ^ (-(faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
            ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ 0))
            * logMoment β (faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
              ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ 0) 0
              (faceCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)
                (b ^ k₂) k₁ k₂ (cornerData (c i j)) 0)
          + N ^ (-((((h₂ + j : ℕ) : ℝ) + 1) / k₂))
            * logMoment β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 0
              (faceFPCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)
                b k₂ (fun _ s => c i j s) (cornerData (c i j)) Mc)
          + transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
              (faceLogCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)
                k₁ k₂ (cornerData (c i j)) Mc) N := by
    intro i _ j _
    unfold faceSum
    rw [face_transfer_sum_eq, transferTerm_one]
    congr 1
    congr 1
    obtain ⟨Mc', hMc'⟩ : ∃ Mc', Mc = Mc' + 1 := ⟨Mc - 1, by omega⟩
    rw [hMc', Fin.sum_univ_succ, Finset.sum_eq_zero fun m _ => ?_]
    · simp
    · simp only [Fin.val_succ]
      rw [faceCoeff_cornerData_succ, logMoment_zero_fun, mul_zero]
  rw [Finset.sum_congr rfl hu, Finset.sum_congr rfl hv,
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (hc i hi)]
  simp only [Finset.sum_add_distrib]
  rw [corner_log_eq' β h₁ h₂ k₁ k₂ M₁ M₂ Mc hk₁ hMc c N,
    ← vface_log_eq β h₁ h₂ k₁ k₂ M₁ M₂ hk₁ c N,
    uface_log_eq_merged β h₁ h₂ k₁ k₂ M₁ M₂ hk₂ c N]
  unfold mergedSum
  have hcomm : ∑ j ∈ Finset.range M₂, ∑ i ∈ Finset.range M₁,
      N ^ (-(faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
        ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ 0))
      * logMoment β (faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
        ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ 0) 0
        (faceCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)
          (b ^ k₂) k₁ k₂ (cornerData (c i j)) 0)
      = ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
      N ^ (-(faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
        ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ 0))
      * logMoment β (faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
        ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ 0) 0
        (faceCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)
          (b ^ k₂) k₁ k₂ (cornerData (c i j)) 0) := Finset.sum_comm
  rw [hcomm]
  ring


/-- The `u`-face admissibility `γ_i < M₂` from the shifted compatibility. -/
theorem uface_gamma_lt_general (p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂) (i : ℕ) (hi : i < M₁) :
    (k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1 < M₂ := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hα : (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = p₁ + (i : ℝ) / k₁ := by
    rw [← hp₁]; push_cast; field_simp; ring
  have e : (k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1
      = (k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁ - p₂) := by
    rw [← hp₂]; field_simp; ring
  rw [e, hα]
  have hi' : (i : ℝ) + 1 ≤ M₁ := by exact_mod_cast hi
  have h1 : (i : ℝ) / k₁ ≤ ((M₁ : ℝ) - 1) / k₁ := by gcongr; linarith
  have h2 : (k₂ : ℝ) * (p₁ + (i : ℝ) / k₁ - p₂) < (k₂ : ℝ) * ((M₂ : ℝ) / k₂) :=
    mul_lt_mul_of_pos_left (by linarith) hk₂'
  rw [mul_div_cancel₀ _ hk₂'.ne'] at h2
  exact h2

theorem vface_gamma_lt_general (p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁) (j : ℕ) (hj : j < M₂) :
    (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1 < M₁ := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hδ : (((h₂ + j : ℕ) : ℝ) + 1) / k₂ = p₂ + (j : ℝ) / k₂ := by
    rw [← hp₂]; push_cast; field_simp; ring
  have e : (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1
      = (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂ - p₁) := by
    rw [← hp₁]; field_simp; ring
  rw [e, hδ]
  have hj' : (j : ℝ) + 1 ≤ M₂ := by exact_mod_cast hj
  have h1 : (j : ℝ) / k₂ ≤ ((M₂ : ℝ) - 1) / k₂ := by gcongr; linarith
  have h2 : (k₁ : ℝ) * (p₂ + (j : ℝ) / k₂ - p₁) < (k₁ : ℝ) * ((M₁ : ℝ) / k₁) :=
    mul_lt_mul_of_pos_left (by linarith) hk₁'
  rw [mul_div_cancel₀ _ hk₁'.ne'] at h2
  exact h2

/-- **The corner admissibility from shifted compatibility**: `γ_ij = k₁δ_j − (h₁+i) − 1 < M₁`
(Astra #9), so the corner order `M₁ + k₁M₂` remains admissible for unequal starts. -/
theorem corner_gamma_lt_general (p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁) (i j : ℕ) (hj : j < M₂) :
    (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1 < M₁ := by
  have h := vface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j hj
  push_cast at h ⊢
  linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]

/-- **The cutoff-indexed expansion of the `d = 2` block with unequal starting exponents.**
Remainder exponent `E = min(p₁ + M₁/k₁, p₂ + M₂/k₂)`; compatibility
`p₁ + (M₁−1)/k₁ < p₂ + M₂/k₂` and symmetrically. -/
theorem twoD_cutoff_general_isBigO (β b p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁)
    (Φ : ℝ → ℝ → ℝ → ℝ) (a bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2)
    (ha : ∀ i, Continuous (Function.uncurry (a i)))
    (hb' : ∀ j, Continuous (Function.uncurry (bj j))) (hc : ∀ i j, Continuous (c i j))
    (Ha Hb : ℕ → ℝ → ℝ) (hHa : ∀ i, Measurable (Ha i)) (hHa0 : ∀ i s, 0 ≤ Ha i s)
    (hHb : ∀ j, Measurable (Hb j)) (hHb0 : ∀ j s, 0 ≤ Hb j s)
    (hremA : ∀ i, i < M₁ → ∀ s, 0 < s → ∀ v ∈ Ioc (0 : ℝ) b,
      |a i v s - ∑ m ∈ Finset.range M₂, c i m s * v ^ m| ≤ Ha i s * v ^ M₂)
    (hremB : ∀ j, j < M₂ → ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |bj j u s - ∑ m ∈ Finset.range M₁, c m j s * u ^ m| ≤ Hb j s * u ^ M₁)
    (C L : ℝ) (D : ℕ) (hC : 0 ≤ C)
    (hmix : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |rectRem Φ a bj c M₁ M₂ u v s| ≤ C * (u ^ M₁ * v ^ M₂) * ((1 + s) ^ D * Real.exp (β * s * L)))
    (hmomA : ∀ i, i < M₁ → FaceMoments β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i)
      (fun m => c i m) (Ha i))
    (hmomB : ∀ j, j < M₂ → FaceMoments β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j)
      (fun m => c m j) (Hb j))
    (hmomC : ∀ i, i < M₁ → ∀ j, j < M₂ → FaceMoments β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i)
      k₁ k₂ (M₁ + k₁ * M₂) (fun _ s => c i j s) (cornerData (c i j)) (fun _ => 0)) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ Φ
        - ((∑ i ∈ Finset.range M₁,
              faceSum β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) N)
          + (∑ j ∈ Finset.range M₂,
              faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) N)
          - ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
              faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
                (fun _ s => c i j s) (cornerData (c i j)) N))
      =O[atTop] fun N : ℝ =>
        N ^ (-(min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  set E : ℝ := min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂) with hE
  have hE₁ : E ≤ p₁ + (M₁ : ℝ) / k₁ := min_le_left _ _
  have hE₂ : E ≤ p₂ + (M₂ : ℝ) / k₂ := min_le_right _ _
  -- the pieces
  set FA : ℕ → ℝ → ℝ := fun i N => twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s)
    - faceSum β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) N with hFA
  set FB : ℕ → ℝ → ℝ := fun j N => twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s)
    - faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) N with hFB
  set FC : ℕ → ℕ → ℝ → ℝ := fun i j N =>
    twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j))
    - faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
        (fun _ s => c i j s) (cornerData (c i j)) N with hFC
  set FR : ℝ → ℝ := fun N => twoDAmp β b N h₁ h₂ k₁ k₂ (rectRem Φ a bj c M₁ M₂) with hFR
  have hA : ∀ i ∈ Finset.range M₁,
      FA i =O[atTop] fun N : ℝ => N ^ (-E) * (1 + Real.log N) := by
    intro i hi
    simp only [hFA]
    have hcont : Continuous fun x : ℝ × ℝ × ℝ => a i x.2.1 x.2.2 :=
      (ha i).comp (continuous_snd)
    have heq : ∀ N, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s)
        = twoDAmp β b N h₂ (h₁ + i) k₂ k₁ (fun v _ s => a i v s) := by
      intro N
      rw [twoDAmp_pow_absorb, twoDAmp_swap β b N (h₁ + i) h₂ k₁ k₂ _ hcont]
    have hγ := uface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i
      (Finset.mem_range.1 hi)
    have hexp : (((h₁ + i : ℕ) : ℝ) + 1) / k₁
        + ((M₂ : ℝ) - ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1)) / k₂
        = p₂ + (M₂ : ℝ) / k₂ := by
      rw [← hp₂]; field_simp; ring
    have h := face_isBigO β b _ h₂ (h₁ + i) k₂ k₁ M₂ hβ hb hk₂ hk₁ rfl (a i) (ha i)
      (fun m => c i m) (fun m => (hc i m).measurable) (Ha i) (hHa i) (hHa0 i) hγ
      (hremA i (Finset.mem_range.1 hi)) (hmomA i (Finset.mem_range.1 hi))
    rw [hexp] at h
    exact (h.congr_left fun N => by rw [heq]).trans (isBigO_rpow_log_mono _ _ hE₂)
  have hB : ∀ j ∈ Finset.range M₂,
      FB j =O[atTop] fun N : ℝ => N ^ (-E) * (1 + Real.log N) := by
    intro j hj
    simp only [hFB]
    have heq : ∀ N, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s)
        = twoDAmp β b N h₁ (h₂ + j) k₁ k₂ (fun u _ s => bj j u s) := fun N =>
      twoDAmp_pow_absorb' β b N h₁ h₂ k₁ k₂ j (bj j)
    have hγ := vface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j
      (Finset.mem_range.1 hj)
    have hexp : (((h₂ + j : ℕ) : ℝ) + 1) / k₂
        + ((M₁ : ℝ) - ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1)) / k₁
        = p₁ + (M₁ : ℝ) / k₁ := by
      rw [← hp₁]; field_simp; ring
    have h := face_isBigO β b _ h₁ (h₂ + j) k₁ k₂ M₁ hβ hb hk₁ hk₂ rfl (bj j) (hb' j)
      (fun m => c m j) (fun m => (hc m j).measurable) (Hb j) (hHb j) (hHb0 j) hγ
      (hremB j (Finset.mem_range.1 hj)) (hmomB j (Finset.mem_range.1 hj))
    rw [hexp] at h
    exact (h.congr_left fun N => by rw [heq]).trans (isBigO_rpow_log_mono _ _ hE₁)
  have hCc : ∀ i ∈ Finset.range M₁, ∀ j ∈ Finset.range M₂,
      FC i j =O[atTop] fun N : ℝ => N ^ (-E) * (1 + Real.log N) := by
    intro i hi j hj
    simp only [hFC]
    have hM₂pos : 0 < M₂ := lt_of_le_of_lt (Nat.zero_le j) (Finset.mem_range.1 hj)
    have hMc : 0 < M₁ + k₁ * M₂ := by positivity
    have heq : ∀ N, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j))
        = twoDAmp β b N (h₁ + i) (h₂ + j) k₁ k₂ (fun _ _ s => c i j s) := fun N =>
      twoDAmp_corner β b N h₁ h₂ k₁ k₂ i j (c i j)
    have hγ : (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1
        < ((M₁ + k₁ * M₂ : ℕ) : ℝ) := by
      have h := corner_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ i j
        (Finset.mem_range.1 hj)
      push_cast at h ⊢
      have : (0 : ℝ) ≤ (k₁ : ℝ) * M₂ := by positivity
      linarith
    have hexp : (((h₂ + j : ℕ) : ℝ) + 1) / k₂
        + (((M₁ + k₁ * M₂ : ℕ) : ℝ)
          - ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)) / k₁
        = p₁ + ((M₁ : ℝ) + k₁ * M₂ + i) / k₁ := by
      rw [← hp₁]; push_cast; field_simp; ring
    have hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
        |(fun _ s => c i j s) u s - ∑ m ∈ Finset.range (M₁ + k₁ * M₂),
          cornerData (c i j) m s * u ^ m| ≤ (fun _ => (0 : ℝ)) s * u ^ (M₁ + k₁ * M₂) := by
      intro s _ u _
      simp only [cornerData_rem (c i j) _ hMc s u, abs_zero, zero_mul, le_refl]
    have h := face_isBigO β b _ (h₁ + i) (h₂ + j) k₁ k₂ (M₁ + k₁ * M₂) hβ hb hk₁ hk₂ rfl
      (fun _ s => c i j s) ((hc i j).comp continuous_snd) (cornerData (c i j))
      (cornerData_measurable (c i j) (hc i j).measurable) (fun _ => 0) measurable_const
      (fun _ => le_rfl) hγ hrem (hmomC i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj))
    rw [hexp] at h
    refine (h.congr_left fun N => by rw [heq]).trans (isBigO_rpow_log_mono _ _ ?_)
    have : (M₁ : ℝ) / k₁ ≤ ((M₁ : ℝ) + k₁ * M₂ + i) / k₁ := by
      apply div_le_div_of_nonneg_right _ hk₁'.le
      have : (0 : ℝ) ≤ k₁ * M₂ := by positivity
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    linarith
  have hR : FR =O[atTop] fun N : ℝ => N ^ (-E) * (1 + Real.log N) := by
    simp only [hFR]
    have h := twoDAmp_env_isBigO β b L C h₁ h₂ k₁ k₂ M₁ M₂ D (rectRem Φ a bj c M₁ M₂) hβ hb hk₁ hk₂
      hC (rectRem_continuous Φ a bj c M₁ M₂ hΦ ha hb' hc) hmix
    refine h.congr_right fun N => ?_
    congr 2
    rw [hE]
    have e1 : (((h₁ + M₁ : ℕ) : ℝ) + 1) / k₁ = p₁ + (M₁ : ℝ) / k₁ := by
      rw [← hp₁]; push_cast; field_simp; ring
    have e2 : (((h₂ + M₂ : ℕ) : ℝ) + 1) / k₂ = p₂ + (M₂ : ℝ) / k₂ := by
      rw [← hp₂]; push_cast; field_simp; ring
    rw [e1, e2]
  -- assemble
  have hfun : (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ Φ
        - ((∑ i ∈ Finset.range M₁,
              faceSum β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) N)
          + (∑ j ∈ Finset.range M₂,
              faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) N)
          - ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
              faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
                (fun _ s => c i j s) (cornerData (c i j)) N))
      = fun N : ℝ => (∑ i ∈ Finset.range M₁, FA i) N + (∑ j ∈ Finset.range M₂, FB j) N
          - (∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂, FC i j) N + FR N := by
    funext N
    simp only [Finset.sum_apply, hFA, hFB, hFC, hFR]
    rw [twoDAmp_rect β b N h₁ h₂ k₁ k₂ Φ a bj c M₁ M₂ hΦ ha hb' hc]
    simp only [Finset.sum_sub_distrib]
    ring
  rw [hfun]
  exact (((IsBigO.sum hA).add (IsBigO.sum hB)).sub
    (IsBigO.sum fun i hi => IsBigO.sum (hCc i hi))).add hR

/-- **The merged cutoff expansion of the `d = 2` block with unequal starting exponents.** -/
theorem twoD_cutoff_general_merged (β b p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁)
    (Φ : ℝ → ℝ → ℝ → ℝ) (a bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2)
    (ha : ∀ i, Continuous (Function.uncurry (a i)))
    (hb' : ∀ j, Continuous (Function.uncurry (bj j))) (hc : ∀ i j, Continuous (c i j))
    (Ha Hb : ℕ → ℝ → ℝ) (hHa : ∀ i, Measurable (Ha i)) (hHa0 : ∀ i s, 0 ≤ Ha i s)
    (hHb : ∀ j, Measurable (Hb j)) (hHb0 : ∀ j s, 0 ≤ Hb j s)
    (hremA : ∀ i, i < M₁ → ∀ s, 0 < s → ∀ v ∈ Ioc (0 : ℝ) b,
      |a i v s - ∑ m ∈ Finset.range M₂, c i m s * v ^ m| ≤ Ha i s * v ^ M₂)
    (hremB : ∀ j, j < M₂ → ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |bj j u s - ∑ m ∈ Finset.range M₁, c m j s * u ^ m| ≤ Hb j s * u ^ M₁)
    (C L : ℝ) (D : ℕ) (hC : 0 ≤ C)
    (hmix : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |rectRem Φ a bj c M₁ M₂ u v s| ≤ C * (u ^ M₁ * v ^ M₂) * ((1 + s) ^ D * Real.exp (β * s * L)))
    (hmomA : ∀ i, i < M₁ → FaceMoments β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i)
      (fun m => c i m) (Ha i))
    (hmomB : ∀ j, j < M₂ → FaceMoments β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j)
      (fun m => c m j) (Hb j))
    (hmomC : ∀ i, i < M₁ → ∀ j, j < M₂ → FaceMoments β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i)
      k₁ k₂ (M₁ + k₁ * M₂) (fun _ s => c i j s) (cornerData (c i j)) (fun _ => 0)) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ Φ - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N)
      =O[atTop] fun N : ℝ =>
        N ^ (-(min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have h := twoD_cutoff_general_isBigO β b p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hβ hb hk₁ hk₂ hp₁ hp₂ hM₁ hM₂
    Φ a bj c hΦ ha hb' hc Ha Hb hHa hHa0 hHb hHb0 hremA hremB C L D hC hmix hmomA hmomB hmomC
  refine h.congr_left fun N => ?_
  by_cases hM : M₁ = 0 ∨ M₂ = 0
  · -- degenerate: no corners, and the merged sum is the face sums
    have hz : ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
        faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
          (fun _ s => c i j s) (cornerData (c i j)) N = 0 := by
      rcases hM with h0 | h0 <;> simp [h0]
    rw [hz, sub_zero]
    have := overcomplete_eq_merged β b h₁ h₂ k₁ k₂ M₁ M₂ 1 hb hk₁ hk₂ one_pos a bj c N
    have hz' : ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
        faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ 1
          (fun _ s => c i j s) (cornerData (c i j)) N = 0 := by
      rcases hM with h0 | h0 <;> simp [h0]
    rw [hz', sub_zero] at this
    rw [this]
  · push Not at hM
    have hMc : 0 < M₁ + k₁ * M₂ := by
      have := Nat.pos_of_ne_zero hM.1
      omega
    rw [overcomplete_eq_merged β b h₁ h₂ k₁ k₂ M₁ M₂ (M₁ + k₁ * M₂) hb hk₁ hk₂ hMc a bj c N]

end Laplace.Grammar
