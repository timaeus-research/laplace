/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.JetRecursion

/-!
# The reduced form of the `d = 2` cutoff expansion (grammar §4.2, higher-order `d = 2`)

The cutoff theorem of unit 107 lists the transferred terms of all faces and corners. The monomial
terms cancel exactly against the corner terms (Astra #5(a)): the `m = j` monomial coefficient of the
`u`-face `i` equals the finite-part coefficient of the corner `(i, j)`, and the `m = i` monomial
coefficient of the `v`-face `j` equals the monomial coefficient of the corner
(`uface_coeff_eq_corner_fp`, `vface_coeff_eq_corner_coeff`, as functions of `s`, with equal
exponents). What remains is the reduced sum

  `∑_i N^{-(p+i/k₁)} M[k₁⁻¹ FP_{k₂i/k₁}(a_i)] + ∑_j N^{-(p+j/k₂)} M[k₂⁻¹ FP_{k₁j/k₂}(b_j)]`
  `+ (log terms of the u-faces) + (log terms of the v-faces) − (log terms of the corners)`,

and `twoD_cutoff_reduced_isBigO` restates unit 107 with it. The three log families combine to a
single copy at each collision; that final simplification is left as a separate lemma.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- A sum weighted by the Taylor data of a constant amplitude has only its `m = 0` term. -/
theorem cornerData_sum (c : ℝ → ℝ) (g : ℕ → ℝ) (M : ℕ) (hM : 0 < M) (s : ℝ) :
    ∑ m ∈ Finset.range M, cornerData c m s * g m = c s * g 0 := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun m _ => by simp [cornerData]]
  simp [cornerData]

/-- The monomial coefficients of a corner vanish for `m ≥ 1`. -/
theorem faceCoeff_cornerData_succ (γ A : ℝ) (k₁ k₂ : ℕ) (c : ℝ → ℝ) (m : ℕ) :
    faceCoeff γ A k₁ k₂ (cornerData c) (m + 1) = fun _ => 0 := by
  funext s
  simp only [faceCoeff, cornerData, Nat.succ_ne_zero, if_false, mul_zero, ite_self]

/-- The finite-part coefficient of a corner: `k₂⁻¹ c · axisPrim γ b 0`. -/
theorem faceFPCoeff_corner (γ b : ℝ) (k₂ : ℕ) (c : ℝ → ℝ) (M : ℕ) (hM : 0 < M) (s : ℝ) :
    faceFPCoeff γ b k₂ (fun _ s => c s) (cornerData c) M s
      = 1 / (k₂ : ℝ) * (c s * axisPrim γ b 0) := by
  unfold faceFPCoeff axisFinitePart regAxisIntegral
  have h0 : ∀ v, taylorRem (fun _ => c s) (fun m => cornerData c m s) M v = 0 := fun v =>
    cornerData_rem c M hM s v
  simp only [h0, mul_zero, integral_zero, zero_add]
  rw [cornerData_sum c (fun m => axisPrim γ b m) M hM s]

/-- **Cancellation (u-face vs corner)**: the `m = j` monomial coefficient of the `u`-face `i`
equals the finite-part coefficient of the corner `(i, j)`. -/
theorem uface_coeff_eq_corner_fp (b p : ℝ) (h₁ h₂ k₁ k₂ i j Mc : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hMc : 0 < Mc) (c : ℕ → ℕ → ℝ → ℝ) :
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
  have e1 : (h₁ : ℝ) + 1 = k₁ * p := by rw [← hp₁]; field_simp
  have e2 : (h₂ : ℝ) + 1 = k₂ * p := by rw [← hp₂]; field_simp
  have hγu' : γu = (k₂ : ℝ) * i / k₁ := by
    rw [hγu]; push_cast
    rw [show (h₁ : ℝ) + i + 1 = ((h₁ : ℝ) + 1) + i by ring, e1,
      show (k₂ : ℝ) * ((k₁ * p + i) / k₁) - h₂ - 1 = (k₂ : ℝ) * ((k₁ * p + i) / k₁) - (h₂ + 1)
        by ring, e2]
    field_simp
    ring
  have hγc' : γc = (k₁ : ℝ) * j / k₂ - i := by
    rw [hγc]; push_cast
    rw [show (h₂ : ℝ) + j + 1 = ((h₂ : ℝ) + 1) + j by ring, e2,
      show (k₁ : ℝ) * ((k₂ * p + j) / k₂) - (h₁ + i) - 1
        = (k₁ : ℝ) * ((k₂ * p + j) / k₂) - (h₁ + 1) - i by ring, e1]
    field_simp
    ring
  unfold faceCoeff axisPrim
  have hiff : ((j : ℝ) = γu) ↔ (((0 : ℕ) : ℝ) = γc) := by
    rw [hγu', hγc']
    push_cast
    constructor
    · intro h
      field_simp at h ⊢
      linarith
    · intro h
      field_simp at h ⊢
      linarith
  by_cases h : (j : ℝ) = γu
  · rw [if_pos h, if_pos (hiff.1 h), Real.log_pow]
    push_cast
    field_simp
    try ring
  · have h' : ¬ (((0 : ℕ) : ℝ) = γc) := fun h' => h (hiff.2 h')
    rw [if_neg h, if_neg h']
    have hne : (k₁ : ℝ) * j - k₂ * i ≠ 0 := by
      intro h0
      apply h
      rw [hγu']
      field_simp
      linarith
    have hne2 : -((k₁ : ℝ) * j) + k₂ * i ≠ 0 := by
      intro h0; apply hne; linarith
    have hpow : ((b : ℝ) ^ k₁) ^ (-(((j : ℝ) - γu) / k₂)) = b ^ (((0 : ℕ) : ℝ) - γc) := by
      rw [← Real.rpow_natCast b k₁, ← Real.rpow_mul hb.le]
      congr 1
      rw [hγu', hγc']
      push_cast
      field_simp
      ring
    rw [hpow, hγu', hγc']
    push_cast
    have d1 : (j : ℝ) - (k₂ : ℝ) * i / k₁ = ((k₁ : ℝ) * j - k₂ * i) / k₁ := by
      field_simp
    have d2 : (0 : ℝ) - ((k₁ : ℝ) * j / k₂ - i) = -((k₁ : ℝ) * j - k₂ * i) / k₂ := by
      field_simp
      ring
    rw [d1, d2]
    field_simp

/-- **Cancellation (v-face vs corner)**: the `m = i` monomial coefficient of the `v`-face `j`
equals the `m = 0` monomial coefficient of the corner `(i, j)`. -/
theorem vface_coeff_eq_corner_coeff (b : ℝ) (h₁ h₂ k₁ k₂ i j : ℕ) (c : ℕ → ℕ → ℝ → ℝ) :
    faceCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1) (b ^ k₂) k₁ k₂
        (fun m => c m j) i
      = faceCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) (b ^ k₂)
        k₁ k₂ (cornerData (c i j)) 0 := by
  funext s
  unfold faceCoeff cornerData
  simp only [if_true]
  have hiff : ((i : ℝ) = (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1)
      ↔ (((0 : ℕ) : ℝ) = (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) := by
    push_cast
    constructor <;> intro h <;> linarith
  by_cases h : (i : ℝ) = (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]
    push_cast
    congr 2
    · congr 1
      ring
    · ring

/-- The `u`-face monomial exponent `m = j` is the corner exponent `p + j/k₂`. -/
theorem uface_exp_eq (p : ℝ) (h₁ h₂ k₁ k₂ i j : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) :
    faceExp ((((h₁ + i : ℕ) : ℝ) + 1) / k₁)
        ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) k₂ j
      = (((h₂ + j : ℕ) : ℝ) + 1) / k₂ := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  unfold faceExp
  have e1 : (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = p + (i : ℝ) / k₁ := by
    rw [← hp₁]; push_cast; field_simp; ring
  have e2 : (((h₂ + j : ℕ) : ℝ) + 1) / k₂ = p + (j : ℝ) / k₂ := by
    rw [← hp₂]; push_cast; field_simp; ring
  rw [e1, e2, ← hp₂]
  field_simp
  ring

/-- The `v`-face monomial exponent `m = i` is the corner monomial exponent `m = 0`. -/
theorem vface_exp_eq (h₁ h₂ k₁ k₂ i j : ℕ) :
    faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
        ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1) k₁ i
      = faceExp ((((h₂ + j : ℕ) : ℝ) + 1) / k₂)
        ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ 0 := by
  unfold faceExp
  push_cast
  ring

/-- The reduced transferred sum: face finite parts and the three log families. -/
noncomputable def reducedSum (β b : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (a bj : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) : ℝ :=
  (∑ i ∈ Finset.range M₁, N ^ (-((((h₁ + i : ℕ) : ℝ) + 1) / k₁))
      * logMoment β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) 0
        (faceFPCoeff ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) b k₁ (a i)
          (fun m => c i m) M₂))
  + (∑ j ∈ Finset.range M₂, N ^ (-((((h₂ + j : ℕ) : ℝ) + 1) / k₂))
      * logMoment β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 0
        (faceFPCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1) b k₂ (bj j)
          (fun m => c m j) M₁))
  + (∑ i ∈ Finset.range M₁, transferTerm β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) 1
      (faceLogCoeff ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1) k₂ k₁
        (fun m => c i m) M₂) N)
  + (∑ j ∈ Finset.range M₂, transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
      (faceLogCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1) k₁ k₂
        (fun m => c m j) M₁) N)
  - ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
      transferTerm β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) 1
        (faceLogCoeff ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1) k₁ k₂
          (cornerData (c i j)) (M₁ + k₁ * M₂)) N

/-- **The over-complete sum equals the reduced sum** (exact, for every `N`). -/
theorem overcomplete_eq_reduced (β b p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (a bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) :
    (∑ i ∈ Finset.range M₁,
        faceSum β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) N)
      + (∑ j ∈ Finset.range M₂,
          faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) N)
      - ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
          faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
            (fun _ s => c i j s) (cornerData (c i j)) N
      = reducedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  set Mc : ℕ := M₁ + k₁ * M₂ with hMc
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
    have hM₂ : 0 < M₂ := Fin.pos j
    have hMc0 : 0 < Mc := by positivity
    rw [uface_exp_eq p h₁ h₂ k₁ k₂ i j hk₁ hk₂ hp₁ hp₂,
      uface_coeff_eq_corner_fp b p h₁ h₂ k₁ k₂ i j Mc hb hk₁ hk₂ hp₁ hp₂ hMc0 c]
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
    intro i _ j hj
    have hM₂ : 0 < M₂ := lt_of_le_of_lt (Nat.zero_le j) (Finset.mem_range.1 hj)
    have hMc0 : 0 < Mc := by positivity
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
  unfold reducedSum
  simp only [Finset.sum_add_distrib]
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

/-- **The reduced cutoff expansion of the `d = 2` block.** -/
theorem twoD_cutoff_reduced_isBigO (β b p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁)
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
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ Φ - reducedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N)
      =O[atTop] fun N : ℝ =>
        N ^ (-(p + min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have h := twoD_cutoff_isBigO β b p h₁ h₂ k₁ k₂ M₁ M₂ hβ hb hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ Φ a bj c hΦ
    ha hb' hc Ha Hb hHa hHa0 hHb hHb0 hremA hremB C L D hC hmix hmomA hmomB hmomC
  refine h.congr_left fun N => ?_
  rw [overcomplete_eq_reduced β b p h₁ h₂ k₁ k₂ M₁ M₂ hb hk₁ hk₂ hp₁ hp₂ a bj c N]

end Laplace.Grammar
