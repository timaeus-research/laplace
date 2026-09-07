/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MixedExplicit

/-!
# The `d = 2` cutoff expansion with an explicit remainder constant (grammar §4.2, Astra #9 R5)

Every step of the cutoff assembly is now quantitative for `N ≥ 1`:

* each face transfer has the explicit constant `faceConst` (an envelope moment plus tail moments
  of the face coefficients, from `face_transfer_bound`), `face_bound_explicit`;
* the mixed remainder has the constant of unit 130 (`twoDAmp_env_explicit`);
* a bound at a larger exponent is a bound at the target exponent for `N ≥ 1` (`bound_mono_exp`).

Summing the pieces gives `twoD_cutoff_general_explicit`:

  `∀ N ≥ 1, |Z(N) − mergedSum(N)| ≤ cutoffConst · N^{−E} (1 + log N)`,
  `E = min(p₁ + M₁/k₁, p₂ + M₂/k₂)`,

with `cutoffConst` the finite sum of the face, corner and mixed constants. Zero
`sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- A bound at exponent `q ≥ E` is a bound at exponent `E` for `N ≥ 1`. -/
theorem bound_mono_exp (X K q E N : ℝ) (hN : 1 ≤ N) (hqE : E ≤ q)
    (h : |X| ≤ K * N ^ (-q) * (1 + Real.log N)) : |X| ≤ K * N ^ (-E) * (1 + Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hA : 0 < N ^ (-q) * (1 + Real.log N) := by positivity
  have hK : 0 ≤ K := by
    have h0 : 0 * (N ^ (-q) * (1 + Real.log N)) ≤ K * (N ^ (-q) * (1 + Real.log N)) := by
      rw [zero_mul, ← mul_assoc]; exact (abs_nonneg X).trans h
    exact le_of_mul_le_mul_right h0 hA
  have hpow : N ^ (-q) ≤ N ^ (-E) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  calc |X| ≤ K * N ^ (-q) * (1 + Real.log N) := h
    _ ≤ K * N ^ (-E) * (1 + Real.log N) := by gcongr

/-- The explicit face transfer constant. -/
noncomputable def faceConst (β p₂ b : ℝ) (h₁ k₁ k₂ M : ℕ) (Ψ : ℝ → ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (H : ℝ → ℝ) : ℝ :=
  envMoment β (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁) 1
      (faceEnv ((k₁ : ℝ) * p₂ - h₁ - 1) (b ^ k₂) k₁ k₂ M H)
    + ∑ i, (b ^ (k₁ + k₂)) ^ (faceα p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ M i
        - (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁))
      * tailMoment β (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁) (faceJ M i)
        (faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M i)

/-- **The face transfer with its explicit constant**, for `N ≥ 1`. -/
theorem face_bound_explicit (β b p₂ : ℝ) (h₁ h₂ k₁ k₂ M : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) (f : ℕ → ℝ → ℝ) (hf : ∀ m, Measurable (f m))
    (H : ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ s, 0 ≤ H s) (hγ : (k₁ : ℝ) * p₂ - h₁ - 1 < M)
    (hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |Ψ u s - ∑ m ∈ Finset.range M, f m s * u ^ m| ≤ H s * u ^ M)
    (hmom : FaceMoments β p₂ b h₁ k₁ k₂ M Ψ f H) (N : ℝ) (hN : 1 ≤ N) :
    |twoDAmp β b N h₁ h₂ k₁ k₂ (fun u _ s => Ψ u s) - faceSum β p₂ b h₁ k₁ k₂ M Ψ f N|
      ≤ faceConst β p₂ b h₁ k₁ k₂ M Ψ f H
        * N ^ (-(p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁)) * (1 + Real.log N) := by
  have h := face_transfer_bound β b p₂ h₁ h₂ k₁ k₂ M hβ.le hb hk₁ hk₂ hp₂ Ψ hΨc f hf H hH hH0 hγ
    hrem hmom.hMc hmom.hMt hmom.hMH N hN
  rw [pow_one] at h
  unfold faceSum faceConst
  calc _ ≤ _ := h
    _ = _ := by ring

/-- The explicit cutoff constant: face, corner and mixed constants summed. -/
noncomputable def cutoffConst (β b L C : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ) (a bj : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℕ → ℝ → ℝ) (Ha Hb : ℕ → ℝ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range M₁,
      faceConst β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) (Ha i))
  + (∑ j ∈ Finset.range M₂,
      faceConst β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) (Hb j))
  + (∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
      faceConst β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
        (fun _ s => c i j s) (cornerData (c i j)) (fun _ => 0))
  + C * Real.exp ((D : ℝ) ^ 2 / β) * mixConst (β / 2) (2 * L) b (h₁ + M₁) (h₂ + M₂) k₁ k₂

/-- The over-complete sum equals the merged sum at the standard corner order (all `M₁, M₂`). -/
theorem overcomplete_eq_merged_std (β b : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (a bj : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℕ → ℝ → ℝ) (N : ℝ) :
    (∑ i ∈ Finset.range M₁,
        faceSum β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) N)
      + (∑ j ∈ Finset.range M₂,
          faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) N)
      - ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
          faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
            (fun _ s => c i j s) (cornerData (c i j)) N
      = mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N := by
  by_cases hM : M₁ = 0 ∨ M₂ = 0
  · have hz : ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
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
    exact this
  · push Not at hM
    have hMc : 0 < M₁ + k₁ * M₂ := by
      have := Nat.pos_of_ne_zero hM.1
      omega
    exact overcomplete_eq_merged β b h₁ h₂ k₁ k₂ M₁ M₂ (M₁ + k₁ * M₂) hb hk₁ hk₂ hMc a bj c N

/-- **The `d = 2` cutoff expansion with an explicit remainder constant**, for `N ≥ 1`. -/
theorem twoD_cutoff_general_explicit (β b p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hβ : 0 < β)
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
      k₁ k₂ (M₁ + k₁ * M₂) (fun _ s => c i j s) (cornerData (c i j)) (fun _ => 0))
    (N : ℝ) (hN : 1 ≤ N) :
    |twoDAmp β b N h₁ h₂ k₁ k₂ Φ - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N|
      ≤ cutoffConst β b L C h₁ h₂ k₁ k₂ M₁ M₂ D a bj c Ha Hb
        * N ^ (-(min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hN0 : 0 < N := by linarith
  set E : ℝ := min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂) with hE
  have hE₁ : E ≤ p₁ + (M₁ : ℝ) / k₁ := min_le_left _ _
  have hE₂ : E ≤ p₂ + (M₂ : ℝ) / k₂ := min_le_right _ _
  set A : ℝ := N ^ (-E) * (1 + Real.log N) with hAdef
  -- the pieces
  set FA : ℕ → ℝ := fun i => twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s)
    - faceSum β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) N with hFA
  set FB : ℕ → ℝ := fun j => twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s)
    - faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) N with hFB
  set FC : ℕ → ℕ → ℝ := fun i j =>
    twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j))
    - faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
        (fun _ s => c i j s) (cornerData (c i j)) N with hFC
  set FR : ℝ := twoDAmp β b N h₁ h₂ k₁ k₂ (rectRem Φ a bj c M₁ M₂) with hFR
  -- the face bounds
  have hA : ∀ i ∈ Finset.range M₁, |FA i|
      ≤ faceConst β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) (Ha i)
        * A := by
    intro i hi
    simp only [hFA]
    have hcont : Continuous fun x : ℝ × ℝ × ℝ => a i x.2.1 x.2.2 :=
      (ha i).comp (continuous_snd)
    have heq : twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s)
        = twoDAmp β b N h₂ (h₁ + i) k₂ k₁ (fun v _ s => a i v s) := by
      rw [twoDAmp_pow_absorb, twoDAmp_swap β b N (h₁ + i) h₂ k₁ k₂ _ hcont]
    have hγ := uface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i
      (Finset.mem_range.1 hi)
    have hexp : (((h₁ + i : ℕ) : ℝ) + 1) / k₁
        + ((M₂ : ℝ) - ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1)) / k₂
        = p₂ + (M₂ : ℝ) / k₂ := by
      rw [← hp₂]; field_simp; ring
    have h := face_bound_explicit β b _ h₂ (h₁ + i) k₂ k₁ M₂ hβ hb hk₂ hk₁ rfl (a i) (ha i)
      (fun m => c i m) (fun m => (hc i m).measurable) (Ha i) (hHa i) (hHa0 i) hγ
      (hremA i (Finset.mem_range.1 hi)) (hmomA i (Finset.mem_range.1 hi)) N hN
    rw [hexp] at h
    rw [heq, hAdef, ← mul_assoc]
    exact bound_mono_exp _ _ _ E N hN hE₂ h
  have hB : ∀ j ∈ Finset.range M₂, |FB j|
      ≤ faceConst β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) (Hb j)
        * A := by
    intro j hj
    simp only [hFB]
    have heq : twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s)
        = twoDAmp β b N h₁ (h₂ + j) k₁ k₂ (fun u _ s => bj j u s) :=
      twoDAmp_pow_absorb' β b N h₁ h₂ k₁ k₂ j (bj j)
    have hγ := vface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j
      (Finset.mem_range.1 hj)
    have hexp : (((h₂ + j : ℕ) : ℝ) + 1) / k₂
        + ((M₁ : ℝ) - ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1)) / k₁
        = p₁ + (M₁ : ℝ) / k₁ := by
      rw [← hp₁]; field_simp; ring
    have h := face_bound_explicit β b _ h₁ (h₂ + j) k₁ k₂ M₁ hβ hb hk₁ hk₂ rfl (bj j) (hb' j)
      (fun m => c m j) (fun m => (hc m j).measurable) (Hb j) (hHb j) (hHb0 j) hγ
      (hremB j (Finset.mem_range.1 hj)) (hmomB j (Finset.mem_range.1 hj)) N hN
    rw [hexp] at h
    rw [heq, hAdef, ← mul_assoc]
    exact bound_mono_exp _ _ _ E N hN hE₁ h
  have hCc : ∀ i ∈ Finset.range M₁, ∀ j ∈ Finset.range M₂, |FC i j|
      ≤ faceConst β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
          (fun _ s => c i j s) (cornerData (c i j)) (fun _ => 0) * A := by
    intro i hi j hj
    simp only [hFC]
    have hM₂pos : 0 < M₂ := lt_of_le_of_lt (Nat.zero_le j) (Finset.mem_range.1 hj)
    have hMc : 0 < M₁ + k₁ * M₂ := by positivity
    have heq : twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j))
        = twoDAmp β b N (h₁ + i) (h₂ + j) k₁ k₂ (fun _ _ s => c i j s) :=
      twoDAmp_corner β b N h₁ h₂ k₁ k₂ i j (c i j)
    have hγ := corner_gamma_lt_general' p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ i j hk₁ hk₂ hp₁ hp₂ hM₂
      (Finset.mem_range.1 hj)
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
    have h := face_bound_explicit β b _ (h₁ + i) (h₂ + j) k₁ k₂ (M₁ + k₁ * M₂) hβ hb hk₁ hk₂ rfl
      (fun _ s => c i j s) ((hc i j).comp continuous_snd) (cornerData (c i j))
      (cornerData_measurable (c i j) (hc i j).measurable) (fun _ => 0) measurable_const
      (fun _ => le_rfl) hγ hrem (hmomC i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj)) N hN
    rw [hexp] at h
    rw [heq, hAdef, ← mul_assoc]
    refine bound_mono_exp _ _ _ E N hN ?_ h
    have : (M₁ : ℝ) / k₁ ≤ ((M₁ : ℝ) + k₁ * M₂ + i) / k₁ := by
      apply div_le_div_of_nonneg_right _ hk₁'.le
      have : (0 : ℝ) ≤ k₁ * M₂ := by positivity
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    linarith
  have hR : |FR| ≤ C * Real.exp ((D : ℝ) ^ 2 / β)
      * mixConst (β / 2) (2 * L) b (h₁ + M₁) (h₂ + M₂) k₁ k₂ * A := by
    simp only [hFR]
    have h := twoDAmp_env_explicit β b L C N h₁ h₂ k₁ k₂ M₁ M₂ D (rectRem Φ a bj c M₁ M₂) hβ hb hk₁
      hk₂ hC hN (rectRem_continuous Φ a bj c M₁ M₂ hΦ ha hb' hc) hmix
    have e1 : (((h₁ + M₁ : ℕ) : ℝ) + 1) / k₁ = p₁ + (M₁ : ℝ) / k₁ := by
      rw [← hp₁]; push_cast; field_simp; ring
    have e2 : (((h₂ + M₂ : ℕ) : ℝ) + 1) / k₂ = p₂ + (M₂ : ℝ) / k₂ := by
      rw [← hp₂]; push_cast; field_simp; ring
    rw [e1, e2, ← hE] at h
    rw [hAdef, ← mul_assoc]
    exact h
  -- the decomposition
  have hdec : twoDAmp β b N h₁ h₂ k₁ k₂ Φ - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ a bj c N
      = (∑ i ∈ Finset.range M₁, FA i) + (∑ j ∈ Finset.range M₂, FB j)
        - (∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂, FC i j) + FR := by
    rw [← overcomplete_eq_merged_std β b h₁ h₂ k₁ k₂ M₁ M₂ hb hk₁ hk₂ a bj c N,
      twoDAmp_rect β b N h₁ h₂ k₁ k₂ Φ a bj c M₁ M₂ hΦ ha hb' hc]
    simp only [hFA, hFB, hFC, hFR, Finset.sum_sub_distrib]
    ring
  rw [hdec]
  have hsumA : |∑ i ∈ Finset.range M₁, FA i| ≤ (∑ i ∈ Finset.range M₁,
      faceConst β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) (Ha i))
        * A := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hA)
  have hsumB : |∑ j ∈ Finset.range M₂, FB j| ≤ (∑ j ∈ Finset.range M₂,
      faceConst β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) (Hb j))
        * A := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hB)
  have hsumC : |∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂, FC i j|
      ≤ (∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
          faceConst β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
            (fun _ s => c i j s) (cornerData (c i j)) (fun _ => 0)) * A := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (hCc i hi))
  unfold cutoffConst
  rw [mul_assoc, ← hAdef]
  calc |(∑ i ∈ Finset.range M₁, FA i) + (∑ j ∈ Finset.range M₂, FB j)
        - (∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂, FC i j) + FR|
      ≤ |∑ i ∈ Finset.range M₁, FA i| + |∑ j ∈ Finset.range M₂, FB j|
        + |∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂, FC i j| + |FR| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ _ := by
        have := add_le_add (add_le_add (add_le_add hsumA hsumB) hsumC) hR
        calc _ ≤ _ := this
          _ = _ := by ring

end Laplace.Grammar
