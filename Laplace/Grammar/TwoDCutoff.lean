/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.RectDecomp

/-!
# The cutoff-indexed expansion of the `d = 2` block (grammar §4.2, higher-order `d = 2`)

Assembly of units 104–106. For the equal-exponent block `(h₁+1)/k₁ = (h₂+1)/k₂ = p` with a general
amplitude `Φ(u, v, s)` admitting compatible face jets `a_i(v, s)`, `b_j(u, s)` and corner jets
`c_{ij}(s)` (truncation lengths `M₁, M₂` with `(M₁−1)/k₁ < M₂/k₂` and `(M₂−1)/k₂ < M₁/k₁`) and a
mixed remainder `|R| ≤ C u^{M₁} v^{M₂} (1+s)^D e^{βsL}`,

  `Z_Φ(N) = ∑_{i<M₁} S_{a_i}(N) + ∑_{j<M₂} S_{b_j}(N) − ∑_{ij} S_{c_{ij}}(N)
            + O(N^{-(p + min(M₁/k₁, M₂/k₂))} (1 + log N))`,

where each `S` is the explicit finite sum of transferred terms of a face expansion (`faceSum`):
powers `N^{-(p+m/k)}` with a logarithm exactly at the collisions `i/k₁ = m/k₂`. This is the
`τ`-cutoff theorem of Astra #4(b) with `τ = min(M₁/k₁, M₂/k₂)`, in the form "all terms listed, some
below the remainder order". Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- The moment hypotheses of the face transfer, bundled. -/
structure FaceMoments (β p₂ b : ℝ) (h₁ k₁ k₂ M : ℕ) (Ψ : ℝ → ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (H : ℝ → ℝ) : Prop where
  hMc : ∀ i, IntegrableOn (fun s => s ^ (faceα p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ M i - 1)
    * (1 + |Real.log s|) ^ faceJ M i
    * (Real.exp (-β * s ^ 2) * |faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M i s|)) (Ioi 0)
  hMt : ∀ i, IntegrableOn (fun s => s ^ (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁ - 1)
    * (1 + |Real.log s|) ^ faceJ M i
    * (Real.exp (-β * s ^ 2) * |faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M i s|)) (Ioi 0)
  hMH : IntegrableOn (fun s => s ^ (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁ - 1)
    * (1 + |Real.log s|) ^ 1
    * (Real.exp (-β * s ^ 2) * faceEnv ((k₁ : ℝ) * p₂ - h₁ - 1) (b ^ k₂) k₁ k₂ M H s)) (Ioi 0)

/-- The transferred sum of a face expansion. -/
noncomputable def faceSum (β p₂ b : ℝ) (h₁ k₁ k₂ M : ℕ) (Ψ : ℝ → ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (N : ℝ) : ℝ :=
  ∑ i, transferTerm β (faceα p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ M i) (faceJ M i)
    (faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M i) N

/-- The face-term expansion as an `IsBigO` statement. -/
theorem face_isBigO (β b p₂ : ℝ) (h₁ h₂ k₁ k₂ M : ℕ) (hβ : 0 < β) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) (f : ℕ → ℝ → ℝ) (hf : ∀ m, Measurable (f m))
    (H : ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ s, 0 ≤ H s) (hγ : (k₁ : ℝ) * p₂ - h₁ - 1 < M)
    (hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |Ψ u s - ∑ m ∈ Finset.range M, f m s * u ^ m| ≤ H s * u ^ M)
    (hmom : FaceMoments β p₂ b h₁ k₁ k₂ M Ψ f H) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (fun u _ s => Ψ u s) - faceSum β p₂ b h₁ k₁ k₂ M Ψ f N)
      =O[atTop] fun N : ℝ =>
        N ^ (-(p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁)) * (1 + Real.log N) := by
  refine IsBigO.of_bound (envMoment β (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁) 1
      (faceEnv ((k₁ : ℝ) * p₂ - h₁ - 1) (b ^ k₂) k₁ k₂ M H)
    + ∑ i, (b ^ (k₁ + k₂)) ^ (faceα p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ M i
        - (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁))
      * tailMoment β (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁) (faceJ M i)
        (faceC ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ Ψ f M i)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have h := face_transfer_bound β b p₂ h₁ h₂ k₁ k₂ M hβ.le hb hk₁ hk₂ hp₂ Ψ hΨc f hf H hH hH0 hγ
    hrem hmom.hMc hmom.hMt hmom.hMH N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) hlog)]
  unfold faceSum
  rw [pow_one] at h
  linarith [h]

/-- Monotonicity of the remainder scale in the exponent. -/
theorem isBigO_rpow_log_mono (a a' : ℝ) (h : a' ≤ a) :
    (fun N : ℝ => N ^ (-a) * (1 + Real.log N)) =O[atTop]
      fun N : ℝ => N ^ (-a') * (1 + Real.log N) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) hlog),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) hlog)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hlog

/-- The Taylor data of a constant amplitude. -/
def cornerData (c : ℝ → ℝ) (m : ℕ) (s : ℝ) : ℝ := if m = 0 then c s else 0

theorem cornerData_measurable (c : ℝ → ℝ) (hc : Measurable c) (m : ℕ) :
    Measurable (cornerData c m) := by
  unfold cornerData
  split_ifs
  · exact hc
  · exact measurable_const

theorem cornerData_rem (c : ℝ → ℝ) (M : ℕ) (hM : 0 < M) (s u : ℝ) :
    c s - ∑ m ∈ Finset.range M, cornerData c m s * u ^ m = 0 := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun m _ => by simp [cornerData]]
  simp [cornerData]

/-- **The cutoff-indexed expansion of the `d = 2` equal-exponent block.** -/
theorem twoD_cutoff_isBigO (β b p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
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
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ Φ
        - ((∑ i ∈ Finset.range M₁,
              faceSum β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂ (a i) (fun m => c i m) N)
          + (∑ j ∈ Finset.range M₂,
              faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁ (bj j) (fun m => c m j) N)
          - ∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
              faceSum β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
                (fun _ s => c i j s) (cornerData (c i j)) N))
      =O[atTop] fun N : ℝ =>
        N ^ (-(p + min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  set τ : ℝ := min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂) with hτ
  have hτ₁ : τ ≤ (M₁ : ℝ) / k₁ := min_le_left _ _
  have hτ₂ : τ ≤ (M₂ : ℝ) / k₂ := min_le_right _ _
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
      FA i =O[atTop] fun N : ℝ => N ^ (-(p + τ)) * (1 + Real.log N) := by
    intro i hi
    simp only [hFA]
    have hi' : (i : ℝ) < M₁ := by exact_mod_cast Finset.mem_range.1 hi
    have hcont : Continuous fun x : ℝ × ℝ × ℝ => a i x.2.1 x.2.2 :=
      (ha i).comp (continuous_snd)
    have heq : ∀ N, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => u ^ i * a i v s)
        = twoDAmp β b N h₂ (h₁ + i) k₂ k₁ (fun v _ s => a i v s) := by
      intro N
      rw [twoDAmp_pow_absorb, twoDAmp_swap β b N (h₁ + i) h₂ k₁ k₂ _ hcont]
    set p₂ : ℝ := (((h₁ + i : ℕ) : ℝ) + 1) / k₁ with hp₂'
    have hp₂p : p₂ = p + (i : ℝ) / k₁ := by
      rw [hp₂', ← hp₁]; push_cast; field_simp; ring
    have hγ : (k₂ : ℝ) * p₂ - h₂ - 1 < M₂ := by
      have : (k₂ : ℝ) * p₂ - h₂ - 1 = (k₂ : ℝ) * i / k₁ := by
        rw [hp₂p, ← hp₂]; field_simp; ring
      rw [this]
      have hi1 : i + 1 ≤ M₁ := Finset.mem_range.1 hi
      have hi1' : (i : ℝ) + 1 ≤ M₁ := by exact_mod_cast hi1
      have h2 : (k₂ : ℝ) * i / k₁ ≤ (k₂ : ℝ) * ((M₁ - 1) / k₁) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hk₁').2 (by linarith)) hk₂'.le
      have h3 : (k₂ : ℝ) * ((M₁ - 1) / k₁) < (k₂ : ℝ) * ((M₂ : ℝ) / k₂) :=
        mul_lt_mul_of_pos_left hM₁ hk₂'
      rw [mul_div_cancel₀ _ hk₂'.ne'] at h3
      linarith
    have hexp : p₂ + ((M₂ : ℝ) - ((k₂ : ℝ) * p₂ - h₂ - 1)) / k₂ = p + (M₂ : ℝ) / k₂ := by
      rw [← hp₂]; field_simp; ring
    have h := face_isBigO β b p₂ h₂ (h₁ + i) k₂ k₁ M₂ hβ hb hk₂ hk₁ rfl (a i) (ha i)
      (fun m => c i m) (fun m => (hc i m).measurable) (Ha i) (hHa i) (hHa0 i) hγ
      (hremA i (Finset.mem_range.1 hi)) (hmomA i (Finset.mem_range.1 hi))
    rw [hexp] at h
    refine (h.congr_left fun N => by rw [heq]).trans (isBigO_rpow_log_mono _ _ ?_)
    linarith
  have hB : ∀ j ∈ Finset.range M₂,
      FB j =O[atTop] fun N : ℝ => N ^ (-(p + τ)) * (1 + Real.log N) := by
    intro j hj
    simp only [hFB]
    have hj' : (j : ℝ) < M₂ := by exact_mod_cast Finset.mem_range.1 hj
    have heq : ∀ N, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => v ^ j * bj j u s)
        = twoDAmp β b N h₁ (h₂ + j) k₁ k₂ (fun u _ s => bj j u s) := fun N =>
      twoDAmp_pow_absorb' β b N h₁ h₂ k₁ k₂ j (bj j)
    set p₂ : ℝ := (((h₂ + j : ℕ) : ℝ) + 1) / k₂ with hp₂'
    have hp₂p : p₂ = p + (j : ℝ) / k₂ := by
      rw [hp₂', ← hp₂]; push_cast; field_simp; ring
    have hγ : (k₁ : ℝ) * p₂ - h₁ - 1 < M₁ := by
      have : (k₁ : ℝ) * p₂ - h₁ - 1 = (k₁ : ℝ) * j / k₂ := by
        rw [hp₂p, ← hp₁]; field_simp; ring
      rw [this]
      have hj1 : j + 1 ≤ M₂ := Finset.mem_range.1 hj
      have hj1' : (j : ℝ) + 1 ≤ M₂ := by exact_mod_cast hj1
      have h2 : (k₁ : ℝ) * j / k₂ ≤ (k₁ : ℝ) * ((M₂ - 1) / k₂) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hk₂').2 (by linarith)) hk₁'.le
      have h3 : (k₁ : ℝ) * ((M₂ - 1) / k₂) < (k₁ : ℝ) * ((M₁ : ℝ) / k₁) :=
        mul_lt_mul_of_pos_left hM₂ hk₁'
      rw [mul_div_cancel₀ _ hk₁'.ne'] at h3
      linarith
    have hexp : p₂ + ((M₁ : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁ = p + (M₁ : ℝ) / k₁ := by
      rw [← hp₁]; field_simp; ring
    have h := face_isBigO β b p₂ h₁ (h₂ + j) k₁ k₂ M₁ hβ hb hk₁ hk₂ rfl (bj j) (hb' j)
      (fun m => c m j) (fun m => (hc m j).measurable) (Hb j) (hHb j) (hHb0 j) hγ
      (hremB j (Finset.mem_range.1 hj)) (hmomB j (Finset.mem_range.1 hj))
    rw [hexp] at h
    refine (h.congr_left fun N => by rw [heq]).trans (isBigO_rpow_log_mono _ _ ?_)
    linarith
  have hCc : ∀ i ∈ Finset.range M₁, ∀ j ∈ Finset.range M₂,
      FC i j =O[atTop] fun N : ℝ => N ^ (-(p + τ)) * (1 + Real.log N) := by
    intro i hi j hj
    simp only [hFC]
    have hi' : (i : ℝ) < M₁ := by exact_mod_cast Finset.mem_range.1 hi
    have hj' : (j : ℝ) < M₂ := by exact_mod_cast Finset.mem_range.1 hj
    have hM₂pos : 0 < M₂ := lt_of_le_of_lt (Nat.zero_le j) (Finset.mem_range.1 hj)
    have hMc : 0 < M₁ + k₁ * M₂ := by positivity
    have heq : ∀ N, twoDAmp β b N h₁ h₂ k₁ k₂ (fun u v s => c i j s * (u ^ i * v ^ j))
        = twoDAmp β b N (h₁ + i) (h₂ + j) k₁ k₂ (fun _ _ s => c i j s) := fun N =>
      twoDAmp_corner β b N h₁ h₂ k₁ k₂ i j (c i j)
    set p₂ : ℝ := (((h₂ + j : ℕ) : ℝ) + 1) / k₂ with hp₂'
    have hp₂p : p₂ = p + (j : ℝ) / k₂ := by
      rw [hp₂', ← hp₂]; push_cast; field_simp; ring
    have hγ : (k₁ : ℝ) * p₂ - ((h₁ + i : ℕ) : ℝ) - 1 < ((M₁ + k₁ * M₂ : ℕ) : ℝ) := by
      have : (k₁ : ℝ) * p₂ - ((h₁ + i : ℕ) : ℝ) - 1 = (k₁ : ℝ) * j / k₂ - i := by
        rw [hp₂p, ← hp₁]; push_cast; field_simp; ring
      rw [this]
      push_cast
      have h1 : (k₁ : ℝ) * j / k₂ ≤ (k₁ : ℝ) * j := by
        rw [div_le_iff₀ hk₂']
        have : (1 : ℝ) ≤ k₂ := by exact_mod_cast hk₂
        nlinarith [mul_nonneg hk₁'.le (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have h2 : (k₁ : ℝ) * j < (k₁ : ℝ) * M₂ := mul_lt_mul_of_pos_left hj' hk₁'
      have h3 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have h4 : (0 : ℝ) ≤ M₁ := Nat.cast_nonneg M₁
      linarith
    have hexp : p₂ + (((M₁ + k₁ * M₂ : ℕ) : ℝ) - ((k₁ : ℝ) * p₂ - ((h₁ + i : ℕ) : ℝ) - 1)) / k₁
        = p + ((M₁ : ℝ) + k₁ * M₂ + i) / k₁ := by
      rw [← hp₁]; push_cast; field_simp; ring
    have hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
        |(fun _ s => c i j s) u s - ∑ m ∈ Finset.range (M₁ + k₁ * M₂),
          cornerData (c i j) m s * u ^ m| ≤ (fun _ => (0 : ℝ)) s * u ^ (M₁ + k₁ * M₂) := by
      intro s _ u _
      simp only [cornerData_rem (c i j) _ hMc s u, abs_zero, zero_mul, le_refl]
    have h := face_isBigO β b p₂ (h₁ + i) (h₂ + j) k₁ k₂ (M₁ + k₁ * M₂) hβ hb hk₁ hk₂ rfl
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
  have hR : FR =O[atTop] fun N : ℝ => N ^ (-(p + τ)) * (1 + Real.log N) := by
    simp only [hFR]
    have h := twoDAmp_env_isBigO β b L C h₁ h₂ k₁ k₂ M₁ M₂ D (rectRem Φ a bj c M₁ M₂) hβ hb hk₁ hk₂
      hC (rectRem_continuous Φ a bj c M₁ M₂ hΦ ha hb' hc) hmix
    refine h.congr_right fun N => ?_
    congr 2
    rw [hτ]
    have e1 : (((h₁ + M₁ : ℕ) : ℝ) + 1) / k₁ = p + (M₁ : ℝ) / k₁ := by
      rw [← hp₁]; push_cast; field_simp; ring
    have e2 : (((h₂ + M₂ : ℕ) : ℝ) + 1) / k₂ = p + (M₂ : ℝ) / k₂ := by
      rw [← hp₂]; push_cast; field_simp; ring
    rw [e1, e2, min_add_add_left]
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

end Laplace.Grammar
