/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AnalyticAdapter

/-!
# The analytic `d = 2` cutoff theorem (grammar §4.2)

For the equal-exponent block and an amplitude given on the box by a double power series with a
radius margin, `Φ(u,v,s) = ∑ c_{ij}(s) u^i v^j` with `|c_{ij}(s)| ρ^{i+j} ≤ H(s) ≤ C₀ (1+s)^D
    e^{βsL}`,
`b < ρ`, the cutoff expansion of units 107–109 holds with the faces `a_i = ∑_j c_{ij} v^j`,
`b_j = ∑_i c_{ij} u^i` and the corner jets `c_{ij}`, and no further hypotheses
(`twoD_cutoff_analytic`): all face remainders, the mixed remainder and the moment hypotheses are
supplied by units 110 and 114. This is the paper-facing higher-order `d = 2` theorem under the
paper's own analyticity assumption, in the Schwarz-free form of Astra #6. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- The resonance parameter of the `u`-face `i` is below `M₂`. -/
theorem uface_gamma_lt (p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ i : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hi : i < M₁) :
    (k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1 < M₂ := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hp₂p : (((h₁ + i : ℕ) : ℝ) + 1) / k₁ = p + (i : ℝ) / k₁ := by
    rw [← hp₁]; push_cast; field_simp; ring
  have : (k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1 = (k₂ : ℝ) * i / k₁ := by
    rw [hp₂p, ← hp₂]; field_simp; ring
  rw [this]
  have hi1 : i + 1 ≤ M₁ := hi
  have hi1' : (i : ℝ) + 1 ≤ M₁ := by exact_mod_cast hi1
  have h2 : (k₂ : ℝ) * i / k₁ ≤ (k₂ : ℝ) * ((M₁ - 1) / k₁) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hk₁').2 (by linarith)) hk₂'.le
  have h3 : (k₂ : ℝ) * ((M₁ - 1) / k₁) < (k₂ : ℝ) * ((M₂ : ℝ) / k₂) := mul_lt_mul_of_pos_left
    hM₁ hk₂'
  rw [mul_div_cancel₀ _ hk₂'.ne'] at h3
  linarith

/-- The resonance parameter of the `v`-face `j` is below `M₁`. -/
theorem vface_gamma_lt (p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ j : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁) (hj : j < M₂) :
    (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1 < M₁ :=
  uface_gamma_lt p h₂ h₁ k₂ k₁ M₂ M₁ j hk₂ hk₁ hp₂ hp₁ hM₂ hj

/-- The resonance parameter of the corner `(i, j)` is below `M₁ + k₁ M₂`. -/
theorem corner_gamma_lt (p : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ i j : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hj : j < M₂) :
    (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1
      < ((M₁ + k₁ * M₂ : ℕ) : ℝ) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hj' : (j : ℝ) < M₂ := by exact_mod_cast hj
  have hp₂p : (((h₂ + j : ℕ) : ℝ) + 1) / k₂ = p + (j : ℝ) / k₂ := by
    rw [← hp₂]; push_cast; field_simp; ring
  have : (k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1
      = (k₁ : ℝ) * j / k₂ - i := by
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

/-- The envelope of the coefficients `c_{im}`, uniform in `m < M`. -/
theorem anaCoeff_env (c : ℕ × ℕ → ℝ → ℝ) (ρ C₀ L β : ℝ) (H : ℝ → ℝ) (D : ℕ) (hρ : 0 < ρ)
    (hC₀ : 0 ≤ C₀) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (i m M : ℕ) (hm : m < M)
    (s : ℝ) (hs : 0 < s) :
    |c (i, m) s| ≤ C₀ * (ρ ^ i)⁻¹ * (1 + ρ⁻¹) ^ M * (1 + s) ^ D * Real.exp (β * s * L) := by
  have h := anaCoeff_abs_le c ρ H hρ hc (i, m) s
  simp only at h
  have hH0 : 0 ≤ H s := le_trans (by positivity) (hc (0, 0) s)
  have hρi : 0 ≤ (ρ ^ i)⁻¹ := by positivity
  have hpow : (ρ⁻¹) ^ m ≤ (1 + ρ⁻¹) ^ M := by
    calc (ρ⁻¹) ^ m ≤ (1 + ρ⁻¹) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ ≤ (1 + ρ⁻¹) ^ M := pow_le_pow_right₀ (by linarith [inv_nonneg.2 hρ.le]) hm.le
  calc |c (i, m) s| ≤ H s * (ρ ^ (i + m))⁻¹ := h
    _ = H s * (ρ ^ i)⁻¹ * (ρ⁻¹) ^ m := by rw [pow_add, mul_inv, inv_pow]; ring
    _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) * (ρ ^ i)⁻¹ * (1 + ρ⁻¹) ^ M :=
        mul_le_mul (mul_le_mul_of_nonneg_right (henv s hs.le) hρi) hpow (by positivity)
          (by positivity)
    _ = _ := by ring

/-- **The analytic `d = 2` cutoff theorem.** -/
theorem twoD_cutoff_analytic (β b p ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁)
    (c : ℕ × ℕ → ℝ → ℝ) (hcc : ∀ ij, Continuous (c ij)) (H : ℝ → ℝ) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp c b)
        - reducedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i,
    j) s) N)
      =O[atTop] fun N : ℝ =>
        N ^ (-(p + min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hθ : b / ρ < 1 := (div_lt_one hρ).2 hbρ
  have h1θ : 0 < 1 - b / ρ := by linarith
  have hH0 : ∀ s, 0 ≤ H s := fun s => le_trans (by positivity) (hc (0, 0) s)
  -- the face envelopes
  set Ha : ℕ → ℝ → ℝ := fun i s => H s * (ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ) with hHa
  set Hb : ℕ → ℝ → ℝ := fun j s => H s * (ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ) with hHb
  have hHam : ∀ i, Measurable (Ha i) := fun i => by
    simp only [hHa]; exact ((hH.measurable.mul_const _).mul_const _).div_const _
  have hHbm : ∀ j, Measurable (Hb j) := fun j => by
    simp only [hHb]; exact ((hH.measurable.mul_const _).mul_const _).div_const _
  have hHa0 : ∀ i s, 0 ≤ Ha i s := fun i s => by
    simp only [hHa]; have := hH0 s; positivity
  have hHb0 : ∀ j s, 0 ≤ Hb j s := fun j s => by
    simp only [hHb]; have := hH0 s; positivity
  -- the face remainders
  have hremA : ∀ i, i < M₁ → ∀ s, 0 < s → ∀ v ∈ Ioc (0 : ℝ) b,
      |anaFaceU c b i v s - ∑ m ∈ Finset.range M₂, c (i, m) s * v ^ m| ≤ Ha i s * v ^ M₂ :=
    fun i _ s _ v hv => anaFaceU_rem c b ρ H hb hbρ hc i M₂ v s hv
  have hremB : ∀ j, j < M₂ → ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |anaFaceV c b j u s - ∑ m ∈ Finset.range M₁, c (m, j) s * u ^ m| ≤ Hb j s * u ^ M₁ :=
    fun j _ s _ u hu => anaFaceV_rem c b ρ H hb hbρ hc j M₁ u s hu
  -- the mixed remainder
  set Cmix : ℝ := C₀ * (ρ ^ (M₁ + M₂))⁻¹ / (1 - b / ρ) ^ 2 with hCmix
  have hCmix0 : 0 ≤ Cmix := by simp only [hCmix]; positivity
  have hmix : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |rectRem (anaAmp c b) (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) M₁ M₂ u v s|
        ≤ Cmix * (u ^ M₁ * v ^ M₂) * ((1 + s) ^ D * Real.exp (β * s * L)) := by
    intro u hu v hv s hs
    refine (anaAmp_rectRem_le c b ρ H hb hbρ hc M₁ M₂ u v s hu hv).trans ?_
    have huv : 0 ≤ u ^ M₁ * v ^ M₂ := mul_nonneg (pow_nonneg hu.1 _) (pow_nonneg hv.1 _)
    calc H s * (ρ ^ (M₁ + M₂))⁻¹ / (1 - b / ρ) ^ 2 * (u ^ M₁ * v ^ M₂)
        ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) * (ρ ^ (M₁ + M₂))⁻¹ / (1 - b / ρ) ^ 2
          * (u ^ M₁ * v ^ M₂) := by gcongr; exact henv s hs
      _ = _ := by rw [hCmix]; ring
  -- the moment hypotheses
  have hmomA : ∀ i, i < M₁ → FaceMoments β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂
      (anaFaceU c b i) (fun m => c (i, m)) (Ha i) := by
    intro i hi
    refine faceMoments_of_envelope β _ b L (C₀ * (ρ ^ i)⁻¹ * (1 + ρ⁻¹) ^ M₂)
      (C₀ * (ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ)) h₂ k₂ k₁ M₂ D hβ hb hk₂ hk₁ (by positivity)
      (anaFaceU c b i) (anaFaceU_continuous c b ρ H hb hbρ hcc hH hc i) (fun m => c (i, m))
      (fun m => (hcc (i, m)).measurable) (Ha i) (hHam i) (hHa0 i)
      (uface_gamma_lt p h₁ h₂ k₁ k₂ M₁ M₂ i hk₁ hk₂ hp₁ hp₂ hM₁ hi) (by positivity)
      (fun m hm s hs => anaCoeff_env c ρ C₀ L β H D hρ hC₀ hc henv i m M₂ hm s hs) ?_
      (fun s hs v hv => hremA i hi s hs v hv)
    intro s hs
    simp only [hHa]
    have := henv s hs.le
    have hk : 0 ≤ (ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ) := by positivity
    calc H s * (ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ)
        = H s * ((ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ)) := by ring
      _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) * ((ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ)) :=
          mul_le_mul_of_nonneg_right this hk
      _ = _ := by ring
  have hmomB : ∀ j, j < M₂ → FaceMoments β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁
      (anaFaceV c b j) (fun m => c (m, j)) (Hb j) := by
    intro j hj
    refine faceMoments_of_envelope β _ b L (C₀ * (ρ ^ j)⁻¹ * (1 + ρ⁻¹) ^ M₁)
      (C₀ * (ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ)) h₁ k₁ k₂ M₁ D hβ hb hk₁ hk₂ (by positivity)
      (anaFaceV c b j) (anaFaceV_continuous c b ρ H hb hbρ hcc hH hc j) (fun m => c (m, j))
      (fun m => (hcc (m, j)).measurable) (Hb j) (hHbm j) (hHb0 j)
      (vface_gamma_lt p h₁ h₂ k₁ k₂ M₁ M₂ j hk₁ hk₂ hp₁ hp₂ hM₂ hj) (by positivity)
      (fun m hm s hs => ?_) ?_ (fun s hs u hu => hremB j hj s hs u hu)
    · have := anaCoeff_env (swapC c) ρ C₀ L β H D hρ hC₀ (swapC_bound c ρ H hc) henv j m M₁ hm
        s hs
      simpa [swapC] using this
    · intro s hs
      simp only [hHb]
      have := henv s hs.le
      have hk : 0 ≤ (ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ) := by positivity
      calc H s * (ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ)
          = H s * ((ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ)) := by ring
        _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) * ((ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ)) :=
            mul_le_mul_of_nonneg_right this hk
        _ = _ := by ring
  have hmomC : ∀ i, i < M₁ → ∀ j, j < M₂ → FaceMoments β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i)
      k₁ k₂ (M₁ + k₁ * M₂) (fun _ s => c (i, j) s) (cornerData (c (i, j))) (fun _ => 0) := by
    intro i hi j hj
    have hMc : 0 < M₁ + k₁ * M₂ := by
      have : 0 < M₂ := lt_of_le_of_lt (Nat.zero_le j) hj
      positivity
    refine faceMoments_of_envelope β _ b L (C₀ * (ρ ^ (i + j))⁻¹) 0 (h₁ + i) k₁ k₂
      (M₁ + k₁ * M₂) D hβ hb hk₁ hk₂ (by positivity) (fun _ s => c (i, j) s)
      ((hcc (i, j)).comp continuous_snd) (cornerData (c (i, j)))
      (cornerData_measurable (c (i, j)) (hcc (i, j)).measurable) (fun _ => 0) measurable_const
      (fun _ => le_rfl) (corner_gamma_lt p h₁ h₂ k₁ k₂ M₁ M₂ i j hk₁ hk₂ hp₁ hp₂ hj) le_rfl
      (fun m _ s hs => ?_) (fun s _ => by simp) (fun s _ u _ => ?_)
    · unfold cornerData
      split_ifs
      · have h := anaCoeff_abs_le c ρ H hρ hc (i, j) s
        simp only at h
        calc |c (i, j) s| ≤ H s * (ρ ^ (i + j))⁻¹ := h
          _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) * (ρ ^ (i + j))⁻¹ :=
              mul_le_mul_of_nonneg_right (henv s hs.le) (by positivity)
          _ = _ := by ring
      · simp only [abs_zero]
        positivity
    · simp only [cornerData_rem (c (i, j)) _ hMc s u, abs_zero, zero_mul, le_refl]
  exact twoD_cutoff_reduced_isBigO β b p h₁ h₂ k₁ k₂ M₁ M₂ hβ hb hk₁ hk₂ hp₁ hp₂ hM₁ hM₂
    (anaAmp c b) (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s)
    (anaAmp_continuous c b ρ H hb hbρ hcc hH hc) (anaFaceU_continuous c b ρ H hb hbρ hcc hH hc)
    (anaFaceV_continuous c b ρ H hb hbρ hcc hH hc) (fun i j => hcc (i, j)) Ha Hb hHam hHa0 hHbm hHb0
    hremA hremB Cmix L D hCmix0 hmix hmomA hmomB hmomC

end Laplace.Grammar
