/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FaceConstEnvelope

/-!
# The uniform-family cutoff theorem (grammar §4.2, Astra #9 R5)

For every `s`-parametrised double series `c` with the COMMON envelope
`|c_ij(s)| ρ^{i+j} ≤ H(s) ≤ C₀(1+s)^D e^{βsL}` and every `N ≥ 1`,

  `|Z_c(N) − S_c(N)| ≤ uniformConst · N^{−E} (1 + log N)`,

where `uniformConst` depends only on `(β, b, ρ, C₀, L, D, h, k, M)` — the constant is chosen
BEFORE the coefficient family (`twoD_cutoff_uniform`). It is the explicit cutoff constant of
unit 131 with every face constant replaced by its envelope bound (unit 132) at the face envelopes
of the analytic adapter, plus the explicit mixed constant of unit 130. This is the input for
integrating the `d = 2` block over noncritical coordinates with `param_integration`. Zero
`sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- **The uniform cutoff constant** for the analytic family with envelope `(C₀, L, D, ρ)`. -/
noncomputable def uniformConst (β b ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ) : ℝ :=
  (∑ i ∈ Finset.range M₁,
      faceEnvConst ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) b h₂ k₂ k₁ M₂
          (C₀ * (ρ ^ i)⁻¹ * (1 + ρ⁻¹) ^ M₂) (C₀ * (ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ))
        * envMoment β ((((h₁ + i : ℕ) : ℝ) + 1) / k₁
            + ((M₂ : ℝ) - ((k₂ : ℝ) * ((((h₁ + i : ℕ) : ℝ) + 1) / k₁) - h₂ - 1)) / k₂) 1
            (gaussEnv β L D))
  + (∑ j ∈ Finset.range M₂,
      faceEnvConst ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b h₁ k₁ k₂ M₁
          (C₀ * (ρ ^ j)⁻¹ * (1 + ρ⁻¹) ^ M₁) (C₀ * (ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ))
        * envMoment β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂
            + ((M₁ : ℝ) - ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - h₁ - 1)) / k₁) 1
            (gaussEnv β L D))
  + (∑ i ∈ Finset.range M₁, ∑ j ∈ Finset.range M₂,
      faceEnvConst ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) b (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂)
          (C₀ * (ρ ^ (i + j))⁻¹) 0
        * envMoment β ((((h₂ + j : ℕ) : ℝ) + 1) / k₂
            + (((M₁ + k₁ * M₂ : ℕ) : ℝ)
              - ((k₁ : ℝ) * ((((h₂ + j : ℕ) : ℝ) + 1) / k₂) - ((h₁ + i : ℕ) : ℝ) - 1)) / k₁) 1
            (gaussEnv β L D))
  + C₀ * (ρ ^ (M₁ + M₂))⁻¹ / (1 - b / ρ) ^ 2 * Real.exp ((D : ℝ) ^ 2 / β)
      * mixConst (β / 2) (2 * L) b (h₁ + M₁) (h₂ + M₂) k₁ k₂

/-- **The uniform-family cutoff theorem**: the remainder constant depends only on the common
envelope data, not on the coefficient family. -/
theorem twoD_cutoff_uniform (β b p₁ p₂ ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ)
    (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hM₁ : p₁ + ((M₁ : ℝ) - 1) / k₁ < p₂ + (M₂ : ℝ) / k₂)
    (hM₂ : p₂ + ((M₂ : ℝ) - 1) / k₂ < p₁ + (M₁ : ℝ) / k₁)
    (c : ℕ × ℕ → ℝ → ℝ) (hcc : ∀ ij, Continuous (c ij)) (H : ℝ → ℝ) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (N : ℝ) (hN : 1 ≤ N) :
    |twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp c b)
        - mergedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i,
    j) s) N|
      ≤ uniformConst β b ρ C₀ L h₁ h₂ k₁ k₂ M₁ M₂ D
        * N ^ (-(min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
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
      (uface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i hi) (by positivity)
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
      (vface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j hj) (by positivity)
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
      (fun _ => le_rfl)
      (corner_gamma_lt_general' p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ i j hk₁ hk₂ hp₁ hp₂ hM₂ hj) le_rfl
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
  have hexpl := twoD_cutoff_general_explicit β b p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hβ hb hk₁ hk₂ hp₁ hp₂
    hM₁ hM₂ (anaAmp c b) (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s)
    (anaAmp_continuous c b ρ H hb hbρ hcc hH hc) (anaFaceU_continuous c b ρ H hb hbρ hcc hH hc)
    (anaFaceV_continuous c b ρ H hb hbρ hcc hH hc) (fun i j => hcc (i, j)) Ha Hb hHam hHa0 hHbm hHb0
    hremA hremB Cmix L D hCmix0 hmix hmomA hmomB hmomC N hN
  refine hexpl.trans ?_
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hA : 0 ≤ N ^ (-(min (p₁ + (M₁ : ℝ) / k₁) (p₂ + (M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
    positivity
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hA
  -- the face envelopes as `gaussEnv` bounds
  have hgE : ∀ s, (1 + s) ^ D * Real.exp (β * s * L) = gaussEnv β L D s := fun s => rfl
  unfold cutoffConst uniformConst
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) (le_of_eq ?_)
  · refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i < M₁ := Finset.mem_range.1 hi
    refine faceConst_le_env β _ b L _ _ h₂ k₂ k₁ M₂ D hβ hb hk₂ hk₁ (by positivity)
      (anaFaceU c b i) (anaFaceU_continuous c b ρ H hb hbρ hcc hH hc i) (fun m => c (i, m))
      (fun m => (hcc (i, m)).measurable) (Ha i) (hHam i) (hHa0 i)
      (uface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₁ i hi')
      (by positivity) (by positivity) ?_ ?_ (fun s hs v hv => hremA i hi' s hs v hv)
    · intro m hm s hs
      have := anaCoeff_env c ρ C₀ L β H D hρ hC₀ hc henv i m M₂ hm s hs
      refine this.trans (le_of_eq ?_)
      unfold gaussEnv; ring
    · intro s hs
      simp only [hHa]
      have := henv s hs.le
      have hk : 0 ≤ (ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ) := by positivity
      calc H s * (ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ)
          = H s * ((ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ)) := by ring
        _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L))
            * ((ρ ^ i)⁻¹ * (ρ ^ M₂)⁻¹ / (1 - b / ρ)) := mul_le_mul_of_nonneg_right this hk
        _ = _ := by unfold gaussEnv; ring
  · refine Finset.sum_le_sum fun j hj => ?_
    have hj' : j < M₂ := Finset.mem_range.1 hj
    refine faceConst_le_env β _ b L _ _ h₁ k₁ k₂ M₁ D hβ hb hk₁ hk₂ (by positivity)
      (anaFaceV c b j) (anaFaceV_continuous c b ρ H hb hbρ hcc hH hc j) (fun m => c (m, j))
      (fun m => (hcc (m, j)).measurable) (Hb j) (hHbm j) (hHb0 j)
      (vface_gamma_lt_general p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ hk₁ hk₂ hp₁ hp₂ hM₂ j hj')
      (by positivity) (by positivity) ?_ ?_ (fun s hs u hu => hremB j hj' s hs u hu)
    · intro m hm s hs
      have := anaCoeff_env (swapC c) ρ C₀ L β H D hρ hC₀ (swapC_bound c ρ H hc) henv j m M₁ hm
        s hs
      simp only [swapC] at this
      refine this.trans (le_of_eq ?_)
      unfold gaussEnv; ring
    · intro s hs
      simp only [hHb]
      have := henv s hs.le
      have hk : 0 ≤ (ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ) := by positivity
      calc H s * (ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ)
          = H s * ((ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ)) := by ring
        _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L))
            * ((ρ ^ j)⁻¹ * (ρ ^ M₁)⁻¹ / (1 - b / ρ)) := mul_le_mul_of_nonneg_right this hk
        _ = _ := by unfold gaussEnv; ring
  · refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    have hi' : i < M₁ := Finset.mem_range.1 hi
    have hj' : j < M₂ := Finset.mem_range.1 hj
    have hMc : 0 < M₁ + k₁ * M₂ := by
      have : 0 < M₂ := lt_of_le_of_lt (Nat.zero_le j) hj'
      positivity
    refine faceConst_le_env β _ b L _ 0 (h₁ + i) k₁ k₂ (M₁ + k₁ * M₂) D hβ hb hk₁ hk₂
      (by positivity) (fun _ s => c (i, j) s) ((hcc (i, j)).comp continuous_snd)
      (cornerData (c (i, j))) (cornerData_measurable (c (i, j)) (hcc (i, j)).measurable)
      (fun _ => 0) measurable_const (fun _ => le_rfl)
      (corner_gamma_lt_general' p₁ p₂ h₁ h₂ k₁ k₂ M₁ M₂ i j hk₁ hk₂ hp₁ hp₂ hM₂ hj')
      (by positivity) le_rfl ?_ (fun s hs => by simp) ?_
    · intro m _ s hs
      unfold cornerData
      split_ifs
      · have h := anaCoeff_abs_le c ρ H hρ hc (i, j) s
        simp only at h
        calc |c (i, j) s| ≤ H s * (ρ ^ (i + j))⁻¹ := h
          _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) * (ρ ^ (i + j))⁻¹ :=
              mul_le_mul_of_nonneg_right (henv s hs.le) (by positivity)
          _ = _ := by unfold gaussEnv; ring
      · simp only [abs_zero]
        have := gaussEnv_nonneg β L D s hs.le
        positivity
    · intro s _ u _
      simp only [cornerData_rem (c (i, j)) _ hMc s u, abs_zero, zero_mul, le_refl]
  · simp only [hCmix]

end Laplace.Grammar
