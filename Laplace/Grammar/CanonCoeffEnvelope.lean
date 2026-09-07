/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDCutoffUniform

/-!
# Envelope bounds for the canonical coefficients (grammar §4.2, towards a uniform Taylor tree)

* `abs_logMoment_le_tailMoment`, `abs_logMoment_le_of_env`: `|M[α;ℓ;c]| ≤ K · envMoment` for a
  coefficient function with the Gaussian envelope `|c(s)| ≤ K (1+s)^D e^{βsa'}`.
* `discard_explicit`: `|N^{−α}(A log N + B)| ≤ (|A|+|B|) N^{−2T}(1+log N)` for `α ≥ 2T`, `N ≥ 1`.
* For the analytic amplitude with envelope `(C₀, L, D, ρ)`, the canonical coefficient functions
  `U_α, V_α, C_α` have explicit envelopes (`canonUEnv`, `canonVEnv`, `canonCEnv`), hence
  `|A_α| ≤ canonCEnv α · EM(α,0)` and `|B_α| ≤ canonUEnv α · EM(α,0) + canonVEnv α · EM(α,0)
  + canonCEnv α · EM(α,1)` (`canonA_abs_le_env`, `canonB_abs_le_env`), with `EM` the Gaussian
  envelope moments. All constants depend only on the envelope data. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

theorem abs_log_pow_le_one_add_pow (s : ℝ) (ℓ : ℕ) : |Real.log s ^ ℓ| ≤ (1 + |Real.log s|) ^ ℓ := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log s)]) ℓ

/-- `|M[α;ℓ;c]| ≤ tailMoment β α ℓ c`. -/
theorem abs_logMoment_le_tailMoment (β α : ℝ) (ℓ : ℕ) (c : ℝ → ℝ) (hc : Measurable c)
    (hint : IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ ℓ
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0)) :
    |logMoment β α ℓ c| ≤ tailMoment β α ℓ c := by
  unfold logMoment tailMoment
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ‖s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)‖
      ≤ s ^ (α - 1) * (1 + |Real.log s|) ^ ℓ * (Real.exp (-β * s ^ 2) * |c s|) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
      abs_of_pos (Real.exp_pos _)]
    gcongr
    exact abs_log_pow_le_one_add_pow s ℓ
  have hfm : Measurable fun s : ℝ => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s) :=
    ((measurable_id.pow_const _).mul (Real.measurable_log.pow_const _)).mul
      ((Real.measurable_exp.comp (measurable_const.mul (measurable_id.pow_const 2))).mul hc)
  have hfint : IntegrableOn (fun s : ℝ =>
      ‖s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)‖) (Ioi 0) := by
    refine Integrable.mono' hint hfm.norm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    rw [norm_norm]
    exact hpt s hs
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact setIntegral_mono_on hfint hint measurableSet_Ioi hpt

/-- `|M[α;ℓ;c]| ≤ K · envMoment β α ℓ (gaussEnv β a' D)` under the Gaussian envelope. -/
theorem abs_logMoment_le_of_env (β a' α K : ℝ) (ℓ D : ℕ) (c : ℝ → ℝ) (hβ : 0 < β) (hα : 0 < α)
    (hc : Measurable c) (henv : ∀ s, 0 < s → |c s| ≤ K * gaussEnv β a' D s) :
    |logMoment β α ℓ c| ≤ K * envMoment β α ℓ (gaussEnv β a' D) := by
  have hint := moment_integrableOn_of_envelope β a' (α - 1) K hβ (by linarith) ℓ D c hc
    (fun s hs => by rw [mul_assoc]; exact henv s hs)
  exact (abs_logMoment_le_tailMoment β α ℓ c hc hint).trans
    (tailMoment_le_of_env β a' α K ℓ D c hβ hα hc henv)

/-- The explicit discard bound: a pole term with exponent `α ≥ 2T`, for `N ≥ 1`. -/
theorem discard_explicit (T A B α N : ℝ) (hα : 2 * T ≤ α) (hN : 1 ≤ N) :
    |N ^ (-α) * (A * Real.log N + B)| ≤ (|A| + |B|) * (N ^ (-(2 * T)) * (1 + Real.log N)) := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hpow : N ^ (-α) ≤ N ^ (-(2 * T)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hpos : 0 ≤ N ^ (-α) := by positivity
  rw [abs_mul, abs_of_nonneg hpos]
  have h1 : |A * Real.log N + B| ≤ (|A| + |B|) * (1 + Real.log N) := by
    calc |A * Real.log N + B| ≤ |A * Real.log N| + |B| := abs_add_le _ _
      _ = |A| * Real.log N + |B| := by rw [abs_mul, abs_of_nonneg hlog]
      _ ≤ (|A| + |B|) * (1 + Real.log N) := by nlinarith [abs_nonneg A, abs_nonneg B]
  calc N ^ (-α) * |A * Real.log N + B|
      ≤ N ^ (-(2 * T)) * ((|A| + |B|) * (1 + Real.log N)) := by gcongr
    _ = (|A| + |B|) * (N ^ (-(2 * T)) * (1 + Real.log N)) := by ring

/-- Envelope constant of the canonical `u`-face coefficient at `α` (analytic family). -/
noncomputable def canonUEnv (b ρ C₀ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) : ℝ :=
  if uExp h₁ k₁ (uIdx h₁ k₁ α) = α then
    fpEnvConst ((k₂ : ℝ) * α - h₂ - 1) b k₁ (canonicalM ((k₂ : ℝ) * α - h₂ - 1))
      (C₀ * (ρ ^ uIdx h₁ k₁ α)⁻¹ * (1 + ρ⁻¹) ^ canonicalM ((k₂ : ℝ) * α - h₂ - 1))
      (C₀ * (ρ ^ uIdx h₁ k₁ α)⁻¹ * (ρ ^ canonicalM ((k₂ : ℝ) * α - h₂ - 1))⁻¹ / (1 - b / ρ))
  else 0

/-- Envelope constant of the canonical `v`-face coefficient at `α`. -/
noncomputable def canonVEnv (b ρ C₀ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) : ℝ :=
  if vExp h₂ k₂ (vIdx h₂ k₂ α) = α then
    fpEnvConst ((k₁ : ℝ) * α - h₁ - 1) b k₂ (canonicalM ((k₁ : ℝ) * α - h₁ - 1))
      (C₀ * (ρ ^ vIdx h₂ k₂ α)⁻¹ * (1 + ρ⁻¹) ^ canonicalM ((k₁ : ℝ) * α - h₁ - 1))
      (C₀ * (ρ ^ vIdx h₂ k₂ α)⁻¹ * (ρ ^ canonicalM ((k₁ : ℝ) * α - h₁ - 1))⁻¹ / (1 - b / ρ))
  else 0

/-- Envelope constant of the canonical collision coefficient at `α`. -/
noncomputable def canonCEnv (ρ C₀ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) : ℝ :=
  if uExp h₁ k₁ (uIdx h₁ k₁ α) = α ∧ vExp h₂ k₂ (vIdx h₂ k₂ α) = α then
    C₀ * (ρ ^ (uIdx h₁ k₁ α + vIdx h₂ k₂ α))⁻¹ / ((k₁ : ℝ) * k₂)
  else 0

theorem one_sub_div_pos (b ρ : ℝ) (hb : 0 < b) (hbρ : b < ρ) : 0 < 1 - b / ρ := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  rw [sub_pos, div_lt_one hρ]
  exact hbρ

/-- Envelope of the canonical `u`-face coefficient function. -/
theorem canonU_abs_le_env (c : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ L β : ℝ) (H : ℝ → ℝ) (h₁ h₂ k₁ k₂ D : ℕ)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hC₀ : 0 ≤ C₀)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α s : ℝ) (hs : 0 < s) :
    |canonU b h₁ h₂ k₁ k₂ (anaFaceU c b) (fun i j s => c (i, j) s) α s|
      ≤ canonUEnv b ρ C₀ h₁ h₂ k₁ k₂ α * gaussEnv β L D s := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have h1θ := one_sub_div_pos b ρ hb hbρ
  unfold canonU canonUEnv
  split_ifs with hP
  · set i := uIdx h₁ k₁ α with hi
    set γ : ℝ := (k₂ : ℝ) * α - h₂ - 1 with hγ
    set M := canonicalM γ with hM
    have hγM : γ < M := lt_canonicalM γ
    refine faceFPCoeff_abs_le_env γ b hb k₁ M hk₁ hγM (anaFaceU c b i) (fun m => c (i, m))
      (fun s => H s * (ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ)) _ _ β L D ?_ ?_ ?_ s hs
    · intro m hm s hs
      have := anaCoeff_env c ρ C₀ L β H D hρ hC₀ hc henv i m M hm s hs
      refine this.trans (le_of_eq ?_)
      unfold gaussEnv; ring
    · intro s hs
      have := henv s hs.le
      have hk : 0 ≤ (ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ) :=
        div_nonneg (by positivity) h1θ.le
      calc H s * (ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ)
          = H s * ((ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ)) := by ring
        _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L))
            * ((ρ ^ i)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ)) := mul_le_mul_of_nonneg_right this hk
        _ = _ := by unfold gaussEnv; ring
    · intro s hs u hu
      exact anaFaceU_rem c b ρ H hb hbρ hc i M u s hu
  · simp

/-- Envelope of the canonical `v`-face coefficient function. -/
theorem canonV_abs_le_env (c : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ L β : ℝ) (H : ℝ → ℝ) (h₁ h₂ k₁ k₂ D : ℕ)
    (hb : 0 < b) (hbρ : b < ρ) (hk₂ : 0 < k₂) (hC₀ : 0 ≤ C₀)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α s : ℝ) (hs : 0 < s) :
    |canonV b h₁ h₂ k₁ k₂ (anaFaceV c b) (fun i j s => c (i, j) s) α s|
      ≤ canonVEnv b ρ C₀ h₁ h₂ k₁ k₂ α * gaussEnv β L D s := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have h1θ := one_sub_div_pos b ρ hb hbρ
  unfold canonV canonVEnv
  split_ifs with hP
  · set j := vIdx h₂ k₂ α with hj
    set γ : ℝ := (k₁ : ℝ) * α - h₁ - 1 with hγ
    set M := canonicalM γ with hM
    have hγM : γ < M := lt_canonicalM γ
    refine faceFPCoeff_abs_le_env γ b hb k₂ M hk₂ hγM (anaFaceV c b j) (fun m => c (m, j))
      (fun s => H s * (ρ ^ j)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ)) _ _ β L D ?_ ?_ ?_ s hs
    · intro m hm s hs
      have := anaCoeff_env (swapC c) ρ C₀ L β H D hρ hC₀ (swapC_bound c ρ H hc) henv j m M hm s hs
      simp only [swapC] at this
      refine this.trans (le_of_eq ?_)
      unfold gaussEnv; ring
    · intro s hs
      have := henv s hs.le
      have hk : 0 ≤ (ρ ^ j)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ) :=
        div_nonneg (by positivity) h1θ.le
      calc H s * (ρ ^ j)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ)
          = H s * ((ρ ^ j)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ)) := by ring
        _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L))
            * ((ρ ^ j)⁻¹ * (ρ ^ M)⁻¹ / (1 - b / ρ)) := mul_le_mul_of_nonneg_right this hk
        _ = _ := by unfold gaussEnv; ring
    · intro s hs u hu
      exact anaFaceV_rem c b ρ H hb hbρ hc j M u s hu
  · simp

/-- Envelope of the canonical collision coefficient function. -/
theorem canonC_abs_le_env (c : ℕ × ℕ → ℝ → ℝ) (ρ C₀ L β : ℝ) (H : ℝ → ℝ) (h₁ h₂ k₁ k₂ D : ℕ)
    (hρ : 0 < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α s : ℝ) (hs : 0 < s) :
    |canonC h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α s|
      ≤ canonCEnv ρ C₀ h₁ h₂ k₁ k₂ α * gaussEnv β L D s := by
  have hk : (0 : ℝ) < (k₁ : ℝ) * k₂ := by positivity
  unfold canonC canonCEnv
  split_ifs with hP
  · have h := anaCoeff_abs_le c ρ H hρ hc (uIdx h₁ k₁ α, vIdx h₂ k₂ α) s
    simp only at h
    rw [abs_div, abs_of_pos hk]
    have hρi : 0 ≤ (ρ ^ (uIdx h₁ k₁ α + vIdx h₂ k₂ α))⁻¹ := by positivity
    calc |c (uIdx h₁ k₁ α, vIdx h₂ k₂ α) s| / ((k₁ : ℝ) * k₂)
        ≤ (H s * (ρ ^ (uIdx h₁ k₁ α + vIdx h₂ k₂ α))⁻¹) / ((k₁ : ℝ) * k₂) := by gcongr
      _ ≤ ((C₀ * (1 + s) ^ D * Real.exp (β * s * L)) * (ρ ^ (uIdx h₁ k₁ α + vIdx h₂ k₂ α))⁻¹)
          / ((k₁ : ℝ) * k₂) := by
          gcongr
          exact henv s hs.le
      _ = _ := by unfold gaussEnv; ring
  · simp

theorem canonC_measurable' (c : ℕ × ℕ → ℝ → ℝ) (hcc : ∀ ij, Continuous (c ij))
    (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) :
    Measurable (canonC h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α) := by
  unfold canonC
  split_ifs
  · exact (hcc _).measurable.div_const _
  · exact measurable_const

theorem canonU_measurable' (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (hcc : ∀ ij, Continuous (c ij)) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) :
    Measurable (canonU b h₁ h₂ k₁ k₂ (anaFaceU c b) (fun i j s => c (i, j) s) α) := by
  unfold canonU
  split_ifs
  · exact faceFPCoeff_measurable _ b k₁ (anaFaceU c b _)
      (anaFaceU_continuous c b ρ H hb hbρ hcc hH hc _) (fun m => c (_, m))
      (fun m => (hcc _).measurable) _
  · exact measurable_const

theorem canonV_measurable' (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (hcc : ∀ ij, Continuous (c ij)) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) :
    Measurable (canonV b h₁ h₂ k₁ k₂ (anaFaceV c b) (fun i j s => c (i, j) s) α) := by
  unfold canonV
  split_ifs
  · exact faceFPCoeff_measurable _ b k₂ (anaFaceV c b _)
      (anaFaceV_continuous c b ρ H hb hbρ hcc hH hc _) (fun m => c (m, _))
      (fun m => (hcc _).measurable) _
  · exact measurable_const

/-- **Envelope bound for the canonical log coefficient** `A_α`. -/
theorem canonA_abs_le_env (c : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ L β : ℝ) (H : ℝ → ℝ) (h₁ h₂ k₁ k₂ D : ℕ)
    (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hcc : ∀ ij, Continuous (c ij)) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    |canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α|
      ≤ canonCEnv ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 0 (gaussEnv β L D) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  unfold canonA
  exact abs_logMoment_le_of_env β L α _ 0 D _ hβ hα (canonC_measurable' c hcc h₁ h₂ k₁ k₂ α)
    (fun s hs => canonC_abs_le_env c ρ C₀ L β H h₁ h₂ k₁ k₂ D hρ hk₁ hk₂ hc henv α s hs)

/-- **Envelope bound for the canonical constant coefficient** `B_α`. -/
theorem canonB_abs_le_env (c : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ L β : ℝ) (H : ℝ → ℝ) (h₁ h₂ k₁ k₂ D : ℕ)
    (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hC₀ : 0 ≤ C₀)
    (hcc : ∀ ij, Continuous (c ij)) (hH : Continuous H)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    |canonB β b h₁ h₂ k₁ k₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) α|
      ≤ canonUEnv b ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 0 (gaussEnv β L D)
        + canonVEnv b ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 0 (gaussEnv β L D)
        + canonCEnv ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 1 (gaussEnv β L D) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  unfold canonB
  refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact abs_logMoment_le_of_env β L α _ 0 D _ hβ hα
      (canonU_measurable' c b ρ H hb hbρ hcc hH hc h₁ h₂ k₁ k₂ α)
      (fun s hs => canonU_abs_le_env c b ρ C₀ L β H h₁ h₂ k₁ k₂ D hb hbρ hk₁ hC₀ hc henv α s hs)
  · exact abs_logMoment_le_of_env β L α _ 0 D _ hβ hα
      (canonV_measurable' c b ρ H hb hbρ hcc hH hc h₁ h₂ k₁ k₂ α)
      (fun s hs => canonV_abs_le_env c b ρ C₀ L β H h₁ h₂ k₁ k₂ D hb hbρ hk₂ hC₀ hc henv α s hs)
  · exact abs_logMoment_le_of_env β L α _ 1 D _ hβ hα (canonC_measurable' c hcc h₁ h₂ k₁ k₂ α)
      (fun s hs => canonC_abs_le_env c ρ C₀ L β H h₁ h₂ k₁ k₂ D hρ hk₁ hk₂ hc henv α s hs)

end Laplace.Grammar
