/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoeffWeightedBound

/-!
# Linearity and the difference form of the canonical coefficients (grammar §4.2, R6)

On the envelope class the canonical coefficients are linear: `A_α(c − d) = A_α(c) − A_α(d)` and
`B_α(c − d) = B_α(c) − B_α(d)` (`canonA_sub`, `canonB_sub`), proved through the collision formula
and the moment series of unit 126 (the finite-part functionals are linear on absolutely convergent
rows). Combined with the weighted-norm bounds of unit 140 this gives the difference form Astra #10
asked for: `|A_α(c) − A_α(d)| ≤ w_C(α) ‖c − d‖_{α,0,r}` and
`|B_α(c) − B_α(d)| ≤ (w_U + w_V)(α) ‖c − d‖_{α,0,r} + w_C(α) ‖c − d‖_{α,1,r}`
(`abs_canonA_sub_le`, `abs_canonB_sub_le`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- The log-moment integrand is integrable when the tail integrand is. -/
theorem logMoment_integrable_of_tail (β α : ℝ) (ℓ : ℕ) (c : ℝ → ℝ) (hc : Measurable c)
    (hint : IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ ℓ
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0)) :
    IntegrableOn (fun s => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s))
      (Ioi 0) := by
  have hfm : Measurable fun s : ℝ => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s) :=
    ((measurable_id.pow_const _).mul (Real.measurable_log.pow_const _)).mul
      ((Real.measurable_exp.comp (measurable_const.mul (measurable_id.pow_const 2))).mul hc)
  refine Integrable.mono' hint hfm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have hs0 : (0 : ℝ) < s := hs
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
    abs_of_pos (Real.exp_pos _)]
  gcongr
  exact abs_log_pow_le_one_add_pow s ℓ

/-- Log moments are additive under differences (given integrability). -/
theorem logMoment_sub (β α : ℝ) (ℓ : ℕ) (c₁ c₂ : ℝ → ℝ)
    (h₁ : IntegrableOn (fun s => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c₁ s))
      (Ioi 0))
    (h₂ : IntegrableOn (fun s => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c₂ s))
      (Ioi 0)) :
    logMoment β α ℓ (fun s => c₁ s - c₂ s) = logMoment β α ℓ c₁ - logMoment β α ℓ c₂ := by
  unfold logMoment
  rw [← integral_sub h₁ h₂]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

/-- The envelope of a difference. -/
theorem sub_envelope (c d : ℕ × ℕ → ℝ → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (H H' : ℝ → ℝ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (hd : ∀ ij s, |d ij s| * ρ ^ (ij.1 + ij.2) ≤ H' s) (ij : ℕ × ℕ) (s : ℝ) :
    |c ij s - d ij s| * ρ ^ (ij.1 + ij.2) ≤ H s + H' s := by
  calc |c ij s - d ij s| * ρ ^ (ij.1 + ij.2)
      ≤ (|c ij s| + |d ij s|) * ρ ^ (ij.1 + ij.2) :=
        mul_le_mul_of_nonneg_right (abs_sub (c ij s) (d ij s)) (by positivity)
    _ = |c ij s| * ρ ^ (ij.1 + ij.2) + |d ij s| * ρ ^ (ij.1 + ij.2) := by ring
    _ ≤ H s + H' s := add_le_add (hc ij s) (hd ij s)

theorem sub_henv (β L C₀ C₀' : ℝ) (D : ℕ) (H H' : ℝ → ℝ)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (henv' : ∀ s, 0 ≤ s → H' s ≤ C₀' * (1 + s) ^ D * Real.exp (β * s * L)) (s : ℝ) (hs : 0 ≤ s) :
    H s + H' s ≤ (C₀ + C₀') * (1 + s) ^ D * Real.exp (β * s * L) := by
  have := henv s hs; have := henv' s hs; linarith

/-- The collision coefficient is linear. -/
theorem canonC_sub (h₁ h₂ k₁ k₂ : ℕ) (c d : ℕ × ℕ → ℝ → ℝ) (α : ℝ) :
    canonC h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s - d (i, j) s) α
      = fun s => canonC h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α s
        - canonC h₁ h₂ k₁ k₂ (fun i j s => d (i, j) s) α s := by
  unfold canonC
  split_ifs
  · funext s; ring
  · funext s; simp

/-- Tail integrability of the collision coefficient (envelope class). -/
theorem canonC_logMoment_integrable (c : ℕ × ℕ → ℝ → ℝ) (ρ C₀ L β : ℝ) (H : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ ℓ D : ℕ) (hβ : 0 < β) (hρ : 0 < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hcc : ∀ ij, Continuous (c ij)) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    IntegrableOn (fun s => s ^ (α - 1) * Real.log s ^ ℓ
      * (Real.exp (-β * s ^ 2) * canonC h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α s)) (Ioi 0) :=
  logMoment_integrable_of_tail β α ℓ _ (canonC_measurable' c hcc h₁ h₂ k₁ k₂ α)
    (moment_integrableOn_of_envelope β L (α - 1) (canonCEnv ρ C₀ h₁ h₂ k₁ k₂ α) hβ (by linarith)
      ℓ D _ (canonC_measurable' c hcc h₁ h₂ k₁ k₂ α)
      (fun s hs => by
        rw [mul_assoc]
        exact canonC_abs_le_env c ρ C₀ L β H h₁ h₂ k₁ k₂ D hρ hk₁ hk₂ hc henv α s hs))

/-- **Linearity of the canonical log coefficient** on the envelope class. -/
theorem canonA_sub (c d : ℕ × ℕ → ℝ → ℝ) (ρ C₀ C₀' L β : ℝ) (H H' : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hρ : 0 < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hcc : ∀ ij, Continuous (c ij)) (hdc : ∀ ij, Continuous (d ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (hd : ∀ ij s, |d ij s| * ρ ^ (ij.1 + ij.2) ≤ H' s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (henv' : ∀ s, 0 ≤ s → H' s ≤ C₀' * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s - d (i, j) s) α
      = canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α
        - canonA β h₁ h₂ k₁ k₂ (fun i j s => d (i, j) s) α := by
  unfold canonA
  rw [canonC_sub]
  exact logMoment_sub β α 0 _ _
    (canonC_logMoment_integrable c ρ C₀ L β H h₁ h₂ k₁ k₂ 0 D hβ hρ hk₁ hk₂ hcc hc henv α hα)
    (canonC_logMoment_integrable d ρ C₀' L β H' h₁ h₂ k₁ k₂ 0 D hβ hρ hk₁ hk₂ hdc hd henv' α hα)

/-- The `u`-face moment is linear (via the moment series). -/
theorem logMoment_canonU_sub (c d : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ C₀' L β : ℝ) (H H' : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ ℓ D : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁)
    (hC₀ : 0 ≤ C₀) (hC₀' : 0 ≤ C₀') (hcc : ∀ ij, Continuous (c ij))
    (hdc : ∀ ij, Continuous (d ij)) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (hd : ∀ ij s, |d ij s| * ρ ^ (ij.1 + ij.2) ≤ H' s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (henv' : ∀ s, 0 ≤ s → H' s ≤ C₀' * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) :
    logMoment β α ℓ (canonU b h₁ h₂ k₁ k₂ (anaFaceU (fun ij s => c ij s - d ij s) b)
        (fun i j s => c (i, j) s - d (i, j) s) α)
      = logMoment β α ℓ (canonU b h₁ h₂ k₁ k₂ (anaFaceU c b) (fun i j s => c (i, j) s) α)
        - logMoment β α ℓ (canonU b h₁ h₂ k₁ k₂ (anaFaceU d b) (fun i j s => d (i, j) s) α) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hcd : ∀ ij, Continuous ((fun ij s => c ij s - d ij s) ij) := fun ij => (hcc ij).sub (hdc ij)
  by_cases hP : uExp h₁ k₁ (uIdx h₁ k₁ α) = α
  · obtain ⟨i, rfl⟩ : ∃ i, uExp h₁ k₁ i = α := ⟨_, hP⟩
    have hα : 0 < uExp h₁ k₁ i := by unfold uExp; positivity
    have hSc := logMoment_canonU_series β b ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ c hcc H hc hC₀ henv
      ℓ i
    have hSd := logMoment_canonU_series β b ρ C₀' L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ d hdc H' hd hC₀'
      henv' ℓ i
    have hScd := logMoment_canonU_series β b ρ (C₀ + C₀') L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁
      (fun ij s => c ij s - d ij s) hcd (fun s => H s + H' s) (sub_envelope c d ρ hρ H H' hc hd)
      (by linarith) (sub_henv β L C₀ C₀' D H H' henv henv') ℓ i
    rw [hScd.2, hSc.2, hSd.2, ← mul_sub, ← hSc.1.tsum_sub hSd.1]
    congr 1
    refine tsum_congr fun j => ?_
    rw [← mul_sub]
    congr 1
    exact logMoment_sub β _ ℓ _ _
      (logMoment_integrable_of_tail β _ ℓ _ (hcc (i, j)).measurable
        (tail_integrable_of_env c ρ C₀ L β _ H ℓ D hβ hα hρ hcc hc henv (i, j)))
      (logMoment_integrable_of_tail β _ ℓ _ (hdc (i, j)).measurable
        (tail_integrable_of_env d ρ C₀' L β _ H' ℓ D hβ hα hρ hdc hd henv' (i, j)))
  · have hno : ∀ i, uExp h₁ k₁ i ≠ α := fun i h => hP (by rw [← h, uIdx_uExp h₁ k₁ hk₁ i])
    rw [canonU_of_not b h₁ h₂ k₁ k₂ _ _ α hno, canonU_of_not b h₁ h₂ k₁ k₂ _ _ α hno,
      canonU_of_not b h₁ h₂ k₁ k₂ _ _ α hno, logMoment_zero_fun, sub_zero]

/-- The `v`-face moment is linear (via the moment series). -/
theorem logMoment_canonV_sub (c d : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ C₀' L β : ℝ) (H H' : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ ℓ D : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hk₂ : 0 < k₂)
    (hC₀ : 0 ≤ C₀) (hC₀' : 0 ≤ C₀') (hcc : ∀ ij, Continuous (c ij))
    (hdc : ∀ ij, Continuous (d ij)) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (hd : ∀ ij s, |d ij s| * ρ ^ (ij.1 + ij.2) ≤ H' s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (henv' : ∀ s, 0 ≤ s → H' s ≤ C₀' * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) :
    logMoment β α ℓ (canonV b h₁ h₂ k₁ k₂ (anaFaceV (fun ij s => c ij s - d ij s) b)
        (fun i j s => c (i, j) s - d (i, j) s) α)
      = logMoment β α ℓ (canonV b h₁ h₂ k₁ k₂ (anaFaceV c b) (fun i j s => c (i, j) s) α)
        - logMoment β α ℓ (canonV b h₁ h₂ k₁ k₂ (anaFaceV d b) (fun i j s => d (i, j) s) α) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hcd : ∀ ij, Continuous ((fun ij s => c ij s - d ij s) ij) := fun ij => (hcc ij).sub (hdc ij)
  by_cases hP : vExp h₂ k₂ (vIdx h₂ k₂ α) = α
  · obtain ⟨j, rfl⟩ : ∃ j, vExp h₂ k₂ j = α := ⟨_, hP⟩
    have hα : 0 < vExp h₂ k₂ j := by unfold vExp; positivity
    have hSc := logMoment_canonV_series β b ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₂ c hcc H hc hC₀ henv
      ℓ j
    have hSd := logMoment_canonV_series β b ρ C₀' L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₂ d hdc H' hd hC₀'
      henv' ℓ j
    have hScd := logMoment_canonV_series β b ρ (C₀ + C₀') L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₂
      (fun ij s => c ij s - d ij s) hcd (fun s => H s + H' s) (sub_envelope c d ρ hρ H H' hc hd)
      (by linarith) (sub_henv β L C₀ C₀' D H H' henv henv') ℓ j
    rw [hScd.2, hSc.2, hSd.2, ← mul_sub, ← hSc.1.tsum_sub hSd.1]
    congr 1
    refine tsum_congr fun i => ?_
    rw [← mul_sub]
    congr 1
    exact logMoment_sub β _ ℓ _ _
      (logMoment_integrable_of_tail β _ ℓ _ (hcc (i, j)).measurable
        (tail_integrable_of_env c ρ C₀ L β _ H ℓ D hβ hα hρ hcc hc henv (i, j)))
      (logMoment_integrable_of_tail β _ ℓ _ (hdc (i, j)).measurable
        (tail_integrable_of_env d ρ C₀' L β _ H' ℓ D hβ hα hρ hdc hd henv' (i, j)))
  · have hno : ∀ j, vExp h₂ k₂ j ≠ α := fun j h => hP (by rw [← h, vIdx_vExp h₂ k₂ hk₂ j])
    rw [canonV_of_not b h₁ h₂ k₁ k₂ _ _ α hno, canonV_of_not b h₁ h₂ k₁ k₂ _ _ α hno,
      canonV_of_not b h₁ h₂ k₁ k₂ _ _ α hno, logMoment_zero_fun, sub_zero]

/-- **Linearity of the canonical constant coefficient** on the envelope class. -/
theorem canonB_sub (c d : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ C₀' L β : ℝ) (H H' : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hC₀ : 0 ≤ C₀) (hC₀' : 0 ≤ C₀') (hcc : ∀ ij, Continuous (c ij))
    (hdc : ∀ ij, Continuous (d ij)) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (hd : ∀ ij s, |d ij s| * ρ ^ (ij.1 + ij.2) ≤ H' s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (henv' : ∀ s, 0 ≤ s → H' s ≤ C₀' * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    canonB β b h₁ h₂ k₁ k₂ (anaFaceU (fun ij s => c ij s - d ij s) b)
        (anaFaceV (fun ij s => c ij s - d ij s) b) (fun i j s => c (i, j) s - d (i, j) s) α
      = canonB β b h₁ h₂ k₁ k₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) α
        - canonB β b h₁ h₂ k₁ k₂ (anaFaceU d b) (anaFaceV d b) (fun i j s => d (i, j) s) α := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  unfold canonB
  rw [logMoment_canonU_sub c d b ρ C₀ C₀' L β H H' h₁ h₂ k₁ k₂ 0 D hβ hb hbρ hk₁ hC₀ hC₀' hcc hdc
      hc hd henv henv' α,
    logMoment_canonV_sub c d b ρ C₀ C₀' L β H H' h₁ h₂ k₁ k₂ 0 D hβ hb hbρ hk₂ hC₀ hC₀' hcc hdc
      hc hd henv henv' α,
    canonC_sub, logMoment_sub β α 1 _ _
      (canonC_logMoment_integrable c ρ C₀ L β H h₁ h₂ k₁ k₂ 1 D hβ hρ hk₁ hk₂ hcc hc henv α hα)
      (canonC_logMoment_integrable d ρ C₀' L β H' h₁ h₂ k₁ k₂ 1 D hβ hρ hk₁ hk₂ hdc hd henv' α
        hα)]
  ring

/-- **The difference form for `A_α`.** -/
theorem abs_canonA_sub_le (c d : ℕ × ℕ → ℝ → ℝ) (ρ C₀ C₀' L β r : ℝ) (H H' : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hρ : 0 < ρ) (hr0 : 0 < r) (hrρ : r < ρ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hcc : ∀ ij, Continuous (c ij)) (hdc : ∀ ij, Continuous (d ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (hd : ∀ ij s, |d ij s| * ρ ^ (ij.1 + ij.2) ≤ H' s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (henv' : ∀ s, 0 ≤ s → H' s ≤ C₀' * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    |canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α
        - canonA β h₁ h₂ k₁ k₂ (fun i j s => d (i, j) s) α|
      ≤ cWeight r h₁ h₂ k₁ k₂ α * coeffNorm β α 0 r (fun ij s => c ij s - d ij s) := by
  rw [← canonA_sub c d ρ C₀ C₀' L β H H' h₁ h₂ k₁ k₂ D hβ hρ hk₁ hk₂ hcc hdc hc hd henv henv' α hα]
  exact abs_canonA_le_coeffNorm (fun ij s => c ij s - d ij s) ρ (C₀ + C₀') L β r
    (fun s => H s + H' s) h₁ h₂ k₁ k₂ D hβ hρ hr0 hrρ hk₁ hk₂ (fun ij => (hcc ij).sub (hdc ij))
    (sub_envelope c d ρ hρ H H' hc hd) (sub_henv β L C₀ C₀' D H H' henv henv') α hα

/-- **The difference form for `B_α`.** -/
theorem abs_canonB_sub_le (c d : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ C₀' L β r : ℝ) (H H' : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hC₀ : 0 ≤ C₀) (hC₀' : 0 ≤ C₀')
    (hcc : ∀ ij, Continuous (c ij)) (hdc : ∀ ij, Continuous (d ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (hd : ∀ ij s, |d ij s| * ρ ^ (ij.1 + ij.2) ≤ H' s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (henv' : ∀ s, 0 ≤ s → H' s ≤ C₀' * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    |canonB β b h₁ h₂ k₁ k₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) α
        - canonB β b h₁ h₂ k₁ k₂ (anaFaceU d b) (anaFaceV d b) (fun i j s => d (i, j) s) α|
      ≤ (uWeight b r h₁ h₂ k₁ k₂ α + vWeight b r h₁ h₂ k₁ k₂ α)
          * coeffNorm β α 0 r (fun ij s => c ij s - d ij s)
        + cWeight r h₁ h₂ k₁ k₂ α * coeffNorm β α 1 r (fun ij s => c ij s - d ij s) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  rw [← canonB_sub c d b ρ C₀ C₀' L β H H' h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ hC₀ hC₀' hcc hdc hc hd
    henv henv' α hα]
  exact abs_canonB_le_coeffNorm (fun ij s => c ij s - d ij s) b ρ (C₀ + C₀') L β r
    (fun s => H s + H' s) h₁ h₂ k₁ k₂ D hβ hb hbρ hbr hrρ hk₁ hk₂ (by linarith)
    (fun ij => (hcc ij).sub (hdc ij)) (sub_envelope c d ρ hρ H H' hc hd)
    (sub_henv β L C₀ C₀' D H H' henv henv') α hα

end Laplace.Grammar
