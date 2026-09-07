/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDCutoffReduced

/-!
# Face moments from envelopes (grammar §4.2, higher-order `d = 2`)

The bundled moment hypotheses `FaceMoments` of the cutoff theorem are discharged from polynomial-
exponential envelopes of the Taylor data (Astra #5(c)). The key estimate is the finite-part bound

  `|FP_γ(Ψ(·,s))| ≤ b^{M-γ}/(M-γ) · H(s) + ∑_{m<M} |f_m(s)| |axisPrim γ b m|`

(`axisFinitePart_abs_le`), after which every face coefficient is bounded by a constant times
`(1+s)^D e^{βsa'}` and `moment_integrableOn_of_envelope` applies; the exponents are automatically
positive (`faceExp_pos`). The constructor `faceMoments_of_envelope` removes the opaque
`FaceMoments` assumptions from applications. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- The finite part is bounded by the remainder envelope and the Taylor data. -/
theorem axisFinitePart_abs_le (γ b H : ℝ) (hb : 0 < b) (M : ℕ) (hM : γ < M) (f : ℝ → ℝ)
    (fm : ℕ → ℝ) (hrem : ∀ v ∈ Ioc (0 : ℝ) b, |taylorRem f fm M v| ≤ H * v ^ M) :
    |axisFinitePart γ b f fm M|
      ≤ H / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ)
        + ∑ m ∈ Finset.range M, |fm m| * |axisPrim γ b m| := by
  unfold axisFinitePart regAxisIntegral
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact weighted_taylorRem_tail_le γ b H M hM f fm hrem b hb le_rfl
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul]

/-- The monomial coefficients are scalar multiples of the Taylor data. -/
noncomputable def faceScalar (γ A : ℝ) (k₁ k₂ : ℕ) (m : ℕ) : ℝ :=
  if (m : ℝ) = γ then 1 / ((k₁ : ℝ) * k₂) * Real.log A
  else -(1 / (k₂ : ℝ)) * A ^ (-(((m : ℝ) - γ) / k₁)) / ((m : ℝ) - γ)

theorem faceCoeff_eq_scalar_mul (γ A : ℝ) (k₁ k₂ : ℕ) (f : ℕ → ℝ → ℝ) (m : ℕ) (s : ℝ) :
    faceCoeff γ A k₁ k₂ f m s = faceScalar γ A k₁ k₂ m * f m s := by
  unfold faceCoeff faceScalar
  split_ifs <;> ring

/-- The monomial exponents are positive: `faceExp p₂ γ k₁ m = (m + h₁ + 1)/k₁` for
`γ = k₁ p₂ − h₁ − 1`. -/
theorem faceExp_pos (p₂ : ℝ) (h₁ k₁ : ℕ) (hk₁ : 0 < k₁) (m : ℕ) :
    0 < faceExp p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ m := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  unfold faceExp
  have : p₂ + ((m : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁ = ((m : ℝ) + h₁ + 1) / k₁ := by
    field_simp; ring
  rw [this]
  positivity

/-- Envelope of the log coefficient. -/
theorem faceLogCoeff_abs_le (γ : ℝ) (k₁ k₂ M : ℕ) (f : ℕ → ℝ → ℝ) (s : ℝ) :
    |faceLogCoeff γ k₁ k₂ f M s|
      ≤ ∑ m ∈ Finset.range M, 1 / ((k₁ : ℝ) * k₂) * |f m s| := by
  unfold faceLogCoeff
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  split_ifs
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((k₁ : ℝ) * k₂))]
  · simp only [abs_zero]
    positivity

/-- **`FaceMoments` from envelopes.** If the Taylor data `f_m` and the remainder envelope `H` are
bounded by `C (1+s)^D e^{βsa'}` on `s > 0`, all moment hypotheses of the face transfer hold. -/
theorem faceMoments_of_envelope (β p₂ b a' Cf CH : ℝ) (h₁ k₁ k₂ M D : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₂ : 0 < p₂) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) (f : ℕ → ℝ → ℝ) (hf : ∀ m, Measurable (f m))
    (H : ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ s, 0 ≤ H s) (hγ : (k₁ : ℝ) * p₂ - h₁ - 1 < M)
    (hCH : 0 ≤ CH)
    (hfenv : ∀ m, m < M → ∀ s, 0 < s → |f m s| ≤ Cf * (1 + s) ^ D * Real.exp (β * s * a'))
    (hHenv : ∀ s, 0 < s → H s ≤ CH * (1 + s) ^ D * Real.exp (β * s * a'))
    (hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |Ψ u s - ∑ m ∈ Finset.range M, f m s * u ^ m| ≤ H s * u ^ M) :
    FaceMoments β p₂ b h₁ k₁ k₂ M Ψ f H := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  set γ : ℝ := (k₁ : ℝ) * p₂ - h₁ - 1 with hγdef
  have hMγ : 0 < (M : ℝ) - γ := by linarith
  have ha : 0 < p₂ + ((M : ℝ) - γ) / k₁ := by positivity
  -- the envelope of each coefficient function
  set E : ℝ → ℝ := fun s => (1 + s) ^ D * Real.exp (β * s * a') with hE
  have hE0 : ∀ s, 0 < s → 0 ≤ E s := fun s hs => by simp only [hE]; positivity
  -- monomial coefficients
  have hmono : ∀ m, m < M → ∀ s, 0 < s →
      |faceCoeff γ (b ^ k₂) k₁ k₂ f m s|
        ≤ (|faceScalar γ (b ^ k₂) k₁ k₂ m| * Cf) * (1 + s) ^ D * Real.exp (β * s * a') := by
    intro m hm s hs
    rw [faceCoeff_eq_scalar_mul, abs_mul]
    calc |faceScalar γ (b ^ k₂) k₁ k₂ m| * |f m s|
        ≤ |faceScalar γ (b ^ k₂) k₁ k₂ m| * (Cf * (1 + s) ^ D * Real.exp (β * s * a')) :=
          mul_le_mul_of_nonneg_left (hfenv m hm s hs) (abs_nonneg _)
      _ = _ := by ring
  -- the finite-part coefficient
  set KFP : ℝ := 1 / (k₂ : ℝ) * (CH / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ)
    + ∑ m ∈ Finset.range M, Cf * |axisPrim γ b m|) with hKFP
  have hfp : ∀ s, 0 < s →
      |faceFPCoeff γ b k₂ Ψ f M s| ≤ KFP * (1 + s) ^ D * Real.exp (β * s * a') := by
    intro s hs
    unfold faceFPCoeff
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (k₂ : ℝ))]
    have h1 := axisFinitePart_abs_le γ b (H s) hb M hγ (fun u => Ψ u s) (fun m => f m s)
      (fun u hu => by simpa [taylorRem] using hrem s hs u hu)
    have hE' : 0 ≤ (1 + s) ^ D * Real.exp (β * s * a') := hE0 s hs
    have h2 : H s / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ)
        ≤ CH / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ) * ((1 + s) ^ D * Real.exp (β * s * a')) := by
      have := hHenv s hs
      have hb' : 0 ≤ b ^ ((M : ℝ) - γ) := Real.rpow_nonneg hb.le _
      calc H s / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ)
          ≤ (CH * (1 + s) ^ D * Real.exp (β * s * a')) / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ) := by
            gcongr
        _ = _ := by ring
    have h3 : ∑ m ∈ Finset.range M, |f m s| * |axisPrim γ b m|
        ≤ (∑ m ∈ Finset.range M, Cf * |axisPrim γ b m|)
          * ((1 + s) ^ D * Real.exp (β * s * a')) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun m hm => ?_
      calc |f m s| * |axisPrim γ b m|
          ≤ (Cf * (1 + s) ^ D * Real.exp (β * s * a')) * |axisPrim γ b m| :=
            mul_le_mul_of_nonneg_right (hfenv m (Finset.mem_range.1 hm) s hs) (abs_nonneg _)
        _ = _ := by ring
    calc 1 / (k₂ : ℝ) * |axisFinitePart γ b (fun u => Ψ u s) (fun m => f m s) M|
        ≤ 1 / (k₂ : ℝ) * (CH / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ)
              * ((1 + s) ^ D * Real.exp (β * s * a'))
            + (∑ m ∈ Finset.range M, Cf * |axisPrim γ b m|)
              * ((1 + s) ^ D * Real.exp (β * s * a'))) := by
          gcongr
          linarith [h1, h2, h3]
      _ = _ := by rw [hKFP]; ring
  -- the log coefficient
  set KL : ℝ := (M : ℝ) * (1 / ((k₁ : ℝ) * k₂)) * Cf with hKL
  have hlog : ∀ s, 0 < s →
      |faceLogCoeff γ k₁ k₂ f M s| ≤ KL * (1 + s) ^ D * Real.exp (β * s * a') := by
    intro s hs
    refine (faceLogCoeff_abs_le γ k₁ k₂ M f s).trans ?_
    calc ∑ m ∈ Finset.range M, 1 / ((k₁ : ℝ) * k₂) * |f m s|
        ≤ ∑ _m ∈ Finset.range M, 1 / ((k₁ : ℝ) * k₂) * (Cf * (1 + s) ^ D * Real.exp (β * s * a')) :=
          Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
            (hfenv m (Finset.mem_range.1 hm) s hs) (by positivity)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hKL]; ring
  -- the envelope
  set KE : ℝ := 1 / (k₂ : ℝ) * ((b ^ k₂) ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ)) * CH with hKE
  have hKE0 : 0 ≤ KE := by
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ b ^ k₂) (-(((M : ℝ) - γ) / k₁))
    positivity
  have henv : ∀ s, 0 < s →
      |faceEnv γ (b ^ k₂) k₁ k₂ M H s| ≤ KE * (1 + s) ^ D * Real.exp (β * s * a') := by
    intro s hs
    unfold faceEnv
    have hc0 : 0 ≤ 1 / (k₂ : ℝ) * ((b ^ k₂) ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ)) := by
      have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ b ^ k₂) (-(((M : ℝ) - γ) / k₁))
      positivity
    rw [abs_of_nonneg (mul_nonneg hc0 (hH0 s))]
    calc 1 / (k₂ : ℝ) * ((b ^ k₂) ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ)) * H s
        ≤ 1 / (k₂ : ℝ) * ((b ^ k₂) ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ))
          * (CH * (1 + s) ^ D * Real.exp (β * s * a')) := mul_le_mul_of_nonneg_left (hHenv s hs) hc0
      _ = _ := by rw [hKE]; ring
  have hCmeas := faceC_measurable γ b k₁ k₂ Ψ hΨc f hf M
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases i with m | i
    · simp only [faceα, faceJ, faceC, Sum.elim_inl]
      by_cases hm : m < M
      · exact moment_integrableOn_of_envelope β a' _ _ hβ (by linarith [faceExp_pos p₂ h₁ k₁ hk₁ m])
          0 D _ (hCmeas (Sum.inl m)) (hmono m hm)
      · exact absurd m.isLt hm
    · fin_cases i
      · simpa [faceα, faceJ, faceC] using moment_integrableOn_of_envelope β a' (p₂ - 1) KFP hβ
          (by linarith) 0 D _ (hCmeas (Sum.inr 0)) hfp
      · simpa [faceα, faceJ, faceC] using moment_integrableOn_of_envelope β a' (p₂ - 1) KL hβ
          (by linarith) 1 D _ (hCmeas (Sum.inr 1)) hlog
  · intro i
    rcases i with m | i
    · simp only [faceJ, faceC, Sum.elim_inl]
      exact moment_integrableOn_of_envelope β a' _ _ hβ (by linarith) 0 D _
        (hCmeas (Sum.inl m)) (hmono m m.isLt)
    · fin_cases i
      · simpa [faceJ, faceC] using moment_integrableOn_of_envelope β a' _ KFP hβ (by linarith) 0 D _
          (hCmeas (Sum.inr 0)) hfp
      · simpa [faceJ, faceC] using moment_integrableOn_of_envelope β a' _ KL hβ (by linarith) 1 D _
          (hCmeas (Sum.inr 1)) hlog
  · have hEm : Measurable (faceEnv γ (b ^ k₂) k₁ k₂ M H) := by
      unfold faceEnv; exact measurable_const.mul hH
    have this : IntegrableOn (fun s => s ^ (p₂ + ((M : ℝ) - γ) / k₁ - 1) * (1 + |Real.log s|) ^ 1
        * (Real.exp (-β * s ^ 2) * |faceEnv γ (b ^ k₂) k₁ k₂ M H s|)) (Ioi 0) :=
      moment_integrableOn_of_envelope β a' _ KE hβ (by linarith) 1 D _ hEm henv
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    beta_reduce
    have hnn : 0 ≤ faceEnv γ (b ^ k₂) k₁ k₂ M H s := by
      unfold faceEnv
      have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ b ^ k₂) (-(((M : ℝ) - γ) / k₁))
      exact mul_nonneg (by positivity) (hH0 s)
    rw [abs_of_nonneg hnn]

end Laplace.Grammar
