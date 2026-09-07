/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDCutoffExplicit

/-!
# Envelope bounds for the face transfer constants (grammar §4.2, Astra #9 R5, step 3)

The explicit face constant `faceConst` of unit 131 involves tail moments of the actual face
coefficients. Under the envelope hypotheses of `faceMoments_of_envelope` (Taylor data `f_m` and
remainder envelope `H` bounded by `C (1+s)^D e^{βsa'}`), every face coefficient is bounded
pointwise by an explicit multiple of the Gaussian envelope `gaussEnv β a' D s = (1+s)^D e^{βsa'}`
(`faceCoeff_abs_le_env`, `faceFPCoeff_abs_le_env`, `faceLogCoeff_abs_le_env`,
`faceEnv_abs_le_env`), tail moments are monotone under pointwise envelopes
(`tailMoment_le_of_env`, `envMoment_le_of_env`), and hence

  `faceConst ≤ faceEnvConst · envMoment β q 1 (gaussEnv β a' D)`   (`faceConst_le_env`)

with `faceEnvConst` an explicit function of `(β, p₂, b, a', h₁, k₁, k₂, M, D, Cf, CH)` only. This
is the ingredient that makes the cutoff constant uniform over a family with a common envelope.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- The Gaussian envelope `(1+s)^D e^{βsa'}`. -/
noncomputable def gaussEnv (β a' : ℝ) (D : ℕ) (s : ℝ) : ℝ := (1 + s) ^ D * Real.exp (β * s * a')

theorem gaussEnv_nonneg (β a' : ℝ) (D : ℕ) (s : ℝ) (hs : 0 ≤ s) : 0 ≤ gaussEnv β a' D s := by
  unfold gaussEnv; positivity

theorem gaussEnv_measurable (β a' : ℝ) (D : ℕ) : Measurable (gaussEnv β a' D) := by
  unfold gaussEnv; fun_prop

/-- Integrability of the Gaussian envelope moment integrand. -/
theorem gaussEnv_moment_integrableOn (β a' q : ℝ) (j D : ℕ) (hβ : 0 < β) (hq : 0 < q) :
    IntegrableOn (fun s => s ^ (q - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * gaussEnv β a' D s)) (Ioi 0) := by
  have h := moment_integrableOn_of_envelope β a' (q - 1) 1 hβ (by linarith) j D (gaussEnv β a' D)
    (gaussEnv_measurable β a' D) (fun s hs => by
      rw [abs_of_nonneg (gaussEnv_nonneg β a' D s hs.le), one_mul]; rfl)
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  beta_reduce
  rw [abs_of_nonneg (gaussEnv_nonneg β a' D s (le_of_lt hs))]

/-- **Tail moments are monotone under pointwise Gaussian envelopes.** -/
theorem tailMoment_le_of_env (β a' q K : ℝ) (j D : ℕ) (c : ℝ → ℝ) (hβ : 0 < β) (hq : 0 < q)
    (hc : Measurable c) (henv : ∀ s, 0 < s → |c s| ≤ K * gaussEnv β a' D s) :
    tailMoment β q j c ≤ K * envMoment β q j (gaussEnv β a' D) := by
  unfold tailMoment envMoment
  rw [← integral_const_mul]
  have hint : IntegrableOn (fun s => s ^ (q - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0) :=
    moment_integrableOn_of_envelope β a' (q - 1) K hβ (by linarith) j D c hc
      (fun s hs => by rw [mul_assoc]; exact henv s hs)
  refine setIntegral_mono_on hint ((gaussEnv_moment_integrableOn β a' q j D hβ hq).const_mul K)
    measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  have h1 : 0 ≤ s ^ (q - 1) * (1 + |Real.log s|) ^ j * Real.exp (-β * s ^ 2) := by positivity
  calc s ^ (q - 1) * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|)
      ≤ s ^ (q - 1) * (1 + |Real.log s|) ^ j
          * (Real.exp (-β * s ^ 2) * (K * gaussEnv β a' D s)) := by
        gcongr
        exact henv s hs0
    _ = K * (s ^ (q - 1) * (1 + |Real.log s|) ^ j
          * (Real.exp (-β * s ^ 2) * gaussEnv β a' D s)) := by
        ring

/-- Envelope moments of a nonnegative function are monotone under pointwise envelopes. -/
theorem envMoment_le_of_env (β a' q K : ℝ) (j D : ℕ) (H : ℝ → ℝ) (hβ : 0 < β) (hq : 0 < q)
    (hH : Measurable H) (hH0 : ∀ s, 0 ≤ H s)
    (henv : ∀ s, 0 < s → H s ≤ K * gaussEnv β a' D s) :
    envMoment β q j H ≤ K * envMoment β q j (gaussEnv β a' D) := by
  have h := tailMoment_le_of_env β a' q K j D H hβ hq hH
    (fun s hs => by rw [abs_of_nonneg (hH0 s)]; exact henv s hs)
  unfold tailMoment at h
  unfold envMoment
  refine le_trans (le_of_eq ?_) h
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [abs_of_nonneg (hH0 s)]

/-- The Gaussian envelope moment is monotone in the log degree. -/
theorem envMoment_gauss_mono (β a' q : ℝ) (D : ℕ) (hβ : 0 < β) (hq : 0 < q) :
    envMoment β q 0 (gaussEnv β a' D) ≤ envMoment β q 1 (gaussEnv β a' D) := by
  unfold envMoment
  refine setIntegral_mono_on (gaussEnv_moment_integrableOn β a' q 0 D hβ hq)
    (gaussEnv_moment_integrableOn β a' q 1 D hβ hq) measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  have hg := gaussEnv_nonneg β a' D s hs0.le
  gcongr
  all_goals linarith [abs_nonneg (Real.log s)]

theorem envMoment_gauss_nonneg (β a' q : ℝ) (j D : ℕ) : 0 ≤ envMoment β q j (gaussEnv β a' D) :=
  setIntegral_nonneg measurableSet_Ioi fun s hs => by
    have hs0 : (0 : ℝ) < s := hs
    have := gaussEnv_nonneg β a' D s hs0.le
    positivity

/-- Envelope of the monomial coefficients. -/
theorem faceCoeff_abs_le_env (γ A : ℝ) (k₁ k₂ : ℕ) (f : ℕ → ℝ → ℝ) (m : ℕ) (Cf β a' : ℝ) (D : ℕ)
    (hfenv : ∀ s, 0 < s → |f m s| ≤ Cf * gaussEnv β a' D s) (s : ℝ) (hs : 0 < s) :
    |faceCoeff γ A k₁ k₂ f m s| ≤ |faceScalar γ A k₁ k₂ m| * Cf * gaussEnv β a' D s := by
  rw [faceCoeff_eq_scalar_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hfenv s hs) (abs_nonneg _)

/-- The envelope constant of the finite-part coefficient. -/
noncomputable def fpEnvConst (γ b : ℝ) (k₂ M : ℕ) (Cf CH : ℝ) : ℝ :=
  1 / (k₂ : ℝ) * (CH / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ)
    + ∑ m ∈ Finset.range M, Cf * |axisPrim γ b m|)

/-- Envelope of the finite-part coefficient. -/
theorem faceFPCoeff_abs_le_env (γ b : ℝ) (hb : 0 < b) (k₂ M : ℕ) (hk₂ : 0 < k₂) (hγ : γ < M)
    (Ψ : ℝ → ℝ → ℝ)
    (f : ℕ → ℝ → ℝ) (H : ℝ → ℝ) (Cf CH β a' : ℝ) (D : ℕ)
    (hfenv : ∀ m, m < M → ∀ s, 0 < s → |f m s| ≤ Cf * gaussEnv β a' D s)
    (hHenv : ∀ s, 0 < s → H s ≤ CH * gaussEnv β a' D s)
    (hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |Ψ u s - ∑ m ∈ Finset.range M, f m s * u ^ m| ≤ H s * u ^ M) (s : ℝ) (hs : 0 < s) :
    |faceFPCoeff γ b k₂ Ψ f M s| ≤ fpEnvConst γ b k₂ M Cf CH * gaussEnv β a' D s := by
  have hMγ : 0 < (M : ℝ) - γ := by linarith
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hE' : 0 ≤ gaussEnv β a' D s := gaussEnv_nonneg β a' D s hs.le
  unfold faceFPCoeff fpEnvConst
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (k₂ : ℝ))]
  have h1 := axisFinitePart_abs_le γ b (H s) hb M hγ (fun u => Ψ u s) (fun m => f m s)
    (fun u hu => by simpa [taylorRem] using hrem s hs u hu)
  have h2 : H s / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ)
      ≤ CH / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ) * gaussEnv β a' D s := by
    have := hHenv s hs
    have hb' : 0 ≤ b ^ ((M : ℝ) - γ) := Real.rpow_nonneg hb.le _
    calc H s / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ)
        ≤ (CH * gaussEnv β a' D s) / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ) := by gcongr
      _ = _ := by ring
  have h3 : ∑ m ∈ Finset.range M, |f m s| * |axisPrim γ b m|
      ≤ (∑ m ∈ Finset.range M, Cf * |axisPrim γ b m|) * gaussEnv β a' D s := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    calc |f m s| * |axisPrim γ b m|
        ≤ (Cf * gaussEnv β a' D s) * |axisPrim γ b m| :=
          mul_le_mul_of_nonneg_right (hfenv m (Finset.mem_range.1 hm) s hs) (abs_nonneg _)
      _ = _ := by ring
  calc 1 / (k₂ : ℝ) * |axisFinitePart γ b (fun u => Ψ u s) (fun m => f m s) M|
      ≤ 1 / (k₂ : ℝ) * (CH / ((M : ℝ) - γ) * b ^ ((M : ℝ) - γ) * gaussEnv β a' D s
          + (∑ m ∈ Finset.range M, Cf * |axisPrim γ b m|) * gaussEnv β a' D s) := by
        gcongr
        linarith [h1, h2, h3]
    _ = _ := by ring

/-- Envelope of the log coefficient. -/
theorem faceLogCoeff_abs_le_env (γ : ℝ) (k₁ k₂ M : ℕ) (f : ℕ → ℝ → ℝ) (Cf β a' : ℝ) (D : ℕ)
    (hfenv : ∀ m, m < M → ∀ s, 0 < s → |f m s| ≤ Cf * gaussEnv β a' D s) (s : ℝ) (hs : 0 < s) :
    |faceLogCoeff γ k₁ k₂ f M s| ≤ (M : ℝ) * (1 / ((k₁ : ℝ) * k₂)) * Cf * gaussEnv β a' D s := by
  refine (faceLogCoeff_abs_le γ k₁ k₂ M f s).trans ?_
  calc ∑ m ∈ Finset.range M, 1 / ((k₁ : ℝ) * k₂) * |f m s|
      ≤ ∑ _m ∈ Finset.range M, 1 / ((k₁ : ℝ) * k₂) * (Cf * gaussEnv β a' D s) :=
        Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
          (hfenv m (Finset.mem_range.1 hm) s hs) (by positivity)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The envelope constant of the remainder envelope `faceEnv`. -/
noncomputable def envEnvConst (γ A : ℝ) (k₁ k₂ M : ℕ) (CH : ℝ) : ℝ :=
  1 / (k₂ : ℝ) * (A ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ)) * CH

theorem faceEnv_nonneg (γ A : ℝ) (hA : 0 < A) (k₁ k₂ M : ℕ) (hγ : γ < M) (H : ℝ → ℝ)
    (hH0 : ∀ s, 0 ≤ H s) (s : ℝ) : 0 ≤ faceEnv γ A k₁ k₂ M H s := by
  unfold faceEnv
  have hMγ : 0 < (M : ℝ) - γ := by linarith
  have := Real.rpow_nonneg hA.le (-(((M : ℝ) - γ) / k₁))
  exact mul_nonneg (by positivity) (hH0 s)

theorem faceEnv_le_env (γ A : ℝ) (hA : 0 < A) (k₁ k₂ M : ℕ) (hγ : γ < M) (H : ℝ → ℝ)
    (CH β a' : ℝ) (D : ℕ) (hHenv : ∀ s, 0 < s → H s ≤ CH * gaussEnv β a' D s) (s : ℝ)
    (hs : 0 < s) :
    faceEnv γ A k₁ k₂ M H s ≤ envEnvConst γ A k₁ k₂ M CH * gaussEnv β a' D s := by
  unfold faceEnv envEnvConst
  have hMγ : 0 < (M : ℝ) - γ := by linarith
  have hc0 : 0 ≤ 1 / (k₂ : ℝ) * (A ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ)) := by
    have := Real.rpow_nonneg hA.le (-(((M : ℝ) - γ) / k₁))
    positivity
  calc 1 / (k₂ : ℝ) * (A ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ)) * H s
      ≤ 1 / (k₂ : ℝ) * (A ^ (-(((M : ℝ) - γ) / k₁)) / ((M : ℝ) - γ)) * (CH * gaussEnv β a' D s) :=
        mul_le_mul_of_nonneg_left (hHenv s hs) hc0
    _ = _ := by ring

/-- The per-index envelope constants of the face coefficients `faceC`. -/
noncomputable def faceCEnv (γ b : ℝ) (k₁ k₂ M : ℕ) (Cf CH : ℝ) : Fin M ⊕ Fin 2 → ℝ :=
  Sum.elim (fun m => |faceScalar γ (b ^ k₂) k₁ k₂ m| * Cf)
    ![fpEnvConst γ b k₂ M Cf CH, (M : ℝ) * (1 / ((k₁ : ℝ) * k₂)) * Cf]

theorem faceCEnv_nonneg (γ b : ℝ) (hb : 0 < b) (k₂ M : ℕ) (hγ : γ < M) (k₁ : ℕ) (Cf CH : ℝ)
    (hCf : 0 ≤ Cf) (hCH : 0 ≤ CH) (i : Fin M ⊕ Fin 2) : 0 ≤ faceCEnv γ b k₁ k₂ M Cf CH i := by
  have hMγ : 0 < (M : ℝ) - γ := by linarith
  rcases i with m | i
  · simp only [faceCEnv, Sum.elim_inl]; positivity
  · fin_cases i
    · show 0 ≤ fpEnvConst γ b k₂ M Cf CH
      unfold fpEnvConst
      have h1 : 0 ≤ ∑ m ∈ Finset.range M, Cf * |axisPrim γ b m| :=
        Finset.sum_nonneg fun m _ => by positivity
      have h2 : 0 ≤ b ^ ((M : ℝ) - γ) := Real.rpow_nonneg hb.le _
      have h3 : 0 ≤ CH / ((M : ℝ) - γ) := div_nonneg hCH hMγ.le
      exact mul_nonneg (by positivity) (add_nonneg (mul_nonneg h3 h2) h1)
    · show 0 ≤ (M : ℝ) * (1 / ((k₁ : ℝ) * k₂)) * Cf
      positivity

/-- Envelope of every face coefficient. -/
theorem faceC_abs_le_env (γ b : ℝ) (hb : 0 < b) (k₁ k₂ M : ℕ) (hk₂ : 0 < k₂) (hγ : γ < M)
    (Ψ : ℝ → ℝ → ℝ)
    (f : ℕ → ℝ → ℝ) (H : ℝ → ℝ) (Cf CH β a' : ℝ) (D : ℕ)
    (hfenv : ∀ m, m < M → ∀ s, 0 < s → |f m s| ≤ Cf * gaussEnv β a' D s)
    (hHenv : ∀ s, 0 < s → H s ≤ CH * gaussEnv β a' D s)
    (hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |Ψ u s - ∑ m ∈ Finset.range M, f m s * u ^ m| ≤ H s * u ^ M) (i : Fin M ⊕ Fin 2) (s : ℝ)
    (hs : 0 < s) :
    |faceC γ b k₁ k₂ Ψ f M i s| ≤ faceCEnv γ b k₁ k₂ M Cf CH i * gaussEnv β a' D s := by
  rcases i with m | i
  · simp only [faceC, faceCEnv, Sum.elim_inl]
    exact faceCoeff_abs_le_env γ (b ^ k₂) k₁ k₂ f m Cf β a' D (hfenv m m.isLt) s hs
  · fin_cases i
    · show |faceFPCoeff γ b k₂ Ψ f M s| ≤ fpEnvConst γ b k₂ M Cf CH * gaussEnv β a' D s
      exact faceFPCoeff_abs_le_env γ b hb k₂ M hk₂ hγ Ψ f H Cf CH β a' D hfenv hHenv hrem s hs
    · show |faceLogCoeff γ k₁ k₂ f M s|
        ≤ (M : ℝ) * (1 / ((k₁ : ℝ) * k₂)) * Cf * gaussEnv β a' D s
      exact faceLogCoeff_abs_le_env γ k₁ k₂ M f Cf β a' D hfenv s hs

/-- **The envelope-only face constant.** -/
noncomputable def faceEnvConst (p₂ b : ℝ) (h₁ k₁ k₂ M : ℕ) (Cf CH : ℝ) : ℝ :=
  envEnvConst ((k₁ : ℝ) * p₂ - h₁ - 1) (b ^ k₂) k₁ k₂ M CH
    + ∑ i, (b ^ (k₁ + k₂)) ^ (faceα p₂ ((k₁ : ℝ) * p₂ - h₁ - 1) k₁ M i
        - (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁))
      * faceCEnv ((k₁ : ℝ) * p₂ - h₁ - 1) b k₁ k₂ M Cf CH i

/-- **The face transfer constant is bounded by envelope data times one Gaussian moment.** -/
theorem faceConst_le_env (β p₂ b a' Cf CH : ℝ) (h₁ k₁ k₂ M D : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₂ : 0 < p₂) (Ψ : ℝ → ℝ → ℝ)
    (hΨc : Continuous (Function.uncurry Ψ)) (f : ℕ → ℝ → ℝ) (hf : ∀ m, Measurable (f m))
    (H : ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ s, 0 ≤ H s) (hγ : (k₁ : ℝ) * p₂ - h₁ - 1 < M)
    (hCf : 0 ≤ Cf) (hCH : 0 ≤ CH)
    (hfenv : ∀ m, m < M → ∀ s, 0 < s → |f m s| ≤ Cf * gaussEnv β a' D s)
    (hHenv : ∀ s, 0 < s → H s ≤ CH * gaussEnv β a' D s)
    (hrem : ∀ s, 0 < s → ∀ u ∈ Ioc (0 : ℝ) b,
      |Ψ u s - ∑ m ∈ Finset.range M, f m s * u ^ m| ≤ H s * u ^ M) :
    faceConst β p₂ b h₁ k₁ k₂ M Ψ f H
      ≤ faceEnvConst p₂ b h₁ k₁ k₂ M Cf CH
        * envMoment β (p₂ + ((M : ℝ) - ((k₁ : ℝ) * p₂ - h₁ - 1)) / k₁) 1 (gaussEnv β a' D) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  set γ : ℝ := (k₁ : ℝ) * p₂ - h₁ - 1 with hγdef
  set q : ℝ := p₂ + ((M : ℝ) - γ) / k₁ with hqdef
  have hMγ : 0 < (M : ℝ) - γ := by linarith
  have hq : 0 < q := by positivity
  have hA : 0 < b ^ k₂ := by positivity
  set G : ℝ := envMoment β q 1 (gaussEnv β a' D) with hG
  have hG0 : 0 ≤ G := envMoment_gauss_nonneg β a' q 1 D
  -- the envelope term
  have hEnvm : Measurable (faceEnv γ (b ^ k₂) k₁ k₂ M H) := by
    unfold faceEnv; exact measurable_const.mul hH
  have h1 : envMoment β q 1 (faceEnv γ (b ^ k₂) k₁ k₂ M H)
      ≤ envEnvConst γ (b ^ k₂) k₁ k₂ M CH * G :=
    envMoment_le_of_env β a' q _ 1 D _ hβ hq hEnvm
      (faceEnv_nonneg γ (b ^ k₂) hA k₁ k₂ M hγ H hH0)
      (faceEnv_le_env γ (b ^ k₂) hA k₁ k₂ M hγ H CH β a' D hHenv)
  -- the tail terms
  have hCmeas := faceC_measurable γ b k₁ k₂ Ψ hΨc f hf M
  have h2 : ∀ i, tailMoment β q (faceJ M i) (faceC γ b k₁ k₂ Ψ f M i)
      ≤ faceCEnv γ b k₁ k₂ M Cf CH i * G := by
    intro i
    have hK := faceCEnv_nonneg γ b hb k₂ M hγ k₁ Cf CH hCf hCH i
    refine (tailMoment_le_of_env β a' q _ (faceJ M i) D _ hβ hq (hCmeas i)
      (faceC_abs_le_env γ b hb k₁ k₂ M hk₂ hγ Ψ f H Cf CH β a' D hfenv hHenv hrem i)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    rcases i with m | i
    · simp only [faceJ, Sum.elim_inl]
      exact envMoment_gauss_mono β a' q D hβ hq
    · fin_cases i
      · exact envMoment_gauss_mono β a' q D hβ hq
      · exact le_rfl
  unfold faceConst faceEnvConst
  rw [add_mul, Finset.sum_mul]
  refine add_le_add h1 (Finset.sum_le_sum fun i _ => ?_)
  have hw : 0 ≤ (b ^ (k₁ + k₂)) ^ (faceα p₂ γ k₁ M i - q) := Real.rpow_nonneg (by positivity) _
  calc (b ^ (k₁ + k₂)) ^ (faceα p₂ γ k₁ M i - q)
        * tailMoment β q (faceJ M i) (faceC γ b k₁ k₂ Ψ f M i)
      ≤ (b ^ (k₁ + k₂)) ^ (faceα p₂ γ k₁ M i - q) * (faceCEnv γ b k₁ k₂ M Cf CH i * G) :=
        mul_le_mul_of_nonneg_left (h2 i) hw
    _ = _ := by ring

end Laplace.Grammar
