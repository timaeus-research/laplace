/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CanonParamMeasurable

/-!
# Weighted-norm bounds for the canonical coefficients (grammar §4.2, Astra #10 rank 4 / R6)

The weighted coefficient norm at exponent `α`, log degree `ℓ` and radius `r`:

  `coeffNorm β α ℓ r c = ∑_{ij} r^{i+j} · ∫₀^∞ s^{α−1}(1+|log s|)^ℓ e^{−βs²} |c_ij(s)| ds`.

For `b < r < ρ` and `c` in the envelope class the norm is finite (`coeffNorm_summable`) and the
canonical coefficients are bounded by it: `|A_α(c)| ≤ cWeight α · coeffNorm β α 0 r c` and
`|B_α(c)| ≤ (uWeight α + vWeight α) · coeffNorm β α 0 r c + cWeight α · coeffNorm β α 1 r c`
(`abs_canonA_le_coeffNorm`, `abs_canonB_le_coeffNorm`), with weights depending only on
`(α, b, r, h, k)`. The face multipliers obey `|axisPrim γ b j| ≤ axisPrimGeomConst γ b · b^j`
(`abs_axisPrim_le_geom`), which is what makes the face series a bounded functional of the weighted
row. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

theorem tailMoment_nonneg (β a : ℝ) (j : ℕ) (c : ℝ → ℝ) : 0 ≤ tailMoment β a j c :=
  setIntegral_nonneg measurableSet_Ioi fun s hs => tailMoment_integrand_nonneg a j c β s hs

theorem tailMoment_zero_fun (β a : ℝ) (j : ℕ) : tailMoment β a j (fun _ => (0 : ℝ)) = 0 := by
  simp [tailMoment]

theorem tailMoment_div_const (β a : ℝ) (j : ℕ) (c : ℝ → ℝ) (k : ℝ) (hk : 0 < k) :
    tailMoment β a j (fun s => c s / k) = tailMoment β a j c / k := by
  unfold tailMoment
  rw [← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [abs_div, abs_of_pos hk]
  ring

/-- **The weighted coefficient norm.** -/
noncomputable def coeffNorm (β α : ℝ) (ℓ : ℕ) (r : ℝ) (c : ℕ × ℕ → ℝ → ℝ) : ℝ :=
  ∑' ij : ℕ × ℕ, r ^ (ij.1 + ij.2) * tailMoment β α ℓ (c ij)

theorem coeffNorm_nonneg (β α : ℝ) (ℓ : ℕ) (r : ℝ) (hr : 0 ≤ r) (c : ℕ × ℕ → ℝ → ℝ) :
    0 ≤ coeffNorm β α ℓ r c :=
  tsum_nonneg fun _ => mul_nonneg (pow_nonneg hr _) (tailMoment_nonneg _ _ _ _)

/-- The tail integrand of `c_ij` is integrable under the envelope. -/
theorem tail_integrable_of_env (c : ℕ × ℕ → ℝ → ℝ) (ρ C₀ L β α : ℝ) (H : ℝ → ℝ) (ℓ D : ℕ)
    (hβ : 0 < β) (hα : 0 < α) (hρ : 0 < ρ) (hcc : ∀ ij, Continuous (c ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (ij : ℕ × ℕ) :
    IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ ℓ
      * (Real.exp (-β * s ^ 2) * |c ij s|)) (Ioi 0) :=
  moment_integrableOn_of_envelope β L (α - 1) (C₀ * (ρ ^ (ij.1 + ij.2))⁻¹) hβ (by linarith) ℓ D
    (c ij) (hcc ij).measurable fun s hs => by
      have h := anaCoeff_abs_le c ρ H hρ hc ij s
      calc |c ij s| ≤ H s * (ρ ^ (ij.1 + ij.2))⁻¹ := h
        _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) * (ρ ^ (ij.1 + ij.2))⁻¹ :=
            mul_le_mul_of_nonneg_right (henv s hs.le) (by positivity)
        _ = _ := by ring

/-- Under the envelope each tail moment is controlled by a Gaussian moment. -/
theorem tailMoment_le_env_coeff (c : ℕ × ℕ → ℝ → ℝ) (ρ C₀ L β α : ℝ) (H : ℝ → ℝ) (ℓ D : ℕ)
    (hβ : 0 < β) (hα : 0 < α) (hρ : 0 < ρ) (hcc : ∀ ij, Continuous (c ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (ij : ℕ × ℕ) :
    tailMoment β α ℓ (c ij)
      ≤ (ρ ^ (ij.1 + ij.2))⁻¹ * C₀ * envMoment β α ℓ (gaussEnv β L D) := by
  refine tailMoment_le_of_env β L α _ ℓ D (c ij) hβ hα (hcc ij).measurable fun s hs => ?_
  have h := anaCoeff_abs_le c ρ H hρ hc ij s
  calc |c ij s| ≤ H s * (ρ ^ (ij.1 + ij.2))⁻¹ := h
    _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) * (ρ ^ (ij.1 + ij.2))⁻¹ :=
        mul_le_mul_of_nonneg_right (henv s hs.le) (by positivity)
    _ = _ := by unfold gaussEnv; ring

/-- **The weighted norm is finite on the envelope class** for `r < ρ`. -/
theorem coeffNorm_summable (c : ℕ × ℕ → ℝ → ℝ) (ρ C₀ L β α r : ℝ) (H : ℝ → ℝ) (ℓ D : ℕ)
    (hβ : 0 < β) (hα : 0 < α) (hρ : 0 < ρ) (hr0 : 0 ≤ r) (hrρ : r < ρ)
    (hcc : ∀ ij, Continuous (c ij)) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) :
    Summable fun ij : ℕ × ℕ => r ^ (ij.1 + ij.2) * tailMoment β α ℓ (c ij) := by
  have hθ0 : 0 ≤ r / ρ := by positivity
  have hθ1 : r / ρ < 1 := (div_lt_one hρ).2 hrρ
  refine Summable.of_nonneg_of_le
    (fun ij => mul_nonneg (by positivity) (tailMoment_nonneg _ _ _ _)) (fun ij => ?_)
    ((summable_geom_prod (r / ρ) hθ0 hθ1).mul_right (C₀ * envMoment β α ℓ (gaussEnv β L D)))
  have h := tailMoment_le_env_coeff c ρ C₀ L β α H ℓ D hβ hα hρ hcc hc henv ij
  calc r ^ (ij.1 + ij.2) * tailMoment β α ℓ (c ij)
      ≤ r ^ (ij.1 + ij.2) * ((ρ ^ (ij.1 + ij.2))⁻¹ * C₀ * envMoment β α ℓ (gaussEnv β L D)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (r / ρ) ^ ij.1 * (r / ρ) ^ ij.2 * (C₀ * envMoment β α ℓ (gaussEnv β L D)) := by
        rw [← pow_add, div_pow, div_eq_mul_inv]; ring

/-- A single weighted tail moment is at most the norm. -/
theorem term_le_coeffNorm (c : ℕ × ℕ → ℝ → ℝ) (ρ C₀ L β α r : ℝ) (H : ℝ → ℝ) (ℓ D : ℕ)
    (hβ : 0 < β) (hα : 0 < α) (hρ : 0 < ρ) (hr0 : 0 ≤ r) (hrρ : r < ρ)
    (hcc : ∀ ij, Continuous (c ij)) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (ij : ℕ × ℕ) :
    r ^ (ij.1 + ij.2) * tailMoment β α ℓ (c ij) ≤ coeffNorm β α ℓ r c :=
  (coeffNorm_summable c ρ C₀ L β α r H ℓ D hβ hα hρ hr0 hrρ hcc hc henv).le_tsum ij
    fun _ _ => mul_nonneg (pow_nonneg hr0 _) (tailMoment_nonneg _ _ _ _)

/-- The geometric multiplier constant of the finite-part weights. -/
noncomputable def axisPrimGeomConst (γ b : ℝ) : ℝ :=
  b ^ (-γ) / ((canonicalM γ : ℝ) - γ)
    + ∑ m ∈ Finset.range (canonicalM γ), |axisPrim γ b m| / b ^ m

theorem axisPrimGeomConst_nonneg (γ b : ℝ) (hb : 0 < b) : 0 ≤ axisPrimGeomConst γ b := by
  unfold axisPrimGeomConst
  have := lt_canonicalM γ
  have h1 : 0 ≤ b ^ (-γ) / ((canonicalM γ : ℝ) - γ) :=
    div_nonneg (Real.rpow_nonneg hb.le _) (by linarith)
  exact add_nonneg h1 (Finset.sum_nonneg fun m _ => by positivity)

/-- **Geometric bound on the finite-part weights**: `|axisPrim γ b j| ≤ C_γ b^j`. -/
theorem abs_axisPrim_le_geom (γ b : ℝ) (hb : 0 < b) (j : ℕ) :
    |axisPrim γ b j| ≤ axisPrimGeomConst γ b * b ^ j := by
  set J := canonicalM γ with hJ
  have hJγ : γ < J := lt_canonicalM γ
  have hbj : 0 < b ^ j := pow_pos hb j
  unfold axisPrimGeomConst
  by_cases hj : j < J
  · have h1 : |axisPrim γ b j| / b ^ j ≤ ∑ m ∈ Finset.range J, |axisPrim γ b m| / b ^ m :=
      Finset.single_le_sum (f := fun m => |axisPrim γ b m| / b ^ m) (fun m _ => by positivity)
        (Finset.mem_range.2 hj)
    have h2 : 0 ≤ b ^ (-γ) / ((J : ℝ) - γ) := div_nonneg (Real.rpow_nonneg hb.le _) (by linarith)
    calc |axisPrim γ b j| = |axisPrim γ b j| / b ^ j * b ^ j := by field_simp
      _ ≤ (∑ m ∈ Finset.range J, |axisPrim γ b m| / b ^ m) * b ^ j :=
          mul_le_mul_of_nonneg_right h1 hbj.le
      _ ≤ (b ^ (-γ) / ((J : ℝ) - γ) + ∑ m ∈ Finset.range J, |axisPrim γ b m| / b ^ m) * b ^ j := by
          gcongr
          linarith
  · push Not at hj
    have h := abs_axisPrim_le γ b hb J j hJγ hj
    have h2 : 0 ≤ ∑ m ∈ Finset.range J, |axisPrim γ b m| / b ^ m :=
      Finset.sum_nonneg fun m _ => by positivity
    calc |axisPrim γ b j| ≤ b ^ j * b ^ (-γ) / ((J : ℝ) - γ) := h
      _ = b ^ (-γ) / ((J : ℝ) - γ) * b ^ j := by ring
      _ ≤ (b ^ (-γ) / ((J : ℝ) - γ) + ∑ m ∈ Finset.range J, |axisPrim γ b m| / b ^ m) * b ^ j := by
          gcongr
          linarith

/-- The collision weight `1/(k₁k₂ r^{i+j})` (zero off collisions). -/
noncomputable def cWeight (r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) : ℝ :=
  if uExp h₁ k₁ (uIdx h₁ k₁ α) = α ∧ vExp h₂ k₂ (vIdx h₂ k₂ α) = α then
    1 / ((k₁ : ℝ) * k₂ * r ^ (uIdx h₁ k₁ α + vIdx h₂ k₂ α))
  else 0

/-- The `u`-face weight `C_{γ_α} /(k₁ r^{i})` (zero off `u`-poles). -/
noncomputable def uWeight (b r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) : ℝ :=
  if uExp h₁ k₁ (uIdx h₁ k₁ α) = α then
    axisPrimGeomConst ((k₂ : ℝ) * α - h₂ - 1) b / ((k₁ : ℝ) * r ^ uIdx h₁ k₁ α)
  else 0

noncomputable def vWeight (b r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) : ℝ :=
  if vExp h₂ k₂ (vIdx h₂ k₂ α) = α then
    axisPrimGeomConst ((k₁ : ℝ) * α - h₁ - 1) b / ((k₂ : ℝ) * r ^ vIdx h₂ k₂ α)
  else 0

/-- The collision moment is bounded by the weighted norm. -/
theorem abs_logMoment_canonC_le (c : ℕ × ℕ → ℝ → ℝ) (ρ C₀ L β r : ℝ) (H : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ ℓ D : ℕ) (hβ : 0 < β) (hρ : 0 < ρ) (hr0 : 0 < r) (hrρ : r < ρ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hcc : ∀ ij, Continuous (c ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    |logMoment β α ℓ (canonC h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α)|
      ≤ cWeight r h₁ h₂ k₁ k₂ α * coeffNorm β α ℓ r c := by
  have hk : (0 : ℝ) < (k₁ : ℝ) * k₂ := by positivity
  have hCN := coeffNorm_nonneg β α ℓ r hr0.le c
  unfold canonC cWeight
  split_ifs with hP
  · set i := uIdx h₁ k₁ α
    set j := vIdx h₂ k₂ α
    have hri : 0 < r ^ (i + j) := pow_pos hr0 _
    have hint := tail_integrable_of_env c ρ C₀ L β α H ℓ D hβ hα hρ hcc hc henv (i, j)
    have hdiv : IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ ℓ
        * (Real.exp (-β * s ^ 2) * |c (i, j) s|) / ((k₁ : ℝ) * k₂)) (Ioi 0) :=
      hint.div_const _
    have hint' : IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ ℓ
        * (Real.exp (-β * s ^ 2) * |c (i, j) s / ((k₁ : ℝ) * k₂)|)) (Ioi 0) := by
      refine hdiv.congr_fun (fun s _ => ?_) measurableSet_Ioi
      rw [abs_div, abs_of_pos hk]
      ring
    have h1 := abs_logMoment_le_tailMoment β α ℓ (fun s => c (i, j) s / ((k₁ : ℝ) * k₂))
      ((hcc (i, j)).div_const _).measurable hint'
    rw [tailMoment_div_const β α ℓ (c (i, j)) _ hk] at h1
    have h2 := term_le_coeffNorm c ρ C₀ L β α r H ℓ D hβ hα hρ hr0.le hrρ hcc hc henv (i, j)
    simp only at h2
    calc _ ≤ tailMoment β α ℓ (c (i, j)) / ((k₁ : ℝ) * k₂) := h1
      _ ≤ coeffNorm β α ℓ r c / r ^ (i + j) / ((k₁ : ℝ) * k₂) := by
          gcongr
          rw [le_div_iff₀ hri]
          linarith [h2]
      _ = 1 / ((k₁ : ℝ) * k₂ * r ^ (i + j)) * coeffNorm β α ℓ r c := by
          field_simp
  · rw [logMoment_zero_fun, abs_zero, zero_mul]

/-- The canonical `u`-face moment is bounded by the weighted norm. -/
theorem abs_logMoment_canonU_le (c : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ L β r : ℝ) (H : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ ℓ D : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ)
    (hk₁ : 0 < k₁) (hC₀ : 0 ≤ C₀) (hcc : ∀ ij, Continuous (c ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) :
    |logMoment β α ℓ (canonU b h₁ h₂ k₁ k₂ (anaFaceU c b) (fun i j s => c (i, j) s) α)|
      ≤ uWeight b r h₁ h₂ k₁ k₂ α * coeffNorm β α ℓ r c := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  unfold uWeight
  split_ifs with hP
  · obtain ⟨i, rfl⟩ : ∃ i, uExp h₁ k₁ i = α := ⟨_, hP⟩
    rw [uIdx_uExp h₁ k₁ hk₁ i]
    set α := uExp h₁ k₁ i with hαdef
    have hα : 0 < α := by simp only [hαdef, uExp]; positivity
    set γ : ℝ := (k₂ : ℝ) * α - h₂ - 1 with hγ
    set C := axisPrimGeomConst γ b with hC
    have hC0 := axisPrimGeomConst_nonneg γ b hb
    have hri : 0 < r ^ i := pow_pos hr0 i
    -- the series formula
    have hS := logMoment_canonU_series β b ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ c hcc H hc hC₀ henv
      ℓ i
    rw [hS.2]
    -- termwise bounds
    have hterm : ∀ j : ℕ, |axisPrim γ b j * logMoment β α ℓ (c (i, j))|
        ≤ C / r ^ i * (r ^ (i + j) * tailMoment β α ℓ (c (i, j))) := by
      intro j
      rw [abs_mul]
      have h1 := abs_axisPrim_le_geom γ b hb j
      have h2 := abs_logMoment_le_tailMoment β α ℓ (c (i, j)) (hcc (i, j)).measurable
        (tail_integrable_of_env c ρ C₀ L β α H ℓ D hβ hα hρ hcc hc henv (i, j))
      have hbr' : b ^ j ≤ r ^ j := pow_le_pow_left₀ hb.le hbr.le j
      calc |axisPrim γ b j| * |logMoment β α ℓ (c (i, j))|
          ≤ (C * b ^ j) * tailMoment β α ℓ (c (i, j)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ (C * r ^ j) * tailMoment β α ℓ (c (i, j)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbr' hC0)
              (tailMoment_nonneg _ _ _ _)
        _ = C / r ^ i * (r ^ (i + j) * tailMoment β α ℓ (c (i, j))) := by
            rw [pow_add]; field_simp
    have hsumG := coeffNorm_summable c ρ C₀ L β α r H ℓ D hβ hα hρ hr0.le hrρ hcc hc henv
    have hrow : Summable fun j : ℕ => r ^ (i + j) * tailMoment β α ℓ (c (i, j)) :=
      hsumG.prod_factor i
    have hrow' : Summable fun j : ℕ => C / r ^ i * (r ^ (i + j) * tailMoment β α ℓ (c (i, j))) :=
      hrow.mul_left (C / r ^ i)
    have habs : Summable fun j : ℕ => ‖axisPrim γ b j * logMoment β α ℓ (c (i, j))‖ :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _)
        (fun j => by rw [Real.norm_eq_abs]; exact hterm j) hrow'
    have hrow_le : ∑' j : ℕ, r ^ (i + j) * tailMoment β α ℓ (c (i, j)) ≤ coeffNorm β α ℓ r c :=
      hrow.tsum_le_tsum_of_inj (fun j => (i, j)) (Prod.mk_right_injective i)
        (fun ij _ => mul_nonneg (pow_nonneg hr0.le _) (tailMoment_nonneg _ _ _ _))
        (fun j => le_rfl) hsumG
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (k₁ : ℝ))]
    calc 1 / (k₁ : ℝ) * |∑' j : ℕ, axisPrim γ b j * logMoment β α ℓ (c (i, j))|
        ≤ 1 / (k₁ : ℝ) * ∑' j : ℕ, ‖axisPrim γ b j * logMoment β α ℓ (c (i, j))‖ := by
          gcongr
          rw [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm habs
      _ ≤ 1 / (k₁ : ℝ) * ∑' j : ℕ, C / r ^ i * (r ^ (i + j) * tailMoment β α ℓ (c (i, j))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact habs.tsum_le_tsum (fun j => by rw [Real.norm_eq_abs]; exact hterm j) hrow'
      _ = 1 / (k₁ : ℝ) * (C / r ^ i * ∑' j : ℕ, r ^ (i + j) * tailMoment β α ℓ (c (i, j))) := by
          rw [tsum_mul_left]
      _ ≤ 1 / (k₁ : ℝ) * (C / r ^ i * coeffNorm β α ℓ r c) := by
          gcongr
      _ = C / ((k₁ : ℝ) * r ^ i) * coeffNorm β α ℓ r c := by
          field_simp
  · have hno : ∀ i, uExp h₁ k₁ i ≠ α := fun i h => hP (by rw [← h, uIdx_uExp h₁ k₁ hk₁ i])
    rw [canonU_of_not b h₁ h₂ k₁ k₂ _ _ α hno, logMoment_zero_fun, abs_zero, zero_mul]

/-- The canonical `v`-face moment is bounded by the weighted norm. -/
theorem abs_logMoment_canonV_le (c : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ L β r : ℝ) (H : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ ℓ D : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ)
    (hk₂ : 0 < k₂) (hC₀ : 0 ≤ C₀) (hcc : ∀ ij, Continuous (c ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) :
    |logMoment β α ℓ (canonV b h₁ h₂ k₁ k₂ (anaFaceV c b) (fun i j s => c (i, j) s) α)|
      ≤ vWeight b r h₁ h₂ k₁ k₂ α * coeffNorm β α ℓ r c := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  unfold vWeight
  split_ifs with hP
  · obtain ⟨j, rfl⟩ : ∃ j, vExp h₂ k₂ j = α := ⟨_, hP⟩
    rw [vIdx_vExp h₂ k₂ hk₂ j]
    set α := vExp h₂ k₂ j with hαdef
    have hα : 0 < α := by simp only [hαdef, vExp]; positivity
    set γ : ℝ := (k₁ : ℝ) * α - h₁ - 1 with hγ
    set C := axisPrimGeomConst γ b with hC
    have hC0 := axisPrimGeomConst_nonneg γ b hb
    have hrj : 0 < r ^ j := pow_pos hr0 j
    have hS := logMoment_canonV_series β b ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₂ c hcc H hc hC₀ henv
      ℓ j
    rw [hS.2]
    have hterm : ∀ i : ℕ, |axisPrim γ b i * logMoment β α ℓ (c (i, j))|
        ≤ C / r ^ j * (r ^ (i + j) * tailMoment β α ℓ (c (i, j))) := by
      intro i
      rw [abs_mul]
      have h1 := abs_axisPrim_le_geom γ b hb i
      have h2 := abs_logMoment_le_tailMoment β α ℓ (c (i, j)) (hcc (i, j)).measurable
        (tail_integrable_of_env c ρ C₀ L β α H ℓ D hβ hα hρ hcc hc henv (i, j))
      have hbr' : b ^ i ≤ r ^ i := pow_le_pow_left₀ hb.le hbr.le i
      calc |axisPrim γ b i| * |logMoment β α ℓ (c (i, j))|
          ≤ (C * b ^ i) * tailMoment β α ℓ (c (i, j)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ (C * r ^ i) * tailMoment β α ℓ (c (i, j)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbr' hC0)
              (tailMoment_nonneg _ _ _ _)
        _ = C / r ^ j * (r ^ (i + j) * tailMoment β α ℓ (c (i, j))) := by
            rw [pow_add]; field_simp
    have hsumG := coeffNorm_summable c ρ C₀ L β α r H ℓ D hβ hα hρ hr0.le hrρ hcc hc henv
    have hcol : Summable fun i : ℕ => r ^ (i + j) * tailMoment β α ℓ (c (i, j)) :=
      hsumG.prod_symm.prod_factor j
    have hcol' : Summable fun i : ℕ => C / r ^ j * (r ^ (i + j) * tailMoment β α ℓ (c (i, j))) :=
      hcol.mul_left (C / r ^ j)
    have habs : Summable fun i : ℕ => ‖axisPrim γ b i * logMoment β α ℓ (c (i, j))‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _)
        (fun i => by rw [Real.norm_eq_abs]; exact hterm i) hcol'
    have hcol_le : ∑' i : ℕ, r ^ (i + j) * tailMoment β α ℓ (c (i, j)) ≤ coeffNorm β α ℓ r c :=
      hcol.tsum_le_tsum_of_inj (fun i => (i, j)) (Prod.mk_left_injective j)
        (fun ij _ => mul_nonneg (pow_nonneg hr0.le _) (tailMoment_nonneg _ _ _ _))
        (fun i => le_rfl) hsumG
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (k₂ : ℝ))]
    calc 1 / (k₂ : ℝ) * |∑' i : ℕ, axisPrim γ b i * logMoment β α ℓ (c (i, j))|
        ≤ 1 / (k₂ : ℝ) * ∑' i : ℕ, ‖axisPrim γ b i * logMoment β α ℓ (c (i, j))‖ := by
          gcongr
          rw [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm habs
      _ ≤ 1 / (k₂ : ℝ) * ∑' i : ℕ, C / r ^ j * (r ^ (i + j) * tailMoment β α ℓ (c (i, j))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact habs.tsum_le_tsum (fun i => by rw [Real.norm_eq_abs]; exact hterm i) hcol'
      _ = 1 / (k₂ : ℝ) * (C / r ^ j * ∑' i : ℕ, r ^ (i + j) * tailMoment β α ℓ (c (i, j))) := by
          rw [tsum_mul_left]
      _ ≤ 1 / (k₂ : ℝ) * (C / r ^ j * coeffNorm β α ℓ r c) := by
          gcongr
      _ = C / ((k₂ : ℝ) * r ^ j) * coeffNorm β α ℓ r c := by
          field_simp
  · have hno : ∀ j, vExp h₂ k₂ j ≠ α := fun j h => hP (by rw [← h, vIdx_vExp h₂ k₂ hk₂ j])
    rw [canonV_of_not b h₁ h₂ k₁ k₂ _ _ α hno, logMoment_zero_fun, abs_zero, zero_mul]

/-- **The canonical log coefficient is bounded by the weighted norm.** -/
theorem abs_canonA_le_coeffNorm (c : ℕ × ℕ → ℝ → ℝ) (ρ C₀ L β r : ℝ) (H : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hρ : 0 < ρ) (hr0 : 0 < r) (hrρ : r < ρ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hcc : ∀ ij, Continuous (c ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    |canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) α|
      ≤ cWeight r h₁ h₂ k₁ k₂ α * coeffNorm β α 0 r c :=
  abs_logMoment_canonC_le c ρ C₀ L β r H h₁ h₂ k₁ k₂ 0 D hβ hρ hr0 hrρ hk₁ hk₂ hcc hc henv α hα

/-- **The canonical constant coefficient is bounded by the weighted norm.** -/
theorem abs_canonB_le_coeffNorm (c : ℕ × ℕ → ℝ → ℝ) (b ρ C₀ L β r : ℝ) (H : ℝ → ℝ)
    (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hC₀ : 0 ≤ C₀) (hcc : ∀ ij, Continuous (c ij))
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (α : ℝ) (hα : 0 < α) :
    |canonB β b h₁ h₂ k₁ k₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) α|
      ≤ (uWeight b r h₁ h₂ k₁ k₂ α + vWeight b r h₁ h₂ k₁ k₂ α) * coeffNorm β α 0 r c
        + cWeight r h₁ h₂ k₁ k₂ α * coeffNorm β α 1 r c := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  unfold canonB
  refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
  · rw [add_mul]
    exact add_le_add
      (abs_logMoment_canonU_le c b ρ C₀ L β r H h₁ h₂ k₁ k₂ 0 D hβ hb hbρ hbr hrρ hk₁ hC₀ hcc hc
        henv α)
      (abs_logMoment_canonV_le c b ρ C₀ L β r H h₁ h₂ k₁ k₂ 0 D hβ hb hbρ hbr hrρ hk₂ hC₀ hcc hc
        henv α)
  · exact abs_logMoment_canonC_le c ρ C₀ L β r H h₁ h₂ k₁ k₂ 1 D hβ hρ hr0 hrρ hk₁ hk₂ hcc hc
      henv α hα

end Laplace.Grammar
