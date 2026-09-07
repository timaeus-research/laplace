/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TaylorDataIdentification

/-!
# Local Lipschitz continuity of the canonical Taylor-tree coefficients (grammar §4.2–§4.3)

Composition of the two continuity results of the coefficient-closure programme: the amplitude map
`(x, y) ↦ ampCoeff β x y` is locally Lipschitz in the weighted norm `‖·‖_ρ` (unit 143), and the
canonical coefficients are bounded linear functionals of the amplitude coefficient array in the
weighted moment norm `coeffNorm` (units 140–141). Hence on the bounded family
`‖x‖_ρ, ‖x'‖_ρ ≤ M_x`, `‖y‖_ρ, ‖y'‖_ρ ≤ M_y`:

`|A_α(x,y) − A_α(x',y')| ≤ lipA · (‖y − y'‖_ρ + 2β M_y ‖x − x'‖_ρ)`,
`|B_α(x,y) − B_α(x',y')| ≤ lipB · (‖y − y'‖_ρ + 2β M_y ‖x − x'‖_ρ)`

(`abs_canonA_ampCoeff_sub_le`, `abs_canonB_ampCoeff_sub_le`) with explicit constants built from the
weights of unit 140, the geometric factor `(1 − r/ρ)^{−2}` and the Gaussian envelope moments of
`(1+s) e^{2βM_x s}`. This is the formal counterpart of the paper's appeal (§4.3, proof of
thm:strataempiricalexpansion) to the continuity of `ξ ↦ C_{μ,m}(ξ)`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- `∑_{ij} θ^{i+j} = (1 − θ)^{−2}`. -/
theorem tsum_geom_prod (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' ij : ℕ × ℕ, θ ^ ij.1 * θ ^ ij.2 = (1 - θ)⁻¹ ^ 2 := by
  have hg : Summable fun i : ℕ => ‖θ ^ i‖ := by
    refine (summable_geometric_of_lt_one h0 h1).congr fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _)]
  rw [← tsum_mul_tsum_of_summable_norm hg hg, tsum_geometric_of_lt_one h0 h1, sq]

theorem cWeight_nonneg (r : ℝ) (hr : 0 < r) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) :
    0 ≤ cWeight r h₁ h₂ k₁ k₂ α := by
  unfold cWeight
  split_ifs
  · positivity
  · exact le_rfl

theorem uWeight_nonneg (b r : ℝ) (hb : 0 < b) (hr : 0 < r) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) :
    0 ≤ uWeight b r h₁ h₂ k₁ k₂ α := by
  unfold uWeight
  split_ifs
  · exact div_nonneg (axisPrimGeomConst_nonneg _ b hb) (by positivity)
  · exact le_rfl

theorem vWeight_nonneg (b r : ℝ) (hb : 0 < b) (hr : 0 < r) (h₁ h₂ k₁ k₂ : ℕ) (α : ℝ) :
    0 ≤ vWeight b r h₁ h₂ k₁ k₂ α := by
  unfold vWeight
  split_ifs
  · exact div_nonneg (axisPrimGeomConst_nonneg _ b hb) (by positivity)
  · exact le_rfl

/-- Common envelope of the amplitude arrays on the bounded family. -/
theorem ampEnv_le_common (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (x y : ℕ × ℕ → ℝ)
    (hx : WSummable ρ x) (Mx My : ℝ) (hMx : wnorm ρ x ≤ Mx) (hMy : wnorm ρ y ≤ My) (s : ℝ)
    (hs : 0 ≤ s) : ampEnv β ρ x y s ≤ My * (1 + s) ^ 0 * Real.exp (β * s * (2 * Mx)) := by
  refine (ampEnv_le β ρ hβ x y s hs).trans ?_
  have h1 : x (0, 0) + wnorm ρ (dropConst x) ≤ 2 * Mx := by
    have := abs_apply_zero_le_wnorm ρ hρ.le x hx
    have := wnorm_dropConst_le ρ hρ.le x hx
    have := le_abs_self (x (0, 0))
    linarith
  have hMy0 : 0 ≤ My := (wnorm_nonneg ρ hρ.le y).trans hMy
  exact mul_le_mul (mul_le_mul_of_nonneg_right hMy (by positivity))
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 (by positivity))) (Real.exp_pos _).le
    (mul_nonneg hMy0 (by positivity))

/-- Pointwise Gaussian envelope of the amplitude difference for `s > 0`. -/
theorem ampCoeff_sub_env (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (x x' y y' : ℕ × ℕ → ℝ)
    (hx : WSummable ρ x) (hx' : WSummable ρ x') (hy : WSummable ρ y) (hy' : WSummable ρ y')
    (Mx My : ℝ) (hMx : wnorm ρ x ≤ Mx) (hMx' : wnorm ρ x' ≤ Mx) (hMy' : wnorm ρ y' ≤ My)
    (ij : ℕ × ℕ) (s : ℝ) (hs : 0 < s) :
    |ampCoeff β x y ij s - ampCoeff β x' y' ij s|
      ≤ (ρ ^ (ij.1 + ij.2))⁻¹
          * ((wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k))
            * gaussEnv β (2 * Mx) 1 s) := by
  set Dy := wnorm ρ (fun k => y k - y' k) with hDy
  set Dx := wnorm ρ (fun k => x k - x' k) with hDx
  have hDy0 : 0 ≤ Dy := wnorm_nonneg ρ hρ.le _
  have hDx0 : 0 ≤ Dx := wnorm_nonneg ρ hρ.le _
  have hMy0 : 0 ≤ My := (wnorm_nonneg ρ hρ.le y').trans hMy'
  have hpos : 0 < ρ ^ (ij.1 + ij.2) := pow_pos hρ _
  have h := ampCoeff_sub_abs_le β ρ hρ x x' y y' hx hx' hy hy' Mx My hMx hMx' hMy' ij s
  rw [← hDy, ← hDx] at h
  have habs : |β * s| = β * s := abs_of_pos (by positivity)
  rw [habs] at h
  rw [show (ρ ^ (ij.1 + ij.2))⁻¹ * ((Dy + 2 * β * My * Dx) * gaussEnv β (2 * Mx) 1 s)
      = (Dy + 2 * β * My * Dx) * gaussEnv β (2 * Mx) 1 s / ρ ^ (ij.1 + ij.2) by ring,
    le_div_iff₀ hpos]
  refine h.trans ?_
  unfold gaussEnv
  have hexp : Real.exp (2 * (β * s) * Mx) = Real.exp (β * s * (2 * Mx)) := by congr 1; ring
  rw [hexp, pow_one]
  have hlin : Dy + 2 * My * (β * s) * Dx ≤ (Dy + 2 * β * My * Dx) * (1 + s) := by
    nlinarith [mul_nonneg hDy0 hs.le,
      mul_nonneg (mul_nonneg (mul_nonneg two_pos.le hβ.le) hMy0) hDx0]
  calc Real.exp (β * s * (2 * Mx)) * (Dy + 2 * My * (β * s) * Dx)
      ≤ Real.exp (β * s * (2 * Mx)) * ((Dy + 2 * β * My * Dx) * (1 + s)) :=
        mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
    _ = (Dy + 2 * β * My * Dx) * ((1 + s) * Real.exp (β * s * (2 * Mx))) := by ring

/-- Weighted tail moment of one amplitude difference. -/
theorem tailMoment_ampCoeff_sub_le (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (x x' y y' : ℕ × ℕ → ℝ)
    (hx : WSummable ρ x) (hx' : WSummable ρ x') (hy : WSummable ρ y) (hy' : WSummable ρ y')
    (Mx My : ℝ) (hMx : wnorm ρ x ≤ Mx) (hMx' : wnorm ρ x' ≤ Mx) (hMy' : wnorm ρ y' ≤ My)
    (α : ℝ) (hα : 0 < α) (ℓ : ℕ) (ij : ℕ × ℕ) :
    tailMoment β α ℓ (fun s => ampCoeff β x y ij s - ampCoeff β x' y' ij s)
      ≤ (ρ ^ (ij.1 + ij.2))⁻¹
          * (wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k))
          * envMoment β α ℓ (gaussEnv β (2 * Mx) 1) :=
  tailMoment_le_of_env β (2 * Mx) α _ ℓ 1 _ hβ hα
    ((ampCoeff_continuous β x y ij).sub (ampCoeff_continuous β x' y' ij)).measurable
    fun s hs => by
      rw [mul_assoc]
      exact ampCoeff_sub_env β ρ hβ hρ x x' y y' hx hx' hy hy' Mx My hMx hMx' hMy' ij s hs

/-- **Weighted moment norm of the amplitude difference**:
`‖c(x,y) − c(x',y')‖_{α,ℓ,r} ≤ (1 − r/ρ)^{−2} (‖y − y'‖_ρ + 2βM_y‖x − x'‖_ρ) EM_{α,ℓ}`. -/
theorem coeffNorm_ampCoeff_sub_le (β ρ r : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hr0 : 0 ≤ r)
    (hrρ : r < ρ) (x x' y y' : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hx' : WSummable ρ x')
    (hy : WSummable ρ y) (hy' : WSummable ρ y') (Mx My : ℝ) (hMx : wnorm ρ x ≤ Mx)
    (hMx' : wnorm ρ x' ≤ Mx) (hMy' : wnorm ρ y' ≤ My) (α : ℝ) (hα : 0 < α) (ℓ : ℕ) :
    coeffNorm β α ℓ r (fun ij s => ampCoeff β x y ij s - ampCoeff β x' y' ij s)
      ≤ (1 - r / ρ)⁻¹ ^ 2
          * (wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k))
          * envMoment β α ℓ (gaussEnv β (2 * Mx) 1) := by
  set K := (wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k))
    * envMoment β α ℓ (gaussEnv β (2 * Mx) 1) with hK
  have hθ0 : 0 ≤ r / ρ := by positivity
  have hθ1 : r / ρ < 1 := (div_lt_one hρ).2 hrρ
  have hgs := summable_geom_prod (r / ρ) hθ0 hθ1
  have hterm : ∀ ij : ℕ × ℕ,
      r ^ (ij.1 + ij.2) * tailMoment β α ℓ (fun s => ampCoeff β x y ij s - ampCoeff β x' y' ij s)
        ≤ (r / ρ) ^ ij.1 * (r / ρ) ^ ij.2 * K := by
    intro ij
    have h := tailMoment_ampCoeff_sub_le β ρ hβ hρ x x' y y' hx hx' hy hy' Mx My hMx hMx' hMy'
      α hα ℓ ij
    calc r ^ (ij.1 + ij.2) * tailMoment β α ℓ (fun s => ampCoeff β x y ij s - ampCoeff β x' y' ij s)
        ≤ r ^ (ij.1 + ij.2) * ((ρ ^ (ij.1 + ij.2))⁻¹
            * (wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k))
            * envMoment β α ℓ (gaussEnv β (2 * Mx) 1)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (r / ρ) ^ ij.1 * (r / ρ) ^ ij.2 * K := by
          rw [hK, ← pow_add, div_pow, div_eq_mul_inv]; ring
  have hs : Summable fun ij : ℕ × ℕ =>
      r ^ (ij.1 + ij.2) * tailMoment β α ℓ (fun s => ampCoeff β x y ij s - ampCoeff β x' y' ij s) :=
    Summable.of_nonneg_of_le (fun ij => mul_nonneg (by positivity) (tailMoment_nonneg _ _ _ _))
      hterm (hgs.mul_right K)
  unfold coeffNorm
  calc ∑' ij : ℕ × ℕ,
        r ^ (ij.1 + ij.2) * tailMoment β α ℓ (fun s => ampCoeff β x y ij s - ampCoeff β x' y' ij s)
      ≤ ∑' ij : ℕ × ℕ, (r / ρ) ^ ij.1 * (r / ρ) ^ ij.2 * K :=
        hs.tsum_le_tsum hterm (hgs.mul_right K)
    _ = (∑' ij : ℕ × ℕ, (r / ρ) ^ ij.1 * (r / ρ) ^ ij.2) * K := tsum_mul_right
    _ = _ := by rw [tsum_geom_prod (r / ρ) hθ0 hθ1, hK]; ring

/-- The Lipschitz constant of `A_α` on the bounded family. -/
noncomputable def lipA (β ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Mx α : ℝ) : ℝ :=
  cWeight r h₁ h₂ k₁ k₂ α * ((1 - r / ρ)⁻¹ ^ 2 * envMoment β α 0 (gaussEnv β (2 * Mx) 1))

/-- The Lipschitz constant of `B_α` on the bounded family. -/
noncomputable def lipB (β b ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Mx α : ℝ) : ℝ :=
  (uWeight b r h₁ h₂ k₁ k₂ α + vWeight b r h₁ h₂ k₁ k₂ α)
      * ((1 - r / ρ)⁻¹ ^ 2 * envMoment β α 0 (gaussEnv β (2 * Mx) 1))
    + cWeight r h₁ h₂ k₁ k₂ α * ((1 - r / ρ)⁻¹ ^ 2 * envMoment β α 1 (gaussEnv β (2 * Mx) 1))

/-- **Local Lipschitz continuity of the log coefficient `A_α`** in the amplitude data. -/
theorem abs_canonA_ampCoeff_sub_le (β ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hρ : 0 < ρ)
    (hr0 : 0 < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (x x' y y' : ℕ × ℕ → ℝ)
    (hx : WSummable ρ x) (hx' : WSummable ρ x') (hy : WSummable ρ y) (hy' : WSummable ρ y')
    (Mx My : ℝ) (hMx : wnorm ρ x ≤ Mx) (hMx' : wnorm ρ x' ≤ Mx) (hMy : wnorm ρ y ≤ My)
    (hMy' : wnorm ρ y' ≤ My) (α : ℝ) (hα : 0 < α) :
    |canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) α
        - canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x' y' (i, j) s) α|
      ≤ lipA β ρ r h₁ h₂ k₁ k₂ Mx α
          * (wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k)) := by
  have h := abs_canonA_sub_le (ampCoeff β x y) (ampCoeff β x' y') ρ My My (2 * Mx) β r
    (ampEnv β ρ x y) (ampEnv β ρ x' y') h₁ h₂ k₁ k₂ 0 hβ hρ hr0 hrρ hk₁ hk₂
    (ampCoeff_continuous β x y) (ampCoeff_continuous β x' y')
    (fun ij s => ampCoeff_abs_le β ρ hρ x y hx hy ij s)
    (fun ij s => ampCoeff_abs_le β ρ hρ x' y' hx' hy' ij s)
    (fun s hs => ampEnv_le_common β ρ hβ hρ x y hx Mx My hMx hMy s hs)
    (fun s hs => ampEnv_le_common β ρ hβ hρ x' y' hx' Mx My hMx' hMy' s hs) α hα
  refine h.trans ?_
  have hc := coeffNorm_ampCoeff_sub_le β ρ r hβ hρ hr0.le hrρ x x' y y' hx hx' hy hy' Mx My hMx
    hMx' hMy' α hα 0
  unfold lipA
  calc cWeight r h₁ h₂ k₁ k₂ α
        * coeffNorm β α 0 r (fun ij s => ampCoeff β x y ij s - ampCoeff β x' y' ij s)
      ≤ cWeight r h₁ h₂ k₁ k₂ α * ((1 - r / ρ)⁻¹ ^ 2
          * (wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k))
          * envMoment β α 0 (gaussEnv β (2 * Mx) 1)) :=
        mul_le_mul_of_nonneg_left hc (cWeight_nonneg r hr0 h₁ h₂ k₁ k₂ α)
    _ = _ := by ring

/-- **Local Lipschitz continuity of the constant coefficient `B_α`** in the amplitude data. -/
theorem abs_canonB_ampCoeff_sub_le (β b ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (x x' y y' : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hx' : WSummable ρ x') (hy : WSummable ρ y)
    (hy' : WSummable ρ y') (Mx My : ℝ) (hMx : wnorm ρ x ≤ Mx) (hMx' : wnorm ρ x' ≤ Mx)
    (hMy : wnorm ρ y ≤ My) (hMy' : wnorm ρ y' ≤ My) (α : ℝ) (hα : 0 < α) :
    |canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
          (fun i j s => ampCoeff β x y (i, j) s) α
        - canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x' y') b) (anaFaceV (ampCoeff β x' y') b)
          (fun i j s => ampCoeff β x' y' (i, j) s) α|
      ≤ lipB β b ρ r h₁ h₂ k₁ k₂ Mx α
          * (wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k)) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  have hMy0 : 0 ≤ My := (wnorm_nonneg ρ hρ.le y').trans hMy'
  have h := abs_canonB_sub_le (ampCoeff β x y) (ampCoeff β x' y') b ρ My My (2 * Mx) β r
    (ampEnv β ρ x y) (ampEnv β ρ x' y') h₁ h₂ k₁ k₂ 0 hβ hb hbρ hbr hrρ hk₁ hk₂ hMy0 hMy0
    (ampCoeff_continuous β x y) (ampCoeff_continuous β x' y')
    (fun ij s => ampCoeff_abs_le β ρ hρ x y hx hy ij s)
    (fun ij s => ampCoeff_abs_le β ρ hρ x' y' hx' hy' ij s)
    (fun s hs => ampEnv_le_common β ρ hβ hρ x y hx Mx My hMx hMy s hs)
    (fun s hs => ampEnv_le_common β ρ hβ hρ x' y' hx' Mx My hMx' hMy' s hs) α hα
  refine h.trans ?_
  have hc0 := coeffNorm_ampCoeff_sub_le β ρ r hβ hρ hr0.le hrρ x x' y y' hx hx' hy hy' Mx My hMx
    hMx' hMy' α hα 0
  have hc1 := coeffNorm_ampCoeff_sub_le β ρ r hβ hρ hr0.le hrρ x x' y y' hx hx' hy hy' Mx My hMx
    hMx' hMy' α hα 1
  have hw : 0 ≤ uWeight b r h₁ h₂ k₁ k₂ α + vWeight b r h₁ h₂ k₁ k₂ α :=
    add_nonneg (uWeight_nonneg b r hb hr0 h₁ h₂ k₁ k₂ α) (vWeight_nonneg b r hb hr0 h₁ h₂ k₁ k₂ α)
  unfold lipB
  set Dsum := wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k) with hD
  calc (uWeight b r h₁ h₂ k₁ k₂ α + vWeight b r h₁ h₂ k₁ k₂ α)
          * coeffNorm β α 0 r (fun ij s => ampCoeff β x y ij s - ampCoeff β x' y' ij s)
        + cWeight r h₁ h₂ k₁ k₂ α
          * coeffNorm β α 1 r (fun ij s => ampCoeff β x y ij s - ampCoeff β x' y' ij s)
      ≤ (uWeight b r h₁ h₂ k₁ k₂ α + vWeight b r h₁ h₂ k₁ k₂ α)
          * ((1 - r / ρ)⁻¹ ^ 2 * Dsum * envMoment β α 0 (gaussEnv β (2 * Mx) 1))
        + cWeight r h₁ h₂ k₁ k₂ α
          * ((1 - r / ρ)⁻¹ ^ 2 * Dsum * envMoment β α 1 (gaussEnv β (2 * Mx) 1)) :=
        add_le_add (mul_le_mul_of_nonneg_left hc0 hw)
          (mul_le_mul_of_nonneg_left hc1 (cWeight_nonneg r hr0 h₁ h₂ k₁ k₂ α))
    _ = _ := by ring

end Laplace.Grammar
