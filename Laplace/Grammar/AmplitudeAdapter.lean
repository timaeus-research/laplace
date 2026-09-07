/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.DoubleSeriesExp
import Laplace.Grammar.TwoDCutoffAnalytic

/-!
# The amplitude adapter for `η e^{βsξ}` (grammar §4.2, analytic bridge)

Given weighted-summable coefficient arrays `x` (of `ξ`) and `y` (of `η`) at radius `ρ`, the
`s`-parametrised array

  `c_k(s) = e^{βs x₀₀} · (y * E(βs))_k`,   `E(t) = expCoeff (dropConst x) t`   (`ampCoeff`)

is the double series of `η(u,v) e^{βs ξ(u,v)}` on `|u|, |v| ≤ ρ` (`dblSum_ampCoeff`), each `c_k` is
continuous in `s`, and `|c_k(s)| ρ^{|k|} ≤ Y e^{βs x₀₀} e^{|βs| X}` with `X = N_ρ(x − x₀₀ δ)`,
`Y = N_ρ(y)` (`ampCoeff_abs_le`). Feeding these into `twoD_cutoff_analytic` (with `L = x₀₀ + X`,
`D = 0`, `C₀ = Y`) gives the analytic `d = 2` cutoff theorem for the chart amplitude of
`thm:TaylorTree` from the analyticity of `ξ, η` alone (`twoD_cutoff_amplitude`). This closes the
coefficient-closure programme (Astra #7). Zero `sorry`/`axiom`.
-/

open Real Set Filter Asymptotics

namespace Laplace.Grammar

/-- Remove the constant term of a coefficient array. -/
noncomputable def dropConst (x : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ := fun k => if k = (0, 0) then 0 else x k

theorem dropConst_zero (x : ℕ × ℕ → ℝ) : dropConst x (0, 0) = 0 := by simp [dropConst]

theorem abs_dropConst_le (x : ℕ × ℕ → ℝ) (k : ℕ × ℕ) : |dropConst x k| ≤ |x k| := by
  unfold dropConst
  split_ifs <;> simp

theorem wsummable_dropConst (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) :
    WSummable ρ (dropConst x) := by
  unfold WSummable at hx ⊢
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hx
  exact mul_le_mul_of_nonneg_right (abs_dropConst_le x k) (by positivity)

theorem wnorm_dropConst_le (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) :
    wnorm ρ (dropConst x) ≤ wnorm ρ x := by
  unfold wnorm
  refine Summable.tsum_le_tsum (fun k => ?_) (wsummable_dropConst ρ hρ x hx) hx
  exact mul_le_mul_of_nonneg_right (abs_dropConst_le x k) (by positivity)

/-- `x = dropConst x + x₀₀ δ` pointwise. -/
theorem dropConst_add_delta (x : ℕ × ℕ → ℝ) (k : ℕ × ℕ) :
    x k = dropConst x k + x (0, 0) * delta k := by
  unfold dropConst delta
  split_ifs with h
  · subst h; simp
  · simp

/-- Absolute summability of the evaluated family. -/
theorem dblSum_summable (ρ u v : ℝ) (f : ℕ × ℕ → ℝ) (hf : WSummable ρ f) (hu : |u| ≤ ρ)
    (hv : |v| ≤ ρ) : Summable fun k : ℕ × ℕ => f k * u ^ k.1 * v ^ k.2 :=
  (dblSum_abs_le_wnorm ρ u v f hf hu hv).1.of_norm

theorem dblSum_dropConst (ρ u v : ℝ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hu : |u| ≤ ρ)
    (hv : |v| ≤ ρ) : dblSum (dropConst x) u v = dblSum x u v - x (0, 0) := by
  have hρ : 0 ≤ ρ := (abs_nonneg u).trans hu
  have hd : dblSum (fun k => x (0, 0) * delta k) u v = x (0, 0) := by
    unfold dblSum
    have : ∀ k : ℕ × ℕ, x (0, 0) * delta k * u ^ k.1 * v ^ k.2
        = x (0, 0) * (delta k * u ^ k.1 * v ^ k.2) := fun k => by ring
    rw [tsum_congr this, tsum_mul_left]
    have h1 := dblSum_delta u v
    unfold dblSum at h1
    rw [h1, mul_one]
  have hsum : dblSum x u v
      = dblSum (dropConst x) u v + dblSum (fun k => x (0, 0) * delta k) u v := by
    unfold dblSum
    rw [← Summable.tsum_add]
    · exact tsum_congr fun k => by rw [dropConst_add_delta x k]; ring
    · exact dblSum_summable ρ u v _ (wsummable_dropConst ρ hρ x hx) hu hv
    · have hw : WSummable ρ fun k => x (0, 0) * delta k := by
        unfold WSummable
        have h := wsummable_delta ρ
        unfold WSummable at h
        exact (h.mul_left |x (0, 0)|).congr fun k => by rw [abs_mul]; ring
      exact dblSum_summable ρ u v _ hw hu hv
  rw [hsum, hd]; ring

/-- The amplitude coefficient array `c_k(s) = e^{βs x₀₀} (y * E(βs))_k`. -/
noncomputable def ampCoeff (β : ℝ) (x y : ℕ × ℕ → ℝ) (k : ℕ × ℕ) (s : ℝ) : ℝ :=
  Real.exp (β * s * x (0, 0)) * conv y (expCoeff (dropConst x) (β * s)) k

theorem ampCoeff_continuous (β : ℝ) (x y : ℕ × ℕ → ℝ) (k : ℕ × ℕ) :
    Continuous (ampCoeff β x y k) := by
  unfold ampCoeff conv
  refine (Real.continuous_exp.comp ((continuous_const.mul continuous_id).mul continuous_const)).mul
    (continuous_finsetSum _ fun a _ => continuous_const.mul ?_)
  exact (expCoeff_continuous (dropConst x) (psub k a)).comp
    ((continuous_const.mul continuous_id))

/-- Weighted summability and the weighted norm bound of the amplitude array. -/
theorem ampCoeff_wnorm_le (β ρ : ℝ) (hρ : 0 < ρ) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) (s : ℝ) :
    WSummable ρ (fun k => ampCoeff β x y k s) ∧
      wnorm ρ (fun k => ampCoeff β x y k s)
        ≤ wnorm ρ y * Real.exp (β * s * x (0, 0)) * Real.exp (|β * s| * wnorm ρ (dropConst x)) := by
  have hE := wnorm_expCoeff_le ρ hρ (dropConst x) (wsummable_dropConst ρ hρ.le x hx)
    (dropConst_zero x) (β * s)
  have hC := wnorm_conv_le ρ hρ y _ hy hE.1
  have hpos : 0 < Real.exp (β * s * x (0, 0)) := Real.exp_pos _
  have hW : WSummable ρ (fun k => ampCoeff β x y k s) := by
    unfold WSummable ampCoeff
    unfold WSummable at hC
    exact (hC.1.mul_left (Real.exp (β * s * x (0, 0)))).congr fun k => by
      rw [abs_mul, abs_of_pos hpos]; ring
  refine ⟨hW, ?_⟩
  have h1 : wnorm ρ (fun k => ampCoeff β x y k s)
      = Real.exp (β * s * x (0, 0)) * wnorm ρ (conv y (expCoeff (dropConst x) (β * s))) := by
    unfold wnorm ampCoeff
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by rw [abs_mul, abs_of_pos hpos]; ring
  rw [h1]
  have hy0 : 0 ≤ wnorm ρ y := wnorm_nonneg ρ hρ.le y
  calc Real.exp (β * s * x (0, 0)) * wnorm ρ (conv y (expCoeff (dropConst x) (β * s)))
      ≤ Real.exp (β * s * x (0, 0)) * (wnorm ρ y * Real.exp (|β * s| * wnorm ρ (dropConst x))) := by
        gcongr
        exact hC.2.trans (mul_le_mul_of_nonneg_left hE.2 hy0)
    _ = _ := by ring

/-- Pointwise weighted bound `|c_k(s)| ρ^{|k|} ≤ Y e^{βs x₀₀} e^{|βs| X}`. -/
theorem ampCoeff_abs_le (β ρ : ℝ) (hρ : 0 < ρ) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) (k : ℕ × ℕ) (s : ℝ) :
    |ampCoeff β x y k s| * ρ ^ (k.1 + k.2)
      ≤ wnorm ρ y * Real.exp (β * s * x (0, 0)) * Real.exp (|β * s| * wnorm ρ (dropConst x)) := by
  obtain ⟨hW, hle⟩ := ampCoeff_wnorm_le β ρ hρ x y hx hy s
  refine le_trans ?_ hle
  unfold WSummable at hW
  exact hW.le_tsum k fun j _ => by positivity

/-- **Evaluation**: `∑_k c_k(s) u^i v^j = η(u,v) e^{βs ξ(u,v)}` for `|u|, |v| ≤ ρ`. -/
theorem dblSum_ampCoeff (β ρ u v : ℝ) (hρ : 0 < ρ) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) (hu : |u| ≤ ρ) (hv : |v| ≤ ρ) (s : ℝ) :
    dblSum (fun k => ampCoeff β x y k s) u v = dblSum y u v * Real.exp (β * s * dblSum x u v) := by
  have hx' := wsummable_dropConst ρ hρ.le x hx
  have hE := wnorm_expCoeff_le ρ hρ (dropConst x) hx' (dropConst_zero x) (β * s)
  have h1 : dblSum (fun k => ampCoeff β x y k s) u v
      = Real.exp (β * s * x (0, 0)) * dblSum (conv y (expCoeff (dropConst x) (β * s))) u v := by
    unfold dblSum ampCoeff
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  rw [h1, dblSum_conv ρ u v _ _ hy hE.1 hu hv,
    dblSum_expCoeff ρ u v hρ _ hx' (dropConst_zero x) hu hv, dblSum_dropConst ρ u v x hx hu hv,
    ← mul_assoc, mul_comm (Real.exp _) (dblSum y u v), mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- The analytic amplitude `anaAmp (ampCoeff β x y) b` is `η e^{βsξ}` on the box `[0,b]²`. -/
theorem anaAmp_ampCoeff (β b ρ : ℝ) (hb : 0 < b) (hbρ : b < ρ) (x y : ℕ × ℕ → ℝ)
    (hx : WSummable ρ x) (hy : WSummable ρ y) (u v s : ℝ) (hu : u ∈ Icc (0 : ℝ) b)
    (hv : v ∈ Icc (0 : ℝ) b) :
    anaAmp (ampCoeff β x y) b u v s = dblSum y u v * Real.exp (β * s * dblSum x u v) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  unfold anaAmp
  rw [clampB_of_mem b u hu, clampB_of_mem b v hv]
  have hu' : |u| ≤ ρ := by rw [abs_of_nonneg hu.1]; linarith [hu.2]
  have hv' : |v| ≤ ρ := by rw [abs_of_nonneg hv.1]; linarith [hv.2]
  exact dblSum_ampCoeff β ρ u v hρ x y hx hy hu' hv' s

/-- The envelope `H(s) = Y e^{βs x₀₀} e^{|βs| X}`. -/
noncomputable def ampEnv (β ρ : ℝ) (x y : ℕ × ℕ → ℝ) (s : ℝ) : ℝ :=
  wnorm ρ y * Real.exp (β * s * x (0, 0)) * Real.exp (|β * s| * wnorm ρ (dropConst x))

theorem ampEnv_continuous (β ρ : ℝ) (x y : ℕ × ℕ → ℝ) : Continuous (ampEnv β ρ x y) := by
  unfold ampEnv
  exact (continuous_const.mul
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).mul continuous_const))).mul
    (Real.continuous_exp.comp
      (((continuous_const.mul continuous_id).abs).mul continuous_const))

theorem ampEnv_le (β ρ : ℝ) (hβ : 0 < β) (x y : ℕ × ℕ → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    ampEnv β ρ x y s ≤ wnorm ρ y * (1 + s) ^ 0
      * Real.exp (β * s * (x (0, 0) + wnorm ρ (dropConst x))) := by
  unfold ampEnv
  rw [abs_of_nonneg (by positivity), pow_zero, mul_one, mul_assoc, ← Real.exp_add]
  apply le_of_eq
  congr 2; ring

/-- **The analytic `d = 2` cutoff theorem for the chart amplitude `η e^{βsξ}`.** Hypotheses: the
coefficient arrays `x` of `ξ` and `y` of `η` are weighted-summable at a radius `ρ > b`; equal
exponents `(h₁+1)/k₁ = (h₂+1)/k₂ = p`; truncation compatibility. Conclusion: the amplitude
`twoDAmp` of `anaAmp (ampCoeff β x y) b` (which equals `η e^{βsξ}` on the box) minus the reduced
sum of face and corner terms is `O(N^{-(p + min(M₁/k₁, M₂/k₂))} (1 + log N))`. -/
theorem twoD_cutoff_amplitude (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hM₁ : ((M₁ : ℝ) - 1) / k₁ < (M₂ : ℝ) / k₂) (hM₂ : ((M₂ : ℝ) - 1) / k₂ < (M₁ : ℝ) / k₁)
    (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hy : WSummable ρ y) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - reducedSum β b h₁ h₂ k₁ k₂ M₁ M₂ (anaFaceU (ampCoeff β x y) b)
            (anaFaceV (ampCoeff β x y) b) (fun i j s => ampCoeff β x y (i, j) s) N)
      =O[atTop] fun N : ℝ =>
        N ^ (-(p + min ((M₁ : ℝ) / k₁) ((M₂ : ℝ) / k₂))) * (1 + Real.log N) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  exact twoD_cutoff_analytic β b p ρ (wnorm ρ y) (x (0, 0) + wnorm ρ (dropConst x)) h₁ h₂ k₁ k₂
    M₁ M₂ 0 hβ hb hbρ hk₁ hk₂ hp₁ hp₂ hM₁ hM₂ (ampCoeff β x y) (ampCoeff_continuous β x y)
    (ampEnv β ρ x y) (ampEnv_continuous β ρ x y)
    (fun ij s => ampCoeff_abs_le β ρ hρ x y hx hy ij s) (wnorm_nonneg ρ hρ.le y)
    (fun s hs => ampEnv_le β ρ hβ x y s hs)

end Laplace.Grammar
