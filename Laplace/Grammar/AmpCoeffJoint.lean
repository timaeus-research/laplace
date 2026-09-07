/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.NormalisedRemainder

/-!
# Joint continuity of the amplitude coefficients and measurability of the chart integral

The amplitude coefficients `c_k(s) = ampCoeff β x y k s` are finite algebraic expressions in
finitely many entries of `x, y` and in `s`, hence jointly continuous in `(a, s)` on
`CoeffPair × ℝ` (`ampCoeff_pair_continuous`). Consequently, for a measurable random Taylor datum
`X : Ω → CoeffPair`, the chart integral `Z_N(X ω)` is a measurable function of `ω`
(`measurable_chartZ_comp`), via the parameter-measurability theorem of unit 138. We also package
the chart integral as a function `chartZ` on `CoeffPair` and restate the uniform Taylor tree
(unit 135) on norm balls of `CoeffPair` (`chartZ_taylor_tree_ball`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

theorem continuous_eval_coeffPair (i : PairIdx) : Continuous fun a : CoeffPair => a i :=
  (lp.lipschitzWith_one_eval 1 i).continuous

theorem continuous_toX (ρ : ℝ) (k : ℕ × ℕ) : Continuous fun a : CoeffPair => toX ρ a k :=
  (continuous_eval_coeffPair _).div_const _

theorem continuous_toY (ρ : ℝ) (k : ℕ × ℕ) : Continuous fun a : CoeffPair => toY ρ a k :=
  (continuous_eval_coeffPair _).div_const _

/-- Convolution powers are continuous in a parameter. -/
theorem convPow_continuous_param {X : Type*} [TopologicalSpace X] (f : X → ℕ × ℕ → ℝ)
    (hf : ∀ k, Continuous fun p => f p k) (n : ℕ) :
    ∀ k, Continuous fun p => convPow (f p) n k := by
  induction n with
  | zero =>
    intro k
    change Continuous fun _ : X => delta k
    exact continuous_const
  | succ n ih =>
    intro k
    change Continuous fun p => conv (f p) (convPow (f p) n) k
    unfold conv
    exact continuous_finsetSum _ fun a _ => (hf a).mul (ih _)

theorem dropConst_continuous_param {X : Type*} [TopologicalSpace X] (f : X → ℕ × ℕ → ℝ)
    (hf : ∀ k, Continuous fun p => f p k) (k : ℕ × ℕ) :
    Continuous fun p => dropConst (f p) k := by
  unfold dropConst
  split_ifs
  · exact continuous_const
  · exact hf k

theorem expCoeff_continuous_param {X : Type*} [TopologicalSpace X] (f : X → ℕ × ℕ → ℝ)
    (hf : ∀ k, Continuous fun p => f p k) (t : X → ℝ) (ht : Continuous t) (k : ℕ × ℕ) :
    Continuous fun p => expCoeff (f p) (t p) k := by
  unfold expCoeff
  exact continuous_finsetSum _ fun n _ =>
    ((ht.pow n).div_const _).mul (convPow_continuous_param f hf n k)

/-- Joint continuity of the amplitude coefficients in the data and in `s`. -/
theorem ampCoeff_continuous_param {X : Type*} [TopologicalSpace X] (β : ℝ)
    (x y : X → ℕ × ℕ → ℝ) (hx : ∀ k, Continuous fun p => x p k)
    (hy : ∀ k, Continuous fun p => y p k) (s : X → ℝ) (hs : Continuous s) (k : ℕ × ℕ) :
    Continuous fun p => ampCoeff β (x p) (y p) k (s p) := by
  unfold ampCoeff conv
  refine (Real.continuous_exp.comp ((continuous_const.mul hs).mul (hx (0, 0)))).mul
    (continuous_finsetSum _ fun a _ => (hy a).mul ?_)
  exact expCoeff_continuous_param (fun p => dropConst (x p))
    (fun k => dropConst_continuous_param x hx k) (fun p => β * s p) (continuous_const.mul hs) _

theorem ampCoeff_pair_continuous (β ρ : ℝ) (k : ℕ × ℕ) :
    Continuous fun q : CoeffPair × ℝ => ampCoeff β (toX ρ q.1) (toY ρ q.1) k q.2 :=
  ampCoeff_continuous_param β (fun q : CoeffPair × ℝ => toX ρ q.1)
    (fun q : CoeffPair × ℝ => toY ρ q.1) (fun k => (continuous_toX ρ k).comp continuous_fst)
    (fun k => (continuous_toY ρ k).comp continuous_fst) (fun q : CoeffPair × ℝ => q.2)
    continuous_snd k

theorem ampCoeff_pair_measurable {Ω : Type*} [MeasurableSpace Ω] (β ρ : ℝ) (X : Ω → CoeffPair)
    (hX : Measurable X) (k : ℕ × ℕ) :
    Measurable fun p : Ω × ℝ => ampCoeff β (toX ρ (X p.1)) (toY ρ (X p.1)) k p.2 :=
  (ampCoeff_pair_continuous β ρ k).measurable.comp
    ((hX.comp measurable_fst).prodMk measurable_snd)

/-- The chart integral `Z_N` as a function of the Taylor data. -/
noncomputable def chartZ (β b ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (N : ℝ) (a : CoeffPair) : ℝ :=
  twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β (toX ρ a) (toY ρ a)) b)

/-- **Measurability of the chart integral in the random Taylor data.** -/
theorem measurable_chartZ_comp {Ω : Type*} [MeasurableSpace Ω] (β b ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ)
    (hb : 0 < b) (hbρ : b < ρ) (N : ℝ) (X : Ω → CoeffPair) (hX : Measurable X) :
    Measurable fun ω => chartZ β b ρ h₁ h₂ k₁ k₂ N (X ω) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  exact twoDAmp_param_measurable β b N ρ h₁ h₂ k₁ k₂ hb hbρ
    (fun ω => ampCoeff β (toX ρ (X ω)) (toY ρ (X ω))) (fun ω ij => ampCoeff_continuous β _ _ ij)
    (fun ij => ampCoeff_pair_measurable β ρ X hX ij)
    (fun ω => ampEnv β ρ (toX ρ (X ω)) (toY ρ (X ω))) (fun ω => ampEnv_continuous β ρ _ _)
    (fun ω ij s => ampCoeff_abs_le β ρ hρ _ _ (wsummable_toX ρ hρ _) (wsummable_toY ρ hρ _) ij s)

theorem measurable_chartZ (β b ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hb : 0 < b) (hbρ : b < ρ) (N : ℝ) :
    Measurable (chartZ β b ρ h₁ h₂ k₁ k₂ N) :=
  measurable_chartZ_comp β b ρ h₁ h₂ k₁ k₂ hb hbρ N id measurable_id

/-- **Uniform Taylor tree on a norm ball of the coefficient-pair space.** -/
theorem chartZ_taylor_tree_ball (β b p₁ p₂ ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (M : ℝ) (hM : 0 ≤ M) (a : CoeffPair) (ha : ‖a‖ ≤ M)
    (T N : ℝ) (hN : 1 ≤ N) :
    |chartZ β b ρ h₁ h₂ k₁ k₂ N a
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * (coeffA β ρ h₁ h₂ k₁ k₂ α a * Real.log N + coeffB β b ρ h₁ h₂ k₁ k₂ α a)|
      ≤ uniformTreeConst β b ρ M (2 * M) p₁ p₂ T h₁ h₂ k₁ k₂ 0
        * (N ^ (-(2 * T)) * (1 + Real.log N)) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hx := wsummable_toX ρ hρ a
  have hy := wsummable_toY ρ hρ a
  have hMx : wnorm ρ (toX ρ a) ≤ M := (wnorm_toX_le_norm ρ hρ a).trans ha
  have hMy : wnorm ρ (toY ρ a) ≤ M := (wnorm_toY_le_norm ρ hρ a).trans ha
  exact twoD_taylor_tree_uniform β b p₁ p₂ ρ M (2 * M) h₁ h₂ k₁ k₂ 0 hβ hb hbρ hk₁ hk₂ hp₁ hp₂
    (ampCoeff β (toX ρ a) (toY ρ a)) (ampCoeff_continuous β _ _)
    (ampEnv β ρ (toX ρ a) (toY ρ a)) (ampEnv_continuous β ρ _ _)
    (fun ij s => ampCoeff_abs_le β ρ hρ _ _ hx hy ij s) hM
    (fun s hs => ampEnv_le_common β ρ hβ hρ _ _ hx M M hMx hMy s hs) T N hN

end Laplace.Grammar
