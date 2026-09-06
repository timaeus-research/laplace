/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StateDensityUniqueCor

/-!
# State density IV: the box form (grammar §4.2)

The general chart standard integral over `(0,b]^{d+1}` with arbitrary continuous `ξ, η` is the
iterated state integral of unit 70 with the last coordinate as the minimal one (Fubini via
`measurePreserving_piFinSuccAbove` at `Fin.last`, as in unit 54). Consequently, when the last
coordinate carries the strictly smallest candidate exponent and `ξ, η` are Lipschitz in it at `0`,

  `∫_{(0,b]^{d+1}} w^h η(w) e^{-βn w^{2k} + β√n w^k ξ(w)} dw ~ C(ξ,η) n^{-p/2}`

with the divisor coefficient `C(ξ,η) = (1/k_d) ∫ v^{h'}(v^{k'})^{-p} A_{p-1}(ξ(v,0)) η(v,0) dv`
(`boxIntegralGen_isEquivalent`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The chart standard integral over the box with general `ξ, η`. -/
noncomputable def boxIntegralGen (β b c : ℝ) {m : ℕ} (k h : Fin m → ℕ)
    (ξ η : (Fin m → ℝ) → ℝ) : ℝ :=
  ∫ w : Fin m → ℝ, (∏ i, w i ^ h i) * η w
    * Real.exp (-β * (c * ∏ i, w i ^ k i) ^ 2 + β * (c * ∏ i, w i ^ k i) * ξ w) ∂(boxMeasure b m)

/-- `Fin.snoc` is continuous in `(v, t)`. -/
theorem continuous_snoc_prod (d : ℕ) :
    Continuous fun x : ℝ × (Fin d → ℝ) => (Fin.snoc x.2 x.1 : Fin (d + 1) → ℝ) := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; exact continuous_fst
  · simp only [Fin.snoc_castSucc]; exact (continuous_apply j).comp continuous_snd

/-- **Fubini bridge**: the box integral is the state integral with the last coordinate minimal. -/
theorem boxIntegralGen_eq_stateIntegral (β b n : ℝ) (hn : 0 ≤ n) {d : ℕ} (k h : Fin (d + 1) → ℕ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η) :
    boxIntegralGen β b (Real.sqrt n) k h ξ η
      = stateIntegral β b n (h (Fin.last d)) (k (Fin.last d)) (fun i => k (Fin.castSucc i))
          (fun i => h (Fin.castSucc i)) (fun u v => ξ (Fin.snoc v u))
          (fun u v => η (Fin.snoc v u)) := by
  unfold boxIntegralGen stateIntegral boxMeasure
  have hmp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => (volume : Measure ℝ).restrict (Ioc 0 b)) (Fin.last d)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d) with he
  set g : ℝ × (Fin d → ℝ) → ℝ := fun y =>
    (∏ j : Fin d, y.2 j ^ h (Fin.castSucc j)) * (y.1 ^ h (Fin.last d) * η (Fin.snoc y.2 y.1)
      * Real.exp (-β * n * (y.1 ^ k (Fin.last d) * ∏ j : Fin d, y.2 j ^ k (Fin.castSucc j)) ^ 2
        + β * Real.sqrt n * (y.1 ^ k (Fin.last d) * ∏ j : Fin d, y.2 j ^ k (Fin.castSucc j))
          * ξ (Fin.snoc y.2 y.1))) with hg
  set F : (Fin (d + 1) → ℝ) → ℝ := fun w => (∏ i, w i ^ h i) * η w
    * Real.exp (-β * (Real.sqrt n * ∏ i, w i ^ k i) ^ 2
      + β * (Real.sqrt n * ∏ i, w i ^ k i) * ξ w) with hF
  have hcomp : ∀ w : Fin (d + 1) → ℝ, F w = g (e w) := by
    intro w
    have h1 : (e w).1 = w (Fin.last d) := rfl
    have h2 : (e w).2 = Fin.init w := by
      funext j
      exact congrArg w (Fin.succAbove_last_apply j)
    have hsn : (Fin.snoc (Fin.init w) (w (Fin.last d)) : Fin (d + 1) → ℝ) = w :=
      Fin.snoc_init_self w
    simp only [hg, hF, h1, h2, hsn]
    rw [Fin.prod_univ_castSucc (fun i : Fin (d + 1) => w i ^ h i),
      Fin.prod_univ_castSucc (fun i : Fin (d + 1) => w i ^ k i)]
    simp only [Fin.init]
    rw [show (Real.sqrt n * ((∏ j : Fin d, w (Fin.castSucc j) ^ k (Fin.castSucc j))
        * w (Fin.last d) ^ k (Fin.last d))) ^ 2
      = n * (w (Fin.last d) ^ k (Fin.last d)
          * ∏ j : Fin d, w (Fin.castSucc j) ^ k (Fin.castSucc j)) ^ 2 by
        rw [mul_pow, Real.sq_sqrt hn]; ring]
    ring_nf
  have hFc : Continuous F := by
    simp only [hF]
    exact ((continuous_prod_pow h).mul hηc).mul (Real.continuous_exp.comp (by fun_prop))
  have hint : Integrable g (((volume : Measure ℝ).restrict (Ioc 0 b)).prod
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b))) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    have : (g ∘ e) = F := funext fun w => (hcomp w).symm
    rw [this]
    exact integrable_box_of_continuous b F hFc
  calc (∫ w, F w ∂(Measure.pi fun _ : Fin (d + 1) => (volume : Measure ℝ).restrict (Ioc 0 b)))
      = ∫ w, g (e w) ∂(Measure.pi fun _ : Fin (d + 1) => (volume : Measure ℝ).restrict (Ioc 0 b)) :=
        integral_congr_ae (Filter.Eventually.of_forall hcomp)
    _ = ∫ y, g y ∂(((volume : Measure ℝ).restrict (Ioc 0 b)).prod
          (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b))) :=
        hmp.integral_comp' g
    _ = ∫ v, (∫ t in Ioc (0 : ℝ) b, g (t, v))
          ∂(Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b)) :=
        integral_prod_symm g hint
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only [hg]
        rw [← MeasureTheory.integral_const_mul]

/-- **State-density theorem in box form**: last coordinate strictly minimal, `ξ, η` continuous and
Lipschitz in it at `0`, `η > 0` on the divisor. -/
theorem boxIntegralGen_isEquivalent (β b : ℝ) (hβ : 0 < β) (hb : 0 < b) {d : ℕ}
    (k h : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (hq : ∀ i : Fin d, ((h (Fin.last d) : ℝ) + 1) / k (Fin.last d)
      < ((h (Fin.castSucc i) : ℝ) + 1) / k (Fin.castSucc i))
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η) (C C' : ℝ) (hC : 0 ≤ C)
    (hξ : ∀ u ∈ Ioc (0 : ℝ) b, ∀ v : Fin d → ℝ, |ξ (Fin.snoc v u) - ξ (Fin.snoc v 0)| ≤ C * u)
    (hη : ∀ u ∈ Ioc (0 : ℝ) b, ∀ v : Fin d → ℝ, |η (Fin.snoc v u) - η (Fin.snoc v 0)| ≤ C' * u)
    (hηpos : ∀ v : Fin d → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) → 0 < η (Fin.snoc v 0)) :
    (fun n : ℝ => boxIntegralGen β b (Real.sqrt n) k h ξ η) ~[atTop]
      fun n : ℝ => (∫ v, divisorDensity β (h (Fin.last d)) (k (Fin.last d))
          (fun i => k (Fin.castSucc i)) (fun i => h (Fin.castSucc i))
          (fun u v => ξ (Fin.snoc v u)) (fun u v => η (Fin.snoc v u)) v ∂(boxMeasure b d))
        * n ^ (-(((h (Fin.last d) : ℝ) + 1) / k (Fin.last d) / 2)) := by
  have hξc' : Continuous fun x : ℝ × (Fin d → ℝ) => ξ (Fin.snoc x.2 x.1) :=
    hξc.comp (continuous_snoc_prod d)
  have hηc' : Continuous fun x : ℝ × (Fin d → ℝ) => η (Fin.snoc x.2 x.1) :=
    hηc.comp (continuous_snoc_prod d)
  have hE := stateIntegral_isEquivalent β b hβ hb (h (Fin.last d)) (k (Fin.last d)) (hk _)
    (fun i => k (Fin.castSucc i)) (fun i => h (Fin.castSucc i)) (fun i => hk _) hq
    (fun u v => ξ (Fin.snoc v u)) (fun u v => η (Fin.snoc v u)) hξc' hηc' C C' hC hξ hη hηpos
  refine hE.congr_left ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with n hn
  exact (boxIntegralGen_eq_stateIntegral β b n hn k h ξ η hξc hηc).symm

end Laplace.Grammar
