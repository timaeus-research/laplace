/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.HeadlineStochasticAssembly
import Laplace.Grammar.SymmetricAmplitudeAsymptotic

/-!
# The signed-reflection identity for arbitrary continuous integrands

Unit 216 (Astra #23 programme D2, step 1). Unit 196 reduced the zero-phase dressed integral over
the symmetric box `(-1,1]^d` to the unit box by reflecting each coordinate. With a phase the kernel
is no longer a function of `x^{2k}` alone, so we need the reflection identity for an **arbitrary
continuous integrand**:
```
∫_{(-1,1]^d} F(x) dx = ∑_{σ ∈ {±1}^d} ∫_{(0,1]^d} F(σ·u) du            (integral_symBox_eq_sum_reflect)
```
(`reflect σ u = (σᵢ uᵢ)ᵢ`, `sgn true = -1`, `sgn false = 1`). Applied to the phase-dressed integrand
in unit 217: on the orthant `σ`, `x^{2k} = u^{2k}` and `x^k ξ(x) = ε_σ u^k ξ(σu)` with
`ε_σ = ∏ σᵢ^{kᵢ}`, so each orthant is a Headline XIII chart with phase `ε_σ ξ∘σ` and amplitude
`(∏ σᵢ^{hᵢ}) η∘σ` (signed monomial density) or `η∘σ` (absolute density `|x|^h`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- A continuous function is integrable on any half-open box. -/
theorem integrableOn_piBox_Ioc_of_continuous (d : ℕ) (a b : ℝ) (F : (Fin d → ℝ) → ℝ)
    (hF : Continuous F) : IntegrableOn F (piBox d (Ioc a b)) :=
  (hF.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (pi_mono fun _ _ => Ioc_subset_Icc_self)

/-- **Signed-reflection identity for continuous integrands**:
`∫_{(-1,1]^d} F = ∑_σ ∫_{(0,1]^d} F(σ·u)`. -/
theorem integral_symBox_eq_sum_reflect :
    ∀ (d : ℕ) (F : (Fin d → ℝ) → ℝ), Continuous F →
      ∫ x in symBox d, F x = ∑ σ : Fin d → Bool, ∫ u in unitBox d, F (reflect σ u) := by
  intro d
  induction d with
  | zero =>
    intro F _
    have hu : unitBox 0 = piBox 0 (Ioc (0 : ℝ) 1) := rfl
    unfold symBox
    rw [hu, integral_piBox_zero, Fintype.sum_unique, integral_piBox_zero]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ d ih =>
    intro F hF
    have hu : unitBox (d + 1) = piBox (d + 1) (Ioc (0 : ℝ) 1) := rfl
    have hu' : unitBox d = piBox d (Ioc (0 : ℝ) 1) := rfl
    unfold symBox
    rw [integral_pi_box_succ d _ _ (integrableOn_piBox_Ioc_of_continuous (d + 1) (-1) 1 F hF)]
    have hIH : ∀ a : ℝ, ∫ b in piBox d (Ioc (-1 : ℝ) 1), F (Fin.cons a b) =
        ∑ τ : Fin d → Bool, ∫ v in unitBox d, F (Fin.cons a (reflect τ v)) := fun a => by
      have := ih (fun w => F (Fin.cons a w)) (hF.comp (continuous_finCons d a))
      simpa [symBox, hu'] using this
    simp_rw [hIH]
    have hG : IntegrableOn (fun a : ℝ =>
        ∑ τ : Fin d → Bool, ∫ v in unitBox d, F (Fin.cons a (reflect τ v))) (Ioc (-1 : ℝ) 1) := by
      have hm := integrableOn_pi_box_marginal d (Ioc (-1 : ℝ) 1) F
        (integrableOn_piBox_Ioc_of_continuous (d + 1) (-1) 1 F hF)
      refine hm.congr_fun (fun a _ => ?_) measurableSet_Ioc
      beta_reduce
      rw [hIH a]
    rw [integral_Ioc_symm_add _ hG]
    rw [← (Fin.consEquiv fun _ : Fin (d + 1) => Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    have hR : ∀ (b : Bool) (τ : Fin d → Bool),
        ∫ u in unitBox (d + 1), F (reflect (Fin.cons b τ) u) =
          ∫ a in Ioc (0 : ℝ) 1, ∫ v in unitBox d, F (Fin.cons (sgn b * a) (reflect τ v)) := by
      intro b τ
      rw [hu, integral_pi_box_succ d _ (fun u => F (reflect (Fin.cons b τ) u))
        (integrableOn_piBox_Ioc_of_continuous (d + 1) 0 1 (fun u => F (reflect (Fin.cons b τ) u))
          (hF.comp (continuous_reflect _)))]
      refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
      refine setIntegral_congr_fun (measurableSet_piBox d _ measurableSet_Ioc) fun v _ => ?_
      rw [reflect_cons]
    simp_rw [hR]
    have hint : ∀ (b : Bool) (τ : Fin d → Bool), IntegrableOn (fun a : ℝ =>
        ∫ v in unitBox d, F (Fin.cons (sgn b * a) (reflect τ v))) (Ioc (0 : ℝ) 1) := by
      intro b τ
      have hm := integrableOn_pi_box_marginal d (Ioc (0 : ℝ) 1)
        (fun x => F (reflect (Fin.cons b τ) x))
        (integrableOn_piBox_Ioc_of_continuous (d + 1) 0 1 (fun x => F (reflect (Fin.cons b τ) x))
          (hF.comp (continuous_reflect _)))
      refine hm.congr_fun (fun a _ => ?_) measurableSet_Ioc
      beta_reduce
      refine setIntegral_congr_fun (measurableSet_piBox d _ measurableSet_Ioc) fun v _ => ?_
      rw [reflect_cons]
    rw [← integral_finsetSum _ fun τ _ => hint true τ,
      ← integral_finsetSum _ fun τ _ => hint false τ,
      ← integral_add (integrable_finsetSum _ fun τ _ => hint true τ)
        (integrable_finsetSum _ fun τ _ => hint false τ)]
    refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
    simp only [sgn, Bool.false_eq_true, ↓reduceIte, neg_one_mul, one_mul]
    rw [add_comm]

end Laplace.Grammar
