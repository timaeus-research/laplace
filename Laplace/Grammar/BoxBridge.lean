/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MultiplicityGeneral

/-!
# The multiplicity-`m` theorem in box form (grammar §4.2, `thm:TaylorTree` leading term)

The chart standard integral over the genuine box `(0,b]^{d'+m}` with general continuous `ξ, η`
(`boxIntegralGen`, unit 72) is identified by Fubini with the block state integral of unit 77, the
first `d'` coordinates being noncritical and the last `m` forming the minimal block
(`boxIntegralGen_eq_blockStateIntegral`). Consequently, when the last `m = d₀+1` exponents are equal
to `p` and the first `d'` exceed `p`,

  `∫_{(0,b]^{d'+m}} w^H η(w) e^{-βn w^{2K} + β√n w^K ξ(w)} dw
      ~ (C(ξ,η)/2^{d₀}) n^{-p/2} (log n)^{d₀}`

with `C(ξ,η) = (∏ kᵢ⁻¹)/d₀! ∫ v^{h'}(v^{k'})^{-p} A_{p-1}(ξ(v,0)) η(v,0) dv`
(`boxIntegralGen_mult_isEquivalent`), together with the free-energy form
(`boxIntegralGen_mult_freeEnergy`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- Splitting `Fin (d' + m) → ℝ` as `(Fin d' → ℝ) × (Fin m → ℝ)`. -/
noncomputable def splitEquiv (d' m : ℕ) : (Fin (d' + m) → ℝ) ≃ᵐ (Fin d' → ℝ) × (Fin m → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (d' + m) => ℝ)
    (finSumFinEquiv : Fin d' ⊕ Fin m ≃ Fin (d' + m))).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d' ⊕ Fin m => ℝ)

theorem splitEquiv_measurePreserving (b : ℝ) (d' m : ℕ) :
    MeasurePreserving (splitEquiv d' m) (boxMeasure b (d' + m))
      ((boxMeasure b d').prod (boxMeasure b m)) := by
  have h1 := (measurePreserving_piCongrLeft
    (μ := fun _ : Fin (d' + m) => (volume : Measure ℝ).restrict (Ioc 0 b))
    (finSumFinEquiv : Fin d' ⊕ Fin m ≃ Fin (d' + m))).symm
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin d' ⊕ Fin m => ℝ)
    (fun _ => (volume : Measure ℝ).restrict (Ioc 0 b))
  unfold boxMeasure
  exact h2.comp h1

theorem splitEquiv_symm_apply (d' m : ℕ) (v : Fin d' → ℝ) (u : Fin m → ℝ) :
    (splitEquiv d' m).symm (v, u) = Fin.append v u := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    show (MeasurableEquiv.piCongrLeft (fun _ : Fin (d' + m) => ℝ) finSumFinEquiv)
      ((MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d' ⊕ Fin m => ℝ).symm (v, u))
        (finSumFinEquiv (Sum.inl j)) = v j
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  · rw [Fin.append_right]
    show (MeasurableEquiv.piCongrLeft (fun _ : Fin (d' + m) => ℝ) finSumFinEquiv)
      ((MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d' ⊕ Fin m => ℝ).symm (v, u))
        (finSumFinEquiv (Sum.inr j)) = u j
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rfl

/-- `Fin.append` is continuous in the pair. -/
theorem continuous_append (d' m : ℕ) :
    Continuous fun x : (Fin d' → ℝ) × (Fin m → ℝ) => (Fin.append x.1 x.2 : Fin (d' + m) → ℝ) := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]; exact (continuous_apply j).comp continuous_fst
  · simp only [Fin.append_right]; exact (continuous_apply j).comp continuous_snd

/-- Products over `Fin (d' + m)` of an appended vector split. -/
theorem prod_append_pow (d' m : ℕ) (v : Fin d' → ℝ) (u : Fin m → ℝ) (H : Fin (d' + m) → ℕ) :
    ∏ i, Fin.append v u i ^ H i
      = (∏ j, v j ^ H (Fin.castAdd m j)) * ∏ i, u i ^ H (Fin.natAdd d' i) := by
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **Fubini bridge**: the box integral over `(0,b]^{d'+m}` is the block state integral with the
first `d'` coordinates noncritical and the last `m` forming the block. -/
theorem boxIntegralGen_eq_blockStateIntegral (β b N : ℝ) {d' m : ℕ} (K H : Fin (d' + m) → ℕ)
    (ξ η : (Fin (d' + m) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η) :
    boxIntegralGen β b N K H ξ η
      = blockStateIntegral β b N (fun i => K (Fin.natAdd d' i)) (fun i => H (Fin.natAdd d' i))
          (fun j => K (Fin.castAdd m j)) (fun j => H (Fin.castAdd m j))
          (fun u v => ξ (Fin.append v u)) (fun u v => η (Fin.append v u)) := by
  have hmp := splitEquiv_measurePreserving b d' m
  set F : (Fin (d' + m) → ℝ) → ℝ := fun w => (∏ i, w i ^ H i) * η w
    * Real.exp (-β * (N * ∏ i, w i ^ K i) ^ 2 + β * (N * ∏ i, w i ^ K i) * ξ w) with hF
  have hFc : Continuous F := by
    simp only [hF]
    exact ((continuous_prod_pow H).mul hηc).mul (Real.continuous_exp.comp (by fun_prop))
  have hG : (fun z : (Fin d' → ℝ) × (Fin m → ℝ) => F ((splitEquiv d' m).symm z))
      = fun z => F (Fin.append z.1 z.2) := by
    funext z
    rw [← splitEquiv_symm_apply d' m z.1 z.2]
  have hGc : Continuous fun z : (Fin d' → ℝ) × (Fin m → ℝ) => F (Fin.append z.1 z.2) :=
    hFc.comp (continuous_append d' m)
  have hstep1 : boxIntegralGen β b N K H ξ η
      = ∫ z, F ((splitEquiv d' m).symm z) ∂((boxMeasure b d').prod (boxMeasure b m)) := by
    rw [← hmp.integral_comp' (fun z => F ((splitEquiv d' m).symm z))]
    unfold boxIntegralGen
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    beta_reduce
    rw [MeasurableEquiv.symm_apply_apply]
  rw [hstep1, hG, integral_prod _ (integrable_box_prod_of_continuous b _ hGc)]
  unfold blockStateIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  beta_reduce
  simp only [hF, prod_append_pow, quadKernel]
  rw [show N * ((∏ j, v j ^ K (Fin.castAdd m j)) * ∏ i, u i ^ K (Fin.natAdd d' i))
    = N * (∏ j, v j ^ K (Fin.castAdd m j)) * ∏ i, u i ^ K (Fin.natAdd d' i) by ring]
  ring_nf

/-- **The multiplicity-`m` theorem in box form** (`thm:TaylorTree` leading term for general
continuous `ξ, η`): last `d₀+1` exponents equal to `p`, first `d'` exponents `> p`,
`η > 0` on the minimal face. -/
theorem boxIntegralGen_mult_isEquivalent (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d' d₀ : ℕ}
    (K H : Fin (d' + (d₀ + 1)) → ℕ) (hK : ∀ i, 0 < K i)
    (hp : ∀ i : Fin (d₀ + 1), ((H (Fin.natAdd d' i) : ℝ) + 1) / K (Fin.natAdd d' i) = p)
    (hq : ∀ j : Fin d', p < ((H (Fin.castAdd (d₀ + 1) j) : ℝ) + 1) / K (Fin.castAdd (d₀ + 1) j))
    (ξ η : (Fin (d' + (d₀ + 1)) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η)
    (hηpos : ∀ v : Fin d' → ℝ, (∀ j, 0 < v j ∧ v j ≤ b) → 0 < η (Fin.append v 0)) :
    (fun n : ℝ => boxIntegralGen β b (Real.sqrt n) K H ξ η) ~[atTop]
      fun n : ℝ => blockCoeff β b p (fun i => K (Fin.natAdd d' i))
          (fun j => K (Fin.castAdd (d₀ + 1) j)) (fun j => H (Fin.castAdd (d₀ + 1) j))
          (fun u v => ξ (Fin.append v u)) (fun u v => η (Fin.append v u)) / 2 ^ d₀
        * (n ^ (-(p / 2)) * Real.log n ^ d₀) := by
  have hξc' : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => ξ (Fin.append x.2 x.1) :=
    hξc.comp ((continuous_append d' (d₀ + 1)).comp (continuous_snd.prodMk continuous_fst))
  have hηc' : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => η (Fin.append x.2 x.1) :=
    hηc.comp ((continuous_append d' (d₀ + 1)).comp (continuous_snd.prodMk continuous_fst))
  have hE := blockStateIntegral_sqrt_isEquivalent β b p hβ hb (fun i => K (Fin.natAdd d' i))
    (fun i => H (Fin.natAdd d' i)) (fun i => hK _) (fun i => hp i)
    (fun j => K (Fin.castAdd (d₀ + 1) j)) (fun j => H (Fin.castAdd (d₀ + 1) j)) (fun j => hK _) hq
    (fun u v => ξ (Fin.append v u)) (fun u v => η (Fin.append v u)) hξc' hηc' hηpos
  refine hE.congr_left (Filter.Eventually.of_forall fun n => ?_)
  exact (boxIntegralGen_eq_blockStateIntegral β b (Real.sqrt n) K H ξ η hξc hηc).symm

/-- **Free-energy form**: `−log Z = (p/2) log n − d₀ log log n + F₀ + o(1)`. -/
theorem boxIntegralGen_mult_freeEnergy (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d' d₀ : ℕ}
    (K H : Fin (d' + (d₀ + 1)) → ℕ) (hK : ∀ i, 0 < K i)
    (hp : ∀ i : Fin (d₀ + 1), ((H (Fin.natAdd d' i) : ℝ) + 1) / K (Fin.natAdd d' i) = p)
    (hq : ∀ j : Fin d', p < ((H (Fin.castAdd (d₀ + 1) j) : ℝ) + 1) / K (Fin.castAdd (d₀ + 1) j))
    (ξ η : (Fin (d' + (d₀ + 1)) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η)
    (hηpos : ∀ v : Fin d' → ℝ, (∀ j, 0 < v j ∧ v j ≤ b) → 0 < η (Fin.append v 0)) :
    ∃ F₀ : ℝ, Tendsto (fun n : ℝ => -Real.log (boxIntegralGen β b (Real.sqrt n) K H ξ η)
      - (p / 2 * Real.log n - (d₀ : ℕ) * Real.log (Real.log n))) atTop (𝓝 F₀) := by
  have hE := boxIntegralGen_mult_isEquivalent β b p hβ hb K H hK hp hq ξ η hξc hηc hηpos
  have hp0 : 0 < p := by
    rw [← hp 0]
    have := hK (Fin.natAdd d' 0)
    positivity
  have hC : 0 < blockCoeff β b p (fun i => K (Fin.natAdd d' i))
      (fun j => K (Fin.castAdd (d₀ + 1) j)) (fun j => H (Fin.castAdd (d₀ + 1) j))
      (fun u v => ξ (Fin.append v u))
      (fun u v => η (Fin.append v u)) / 2 ^ d₀ := by
    refine div_pos ?_ (by positivity)
    refine integral_blockDivisorDensity_pos β b p hβ hb hp0 _ (toNatFun_pos _ fun i => hK _) _ _ _
      (fun j => hK _) hq _ _ ?_ ?_ hηpos
    · exact hξc.comp ((continuous_append d' (d₀ + 1)).comp (continuous_id.prodMk continuous_const))
    · exact hηc.comp ((continuous_append d' (d₀ + 1)).comp (continuous_id.prodMk continuous_const))
  refine ⟨-Real.log (blockCoeff β b p (fun i => K (Fin.natAdd d' i))
    (fun j => K (Fin.castAdd (d₀ + 1) j)) (fun j => H (Fin.castAdd (d₀ + 1) j))
    (fun u v => ξ (Fin.append v u)) (fun u v => η (Fin.append v u)) / 2 ^ d₀), ?_⟩
  have := (tendsto_log_of_isEquivalent_powLog hC hE).neg
  refine this.congr' (Filter.Eventually.of_forall fun n => ?_)
  push_cast
  ring_nf

end Laplace.Grammar
