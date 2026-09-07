/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseLipschitz

/-!
# Lipschitz dependence of the limit coefficient on phase and amplitude

Unit 210 (programme A2, step 2). The limit functional of Headline XIII,
`(ξ, η) ↦ phaseCoeff h k λ β ξ η = D ∫ η(πu) J_p(ξ(πu)) w(u) du`, is Lipschitz in sup norm on
bounded input sets:
```
|phaseCoeff(ξ,η) − phaseCoeff(ξ',η')| ≤ D (‖η−η'‖ J_p(M) + β A ‖ξ−ξ'‖ J_{p+1}(M)) ∫ w
```
for `|ξ|, |ξ'| ≤ M`, `|η'| ≤ A` on the closed cube, where `J_p(a) = phaseMoment β p a` and
`J_{p+1}(M) = ∫ s^p e^{-βs²+βMs} ds` (`phaseCoeff_sub_le`). Ingredients: monotonicity of `J_p` in
the phase (`phaseMoment_le_of_le`) and the moment-level Lipschitz bound
`|J_p(a) − J_p(a')| ≤ β |a − a'| J_{p+1}(M)` (`phaseMoment_sub_le`), both from the kernel bounds of
unit 209. Together with `normalised_lipschitz_eventually` this gives equi-Lipschitz control of the
whole family `{F_N}_{N ≥ N₀} ∪ {F}` on bounded input sets. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- Monotonicity of the dressed normal moment in the phase. -/
theorem phaseMoment_le_of_le (β p a M : ℝ) (hβ : 0 < β) (hp : 0 < p) (haM : a ≤ M) :
    phaseMoment β p a ≤ phaseMoment β p M := by
  unfold phaseMoment
  refine setIntegral_mono_on (phaseMoment_integrand_integrableOn β p a hβ hp)
    (phaseMoment_integrand_integrableOn β p M hβ hp) measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  exact mul_le_mul_of_nonneg_left (quadKernel_le_of_le β a M s hβ hs0.le haM)
    (Real.rpow_nonneg hs0.le _)

/-- **Lipschitz bound for the dressed normal moment**:
`|J_p(a) − J_p(a')| ≤ β |a − a'| J_{p+1}(M)` for `|a|, |a'| ≤ M`. -/
theorem phaseMoment_sub_le (β p a a' M : ℝ) (hβ : 0 < β) (hp : 0 < p) (ha : |a| ≤ M)
    (ha' : |a'| ≤ M) :
    |phaseMoment β p a - phaseMoment β p a'| ≤ β * |a - a'| * phaseMoment β (p + 1) M := by
  unfold phaseMoment
  rw [← integral_sub (phaseMoment_integrand_integrableOn β p a hβ hp)
    (phaseMoment_integrand_integrableOn β p a' hβ hp)]
  have hbd : IntegrableOn (fun s : ℝ => β * |a - a'| * (s ^ (p + 1 - 1) * quadKernel β M s))
      (Ioi 0) :=
    (phaseMoment_integrand_integrableOn β (p + 1) M hβ (by positivity)).const_mul _
  have hpt : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖s ^ (p - 1) * quadKernel β a s - s ^ (p - 1) * quadKernel β a' s‖ ≤
        β * |a - a'| * (s ^ (p + 1 - 1) * quadKernel β M s) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := hs
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
      show p + 1 - 1 = (p - 1) + 1 by ring, Real.rpow_add_one hs0.ne']
    calc s ^ (p - 1) * |quadKernel β a s - quadKernel β a' s|
        ≤ s ^ (p - 1) * (β * s * |a - a'| * quadKernel β M s) :=
          mul_le_mul_of_nonneg_left (quadKernel_sub_le β a a' M s hβ hs0.le ha ha')
            (Real.rpow_nonneg hs0.le _)
      _ = β * |a - a'| * (s ^ (p - 1) * s * quadKernel β M s) := by ring
  have h := norm_integral_le_of_norm_le hbd hpt
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h

/-- **Lipschitz dependence of the limit coefficient**: for continuous inputs with `|ξ|, |ξ'| ≤ M`,
`|η'| ≤ A`, `|ξ − ξ'| ≤ δξ`, `|η − η'| ≤ δη` on the closed cube,
`|phaseCoeff(ξ,η) − phaseCoeff(ξ',η')| ≤ D (δη J_{2λ}(M) + β A δξ J_{2λ+1}(M)) ∫ w`. -/
theorem phaseCoeff_sub_le (d : ℕ) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β M A δξ δη : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (ξ ξ' η η' : (Fin d → ℝ) → ℝ) (hξ : Continuous ξ) (hξ' : Continuous ξ') (hη : Continuous η)
    (hη' : Continuous η') (hξM : ∀ x ∈ closedCube d, |ξ x| ≤ M)
    (hξ'M : ∀ x ∈ closedCube d, |ξ' x| ≤ M) (hη'A : ∀ x ∈ closedCube d, |η' x| ≤ A)
    (hδξ : ∀ x ∈ closedCube d, |ξ x - ξ' x| ≤ δξ) (hδη : ∀ x ∈ closedCube d, |η x - η' x| ≤ δη) :
    |phaseCoeff h k l β ξ η - phaseCoeff h k l β ξ' η'| ≤
      2 ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l *
        ((δη * phaseMoment β (2 * l) M + β * A * δξ * phaseMoment β (2 * l + 1) M) *
          ∫ u in unitBox d, residualWeight h k l u) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hη'A 0 fun i _ => ⟨le_rfl, zero_le_one⟩)
  have hδξ0 : 0 ≤ δξ := (abs_nonneg _).trans (hδξ 0 fun i _ => ⟨le_rfl, zero_le_one⟩)
  have hδη0 : 0 ≤ δη := (abs_nonneg _).trans (hδη 0 fun i _ => ⟨le_rfl, zero_le_one⟩)
  have hp : (0 : ℝ) < 2 * l := by positivity
  have hcont : Continuous fun a => phaseMoment β (2 * l) a := continuous_phaseMoment β (2 * l) hβ hp
  have hI : IntegrableOn (fun u => (η (faceProj h k l u) *
      phaseMoment β (2 * l) (ξ (faceProj h k l u))) * residualWeight h k l u) (unitBox d) :=
    integrableOn_face_mul h k hk l hmin (fun x => η x * phaseMoment β (2 * l) (ξ x))
      (hη.mul (hcont.comp hξ))
  have hI' : IntegrableOn (fun u => (η' (faceProj h k l u) *
      phaseMoment β (2 * l) (ξ' (faceProj h k l u))) * residualWeight h k l u) (unitBox d) :=
    integrableOn_face_mul h k hk l hmin (fun x => η' x * phaseMoment β (2 * l) (ξ' x))
      (hη'.mul (hcont.comp hξ'))
  have hbd : IntegrableOn (fun u => (δη * phaseMoment β (2 * l) M +
      β * A * δξ * phaseMoment β (2 * l + 1) M) * residualWeight h k l u) (unitBox d) :=
    (residualWeight_integrableOn h k hk l hmin).const_mul _
  have hpt : ∀ᵐ u ∂(volume.restrict (unitBox d)),
      ‖(η (faceProj h k l u) * phaseMoment β (2 * l) (ξ (faceProj h k l u))) *
          residualWeight h k l u -
        (η' (faceProj h k l u) * phaseMoment β (2 * l) (ξ' (faceProj h k l u))) *
          residualWeight h k l u‖ ≤
      (δη * phaseMoment β (2 * l) M + β * A * δξ * phaseMoment β (2 * l + 1) M) *
        residualWeight h k l u := by
    refine (ae_restrict_iff' (measurableSet_unitBox _)).2 (Eventually.of_forall fun u hu => ?_)
    have hπ : faceProj h k l u ∈ closedCube d := faceProj_mapsTo h k l hu
    have hw := residualWeight_nonneg h k l u hu
    set v := faceProj h k l u with hv
    have hJpos := phaseMoment_pos β (2 * l) (ξ v) hβ hp
    have hJle := phaseMoment_le_of_le β (2 * l) (ξ v) M hβ hp ((le_abs_self _).trans (hξM v hπ))
    have hJsub := phaseMoment_sub_le β (2 * l) (ξ v) (ξ' v) M hβ hp (hξM v hπ) (hξ'M v hπ)
    have hdecomp : η v * phaseMoment β (2 * l) (ξ v) - η' v * phaseMoment β (2 * l) (ξ' v) =
        (η v - η' v) * phaseMoment β (2 * l) (ξ v) +
          η' v * (phaseMoment β (2 * l) (ξ v) - phaseMoment β (2 * l) (ξ' v)) := by ring
    rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, hdecomp]
    refine mul_le_mul_of_nonneg_right ?_ hw
    calc |(η v - η' v) * phaseMoment β (2 * l) (ξ v) +
          η' v * (phaseMoment β (2 * l) (ξ v) - phaseMoment β (2 * l) (ξ' v))|
        ≤ |η v - η' v| * phaseMoment β (2 * l) (ξ v) +
          |η' v| * |phaseMoment β (2 * l) (ξ v) - phaseMoment β (2 * l) (ξ' v)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos hJpos]
      _ ≤ δη * phaseMoment β (2 * l) M + A * (β * |ξ v - ξ' v| * phaseMoment β (2 * l + 1) M) := by
          gcongr
          · exact hδη v hπ
          · exact hη'A v hπ
      _ ≤ δη * phaseMoment β (2 * l) M + A * (β * δξ * phaseMoment β (2 * l + 1) M) := by
          gcongr
          all_goals first
            | exact hδξ v hπ
            | exact (phaseMoment_pos β (2 * l + 1) M hβ (by positivity)).le
      _ = δη * phaseMoment β (2 * l) M + β * A * δξ * phaseMoment β (2 * l + 1) M := by ring
  have hnorm := norm_integral_le_of_norm_le hbd hpt
  rw [Real.norm_eq_abs, integral_const_mul] at hnorm
  unfold phaseCoeff
  rw [← mul_sub, ← integral_sub hI hI', abs_mul,
    abs_of_nonneg (by have := faceNorm_nonneg h k l; positivity)]
  exact mul_le_mul_of_nonneg_left hnorm (by have := faceNorm_nonneg h k l; positivity)

end Laplace.Grammar
