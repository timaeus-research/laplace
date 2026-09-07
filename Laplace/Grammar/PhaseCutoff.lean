/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.HeadlinePhase

/-!
# Phase-dressed leading term with a uniform cutoff

Unit 204 (programme D, the transport-only part). The paper's tubular fibres are boxes `(0,ε]^d`;
the phase-dressed leading theorem of units 202–203 on the unit box transports to `(0,b]^d` by the
dilation `u = b·x`, exactly as `CutoffScaling.lean` did for the bare monomial integral:

* `phaseBoxCutoff_eq`: `∫_{(0,b]^d} η u^h e^{-β(Nu^k)²+β(Nu^k)ξ(u)} du
    = b^{∑(hᵢ+1)} ∫_{(0,1]^d} η(bx) x^h e^{-β(N'x^k)²+β(N'x^k)ξ(bx)} dx`, `N' = N b^{∑kᵢ}`;
* `phaseBoxCutoff_tendsto`: the leading coefficient acquires the factor
  `b^{∑ᵢ(hᵢ+1) - 2λ∑ᵢkᵢ} = ∏_{i∉J} b^{hᵢ+1-2kᵢλ}` and the phase/amplitude are composed with the
  dilation (so the face integral is over the face of `(0,b]^d`);
* `headline_phase_leading_cutoff`: the paper-facing form with kernel
  `e^{-βN²u^{2k}+βNu^kξ(u)}` and constant `b^{…}/((m-1)! ∏_{i∈J} kᵢ)`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set
open scoped Pointwise

namespace Laplace.Grammar

/-- The phase-dressed integral on the cutoff box `(0,b]^d`. -/
noncomputable def phaseBoxCutoff (d : ℕ) (h k : Fin d → ℕ) (b β N : ℝ)
    (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ u in cutoffBox d b, η u * ((∏ i, u i ^ h i) * quadKernel β (ξ u) (N * ∏ i, u i ^ k i))

/-- **Dilation**: the cutoff integral is `b^{∑(hᵢ+1)}` times the unit-box integral at `N b^{∑kᵢ}`
with dilated phase and amplitude. -/
theorem phaseBoxCutoff_eq (d : ℕ) (h k : Fin d → ℕ) (b β N : ℝ) (hb : 0 < b)
    (ξ η : (Fin d → ℝ) → ℝ) :
    phaseBoxCutoff d h k b β N ξ η = b ^ (∑ i, (h i + 1)) *
      ∫ x in unitBox d, η (b • x) * ((∏ i, x i ^ h i) *
        quadKernel β (ξ (b • x)) ((N * b ^ (∑ i, k i)) * ∏ i, x i ^ k i)) := by
  unfold phaseBoxCutoff
  rw [cutoffBox_eq_smul d b hb]
  set f : (Fin d → ℝ) → ℝ := fun u =>
    η u * ((∏ i, u i ^ h i) * quadKernel β (ξ u) (N * ∏ i, u i ^ k i)) with hf
  have h1 := MeasureTheory.Measure.setIntegral_comp_smul_of_pos volume f (unitBox d) hb
  rw [Module.finrank_fin_fun, smul_eq_mul] at h1
  have h2 : ∫ x in b • unitBox d, f x = b ^ d * ∫ x in unitBox d, f (b • x) := by
    rw [h1, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hb.ne'), one_mul]
  have h3 : ∫ x in unitBox d, f (b • x) = b ^ (∑ i, h i) *
      ∫ x in unitBox d, η (b • x) * ((∏ i, x i ^ h i) *
        quadKernel β (ξ (b • x)) ((N * b ^ (∑ i, k i)) * ∏ i, x i ^ k i)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitBox d) fun x _ => ?_
    simp only [hf, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [show N * (b ^ (∑ i, k i) * ∏ i, x i ^ k i) = (N * b ^ (∑ i, k i)) * ∏ i, x i ^ k i by ring]
    ring
  change ∫ x in b • unitBox d, f x = _
  rw [h2, h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, pow_add]
  ring

/-- `b^{∑(hᵢ+1) - 2λ∑kᵢ} = b^{∑(hᵢ+1)} · (b^{∑kᵢ})^{-2λ}`. -/
theorem cutoff_power_eq' (d : ℕ) (h k : Fin d → ℕ) (b l : ℝ) (hb : 0 < b) :
    b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) =
      b ^ (∑ i, (h i + 1)) * (b ^ (∑ i, k i)) ^ (-(2 * l)) := by
  rw [← Real.rpow_natCast b (∑ i, (h i + 1)), ← Real.rpow_natCast b (∑ i, k i),
    ← Real.rpow_mul hb.le, ← Real.rpow_add hb]
  congr 1
  push_cast
  ring

/-- **Phase-dressed leading term on `(0,b]^d`**: the unit-box coefficient with dilated phase and
amplitude, times `b^{∑(hᵢ+1) - 2λ∑kᵢ}`. -/
theorem phaseBoxCutoff_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (b l β : ℝ)
    (hb : 0 < b) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (ξ η : (Fin (d + 1) → ℝ) → ℝ) (hξ : Continuous ξ)
    (hη : Continuous η) :
    Tendsto (fun N => phaseBoxCutoff (d + 1) h k b β N ξ η /
        (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) *
        phaseCoeff h k l β (fun x => ξ (b • x)) (fun x => η (b • x)))) := by
  set c : ℝ := b ^ (∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  set r : ℕ := multCount (ratioExp h k) l - 1 with hr
  have hdil : Continuous fun x : Fin (d + 1) → ℝ => b • x := continuous_const_smul b
  have hT := phase_leading_tendsto d h k hk l β hl hβ hmin hatt (fun x => ξ (b • x))
    (fun x => η (b • x)) (hξ.comp hdil) (hη.comp hdil)
  have hT' : Tendsto (fun N => (∫ x in unitBox (d + 1), η (b • x) * ((∏ i, x i ^ h i) *
      quadKernel β (ξ (b • x)) ((N * c) * ∏ i, x i ^ k i))) /
      ((N * c) ^ (-(2 * l)) * Real.log (N * c) ^ r)) atTop
      (𝓝 (phaseCoeff h k l β (fun x => ξ (b • x)) (fun x => η (b • x)))) :=
    hT.comp (tendsto_id.atTop_mul_const hc0)
  have hprod := (hT'.mul (tendsto_log_scale_pow c hc0 r)).const_mul
    (b ^ (∑ i, (h i + 1)) * c ^ (-(2 * l)))
  rw [mul_one] at hprod
  rw [cutoff_power_eq' (d + 1) h k b l hb, ← hc]
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (max 1 (1 / c))] with N hN
  have hN1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : 0 < N := by linarith
  have hNc : 1 < N * c := by
    have : 1 / c < N := lt_of_le_of_lt (le_max_right _ _) hN
    rwa [div_lt_iff₀ hc0] at this
  have hlogN : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
  have hlogNc : Real.log (N * c) ≠ 0 := (Real.log_pos hNc).ne'
  have hpN : N ^ (-(2 * l)) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hpc : c ^ (-(2 * l)) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
  have hlogNr : Real.log N ^ r ≠ 0 := pow_ne_zero _ hlogN
  have hlogNcr : Real.log (N * c) ^ r ≠ 0 := pow_ne_zero _ hlogNc
  rw [phaseBoxCutoff_eq (d + 1) h k b β N hb ξ η, ← hc, Real.mul_rpow hN0.le hc0.le, div_pow]
  field_simp

/-- **Headline XIII with cutoff**: on `(0,b]^d` with the paper's kernel, the limit is
`b^{∑(hᵢ+1)-2λ∑kᵢ}/((m-1)! ∏_{i∈J} kᵢ) · ∫ η(b·πu) J_p(ξ(b·πu)) ∏_{i∉J} uᵢ^{hᵢ-pkᵢ} du`. -/
theorem headline_phase_leading_cutoff (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (b l β : ℝ) (hb : 0 < b) (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) (ξ η : (Fin (m + 1) → ℝ) → ℝ)
    (hξ : Continuous ξ) (hη : Continuous η) :
    Tendsto (fun N : ℝ => (∫ u in cutoffBox (m + 1) b, η u * ((∏ i, u i ^ h i) *
        Real.exp (-(β * N ^ 2 * ∏ i, u i ^ (2 * k i)) + β * (N * ∏ i, u i ^ k i) * ξ u))) /
        (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) /
          (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
            ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
        ∫ u in unitBox (m + 1),
          (η (b • faceProj h k l u) * phaseMoment β (2 * l) (ξ (b • faceProj h k l u))) *
            residualWeight h k l u)) := by
  have hT := phaseBoxCutoff_tendsto m h k hk b l β hb hl hβ hmin hatt ξ η hξ hη
  rw [phaseCoeff, two_pow_mul_faceNorm h k l (multCount_pos_of_att h k l hatt)] at hT
  have hconst : b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) *
      (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
        ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
      ∫ u in unitBox (m + 1), ((fun x => η (b • x)) (faceProj h k l u) *
        phaseMoment β (2 * l) ((fun x => ξ (b • x)) (faceProj h k l u))) *
          residualWeight h k l u) =
      b ^ (((∑ i, (h i + 1) : ℕ) : ℝ) - 2 * l * ((∑ i, k i : ℕ) : ℝ)) /
          (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
            ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
        ∫ u in unitBox (m + 1),
          (η (b • faceProj h k l u) * phaseMoment β (2 * l) (ξ (b • faceProj h k l u))) *
            residualWeight h k l u := by
    ring
  rw [hconst] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  unfold phaseBoxCutoff
  congr 1
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun u _ => ?_
  rw [paperKernel_eq_quadKernel]

end Laplace.Grammar
