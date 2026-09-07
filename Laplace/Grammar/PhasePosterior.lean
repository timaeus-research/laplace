/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseCutoff

/-!
# The per-stratum posterior expectation in general dimension

Unit 205 (Headline XIV). The paper's per-stratum expectation is a quotient of two dressed normal
integrals with the same phase: numerator amplitude `φ·c` (observable times density), denominator
amplitude `c`. Both are Headline XIII limits at the same scale, and the denominator's coefficient
is strictly positive when `c > 0` on the cube, so the quotient converges:
```
∫ φ c u^h e^{-β(Nu^k)²+β(Nu^k)ξ} / ∫ c u^h e^{-β(Nu^k)²+β(Nu^k)ξ}
  → ∫ φ(πu) c(πu) J_p(ξ(πu)) w(u) du / ∫ c(πu) J_p(ξ(πu)) w(u) du,
```
`w = ∏_{i∉J} uᵢ^{hᵢ-pkᵢ}`: the posterior expectation of `φ` concentrates on the face `u_J = 0`
with density `c·J_p(ξ)·w`. In the equal-ratio case the face is the corner and the limit is `φ(0)`.

* `continuous_faceProj`, `phaseMoment_pos`, `integral_residualWeight_pos`, `faceNorm_pos`;
* `phaseCoeff_pos`: `0 < phaseCoeff h k λ β ξ c` for continuous `ξ` and continuous `c > 0`;
* `phase_posterior_tendsto`: the quotient limit (coefficient form);
* `headline_phase_posterior`: paper kernel, explicit face-density form;
* `phaseCoeff_equal`, `headline_phase_posterior_equal`: equal ratios, limit `φ(0)`.

Scope as in Headline XIII: deterministic fixed phase, one unit-box chart, boundary-type
coordinates; the paper's global posterior additionally needs chart assembly. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

theorem faceProj_mem_closedCube {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) : faceProj h k l u ∈ closedCube d := by
  intro i _
  simp only [faceProj]
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact hu i (mem_univ i)

theorem continuous_faceProj {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) : Continuous (faceProj h k l) := by
  refine continuous_pi fun i => ?_
  unfold faceProj
  split_ifs
  · exact continuous_const
  · exact continuous_apply i

/-- `J_p(a) > 0`. -/
theorem phaseMoment_pos (β p a : ℝ) (hβ : 0 < β) (hp : 0 < p) : 0 < phaseMoment β p a := by
  rw [phaseMoment, setIntegral_pos_iff_support_of_nonneg_ae ?_
    (phaseMoment_integrand_integrableOn β p a hβ hp)]
  · have hsub : Ioi (0 : ℝ) ⊆ Function.support
        (fun s : ℝ => s ^ (p - 1) * quadKernel β a s) ∩ Ioi 0 := by
      intro s hs
      have hs0 : (0 : ℝ) < s := hs
      refine ⟨?_, hs⟩
      rw [Function.mem_support]
      exact (mul_pos (Real.rpow_pos_of_pos hs0 _) (quadKernel_pos β a s)).ne'
    calc (0 : ENNReal) < volume (Ioi (0 : ℝ)) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
      _ ≤ _ := measure_mono hsub
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs
    exact mul_nonneg (Real.rpow_nonneg hs0.le _) (quadKernel_pos β a s).le

/-- `∫_{(0,1]^d} ∏_{i∉J} uᵢ^{hᵢ-2kᵢλ} du > 0`. -/
theorem integral_residualWeight_pos {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) :
    0 < ∫ u in unitBox d, residualWeight h k l u := by
  have h1 := amplitudeCoeff_const h k hk l β hmin 1
  unfold amplitudeCoeff at h1
  simp only [one_mul] at h1
  have hM := monomialMixedConst_pos h k hk l β hl hβ hmin
  rw [← h1] at hM
  exact pos_of_mul_pos_right hM (faceLeadConst_pos h k hk l β hl hβ).le

theorem faceNorm_pos {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) :
    0 < faceNorm h k l := by
  unfold faceNorm
  refine mul_pos (by positivity) (Finset.prod_pos fun i _ => ?_)
  split_ifs
  · have := hk i
    positivity
  · exact one_pos

/-- **Positivity of the dressed denominator coefficient**: for continuous `ξ` and continuous `c > 0`
on the closed cube, `phaseCoeff h k λ β ξ c > 0`. -/
theorem phaseCoeff_pos (d : ℕ) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l)
    (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (ξ c : (Fin d → ℝ) → ℝ) (hξ : Continuous ξ)
    (hc : Continuous c) (hcpos : ∀ x ∈ closedCube d, 0 < c x) :
    0 < phaseCoeff h k l β ξ c := by
  unfold phaseCoeff
  refine mul_pos (mul_pos (by positivity) (faceNorm_pos h k hk l)) ?_
  -- the face density `G u = c(πu) J_p(ξ(πu))` is continuous and positive on the cube
  set G : (Fin d → ℝ) → ℝ := fun u =>
    c (faceProj h k l u) * phaseMoment β (2 * l) (ξ (faceProj h k l u)) with hG
  have hGc : Continuous G := (hc.comp (continuous_faceProj h k l)).mul
    ((continuous_phaseMoment β (2 * l) hβ (by positivity)).comp
      (hξ.comp (continuous_faceProj h k l)))
  have hGpos : ∀ u ∈ closedCube d, 0 < G u := fun u hu =>
    mul_pos (hcpos _ (faceProj_mem_closedCube h k l hu))
      (phaseMoment_pos β (2 * l) _ hβ (by positivity))
  obtain ⟨x₀, hx₀, hmin₀⟩ := (isCompact_closedCube d).exists_isMinOn
    ⟨0, fun i _ => ⟨le_rfl, zero_le_one⟩⟩ hGc.continuousOn
  have hg0 : 0 < G x₀ := hGpos x₀ hx₀
  have hint₁ : IntegrableOn (fun u => G x₀ * residualWeight h k l u) (unitBox d) :=
    (residualWeight_integrableOn h k hk l hmin).const_mul _
  have hint₂ : IntegrableOn (fun u => (c (faceProj h k l u) *
      phaseMoment β (2 * l) (ξ (faceProj h k l u))) * residualWeight h k l u) (unitBox d) :=
    integrableOn_face_mul h k hk l hmin (fun x => c x * phaseMoment β (2 * l) (ξ x))
      (hc.mul ((continuous_phaseMoment β (2 * l) hβ (by positivity)).comp hξ))
  calc (0 : ℝ) < G x₀ * ∫ u in unitBox d, residualWeight h k l u :=
        mul_pos hg0 (integral_residualWeight_pos h k hk l β hl hβ hmin)
    _ = ∫ u in unitBox d, G x₀ * residualWeight h k l u := (integral_const_mul _ _).symm
    _ ≤ ∫ u in unitBox d, (c (faceProj h k l u) *
          phaseMoment β (2 * l) (ξ (faceProj h k l u))) * residualWeight h k l u := by
        refine setIntegral_mono_on hint₁ hint₂ (measurableSet_unitBox d) fun u hu => ?_
        have hu' : u ∈ closedCube d := unitBox_subset_closedCube d hu
        exact mul_le_mul_of_nonneg_right (hmin₀ hu') (residualWeight_nonneg h k l u hu)

/-- **Per-stratum posterior expectation, coefficient form**: the quotient of the phase-dressed
integrals with amplitudes `φ·c` and `c` converges to the quotient of the leading coefficients. -/
theorem phase_posterior_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ξ φ c : (Fin (d + 1) → ℝ) → ℝ) (hξ : Continuous ξ) (hφ : Continuous φ) (hc : Continuous c)
    (hcpos : ∀ x ∈ closedCube (d + 1), 0 < c x) :
    Tendsto (fun N : ℝ => (∫ x in unitBox (d + 1),
        (φ x * c x) * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i))) /
        ∫ x in unitBox (d + 1), c x * ((∏ i, x i ^ h i) * quadKernel β (ξ x) (N * ∏ i, x i ^ k i)))
      atTop (𝓝 (phaseCoeff h k l β ξ (fun x => φ x * c x) / phaseCoeff h k l β ξ c)) := by
  have hnum := phase_leading_tendsto d h k hk l β hl hβ hmin hatt ξ (fun x => φ x * c x) hξ
    (hφ.mul hc)
  have hden := phase_leading_tendsto d h k hk l β hl hβ hmin hatt ξ c hξ hc
  have hpos := phaseCoeff_pos (d + 1) h k hk l β hl hβ hmin ξ c hξ hc hcpos
  refine (hnum.div hden hpos.ne').congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hscale : N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    (mul_pos (Real.rpow_pos_of_pos hN0 _) (pow_pos (Real.log_pos hN) _)).ne'
  exact div_div_div_cancel_right₀ hscale _ _

/-- **Headline XIV (per-stratum posterior expectation, general dimension)**: with the paper's
kernel,
`∫ φ c u^h e^{…} / ∫ c u^h e^{…} → ∫ φ(πu) c(πu) J_p(ξ(πu)) w / ∫ c(πu) J_p(ξ(πu)) w`,
`w = ∏_{i∉J} uᵢ^{hᵢ-pkᵢ}`. -/
theorem headline_phase_posterior (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) (ξ φ c : (Fin (m + 1) → ℝ) → ℝ)
    (hξ : Continuous ξ) (hφ : Continuous φ) (hc : Continuous c)
    (hcpos : ∀ x ∈ closedCube (m + 1), 0 < c x) :
    Tendsto (fun N : ℝ => (∫ u in unitBox (m + 1), (φ u * c u) * ((∏ i, u i ^ h i) *
        Real.exp (-(β * N ^ 2 * ∏ i, u i ^ (2 * k i)) + β * (N * ∏ i, u i ^ k i) * ξ u))) /
        ∫ u in unitBox (m + 1), c u * ((∏ i, u i ^ h i) *
          Real.exp (-(β * N ^ 2 * ∏ i, u i ^ (2 * k i)) + β * (N * ∏ i, u i ^ k i) * ξ u)))
      atTop
      (𝓝 ((∫ u in unitBox (m + 1), (φ (faceProj h k l u) * c (faceProj h k l u) *
            phaseMoment β (2 * l) (ξ (faceProj h k l u))) * residualWeight h k l u) /
          ∫ u in unitBox (m + 1), (c (faceProj h k l u) *
            phaseMoment β (2 * l) (ξ (faceProj h k l u))) * residualWeight h k l u)) := by
  have hT := phase_posterior_tendsto m h k hk l β hl hβ hmin hatt ξ φ c hξ hφ hc hcpos
  have hD : (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l ≠ 0 :=
    (mul_pos (by positivity) (faceNorm_pos h k hk l)).ne'
  have hlim : phaseCoeff h k l β ξ (fun x => φ x * c x) / phaseCoeff h k l β ξ c =
      (∫ u in unitBox (m + 1), (φ (faceProj h k l u) * c (faceProj h k l u) *
          phaseMoment β (2 * l) (ξ (faceProj h k l u))) * residualWeight h k l u) /
        ∫ u in unitBox (m + 1), (c (faceProj h k l u) *
          phaseMoment β (2 * l) (ξ (faceProj h k l u))) * residualWeight h k l u := by
    unfold phaseCoeff
    rw [mul_div_mul_left _ _ hD]
  rw [hlim] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  congr 1
  · refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    rw [paperKernel_eq_quadKernel]
  · refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    rw [paperKernel_eq_quadKernel]

/-- **Equal ratios**: the phase-dressed coefficient is the corner value
`η(0) J_p(ξ(0)) / (d! ∏ᵢ kᵢ)` (here `d + 1` coordinates, `d = m`). -/
theorem phaseCoeff_equal (m : ℕ) (h k : Fin (m + 1) → ℕ) (l β : ℝ)
    (hratio : ∀ i, ratioExp h k i = l) (ξ η : (Fin (m + 1) → ℝ) → ℝ) :
    phaseCoeff h k l β ξ η =
      η 0 * phaseMoment β (2 * l) (ξ 0) / ((m.factorial : ℝ) * ∏ i, (k i : ℝ)) := by
  have hm : multCount (ratioExp h k) l = m + 1 := by
    unfold multCount
    simp [hratio]
  have hπ : faceProj h k l = fun _ => 0 := by
    funext u i
    simp [faceProj, hratio]
  have hw : residualWeight h k l = fun _ => 1 := by
    funext u
    unfold residualWeight
    simp [hratio]
  have hprod : (∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) = ∏ i, (k i : ℝ) :=
    Finset.prod_congr rfl fun i _ => by rw [if_pos (hratio i)]
  rw [phaseCoeff, two_pow_mul_faceNorm h k l (multCount_pos_of_att h k l ⟨0, hratio 0⟩), hm,
    Nat.add_sub_cancel, hπ, hw, hprod]
  simp only [mul_one]
  rw [setIntegral_const, measureReal_def, volume_unitBox, ENNReal.toReal_one, one_smul]
  ring

/-- **Headline XIV, equal ratios**: the posterior expectation converges to the corner value
`φ(0)`. -/
theorem headline_phase_posterior_equal (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l)
    (ξ φ c : (Fin (m + 1) → ℝ) → ℝ) (hξ : Continuous ξ) (hφ : Continuous φ) (hc : Continuous c)
    (hcpos : ∀ x ∈ closedCube (m + 1), 0 < c x) :
    Tendsto (fun N : ℝ => (∫ u in unitBox (m + 1), (φ u * c u) * ((∏ i, u i ^ h i) *
        Real.exp (-(β * N ^ 2 * ∏ i, u i ^ (2 * k i)) + β * (N * ∏ i, u i ^ k i) * ξ u))) /
        ∫ u in unitBox (m + 1), c u * ((∏ i, u i ^ h i) *
          Real.exp (-(β * N ^ 2 * ∏ i, u i ^ (2 * k i)) + β * (N * ∏ i, u i ^ k i) * ξ u)))
      atTop (𝓝 (φ 0)) := by
  have hT := phase_posterior_tendsto m h k hk l β hl hβ (fun i => (hratio i).symm.le) ⟨0, hratio 0⟩
    ξ φ c hξ hφ hc hcpos
  rw [phaseCoeff_equal m h k l β hratio, phaseCoeff_equal m h k l β hratio] at hT
  have hc0 : c 0 ≠ 0 := (hcpos 0 fun i _ => ⟨le_rfl, zero_le_one⟩).ne'
  have hJ : phaseMoment β (2 * l) (ξ 0) ≠ 0 := (phaseMoment_pos β (2 * l) _ hβ (by positivity)).ne'
  have hK : ((m.factorial : ℝ) * ∏ i, (k i : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < ∏ i, (k i : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hk i
    positivity
  have hlim : φ 0 * c 0 * phaseMoment β (2 * l) (ξ 0) / ((m.factorial : ℝ) * ∏ i, (k i : ℝ)) /
      (c 0 * phaseMoment β (2 * l) (ξ 0) / ((m.factorial : ℝ) * ∏ i, (k i : ℝ))) = φ 0 := by
    rw [div_div_div_cancel_right₀ hK, mul_div_mul_right _ _ hJ, mul_div_cancel_right₀ _ hc0]
  rw [hlim] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  congr 1
  · refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    rw [paperKernel_eq_quadKernel]
  · refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    rw [paperKernel_eq_quadKernel]

end Laplace.Grammar
