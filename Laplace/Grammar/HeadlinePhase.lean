/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseLeadingTerm

/-!
# Headline statements, part XIII: the phase-dressed leading term in general dimension

Paper-facing wrappers for unit 202 (programme A, deterministic core). With `s = N u^k`,
`p = 2λ`, `λ = min_i (hᵢ+1)/(2kᵢ)`, minimiser set `J`, `m = |J|`, `π` the projection setting the
`J`-coordinates to `0`, `S^{(β)}_{p/2}(a) = ∫₀^∞ s^{p-1} e^{-βs²+βas} ds` (`phaseMoment β p a`;
this is the paper's `J_p(a) = S_{p/2}(a)/2`, so the equal-ratio `d = 2` limit is the paper's
`A_p = y₀₀ J_p(x₀₀)/(k₁k₂)`):

* `headline_phase_leading`: for continuous `ξ`, `η` on `ℝ^d`,
  `∫_{(0,1]^d} η(u) u^h e^{-βN²u^{2k} + βNu^k ξ(u)} du / (N^{-p}(log N)^{m-1})
     → (1/((m-1)! ∏_{i∈J} kᵢ)) ∫_{(0,1]^d} η(πu) S^{(β)}_{p/2}(ξ(πu)) ∏_{i∉J} uᵢ^{hᵢ-pkᵢ} du`.
* `headline_phase_leading_equal` (all ratios equal, `J` everything, `m = d`): the limit is the
  corner value `η(0) S^{(β)}_{p/2}(ξ(0)) / ((d-1)! ∏ᵢ kᵢ)`.
* `phaseCoeff_zero_phase`: at `ξ = 0` the coefficient is `2^{m-1}` times the zero-phase amplitude
  coefficient of unit 186, consistent with the square-parameter transport (`n = N²`,
  `log n = 2 log N`).

Scope: deterministic fixed phase; one positive unit-box chart with boundary-type coordinates; the
local unnormalised integral (a posterior-expectation statement needs the denominator and chart
assembly); the phase and amplitude of the leading term live on the face `πu`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- `multCount` is the cardinality of the minimiser set. -/
theorem multCount_eq_card {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) :
    multCount ℓ l = (Finset.univ.filter fun i => ℓ i = l).card := by
  unfold multCount
  rw [Finset.sum_boole]
  simp

/-- `∏_{i∈J} 1/(2kᵢ) = (1/2)^m ∏_{i∈J} 1/kᵢ`. -/
theorem prod_ite_half_div {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) :
    (∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1) =
      (1 / 2 : ℝ) ^ multCount (ratioExp h k) l *
        ∏ i, if ratioExp h k i = l then 1 / (k i : ℝ) else 1 := by
  have hsplit : (∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1) =
      (∏ i, if ratioExp h k i = l then (1 / 2 : ℝ) else 1) *
        ∏ i, if ratioExp h k i = l then 1 / (k i : ℝ) else 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [one_div_mul_one_div]
    · rw [mul_one]
  have hhalf : (∏ i, if ratioExp h k i = l then (1 / 2 : ℝ) else 1) =
      (1 / 2 : ℝ) ^ multCount (ratioExp h k) l := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, multCount_eq_card]
  rw [hsplit, hhalf]

/-- The paper constant: `2^{m-1}·2·faceNorm = 1/((m-1)! ∏_{i∈J} kᵢ)` (for `m ≥ 1`). -/
theorem two_pow_mul_faceNorm {d : ℕ} (h k : Fin d → ℕ) (l : ℝ)
    (hm : 1 ≤ multCount (ratioExp h k) l) :
    (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) * 2 * faceNorm h k l =
      1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
        ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) := by
  unfold faceNorm
  rw [prod_ite_half_div]
  have h2 : (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) * 2 = 2 ^ multCount (ratioExp h k) l := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  have hinv : (∏ i, if ratioExp h k i = l then 1 / (k i : ℝ) else 1) =
      (∏ i, if ratioExp h k i = l then (k i : ℝ) else 1)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [one_div]
    · rw [inv_one]
  have h22 : (2 : ℝ) ^ multCount (ratioExp h k) l *
      (1 / 2 : ℝ) ^ multCount (ratioExp h k) l = 1 := by
    rw [← mul_pow]
    norm_num
  rw [h2, hinv]
  calc (2 : ℝ) ^ multCount (ratioExp h k) l *
        (1 / ((multCount (ratioExp h k) l - 1).factorial : ℝ) *
          ((1 / 2 : ℝ) ^ multCount (ratioExp h k) l *
            (∏ i, if ratioExp h k i = l then (k i : ℝ) else 1)⁻¹))
      = ((2 : ℝ) ^ multCount (ratioExp h k) l * (1 / 2 : ℝ) ^ multCount (ratioExp h k) l) *
        (1 / ((multCount (ratioExp h k) l - 1).factorial : ℝ) *
          (∏ i, if ratioExp h k i = l then (k i : ℝ) else 1)⁻¹) := by ring
    _ = 1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
        ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) := by
        rw [h22, one_mul, one_div, one_div, ← mul_inv]

theorem multCount_pos_of_att {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (hatt : ∃ i, ratioExp h k i = l) :
    1 ≤ multCount (ratioExp h k) l := by
  obtain ⟨i, hi⟩ := hatt
  unfold multCount
  calc 1 = (if ratioExp h k i = l then 1 else 0) := by rw [if_pos hi]
    _ ≤ ∑ j, if ratioExp h k j = l then 1 else 0 :=
        Finset.single_le_sum (f := fun j => if ratioExp h k j = l then 1 else 0)
          (fun _ _ => by split_ifs <;> omega) (Finset.mem_univ i)

/-- The paper's kernel equals the dressed quadratic kernel at `s = N u^k`. -/
theorem paperKernel_eq_quadKernel {d : ℕ} (β N : ℝ) (k : Fin d → ℕ) (ξ : (Fin d → ℝ) → ℝ)
    (u : Fin d → ℝ) :
    Real.exp (-(β * N ^ 2 * ∏ i, u i ^ (2 * k i)) + β * (N * ∏ i, u i ^ k i) * ξ u) =
      quadKernel β (ξ u) (N * ∏ i, u i ^ k i) := by
  unfold quadKernel
  congr 1
  rw [mul_assoc β (N ^ 2), ← sq_mul_prod_pow k N u]
  ring

/-- **Headline XIII (general-dimensional phase-dressed leading asymptotic)**: for continuous phase
`ξ` and amplitude `η`,
`∫ η(u) u^h e^{-βN²u^{2k} + βNu^k ξ(u)} du / (N^{-p}(log N)^{m-1})
   → (1/((m-1)! ∏_{i∈J} kᵢ)) ∫ η(πu) S^{(β)}_{p/2}(ξ(πu)) ∏_{i∉J} uᵢ^{hᵢ-pkᵢ} du`. -/
theorem headline_phase_leading (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) (ξ η : (Fin (m + 1) → ℝ) → ℝ)
    (hξ : Continuous ξ) (hη : Continuous η) :
    Tendsto (fun N : ℝ => (∫ u in unitBox (m + 1), η u * ((∏ i, u i ^ h i) *
        Real.exp (-(β * N ^ 2 * ∏ i, u i ^ (2 * k i)) + β * (N * ∏ i, u i ^ k i) * ξ u))) /
        (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
          ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
        ∫ u in unitBox (m + 1),
          (η (faceProj h k l u) * phaseMoment β (2 * l) (ξ (faceProj h k l u))) *
            residualWeight h k l u)) := by
  have hT := phase_leading_tendsto m h k hk l β hl hβ hmin hatt ξ η hξ hη
  rw [phaseCoeff, two_pow_mul_faceNorm h k l (multCount_pos_of_att h k l hatt)] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  rw [paperKernel_eq_quadKernel]

/-- **Headline XIII, equal ratios**: all `λᵢ = λ`, so the leading term concentrates at the corner:
the limit is `η(0) S^{(β)}_{p/2}(ξ(0)) / ((d-1)! ∏ᵢ kᵢ)`. -/
theorem headline_phase_leading_equal (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l)
    (ξ η : (Fin (m + 1) → ℝ) → ℝ) (hξ : Continuous ξ) (hη : Continuous η) :
    Tendsto (fun N : ℝ => (∫ u in unitBox (m + 1), η u * ((∏ i, u i ^ h i) *
        Real.exp (-(β * N ^ 2 * ∏ i, u i ^ (2 * k i)) + β * (N * ∏ i, u i ^ k i) * ξ u))) /
        (N ^ (-(2 * l)) * Real.log N ^ m)) atTop
      (𝓝 (η 0 * phaseMoment β (2 * l) (ξ 0) / ((m.factorial : ℝ) * ∏ i, (k i : ℝ)))) := by
  have hm : multCount (ratioExp h k) l = m + 1 := by
    unfold multCount
    simp [ratioExp, hratio]
  have hT := headline_phase_leading m h k hk l β hl hβ (fun i => (hratio i).symm.le) ⟨0, hratio 0⟩
    ξ η hξ hη
  rw [hm, Nat.add_sub_cancel] at hT
  have hπ : faceProj h k l = fun _ => 0 := by
    funext u i
    simp [faceProj, ratioExp, hratio]
  have hw : residualWeight h k l = fun _ => 1 := by
    funext u
    unfold residualWeight
    simp [ratioExp, hratio]
  have hprod : (∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) = ∏ i, (k i : ℝ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [if_pos (show ratioExp h k i = l from hratio i)]
  rw [hπ, hw, hprod] at hT
  simp only [mul_one] at hT
  rw [setIntegral_const, measureReal_def, volume_unitBox, ENNReal.toReal_one, one_smul] at hT
  rw [show 1 / ((m.factorial : ℝ) * ∏ i, (k i : ℝ)) * (η 0 * phaseMoment β (2 * l) (ξ 0)) =
      η 0 * phaseMoment β (2 * l) (ξ 0) / ((m.factorial : ℝ) * ∏ i, (k i : ℝ)) by ring] at hT
  exact hT

/-- **Zero-phase regression**: at `ξ = 0` the phase-dressed coefficient is `2^{m-1}` times the
zero-phase amplitude coefficient of unit 186 (the `2^{m-1}` is
`(log N²)^{m-1} = 2^{m-1}(log N)^{m-1}` of the square-parameter transport). -/
theorem phaseCoeff_zero_phase {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (η : (Fin d → ℝ) → ℝ) :
    phaseCoeff h k l β (fun _ => 0) η =
      2 ^ (multCount (ratioExp h k) l - 1) * amplitudeCoeff h k l β η := by
  have hS := phaseMoment_zero β (2 * l) hβ (by positivity)
  rw [show 2 * l / 2 = l by ring] at hS
  unfold phaseCoeff amplitudeCoeff faceLeadConst faceNorm
  conv_rhs => rw [← mul_assoc]
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  beta_reduce
  rw [hS]
  ring

end Laplace.Grammar
