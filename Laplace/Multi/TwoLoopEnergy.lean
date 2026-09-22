/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.OneLoopRotated
import Laplace.Multi.VarianceOrder3
import Laplace.Multi.E2Matrix

/-!
# The energy (LLC) to two loops

The note states eq:llc at leading order, `⟨K⟩ = ½ tr(HS) + O(S²)` with `S = (tH)⁻¹`, and reports in
E2 that at `t = 3` the exact scaled energy is `4.76`, not `d/2 = 5`. The next term is the two-loop
vacuum energy: with `L = ½ wᵀHw + (1/6) T w³ + (1/24) Q₄ w⁴ + …`,

  `twoLoopEnergy = ½ tr(HS) + (t/12) θ + (t/8) δ − (1/8) q`,

where `θ = ∑ Tᵢⱼₖ Tₗₘₙ Sᵢₗ Sⱼₘ Sₖₙ = ∑ᵢⱼ Sᵢⱼ (TSST)ᵢⱼ` (theta), `δ = (T:S)ᵀ S (T:S)` (dumbbell) and
`q = ∑ Q₄ᵢⱼₖₗ Sᵢⱼ Sₖₗ` (figure-eight). The coefficients are the Wick symmetry factors of the
two-loop free energy `log Z = −tL* − ½ log det(tH/2π) + (t²/12)θ + (t²/8)δ − (t/8)q + …`
(`3! = 6` three-cross-edge pairings, `3·3 = 9` one-cross-edge pairings, `3` quartic pairings, out of
the `15` pairings of six legs), differentiated in `−∂ₜ`.

* `frobenius_conj_diagonal`: `∑ᵢⱼ (Q diag a Qᵀ)ᵢⱼ (Q diag b Qᵀ)ᵢⱼ = ∑ₚ aₚ bₚ`;
* `thetaDiagram_rot`, `dumbbell_rot`, `figureEight_rot`: on the rotated tensors
  `θ = δ = ∑ αᵢ² sᵢ³` and `q = ∑ γᵢ sᵢ²` (`s = 1/(λt)`);
* `thetaDiagram_test`, `dumbbell_test`: a tensor outside the separable family
  (`T₀₀₁ = T₀₁₀ = T₁₀₀ = 1` in two dimensions, `S = s·1`) with `θ = 3s³ ≠ δ = s³`, so the two
  coefficients are genuinely distinct in `twoLoopEnergy`;
* `twoLoopEnergy_rot`: `twoLoopEnergy = d/(2t) + (∑ᵢ (5αᵢ²/(24λᵢ³) − γᵢ/(8λᵢ²)))/t²` on
  E2's tensors, and `twoLoopEnergy_rot_note`: `= d/(2t) + d(5a²/24 − 1/8)/t²` in the note's
  parametrisation;
* `separableAnharmonic_energy_order1_rate_sharp`, `twoLoopEnergy_rotatedAnharmonic_rate`,
  `twoLoopEnergy_rotatedAnharmonic_scaled_rate`: `|⟨L∘A⟩ − twoLoopEnergy| ≤ K/t³`, i.e.
  `|t⟨K⟩ − t·twoLoopEnergy| ≤ K/t²`, from the sharp scalar energy rate summed over coordinates;
* `twoLoop_E2_value`: at `d = 10`, `a = ½`, `t = 3` the two-loop scaled energy is
  `685/144 = 4.7569…`, which rounds to E2's reported `4.76` (`twoLoop_E2_rounds`).

The rate theorem is for E2's rotated-separable family; the definition is the general tensor
expression, whose evaluation on that family is exact.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

variable {d : ℕ}

/-! ### The two-loop vacuum diagrams -/

/-- The theta diagram `θ = ∑ Tᵢⱼₖ Tₗₘₙ Sᵢₗ Sⱼₘ Sₖₙ = ∑ᵢⱼ Sᵢⱼ (TSST)ᵢⱼ`. -/
noncomputable def thetaDiagram (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, S i j * bubble T S i j

/-- The dumbbell `δ = (T:S) ⬝ S (T:S)`. -/
noncomputable def dumbbell (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  contractT T S ⬝ᵥ (S *ᵥ contractT T S)

/-- The figure-eight `q = ∑ Q₄ᵢⱼₖₗ Sᵢⱼ Sₖₗ = ∑ᵢⱼ (Q₄:S)ᵢⱼ Sᵢⱼ`. -/
noncomputable def figureEight (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, contractQ Q4 S i j * S i j

/-- The energy to two loops, `½ tr(HS) + (t/12) θ + (t/8) δ − (1/8) q` with `S = (tH)⁻¹`. -/
noncomputable def twoLoopEnergy (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ) : ℝ :=
  1 / 2 * (H * (t • H)⁻¹).trace + t / 12 * thetaDiagram T (t • H)⁻¹ +
    t / 8 * dumbbell T (t • H)⁻¹ - 1 / 8 * figureEight Q4 (t • H)⁻¹

/-! ### The theta and dumbbell contractions are distinct -/

/-- `T₀₀₁ = T₀₁₀ = T₁₀₀ = 1`, all other entries zero: a symmetric cubic tensor in two dimensions. -/
def testT : Fin 2 → Fin 2 → Fin 2 → ℝ := ![![![0, 1], ![1, 0]], ![![1, 0], ![0, 0]]]

theorem thetaDiagram_test (s : ℝ) :
    thetaDiagram testT (s • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 3 * s ^ 3 := by
  simp [thetaDiagram, bubble, testT, Fin.sum_univ_two, Matrix.one_apply]
  ring

theorem dumbbell_test (s : ℝ) : dumbbell testT (s • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = s ^ 3 := by
  simp [dumbbell, contractT, testT, Fin.sum_univ_two, Matrix.one_apply, Matrix.mulVec, dotProduct]
  ring

/-! ### Evaluation on the rotated tensors -/

section Rotated

variable {Q : Matrix (Fin d) (Fin d) ℝ}

/-- **The Frobenius pairing in the eigenframe**:
`∑ᵢⱼ (Q diag a Qᵀ)ᵢⱼ (Q diag b Qᵀ)ᵢⱼ = ∑ₚ aₚ bₚ`. -/
theorem frobenius_conj_diagonal (hQ : Qᵀ * Q = 1) (a b : Fin d → ℝ) :
    ∑ i, ∑ j, (Q * diagonal a * Qᵀ) i j * (Q * diagonal b * Qᵀ) i j = ∑ p, a p * b p := by
  have hsym : (Q * diagonal a * Qᵀ)ᵀ = Q * diagonal a * Qᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have htr : ((Q * diagonal a * Qᵀ)ᵀ * (Q * diagonal b * Qᵀ)).trace =
      ∑ i, ∑ j, (Q * diagonal a * Qᵀ) i j * (Q * diagonal b * Qᵀ) i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, transpose_apply]
    exact Finset.sum_comm
  rw [← htr, hsym, conj_mul_conj hQ, diagonal_mul_diagonal, Matrix.trace_mul_cycle, hQ,
    Matrix.one_mul, trace_diagonal]

/-- `θ = ∑ₚ αₚ² sₚ³` for the rotated cubic tensor and `S = Q diag(s) Qᵀ`. -/
theorem thetaDiagram_rot (hQ : Qᵀ * Q = 1) (alpha s : Fin d → ℝ) :
    thetaDiagram (rotT Q alpha) (Q * diagonal s * Qᵀ) = ∑ p, alpha p ^ 2 * s p ^ 3 := by
  rw [thetaDiagram, bubble_rot hQ, frobenius_conj_diagonal hQ]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- `δ = ∑ₚ αₚ² sₚ³` for the rotated cubic tensor and `S = Q diag(s) Qᵀ`. -/
theorem dumbbell_rot (hQ : Qᵀ * Q = 1) (alpha s : Fin d → ℝ) :
    dumbbell (rotT Q alpha) (Q * diagonal s * Qᵀ) = ∑ p, alpha p ^ 2 * s p ^ 3 := by
  rw [dumbbell, contractT_rot_mulVec hQ, conj_mulVec_mulVec hQ, mulVec_dotProduct_mulVec hQ]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- `q = ∑ₚ γₚ sₚ²` for the rotated quartic tensor and `S = Q diag(s) Qᵀ`. -/
theorem figureEight_rot (hQ : Qᵀ * Q = 1) (gamma s : Fin d → ℝ) :
    figureEight (rotQ Q gamma) (Q * diagonal s * Qᵀ) = ∑ p, gamma p * s p ^ 2 := by
  rw [figureEight, contractQ_rot hQ, frobenius_conj_diagonal hQ]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- `tr(H (tH)⁻¹) = d/t`. -/
theorem trace_HS_rot (hQ : Qᵀ * Q = 1) {lam : Fin d → ℝ} (hlam : ∀ i, lam i ≠ 0) {t : ℝ}
    (ht : t ≠ 0) :
    ((Q * diagonal lam * Qᵀ) * (t • (Q * diagonal lam * Qᵀ))⁻¹).trace = (d : ℝ) / t := by
  rw [smul_conj_diagonal_inv hQ hlam ht, conj_mul_conj hQ, diagonal_mul_diagonal,
    Matrix.trace_mul_cycle, hQ, Matrix.one_mul, trace_diagonal]
  have h : ∀ i, lam i * (1 / (lam i * t)) = 1 / t := fun i => by
    have := hlam i
    field_simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The two-loop energy on E2's tensors**:
`twoLoopEnergy = d/(2t) + (∑ᵢ (5αᵢ²/(24λᵢ³) − γᵢ/(8λᵢ²)))/t²`. -/
theorem twoLoopEnergy_rot (hQ : Qᵀ * Q = 1) {lam : Fin d → ℝ} (hlam : ∀ i, lam i ≠ 0)
    (alpha gamma : Fin d → ℝ) {t : ℝ} (ht : t ≠ 0) :
    twoLoopEnergy t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma) =
      (d : ℝ) / (2 * t) +
        (∑ i, (5 * alpha i ^ 2 / (24 * lam i ^ 3) - gamma i / (8 * lam i ^ 2))) / t ^ 2 := by
  rw [twoLoopEnergy, trace_HS_rot hQ hlam ht, smul_conj_diagonal_inv hQ hlam ht,
    thetaDiagram_rot hQ, dumbbell_rot hQ, figureEight_rot hQ]
  have e : ∀ i, t / 12 * (alpha i ^ 2 * (1 / (lam i * t)) ^ 3) +
      t / 8 * (alpha i ^ 2 * (1 / (lam i * t)) ^ 3) - 1 / 8 * (gamma i * (1 / (lam i * t)) ^ 2) =
      (5 * alpha i ^ 2 / (24 * lam i ^ 3) - gamma i / (8 * lam i ^ 2)) / t ^ 2 := fun i => by
    have := hlam i
    field_simp
    ring
  simp only [Finset.mul_sum, Finset.sum_div]
  rw [add_assoc, ← Finset.sum_add_distrib, add_sub_assoc, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun i _ => e i]
  ring

/-- In the note's parametrisation (`γᵢ = λᵢ²`, `αᵢ² = a²λᵢ³`):
`twoLoopEnergy = d/(2t) + d(5a²/24 − 1/8)/t²`. -/
theorem twoLoopEnergy_rot_note (hQ : Qᵀ * Q = 1) {lam alpha gamma : Fin d → ℝ} {a : ℝ}
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, gamma i = lam i ^ 2)
    (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3) {t : ℝ} (ht : t ≠ 0) :
    twoLoopEnergy t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma) =
      (d : ℝ) / (2 * t) + (d : ℝ) * (5 * a ^ 2 / 24 - 1 / 8) / t ^ 2 := by
  rw [twoLoopEnergy_rot hQ (fun i => (hlam i).ne') alpha gamma ht]
  have h : ∀ i, 5 * alpha i ^ 2 / (24 * lam i ^ 3) - gamma i / (8 * lam i ^ 2) =
      5 * a ^ 2 / 24 - 1 / 8 := fun i => by
    have := (hlam i).ne'
    rw [halpha i, hgamma i]
    field_simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- E2's numbers: `d = 10`, `a = ½`, `t = 3` give the scaled two-loop energy `685/144`. -/
theorem twoLoop_E2_value :
    (3 : ℝ) * ((10 : ℝ) / (2 * 3) + (10 : ℝ) * (5 * (1 / 2 : ℝ) ^ 2 / 24 - 1 / 8) / 3 ^ 2) =
      685 / 144 := by
  norm_num

/-- `685/144 = 4.7569…` rounds to the note's `4.76`. -/
theorem twoLoop_E2_rounds : |(685 : ℝ) / 144 - 4.76| < 0.005 := by
  rw [abs_sub_lt_iff]
  constructor <;> norm_num

end Rotated

/-! ### The remainder -/

section Rate

variable {ι : Type*} [Fintype ι] {lam alpha gamma : ι → ℝ}

/-- **The separable energy at first order with the sharp rate, general parameters**:
`|t⟨L⟩ − d/2 − (∑ᵢ cᵢ)/t| ≤ K/t²` with `cᵢ = 5αᵢ²/(24λᵢ³) − γᵢ/(8λᵢ²)`. -/
theorem separableAnharmonic_energy_order1_rate_sharp (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (separableAnharmonic lam alpha gamma) t
          (separableAnharmonic lam alpha gamma) - (Fintype.card ι : ℝ) / 2 -
        (∑ i, (5 * alpha i ^ 2 / (24 * lam i ^ 3) - gamma i / (8 * lam i ^ 2))) / t| ≤
        K / t ^ 2 := by
  choose K T hK hT h using fun i =>
    energy_anharmonic_order1_rate_sharp (hlam i) (hgamma i) (hdisc i)
  refine ⟨∑ i, K i, 1 + ∑ i, T i, Finset.sum_nonneg fun i _ => hK i,
    le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (zero_le_one.trans (hT i))),
    fun {t} ht => ?_⟩
  have hsum : 0 ≤ ∑ i, T i := Finset.sum_nonneg fun i _ => zero_le_one.trans (hT i)
  have hTi : ∀ i, T i ≤ t := fun i => by
    have := Finset.single_le_sum (f := T) (fun j _ => zero_le_one.trans (hT j)) (Finset.mem_univ i)
    linarith
  have htpos : 0 < t := by linarith
  rw [gibbsExpectation_energy_separableAnharmonic hlam hgamma hdisc htpos, Finset.mul_sum]
  have hsplit : ∑ i, t * _root_.Laplace.gibbsExpectation
        (anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) - (Fintype.card ι : ℝ) / 2 -
      (∑ i, (5 * alpha i ^ 2 / (24 * lam i ^ 3) - gamma i / (8 * lam i ^ 2))) / t =
      ∑ i, (t * _root_.Laplace.gibbsExpectation (anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 -
        (5 * alpha i ^ 2 / (24 * lam i ^ 3) - gamma i / (8 * lam i ^ 2)) / t) := by
    conv_rhs => rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]
    ring
  rw [hsplit]
  calc |∑ i, (t * _root_.Laplace.gibbsExpectation
          (anharmonicPotential (lam i) (alpha i) (gamma i)) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 -
          (5 * alpha i ^ 2 / (24 * lam i ^ 3) - gamma i / (8 * lam i ^ 2)) / t)|
      ≤ ∑ i, |t * _root_.Laplace.gibbsExpectation
          (anharmonicPotential (lam i) (alpha i) (gamma i)) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 -
          (5 * alpha i ^ 2 / (24 * lam i ^ 3) - gamma i / (8 * lam i ^ 2)) / t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, K i / t ^ 2 := Finset.sum_le_sum fun i _ => h i (hTi i)
    _ = (∑ i, K i) / t ^ 2 := by rw [Finset.sum_div]

end Rate

section RotatedRate

variable {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ}

/-- **The scaled energy to two loops** for E2's oscillator in the ambient frame:
`|t⟨L∘A⟩ − t·twoLoopEnergy| ≤ K/t²`. -/
theorem twoLoopEnergy_rotatedAnharmonic_scaled_rate (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t
          (rotatedAnharmonic Q c lam alpha gamma) -
        t * twoLoopEnergy t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma)| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := separableAnharmonic_energy_order1_rate_sharp hlam hgamma hdisc
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [gibbsExpectation_rotatedAnharmonic_self hQ c t,
    twoLoopEnergy_rot hQ (fun i => (hlam i).ne') alpha gamma ht0.ne']
  have hh := h ht
  rw [Fintype.card_fin] at hh
  set C := ∑ i, (5 * alpha i ^ 2 / (24 * lam i ^ 3) - gamma i / (8 * lam i ^ 2)) with hC
  clear_value C
  have e : t * ((d : ℝ) / (2 * t) + C / t ^ 2) = (d : ℝ) / 2 + C / t := by
    field_simp
  rw [e, ← sub_sub]
  exact hh

/-- **The energy to two loops** for E2's oscillator: `|⟨L∘A⟩ − twoLoopEnergy| ≤ K/t³`. -/
theorem twoLoopEnergy_rotatedAnharmonic_rate (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t
          (rotatedAnharmonic Q c lam alpha gamma) -
        twoLoopEnergy t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma)| ≤ K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ :=
    twoLoopEnergy_rotatedAnharmonic_scaled_rate hQ c hlam hgamma hdisc
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  set E := gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t
    (rotatedAnharmonic Q c lam alpha gamma) with hE
  set W := twoLoopEnergy t (Q * diagonal lam * Qᵀ) (rotT Q alpha) (rotQ Q gamma) with hW
  have key : E - W = (t * E - t * W) / t := by
    field_simp
  rw [key, abs_div, abs_of_pos ht0]
  calc |t * E - t * W| / t ≤ (K / t ^ 2) / t := div_le_div_of_nonneg_right (h ht) ht0.le
    _ = K / t ^ 3 := by ring

end RotatedRate

end Laplace.Multi
