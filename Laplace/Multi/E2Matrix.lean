/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovKSeparable
import Laplace.Multi.HessianRoute
import Laplace.Multi.OneLoopRotated

/-!
# eq:mean and eq:covK in matrix form for the rotated oscillator

The note's Hessian route states four predictions in matrix notation, with `S = (tH)⁻¹`:

* eq:mean, `⟨w⟩ − w* = −½ S (t T:S)` (at `γ = 0`), the seabed's `meanShift` (`HessianRoute`);
* eq:covK, `Cov[K, ψ] = ½ tr(HSBS) + ½ (Sb)ᵀ(T:S) − (t/2) bᵀ SHS (T:S) − (t/2) (Sb)ᵀ (T:(SHS))` for
  the probe `ψ(w) = ½ (w−w*)ᵀB(w−w*) + bᵀ(w−w*)`, here `covKFormula` (`K = L − L(w*)`, so
  `Cov[K, ψ] = Cov[L, ψ]`).

For E2's oscillator `L∘A`, `A(w) = Qᵀ(w − c)`, with the rotated tensors of `OneLoopRotated`:

* `meanShift_rot`: `meanShift = Q (−αᵢ/(2λᵢ²t))`, and `meanShift_rot_rate`: every ambient
  coordinate of the exact mean satisfies `|⟨wⱼ⟩ − cⱼ − meanShift j| ≤ K/t²` eventually (with the
  scaled residual `t(⟨wⱼ⟩ − cⱼ − meanShift j) → 0`, `meanShift_rot_tendsto`);
* `covKFormula_rot`: the four terms sum to `(∑ᵢ ((QᵀBQ)ᵢᵢ/(2λᵢ) − (Qᵀb)ᵢαᵢ/(2λᵢ²)))/t²` (the two
  negative `b`-terms and the positive one leave `−(Qᵀb)ᵢαᵢ/(2λᵢ²t²)`, as in one dimension), and
  `covKFormula_rot_tendsto`: `t²(Cov[L∘A, ψ] − covKFormula) → 0` for the ambient quadratic probe,
  via the probe identity `½(w−c)ᵀB(w−c) + bᵀ(w−c) = ½uᵀ(QᵀBQ)u + (Qᵀb)ᵀu`, `u = Qᵀ(w − c)`.

With `(tH)⁻¹` and its one-loop correction (`OneLoopRotated`) and `t⟨L∘A⟩ → d/2` (`SeparableExact`),
all four predictions are thus checked in the note's notation for the rotated separable anharmonic
family, at their asymptotic orders.
-/

open Matrix MeasureTheory Filter Topology

namespace Laplace.Multi

variable {d : ℕ}

/-- The right-hand side of eq:covK, with `S = (tH)⁻¹`. -/
noncomputable def covKFormula (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) : ℝ :=
  1 / 2 * (H * (t • H)⁻¹ * B * (t • H)⁻¹).trace
    + 1 / 2 * (((t • H)⁻¹ *ᵥ b) ⬝ᵥ contractT T (t • H)⁻¹)
    - t / 2 * (b ⬝ᵥ (((t • H)⁻¹ * H * (t • H)⁻¹) *ᵥ contractT T (t • H)⁻¹))
    - t / 2 * (((t • H)⁻¹ *ᵥ b) ⬝ᵥ contractT T ((t • H)⁻¹ * H * (t • H)⁻¹))

/-! ### Vectors under an orthogonal `Q` -/

section Vec

variable {Q : Matrix (Fin d) (Fin d) ℝ}

theorem mul_transpose_self_of (hQ : Qᵀ * Q = 1) : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ

/-- `(Q diag(s) Qᵀ) (Q v) = Q (s v)`. -/
theorem conj_mulVec_mulVec (hQ : Qᵀ * Q = 1) (s v : Fin d → ℝ) :
    (Q * diagonal s * Qᵀ) *ᵥ (Q *ᵥ v) = Q *ᵥ (fun i => s i * v i) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  exact Matrix.mulVec_diagonal s v i

/-- `(Q diag(s) Qᵀ) v = Q (s (Qᵀ v))`. -/
theorem conj_mulVec (hQ : Qᵀ * Q = 1) (s v : Fin d → ℝ) :
    (Q * diagonal s * Qᵀ) *ᵥ v = Q *ᵥ (fun i => s i * (Qᵀ *ᵥ v) i) := by
  have hv : v = Q *ᵥ (Qᵀ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, mul_transpose_self_of hQ, Matrix.one_mulVec]
  conv_lhs => rw [hv]
  exact conj_mulVec_mulVec hQ s _

/-- `(Q v) ⬝ (Q w) = v ⬝ w`. -/
theorem mulVec_dotProduct_mulVec (hQ : Qᵀ * Q = 1) (v w : Fin d → ℝ) :
    (Q *ᵥ v) ⬝ᵥ (Q *ᵥ w) = v ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hQ,
    Matrix.vecMul_one]

/-- `b ⬝ (Q v) = (Qᵀ b) ⬝ v`. -/
theorem dotProduct_mulVec_eq (Q : Matrix (Fin d) (Fin d) ℝ) (b v : Fin d → ℝ) :
    b ⬝ᵥ (Q *ᵥ v) = (Qᵀ *ᵥ b) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- `(T:S)` for the rotated tensors, as a `mulVec`: `Q (α s)`. -/
theorem contractT_rot_mulVec (hQ : Qᵀ * Q = 1) (alpha s : Fin d → ℝ) :
    contractT (rotT Q alpha) (Q * diagonal s * Qᵀ) = Q *ᵥ (fun p => alpha p * s p) := by
  funext l
  rw [contractT_rot hQ alpha s l]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- `S H S = Q diag(1/(λt²)) Qᵀ`. -/
theorem SHS_rot (hQ : Qᵀ * Q = 1) {lam : Fin d → ℝ} (hlam : ∀ i, lam i ≠ 0) {t : ℝ}
    (ht : t ≠ 0) :
    (t • (Q * diagonal lam * Qᵀ))⁻¹ * (Q * diagonal lam * Qᵀ) * (t • (Q * diagonal lam * Qᵀ))⁻¹ =
      Q * diagonal (fun i => 1 / (lam i * t ^ 2)) * Qᵀ := by
  rw [smul_conj_diagonal_inv hQ hlam ht, conj_mul_conj hQ, conj_mul_conj hQ,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  have : (fun i => 1 / (lam i * t) * lam i * (1 / (lam i * t))) =
      fun i => 1 / (lam i * t ^ 2) := by
    funext i
    have := hlam i
    field_simp
  rw [this]

/-- `tr(HSBS) = ∑ᵢ (QᵀBQ)ᵢᵢ/(λᵢt²)`. -/
theorem trace_HSBS_rot (hQ : Qᵀ * Q = 1) {lam : Fin d → ℝ} (hlam : ∀ i, lam i ≠ 0) {t : ℝ}
    (ht : t ≠ 0) (B : Matrix (Fin d) (Fin d) ℝ) :
    ((Q * diagonal lam * Qᵀ) * (t • (Q * diagonal lam * Qᵀ))⁻¹ * B *
        (t • (Q * diagonal lam * Qᵀ))⁻¹).trace =
      ∑ i, (Qᵀ * B * Q) i i * (1 / (lam i * t ^ 2)) := by
  rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, SHS_rot hQ hlam ht, Matrix.mul_assoc,
    Matrix.trace_mul_cycle]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]

end Vec

/-! ### eq:mean -/

section Mean

variable {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ}

/-- **eq:mean on the rotated tensors**: `meanShift = Q (−αᵢ/(2λᵢ²t))`. -/
theorem meanShift_rot (hQ : Qᵀ * Q = 1) (hlam : ∀ i, lam i ≠ 0) (alpha : Fin d → ℝ) {t : ℝ}
    (ht : t ≠ 0) :
    meanShift t (Q * diagonal lam * Qᵀ) (rotT Q alpha) =
      Q *ᵥ (fun i => -alpha i / (2 * lam i ^ 2 * t)) := by
  rw [meanShift, smul_conj_diagonal_inv hQ hlam ht, contractT_rot_mulVec hQ, Matrix.mulVec_smul,
    conj_mulVec_mulVec hQ, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have := hlam i
  field_simp

/-- **eq:mean at its rate**: for every ambient coordinate,
`|⟨wⱼ⟩ − cⱼ − meanShift j| ≤ K/t²` eventually. -/
theorem meanShift_rot_rate (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) - c j -
        meanShift t (Q * diagonal lam * Qᵀ) (rotT Q alpha) j| ≤ K / t ^ 2 := by
  choose K T hK hT h using fun i => mean_anharmonic_rate_div (hlam i) (hgamma i) (hdisc i)
  refine ⟨∑ i, |Q j i| * K i, 1 + ∑ i, T i,
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hK i),
    le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (hT i)),
    fun {t} ht => ?_⟩
  have hsum : 0 ≤ ∑ i, T i := Finset.sum_nonneg fun i _ => zero_le_one.trans (hT i)
  have hTi : ∀ i, T i ≤ t := fun i => by
    have := Finset.single_le_sum (f := T) (fun j _ => zero_le_one.trans (hT j)) (Finset.mem_univ i)
    linarith
  have htpos : 0 < t := by linarith
  have hlne : ∀ i, lam i ≠ 0 := fun i => (hlam i).ne'
  have htne : t ≠ 0 := htpos.ne'
  have hcoord : ∀ i, gibbsExpectation (separableAnharmonic lam alpha gamma) t (fun u => u i) =
      _root_.Laplace.gibbsExpectation (OneD.anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (fun x => x) := fun i =>
    gibbsExpectation_coord_separableAnharmonic hlam hgamma hdisc htpos i (fun x => x)
  rw [gibbsExpectation_coord_rotatedAnharmonic hQ c hlam hgamma hdisc htpos j,
    meanShift_rot hQ hlne alpha htne]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [hcoord]
  set E : Fin d → ℝ := fun i =>
    _root_.Laplace.gibbsExpectation (OneD.anharmonicPotential (lam i) (alpha i) (gamma i)) t
      (fun x => x) with hE
  have key : c j + ∑ i, Q j i * E i - c j - ∑ i, Q j i * (-alpha i / (2 * lam i ^ 2 * t)) =
      ∑ i, Q j i * (E i - (-alpha i / (2 * lam i ^ 2)) / t) := by
    rw [add_sub_cancel_left, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hlne i
    field_simp
  rw [key]
  calc |∑ i, Q j i * (E i - (-alpha i / (2 * lam i ^ 2)) / t)|
      ≤ ∑ i, |Q j i * (E i - (-alpha i / (2 * lam i ^ 2)) / t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |Q j i| * (K i / t ^ 2) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (h i (hTi i)) (abs_nonneg _)
    _ = (∑ i, |Q j i| * K i) / t ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

/-- **The scaled residual of eq:mean vanishes**: `t(⟨wⱼ⟩ − cⱼ − meanShift j) → 0`. -/
theorem meanShift_rot_tendsto (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (j : Fin d) :
    Tendsto (fun t : ℝ => t * (gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t
        (fun w => w j) - c j - meanShift t (Q * diagonal lam * Qᵀ) (rotT Q alpha) j)) atTop
      (𝓝 0) := by
  have h := (rotatedAnharmonic_ambient_mean_asymptotic hQ c hlam hgamma hdisc j).sub_const
    (∑ i, Q j i * (-alpha i / (2 * lam i ^ 2)))
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htne := ht.ne'
  have hm : (Q *ᵥ (fun i => -alpha i / (2 * lam i ^ 2 * t))) j =
      (∑ i, Q j i * (-alpha i / (2 * lam i ^ 2))) / t := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hlam i).ne'
    field_simp
  rw [meanShift_rot hQ (fun i => (hlam i).ne') alpha htne, hm]
  field_simp

end Mean

/-! ### eq:covK -/

section CovK

variable {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ}

/-- **eq:covK's four terms on the rotated tensors**:
`covKFormula = (∑ᵢ ((QᵀBQ)ᵢᵢ/(2λᵢ) − (Qᵀb)ᵢαᵢ/(2λᵢ²)))/t²`. -/
theorem covKFormula_rot (hQ : Qᵀ * Q = 1) (hlam : ∀ i, lam i ≠ 0) (alpha : Fin d → ℝ) {t : ℝ}
    (ht : t ≠ 0) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    covKFormula t (Q * diagonal lam * Qᵀ) (rotT Q alpha) B b =
      (∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) - (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2))) /
        t ^ 2 := by
  rw [covKFormula, trace_HSBS_rot hQ hlam ht B, SHS_rot hQ hlam ht,
    smul_conj_diagonal_inv hQ hlam ht, contractT_rot_mulVec hQ, contractT_rot_mulVec hQ,
    conj_mulVec hQ, conj_mulVec_mulVec hQ, mulVec_dotProduct_mulVec hQ,
    mulVec_dotProduct_mulVec hQ, dotProduct_mulVec_eq]
  simp only [dotProduct]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hlam i
  field_simp
  ring

/-- The ambient quadratic probe in the eigenframe:
`½(w−c)ᵀB(w−c) + bᵀ(w−c) = ½ uᵀ(QᵀBQ)u + (Qᵀb)ᵀu` with `u = Qᵀ(w − c)`. -/
theorem probe_affineFrame (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ)
    (b w : Fin d → ℝ) :
    1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c) =
      ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
        ∑ i, (Qᵀ *ᵥ b) i * affineFrame Q c w i := by
  have hwc : w - c = Q *ᵥ affineFrame Q c w := by
    unfold affineFrame
    rw [Matrix.mulVec_mulVec, mul_transpose_self_of hQ, Matrix.one_mulVec]
  conv_lhs => rw [hwc]
  rw [Matrix.mulVec_mulVec, dotProduct_comm (Q *ᵥ affineFrame Q c w), dotProduct_mulVec_eq,
    Matrix.mulVec_mulVec, dotProduct_mulVec_eq, dotProduct_comm]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_assoc]
  ring

/-- **eq:covK for the rotated oscillator and an ambient quadratic probe**:
`t² Cov[L∘A, ½(w−c)ᵀB(w−c) + bᵀ(w−c)] → ∑ᵢ ((QᵀBQ)ᵢᵢ/(2λᵢ) − (Qᵀb)ᵢαᵢ/(2λᵢ²))`. -/
theorem covK_matrix_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c))) atTop
      (𝓝 (∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) - (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2)))) := by
  have h := covK_rotatedAnharmonic_quadratic hQ c hlam hgamma hdisc (fun i j => (Qᵀ * B * Q) i j)
    (Qᵀ *ᵥ b)
  have hprobe : (fun w : Fin d → ℝ => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      fun w => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
        ∑ i, (Qᵀ *ᵥ b) i * affineFrame Q c w i :=
    funext (probe_affineFrame hQ c B b)
  rw [hprobe]
  exact h

/-- **The scaled residual of eq:covK vanishes**: `t²(Cov[L∘A, ψ] − covKFormula) → 0`. -/
theorem covKFormula_rot_tendsto (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * (gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) -
        covKFormula t (Q * diagonal lam * Qᵀ) (rotT Q alpha) B b)) atTop (𝓝 0) := by
  have h := (covK_matrix_rotatedAnharmonic hQ c hlam hgamma hdisc B b).sub_const
    (∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) - (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2)))
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [covKFormula_rot hQ (fun i => (hlam i).ne') alpha ht.ne' B b, mul_sub]
  congr 1
  have := ht.ne'
  field_simp

end CovK

end Laplace.Multi
