/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FibreSubstitution

/-!
# The fibre kernel of a monomial truth coordinate

Step (3) of the fibre-identity plan (laplace `docs/hironaka_wall_atlas_spec.md`): on a chart box in
`m + 1` coordinates the truth reads `s = T(u) = S ∏_j u_j^{q_j}` exactly. Solving for the coordinate
`u_k` with `q_k ≥ 1`, `T(u) = c(w) u_k^{q_k}` with `w` the other coordinates and
`c(w) = S ∏_{j ≠ k} w_j^{q_j}`. For nonnegative measurable `Φ` on the box (the pulled-back integrand
times the chart density) and a nonnegative measurable test `η` of the truth,
`∫ Φ(u) η(T u) du = ∫ η(s) K(s) ds` with the **fibre kernel**
`K(s) = ∫_w [Φ(w, −V) + Φ(w, V)] V/(q_k |s|) dw` restricted to the branch where
`c(w) (±V)^{q_k} = s`,
`V = (|s|/|c(w)|)^{1/q_k}` (`lintegral_mul_comp_truthMono`). Fubini splits off the solved coordinate
(`MeasurableEquiv.piFinSuccAbove`), the one-dimensional two-branch substitution
(`lintegral_two_branch`, from Mathlib's `lintegral_image_eq_lintegral_abs_deriv_mul`) handles each
fibre `c(w) ≠ 0`, the exceptional set `c(w) = 0` is a finite union of coordinate hyperplanes, and
Tonelli swaps the order. In measure language: the push-forward of `Φ · du` under `T` has density
`K`.
-/

open Real MeasureTheory Set Filter
open scoped ENNReal

namespace Laplace.Multi

/-! ### The half-line images as sign conditions -/

theorem image_pow_Ioi_eq_setOf {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) :
    (fun v : ℝ ↦ c * v ^ q) '' Ioi 0 = {s | 0 < c * s} := by
  rw [image_pow_Ioi hc hq]
  ext s
  rcases lt_or_gt_of_ne hc with hcn | hcp
  · rw [if_neg (not_lt.mpr hcn.le)]
    change s < 0 ↔ 0 < c * s
    constructor
    · intro h; exact mul_pos_of_neg_of_neg hcn h
    · intro h; by_contra h'; push Not at h'; nlinarith
  · rw [if_pos hcp]
    change 0 < s ↔ 0 < c * s
    exact (mul_pos_iff_of_pos_left hcp).symm

theorem image_pow_Iio_eq_setOf {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) :
    (fun v : ℝ ↦ c * v ^ q) '' Iio 0 = {s | 0 < c * (-1) ^ q * s} := by
  rw [image_pow_Iio_eq, image_pow_Ioi_eq_setOf (mul_ne_zero hc (pow_ne_zero _ (by norm_num))) hq]

theorem solvedCoord_mul_neg_one_pow (c : ℝ) (q : ℕ) (s : ℝ) :
    solvedCoord (c * (-1) ^ q) q s = solvedCoord c q s := by
  simp only [solvedCoord, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]

/-- On the positive branch `c · V(s)^q = s`. -/
theorem solvedCoord_pos_spec {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) {s : ℝ}
    (hs : 0 < c * s) : c * solvedCoord c q s ^ q = s := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold solvedCoord
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg (abs_nonneg _) (abs_nonneg _)),
    one_div_mul_cancel hq', Real.rpow_one, ← abs_div]
  have hpos : 0 < s / c := by
    rcases lt_or_gt_of_ne hc with h | h
    · exact div_pos_of_neg_of_neg (by nlinarith) h
    · exact div_pos (by nlinarith) h
  rw [abs_of_pos hpos]
  field_simp

/-- On the negative branch `c · (−V(s))^q = s`. -/
theorem solvedCoord_neg_spec {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) {s : ℝ}
    (hs : 0 < c * (-1) ^ q * s) : c * (-solvedCoord c q s) ^ q = s := by
  have hc' : c * (-1) ^ q ≠ 0 := mul_ne_zero hc (pow_ne_zero _ (by norm_num))
  have := solvedCoord_pos_spec hc' hq hs
  rw [solvedCoord_mul_neg_one_pow] at this
  rw [neg_pow, ← mul_assoc]
  exact this

/-! ### The one-dimensional two-branch substitution, `lintegral` form -/

theorem measurable_solvedCoord (c : ℝ) (q : ℕ) : Measurable (solvedCoord c q) := by
  unfold solvedCoord
  exact (measurable_abs.div measurable_const).pow_const _

/-- The two-branch substitution for nonnegative measurable integrands: `∫ Ψ(v) dv` is the integral
in `s` of the negative-branch and positive-branch kernels, each carried by its sign set. -/
theorem lintegral_two_branch {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) {Ψ : ℝ → ℝ≥0∞}
    (hΨ : Measurable Ψ) :
    ∫⁻ v, Ψ v = ∫⁻ s,
      ({s | 0 < c * (-1) ^ q * s}.indicator
        (fun s ↦ Ψ (-solvedCoord c q s) * ENNReal.ofReal (solvedCoord c q s / (q * |s|))) s +
      {s | 0 < c * s}.indicator
        (fun s ↦ Ψ (solvedCoord c q s) * ENNReal.ofReal (solvedCoord c q s / (q * |s|))) s) := by
  have hV := measurable_solvedCoord c q
  have hden : Measurable fun s ↦ ENNReal.ofReal (solvedCoord c q s / (q * |s|)) :=
    ENNReal.measurable_ofReal.comp (hV.div (measurable_const.mul measurable_abs))
  have hmneg : Measurable fun s ↦
      Ψ (-solvedCoord c q s) * ENNReal.ofReal (solvedCoord c q s / (q * |s|)) :=
    (hΨ.comp hV.neg).mul hden
  have hsneg : MeasurableSet {s : ℝ | 0 < c * (-1) ^ q * s} :=
    measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  have hspos : MeasurableSet {s : ℝ | 0 < c * s} :=
    measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  -- the negative branch
  have hneg : ∫⁻ v in Iio 0, Ψ v = ∫⁻ s in (fun v : ℝ ↦ c * v ^ q) '' Iio 0,
      Ψ (-solvedCoord c q s) * ENNReal.ofReal (solvedCoord c q s / (q * |s|)) := by
    rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Iio
      (fun v _ ↦ hasDerivWithinAt_mul_pow c q (Iio 0) v) (injOn_mul_pow_Iio hc hq)]
    refine setLIntegral_congr_fun measurableSet_Iio fun v hv ↦ ?_
    have hv : v < 0 := hv
    have h1 := density_branch hc hq hv.ne
    rw [solvedCoord_mul_pow hc hq, abs_of_neg hv] at h1
    rw [solvedCoord_mul_pow hc hq, abs_of_neg hv, neg_neg, mul_left_comm,
      ← ENNReal.ofReal_mul (abs_nonneg _), h1, ENNReal.ofReal_one, mul_one]
  -- the positive branch
  have hpos : ∫⁻ v in Ioi 0, Ψ v = ∫⁻ s in (fun v : ℝ ↦ c * v ^ q) '' Ioi 0,
      Ψ (solvedCoord c q s) * ENNReal.ofReal (solvedCoord c q s / (q * |s|)) := by
    rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
      (fun v _ ↦ hasDerivWithinAt_mul_pow c q (Ioi 0) v) (injOn_mul_pow_Ioi hc hq)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun v hv ↦ ?_
    have hv : 0 < v := hv
    have h1 := density_branch hc hq hv.ne'
    rw [solvedCoord_mul_pow hc hq, abs_of_pos hv] at h1
    rw [solvedCoord_mul_pow hc hq, abs_of_pos hv, mul_left_comm,
      ← ENNReal.ofReal_mul (abs_nonneg _), h1, ENNReal.ofReal_one, mul_one]
  calc ∫⁻ v, Ψ v = ∫⁻ v in Iio 0 ∪ Ioi 0, Ψ v := by
        rw [Iio_union_Ioi, restrict_compl_singleton]
    _ = (∫⁻ v in Iio 0, Ψ v) + ∫⁻ v in Ioi 0, Ψ v :=
        lintegral_union measurableSet_Ioi (Ioi_disjoint_Iio_of_le le_rfl).symm
    _ = (∫⁻ s, {s | 0 < c * (-1) ^ q * s}.indicator
          (fun s ↦ Ψ (-solvedCoord c q s) * ENNReal.ofReal (solvedCoord c q s / (q * |s|))) s) +
        ∫⁻ s, {s | 0 < c * s}.indicator
          (fun s ↦ Ψ (solvedCoord c q s) * ENNReal.ofReal (solvedCoord c q s / (q * |s|))) s := by
        rw [hneg, hpos, image_pow_Iio_eq_setOf hc hq, image_pow_Ioi_eq_setOf hc hq,
          ← lintegral_indicator hsneg, ← lintegral_indicator hspos]
    _ = _ := (lintegral_add_left (hmneg.indicator hsneg) _).symm

/-! ### Fubini in the solved coordinate -/

variable {m : ℕ}

/-- The truth monomial `S ∏_j u_j^{q_j}`. -/
def truthMono (S : ℝ) (q : Fin (m + 1) → ℕ) (u : Fin (m + 1) → ℝ) : ℝ := S * ∏ j, u j ^ q j

/-- The coefficient of the solved coordinate: `S ∏_{j ≠ k} w_j^{q_j}`. -/
def solvedCoeff (k : Fin (m + 1)) (S : ℝ) (q : Fin (m + 1) → ℕ) (w : Fin m → ℝ) : ℝ :=
  S * ∏ j, w j ^ q (k.succAbove j)

theorem truthMono_insertNth (k : Fin (m + 1)) (S : ℝ) (q : Fin (m + 1) → ℕ) (v : ℝ)
    (w : Fin m → ℝ) : truthMono S q (k.insertNth v w) = solvedCoeff k S q w * v ^ q k := by
  unfold truthMono solvedCoeff
  rw [Fin.prod_univ_succAbove _ k, Fin.insertNth_apply_same]
  simp only [Fin.insertNth_apply_succAbove]
  ring

theorem measurable_truthMono (S : ℝ) (q : Fin (m + 1) → ℕ) : Measurable (truthMono S q) := by
  unfold truthMono
  exact measurable_const.mul
    (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)

theorem measurable_solvedCoeff (k : Fin (m + 1)) (S : ℝ) (q : Fin (m + 1) → ℕ) :
    Measurable (solvedCoeff k S q) := by
  unfold solvedCoeff
  exact measurable_const.mul
    (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)

/-- The exceptional set `c(w) = 0` is null. -/
theorem volume_solvedCoeff_eq_zero (k : Fin (m + 1)) {S : ℝ} (hS : S ≠ 0) (q : Fin (m + 1) → ℕ) :
    volume {w : Fin m → ℝ | solvedCoeff k S q w = 0} = 0 := by
  refine measure_mono_null (t := ⋃ j : Fin m, {w : Fin m → ℝ | w j = 0}) ?_
    (measure_iUnion_null fun j ↦ by rw [volume_pi]; exact Measure.pi_hyperplane _ j 0)
  intro w hw
  change solvedCoeff k S q w = 0 at hw
  unfold solvedCoeff at hw
  rcases mul_eq_zero.mp hw with h | h
  · exact absurd h hS
  · obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h
    exact mem_iUnion.mpr ⟨j, (pow_eq_zero_iff'.mp hj).1⟩

/-- The two-branch kernel of one fibre `w`: the contributions of `u_k = −V` and `u_k = V`. -/
noncomputable def branchKernel (k : Fin (m + 1)) (S : ℝ) (q : Fin (m + 1) → ℕ)
    (Φ : (Fin (m + 1) → ℝ) → ℝ≥0∞) (w : Fin m → ℝ) (s : ℝ) : ℝ≥0∞ :=
  {s | 0 < solvedCoeff k S q w * (-1) ^ q k * s}.indicator
    (fun s ↦ Φ (k.insertNth (-solvedCoord (solvedCoeff k S q w) (q k) s) w) *
      ENNReal.ofReal (solvedCoord (solvedCoeff k S q w) (q k) s / (q k * |s|))) s +
  {s | 0 < solvedCoeff k S q w * s}.indicator
    (fun s ↦ Φ (k.insertNth (solvedCoord (solvedCoeff k S q w) (q k) s) w) *
      ENNReal.ofReal (solvedCoord (solvedCoeff k S q w) (q k) s / (q k * |s|))) s

/-- The fibre kernel: the branch kernel integrated over the unsolved coordinates. -/
noncomputable def fibreKernel (k : Fin (m + 1)) (S : ℝ) (q : Fin (m + 1) → ℕ)
    (Φ : (Fin (m + 1) → ℝ) → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, branchKernel k S q Φ w s

theorem measurable_branchKernel_uncurry (k : Fin (m + 1)) (S : ℝ) (q : Fin (m + 1) → ℕ)
    {Φ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable fun p : (Fin m → ℝ) × ℝ ↦ branchKernel k S q Φ p.1 p.2 := by
  have hc : Measurable fun p : (Fin m → ℝ) × ℝ ↦ solvedCoeff k S q p.1 :=
    (measurable_solvedCoeff k S q).comp measurable_fst
  have hV : Measurable fun p : (Fin m → ℝ) × ℝ ↦ solvedCoord (solvedCoeff k S q p.1) (q k) p.2 := by
    unfold solvedCoord
    exact ((measurable_abs.comp measurable_snd).div (measurable_abs.comp hc)).pow_const _
  have hden : Measurable fun p : (Fin m → ℝ) × ℝ ↦
      ENNReal.ofReal (solvedCoord (solvedCoeff k S q p.1) (q k) p.2 / (q k * |p.2|)) :=
    ENNReal.measurable_ofReal.comp
      (hV.div (measurable_const.mul (measurable_abs.comp measurable_snd)))
  have hins : Measurable fun p : ℝ × (Fin m → ℝ) ↦
      (Fin.insertNth (α := fun _ ↦ ℝ) k p.1 p.2 : Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) k).symm.measurable
  unfold branchKernel
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  refine Measurable.add (Measurable.ite ?_ ?_ measurable_const)
    (Measurable.ite ?_ ?_ measurable_const)
  · exact measurableSet_lt measurable_const ((hc.mul measurable_const).mul measurable_snd)
  · exact (hΦ.comp (hins.comp (hV.neg.prodMk measurable_fst))).mul hden
  · exact measurableSet_lt measurable_const (hc.mul measurable_snd)
  · exact (hΦ.comp (hins.comp (hV.prodMk measurable_fst))).mul hden

/-- **Fubini in the solved coordinate.** For nonnegative measurable `Φ` and `η`,
`∫ Φ(u) η(T u) du = ∫ η(s) K(s) ds` with `K` the fibre kernel. -/
theorem lintegral_mul_comp_truthMono (k : Fin (m + 1)) {S : ℝ} (hS : S ≠ 0)
    {q : Fin (m + 1) → ℕ} (hq : 0 < q k) {Φ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ)
    {η : ℝ → ℝ≥0∞} (hη : Measurable η) :
    ∫⁻ u, Φ u * η (truthMono S q u) = ∫⁻ s, η s * fibreKernel k S q Φ s := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) k with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) k
  rw [← hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding]
  have hesymm : ∀ p : ℝ × (Fin m → ℝ), e.symm p = k.insertNth p.1 p.2 := fun p ↦ rfl
  have hG : Measurable fun p : ℝ × (Fin m → ℝ) ↦
      Φ (e.symm p) * η (truthMono S q (e.symm p)) :=
    (hΦ.comp e.symm.measurable).mul (hη.comp ((measurable_truthMono S q).comp e.symm.measurable))
  rw [Measure.volume_eq_prod, lintegral_prod_symm' _ hG]
  -- the fibre integral at a regular `w`
  have hinner : ∀ w : Fin m → ℝ, solvedCoeff k S q w ≠ 0 →
      ∫⁻ v, Φ (e.symm (v, w)) * η (truthMono S q (e.symm (v, w))) =
        ∫⁻ s, η s * branchKernel k S q Φ w s := by
    intro w hw
    have hΨm : Measurable fun v : ℝ ↦
        Φ (k.insertNth v w) * η (solvedCoeff k S q w * v ^ q k) :=
      (hΦ.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))).mul
        (hη.comp (measurable_const.mul (measurable_id.pow_const _)))
    simp only [hesymm, truthMono_insertNth]
    rw [lintegral_two_branch hw hq hΨm]
    refine lintegral_congr fun s ↦ ?_
    unfold branchKernel
    rw [mul_add]
    congr 1
    · by_cases hs : 0 < solvedCoeff k S q w * (-1) ^ q k * s
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hs, if_true,
          solvedCoord_neg_spec hw hq hs]
        ring
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hs, if_false, mul_zero]
    · by_cases hs : 0 < solvedCoeff k S q w * s
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hs, if_true,
          solvedCoord_pos_spec hw hq hs]
        ring
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hs, if_false, mul_zero]
  -- almost every `w` is regular
  have hae : ∀ᵐ w : Fin m → ℝ, solvedCoeff k S q w ≠ 0 := by
    rw [ae_iff]
    convert volume_solvedCoeff_eq_zero k hS q using 2
    ext w
    simp only [Set.mem_ofPred_eq, not_not]
  rw [lintegral_congr_ae (hae.mono fun w hw ↦ hinner w hw)]
  -- Tonelli
  have hK := measurable_branchKernel_uncurry k S q hΦ
  have hswap : Measurable (Function.uncurry fun (w : Fin m → ℝ) (s : ℝ) ↦
      η s * branchKernel k S q Φ w s) :=
    (hη.comp measurable_snd).mul hK
  rw [lintegral_lintegral_swap (f := fun w s ↦ η s * branchKernel k S q Φ w s) hswap.aemeasurable]
  refine lintegral_congr fun s ↦ ?_
  unfold fibreKernel
  have hK' : Measurable (Function.uncurry (branchKernel k S q Φ)) := hK
  exact lintegral_const_mul (η s) hK'.of_uncurry_right

end Laplace.Multi
