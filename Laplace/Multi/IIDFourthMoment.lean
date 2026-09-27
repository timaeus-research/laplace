/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.EmpiricalMoments
import Laplace.Multi.SqrtDensityAffinity

/-!
# Fourth moments of the empirical response

For mutually independent, centred, bounded real variables `|Y_i| ≤ M` the partial sums
`T_n = ∑_{i<n} Y_i` satisfy `E T_n² ≤ n M²` and **`E T_n⁴ ≤ 3 n² M⁴`**
(`integral_pow_four_iidPartialSum_le`): expanding `(T_n + Y_n)⁴` and using the independence of
`T_n` and `Y_n`, the odd cross terms vanish and `E T_{n+1}⁴ = E T_n⁴ + 6 E T_n² E Y_n² + E Y_n⁴`.

For the empirical response `ξ̄_n = M̂_n − m_D` of `n` i.i.d. samples with features bounded by `B`,
in the sup norm on `J → ℝ` (`|J|` the number of features):

* `integral_norm_sq_sampleResponse_sub_le`: `E‖ξ̄_n‖² ≤ |J|² (2B)²/n`,
* `integral_norm_pow_four_sampleResponse_sub_le`: `E‖ξ̄_n‖⁴ ≤ 3 |J|⁴ (2B)⁴/n²`,
* **`integral_norm_pow_three_sampleResponse_sub_le`**: `E‖ξ̄_n‖³ ≤ √3 |J|³ (2B)³ / n^{3/2}`
  (Cauchy–Schwarz `M₃² ≤ M₂ M₄`).

The third absolute moment is what the localised sampling-bias theorem consumes; it is of order
`n^{−3/2}`, one order below the curvature term. Mutual independence (`iIndepFun`) is required for
the fourth moment; pairwise independence only supports the second moment.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Scalar

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)

/-- The partial sums `T_n = ∑_{i<n} Y_i`. -/
noncomputable def iidPartialSum (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range n, Y i ω

omit [MeasurableSpace Ω] in
theorem iidPartialSum_succ (n : ℕ) (ω : Ω) :
    iidPartialSum Y (n + 1) ω = iidPartialSum Y n ω + Y n ω := by
  unfold iidPartialSum
  rw [Finset.sum_range_succ]

omit [MeasurableSpace Ω] in
theorem iidPartialSum_zero (ω : Ω) : iidPartialSum Y 0 ω = 0 := by simp [iidPartialSum]

variable (hYm : ∀ i, Measurable (Y i)) {M : ℝ} (hM : ∀ i ω, |Y i ω| ≤ M)
include hYm hM

omit hM in
theorem measurable_iidPartialSum (n : ℕ) : Measurable (iidPartialSum Y n) :=
  Finset.measurable_sum _ fun i _ ↦ hYm i

omit [MeasurableSpace Ω] hYm in
theorem abs_iidPartialSum_le (n : ℕ) (ω : Ω) : |iidPartialSum Y n ω| ≤ n * M := by
  unfold iidPartialSum
  calc |∑ i ∈ Finset.range n, Y i ω| ≤ ∑ i ∈ Finset.range n, |Y i ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, M := Finset.sum_le_sum fun i _ ↦ hM i ω
    _ = n * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem bdd_iidPartialSum_pow (n k : ℕ) : Bdd fun ω ↦ iidPartialSum Y n ω ^ k :=
  ⟨(measurable_iidPartialSum Y hYm n).pow_const k, |(n : ℝ) * M| ^ k, fun ω ↦ by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_iidPartialSum_le Y hM n ω).trans (le_abs_self _)) k⟩

theorem bdd_iid_pow (i k : ℕ) : Bdd fun ω ↦ Y i ω ^ k :=
  ⟨(hYm i).pow_const k, |M| ^ k, fun ω ↦ by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hM i ω).trans (le_abs_self _)) k⟩

theorem integral_iid_sq_le (i : ℕ) : ∫ ω, Y i ω ^ 2 ∂P ≤ M ^ 2 := by
  calc ∫ ω, Y i ω ^ 2 ∂P ≤ ∫ _ω, M ^ 2 ∂P :=
        integral_mono (integrable_of_bdd_prob P (bdd_iid_pow Y hYm hM i 2)) (integrable_const _)
          fun ω ↦ by
            rw [← sq_abs (Y i ω)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hM i ω) 2
    _ = M ^ 2 := by rw [integral_const, probReal_univ, one_smul]

theorem integral_iid_pow_four_le (i : ℕ) : ∫ ω, Y i ω ^ 4 ∂P ≤ M ^ 4 := by
  calc ∫ ω, Y i ω ^ 4 ∂P ≤ ∫ _ω, M ^ 4 ∂P :=
        integral_mono (integrable_of_bdd_prob P (bdd_iid_pow Y hYm hM i 4)) (integrable_const _)
          fun ω ↦ by
            rw [← Even.pow_abs (by decide : Even 4) (Y i ω)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hM i ω) 4
    _ = M ^ 4 := by rw [integral_const, probReal_univ, one_smul]

variable (hind : iIndepFun Y P)
include hind

omit [IsProbabilityMeasure P] hM in
/-- The partial sum `T_n` is independent of the next summand `Y_n`. -/
theorem indepFun_iidPartialSum (n : ℕ) : IndepFun (iidPartialSum Y n) (Y n) P := by
  have h := hind.indepFun_finset (Finset.range n) {n}
    (Finset.disjoint_singleton_right.2 (by simp)) hYm
  have hψ : Measurable fun v : {i // i ∈ ({n} : Finset ℕ)} → ℝ ↦
      v ⟨n, Finset.mem_singleton_self n⟩ := measurable_pi_apply _
  have h2 := h.comp (φ := fun v : {i // i ∈ Finset.range n} → ℝ ↦ ∑ i, v i)
    (ψ := fun v : {i // i ∈ ({n} : Finset ℕ)} → ℝ ↦ v ⟨n, Finset.mem_singleton_self n⟩)
    (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i) hψ
  convert h2 using 1
  · funext ω
    simp only [Function.comp_def, iidPartialSum]
    exact (Finset.sum_coe_sort (Finset.range n) fun i ↦ Y i ω).symm
  · rfl

omit [IsProbabilityMeasure P] hM in
/-- Mixed moments of `T_n` and `Y_n` factorise. -/
theorem integral_iidPartialSum_pow_mul_pow (n k l : ℕ) :
    ∫ ω, iidPartialSum Y n ω ^ k * Y n ω ^ l ∂P =
      (∫ ω, iidPartialSum Y n ω ^ k ∂P) * ∫ ω, Y n ω ^ l ∂P := by
  have h : IndepFun (fun ω ↦ iidPartialSum Y n ω ^ k) (fun ω ↦ Y n ω ^ l) P :=
    (indepFun_iidPartialSum P Y hYm hind n).comp (measurable_id.pow_const k)
      (measurable_id.pow_const l)
  exact h.integral_fun_mul_eq_mul_integral
    ((measurable_iidPartialSum Y hYm n).pow_const k).aestronglyMeasurable
    ((hYm n).pow_const l).aestronglyMeasurable

variable (h0 : ∀ i, ∫ ω, Y i ω ∂P = 0)
include h0

omit hind in
theorem integral_iidPartialSum_eq_zero (n : ℕ) : ∫ ω, iidPartialSum Y n ω ∂P = 0 := by
  unfold iidPartialSum
  rw [integral_finsetSum _ fun i _ ↦ integrable_of_bdd_prob P
    ⟨hYm i, |M|, fun ω ↦ (hM i ω).trans (le_abs_self M)⟩]
  exact Finset.sum_eq_zero fun i _ ↦ h0 i

/-- **The second moment of the partial sums**: `E T_n² ≤ n M²`. -/
theorem integral_sq_iidPartialSum_le (n : ℕ) :
    ∫ ω, iidPartialSum Y n ω ^ 2 ∂P ≤ n * M ^ 2 := by
  induction n with
  | zero => simp [iidPartialSum_zero]
  | succ n ih =>
    have e : ∀ ω, iidPartialSum Y (n + 1) ω ^ 2 =
        iidPartialSum Y n ω ^ 2 + 2 * (iidPartialSum Y n ω ^ 1 * Y n ω ^ 1) + Y n ω ^ 2 := by
      intro ω
      rw [iidPartialSum_succ]
      ring
    simp_rw [e]
    have i1 := integrable_of_bdd_prob P (bdd_iidPartialSum_pow Y hYm hM n 2)
    have i2 : Integrable (fun ω ↦ 2 * (iidPartialSum Y n ω ^ 1 * Y n ω ^ 1)) P :=
      (integrable_of_bdd_prob P
        ((bdd_iidPartialSum_pow Y hYm hM n 1).mul (bdd_iid_pow Y hYm hM n 1))).const_mul 2
    have i3 := integrable_of_bdd_prob P (bdd_iid_pow Y hYm hM n 2)
    have i12 : Integrable
        (fun ω ↦ iidPartialSum Y n ω ^ 2 + 2 * (iidPartialSum Y n ω ^ 1 * Y n ω ^ 1)) P :=
      i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul,
      integral_iidPartialSum_pow_mul_pow P Y hYm hind n 1 1]
    have hY0 : ∫ ω, Y n ω ^ 1 ∂P = 0 := by simp only [pow_one]; exact h0 n
    have hY2 := integral_iid_sq_le P Y hYm hM n
    rw [hY0, mul_zero, mul_zero, add_zero]
    push_cast
    linarith

/-- **The fourth moment of the partial sums**: `E T_n⁴ ≤ 3 n² M⁴`. -/
theorem integral_pow_four_iidPartialSum_le (n : ℕ) :
    ∫ ω, iidPartialSum Y n ω ^ 4 ∂P ≤ 3 * n ^ 2 * M ^ 4 := by
  induction n with
  | zero => simp [iidPartialSum_zero]
  | succ n ih =>
    have e : ∀ ω, iidPartialSum Y (n + 1) ω ^ 4 =
        iidPartialSum Y n ω ^ 4 + 4 * (iidPartialSum Y n ω ^ 3 * Y n ω ^ 1) +
          6 * (iidPartialSum Y n ω ^ 2 * Y n ω ^ 2) +
          4 * (iidPartialSum Y n ω ^ 1 * Y n ω ^ 3) + Y n ω ^ 4 := by
      intro ω
      rw [iidPartialSum_succ]
      ring
    simp_rw [e]
    have i1 := integrable_of_bdd_prob P (bdd_iidPartialSum_pow Y hYm hM n 4)
    have i2 : Integrable (fun ω ↦ 4 * (iidPartialSum Y n ω ^ 3 * Y n ω ^ 1)) P :=
      (integrable_of_bdd_prob P
        ((bdd_iidPartialSum_pow Y hYm hM n 3).mul (bdd_iid_pow Y hYm hM n 1))).const_mul 4
    have i3 : Integrable (fun ω ↦ 6 * (iidPartialSum Y n ω ^ 2 * Y n ω ^ 2)) P :=
      (integrable_of_bdd_prob P
        ((bdd_iidPartialSum_pow Y hYm hM n 2).mul (bdd_iid_pow Y hYm hM n 2))).const_mul 6
    have i4 : Integrable (fun ω ↦ 4 * (iidPartialSum Y n ω ^ 1 * Y n ω ^ 3)) P :=
      (integrable_of_bdd_prob P
        ((bdd_iidPartialSum_pow Y hYm hM n 1).mul (bdd_iid_pow Y hYm hM n 3))).const_mul 4
    have i5 := integrable_of_bdd_prob P (bdd_iid_pow Y hYm hM n 4)
    have i12 : Integrable
        (fun ω ↦ iidPartialSum Y n ω ^ 4 + 4 * (iidPartialSum Y n ω ^ 3 * Y n ω ^ 1)) P :=
      i1.add i2
    have i123 : Integrable (fun ω ↦ iidPartialSum Y n ω ^ 4 +
        4 * (iidPartialSum Y n ω ^ 3 * Y n ω ^ 1) +
        6 * (iidPartialSum Y n ω ^ 2 * Y n ω ^ 2)) P := i12.add i3
    have i1234 : Integrable (fun ω ↦ iidPartialSum Y n ω ^ 4 +
        4 * (iidPartialSum Y n ω ^ 3 * Y n ω ^ 1) +
        6 * (iidPartialSum Y n ω ^ 2 * Y n ω ^ 2) +
        4 * (iidPartialSum Y n ω ^ 1 * Y n ω ^ 3)) P := i123.add i4
    rw [integral_add i1234 i5, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_iidPartialSum_pow_mul_pow P Y hYm hind n 3 1,
      integral_iidPartialSum_pow_mul_pow P Y hYm hind n 2 2,
      integral_iidPartialSum_pow_mul_pow P Y hYm hind n 1 3]
    have hY0 : ∫ ω, Y n ω ^ 1 ∂P = 0 := by simp only [pow_one]; exact h0 n
    have hT0 : ∫ ω, iidPartialSum Y n ω ^ 1 ∂P = 0 := by
      simp only [pow_one]
      exact integral_iidPartialSum_eq_zero P Y hYm hM h0 n
    have hY2 := integral_iid_sq_le P Y hYm hM n
    have hY4 := integral_iid_pow_four_le P Y hYm hM n
    have hT2 := integral_sq_iidPartialSum_le P Y hYm hM hind h0 n
    have hY2nn : 0 ≤ ∫ ω, Y n ω ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg _
    have hprod : (∫ ω, iidPartialSum Y n ω ^ 2 ∂P) * ∫ ω, Y n ω ^ 2 ∂P ≤ n * M ^ 2 * M ^ 2 :=
      mul_le_mul hT2 hY2 hY2nn (by positivity)
    rw [hY0, hT0]
    simp only [mul_zero, zero_mul, add_zero]
    push_cast
    nlinarith

end Scalar

section Vector

variable {X : Type*} {J : Type*} {Ω : Type*} [MeasurableSpace X] [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) [MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P] (D : Measure X) [IsProbabilityMeasure D] (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : iIndepFun Xs P) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ j x, |S j x| ≤ B)
include hS hXm hid hlaw hind hB0 hB

omit hS hXm hid hlaw hind hB0 hB [MeasurableSpace X] [MeasurableSpace Ω] [IsProbabilityMeasure P]
  [IsProbabilityMeasure D] [Nonempty J] in
/-- The sup norm is bounded by the sum of the coordinates. -/
theorem norm_le_sum_abs (v : J → ℝ) : ‖v‖ ≤ ∑ j, |v j| :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ ↦ abs_nonneg _)).2 fun j ↦ by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (v i)) (Finset.mem_univ j)

omit hS hXm hid hlaw hind hB0 hB [MeasurableSpace X] [MeasurableSpace Ω] [IsProbabilityMeasure P]
  [IsProbabilityMeasure D] in
/-- `‖v‖⁴ ≤ |J|³ ∑ vⱼ⁴`. -/
theorem norm_pow_four_le (v : J → ℝ) : ‖v‖ ^ 4 ≤ Fintype.card J ^ 3 * ∑ j, v j ^ 4 := by
  have h1 : ‖v‖ ^ 4 ≤ (∑ j, |v j|) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) (norm_le_sum_abs v) 4
  have h2 := pow_sum_div_card_le_sum_pow (s := Finset.univ) (fun j _ ↦ abs_nonneg (v j)) 3
  rw [Finset.card_univ, div_le_iff₀ (by positivity)] at h2
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ Even.pow_abs (by decide) _

omit hS hXm hid hlaw hind hB0 hB [MeasurableSpace X] [MeasurableSpace Ω] [IsProbabilityMeasure P]
  [IsProbabilityMeasure D] in
/-- `‖v‖² ≤ |J| ∑ vⱼ²`. -/
theorem norm_sq_le (v : J → ℝ) : ‖v‖ ^ 2 ≤ Fintype.card J * ∑ j, v j ^ 2 := by
  have h1 : ‖v‖ ^ 2 ≤ (∑ j, |v j|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_le_sum_abs v) 2
  have h2 := pow_sum_div_card_le_sum_pow (s := Finset.univ) (fun j _ ↦ abs_nonneg (v j)) 1
  rw [Finset.card_univ, pow_one, div_le_iff₀ (by positivity)] at h2
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ Even.pow_abs (by decide) _

variable {n : ℕ} (hn : 0 < n)
include hn

omit [Fintype J] [Nonempty J] hS [MeasurableSpace Ω] [IsProbabilityMeasure P] hXm hid hlaw hind hB0
  hn in
/-- The centred feature of a sample is bounded by `2B`. -/
theorem abs_comp_Xs_sub_le (j : J) (i : ℕ) (ω : Ω) :
    |S j (Xs i ω) - ∫ x, S j x ∂D| ≤ 2 * B := by
  have hM : |∫ x, S j x ∂D| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := D) (f := S j) (C := B)
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB j x)
    rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this
  calc |S j (Xs i ω) - ∫ x, S j x ∂D| ≤ |S j (Xs i ω)| + |∫ x, S j x ∂D| := abs_sub _ _
    _ ≤ B + B := add_le_add (hB j _) hM
    _ = 2 * B := by ring

omit [Fintype J] [Nonempty J] hB0 in
/-- **The fourth moment of an empirical coordinate**: `E (M̂_{n,j} − M_j)⁴ ≤ 3 (2B)⁴ / n²`. -/
theorem integral_pow_four_sampleResponse_sub_le (j : J) :
    ∫ ω, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 4 ∂P ≤ 3 * (2 * B) ^ 4 / n ^ 2 := by
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → Ω → ℝ, Y = fun i ω ↦ S j (Xs i ω) - ∫ x, S j x ∂D := ⟨_, rfl⟩
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ hY ▸ ((hS j).1.comp (hXm i)).sub measurable_const
  have hYind : iIndepFun Y P := by
    rw [hY]
    exact hind.comp (fun _ x ↦ S j x - ∫ x, S j x ∂D) fun _ ↦ (hS j).1.sub measurable_const
  have hM : ∀ i ω, |Y i ω| ≤ 2 * B := fun i ω ↦ hY ▸ abs_comp_Xs_sub_le D Xs hB j i ω
  have h0 : ∀ i, ∫ ω, Y i ω ∂P = 0 := fun i ↦ by
    rw [hY]; exact integral_comp_Xs_sub P D Xs hXm hid hlaw i (hS j)
  have e : ∀ ω, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 4 =
      iidPartialSum Y n ω ^ 4 / n ^ 4 := fun ω ↦ by
    rw [sampleResponse_sub_eq D Xs hn ω j, div_pow]
    simp only [iidPartialSum, hY]
  simp_rw [e]
  rw [integral_div]
  have h := integral_pow_four_iidPartialSum_le P Y hYm hM hYind h0 n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∫ ω, iidPartialSum Y n ω ^ 4 ∂P) * (n : ℝ) ^ 2 ≤ 3 * n ^ 2 * (2 * B) ^ 4 * n ^ 2 :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 3 * (2 * B) ^ 4 * n ^ 4 := by ring

omit [Fintype J] [Nonempty J] hB0 in
/-- **The second moment of an empirical coordinate**: `E (M̂_{n,j} − M_j)² ≤ (2B)² / n`. -/
theorem integral_sq_sampleResponse_sub_le (j : J) :
    ∫ ω, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 ∂P ≤ (2 * B) ^ 2 / n := by
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → Ω → ℝ, Y = fun i ω ↦ S j (Xs i ω) - ∫ x, S j x ∂D := ⟨_, rfl⟩
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ hY ▸ ((hS j).1.comp (hXm i)).sub measurable_const
  have hYind : iIndepFun Y P := by
    rw [hY]
    exact hind.comp (fun _ x ↦ S j x - ∫ x, S j x ∂D) fun _ ↦ (hS j).1.sub measurable_const
  have hM : ∀ i ω, |Y i ω| ≤ 2 * B := fun i ω ↦ hY ▸ abs_comp_Xs_sub_le D Xs hB j i ω
  have h0 : ∀ i, ∫ ω, Y i ω ∂P = 0 := fun i ↦ by
    rw [hY]; exact integral_comp_Xs_sub P D Xs hXm hid hlaw i (hS j)
  have e : ∀ ω, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 =
      iidPartialSum Y n ω ^ 2 / n ^ 2 := fun ω ↦ by
    rw [sampleResponse_sub_eq D Xs hn ω j, div_pow]
    simp only [iidPartialSum, hY]
  simp_rw [e]
  rw [integral_div]
  have h := integral_sq_iidPartialSum_le P Y hYm hM hYind h0 n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∫ ω, iidPartialSum Y n ω ^ 2 ∂P) * (n : ℝ) ≤ n * (2 * B) ^ 2 * n :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = (2 * B) ^ 2 * n ^ 2 := by ring

omit [Fintype J] [Nonempty J] [IsProbabilityMeasure P] [IsProbabilityMeasure D] hid hlaw hind hB0
  hB hn in
/-- The empirical displacement is measurable. -/
theorem measurable_sampleResponse_sub :
    Measurable fun ω ↦ (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) :=
  measurable_pi_iff.2 fun j ↦
    ((measurable_pi_apply j).comp (measurable_sampleResponse hS Xs hXm n)).sub measurable_const

omit [Nonempty J] hS [MeasurableSpace Ω] [IsProbabilityMeasure P] hXm hid hlaw hind hB0 in
/-- The empirical displacement is bounded by `2|J|B` in the sup norm. -/
theorem norm_sampleResponse_sub_le (ω : Ω) :
    ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ≤ Fintype.card J * (2 * B) := by
  refine (norm_le_sum_abs _).trans ?_
  calc ∑ j, |sampleResponse S Xs n ω j - ∫ x, S j x ∂D| ≤ ∑ _j : J, 2 * B :=
        Finset.sum_le_sum fun j _ ↦ by
          rw [sampleResponse_sub_eq D Xs hn ω j, abs_div, Nat.abs_cast, div_le_iff₀ (by
            exact_mod_cast hn)]
          calc |∑ i ∈ Finset.range n, (S j (Xs i ω) - ∫ x, S j x ∂D)|
              ≤ ∑ i ∈ Finset.range n, |S j (Xs i ω) - ∫ x, S j x ∂D| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i ∈ Finset.range n, 2 * B := Finset.sum_le_sum fun i _ ↦
                abs_comp_Xs_sub_le D Xs hB j i ω
            _ = 2 * B * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ = Fintype.card J * (2 * B) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [Nonempty J] [IsProbabilityMeasure P] hid hlaw hind hB0 in
theorem bdd_norm_sampleResponse_sub_pow (k : ℕ) :
    Bdd fun ω ↦ ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ k :=
  ⟨(measurable_sampleResponse_sub hS D Xs hXm).norm.pow_const k,
    (Fintype.card J * (2 * B)) ^ k, fun ω ↦ by
      rw [abs_pow, abs_of_nonneg (norm_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_sampleResponse_sub_le D Xs hB hn ω) k⟩

omit hB0 in
/-- **The fourth moment of the empirical response**: `E‖M̂_n − M‖⁴ ≤ 3 |J|⁴ (2B)⁴ / n²`. -/
theorem integral_norm_pow_four_sampleResponse_sub_le :
    ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 4 ∂P ≤
      3 * Fintype.card J ^ 4 * (2 * B) ^ 4 / n ^ 2 := by
  have hI : Integrable (fun ω ↦ (Fintype.card J : ℝ) ^ 3 *
      ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 4) P := by
    refine Integrable.const_mul (integrable_finsetSum _ fun j _ ↦ integrable_of_bdd_prob P ?_) _
    exact ⟨((measurable_pi_apply j).comp (measurable_sampleResponse hS Xs hXm n)).sub
      measurable_const |>.pow_const 4, (2 * B) ^ 4, fun ω ↦ by
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
        rw [sampleResponse_sub_eq D Xs hn ω j, abs_div, Nat.abs_cast, div_le_iff₀ (by
          exact_mod_cast hn)]
        calc |∑ i ∈ Finset.range n, (S j (Xs i ω) - ∫ x, S j x ∂D)|
            ≤ ∑ i ∈ Finset.range n, |S j (Xs i ω) - ∫ x, S j x ∂D| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i ∈ Finset.range n, 2 * B := Finset.sum_le_sum fun i _ ↦
              abs_comp_Xs_sub_le D Xs hB j i ω
          _ = 2 * B * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring⟩
  calc ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 4 ∂P
      ≤ ∫ ω, (Fintype.card J : ℝ) ^ 3 *
          ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 4 ∂P :=
        integral_mono (integrable_of_bdd_prob P
          (bdd_norm_sampleResponse_sub_pow hS D Xs hXm hB hn 4)) hI
          fun ω ↦ norm_pow_four_le _
    _ = (Fintype.card J : ℝ) ^ 3 *
          ∑ j, ∫ ω, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 4 ∂P := by
        rw [integral_const_mul, integral_finsetSum]
        intro j _
        exact integrable_of_bdd_prob P ⟨((measurable_pi_apply j).comp
          (measurable_sampleResponse hS Xs hXm n)).sub measurable_const |>.pow_const 4,
          (Fintype.card J * (2 * B)) ^ 4, fun ω ↦ by
            rw [abs_pow]
            refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
            have := norm_le_pi_norm (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) j
            rw [Real.norm_eq_abs] at this
            exact this.trans (norm_sampleResponse_sub_le D Xs hB hn ω)⟩
    _ ≤ (Fintype.card J : ℝ) ^ 3 * ∑ _j : J, 3 * (2 * B) ^ 4 / n ^ 2 := by
        gcongr with j _
        exact integral_pow_four_sampleResponse_sub_le hS P D Xs hXm hid hlaw hind hB hn j
    _ = 3 * Fintype.card J ^ 4 * (2 * B) ^ 4 / n ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

omit hB0 in
/-- **The second moment of the empirical response**: `E‖M̂_n − M‖² ≤ |J|² (2B)² / n`. -/
theorem integral_norm_sq_sampleResponse_sub_le :
    ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 2 ∂P ≤
      Fintype.card J ^ 2 * (2 * B) ^ 2 / n := by
  have hbdd : ∀ j, Bdd fun ω ↦ (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 := fun j ↦
    ⟨((measurable_pi_apply j).comp (measurable_sampleResponse hS Xs hXm n)).sub
      measurable_const |>.pow_const 2, (Fintype.card J * (2 * B)) ^ 2, fun ω ↦ by
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        have := norm_le_pi_norm (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) j
        rw [Real.norm_eq_abs] at this
        exact this.trans (norm_sampleResponse_sub_le D Xs hB hn ω)⟩
  have hI : Integrable (fun ω ↦ (Fintype.card J : ℝ) *
      ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2) P :=
    Integrable.const_mul (integrable_finsetSum _ fun j _ ↦ integrable_of_bdd_prob P (hbdd j)) _
  calc ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 2 ∂P
      ≤ ∫ ω, (Fintype.card J : ℝ) *
          ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 ∂P :=
        integral_mono (integrable_of_bdd_prob P
          (bdd_norm_sampleResponse_sub_pow hS D Xs hXm hB hn 2)) hI
          fun ω ↦ norm_sq_le _
    _ = (Fintype.card J : ℝ) *
          ∑ j, ∫ ω, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ integrable_of_bdd_prob P (hbdd j)]
    _ ≤ (Fintype.card J : ℝ) * ∑ _j : J, (2 * B) ^ 2 / n := by
        gcongr with j _
        exact integral_sq_sampleResponse_sub_le hS P D Xs hXm hid hlaw hind hB hn j
    _ = Fintype.card J ^ 2 * (2 * B) ^ 2 / n := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **The third absolute moment of the empirical response**:
`E‖M̂_n − M‖³ ≤ √3 |J|³ (2B)³ / n^{3/2}` (Cauchy–Schwarz `M₃² ≤ M₂ M₄`). -/
theorem integral_norm_pow_three_sampleResponse_sub_le :
    ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 3 ∂P ≤
      Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcs := sq_integral_mul_le P
    (bdd_norm_sampleResponse_sub_pow hS D Xs hXm hB hn 1)
    (bdd_norm_sampleResponse_sub_pow hS D Xs hXm hB hn 2)
  have e3 : ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 1 *
      ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 2 ∂P =
      ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 3 ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
  have e2 : ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 1 *
      ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 1 ∂P =
      ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 2 ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
  have e4 : ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 2 *
      ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 2 ∂P =
      ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 4 ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
  rw [e3, e2, e4] at hcs
  have h2 := integral_norm_sq_sampleResponse_sub_le hS P D Xs hXm hid hlaw hind hB hn
  have h4 := integral_norm_pow_four_sampleResponse_sub_le hS P D Xs hXm hid hlaw hind hB hn
  have h2nn : 0 ≤ ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 2 ∂P :=
    integral_nonneg fun ω ↦ by positivity
  have h4nn : 0 ≤ ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 4 ∂P :=
    integral_nonneg fun ω ↦ by positivity
  have h3nn : 0 ≤ ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 3 ∂P :=
    integral_nonneg fun ω ↦ by positivity
  have hR : 0 ≤ Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n) := by
    positivity
  have hsq : (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n)) ^ 2 =
      (Fintype.card J ^ 2 * (2 * B) ^ 2 / n) * (3 * Fintype.card J ^ 4 * (2 * B) ^ 4 / n ^ 2) := by
    rw [div_pow, mul_pow (Real.sqrt 3 * (Fintype.card J : ℝ) ^ 3) ((2 * B) ^ 3) 2,
      mul_pow (Real.sqrt 3) ((Fintype.card J : ℝ) ^ 3) 2, mul_pow (n : ℝ) (Real.sqrt n) 2,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sq_sqrt hn'.le]
    ring
  have hle : (∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 3 ∂P) ^ 2 ≤
      (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n)) ^ 2 := by
    rw [hsq]
    exact hcs.trans (mul_le_mul h2 h4 h4nn (by positivity))
  calc ∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 3 ∂P
      = Real.sqrt ((∫ ω, ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ ^ 3 ∂P) ^ 2) :=
        (Real.sqrt_sq h3nn).symm
    _ ≤ Real.sqrt ((Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n) := Real.sqrt_sq hR

end Vector

end Laplace.Multi
