/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.EmpiricalProjection
import Mathlib.Probability.Moments.SubGaussian

/-!
# Moments and tails of the empirical response

For i.i.d. samples `X_i ∼ D` with bounded features, the empirical response
`M̂_n = (1/n) Σ_{i<n} S(X_i)` has mean `M_D = E_D S` (`integral_sampleResponse`), second moments
`E[(M̂_n − M)_a (M̂_n − M)_b] = Γ_ab / n` with `Γ = Cov_D(S)` the DATA covariance
(`integral_sampleResponse_sub_mul_sub`), and sub-Gaussian tails
`P(‖M̂_n − M‖ > δ) ≤ 2|J| exp(−c n δ²)` by Hoeffding's inequality
(`measureReal_norm_sampleResponse_sub_gt_le`). These are the probabilistic inputs of the
reconstruction-bias theorem.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} {J : Type*} {Ω : Type*} [MeasurableSpace X] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hid hlaw

omit [IsProbabilityMeasure P] [IsProbabilityMeasure D] in
/-- The law of every sample is `D`. -/
theorem map_Xs_eq (i : ℕ) : P.map (Xs i) = D := by rw [(hid i).map_eq, hlaw]

include hXm

omit [IsProbabilityMeasure P] [IsProbabilityMeasure D] in
/-- The expectation of a bounded observable of a sample is its `D`-expectation. -/
theorem integral_comp_Xs (i : ℕ) {g : X → ℝ} (hg : Measurable g) :
    ∫ ω, g (Xs i ω) ∂P = ∫ x, g x ∂D := by
  rw [← map_Xs_eq P D Xs hid hlaw i, integral_map (hXm i).aemeasurable
    hg.aestronglyMeasurable]

include hS

omit hid hlaw [IsProbabilityMeasure P] [IsProbabilityMeasure D] in
/-- Measurability of the empirical response. -/
theorem measurable_sampleResponse (n : ℕ) : Measurable fun ω ↦ sampleResponse S Xs n ω := by
  refine measurable_pi_iff.2 fun j ↦ ?_
  unfold sampleResponse
  exact (Finset.measurable_sum _ fun i _ ↦ (hS j).1.comp (hXm i)).div_const _

omit [IsProbabilityMeasure D] in
/-- **The empirical response is unbiased**: `E[M̂_n] = M_D` for `n ≥ 1`. -/
theorem integral_sampleResponse {n : ℕ} (hn : 0 < n) (j : J) :
    ∫ ω, sampleResponse S Xs n ω j ∂P = ∫ x, S j x ∂D := by
  unfold sampleResponse
  have hint : ∀ i, Integrable (fun ω ↦ S j (Xs i ω)) P := fun i ↦ by
    obtain ⟨hm, B, hB⟩ := hS j
    exact (integrable_const B).mono' (hm.comp (hXm i)).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hB _)
  rw [integral_div, integral_finsetSum _ fun i _ ↦ hint i]
  simp only [integral_comp_Xs P D Xs hXm hid hlaw _ (hS j).1, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

omit hS [IsProbabilityMeasure D] hid hlaw in
/-- A bounded observable of a sample is integrable. -/
theorem integrable_comp_Xs (i : ℕ) {g : X → ℝ} (hg : Bdd g) :
    Integrable (fun ω ↦ g (Xs i ω)) P := by
  obtain ⟨hm, B, hB⟩ := hg
  exact (integrable_const B).mono' (hm.comp (hXm i)).aestronglyMeasurable
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hB _)

omit hS [MeasurableSpace Ω] [IsProbabilityMeasure D] hXm hid hlaw in
/-- The empirical deviation is the average of the centred features. -/
theorem sampleResponse_sub_eq {n : ℕ} (hn : 0 < n) (ω : Ω) (a : J) :
    sampleResponse S Xs n ω a - ∫ x, S a x ∂D =
      (∑ i ∈ Finset.range n, (S a (Xs i ω) - ∫ x, S a x ∂D)) / n := by
  unfold sampleResponse
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

omit hS in
/-- The centred samples have mean zero. -/
theorem integral_comp_Xs_sub (i : ℕ) {g : X → ℝ} (hg : Bdd g) :
    ∫ ω, (g (Xs i ω) - ∫ x, g x ∂D) ∂P = 0 := by
  have hgD : Integrable g D := by
    obtain ⟨hm, B, hB⟩ := hg
    exact (integrable_const B).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB _)
  rw [integral_sub (integrable_comp_Xs P Xs hXm i hg) (integrable_const _),
    integral_comp_Xs P D Xs hXm hid hlaw i hg.1, integral_const, probReal_univ, one_smul, sub_self]

omit hS [IsProbabilityMeasure D] hid hlaw in
/-- A product of bounded observables of two samples is integrable. -/
theorem integrable_comp_Xs_mul (i k : ℕ) {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    Integrable (fun ω ↦ f (Xs i ω) * g (Xs k ω)) P := by
  obtain ⟨hfm, B, hB⟩ := hf
  obtain ⟨hgm, B', hB'⟩ := hg
  refine (integrable_const (B * B')).mono'
    ((hfm.comp (hXm i)).mul (hgm.comp (hXm k))).aestronglyMeasurable
    (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hB _) (hB' _) (abs_nonneg _) ((abs_nonneg (f (Xs i ω))).trans (hB _))

/-- **The second moments of the empirical response are the data covariance over `n`**:
`E[(M̂_n − M)_a (M̂_n − M)_b] = Γ_ab / n` with `Γ = Cov_D(S)`. -/
theorem integral_sampleResponse_sub_mul_sub (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) (a b : J) :
    ∫ ω, (sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
        (sampleResponse S Xs n ω b - ∫ x, S b x ∂D) ∂P =
      (∫ x, (S a x - ∫ y, S a y ∂D) * (S b x - ∫ y, S b y ∂D) ∂D) / n := by
  obtain ⟨Ya, hYa⟩ : ∃ Ya : X → ℝ, Ya = fun x ↦ S a x - ∫ y, S a y ∂D := ⟨_, rfl⟩
  obtain ⟨Yb, hYb⟩ : ∃ Yb : X → ℝ, Yb = fun x ↦ S b x - ∫ y, S b y ∂D := ⟨_, rfl⟩
  have hYab : Bdd Ya := hYa ▸ (hS a).sub (Bdd.const _)
  have hYbb : Bdd Yb := hYb ▸ (hS b).sub (Bdd.const _)
  have hexp : ∀ ω, (sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
      (sampleResponse S Xs n ω b - ∫ x, S b x ∂D) =
      (∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n, Ya (Xs i ω) * Yb (Xs k ω)) / (n * n) := by
    intro ω
    rw [sampleResponse_sub_eq D Xs hn ω a, sampleResponse_sub_eq D Xs hn ω b,
      div_mul_div_comm, Finset.sum_mul_sum, hYa, hYb]
  have hint : ∀ i k, Integrable (fun ω ↦ Ya (Xs i ω) * Yb (Xs k ω)) P :=
    fun i k ↦ integrable_comp_Xs_mul P Xs hXm i k hYab hYbb
  have hcent : ∀ i, ∫ ω, Ya (Xs i ω) ∂P = 0 := fun i ↦ by
    rw [hYa]; exact integral_comp_Xs_sub P D Xs hXm hid hlaw i (hS a)
  have hcentb : ∀ i, ∫ ω, Yb (Xs i ω) ∂P = 0 := fun i ↦ by
    rw [hYb]; exact integral_comp_Xs_sub P D Xs hXm hid hlaw i (hS b)
  have hterm : ∀ i k, ∫ ω, Ya (Xs i ω) * Yb (Xs k ω) ∂P =
      if i = k then ∫ x, Ya x * Yb x ∂D else 0 := by
    intro i k
    split_ifs with hik
    · subst hik
      exact integral_comp_Xs P D Xs hXm hid hlaw i (hYab.mul hYbb).1
    · have h := ((hind i k hik).comp hYab.1 hYbb.1).integral_fun_mul_eq_mul_integral
        (hYab.1.comp (hXm i)).aestronglyMeasurable (hYbb.1.comp (hXm k)).aestronglyMeasurable
      simp only [Function.comp_apply] at h
      rw [h, hcent i, zero_mul]
  simp_rw [hexp]
  rw [integral_div, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun k _ ↦ hint i k,
    Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun k _ ↦ hint i k]
  simp_rw [hterm]
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [Finset.sum_ite_eq, if_pos hi], Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, hYa, hYb]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- **Hoeffding tail of one empirical coordinate**: for i.i.d. samples and features bounded by
`B`, `P(|M̂_{n,j} − M_j| > δ) ≤ 2 exp(−n δ² / (8 B²))`. -/
theorem measureReal_abs_sampleResponse_sub_gt_le (hind : iIndepFun Xs P) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j x, |S j x| ≤ B) {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (j : J) :
    P.real {ω | δ < |sampleResponse S Xs n ω j - ∫ x, S j x ∂D|} ≤
      2 * Real.exp (-((n : ℝ) * δ ^ 2) / (8 * B ^ 2)) := by
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → Ω → ℝ, Y = fun i ω ↦ S j (Xs i ω) - ∫ x, S j x ∂D := ⟨_, rfl⟩
  have hM : |∫ x, S j x ∂D| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := D) (f := S j) (C := B)
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB j x)
    rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ hY ▸ ((hS j).1.comp (hXm i)).sub measurable_const
  have hYind : iIndepFun Y P := by
    rw [hY]
    exact hind.comp (fun _ x ↦ S j x - ∫ x, S j x ∂D) fun _ ↦ (hS j).1.sub measurable_const
  have hYIcc : ∀ i ω, Y i ω ∈ Set.Icc (-(2 * B)) (2 * B) := by
    intro i ω
    have h1 := abs_le.mp (hB j (Xs i ω))
    have h2 := abs_le.mp hM
    simp only [hY, Set.mem_Icc]
    constructor <;> linarith
  have hY0 : ∀ i, ∫ ω, Y i ω ∂P = 0 := fun i ↦ by
    rw [hY]; exact integral_comp_Xs_sub P D Xs hXm hid hlaw i (hS j)
  have hsub : ∀ i, HasSubgaussianMGF (Y i) ((‖(2 * B) - -(2 * B)‖₊ / 2) ^ 2) P := fun i ↦
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hYm i).aemeasurable
      (Eventually.of_forall (hYIcc i)) (hY0 i)
  have hc : ((((‖(2 * B) - -(2 * B)‖₊ / 2) ^ 2 : ℝ≥0)) : ℝ) = 4 * B ^ 2 := by
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    ring
  have hε : 0 ≤ (n : ℝ) * δ := by positivity
  have hplus := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hYind (n := n)
    (fun i _ ↦ hsub i) hε
  have hminus := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (hYind.comp (fun _ ↦ Neg.neg) fun _ ↦ measurable_neg) (n := n)
    (fun i _ ↦ (hsub i).neg) hε
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : Real.exp (-((n : ℝ) * δ) ^ 2 /
      (2 * n * ((((‖(2 * B) - -(2 * B)‖₊ / 2) ^ 2 : ℝ≥0)) : ℝ))) =
      Real.exp (-((n : ℝ) * δ ^ 2) / (8 * B ^ 2)) := by
    rw [hc]
    congr 1
    by_cases hB' : B = 0
    · simp [hB']
    · field_simp
      ring
  rw [hexp] at hplus hminus
  have hsubset : {ω | δ < |sampleResponse S Xs n ω j - ∫ x, S j x ∂D|} ⊆
      {ω | (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, Y i ω} ∪
        {ω | (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, (Neg.neg ∘ Y i) ω} := by
    intro ω hω
    have hω' : δ < |sampleResponse S Xs n ω j - ∫ x, S j x ∂D| := hω
    rw [sampleResponse_sub_eq D Xs hn ω j, abs_div, abs_of_pos hn', lt_div_iff₀ hn'] at hω'
    rcases lt_abs.mp hω' with h | h
    · left
      change (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, Y i ω
      simp only [hY]
      linarith
    · right
      change (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, (Neg.neg ∘ Y i) ω
      simp only [hY, Function.comp_apply, Finset.sum_neg_distrib]
      linarith
  calc P.real {ω | δ < |sampleResponse S Xs n ω j - ∫ x, S j x ∂D|}
      ≤ P.real ({ω | (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, Y i ω} ∪
        {ω | (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, (Neg.neg ∘ Y i) ω}) := measureReal_mono hsubset
    _ ≤ P.real {ω | (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, Y i ω} +
        P.real {ω | (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, (Neg.neg ∘ Y i) ω} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-((n : ℝ) * δ ^ 2) / (8 * B ^ 2)) +
        Real.exp (-((n : ℝ) * δ ^ 2) / (8 * B ^ 2)) := add_le_add hplus hminus
    _ = 2 * Real.exp (-((n : ℝ) * δ ^ 2) / (8 * B ^ 2)) := by ring

/-- **Hoeffding tail of the empirical response** (sup norm on `J → ℝ`):
`P(‖M̂_n − M‖ > δ) ≤ 2 |J| exp(−n δ² / (8 B²))`. -/
theorem measureReal_norm_sampleResponse_sub_gt_le [Fintype J] (hind : iIndepFun Xs P) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B) {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | δ < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} ≤
      2 * Fintype.card J * Real.exp (-((n : ℝ) * δ ^ 2) / (8 * B ^ 2)) := by
  have hsubset : {ω | δ < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} ⊆
      ⋃ j, {ω | δ < |sampleResponse S Xs n ω j - ∫ x, S j x ∂D|} := by
    intro ω hω
    have hω' : δ < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖ := hω
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    refine hω'.not_ge ((pi_norm_le_iff_of_nonneg hδ.le).2 fun j ↦ ?_)
    rw [Real.norm_eq_abs]
    exact not_lt.mp (hcon j)
  calc P.real {ω | δ < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖}
      ≤ P.real (⋃ j, {ω | δ < |sampleResponse S Xs n ω j - ∫ x, S j x ∂D|}) :=
      measureReal_mono hsubset
    _ ≤ ∑ j, P.real {ω | δ < |sampleResponse S Xs n ω j - ∫ x, S j x ∂D|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : J, 2 * Real.exp (-((n : ℝ) * δ ^ 2) / (8 * B ^ 2)) :=
      Finset.sum_le_sum fun j _ ↦
        measureReal_abs_sampleResponse_sub_gt_le hS P D Xs hXm hid hlaw hind hB0 hB hn hδ j
    _ = 2 * Fintype.card J * Real.exp (-((n : ℝ) * δ ^ 2) / (8 * B ^ 2)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- **Exponential tails with a positive rate**: there is `c > 0` with
`P(‖M̂_n − M‖ > δ) ≤ 2 |J| exp(−c n δ²)` for all `n ≥ 1` and `δ > 0`. -/
theorem exists_tail_sampleResponse [Fintype J] (hind : iIndepFun Xs P) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ δ : ℝ, 0 < δ →
      P.real {ω | δ < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} ≤
        2 * Fintype.card J * Real.exp (-(c * n * δ ^ 2)) := by
  have hB' : ∀ j, ∃ M, ∀ x, |S j x| ≤ M := fun j ↦ (hS j).2
  choose Bj hBj using hB'
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ j, |Bj j| := ⟨_, rfl⟩
  have hBnn : 0 ≤ B := hBdef ▸ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hB0 : 0 ≤ B + 1 := by linarith
  have hB : ∀ j x, |S j x| ≤ B + 1 := fun j x ↦ by
    have := (hBj j x).trans ((le_abs_self _).trans (hBdef ▸ Finset.single_le_sum
      (f := fun j ↦ |Bj j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)))
    linarith
  refine ⟨1 / (8 * (B + 1) ^ 2), by have := pow_pos (by linarith : (0 : ℝ) < B + 1) 2; positivity,
    fun n hn δ hδ ↦ ?_⟩
  refine (measureReal_norm_sampleResponse_sub_gt_le hS P D Xs hXm hid hlaw hind hB0 hB hn
    hδ).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have e : 1 / (8 * (B + 1) ^ 2) * n * δ ^ 2 = (n : ℝ) * δ ^ 2 / (8 * (B + 1) ^ 2) := by ring
  rw [e, neg_div]

end Laplace.Multi
