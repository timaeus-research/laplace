/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.EmpiricalRelative
import Laplace.Multi.MonomialVisibility
import Laplace.Multi.KernelInstance

/-!
# Empirical rescaled moments and the schedule theorem with the population limit discharged

The empirical layer of `EmpiricalRelative` is transported to the forward-expansion setting:
for a population package `A : LocalLaplaceDomain L H` (region `U`, Hessian `H`) and an empirical
loss `K` within `δ` of `L` on `U`, the empirical rescaled moment
`A.empMoment K P q = ∫_{qx ∈ U} P(x) e^{-(K(qx)−K(0))/q²} / ∫_{qx ∈ U} e^{-(K(qx)−K(0))/q²}` is the
population one reweighted by `w = e^{-((K−L)(qx) − (K−L)(0))/q²} ∈ [e^{-2δ/q²}, e^{2δ/q²}]`, so the
abstract reweighting bound gives `|A.empMoment K P q − A.rescaledMoment P q| ≤ (e^{4δ/q²} − 1) ·
A.rescaledMoment |P| q` (`abs_empMoment_sub_popMoment_le`). Along a schedule `q_n → 0⁺` with
`δ_n / q_n^k → 0`, the empirical rescaled moment differences of two losses with equal jets below
degree `k` have the population limit `−Cov_γ(P, T_k L₁ − T_k L₂)` after division by `q_n^{k−2}`
(`tendsto_empMoment_difference_div_pow`): the population hypothesis of the schedule theorem is
discharged by the forward expansion.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

/-! ### Abstract reweighting -/

/-- **Reweighting a normalized integral.** If `w ∈ [e^{-a}, e^{a}]` wherever `F` or `G` is
nonzero, then the `w`-reweighted ratio `∫ F w / ∫ G w` is within `(e^{2a} − 1) ∫|F| / ∫ G` of
`∫ F / ∫ G`. -/
theorem abs_reweighted_ratio_sub_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F G w : X → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hF : Integrable F μ) (hFw : Integrable (fun x ↦ F x * w x) μ)
    (hG : Integrable G μ) (hGw : Integrable (fun x ↦ G x * w x) μ)
    (hG0 : ∀ x, 0 ≤ G x) (hGpos : 0 < ∫ x, G x ∂μ)
    (hw : ∀ x, F x ≠ 0 ∨ G x ≠ 0 → Real.exp (-a) ≤ w x ∧ w x ≤ Real.exp a) :
    |(∫ x, F x * w x ∂μ) / (∫ x, G x * w x ∂μ) - (∫ x, F x ∂μ) / (∫ x, G x ∂μ)| ≤
      (Real.exp (2 * a) - 1) * ((∫ x, |F x| ∂μ) / ∫ x, G x ∂μ) := by
  have hZK_lower : Real.exp (-a) * ∫ x, G x ∂μ ≤ ∫ x, G x * w x ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (hG.const_mul _) hGw fun x ↦ ?_
    beta_reduce
    by_cases hGx : G x = 0
    · simp [hGx]
    · have := (hw x (Or.inr hGx)).1
      have hGx0 := hG0 x
      nlinarith
  have hZK_upper : ∫ x, G x * w x ∂μ ≤ Real.exp a * ∫ x, G x ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono hGw (hG.const_mul _) fun x ↦ ?_
    beta_reduce
    by_cases hGx : G x = 0
    · simp [hGx]
    · have := (hw x (Or.inr hGx)).2
      have hGx0 := hG0 x
      nlinarith
  have hZKpos : 0 < ∫ x, G x * w x ∂μ := lt_of_lt_of_le (by positivity) hZK_lower
  set b : ℝ := (∫ x, G x * w x ∂μ) / ∫ x, G x ∂μ with hb_def
  have hb1 : Real.exp (-a) ≤ b := by
    rw [hb_def, le_div_iff₀ hGpos]
    exact hZK_lower
  have hb2 : b ≤ Real.exp a := by
    rw [hb_def, div_le_iff₀ hGpos]
    exact hZK_upper
  have hsplit : (∫ x, F x * (w x - b) ∂μ) = (∫ x, F x * w x ∂μ) - b * ∫ x, F x ∂μ := by
    rw [← integral_const_mul, ← integral_sub hFw (hF.const_mul b)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    ring
  have hdiff : (∫ x, F x * w x ∂μ) / (∫ x, G x * w x ∂μ) - (∫ x, F x ∂μ) / (∫ x, G x ∂μ) =
      (∫ x, F x * (w x - b) ∂μ) / ∫ x, G x * w x ∂μ := by
    rw [hsplit, hb_def]
    field_simp
  have hea : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
  have hpt : ∀ x, ‖F x * (w x - b)‖ ≤ (Real.exp a - Real.exp (-a)) * |F x| := by
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hFx : F x = 0
    · simp [hFx]
    · obtain ⟨h1, h2⟩ := hw x (Or.inl hFx)
      have hab : |w x - b| ≤ Real.exp a - Real.exp (-a) := by
        rw [abs_le]
        constructor <;> linarith
      calc |F x| * |w x - b| ≤ |F x| * (Real.exp a - Real.exp (-a)) :=
            mul_le_mul_of_nonneg_left hab (abs_nonneg _)
        _ = (Real.exp a - Real.exp (-a)) * |F x| := mul_comm _ _
  have hnum : |∫ x, F x * (w x - b) ∂μ| ≤ (Real.exp a - Real.exp (-a)) * ∫ x, |F x| ∂μ := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hF.abs.const_mul _) (Filter.Eventually.of_forall hpt)
  have hIA0 : 0 ≤ ∫ x, |F x| ∂μ := integral_nonneg fun x ↦ abs_nonneg _
  rw [hdiff, abs_div, abs_of_pos hZKpos]
  calc |∫ x, F x * (w x - b) ∂μ| / ∫ x, G x * w x ∂μ
      ≤ (Real.exp a - Real.exp (-a)) * (∫ x, |F x| ∂μ) / ∫ x, G x * w x ∂μ :=
        div_le_div_of_nonneg_right hnum hZKpos.le
    _ ≤ (Real.exp a - Real.exp (-a)) * (∫ x, |F x| ∂μ) / (Real.exp (-a) * ∫ x, G x ∂μ) :=
        div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hea) hIA0) (by positivity)
          hZK_lower
    _ = (Real.exp (2 * a) - 1) * ((∫ x, |F x| ∂μ) / ∫ x, G x ∂μ) := by
        have h2a : Real.exp (2 * a) = Real.exp a * Real.exp a := by
          rw [← Real.exp_add]
          ring_nf
        rw [h2a, Real.exp_neg]
        field_simp

theorem HasPolynomialGrowth.abs {d : ℕ} {f : EuclidD d → ℝ} (hf : HasPolynomialGrowth f) :
    HasPolynomialGrowth fun x ↦ |f x| := by
  obtain ⟨C, n, hC, h⟩ := hf
  exact ⟨C, n, hC, fun x ↦ by rw [abs_abs]; exact h x⟩

/-! ### Empirical rescaled moments on the population region -/

variable {d : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

namespace LocalLaplaceDomain

/-- The rescaled integrand of the empirical loss `K` on the population region. -/
noncomputable def empIntegrand (A : LocalLaplaceDomain L H) (K h : EuclidD d → ℝ) (q : ℝ)
    (x : EuclidD d) : ℝ :=
  Set.indicator {x : EuclidD d | q • x ∈ A.U}
    (fun x ↦ h x * Real.exp (-((K (q • x) - K 0) / q ^ 2))) x

/-- The population rescaled moment (the same as `HigherLaplaceDomain.rescaledMoment`). -/
noncomputable def popMoment (A : LocalLaplaceDomain L H) (h : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  (∫ x, A.integrand h q x) / ∫ x, A.integrand (fun _ ↦ 1) q x

/-- The empirical rescaled moment. -/
noncomputable def empMoment (A : LocalLaplaceDomain L H) (K h : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  (∫ x, A.empIntegrand K h q x) / ∫ x, A.empIntegrand K (fun _ ↦ 1) q x

/-- The reweighting factor `e^{-((K−L)(qx) − (K−L)(0))/q²}`. -/
noncomputable def empWeight (K L : EuclidD d → ℝ) (q : ℝ) (x : EuclidD d) : ℝ :=
  Real.exp (-(((K (q • x) - L (q • x)) - (K 0 - L 0)) / q ^ 2))

theorem empIntegrand_eq (A : LocalLaplaceDomain L H) (K h : EuclidD d → ℝ) (q : ℝ)
    (x : EuclidD d) : A.empIntegrand K h q x = A.integrand h q x * empWeight K L q x := by
  unfold empIntegrand integrand empWeight
  by_cases hx : x ∈ {x : EuclidD d | q • x ∈ A.U}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

theorem zero_mem_U (A : LocalLaplaceDomain L H) : (0 : EuclidD d) ∈ A.U :=
  A.ball_subset_U (Metric.mem_ball_self A.delta_pos)

theorem empWeight_bounds (A : LocalLaplaceDomain L H) {K : EuclidD d → ℝ} {δ : ℝ}
    (hclose : ∀ y ∈ A.U, |K y - L y| ≤ δ) {q : ℝ} (hq : 0 < q) {x : EuclidD d}
    (hx : q • x ∈ A.U) :
    Real.exp (-(2 * δ / q ^ 2)) ≤ empWeight K L q x ∧ empWeight K L q x ≤ Real.exp (2 * δ / q ^ 2) := by
  have h1 := abs_le.mp (hclose _ hx)
  have h2 := abs_le.mp (hclose _ A.zero_mem_U)
  have hq2 : 0 < q ^ 2 := by positivity
  unfold empWeight
  constructor
  · rw [Real.exp_le_exp, neg_le_neg_iff, div_le_div_iff_of_pos_right hq2]
    linarith
  · rw [Real.exp_le_exp, neg_le_iff_add_nonneg, ← sub_nonneg]
    have : 0 ≤ (2 * δ + ((K (q • x) - L (q • x)) - (K 0 - L 0))) / q ^ 2 := by
      apply div_nonneg _ hq2.le
      linarith
    rw [add_div] at this
    linarith

theorem integrand_nonneg_one (A : LocalLaplaceDomain L H) (q : ℝ) (x : EuclidD d) :
    0 ≤ A.integrand (fun _ ↦ (1 : ℝ)) q x := by
  unfold integrand
  by_cases hx : x ∈ {x : EuclidD d | q • x ∈ A.U}
  · rw [Set.indicator_of_mem hx]
    positivity
  · rw [Set.indicator_of_notMem hx]

theorem integrand_eq_zero_of_notMem (A : LocalLaplaceDomain L H) (h : EuclidD d → ℝ) (q : ℝ)
    {x : EuclidD d} (hx : x ∉ {x : EuclidD d | q • x ∈ A.U}) : A.integrand h q x = 0 := by
  unfold integrand
  rw [Set.indicator_of_notMem hx]

theorem integrable_empIntegrand (A : LocalLaplaceDomain L H) {K : EuclidD d → ℝ}
    (hKm : Measurable K) {δ : ℝ} (hclose : ∀ y ∈ A.U, |K y - L y| ≤ δ)
    {h : EuclidD d → ℝ} (h_cont : Continuous h) (h_growth : HasPolynomialGrowth h) {q : ℝ}
    (hq : 0 < q) : Integrable (A.empIntegrand K h q) := by
  have hint := A.integrable_integrand h_cont h_growth hq
  have hset : MeasurableSet {x : EuclidD d | q • x ∈ A.U} :=
    (measurable_const_smul q) A.measurableSet_U
  have hmK : Measurable fun x : EuclidD d ↦ Real.exp (-((K (q • x) - K 0) / q ^ 2)) := by
    have hm : Measurable fun x : EuclidD d ↦ K (q • x) := hKm.comp (measurable_const_smul q)
    exact Real.measurable_exp.comp (((hm.sub measurable_const).div_const _).neg)
  refine (hint.norm.const_mul (Real.exp (2 * δ / q ^ 2))).mono'
    (((h_cont.measurable.mul hmK).aestronglyMeasurable).indicator hset)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [A.empIntegrand_eq K h q x, norm_mul]
  by_cases hx : x ∈ {x : EuclidD d | q • x ∈ A.U}
  · have hw := (A.empWeight_bounds hclose hq hx).2
    have hwpos : 0 < empWeight K L q x := Real.exp_pos _
    rw [Real.norm_eq_abs (empWeight K L q x), abs_of_pos hwpos, mul_comm]
    exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
  · rw [A.integrand_eq_zero_of_notMem h q hx]
    simp

/-- **Relative stability of the rescaled moments.** -/
theorem abs_empMoment_sub_popMoment_le (A : LocalLaplaceDomain L H) {K : EuclidD d → ℝ}
    (hKm : Measurable K) {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ y ∈ A.U, |K y - L y| ≤ δ)
    {h : EuclidD d → ℝ} (h_cont : Continuous h) (h_growth : HasPolynomialGrowth h) {q : ℝ}
    (hq : 0 < q) (hZ : 0 < ∫ x, A.integrand (fun _ ↦ 1) q x) :
    |A.empMoment K h q - A.popMoment h q| ≤
      (Real.exp (2 * (2 * δ / q ^ 2)) - 1) * A.popMoment (fun x ↦ |h x|) q := by
  unfold empMoment popMoment
  have hF := A.integrable_integrand h_cont h_growth hq
  have hG := A.integrable_integrand continuous_const (hasPolynomialGrowth_const 1) hq
  have hFw : Integrable fun x ↦ A.integrand h q x * empWeight K L q x :=
    (A.integrable_empIntegrand hKm hclose h_cont h_growth hq).congr
      (Filter.Eventually.of_forall fun x ↦ A.empIntegrand_eq K h q x)
  have hGw : Integrable fun x ↦ A.integrand (fun _ ↦ 1) q x * empWeight K L q x :=
    (A.integrable_empIntegrand hKm hclose continuous_const (hasPolynomialGrowth_const 1) hq).congr
      (Filter.Eventually.of_forall fun x ↦ A.empIntegrand_eq K (fun _ ↦ 1) q x)
  have hw : ∀ x, A.integrand h q x ≠ 0 ∨ A.integrand (fun _ ↦ 1) q x ≠ 0 →
      Real.exp (-(2 * δ / q ^ 2)) ≤ empWeight K L q x ∧ empWeight K L q x ≤ Real.exp (2 * δ / q ^ 2) := by
    intro x hx
    by_cases hmem : x ∈ {x : EuclidD d | q • x ∈ A.U}
    · exact A.empWeight_bounds hclose hq hmem
    · exfalso
      rcases hx with hx | hx
      · exact hx (A.integrand_eq_zero_of_notMem h q hmem)
      · exact hx (A.integrand_eq_zero_of_notMem _ q hmem)
  have habs := abs_reweighted_ratio_sub_le (a := 2 * δ / q ^ 2) (by positivity) hF hFw hG hGw
    (A.integrand_nonneg_one q) hZ hw
  have e1 : ∫ x, A.empIntegrand K h q x = ∫ x, A.integrand h q x * empWeight K L q x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ A.empIntegrand_eq K h q x)
  have e2 : ∫ x, A.empIntegrand K (fun _ ↦ 1) q x =
      ∫ x, A.integrand (fun _ ↦ 1) q x * empWeight K L q x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ A.empIntegrand_eq K _ q x)
  have e3 : ∫ x, |A.integrand h q x| = ∫ x, A.integrand (fun x ↦ |h x|) q x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    unfold integrand
    by_cases hx : x ∈ {x : EuclidD d | q • x ∈ A.U}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, abs_mul,
        abs_of_pos (Real.exp_pos _)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, abs_zero]
  rw [e1, e2]
  rw [e3] at habs
  exact habs

/-- The rescaled absolute moment converges to the Gaussian expectation of `|h|`; in
particular it is eventually bounded. -/
theorem tendsto_popMoment (A : LocalLaplaceDomain L H) {h : EuclidD d → ℝ}
    (h_cont : Continuous h) (h_growth : HasPolynomialGrowth h) :
    Tendsto (fun q ↦ A.popMoment h q) (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ x, h x * quadKernel H x) / ∫ x, quadKernel H x)) := by
  have hnum := A.tendsto_integral_rescaled_poly h_cont h_growth
  have hden := A.tendsto_integral_rescaled_poly continuous_const (hasPolynomialGrowth_const 1)
  simp only [one_mul] at hden
  exact hnum.div hden (integral_quadKernel_pos A.hH_posDef).ne'

end LocalLaplaceDomain

theorem HigherLaplaceDomain.rescaledMoment_eq_popMoment {k : ℕ} (A : HigherLaplaceDomain k L H)
    (P : EuclidD d → ℝ) (q : ℝ) :
    A.rescaledMoment P q = A.toLocalLaplaceDomain.popMoment P q := rfl

/-! ### The schedule theorem with the population limit discharged -/

/-- **Empirical rescaled moment differences have the population limit.** Two population
packages with equal jets below degree `k`, empirical losses within `δ_n` on the regions, a
schedule `q_n → 0⁺` with `δ_n / q_n^k → 0`: the empirical rescaled difference divided by
`q_n^{k−2}` tends to `−Cov_γ(P, T_k L₁ − T_k L₂)`. -/
theorem tendsto_empMoment_difference_div_pow {k : ℕ} (hk : 2 < k) {L₁ L₂ : EuclidD d → ℝ}
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P) (hP_growth : HasPolynomialGrowth P)
    {K₁ K₂ : ℕ → EuclidD d → ℝ} (hK1m : ∀ n, Measurable (K₁ n)) (hK2m : ∀ n, Measurable (K₂ n))
    {δ q : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) (hq : ∀ n, 0 < q n) (hq0 : Tendsto q atTop (𝓝[>] (0 : ℝ)))
    (hclose1 : ∀ n, ∀ y ∈ A₁.U, |K₁ n y - L₁ y| ≤ δ n)
    (hclose2 : ∀ n, ∀ y ∈ A₂.U, |K₂ n y - L₂ y| ≤ δ n)
    (hsched : Tendsto (fun n ↦ δ n / q n ^ k) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (A₁.toLocalLaplaceDomain.empMoment (K₁ n) P (q n) -
        A₂.toLocalLaplaceDomain.empMoment (K₂ n) P (q n)) / q n ^ (k - 2)) atTop
      (𝓝 (-gaussianCovariance H P
        (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hpop := (HigherLaplaceDomain.tendsto_pairwise_normalized_moment_difference hk A₁ A₂ hlower
    hP_cont hP_growth).comp hq0
  simp only [Function.comp_def, HigherLaplaceDomain.rescaledMoment_eq_popMoment,
    Nat.add_sub_cancel] at hpop
  -- eventual positivity of the normalizers and boundedness of the absolute moments
  have hZ1 := hq0.eventually A₁.toLocalLaplaceDomain.eventually_integrand_one_pos
  have hZ2 := hq0.eventually A₂.toLocalLaplaceDomain.eventually_integrand_one_pos
  set M₁ : ℝ := (∫ x, |P x| * quadKernel H x) / ∫ x, quadKernel H x with hM₁
  have hA1 := (A₁.toLocalLaplaceDomain.tendsto_popMoment hP_cont.abs hP_growth.abs).comp hq0
  have hA2 := (A₂.toLocalLaplaceDomain.tendsto_popMoment hP_cont.abs hP_growth.abs).comp hq0
  have hA1' : ∀ᶠ n in atTop,
      A₁.toLocalLaplaceDomain.popMoment (fun x ↦ |P x|) (q n) ≤ M₁ + 1 := by
    have := hA1.eventually (Iic_mem_nhds (by linarith : M₁ < M₁ + 1))
    filter_upwards [this] with n hn
    exact Set.mem_Iic.mp hn
  have hA2' : ∀ᶠ n in atTop,
      A₂.toLocalLaplaceDomain.popMoment (fun x ↦ |P x|) (q n) ≤ M₁ + 1 := by
    have := hA2.eventually (Iic_mem_nhds (by linarith : M₁ < M₁ + 1))
    filter_upwards [this] with n hn
    exact Set.mem_Iic.mp hn
  have hM0 : 0 ≤ M₁ := div_nonneg (integral_nonneg fun x ↦ mul_nonneg (abs_nonneg _)
    (quadKernel_pos H x).le) (integral_quadKernel_pos A₁.hH_posDef).le
  -- the small parameter `a_n = 2 δ_n / q_n²` tends to zero
  have hq_nhds : Tendsto q atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hq0).1
  have ha : Tendsto (fun n ↦ 2 * δ n / q n ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ 2 * ((δ n / q n ^ (j + 2)) * q n ^ j)) atTop (𝓝 0) := by
      have := (hsched.mul (hq_nhds.pow j)).const_mul 2
      simpa using this
    refine h1.congr fun n ↦ ?_
    have hqn := (hq n).ne'
    field_simp
    ring
  have hlin : ∀ᶠ n in atTop, 2 * δ n / q n ^ 2 ≤ 1 := by
    have := ha.eventually (Iic_mem_nhds one_pos)
    filter_upwards [this] with n hn
    exact Set.mem_Iic.mp hn
  -- the perturbation tends to zero
  have hpert : Tendsto (fun n ↦
      (A₁.toLocalLaplaceDomain.empMoment (K₁ n) P (q n) -
        A₂.toLocalLaplaceDomain.empMoment (K₂ n) P (q n)) / q n ^ j -
      (A₁.toLocalLaplaceDomain.popMoment P (q n) -
        A₂.toLocalLaplaceDomain.popMoment P (q n)) / q n ^ j) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n ↦ (8 * Real.exp 2 * (M₁ + 1)) * (δ n / q n ^ (j + 2))) atTop
        (𝓝 0) := by
      simpa using hsched.const_mul (8 * Real.exp 2 * (M₁ + 1))
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hZ1, hZ2, hA1', hA2', hlin] with n hZ1n hZ2n hA1n hA2n hlinn
    have hqn := hq n
    have hδn := hδ n
    have h1 := A₁.toLocalLaplaceDomain.abs_empMoment_sub_popMoment_le (hK1m n) (hδ n)
      (hclose1 n) hP_cont hP_growth hqn hZ1n
    have h2 := A₂.toLocalLaplaceDomain.abs_empMoment_sub_popMoment_le (hK2m n) (hδ n)
      (hclose2 n) hP_cont hP_growth hqn hZ2n
    have hexp := exp_two_mul_sub_one_le (a := 2 * δ n / q n ^ 2) (by positivity) hlinn
    have hexp0 : 0 ≤ Real.exp (2 * (2 * δ n / q n ^ 2)) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (2 * (2 * δ n / q n ^ 2)) := Real.one_le_exp (by positivity)
      linarith
    have hb1 : |A₁.toLocalLaplaceDomain.empMoment (K₁ n) P (q n) -
        A₁.toLocalLaplaceDomain.popMoment P (q n)| ≤
        (Real.exp (2 * (2 * δ n / q n ^ 2)) - 1) * (M₁ + 1) :=
      h1.trans (mul_le_mul_of_nonneg_left hA1n hexp0)
    have hb2 : |A₂.toLocalLaplaceDomain.empMoment (K₂ n) P (q n) -
        A₂.toLocalLaplaceDomain.popMoment P (q n)| ≤
        (Real.exp (2 * (2 * δ n / q n ^ 2)) - 1) * (M₁ + 1) :=
      h2.trans (mul_le_mul_of_nonneg_left hA2n hexp0)
    have hqj : 0 < q n ^ j := pow_pos hqn j
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hqj, div_le_iff₀ hqj]
    calc |(A₁.toLocalLaplaceDomain.empMoment (K₁ n) P (q n) -
            A₂.toLocalLaplaceDomain.empMoment (K₂ n) P (q n)) -
          (A₁.toLocalLaplaceDomain.popMoment P (q n) -
            A₂.toLocalLaplaceDomain.popMoment P (q n))|
        = |(A₁.toLocalLaplaceDomain.empMoment (K₁ n) P (q n) -
            A₁.toLocalLaplaceDomain.popMoment P (q n)) -
          (A₂.toLocalLaplaceDomain.empMoment (K₂ n) P (q n) -
            A₂.toLocalLaplaceDomain.popMoment P (q n))| := by
          ring_nf
      _ ≤ |A₁.toLocalLaplaceDomain.empMoment (K₁ n) P (q n) -
            A₁.toLocalLaplaceDomain.popMoment P (q n)| +
          |A₂.toLocalLaplaceDomain.empMoment (K₂ n) P (q n) -
            A₂.toLocalLaplaceDomain.popMoment P (q n)| := abs_sub _ _
      _ ≤ (Real.exp (2 * (2 * δ n / q n ^ 2)) - 1) * (M₁ + 1) +
          (Real.exp (2 * (2 * δ n / q n ^ 2)) - 1) * (M₁ + 1) := add_le_add hb1 hb2
      _ ≤ (2 * Real.exp 2 * (2 * δ n / q n ^ 2)) * (M₁ + 1) +
          (2 * Real.exp 2 * (2 * δ n / q n ^ 2)) * (M₁ + 1) := by
          gcongr
      _ = (8 * Real.exp 2 * (M₁ + 1)) * (δ n / q n ^ (j + 2)) * q n ^ j := by
          have hqn' := hqn.ne'
          field_simp
          ring
  have h := hpop.add hpert
  rw [add_zero] at h
  exact h.congr fun n ↦ by ring

/-! ### Sample size: the schedule `q_n = n^{-β/2}` -/

/-- The schedule `q_n = n^{-β/2}` (temperature `t_n = n^β`) tends to `0⁺`. -/
theorem tendsto_rpow_neg_half_beta {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(β / 2))) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (tendsto_rpow_neg_atTop (by positivity : 0 < β / 2)).comp tendsto_natCast_atTop_atTop
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.rpow_pos_of_pos this _

/-- With `δ_n ≤ C n^{-1/2}` and `q_n = n^{-β/2}`, the schedule condition `δ_n / q_n^k → 0`
holds as soon as `β k < 1`. -/
theorem tendsto_delta_div_pow_of_sample_size {δ : ℕ → ℝ} {C β : ℝ} (hδ : ∀ n, 0 ≤ δ n)
    (hδn : ∀ n : ℕ, 1 ≤ n → δ n ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ))) (k : ℕ) (hβk : β * k < 1) :
    Tendsto (fun n : ℕ ↦ δ n / ((n : ℝ) ^ (-(β / 2))) ^ k) atTop (𝓝 0) := by
  have h := tendsto_delta_mul_rpow_of_sample_size (β := β) (e := (k : ℝ) / 2) hδ hδn
    (by linarith)
  refine (h.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_mul hn0.le, neg_mul,
    Real.rpow_neg hn0.le, div_inv_eq_mul]
  congr 1
  congr 1
  ring

/-! ### The two limits for the monomial design -/

/-- **Certification of a visible jet difference.** If the jets agree below degree `k > 2` and
differ at degree `k`, some monomial word of length `k` has a nonzero pairing with the
difference, and along any admissible empirical schedule the empirical rescaled difference for
that word, divided by `q_n^{k−2}`, converges to that nonzero number. -/
theorem exists_word_empirical_certification {k : ℕ} (hk : 2 < k) {L₁ L₂ : EuclidD d → ℝ}
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hdiff : (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x) ≠ 0) :
    ∃ w : Fin k → Fin d,
      -gaussianCovariance H (monomialTest w)
        (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x) ≠ 0 ∧
      ∀ {K₁ K₂ : ℕ → EuclidD d → ℝ}, (∀ n, Measurable (K₁ n)) → (∀ n, Measurable (K₂ n)) →
      ∀ {δ q : ℕ → ℝ}, (∀ n, 0 ≤ δ n) → (∀ n, 0 < q n) → Tendsto q atTop (𝓝[>] (0 : ℝ)) →
      (∀ n, ∀ y ∈ A₁.U, |K₁ n y - L₁ y| ≤ δ n) → (∀ n, ∀ y ∈ A₂.U, |K₂ n y - L₂ y| ≤ δ n) →
      Tendsto (fun n ↦ δ n / q n ^ k) atTop (𝓝 0) →
      Tendsto (fun n ↦ (A₁.toLocalLaplaceDomain.empMoment (K₁ n) (monomialTest w) (q n) -
          A₂.toLocalLaplaceDomain.empMoment (K₂ n) (monomialTest w) (q n)) / q n ^ (k - 2))
        atTop (𝓝 (-gaussianCovariance H (monomialTest w)
          (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x))) := by
  have hinj := monomialTest_family_injective A₁.hH_posDef (by omega : 0 < k)
    (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x)
    (taylorDifference_mem_homogPolySpan L₁ L₂)
  have hex : ∃ w : Fin k → Fin d, gaussianCovariance H (monomialTest w)
      (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hdiff (hinj hall)
  obtain ⟨w, hw⟩ := hex
  refine ⟨w, neg_ne_zero.mpr hw, ?_⟩
  intro K₁ K₂ hK1m hK2m δ q hδ hq hq0 hclose1 hclose2 hsched
  exact tendsto_empMoment_difference_div_pow hk A₁ A₂ hlower (monomialTest_continuous w)
    (monomialTest_hasPolynomialGrowth w) hK1m hK2m hδ hq hq0 hclose1 hclose2 hsched

/-- **Blindness beyond the design degree.** For the standard Gaussian reference in `d ≥ 2`
and `k > max m 2`, there are two certified losses with equal jets below degree `k` and
different degree-`k` tensors such that, for every monomial of degree `≤ m` and every
admissible empirical schedule, the empirical rescaled difference divided by `q_n^{k−2}` tends
to zero: no monomial of degree `≤ m` can certify the degree-`k` difference at leading order. -/
theorem exists_pair_monomial_design_empirically_blind (hd : 2 ≤ d) {m k : ℕ} (hmk : m < k)
    (hk : 2 < k) :
    ∃ (L₁ L₂ : EuclidD d → ℝ) (A₁ : HigherLaplaceDomain k L₁ (1 : Matrix (Fin d) (Fin d) ℝ))
      (A₂ : HigherLaplaceDomain k L₂ (1 : Matrix (Fin d) (Fin d) ℝ)),
      (∀ j < k, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0) ∧
      iteratedFDeriv ℝ k L₁ 0 ≠ iteratedFDeriv ℝ k L₂ 0 ∧
      ∀ (q' : ℕ) (w : Fin q' → Fin d), q' ≤ m →
      ∀ {K₁ K₂ : ℕ → EuclidD d → ℝ}, (∀ n, Measurable (K₁ n)) → (∀ n, Measurable (K₂ n)) →
      ∀ {δ q : ℕ → ℝ}, (∀ n, 0 ≤ δ n) → (∀ n, 0 < q n) → Tendsto q atTop (𝓝[>] (0 : ℝ)) →
      (∀ n, ∀ y ∈ A₁.U, |K₁ n y - L₁ y| ≤ δ n) → (∀ n, ∀ y ∈ A₂.U, |K₂ n y - L₂ y| ≤ δ n) →
      Tendsto (fun n ↦ δ n / q n ^ k) atTop (𝓝 0) →
      Tendsto (fun n ↦ (A₁.toLocalLaplaceDomain.empMoment (K₁ n) (monomialTest w) (q n) -
          A₂.toLocalLaplaceDomain.empMoment (K₂ n) (monomialTest w) (q n)) / q n ^ (k - 2))
        atTop (𝓝 0) := by
  obtain ⟨L₁, L₂, A₁, A₂, hlower, hne, hQ⟩ := exists_pair_of_kernel_direction hk
    Matrix.PosDef.one (harm_mem_homogPolySpan hd k).1 (harmRe_ne_zero hd k)
  refine ⟨L₁, L₂, A₁, A₂, hlower, hne, ?_⟩
  intro q' w hq' K₁ K₂ hK1m hK2m δ q hδ hq hq0 hclose1 hclose2 hsched
  have h := tendsto_empMoment_difference_div_pow hk A₁ A₂ hlower (monomialTest_continuous w)
    (monomialTest_hasPolynomialGrowth w) hK1m hK2m hδ hq hq0 hclose1 hclose2 hsched
  rw [hQ, gaussianCovariance_monomialTest_harmRe hd (by omega) w, neg_zero] at h
  exact h

end Laplace.Multi
