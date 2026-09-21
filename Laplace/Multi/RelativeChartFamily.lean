/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.RelativeChartLeading
import Laplace.Multi.ResolvedChartResponse

/-!
# Level 3, conditional on a relative chart decomposition

**The hypothesis** (what a relative modification with frozen chart data delivers, see
`docs/hironaka_relative_resolution_spec.md`): on a parameter interval, a finite family of charts
`i : Fin N`, each with one active variable, frozen exponents `(k i, h i)`, units `a i s`, Jacobian
units `b i s` and cutoffs `χ i`, such that the tempered integral of a test decomposes as the sum of
the chart integrals (`RelativeChartDecomposition`), and the units and Jacobians are differentiable
in `s` with continuous bounded derivatives (`RelativeChartFamily`).

**What follows.** With `e i = (h i + 1)/(2 k i)` the chart exponents and `lam = min e`:

* `t^{lam} ∫ φ e^{-t L_s} → Σ_{e i = lam} C_i(s)`: the leading exponent is `lam`, read off the
  frozen data, hence constant along the family; the charts with `e i > lam` are `o(t^{-lam})`
  (`RelativeChartDecomposition.tendsto_rpow_mul`);
* each chart coefficient `C_i(s) = c_{k,h} ∫ χ_i(0,y) b_i(s,0,y) φ_i(0,y) a_i(s,0,y)^{-e_i} dy` is
  differentiable in `s`, with derivative the integral against the score
  `b'_i/b_i − e_i a'_i/a_i` (`RelativeChartFamily.hasDerivAt_chartCoeff`), and so is the leading
  coefficient (`hasDerivAt_leadingCoeff`);
* the leading normalised expectation `Σ C_i(s)[φ] / Σ C_i(s)[1]` is differentiable with a
  covariance-type derivative (`hasDerivAt_leadingExp`).

This is the note's Level 3 (`germbij_slop.tex` S7) with the resolution taken as a hypothesis in
chart form: fixed exponent data on every chart ⇒ constant `λ` and smooth coefficients whose
derivatives are covariances with explicit scores. The genuine global input — producing the chart
decomposition from an analytic family — is the hironaka spec.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {n : ℕ}

/-- The chart exponent `e = (h + 1)/(2k)`. -/
noncomputable def chartExp (k h : ℕ) : ℝ := ((h : ℝ) + 1) / (2 * k)

/-- The chart's leading density on the divisor `{x = 0}`:
`c_{k,h} χ(0,y) b(s,0,y) φ(0,y) a(s,0,y)^{-e}`. -/
noncomputable def chartDensity (k h : ℕ) (a b φ χ : ℝ × EuclidD n → ℝ) (y : EuclidD n) : ℝ :=
  agmom k h * (χ (0, y) * (b (0, y) * φ (0, y)) * a (0, y) ^ (-((h : ℝ) + 1) / (2 * k)))

/-- **A relative chart family**: for every `s` and every chart the chart data (with a common lower
bound `a₀` on the units), and `s`-derivatives of the units and Jacobians, continuous in the chart
variables and uniformly bounded. -/
structure RelativeChartFamily {N : ℕ} (k h : Fin N → ℕ)
    (a a' b b' : Fin N → ℝ → ℝ × EuclidD n → ℝ) (χ : Fin N → ℝ × EuclidD n → ℝ)
    (a₀ Ba Bb : ℝ) : Prop where
  chart : ∀ i s, ChartData (k i) (h i) (a i s) (b i s) (χ i) a₀
  a_deriv : ∀ i s z, HasDerivAt (fun v ↦ a i v z) (a' i s z) s
  b_deriv : ∀ i s z, HasDerivAt (fun v ↦ b i v z) (b' i s z) s
  a'_cont : ∀ i s, Continuous (a' i s)
  b'_cont : ∀ i s, Continuous (b' i s)
  a'_bound : ∀ i s z, |a' i s z| ≤ Ba
  b'_bound : ∀ i s z, |b' i s z| ≤ Bb
  b_bound : ∀ i s z, |b i s z| ≤ Bb

/-- **The resolution hypothesis**: the tempered integral of the test `φ` against `e^{-t L_s}`
equals the sum of the chart integrals (each chart carrying the pulled-back test `φ i`). -/
def RelativeChartDecomposition {N : ℕ} (Z : ℝ → ℝ → ℝ) (k h : Fin N → ℕ)
    (a b : Fin N → ℝ → ℝ × EuclidD n → ℝ) (χ φ : Fin N → ℝ × EuclidD n → ℝ) : Prop :=
  ∀ s t, 0 < t → Z s t = ∑ i, chartIntegral (k i) (h i) (a i s) (fun z ↦ b i s z * φ i z) (χ i)
    (fun _ ↦ (1 : ℝ)) t

/-! ### Leading order of the decomposed integral -/

/-- The chart data with the test absorbed into the Jacobian unit. -/
theorem ChartData.mul_test {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) {φ : ℝ × EuclidD n → ℝ} (hφ : Continuous φ) :
    ChartData k h a (fun z ↦ b z * φ z) χ a₀ :=
  { hc with b_cont := hc.b_cont.mul hφ }

/-- A chart with exponent `e > lam` is `o(t^{-lam})`. -/
theorem tendsto_rpow_mul_chartIntegral_of_lt {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) {lam : ℝ} (hlt : lam < chartExp k h) :
    Tendsto (fun t ↦ t ^ lam * chartIntegral k h a b χ (fun _ ↦ (1 : ℝ)) t) atTop (𝓝 0) := by
  have h1 := hc.tendsto_rpow_mul_chartIntegral (g := fun _ ↦ (1 : ℝ)) continuous_const
  have h2 : Tendsto (fun t : ℝ ↦ t ^ (-(chartExp k h - lam))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have := h2.mul h1
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  unfold chartExp
  rw [← mul_assoc, ← Real.rpow_add ht]
  congr 2
  ring

/-- **Constant leading exponent and the leading coefficient of the family.** With `lam` the
minimum of the chart exponents, `t^{lam} Z s t → Σ_{e i = lam} C_i(s)`. -/
theorem RelativeChartDecomposition.tendsto_rpow_mul {N : ℕ} {Z : ℝ → ℝ → ℝ} {k h : Fin N → ℕ}
    {a b : Fin N → ℝ → ℝ × EuclidD n → ℝ} {χ φ : Fin N → ℝ × EuclidD n → ℝ}
    (hZ : RelativeChartDecomposition Z k h a b χ φ) {a₀ : ℝ} (s : ℝ)
    (hc : ∀ i, ChartData (k i) (h i) (a i s) (b i s) (χ i) a₀) (hφ : ∀ i, Continuous (φ i))
    {lam : ℝ} (hlam : ∀ i, lam ≤ chartExp (k i) (h i)) :
    Tendsto (fun t ↦ t ^ lam * Z s t) atTop
      (𝓝 (∑ i ∈ Finset.univ.filter (fun i ↦ chartExp (k i) (h i) = lam),
        ∫ y, chartDensity (k i) (h i) (a i s) (b i s) (φ i) (χ i) y)) := by
  classical
  -- each chart's contribution
  have hterm : ∀ i, Tendsto (fun t ↦ t ^ lam *
      chartIntegral (k i) (h i) (a i s) (fun z ↦ b i s z * φ i z) (χ i) (fun _ ↦ (1 : ℝ)) t) atTop
      (𝓝 (if chartExp (k i) (h i) = lam then
        ∫ y, chartDensity (k i) (h i) (a i s) (b i s) (φ i) (χ i) y else 0)) := by
    intro i
    by_cases hi : chartExp (k i) (h i) = lam
    · rw [if_pos hi]
      have := ((hc i).mul_test (hφ i)).tendsto_rpow_mul_chartIntegral (g := fun _ ↦ (1 : ℝ))
        continuous_const
      have hcoef : chartCoeff (k i) (h i) (a i s) (fun z ↦ b i s z * φ i z) (χ i) (fun _ ↦ 1) =
          ∫ y, chartDensity (k i) (h i) (a i s) (b i s) (φ i) (χ i) y := by
        unfold chartCoeff chartDensity
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
        ring
      rw [hcoef] at this
      unfold chartExp at hi
      rw [← hi]
      exact this
    · rw [if_neg hi]
      exact tendsto_rpow_mul_chartIntegral_of_lt ((hc i).mul_test (hφ i))
        (lt_of_le_of_ne (hlam i) (Ne.symm hi))
  have hsum := tendsto_finsetSum Finset.univ fun i _ ↦ hterm i
  -- the sum of the `if`s is the sum over the charts attaining `lam`
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [hZ s t ht, Finset.mul_sum]

/-! ### The response of the chart coefficients -/

variable {N : ℕ} {k h : Fin N → ℕ} {a a' b b' : Fin N → ℝ → ℝ × EuclidD n → ℝ}
  {χ : Fin N → ℝ × EuclidD n → ℝ} {a₀ Ba Bb : ℝ}

/-- The `s`-derivative of the chart density on the divisor. -/
noncomputable def chartDensityDeriv (k h : ℕ) (a a' b b' φ χ : ℝ × EuclidD n → ℝ) (y : EuclidD n) :
    ℝ :=
  agmom k h * (χ (0, y) * φ (0, y) *
    (b' (0, y) * a (0, y) ^ (-((h : ℝ) + 1) / (2 * k)) +
      b (0, y) * (a' (0, y) * (-((h : ℝ) + 1) / (2 * k)) *
        a (0, y) ^ (-((h : ℝ) + 1) / (2 * k) - 1))))

theorem RelativeChartFamily.hasDerivAt_chartDensity
    (hf : RelativeChartFamily k h a a' b b' χ a₀ Ba Bb)
    (i : Fin N) {φ : ℝ × EuclidD n → ℝ} (s : ℝ) (y : EuclidD n) :
    HasDerivAt (fun v ↦ chartDensity (k i) (h i) (a i v) (b i v) φ (χ i) y)
      (chartDensityDeriv (k i) (h i) (a i s) (a' i s) (b i s) (b' i s) φ (χ i) y) s := by
  have hb := hf.b_deriv i s (0, y)
  have ha := (hf.a_deriv i s (0, y)).rpow_const (p := -((h i : ℝ) + 1) / (2 * k i))
    (Or.inl ((hf.chart i s).a₀_pos.trans_le ((hf.chart i s).a_lower _)).ne')
  have := ((hb.mul_const (φ (0, y))).const_mul (χ i (0, y))).mul ha
  have hd := this.const_mul (agmom (k i) (h i))
  unfold chartDensity chartDensityDeriv
  refine hd.congr_deriv ?_
  ring

/-- Uniform bound on the derivative of the chart density. -/
theorem RelativeChartFamily.abs_chartDensityDeriv_le
    (hf : RelativeChartFamily k h a a' b b' χ a₀ Ba Bb)
    (i : Fin N) {φ : ℝ × EuclidD n → ℝ} (s : ℝ) (y : EuclidD n) :
    |chartDensityDeriv (k i) (h i) (a i s) (a' i s) (b i s) (b' i s) φ (χ i) y| ≤
      |χ i (0, y) * φ (0, y)| *
        (agmom (k i) (h i) * (Bb * a₀ ^ (-((h i : ℝ) + 1) / (2 * k i)) +
          Bb * (Ba * (((h i : ℝ) + 1) / (2 * k i)) *
            a₀ ^ (-((h i : ℝ) + 1) / (2 * k i) - 1)))) := by
  have hc := hf.chart i s
  have hk : (0 : ℝ) < k i := by exact_mod_cast hc.k_pos
  have ha₀ := hc.a₀_pos
  have hay := ha₀.trans_le (hc.a_lower (0, y))
  have hlow := hc.a_lower (0, y)
  have hBb : 0 ≤ Bb := (abs_nonneg _).trans (hf.b_bound i s (0, y))
  have hBa : 0 ≤ Ba := (abs_nonneg _).trans (hf.a'_bound i s (0, y))
  have hmono : ∀ e : ℝ, e ≤ 0 → a i s (0, y) ^ e ≤ a₀ ^ e := by
    intro e he
    rw [← neg_neg e, Real.rpow_neg hay.le, Real.rpow_neg ha₀.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos ha₀ _) (Real.rpow_le_rpow ha₀.le hlow (by linarith))
  have hexp0 : -((h i : ℝ) + 1) / (2 * k i) ≤ 0 := by
    rw [neg_div]
    have : (0 : ℝ) ≤ ((h i : ℝ) + 1) / (2 * k i) := by positivity
    linarith
  have hexp1 : -((h i : ℝ) + 1) / (2 * k i) - 1 ≤ 0 := by linarith
  have hag : 0 ≤ agmom (k i) (h i) := (agmom_pos (k i) hc.k_pos (h i)).le
  have h1 : |b' i s (0, y) * a i s (0, y) ^ (-((h i : ℝ) + 1) / (2 * k i))| ≤
      Bb * a₀ ^ (-((h i : ℝ) + 1) / (2 * k i)) := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hay _)]
    exact mul_le_mul (hf.b'_bound i s _) (hmono _ hexp0) (Real.rpow_pos_of_pos hay _).le hBb
  have h2 : |b i s (0, y) * (a' i s (0, y) * (-((h i : ℝ) + 1) / (2 * k i)) *
      a i s (0, y) ^ (-((h i : ℝ) + 1) / (2 * k i) - 1))| ≤
      Bb * (Ba * (((h i : ℝ) + 1) / (2 * k i)) * a₀ ^ (-((h i : ℝ) + 1) / (2 * k i) - 1)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hay _), abs_div, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < (h i : ℝ) + 1),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * k i)]
    refine mul_le_mul (hf.b_bound i s _) ?_
      (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (Real.rpow_pos_of_pos hay _).le) hBb
    refine mul_le_mul (mul_le_mul_of_nonneg_right (hf.a'_bound i s _) (by positivity))
      (hmono _ hexp1) (Real.rpow_pos_of_pos hay _).le (mul_nonneg hBa (by positivity))
  unfold chartDensityDeriv
  rw [abs_mul, abs_mul, abs_of_nonneg hag, show |χ i (0, y) * φ (0, y)| *
      (agmom (k i) (h i) * (Bb * a₀ ^ (-((h i : ℝ) + 1) / (2 * k i)) +
        Bb * (Ba * (((h i : ℝ) + 1) / (2 * k i)) * a₀ ^ (-((h i : ℝ) + 1) / (2 * k i) - 1)))) =
      agmom (k i) (h i) * (|χ i (0, y) * φ (0, y)| *
        (Bb * a₀ ^ (-((h i : ℝ) + 1) / (2 * k i)) +
          Bb * (Ba * (((h i : ℝ) + 1) / (2 * k i)) * a₀ ^ (-((h i : ℝ) + 1) / (2 * k i) - 1))))
      by ring]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hag
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem RelativeChartFamily.continuous_chartDensity
    (hf : RelativeChartFamily k h a a' b b' χ a₀ Ba Bb)
    (i : Fin N) {φ : ℝ × EuclidD n → ℝ} (hφ : Continuous φ) (s : ℝ) :
    Continuous fun y ↦ chartDensity (k i) (h i) (a i s) (b i s) φ (χ i) y := by
  have hc := hf.chart i s
  have hz : Continuous fun y : EuclidD n ↦ ((0 : ℝ), y) := by fun_prop
  have ha : Continuous fun y : EuclidD n ↦ a i s (0, y) ^ (-((h i : ℝ) + 1) / (2 * k i)) :=
    (hc.a_cont.comp hz).rpow_const fun y ↦
      Or.inl (hc.a₀_pos.trans_le (hc.a_lower _)).ne'
  unfold chartDensity
  exact continuous_const.mul
    (((hc.χ_cont.comp hz).mul ((hc.b_cont.comp hz).mul (hφ.comp hz))).mul ha)

theorem RelativeChartFamily.continuous_chartDensityDeriv
    (hf : RelativeChartFamily k h a a' b b' χ a₀ Ba Bb) (i : Fin N) {φ : ℝ × EuclidD n → ℝ}
    (hφ : Continuous φ) (s : ℝ) :
    Continuous fun y ↦
      chartDensityDeriv (k i) (h i) (a i s) (a' i s) (b i s) (b' i s) φ (χ i) y := by
  have hc := hf.chart i s
  have hz : Continuous fun y : EuclidD n ↦ ((0 : ℝ), y) := by fun_prop
  have hpos : ∀ y : EuclidD n, a i s (0, y) ≠ 0 := fun y ↦
    (hc.a₀_pos.trans_le (hc.a_lower _)).ne'
  have ha : Continuous fun y : EuclidD n ↦ a i s (0, y) ^ (-((h i : ℝ) + 1) / (2 * k i)) :=
    (hc.a_cont.comp hz).rpow_const fun y ↦ Or.inl (hpos y)
  have ha1 : Continuous fun y : EuclidD n ↦ a i s (0, y) ^ (-((h i : ℝ) + 1) / (2 * k i) - 1) :=
    (hc.a_cont.comp hz).rpow_const fun y ↦ Or.inl (hpos y)
  unfold chartDensityDeriv
  exact continuous_const.mul (((hc.χ_cont.comp hz).mul (hφ.comp hz)).mul
    ((((hf.b'_cont i s).comp hz).mul ha).add
      ((hc.b_cont.comp hz).mul ((((hf.a'_cont i s).comp hz).mul continuous_const).mul ha1))))

/-- The chart density has compact support in `y` (the `y`-shadow of the cutoff's support). -/
theorem RelativeChartFamily.hasCompactSupport_cutoff_zero
    (hf : RelativeChartFamily k h a a' b b' χ a₀ Ba Bb) (i : Fin N) (s : ℝ) :
    HasCompactSupport fun y : EuclidD n ↦ χ i (0, y) := by
  have hc := hf.chart i s
  have hK : IsCompact (Prod.snd '' tsupport (χ i)) := hc.χ_supp.image continuous_snd
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) (closure_minimal ?_ hK.isClosed)
  intro y hy
  rw [Function.mem_support] at hy
  exact ⟨(0, y), subset_tsupport _ hy, rfl⟩

/-- **The response of a chart coefficient**: `d/ds C_i(s) = ∫ (score density)`. -/
theorem RelativeChartFamily.hasDerivAt_chartCoeff
    (hf : RelativeChartFamily k h a a' b b' χ a₀ Ba Bb)
    (i : Fin N) {φ : ℝ × EuclidD n → ℝ} (hφ : Continuous φ) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ ∫ y, chartDensity (k i) (h i) (a i s) (b i s) φ (χ i) y)
      (∫ y, chartDensityDeriv (k i) (h i) (a i s₀) (a' i s₀) (b i s₀) (b' i s₀) φ (χ i) y) s₀ := by
  have hz : Continuous fun y : EuclidD n ↦ ((0 : ℝ), y) := by fun_prop
  have hsupp : HasCompactSupport fun y : EuclidD n ↦ |χ i (0, y) * φ (0, y)| := by
    have := (hf.hasCompactSupport_cutoff_zero i s₀).mul_right (f' := fun y ↦ φ (0, y))
    exact this.abs
  have hbi : Integrable fun y : EuclidD n ↦ |χ i (0, y) * φ (0, y)| *
      (agmom (k i) (h i) * (Bb * a₀ ^ (-((h i : ℝ) + 1) / (2 * k i)) +
        Bb * (Ba * (((h i : ℝ) + 1) / (2 * k i)) * a₀ ^ (-((h i : ℝ) + 1) / (2 * k i) - 1)))) :=
    (((((hf.chart i s₀).χ_cont.comp hz).mul (hφ.comp hz)).abs.integrable_of_hasCompactSupport
      hsupp)).mul_const _
  have hWi : Integrable fun y ↦ chartDensity (k i) (h i) (a i s₀) (b i s₀) φ (χ i) y := by
    refine (hf.continuous_chartDensity i hφ s₀).integrable_of_hasCompactSupport ?_
    have : (fun y ↦ chartDensity (k i) (h i) (a i s₀) (b i s₀) φ (χ i) y) =
        fun y ↦ χ i (0, y) * (agmom (k i) (h i) * (b i s₀ (0, y) * φ (0, y)) *
          a i s₀ (0, y) ^ (-((h i : ℝ) + 1) / (2 * k i))) := by
      funext y
      unfold chartDensity
      ring
    rw [this]
    exact (hf.hasCompactSupport_cutoff_zero i s₀).mul_right
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (EuclidD n)))
    (F := fun s y ↦ chartDensity (k i) (h i) (a i s) (b i s) φ (χ i) y)
    (F' := fun s y ↦ chartDensityDeriv (k i) (h i) (a i s) (a' i s) (b i s) (b' i s) φ (χ i) y)
    (x₀ := s₀) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun s ↦ (hf.continuous_chartDensity i hφ s).aestronglyMeasurable)
    hWi (hf.continuous_chartDensityDeriv i hφ s₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y s _ ↦ by
      rw [Real.norm_eq_abs]
      exact hf.abs_chartDensityDeriv_le i s y) hbi
    (Filter.Eventually.of_forall fun y s _ ↦ hf.hasDerivAt_chartDensity i s y)
  exact key.2

/-- **The response of the leading coefficient**: the sum over the charts attaining `lam`. -/
theorem RelativeChartFamily.hasDerivAt_leadingCoeff
    (hf : RelativeChartFamily k h a a' b b' χ a₀ Ba Bb)
    {φ : Fin N → ℝ × EuclidD n → ℝ} (hφ : ∀ i, Continuous (φ i)) (T : Finset (Fin N)) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ ∑ i ∈ T, ∫ y, chartDensity (k i) (h i) (a i s) (b i s) (φ i) (χ i) y)
      (∑ i ∈ T, ∫ y, chartDensityDeriv (k i) (h i) (a i s₀) (a' i s₀) (b i s₀) (b' i s₀) (φ i)
        (χ i) y) s₀ := by
  have := HasDerivAt.sum (u := T)
    (A := fun i s ↦ ∫ y, chartDensity (k i) (h i) (a i s) (b i s) (φ i) (χ i) y)
    (A' := fun i ↦ ∫ y, chartDensityDeriv (k i) (h i) (a i s₀) (a' i s₀) (b i s₀) (b' i s₀) (φ i)
      (χ i) y) fun i _ ↦ hf.hasDerivAt_chartCoeff i (hφ i) s₀
  have hfun : (fun s ↦ ∑ i ∈ T, ∫ y, chartDensity (k i) (h i) (a i s) (b i s) (φ i) (χ i) y) =
      ∑ i ∈ T, fun s ↦ ∫ y, chartDensity (k i) (h i) (a i s) (b i s) (φ i) (χ i) y := by
    funext s
    simp [Finset.sum_apply]
  rw [hfun]
  exact this

/-- **The response of the leading normalised expectation**: with the leading density
`W_s = Σ_{i ∈ T} chartDensity_i(s)` of the test `1` and the leading numerator density of the test
`φ`, `d/ds (∫ W^φ_s / ∫ W_s) = ∫ D^φ / Z − E[φ] ∫ D / Z`. -/
theorem RelativeChartFamily.hasDerivAt_leadingExp
    (hf : RelativeChartFamily k h a a' b b' χ a₀ Ba Bb)
    {φ : Fin N → ℝ × EuclidD n → ℝ} (hφ : ∀ i, Continuous (φ i)) (T : Finset (Fin N)) {s₀ : ℝ}
    (hZ : 0 < ∑ i ∈ T, ∫ y, chartDensity (k i) (h i) (a i s₀) (b i s₀) (fun _ ↦ 1) (χ i) y) :
    HasDerivAt (fun s ↦ (∑ i ∈ T, ∫ y, chartDensity (k i) (h i) (a i s) (b i s) (φ i) (χ i) y) /
        ∑ i ∈ T, ∫ y, chartDensity (k i) (h i) (a i s) (b i s) (fun _ ↦ 1) (χ i) y)
      ((∑ i ∈ T, ∫ y, chartDensityDeriv (k i) (h i) (a i s₀) (a' i s₀) (b i s₀) (b' i s₀) (φ i)
          (χ i) y) /
        (∑ i ∈ T, ∫ y, chartDensity (k i) (h i) (a i s₀) (b i s₀) (fun _ ↦ 1) (χ i) y) -
        (∑ i ∈ T, ∫ y, chartDensity (k i) (h i) (a i s₀) (b i s₀) (φ i) (χ i) y) /
          (∑ i ∈ T, ∫ y, chartDensity (k i) (h i) (a i s₀) (b i s₀) (fun _ ↦ 1) (χ i) y) *
          ((∑ i ∈ T, ∫ y, chartDensityDeriv (k i) (h i) (a i s₀) (a' i s₀) (b i s₀) (b' i s₀)
            (fun _ ↦ 1) (χ i) y) /
            ∑ i ∈ T, ∫ y, chartDensity (k i) (h i) (a i s₀) (b i s₀) (fun _ ↦ 1) (χ i) y)) s₀ := by
  have hN := hf.hasDerivAt_leadingCoeff hφ T s₀
  have hD := hf.hasDerivAt_leadingCoeff (φ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ continuous_const) T s₀
  have hd := hN.div hD hZ.ne'
  refine hd.congr_deriv ?_
  field_simp

end Laplace.Multi
