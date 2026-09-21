/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.MorseBottResponse
import Laplace.Multi.SingularPowerNormalForm

/-!
# Resolution in families, at the chart level: moving units on a fixed monomial chart

What "a resolution that works in the family" buys, in the form the present seabed can state.
On a resolved chart the loss is `a_s(y) · xᴺ` with the exponent data `N` frozen along the family
and only the unit `a_s` and the amplitude (cutoff) `χ_s` moving. In the singular power normal
form this is exactly `L_s = a_s(y) x^{2k}` with `k` fixed (`R11`), whose tangential expectation
values are, at every temperature, the normalised expectations under the density
`W_s = χ_s a_s^{-1/2k}`. Here we differentiate along the family:

* the generic fact (`hasDerivAt_normalized_of_dominated`): for a family of densities `W_u` with
  dominated derivatives `D_u`, `d/du (∫ g W_u / ∫ W_u) = ∫ g D_u / Z − E_u[g] · ∫ D_u / Z`
  (the covariance of `g` with the "score" `D_u / W_u` where `W_u ≠ 0`);
* the singular chart family (`SPFamilyData`, `hasDerivAt_spExp_tangential_family`):
  `D_s = χ'_s a_s^{-p} − p χ_s a_s^{-p-1} a'_s`, `p = 1/2k`, i.e. the score is
  `χ'_s/χ_s − (1/2k) a'_s/a_s` where `χ_s ≠ 0` (`spDeriv_eq_score`) — Astra's formula for the power
  model, with the RLCT `1/2k` as the weight of the unit's log-derivative;
* Morse–Bott with a varying cutoff (`hasDerivAt_mbExp_tangential_family'`): the score is
  `χ'_u/χ_u − ½ tr(H_u⁻¹ H'_u)`.

The frozen data (`k`, resp. the normal rank `r`) are what a relative simple-normal-crossings
resolution keeps constant along a stratum; across strata they jump and the smooth response fails
(`ToyCrossover`). The genuinely global statement — several charts, an actual blow-up — needs the
hironaka/greybook machinery of S5 and is not attempted here.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### The generic derivative of a normalised expectation -/

/-- **Derivative of a normalised expectation along a family of densities with dominated
derivatives.** -/
theorem hasDerivAt_normalized_of_dominated {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    {W D : ℝ → Y → ℝ} {g bound : Y → ℝ} {u₀ : ℝ}
    (hWm : ∀ u, AEStronglyMeasurable (W u) μ) (hWi : Integrable (W u₀) μ)
    (hDm : AEStronglyMeasurable (D u₀) μ) (hgm : Measurable g) {Mg : ℝ} (hg : ∀ y, |g y| ≤ Mg)
    (hbound : ∀ u y, |D u y| ≤ bound y) (hbi : Integrable bound μ)
    (hdiff : ∀ u y, HasDerivAt (fun v ↦ W v y) (D u y) u) (hZ : 0 < ∫ y, W u₀ y ∂μ) :
    HasDerivAt (fun u ↦ (∫ y, g y * W u y ∂μ) / ∫ y, W u y ∂μ)
      ((∫ y, g y * D u₀ y ∂μ) / (∫ y, W u₀ y ∂μ) -
        (∫ y, g y * W u₀ y ∂μ) / (∫ y, W u₀ y ∂μ) *
          ((∫ y, D u₀ y ∂μ) / (∫ y, W u₀ y ∂μ))) u₀ := by
  have hMg : 0 ≤ Mg := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y⟩ : Nonempty Y := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have : (∫ y, W u₀ y ∂μ) = 0 := by simp [Measure.eq_zero_of_isEmpty μ]
      linarith
    linarith [abs_nonneg (g y), hg y]
  -- the denominator
  have hZd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := W) (F' := D)
    (bound := bound) (x₀ := u₀) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall hWm) hWi hDm
    (Filter.Eventually.of_forall fun y u _ ↦ by rw [Real.norm_eq_abs]; exact hbound u y) hbi
    (Filter.Eventually.of_forall fun y u _ ↦ hdiff u y)
  -- the numerator
  have hNd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun u y ↦ g y * W u y) (F' := fun u y ↦ g y * D u y)
    (bound := fun y ↦ Mg * bound y) (x₀ := u₀) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun u ↦ (hgm.aestronglyMeasurable).mul (hWm u))
    (hWi.bdd_mul hgm.aestronglyMeasurable (c := Mg) (Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs]; exact hg y))
    ((hgm.aestronglyMeasurable).mul hDm)
    (Filter.Eventually.of_forall fun y u _ ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hg y) (hbound u y) (abs_nonneg _) hMg)
    (hbi.const_mul Mg)
    (Filter.Eventually.of_forall fun y u _ ↦ (hdiff u y).const_mul (g y))
  have hd := hNd.2.div hZd.2 hZ.ne'
  refine hd.congr_deriv ?_
  field_simp

/-! ### The singular chart family: `L_s = a_s(y) x^{2k}` with moving unit and amplitude -/

variable {n : ℕ}

/-- A one-parameter family of singular chart models: for each `s` the normal-form data with a
common lower bound `a₀` and a common compact support `K` for the cutoffs; the unit and the
amplitude are differentiable in `s` with continuous, bounded derivatives. -/
structure SPFamilyData (a a' χ χ' : ℝ → EuclidD n → ℝ) (k : ℕ) (a₀ Ba Bχ Cχ : ℝ)
    (K : Set (EuclidD n)) : Prop where
  base : ∀ s, SPData (a s) (χ s) k a₀
  K_compact : IsCompact K
  χ_supp : ∀ s y, y ∉ K → χ s y = 0
  a_deriv : ∀ s y, HasDerivAt (fun v ↦ a v y) (a' s y) s
  χ_deriv : ∀ s y, HasDerivAt (fun v ↦ χ v y) (χ' s y) s
  a'_cont : ∀ s, Continuous (a' s)
  χ'_cont : ∀ s, Continuous (χ' s)
  a'_bound : ∀ s y, |a' s y| ≤ Ba
  χ'_bound : ∀ s y, |χ' s y| ≤ Bχ
  χ_bound : ∀ s y, |χ s y| ≤ Cχ

/-- The tangential density `W_s = χ_s a_s^{-1/2k}`. -/
noncomputable def spDensity (a χ : ℝ → EuclidD n → ℝ) (k : ℕ) (s : ℝ) (y : EuclidD n) : ℝ :=
  χ s y * a s y ^ (-(1 : ℝ) / (2 * k))

/-- Its derivative in `s`: `D_s = χ'_s a_s^{-p} + χ_s (a'_s · (-p) · a_s^{-p-1})`. -/
noncomputable def spDeriv (a a' χ χ' : ℝ → EuclidD n → ℝ) (k : ℕ) (s : ℝ) (y : EuclidD n) : ℝ :=
  χ' s y * a s y ^ (-(1 : ℝ) / (2 * k)) +
    χ s y * (a' s y * (-(1 : ℝ) / (2 * k)) * a s y ^ (-(1 : ℝ) / (2 * k) - 1))

theorem SPFamilyData.hasDerivAt_spDensity {a a' χ χ' : ℝ → EuclidD n → ℝ} {k : ℕ}
    {a₀ Ba Bχ Cχ : ℝ} {K : Set (EuclidD n)} (h : SPFamilyData a a' χ χ' k a₀ Ba Bχ Cχ K) (s : ℝ)
    (y : EuclidD n) :
    HasDerivAt (fun v ↦ spDensity a χ k v y) (spDeriv a a' χ χ' k s y) s := by
  have ha := (h.a_deriv s y).rpow_const (p := -(1 : ℝ) / (2 * k))
    (Or.inl ((h.base s).a_pos y).ne')
  exact (h.χ_deriv s y).mul ha

/-- Off the common support the derivative vanishes. -/
theorem SPFamilyData.χ'_eq_zero {a a' χ χ' : ℝ → EuclidD n → ℝ} {k : ℕ} {a₀ Ba Bχ Cχ : ℝ}
    {K : Set (EuclidD n)} (h : SPFamilyData a a' χ χ' k a₀ Ba Bχ Cχ K) (s : ℝ) {y : EuclidD n}
    (hy : y ∉ K) : χ' s y = 0 := by
  have h1 := h.χ_deriv s y
  have h2 : HasDerivAt (fun v ↦ χ v y) 0 s := by
    have : (fun v ↦ χ v y) = fun _ ↦ (0 : ℝ) := funext fun v ↦ h.χ_supp v y hy
    rw [this]
    exact hasDerivAt_const _ _
  exact h1.unique h2

/-- The uniform bound on the derivative density. -/
theorem SPFamilyData.abs_spDeriv_le {a a' χ χ' : ℝ → EuclidD n → ℝ} {k : ℕ} {a₀ Ba Bχ Cχ : ℝ}
    {K : Set (EuclidD n)} (h : SPFamilyData a a' χ χ' k a₀ Ba Bχ Cχ K) (s : ℝ) (y : EuclidD n) :
    |spDeriv a a' χ χ' k s y| ≤
      K.indicator (fun _ ↦ Bχ * a₀ ^ (-(1 : ℝ) / (2 * k)) +
        Cχ * (Ba * (1 / (2 * k)) * a₀ ^ (-(1 : ℝ) / (2 * k) - 1))) y := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (h.base s).k_pos
  have ha₀ := (h.base s).a₀_pos
  have hay := (h.base s).a_pos y
  have hlow := (h.base s).a_lower y
  by_cases hy : y ∈ K
  · rw [Set.indicator_of_mem hy]
    -- `a^{-p} ≤ a₀^{-p}` and `a^{-p-1} ≤ a₀^{-p-1}`: `a ≥ a₀ > 0`, negative exponents
    have hmono : ∀ e : ℝ, e ≤ 0 → a s y ^ e ≤ a₀ ^ e := by
      intro e he
      rw [← neg_neg e, Real.rpow_neg hay.le, Real.rpow_neg ha₀.le]
      have : a₀ ^ (-e) ≤ a s y ^ (-e) := Real.rpow_le_rpow ha₀.le hlow (by linarith)
      exact inv_anti₀ (Real.rpow_pos_of_pos ha₀ _) this
    have h1 : |χ' s y * a s y ^ (-(1 : ℝ) / (2 * k))| ≤ Bχ * a₀ ^ (-(1 : ℝ) / (2 * k)) := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hay _)]
      exact mul_le_mul (h.χ'_bound s y) (hmono _ (by
        have : (0 : ℝ) ≤ 1 / (2 * k) := by positivity
        rw [neg_div]; linarith)) (Real.rpow_pos_of_pos hay _).le
        ((abs_nonneg _).trans (h.χ'_bound s y))
    have h2 : |χ s y * (a' s y * (-(1 : ℝ) / (2 * k)) * a s y ^ (-(1 : ℝ) / (2 * k) - 1))| ≤
        Cχ * (Ba * (1 / (2 * k)) * a₀ ^ (-(1 : ℝ) / (2 * k) - 1)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hay _), abs_div, abs_neg,
        abs_one, abs_of_pos (by positivity : (0 : ℝ) < 2 * k)]
      have hBa : 0 ≤ Ba := (abs_nonneg _).trans (h.a'_bound s y)
      refine mul_le_mul (h.χ_bound s y) ?_
        (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (Real.rpow_pos_of_pos hay _).le)
        ((abs_nonneg _).trans (h.χ_bound s y))
      refine mul_le_mul (mul_le_mul_of_nonneg_right (h.a'_bound s y) (by positivity))
        (hmono _ (by
          have : (0 : ℝ) ≤ 1 / (2 * k) := by positivity
          rw [neg_div]; linarith)) (Real.rpow_pos_of_pos hay _).le
        (mul_nonneg hBa (by positivity))
    unfold spDeriv
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  · rw [Set.indicator_of_notMem hy]
    unfold spDeriv
    rw [h.χ'_eq_zero s hy, h.χ_supp s y hy]
    simp

theorem SPFamilyData.continuous_spDensity {a a' χ χ' : ℝ → EuclidD n → ℝ} {k : ℕ}
    {a₀ Ba Bχ Cχ : ℝ} {K : Set (EuclidD n)} (h : SPFamilyData a a' χ χ' k a₀ Ba Bχ Cχ K) (s : ℝ) :
    Continuous (spDensity a χ k s) :=
  (h.base s).χ_cont.mul ((h.base s).continuous_rpow _)

theorem SPFamilyData.continuous_spDeriv {a a' χ χ' : ℝ → EuclidD n → ℝ} {k : ℕ}
    {a₀ Ba Bχ Cχ : ℝ} {K : Set (EuclidD n)} (h : SPFamilyData a a' χ χ' k a₀ Ba Bχ Cχ K) (s : ℝ) :
    Continuous (spDeriv a a' χ χ' k s) := by
  unfold spDeriv
  exact ((h.χ'_cont s).mul ((h.base s).continuous_rpow _)).add
    ((h.base s).χ_cont.mul (((h.a'_cont s).mul continuous_const).mul
      ((h.base s).continuous_rpow _)))

/-- The bound is integrable: a constant on a compact set. -/
theorem SPFamilyData.integrable_bound {a a' χ χ' : ℝ → EuclidD n → ℝ} {k : ℕ} {a₀ Ba Bχ Cχ : ℝ}
    {K : Set (EuclidD n)} (h : SPFamilyData a a' χ χ' k a₀ Ba Bχ Cχ K) (C : ℝ) :
    Integrable (K.indicator fun _ ↦ C) := by
  have hK := h.K_compact
  exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.isClosed.measurableSet

/-- **Response of the singular chart model**: along the family the tangential expectation of `g`
has derivative `∫ g D_s / Z_s − E_s[g] ∫ D_s / Z_s`, with `D_s` the derivative density
`χ'_s a_s^{-p} − p χ_s a_s^{-p-1} a'_s`. -/
theorem SPFamilyData.hasDerivAt_tanExp {a a' χ χ' : ℝ → EuclidD n → ℝ} {k : ℕ} {a₀ Ba Bχ Cχ : ℝ}
    {K : Set (EuclidD n)} (h : SPFamilyData a a' χ χ' k a₀ Ba Bχ Cχ K) {g : EuclidD n → ℝ}
    (hgm : Measurable g) {Mg : ℝ} (hg : ∀ y, |g y| ≤ Mg) {s₀ : ℝ} {y₀ : EuclidD n}
    (hy₀ : χ s₀ y₀ ≠ 0) :
    HasDerivAt (fun s ↦ (∫ y, g y * spDensity a χ k s y) / ∫ y, spDensity a χ k s y)
      ((∫ y, g y * spDeriv a a' χ χ' k s₀ y) / (∫ y, spDensity a χ k s₀ y) -
        (∫ y, g y * spDensity a χ k s₀ y) / (∫ y, spDensity a χ k s₀ y) *
          ((∫ y, spDeriv a a' χ χ' k s₀ y) / ∫ y, spDensity a χ k s₀ y)) s₀ := by
  have hZ : 0 < ∫ y, spDensity a χ k s₀ y := integral_cutoff_mul_rpow_pos (h.base s₀) hy₀ _
  refine hasDerivAt_normalized_of_dominated (W := spDensity a χ k) (D := spDeriv a a' χ χ' k)
    (fun u ↦ (h.continuous_spDensity u).aestronglyMeasurable) ?_
    (h.continuous_spDeriv s₀).aestronglyMeasurable hgm hg (fun u y ↦ h.abs_spDeriv_le u y)
    (h.integrable_bound _) (fun u y ↦ h.hasDerivAt_spDensity u y) hZ
  exact (h.continuous_spDensity s₀).integrable_of_hasCompactSupport
    ((h.base s₀).χ_supp.mul_right)

/-- Where the cutoff is nonzero the derivative density is the density times the score
`χ'_s/χ_s − (1/2k) a'_s/a_s`. -/
theorem SPFamilyData.spDeriv_eq_score {a a' χ χ' : ℝ → EuclidD n → ℝ} {k : ℕ} {a₀ Ba Bχ Cχ : ℝ}
    {K : Set (EuclidD n)} (h : SPFamilyData a a' χ χ' k a₀ Ba Bχ Cχ K) (s : ℝ) {y : EuclidD n}
    (hy : χ s y ≠ 0) :
    spDeriv a a' χ χ' k s y =
      spDensity a χ k s y * (χ' s y / χ s y - 1 / (2 * k) * (a' s y / a s y)) := by
  have hay := (h.base s).a_pos y
  have hk : (0 : ℝ) < k := by exact_mod_cast (h.base s).k_pos
  unfold spDeriv spDensity
  have hsub : a s y ^ (-(1 : ℝ) / (2 * k) - 1) = a s y ^ (-(1 : ℝ) / (2 * k)) / a s y := by
    rw [Real.rpow_sub hay, Real.rpow_one]
  rw [hsub]
  field_simp
  ring

/-- **Response of the expectation values of the singular model.** The exact tangential
expectations of `L_s = a_s x^{2k}` are these tangential expectations at every temperature (R11),
so along the family `d/ds E_{s,t}[yᵛ]` is given by the derivative density. -/
theorem SPFamilyData.hasDerivAt_spExp_tangential {a a' χ χ' : ℝ → EuclidD n → ℝ} {k : ℕ}
    {a₀ Ba Bχ Cχ : ℝ} {K : Set (EuclidD n)} (h : SPFamilyData a a' χ χ' k a₀ Ba Bχ Cχ K)
    {t : ℝ} (ht : 0 < t) {q : ℕ} (w : Fin q → Fin n) {s₀ : ℝ} {y₀ : EuclidD n}
    (hy₀ : χ s₀ y₀ ≠ 0) :
    HasDerivAt (fun s ↦ spExp (a s) (χ s) k t (fun z ↦ monomialTest w z.2))
      ((∫ y, monomialTest w y * spDeriv a a' χ χ' k s₀ y) / (∫ y, spDensity a χ k s₀ y) -
        (∫ y, monomialTest w y * spDensity a χ k s₀ y) / (∫ y, spDensity a χ k s₀ y) *
          ((∫ y, spDeriv a a' χ χ' k s₀ y) / ∫ y, spDensity a χ k s₀ y)) s₀ := by
  -- the monomial is bounded on the common support; replace it by a bounded test there
  obtain ⟨M, hM⟩ :=
    h.K_compact.exists_bound_of_continuousOn (monomialTest_continuous w).continuousOn
  set gK : EuclidD n → ℝ := K.indicator (monomialTest w) with hgK
  have hgKm : Measurable gK :=
    (monomialTest_continuous w).measurable.indicator h.K_compact.isClosed.measurableSet
  have hgKb : ∀ y, |gK y| ≤ |M| := fun y ↦ by
    simp only [gK]
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      exact ((hM y hy).trans (le_abs_self M))
    · rw [Set.indicator_of_notMem hy, abs_zero]
      exact abs_nonneg _
  have hd := h.hasDerivAt_tanExp hgKm hgKb (s₀ := s₀) hy₀
  -- on the support `gK = monomialTest w`
  have hnum : ∀ s, (∫ y, gK y * spDensity a χ k s y) =
      ∫ y, monomialTest w y * spDensity a χ k s y := by
    intro s
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [gK]
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      simp [spDensity, h.χ_supp s y hy]
  have hnum' : (∫ y, gK y * spDeriv a a' χ χ' k s₀ y) =
      ∫ y, monomialTest w y * spDeriv a a' χ χ' k s₀ y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [gK]
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      simp [spDeriv, h.χ_supp s₀ y hy, h.χ'_eq_zero s₀ hy]
  simp only [hnum, hnum'] at hd
  refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ ?_)
  change spExp (a s) (χ s) k t (fun z ↦ monomialTest w z.2) =
    (∫ y, monomialTest w y * spDensity a χ k s y) / ∫ y, spDensity a χ k s y
  rw [spExp_tangential (h.base s) ht w]
  unfold spDensity
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  ring

/-! ### Morse–Bott with a varying cutoff -/

/-- The Morse–Bott family with a varying cutoff: the `H`-data of `MBFamilyData` (with a reference
cutoff `χ₀`, unused) and a family `χ_u` supported in a common compact `K`, differentiable in `u`
with continuous bounded derivative. -/
structure MBFamilyData' {r : ℕ} (H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ)
    (χ₀ : EuclidD n → ℝ) (χ χ' : ℝ → EuclidD n → ℝ) (c B Bχ Cχ : ℝ) (K : Set (EuclidD n)) :
    Prop where
  fam : MBFamilyData H H' χ₀ c B
  K_compact : IsCompact K
  χ_cont : ∀ u, Continuous (χ u)
  χ_nonneg : ∀ u y, 0 ≤ χ u y
  χ_supp : ∀ u y, y ∉ K → χ u y = 0
  χ_deriv : ∀ u y, HasDerivAt (fun v ↦ χ v y) (χ' u y) u
  χ'_cont : ∀ u, Continuous (χ' u)
  χ'_bound : ∀ u y, |χ' u y| ≤ Bχ
  χ_bound : ∀ u y, |χ u y| ≤ Cχ

variable {r : ℕ}

theorem MBFamilyData'.base' {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ₀ : EuclidD n → ℝ}
    {χ χ' : ℝ → EuclidD n → ℝ} {c B Bχ Cχ : ℝ} {K : Set (EuclidD n)}
    (h : MBFamilyData' H H' χ₀ χ χ' c B Bχ Cχ K) (u : ℝ) : MBData (H u) (χ u) c :=
  { posDef := (h.fam.base u).posDef
    cont := (h.fam.base u).cont
    c_pos := (h.fam.base u).c_pos
    ellip := (h.fam.base u).ellip
    χ_cont := h.χ_cont u
    χ_supp := by
      refine IsCompact.of_isClosed_subset h.K_compact (isClosed_tsupport _)
        (closure_minimal ?_ h.K_compact.isClosed)
      intro y hy
      by_contra hcon
      exact hy (h.χ_supp u y hcon)
    χ_nonneg := h.χ_nonneg u }

theorem MBFamilyData'.χ'_eq_zero {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ₀ : EuclidD n → ℝ} {χ χ' : ℝ → EuclidD n → ℝ} {c B Bχ Cχ : ℝ} {K : Set (EuclidD n)}
    (h : MBFamilyData' H H' χ₀ χ χ' c B Bχ Cχ K) (u : ℝ) {y : EuclidD n} (hy : y ∉ K) :
    χ' u y = 0 := by
  have h1 := h.χ_deriv u y
  have h2 : HasDerivAt (fun v ↦ χ v y) 0 u := by
    have : (fun v ↦ χ v y) = fun _ ↦ (0 : ℝ) := funext fun v ↦ h.χ_supp v y hy
    rw [this]
    exact hasDerivAt_const _ _
  exact h1.unique h2

/-- The derivative density of `χ_u ρ_u`: `χ'_u ρ_u + χ_u S_u ρ_u`. -/
noncomputable def mbDeriv' (H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ)
    (χ χ' : ℝ → EuclidD n → ℝ) (u : ℝ) (y : EuclidD n) : ℝ :=
  χ' u y * mbDensity (H u) y + χ u y * (mbScore H H' u y * mbDensity (H u) y)

theorem MBFamilyData'.mbDensity_le {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ₀ : EuclidD n → ℝ} {χ χ' : ℝ → EuclidD n → ℝ} {c B Bχ Cχ : ℝ} {K : Set (EuclidD n)}
    (h : MBFamilyData' H H' χ₀ χ χ' c B Bχ Cχ K) (u : ℝ) (y : EuclidD n) :
    mbDensity (H u) y ≤ ∫ x : EuclidD r, Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
  unfold mbDensity
  have hc := (h.fam.base u).c_pos
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ (quadKernel_pos _ _).le)
    (integrable_exp_neg_mul_sq_norm (by positivity)) (Filter.Eventually.of_forall fun x ↦ ?_)
  exact quadKernel_le_exp_of_ellip ((h.fam.base u).ellip y) x

/-- **Response of the Morse–Bott expectation values with a varying cutoff.** -/
theorem MBFamilyData'.hasDerivAt_mbExp_tangential {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ₀ : EuclidD n → ℝ} {χ χ' : ℝ → EuclidD n → ℝ} {c B Bχ Cχ : ℝ} {K : Set (EuclidD n)}
    (h : MBFamilyData' H H' χ₀ χ χ' c B Bχ Cχ K) {t : ℝ} (ht : 0 < t) {q : ℕ} (w : Fin q → Fin n)
    {u₀ : ℝ} {y₀ : EuclidD n} (hy₀ : χ u₀ y₀ ≠ 0) :
    HasDerivAt (fun u ↦ mbExp (H u) (χ u) t (fun z ↦ monomialTest w z.2))
      ((∫ y, monomialTest w y * mbDeriv' H H' χ χ' u₀ y) / (∫ y, χ u₀ y * mbDensity (H u₀) y) -
        (∫ y, monomialTest w y * (χ u₀ y * mbDensity (H u₀) y)) /
          (∫ y, χ u₀ y * mbDensity (H u₀) y) *
          ((∫ y, mbDeriv' H H' χ χ' u₀ y) / ∫ y, χ u₀ y * mbDensity (H u₀) y)) u₀ := by
  have hc := (h.fam.base u₀).c_pos
  set I₀ : ℝ := ∫ x : EuclidD r, Real.exp (-(c / 2) * ‖x‖ ^ 2) with hI₀
  set I₂ : ℝ := ∫ x : EuclidD r, ‖x‖ ^ 2 * Real.exp (-(c / 2) * ‖x‖ ^ 2) with hI₂
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun x ↦ (Real.exp_pos _).le
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun x ↦ by positivity
  have hB := h.fam.B_nonneg
  -- the monomial truncated to the common support
  obtain ⟨M, hM⟩ :=
    h.K_compact.exists_bound_of_continuousOn (monomialTest_continuous w).continuousOn
  set gK : EuclidD n → ℝ := K.indicator (monomialTest w) with hgK
  have hgKm : Measurable gK :=
    (monomialTest_continuous w).measurable.indicator h.K_compact.isClosed.measurableSet
  have hgKb : ∀ y, |gK y| ≤ |M| := fun y ↦ by
    simp only [gK]
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      exact ((hM y hy).trans (le_abs_self M))
    · rw [Set.indicator_of_notMem hy, abs_zero]
      exact abs_nonneg _
  -- the bound on the derivative density
  have hbound : ∀ u y, |mbDeriv' H H' χ χ' u y| ≤
      K.indicator (fun _ ↦ Bχ * I₀ + Cχ * (1 / 2 * B * I₂)) y := by
    intro u y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      unfold mbDeriv'
      have h1 : |χ' u y * mbDensity (H u) y| ≤ Bχ * I₀ := by
        rw [abs_mul, abs_of_pos (mbDensity_pos (h.fam.base u) y)]
        exact mul_le_mul (h.χ'_bound u y) (h.mbDensity_le u y) (mbDensity_pos (h.fam.base u) y).le
          ((abs_nonneg _).trans (h.χ'_bound u y))
      have h2 : |χ u y * (mbScore H H' u y * mbDensity (H u) y)| ≤ Cχ * (1 / 2 * B * I₂) := by
        rw [abs_mul]
        exact mul_le_mul (h.χ_bound u y) (h.fam.abs_deriv_mbDensity_le u y) (abs_nonneg _)
          ((abs_nonneg _).trans (h.χ_bound u y))
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    · rw [Set.indicator_of_notMem hy]
      unfold mbDeriv'
      rw [h.χ'_eq_zero u hy, h.χ_supp u y hy]
      simp
  have hbi : Integrable (K.indicator fun _ : EuclidD n ↦ Bχ * I₀ + Cχ * (1 / 2 * B * I₂)) :=
    (integrableOn_const h.K_compact.measure_lt_top.ne).integrable_indicator
      h.K_compact.isClosed.measurableSet
  have hWc : ∀ u, Continuous fun y ↦ χ u y * mbDensity (H u) y := fun u ↦
    (h.χ_cont u).mul (mbDensity_continuous (h.fam.base u))
  have hDc : Continuous (mbDeriv' H H' χ χ' u₀) := by
    unfold mbDeriv'
    exact ((h.χ'_cont u₀).mul (mbDensity_continuous (h.fam.base u₀))).add
      ((h.χ_cont u₀).mul (h.fam.continuous_deriv_mbDensity u₀))
  have hZ : 0 < ∫ y, χ u₀ y * mbDensity (H u₀) y :=
    integral_cutoff_mul_mbDensity_pos (h.base' u₀) hy₀
  have hd := hasDerivAt_normalized_of_dominated (W := fun u y ↦ χ u y * mbDensity (H u) y)
    (D := mbDeriv' H H' χ χ') (fun u ↦ (hWc u).aestronglyMeasurable)
    ((hWc u₀).integrable_of_hasCompactSupport (h.base' u₀).χ_supp.mul_right)
    hDc.aestronglyMeasurable hgKm hgKb hbound hbi
    (fun u y ↦ (h.χ_deriv u y).mul (h.fam.hasDerivAt_mbDensity u y)) hZ
  -- replace the truncated test by the monomial
  have hnum : ∀ u, (∫ y, gK y * (χ u y * mbDensity (H u) y)) =
      ∫ y, monomialTest w y * (χ u y * mbDensity (H u) y) := by
    intro u
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [gK]
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      simp [h.χ_supp u y hy]
  have hnum' : (∫ y, gK y * mbDeriv' H H' χ χ' u₀ y) =
      ∫ y, monomialTest w y * mbDeriv' H H' χ χ' u₀ y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [gK]
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      simp [mbDeriv', h.χ_supp u₀ y hy, h.χ'_eq_zero u₀ hy]
  simp only [hnum, hnum'] at hd
  refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦ ?_)
  change mbExp (H u) (χ u) t (fun z ↦ monomialTest w z.2) =
    (∫ y, monomialTest w y * (χ u y * mbDensity (H u) y)) / ∫ y, χ u y * mbDensity (H u) y
  by_cases hu : ∃ y, χ u y ≠ 0
  · obtain ⟨y₁, hy₁⟩ := hu
    exact mbExp_tangential (h.base' u) ht hy₁ w
  · push Not at hu
    -- a vanishing cutoff: both sides are `0/0 = 0`
    have hχ0 : (fun y ↦ χ u y * mbDensity (H u) y) = fun _ ↦ 0 := funext fun y ↦ by
      simp [hu y]
    unfold mbExp mbWeight
    simp [hu]

end Laplace.Multi
