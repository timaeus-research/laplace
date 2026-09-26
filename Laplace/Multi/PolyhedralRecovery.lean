/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ProjectionDensityBounds

/-!
# Polyhedral completion IV: local entropy recovery and continuity of the rate

For `M_n → M` in a charged polytope, the **recovery laws** `g_n = f + h_{a(M_n)} − h_{a(M)}`
(`f` a dominated representative of `dq_M/dν`, `h_a` the vertex densities, `a` the continuous
vertex section) are eventually probability densities with mean `M_n`, converge uniformly to `f`,
and have relative entropy converging to `𝓘(M)` (`exists_recovery`). Hence the rate is upper
semicontinuous on the polytope; with `lowerSemicontinuous_genRate` it is **continuous on the whole
closed moment body** (`tendsto_genRate_of_tendsto`, `continuousOn_genRate_polytope`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section KL

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The log-likelihood ratio of a bounded-density law is the log of the density, a.e. -/
theorem llr_withDensity_ofReal_ae {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    llr (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) ν =ᵐ[ν] fun x ↦ Real.log (g x) := by
  filter_upwards [Measure.rnDeriv_withDensity ν hg.ennreal_ofReal] with x hx
  unfold llr
  rw [show (ν.withDensity fun x ↦ ENNReal.ofReal (g x)).rnDeriv ν x = ENNReal.ofReal (g x) from hx,
    ENNReal.toReal_ofReal (hg0 x)]

theorem integrable_mul_log_of_bdd {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {C : ℝ}
    (hgC : ∀ x, g x ≤ C) : Integrable (fun x ↦ g x * Real.log (g x)) ν := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := C)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  exact integrable_of_bdd_prob ν ⟨hg.mul (Real.measurable_log.comp hg), K, fun x ↦ by
    rw [← Real.norm_eq_abs]
    exact hK _ ⟨hg0 x, hgC x⟩⟩

theorem integrable_llr_withDensity_of_bdd {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    {C : ℝ} (hgC : ∀ x, g x ≤ C) :
    Integrable (llr (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) ν)
      (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) := by
  rw [integrable_withDensity_iff_integrable_smul₀' hg.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine (integrable_mul_log_of_bdd ν hg hg0 hgC).congr ?_
  filter_upwards [llr_withDensity_ofReal_ae ν hg hg0] with x hx
  rw [hx, ENNReal.toReal_ofReal (hg0 x), smul_eq_mul]

theorem klDiv_withDensity_ne_top_of_bdd {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    {C : ℝ} (hgC : ∀ x, g x ≤ C) :
    klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) ν ≠ ⊤ :=
  klDiv_ne_top (withDensity_absolutelyContinuous _ _)
    (integrable_llr_withDensity_of_bdd ν hg hg0 hgC)

/-- **The relative entropy of a bounded probability density** is `∫ g log g dν`. -/
theorem toReal_klDiv_withDensity_of_bdd {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    {C : ℝ} (hgC : ∀ x, g x ≤ C)
    (hP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (g x))) :
    (klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) ν).toReal =
      ∫ x, g x * Real.log (g x) ∂ν := by
  rw [toReal_klDiv (withDensity_absolutelyContinuous _ _)
    (integrable_llr_withDensity_of_bdd ν hg hg0 hgC), probReal_univ, probReal_univ,
    add_sub_cancel_right, integral_withDensity_eq_integral_toReal_smul₀
      hg.ennreal_ofReal.aemeasurable (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [llr_withDensity_ofReal_ae ν hg hg0] with x hx
  rw [hx, ENNReal.toReal_ofReal (hg0 x), smul_eq_mul]

theorem klDiv_withDensity_eq_ofReal_of_bdd {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    {C : ℝ} (hgC : ∀ x, g x ≤ C)
    (hP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (g x))) :
    klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) ν =
      ENNReal.ofReal (∫ x, g x * Real.log (g x) ∂ν) := by
  rw [← toReal_klDiv_withDensity_of_bdd ν hg hg0 hgC hP,
    ENNReal.ofReal_toReal (klDiv_withDensity_ne_top_of_bdd ν hg hg0 hgC)]

omit [IsProbabilityMeasure ν] in
theorem integral_withDensity_ofReal {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (F : X → ℝ) :
    ∫ x, F x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (g x)) = ∫ x, g x * F x ∂ν := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hg.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) F]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (hg0 x), smul_eq_mul]

omit [IsProbabilityMeasure ν] in
theorem isProbabilityMeasure_withDensity_ofReal {g : X → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hint : Integrable g ν) (h1 : ∫ x, g x ∂ν = 1) :
    IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hg0), h1, ENNReal.ofReal_one]

omit [IsProbabilityMeasure ν] in
theorem integral_eq_one_of_isProbabilityMeasure_withDensity {g : X → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hint : Integrable g ν)
    (hP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (g x))) :
    ∫ x, g x ∂ν = 1 := by
  have := hP.measure_univ
  rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hg0),
    ENNReal.ofReal_eq_one] at this

end KL

section Recovery

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V] (hV : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hV

omit [Nonempty X] [Fintype J] [Nonempty J] [Nonempty V] hS [IsProbabilityMeasure ν] in
/-- Termwise lower bounds pass to the vertex densities. -/
theorem neg_mul_vertexDensity_le {δ : ℝ} {a b : V → ℝ} (hab : ∀ v, -δ * a v ≤ b v)
    (x : X) : -δ * vertexDensity S ν V a x ≤ vertexDensity S ν V b x := by
  unfold vertexDensity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ ↦ ?_
  by_cases hx : x ∈ statFibre S (v : J → ℝ)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hab v) (hV v v.2).le
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

omit [Nonempty X] [Fintype J] [Nonempty J] [Nonempty V] hS [IsProbabilityMeasure ν] in
/-- The uniform bound `|h_b| ≤ Σ_v |b_v| / ν{S = v}`. -/
theorem abs_vertexDensity_le (b : V → ℝ) (x : X) :
    |vertexDensity S ν V b x| ≤ ∑ v : V, |b v| / ν.real (statFibre S (v : J → ℝ)) := by
  unfold vertexDensity
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ ↦ ?_)
  by_cases hx : x ∈ statFibre S (v : J → ℝ)
  · rw [Set.indicator_of_mem hx, abs_div, abs_of_pos (hV v v.2)]
  · rw [Set.indicator_of_notMem hx, abs_zero]
    exact div_nonneg (abs_nonneg _) measureReal_nonneg

/-- **Local entropy recovery**: along `M_n → M` in the polytope there are bounded densities `g_n`
with mean `M_n`, eventually nonnegative, converging uniformly to a bounded representative `f` of
`dq_M/dν`, with relative entropies converging to `𝓘(M)`. -/
theorem exists_recovery {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) {m : ℕ → J → ℝ}
    (hm : ∀ n, m n ∈ convexHull ℝ (V : Set (J → ℝ))) (hlim : Tendsto m atTop (𝓝 M)) :
    ∃ (f : X → ℝ) (g : ℕ → X → ℝ) (C : ℝ) (ε : ℕ → ℝ), Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x, f x ≤ C) ∧
      responseProjection hS ν M = ν.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      (∀ n, Measurable (g n)) ∧ (∀ n, ∫ x, g n x ∂ν = 1) ∧
      (∀ n j, ∫ x, S j x * g n x ∂ν = m n j) ∧
      (∀ n x, |g n x - f x| ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, ∀ x, 0 ≤ g n x) ∧
      Tendsto (fun n ↦ klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g n x)) ν) atTop
        (𝓝 (genRate ν S M)) := by
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hV hM
  obtain ⟨A, f₀, c, C₀, hA, -, hc, hf₀m, hf₀, hf₀b, hf₀0⟩ :=
    exists_projection_density_bounds hS ν hfin
  obtain ⟨a, ha_def⟩ : ∃ a : V → ℝ, a = vertexSection V M := ⟨_, rfl⟩
  have ha : a ∈ stdSimplex ℝ V := ha_def ▸ vertexSection_mem_stdSimplex V hM
  have haM : ∑ v : V, a v • (v : J → ℝ) = M := ha_def ▸ sum_vertexSection_smul V hM
  have ha1 : ∀ v, a v ≤ 1 := fun v ↦ ha_def ▸ vertexSection_le_one V hM v
  obtain ⟨δ, hδ, hdom⟩ := exists_pos_mul_vertexDensity_le hS ν V hV hfin hA hc hf₀
    (fun x hx ↦ (hf₀b x hx).1) hf₀0 ha haM
  obtain ⟨H, hH_def⟩ : ∃ H : ℝ, H = ∑ v : V, (ν.real (statFibre S (v : J → ℝ)))⁻¹ := ⟨_, rfl⟩
  have hH : ∀ x, vertexDensity S ν V a x ≤ H := fun x ↦ hH_def ▸ vertexDensity_le ν V hV ha1 x
  have hH0 : 0 ≤ H := hH_def ▸ Finset.sum_nonneg fun v _ ↦ inv_nonneg.2 (hV v v.2).le
  -- the pointwise dominated representative
  obtain ⟨f, hf_def⟩ : ∃ f : X → ℝ, f = fun x ↦ max (f₀ x) (δ * vertexDensity S ν V a x) :=
    ⟨_, rfl⟩
  have hfm : Measurable f := hf_def ▸ hf₀m.max ((measurable_vertexDensity hS ν V a).const_mul δ)
  have hdom' : ∀ x, δ * vertexDensity S ν V a x ≤ f x := fun x ↦ hf_def ▸ le_max_right _ _
  have hf0 : ∀ x, 0 ≤ f x := fun x ↦
    (mul_nonneg hδ.le (vertexDensity_nonneg ν V hV ha.1 x)).trans (hdom' x)
  obtain ⟨C, hC_def⟩ : ∃ C : ℝ, C = max C₀ (δ * H) + 1 := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by
    rw [hC_def]
    linarith [le_max_right C₀ (δ * H), mul_nonneg hδ.le hH0]
  have hfC : ∀ x, f x ≤ C := fun x ↦ by
    rw [hf_def, hC_def]
    beta_reduce
    by_cases hx : x ∈ A
    · exact (max_le_max (hf₀b x hx).2 (mul_le_mul_of_nonneg_left (hH x) hδ.le)).trans
        (by linarith)
    · rw [hf₀0 x hx]
      exact (max_le (le_max_of_le_right (mul_nonneg hδ.le hH0))
        (le_max_of_le_right (mul_le_mul_of_nonneg_left (hH x) hδ.le))).trans (by linarith)
  have hfae : f =ᵐ[ν] f₀ := by
    filter_upwards [hdom] with x hx
    rw [hf_def]
    exact max_eq_left hx
  have hf : responseProjection hS ν M = ν.withDensity fun x ↦ ENNReal.ofReal (f x) := by
    rw [hf₀]
    exact withDensity_congr_ae (hfae.mono fun x hx ↦ by beta_reduce; rw [hx])
  have hfP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (f x)) :=
    hf ▸ (responseProjection_spec hS ν hfin).1
  have hfint : Integrable f ν :=
    integrable_of_bdd_prob ν ⟨hfm, C, fun x ↦ abs_le.2 ⟨by linarith [hf0 x], hfC x⟩⟩
  have hf1 : ∫ x, f x ∂ν = 1 := integral_eq_one_of_isProbabilityMeasure_withDensity ν hf0 hfint hfP
  have hfmean : ∀ j, ∫ x, S j x * f x ∂ν = M j := fun j ↦ by
    have := congrFun (responseProjection_spec hS ν hfin).2.1 j
    rw [hf, integral_withDensity_ofReal ν hfm hf0] at this
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  -- the moving weights
  obtain ⟨an, han_def⟩ : ∃ an : ℕ → V → ℝ, an = fun n ↦ vertexSection V (m n) := ⟨_, rfl⟩
  have han : ∀ n, an n ∈ stdSimplex ℝ V := fun n ↦ han_def ▸ vertexSection_mem_stdSimplex V (hm n)
  have hanM : ∀ n, ∑ v : V, an n v • (v : J → ℝ) = m n := fun n ↦
    han_def ▸ sum_vertexSection_smul V (hm n)
  have hlimP : Tendsto m atTop (𝓝[convexHull ℝ (V : Set (J → ℝ))] M) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hm⟩
  have hacont : Tendsto an atTop (𝓝 a) := by
    rw [han_def, ha_def]
    exact ((continuousOn_vertexSection V) M hM).tendsto.comp hlimP
  have hacoord : ∀ v, Tendsto (fun n ↦ an n v) atTop (𝓝 (a v)) := fun v ↦
    tendsto_pi_nhds.1 hacont v
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℕ → ℝ,
      ε = fun n ↦ ∑ v : V, |an n v - a v| / ν.real (statFibre S (v : J → ℝ)) := ⟨_, rfl⟩
  have hε : Tendsto ε atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset V) fun v _ ↦
      (((hacoord v).sub_const (a v)).abs).div_const (ν.real (statFibre S (v : J → ℝ)))
    rw [hε_def]
    simpa [sub_self, abs_zero, zero_div, Finset.sum_const_zero] using h
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ → X → ℝ,
      g = fun n x ↦ f x + vertexDensity S ν V (an n - a) x := ⟨_, rfl⟩
  have hgm : ∀ n, Measurable (g n) := fun n ↦
    hg_def ▸ hfm.add (measurable_vertexDensity hS ν V _)
  have hgf : ∀ n x, |g n x - f x| ≤ ε n := fun n x ↦ by
    rw [hg_def, hε_def]
    simp only [add_sub_cancel_left]
    exact abs_vertexDensity_le ν V hV _ x
  have hg1 : ∀ n, ∫ x, g n x ∂ν = 1 := fun n ↦ by
    rw [hg_def]
    simp only
    rw [integral_add hfint (integrable_vertexDensity hS ν V _), hf1,
      integral_vertexDensity hS ν V hV]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, (han n).2, ha.2, sub_self, add_zero]
  have hcoord : ∀ (b : V → ℝ) (j : J),
      (∑ v : V, b v • (v : J → ℝ)) j = ∑ v : V, b v * (v : J → ℝ) j := fun b j ↦ by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun v _ ↦ by rw [Pi.smul_apply, smul_eq_mul]
  have hgmean : ∀ n j, ∫ x, S j x * g n x ∂ν = m n j := fun n j ↦ by
    obtain ⟨_, L, hL⟩ := hS j
    have h1 : Integrable (fun x ↦ S j x * f x) ν :=
      hfint.bdd_mul (hS j).1.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hL x)
    have h2 : Integrable (fun x ↦ S j x * vertexDensity S ν V (an n - a) x) ν :=
      (integrable_vertexDensity hS ν V _).bdd_mul (hS j).1.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hL x)
    rw [hg_def]
    simp only [mul_add]
    rw [integral_add h1 h2, hfmean, integral_stat_mul_vertexDensity hS ν V hV, ← hanM n, ← haM,
      hcoord, hcoord]
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  -- eventual nonnegativity
  obtain ⟨δ', hδ'_def⟩ : ∃ δ' : ℝ, δ' = min δ 1 := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := hδ'_def ▸ lt_min hδ one_pos
  have hδ'δ : δ' ≤ δ := hδ'_def ▸ min_le_left _ _
  have hev : ∀ᶠ n in atTop, ∀ v, -δ' * a v ≤ an n v - a v := by
    rw [Filter.eventually_all]
    intro v
    rcases (ha.1 v).eq_or_lt with h0 | hpos
    · refine Eventually.of_forall fun n ↦ ?_
      rw [← h0, mul_zero, sub_zero]
      exact (han n).1 v
    · have hlt : (1 - δ') * a v < a v := by nlinarith
      filter_upwards [(hacoord v).eventually_const_lt hlt] with n hn
      have hn' : (1 - δ') * a v < an n v := hn
      linarith
  have hgnn : ∀ᶠ n in atTop, ∀ x, 0 ≤ g n x := by
    filter_upwards [hev] with n hn x
    have h1 := neg_mul_vertexDensity_le ν V hV (b := an n - a) hn x
    have h2 := hdom' x
    have h3 := vertexDensity_nonneg ν V hV ha.1 x
    rw [hg_def]
    simp only
    nlinarith [mul_le_mul_of_nonneg_right hδ'δ h3]
  have hgC : ∀ᶠ n in atTop, ∀ x, g n x ≤ C + 1 := by
    filter_upwards [hε.eventually (eventually_le_nhds one_pos)] with n hn x
    linarith [(abs_le.1 (hgf n x)).2, hfC x]
  -- entropy convergence by dominated convergence
  have hKL : Tendsto (fun n ↦ ∫ x, g n x * Real.log (g n x) ∂ν) atTop
      (𝓝 (∫ x, f x * Real.log (f x) ∂ν)) := by
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := C + 1)).exists_bound_of_continuousOn
      Real.continuous_mul_log.continuousOn
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ K)
      (Eventually.of_forall fun n ↦
        ((hgm n).mul (Real.measurable_log.comp (hgm n))).aestronglyMeasurable) ?_
      (integrable_const K) (Eventually.of_forall fun x ↦ ?_)
    · filter_upwards [hgnn, hgC] with n hn hnC
      exact Eventually.of_forall fun x ↦ hK _ ⟨hn x, hnC x⟩
    · have hgx : Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact squeeze_zero (fun n ↦ norm_nonneg _)
          (fun n ↦ by rw [Real.norm_eq_abs]; exact hgf n x) hε
      exact (Real.continuous_mul_log.tendsto (f x)).comp hgx
  refine ⟨f, g, C, ε, hfm, hf0, hfC, hf, hgm, hg1, hgmean, hgf, hε, hgnn, ?_⟩
  have hgen : genRate ν S M = ENNReal.ofReal (∫ x, f x * Real.log (f x) ∂ν) := by
    rw [← (responseProjection_spec hS ν hfin).2.2.1, hf,
      klDiv_withDensity_eq_ofReal_of_bdd ν hfm hf0 hfC hfP]
  rw [hgen]
  refine (ENNReal.tendsto_ofReal hKL).congr' ?_
  filter_upwards [hgnn, hgC] with n hn hnC
  have hP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (g n x)) :=
    isProbabilityMeasure_withDensity_ofReal ν hn (integrable_of_bdd_prob ν
      ⟨hgm n, C + 1, fun x ↦ abs_le.2 ⟨by linarith [hn x], hnC x⟩⟩) (hg1 n)
  exact (klDiv_withDensity_eq_ofReal_of_bdd ν (hgm n) hn hnC hP).symm

/-- **The rate is continuous along sequences in the polytope.** -/
theorem tendsto_genRate_of_tendsto {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    {m : ℕ → J → ℝ} (hm : ∀ n, m n ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hlim : Tendsto m atTop (𝓝 M)) :
    Tendsto (fun n ↦ genRate ν S (m n)) atTop (𝓝 (genRate ν S M)) := by
  obtain ⟨f, g, C, ε, hfm, hf0, hfC, hf, hgm, hg1, hgmean, hgf, hε, hgnn, hKL⟩ :=
    exists_recovery hS ν V hV hM hm hlim
  have hC0 : 0 ≤ C := (hf0 (Classical.arbitrary X)).trans (hfC _)
  have hgC : ∀ᶠ n in atTop, ∀ x, g n x ≤ C + 1 := by
    filter_upwards [hε.eventually (eventually_le_nhds one_pos)] with n hn x
    linarith [(abs_le.1 (hgf n x)).2, hfC x]
  refine tendsto_order.2 ⟨fun a ha ↦ hlim.eventually (lowerSemicontinuous_genRate ν S M a ha),
    fun a ha ↦ ?_⟩
  filter_upwards [hgnn, hgC, hKL.eventually_lt_const ha] with n hn hnC hlt
  have hP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (g n x)) :=
    isProbabilityMeasure_withDensity_ofReal ν hn (integrable_of_bdd_prob ν
      ⟨hgm n, C + 1, fun x ↦ abs_le.2 ⟨by linarith [hn x, hC0], hnC x⟩⟩) (hg1 n)
  refine lt_of_le_of_lt (genRate_le_klDiv ν hS _ ?_) hlt
  funext j
  rw [integral_withDensity_ofReal ν (hgm n) hn, ← hgmean n j]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)

/-- **The rate is continuous on the whole charged polytope.** -/
theorem continuousOn_genRate_polytope :
    ContinuousOn (genRate ν S) (convexHull ℝ (V : Set (J → ℝ))) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_iff_seqContinuous.2 fun u M hu ↦ ?_
  exact tendsto_genRate_of_tendsto hS ν V hV M.2 (fun n ↦ (u n).2)
    ((continuous_subtype_val.tendsto M).comp hu)

/-- The rate is continuous on the whole moment body when it is a charged polytope. -/
theorem continuousOn_genRate_momentBody
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ))) :
    ContinuousOn (genRate ν S) (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
  hpoly ▸ continuousOn_genRate_polytope hS ν V hV

end Recovery

end Laplace.Multi
