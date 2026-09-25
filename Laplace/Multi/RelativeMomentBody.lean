/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RelativeInterior
import Laplace.Multi.BoundaryBarrier

/-!
# The relative-interior moment-body theorem

For a bounded statistic `S` under a positive prior, **without any nondegeneracy hypothesis**, the
image of the mean map is the relative interior of the moment body:
  `range (θ ↦ E_θ S) = intrinsicInterior ℝ K`
(`range_meanMap_eq_intrinsicInterior_momentBody`).

* `⊆`: a mean `m = E_θ S` lies in `K`, and any functional `e·` maximised at `m` over `K` bounds
  `e·S` almost surely by its own `θ`-expectation, hence is almost surely constant, hence constant on
  `K`; the supporting characterisation of the relative interior does the rest.
* `⊇`: for `x ∈ relint K` the variational functional `θ ↦ A(θ) + θ·x` is coercive on the direction
  subspace `𝕍 = dirSpan μ π S` of the affine span (`cap_lemma_rel`, `coercive_bound_rel`, from far
  points of the essential range in every unit direction of `𝕍`), so it has a minimiser `θ₀ ∈ 𝕍`
  (`exists_min_variational_rel`); the first-order condition along `𝕍` gives `e·(x − m(θ₀)) = 0` for
  all `e ∈ 𝕍`, and `x − m(θ₀) ∈ 𝕍` itself, so `x = m(θ₀)` (`meanMap_eq_of_min_rel`).

This is the intrinsic response chart of a conditioned or degenerate family: the ambient
nondegeneracy `hnd` fails on every proper supporting face, but the chart survives.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : Type*} [Fintype J] [Nonempty J]
variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hπm hπi hπ hπpos hS

omit [Nonempty X] [Nonempty J] hπm hπi hπ hπpos hS in
/-- The direction subspace `𝕍` of the affine span of the moment body. -/
abbrev dirSpan (μ : Measure X) (π : X → ℝ) (S : J → X → ℝ) : Submodule ℝ (J → ℝ) :=
  (affineSpan ℝ (momentBody μ π S)).direction

omit [Nonempty X] hπm hπi hπ hπpos hS in
/-- `1 ≤ e·e` for a unit vector of the sup norm. -/
theorem one_le_dotJ_self {e : J → ℝ} (he : ‖e‖ = 1) : 1 ≤ dotJ e e := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j ↦ |e j|) Finset.univ_nonempty
  have h1 : ‖e‖ ≤ |e j| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i ↦ by
    rw [Real.norm_eq_abs]
    exact hj i (Finset.mem_univ i)
  rw [he] at h1
  calc (1 : ℝ) ≤ |e j| * |e j| := by nlinarith
    _ = e j * e j := by rw [abs_mul_abs_self]
    _ ≤ ∑ i, e i * e i :=
      Finset.single_le_sum (f := fun i ↦ e i * e i) (fun i _ ↦ mul_self_nonneg _)
        (Finset.mem_univ j)

omit [Nonempty X] hπm hπi hπ hπpos hS in
/-- **A far point of the essential range in every unit direction of `𝕍`.** -/
theorem exists_far_point_rel {x : J → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ v ∈ dirSpan μ π S, ‖v‖ < δ → x + v ∈ momentBody μ π S) {e : J → ℝ}
    (heV : e ∈ dirSpan μ π S) (he : ‖e‖ = 1) : ∃ y₀ ∈ essRange μ π S, δ / 2 ≤ dotJ e (x - y₀) := by
  by_contra h
  push Not at h
  have hlin := isLinearMap_dotJ e
  have hsub : essRange μ π S ⊆ {y | dotJ e x - δ / 2 ≤ dotJ e y} := fun y hy ↦ by
    have := h y hy
    rw [hlin.map_sub] at this
    change dotJ e x - δ / 2 ≤ dotJ e y
    linarith
  have hC : momentBody μ π S ⊆ {y | dotJ e x - δ / 2 ≤ dotJ e y} :=
    closure_minimal (convexHull_min hsub (convex_halfSpace_ge hlin _))
      (isClosed_le continuous_const (continuous_dotJ_right e))
  have hz : x + (-(3 * δ / 4)) • e ∈ momentBody μ π S := by
    refine hball _ (Submodule.smul_mem _ _ heV) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity), he, mul_one]
    linarith
  have h1 : dotJ e x - δ / 2 ≤ dotJ e (x + (-(3 * δ / 4)) • e) := hC hz
  rw [hlin.map_add, hlin.map_smul, smul_eq_mul] at h1
  have hee := one_le_dotJ_self he
  nlinarith

omit [Nonempty X] hπpos in
/-- **The relative cap lemma**: for `x` in the relative interior of the moment body there are
`c, m > 0` such that every unit direction `e ∈ 𝕍` has a cap `{⟨e, x − S⟩ ≥ c}` of prior mass at
least `m`. -/
theorem cap_lemma_rel {x : J → ℝ} (hx : x ∈ intrinsicInterior ℝ (momentBody μ π S)) :
    ∃ c > 0, ∃ m > 0, ∀ e ∈ dirSpan μ π S, ‖e‖ = 1 →
      m ≤ ∫ y in {y | c ≤ dotJ e (x - statPoint S y)}, π y ∂μ := by
  classical
  obtain ⟨K, hK0, hK⟩ : ∃ K, 0 ≤ K ∧ ∀ j y, |S j y| ≤ K := by
    choose M hM using fun j ↦ (hS j).2
    refine ⟨∑ j, |M j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j y ↦ (hM j y).trans ?_⟩
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j ↦ |M j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j))
  have hSx : ∀ y, ‖x - statPoint S y‖ ≤ ‖x‖ + K := fun y ↦
    (norm_sub_le _ _).trans (add_le_add le_rfl ((pi_norm_le_iff_of_nonneg hK0).2 fun j ↦ by
      rw [Real.norm_eq_abs]; exact hK j y))
  obtain ⟨-, δ, hδ, hball⟩ := mem_intrinsicInterior_iff_exists_ball.1 hx
  set n : ℝ := (Fintype.card J : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set r : ℝ := δ / (4 * n) with hr
  have hr0 : 0 < r := by positivity
  set ρ : ℝ := δ / (8 * n * (‖x‖ + K + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  -- the compact set of unit directions of `dirSpan μ π S`
  set E : Set (J → ℝ) := (dirSpan μ π S : Set (J → ℝ)) ∩ Metric.sphere 0 1 with hE
  have hEc : IsCompact E := (isCompact_sphere (0 : J → ℝ) 1).inter_left
    (Submodule.closed_of_finiteDimensional _)
  rcases E.eq_empty_or_nonempty with hEe | hEne
  · refine ⟨1, one_pos, 1, one_pos, fun e heV he ↦ ?_⟩
    exact absurd (show e ∈ E from ⟨heV, mem_sphere_zero_iff_norm.2 he⟩) (by rw [hEe]; simp)
  have far : ∀ e ∈ E, ∃ y₀ ∈ essRange μ π S, δ / 2 ≤ dotJ e (x - y₀) :=
    fun e he ↦ exists_far_point_rel hδ hball he.1 (mem_sphere_zero_iff_norm.1 he.2)
  choose! y₀ hy₀ hfar using far
  have hcap : ∀ e ∈ E, ∀ e' ∈ Metric.ball e ρ, ∀ y,
      statPoint S y ∈ Metric.ball (y₀ e) r → δ / 8 ≤ dotJ e' (x - statPoint S y) := by
    intro e he e' he' y hy
    have hlin := isLinearMap_dotJ e
    have he1 : ‖e‖ = 1 := mem_sphere_zero_iff_norm.1 he.2
    have hee' : ‖e' - e‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at he'
    have hyr : ‖statPoint S y - y₀ e‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have h1 : δ / 4 ≤ dotJ e (x - statPoint S y) := by
      have e1 : dotJ e (x - statPoint S y) =
          dotJ e (x - y₀ e) - dotJ e (statPoint S y - y₀ e) := by
        rw [← hlin.map_sub]; congr 1; abel
      have h2 : |dotJ e (statPoint S y - y₀ e)| ≤ n * r := by
        refine (abs_dotJ_le _ _).trans ?_
        exact mul_le_mul (sum_abs_le_card_of_norm_le_one he1.le) hyr.le (norm_nonneg _) hnpos.le
      have h3 : n * r = δ / 4 := by rw [hr]; field_simp
      have := hfar e he
      rw [e1]
      have := abs_le.1 h2
      linarith
    have h4 : |dotJ (e' - e) (x - statPoint S y)| ≤ n * ρ * (‖x‖ + K) := by
      refine (abs_dotJ_le _ _).trans ?_
      have : ∑ j, |(e' - e) j| ≤ n * ρ := by
        calc ∑ j, |(e' - e) j| ≤ ∑ _j : J, ρ := Finset.sum_le_sum fun j _ ↦ by
              rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (e' - e) j).trans hee'.le
          _ = n * ρ := by simp [hn]
      exact mul_le_mul this (hSx y) (norm_nonneg _) (by positivity)
    have h5 : n * ρ * (‖x‖ + K) ≤ δ / 8 := by
      rw [hρ]
      have hpos : 0 < ‖x‖ + K + 1 := by positivity
      have e3 : n * (δ / (8 * n * (‖x‖ + K + 1))) * (‖x‖ + K) =
          δ / 8 * ((‖x‖ + K) / (‖x‖ + K + 1)) := by
        field_simp
      rw [e3]
      have : (‖x‖ + K) / (‖x‖ + K + 1) ≤ 1 := by
        rw [div_le_one hpos]; linarith
      nlinarith
    have e2 : dotJ e' (x - statPoint S y) =
        dotJ e (x - statPoint S y) + dotJ (e' - e) (x - statPoint S y) := by
      simp only [dotJ, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; ring
    have := abs_le.1 h4
    rw [e2]
    linarith
  obtain ⟨t, ht⟩ := hEc.elim_nhds_subcover' (fun e _ ↦ Metric.ball e ρ)
    fun e _ ↦ Metric.ball_mem_nhds e hρ0
  set mass : (J → ℝ) → ℝ := fun e ↦ ∫ y in statPoint S ⁻¹' Metric.ball (y₀ e) r, π y ∂μ
    with hmass
  have hmass_pos : ∀ e ∈ E, 0 < mass e := fun e he ↦
    setIntegral_pi_pos hπ hπi ((mem_essRange_iff hπm hπ hS).1 (hy₀ e he) r hr0)
  have htne : t.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨e₀, he₀⟩ := hEne
    have := ht he₀
    simp [hemp] at this
  refine ⟨δ / 8, by positivity, t.inf' htne (fun e ↦ mass (e : J → ℝ)), ?_, fun e' he'V he' ↦ ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun e _ ↦ hmass_pos (e : J → ℝ) e.2
  · obtain ⟨e, het, he'e⟩ : ∃ e ∈ t, e' ∈ Metric.ball (e : J → ℝ) ρ := by
      have := ht (show e' ∈ E from ⟨he'V, mem_sphere_zero_iff_norm.2 he'⟩)
      simpa using this
    calc t.inf' htne (fun e ↦ mass (e : J → ℝ)) ≤ mass (e : J → ℝ) := Finset.inf'_le _ het
      _ ≤ ∫ y in {y | δ / 8 ≤ dotJ e' (x - statPoint S y)}, π y ∂μ := by
          refine setIntegral_mono_set hπi.integrableOn
            (Filter.Eventually.of_forall fun y ↦ (hπ y).le)
            (Filter.Eventually.of_forall fun y hy ↦ hcap e e.2 e' he'e y hy)

omit [Nonempty X] [Nonempty J] in
/-- **Coercivity along `𝕍`**: `ψ(θ) + ⟨θ, x⟩ ≥ c ‖θ‖ + log m` for nonzero `θ ∈ 𝕍`. -/
theorem coercive_bound_rel {x : J → ℝ} {c m : ℝ} (hm : 0 < m)
    (hcap : ∀ e ∈ dirSpan μ π S, ‖e‖ = 1 →
      m ≤ ∫ y in {y | c ≤ dotJ e (x - statPoint S y)}, π y ∂μ)
    {θ : J → ℝ} (hθV : θ ∈ dirSpan μ π S) (hθ : θ ≠ 0) :
    c * ‖θ‖ + Real.log m ≤ affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x := by
  classical
  set e : J → ℝ := ‖θ‖⁻¹ • θ with he
  have he1 : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hθ)]
  have heV : e ∈ dirSpan μ π S := Submodule.smul_mem _ _ hθV
  have hpt : ∀ y ∈ {y | c ≤ dotJ e (x - statPoint S y)},
      c * ‖θ‖ - dotJ θ x ≤ -(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ y) := by
    intro y hy
    have hy' : c ≤ dotJ e (x - statPoint S y) := hy
    rw [one_mul, affLoss_zero_eq_dotJ]
    have e1 : dotJ θ (x - statPoint S y) = ‖θ‖ * dotJ e (x - statPoint S y) := by
      rw [he, dotJ_smul_left, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hθ), one_mul]
    have e2 : dotJ θ (x - statPoint S y) = dotJ θ x - dotJ θ (statPoint S y) :=
      (isLinearMap_dotJ θ).map_sub _ _
    have : c * ‖θ‖ ≤ dotJ θ (x - statPoint S y) := by
      rw [e1]
      exact mul_le_mul_of_nonneg_left hy' (norm_nonneg _) |>.trans_eq' (by ring)
    linarith
  have hA := measurable_cap hS e x c
  have hmass := hcap e heV he1
  have hZ : 0 < priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 :=
    affZ_pos hπm hπi hπ hπpos measurable_const (zero_bdd (X := X)) hS (t := 1) θ
  have hν : Integrable (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const (zero_bdd (X := X)) hS θ θ
      1).choose_spec.ν_int
  have hlow : Real.exp (c * ‖θ‖ - dotJ θ x) * m ≤ priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 := by
    calc Real.exp (c * ‖θ‖ - dotJ θ x) * m
        ≤ Real.exp (c * ‖θ‖ - dotJ θ x) * ∫ y in {y | c ≤ dotJ e (x - statPoint S y)}, π y ∂μ :=
          mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
      _ = ∫ y in {y | c ≤ dotJ e (x - statPoint S y)}, Real.exp (c * ‖θ‖ - dotJ θ x) * π y ∂μ := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ ∫ y in {y | c ≤ dotJ e (x - statPoint S y)},
            Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ y)) * π y ∂μ := by
          refine setIntegral_mono_on (hπi.const_mul _).integrableOn hν.integrableOn hA
            fun y hy ↦ ?_
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hpt y hy)) (hπ y).le
      _ ≤ priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 := by
          unfold priorZ
          exact setIntegral_le_integral hν
            (Filter.Eventually.of_forall fun y ↦ by have := hπ y; positivity)
  have := Real.log_le_log (by positivity) hlow
  rw [Real.log_mul (Real.exp_pos _).ne' hm.ne', Real.log_exp] at this
  unfold affLogZ
  linarith

/-- **Existence of a minimiser on `𝕍`** for the variational functional of a relative-interior
point. -/
theorem exists_min_variational_rel {x : J → ℝ}
    (hx : x ∈ intrinsicInterior ℝ (momentBody μ π S)) :
    ∃ θ₀ ∈ dirSpan μ π S, ∀ θ ∈ dirSpan μ π S,
      affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ + dotJ θ₀ x ≤
        affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x := by
  obtain ⟨c, hc, m, hm, hcap⟩ := cap_lemma_rel hπm hπi hπ hS hx
  obtain ⟨f, hfdef⟩ : ∃ f : dirSpan μ π S → ℝ, f = fun θ : dirSpan μ π S ↦
      affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 (θ : J → ℝ) + dotJ (θ : J → ℝ) x := ⟨_, rfl⟩
  have hf : Continuous f := by
    rw [hfdef]
    exact ((continuous_affLogZ_general hπm hπi hπ hπpos hS).add (continuous_dotJ_left x)).comp
      continuous_subtype_val
  have hcoer : ∀ᶠ θ in cocompact (dirSpan μ π S), f 0 ≤ f θ := by
    have hnorm : Tendsto (fun θ : dirSpan μ π S ↦ ‖θ‖) (cocompact (dirSpan μ π S)) atTop :=
      tendsto_norm_cocompact_atTop
    filter_upwards [hnorm.eventually (eventually_ge_atTop ((f 0 - Real.log m) / c + 1))]
      with θ hθ
    by_cases h0 : θ = 0
    · rw [h0]
    · have hθ' : (θ : J → ℝ) ≠ 0 := fun h ↦ h0 (Subtype.ext h)
      have hb := coercive_bound_rel hπm hπi hπ hπpos hS hm hcap θ.2 hθ'
      have h1 : (f 0 - Real.log m) / c ≤ ‖θ‖ := by linarith
      rw [div_le_iff₀ hc] at h1
      have hn : ‖(θ : J → ℝ)‖ = ‖θ‖ := rfl
      rw [hn] at hb
      simp only [hfdef] at h1 ⊢
      linarith
  obtain ⟨θ₀, hθ₀⟩ := hf.exists_forall_le' 0 hcoer
  refine ⟨θ₀, θ₀.2, fun θ hθ ↦ ?_⟩
  have := hθ₀ ⟨θ, hθ⟩
  rw [hfdef] at this
  exact this

omit [Nonempty J] in
/-- **The first-order condition on `𝕍` determines the mean**: a minimiser `θ₀ ∈ 𝕍` of the
variational functional of `x ∈ K` has `m(θ₀) = x`. -/
theorem meanMap_eq_of_min_rel {x θ₀ : J → ℝ} (hx : x ∈ momentBody μ π S)
    (hθ₀ : θ₀ ∈ dirSpan μ π S)
    (hmin : ∀ θ ∈ dirSpan μ π S, affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ + dotJ θ₀ x ≤
      affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x) :
    meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ = x := by
  classical
  obtain ⟨hLm, ML, hLb⟩ := bdd_affLoss (L₀ := fun _ : X ↦ (0 : ℝ)) measurable_const
    (zero_bdd (X := X)) hS θ₀
  have hT : TiltData μ (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) 1) (fun _ ↦ 0) 0 :=
    tiltData_baseWeight_of_bounded μ hπm hπi (fun x ↦ (hπ x).le) hπpos hLm hLb measurable_const
      (fun _ ↦ by simp) 1
  have hder : ∀ e ∈ dirSpan μ π S,
      dotJ e x = dotJ e (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀) := by
    intro e heV
    have hψ := hT.hasDerivAt_affLogZ_dir' hS e
    have hd : HasDerivAt (fun ε : ℝ ↦ dotJ (θ₀ + ε • e) x) (dotJ e x) 0 := by
      have e' : (fun ε : ℝ ↦ dotJ (θ₀ + ε • e) x) = fun ε ↦ dotJ θ₀ x + ε * dotJ e x := by
        funext ε; rw [dotJ_add_left, dotJ_smul_left]
      rw [e']
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotJ e x)).const_add (dotJ θ₀ x)
    have hsum := hψ.add hd
    have hloc : IsLocalMin (fun ε : ℝ ↦ affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 (θ₀ + ε • e) +
        dotJ (θ₀ + ε • e) x) 0 := by
      refine Filter.Eventually.of_forall fun ε ↦ ?_
      simp only [zero_smul, add_zero]
      exact hmin _ (Submodule.add_mem _ hθ₀ (Submodule.smul_mem _ ε heV))
    have h0 := hloc.hasDerivAt_eq_zero hsum
    simp only [neg_mul, one_mul] at h0
    have e0 : dotJ e (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀) =
        ∑ i, e i * meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ i := rfl
    rw [e0]
    linarith
  have hmK := mean_mem_momentBody hπm hπi hπ hπpos hS θ₀
  have hdV : x - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ ∈ dirSpan μ π S := by
    have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hmK)
    simpa [vsub_eq_sub] using this
  have hdd : dotJ (x - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀)
      (x - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀) = 0 := by
    rw [(isLinearMap_dotJ _).map_sub, hder _ hdV, sub_self]
  have hzero : ∀ j, (x - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀) j = 0 := fun j ↦
    mul_self_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_self_nonneg _).1 hdd j
      (Finset.mem_univ j))
  have : x - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ = 0 := funext hzero
  exact (sub_eq_zero.1 this).symm

/-- **The relative-interior moment-body theorem**: with no nondegeneracy hypothesis, the image of
the mean map is the relative interior of the moment body. -/
theorem range_meanMap_eq_intrinsicInterior_momentBody :
    Set.range (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1) = intrinsicInterior ℝ (momentBody μ π S) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  refine Set.Subset.antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨θ, rfl⟩
    rw [mem_intrinsicInterior_iff_forall_supporting (convex_momentBody S)]
    refine ⟨mean_mem_momentBody hπm hπi hπ hπpos hS θ, fun e he ↦ ?_⟩
    set m := meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ with hm
    have hP := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos measurable_const h0 hS
      (t := 1) θ
    have hac : familyMeasure μ π (fun _ ↦ (0 : ℝ)) S 1 θ ≪ μ := withDensity_absolutelyContinuous _ _
    -- the a.e. bound `e·S ≤ e·m`
    have hae : ∀ᵐ y ∂μ, dirLoss S e y ≤ dotJ e m := by
      filter_upwards [ae_statPoint_mem_essRange hπm hπ hS] with y hy
      exact he _ (essRange_subset_momentBody S hy)
    -- the expectation of `e·S` under `P_θ` is `e·m`
    have hν : Integrable (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1) μ :=
      (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const (zero_bdd (X := X)) hS θ θ
        1).choose_spec.ν_int
    have hint : ∫ y, dirLoss S e y ∂familyMeasure μ π (fun _ ↦ (0 : ℝ)) S 1 θ = dotJ e m := by
      rw [integral_familyMeasure hπm hπi hπ hπpos measurable_const h0 hS θ,
        priorExp_dirLoss hν hS e]
      rfl
    -- hence `e·S = e·m` a.e.
    have hg : Bdd fun y ↦ dotJ e m - dirLoss S e y := (Bdd.const _).sub (bdd_dirLoss hS e)
    have hzero : (fun y ↦ dotJ e m - dirLoss S e y) =ᵐ[familyMeasure μ π (fun _ ↦ (0 : ℝ)) S 1 θ]
        0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae ?_ (integrable_of_bdd_prob _ hg)).1 ?_
      · filter_upwards [hac.ae_le hae] with y hy
        simp only [Pi.zero_apply]
        linarith
      · rw [integral_sub (integrable_const _) (integrable_of_bdd_prob _ (bdd_dirLoss hS e)), hint,
          integral_const]
        simp
    have hμ : ∀ᵐ y ∂μ, dirLoss S e y = dotJ e m := by
      have hP' : ∀ᵐ y ∂familyMeasure μ π (fun _ ↦ (0 : ℝ)) S 1 θ, dirLoss S e y = dotJ e m := by
        filter_upwards [hzero] with y hy
        simp only [Pi.zero_apply] at hy
        linarith
      rw [ae_iff] at hP' ⊢
      exact (familyMeasure_eq_zero_iff hπm hπi hπ hπpos measurable_const h0 hS (t := 1) θ).1 hP'
    -- so the moment body lies in the hyperplane `e·y = e·m`
    have hle : momentBody μ π S ⊆ {y | dotJ e y ≤ dotJ e m} :=
      momentBody_subset_halfspace hπm hπ hS (hμ.mono fun y hy ↦ hy.le)
    have hge : momentBody μ π S ⊆ {y | dotJ (-e) y ≤ -dotJ e m} := by
      refine momentBody_subset_halfspace hπm hπ hS ?_
      filter_upwards [hμ] with y hy
      rw [show -e = (-1 : ℝ) • e by rw [neg_one_smul], dirLoss_smul]
      change (-1 : ℝ) * dirLoss S e y ≤ -dotJ e m
      rw [hy]
      linarith
    intro y hy
    have h1 := hle hy
    have h2 := hge hy
    simp only [Set.mem_ofPred_eq, dotJ_neg_left] at h1 h2
    linarith
  · obtain ⟨θ₀, hθ₀V, hmin⟩ := exists_min_variational_rel hπm hπi hπ hπpos hS hx
    exact ⟨θ₀, meanMap_eq_of_min_rel hπm hπi hπ hπpos hS (intrinsicInterior_subset hx) hθ₀V hmin⟩

end

end Laplace.Multi
