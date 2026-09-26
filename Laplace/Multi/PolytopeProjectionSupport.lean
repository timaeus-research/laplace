/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolytopeMinimalFace
import Laplace.Multi.PolyhedralCompletion

/-!
# The response projection on a charged polytope: support, face law, density bound

On a charged polytope (`momentBody ν 1 S = conv V`, every vertex fibre of positive mass) the
minimal-face theorem of `PolytopeMinimalFace` exposes every `M ∈ conv V` by a functional `u` whose
face fibre `{⟨u,S⟩ = β}` has positive mass and contains `M` in the relative interior of its face.
Consequences for the response projection `q_M`:

* every `q_M` is the total-variation limit of an explicit natural ray
  (`exists_ray_tendsto_responseProjection_of_mem_polytope`);
* `q_M` is carried by the face fibre (`responseProjection_compl_faceFibre_eq_zero`, the essential
  support) and equals the response projection of the conditioned law
  (`responseProjection_eq_faceMeasure_of_mem_polytope`);
* the density `dq_M/dν` is bounded by `1/m` whenever every vertex fibre has mass at least `m`
  (`ae_projDens_le_of_mem_polytope`): the face density `e^{−⟨θ,S⟩}/Z_F` attains its supremum on a
  vertex of the face, and the normaliser contains that vertex fibre;
* hence `L^p` continuity of the completed family for every finite `p`
  (`tendsto_integral_abs_projDens_sub_pow`), from the `L¹` continuity of
  `PolyhedralCompletion`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Fibre

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] {S : J → X → ℝ}

omit [MeasurableSpace X] in
theorem dirLoss_eq_dotJ_statPoint (θ : J → ℝ) (x : X) :
    dirLoss S θ x = dotJ θ (statPoint S x) := rfl

omit [MeasurableSpace X] in
theorem statFibre_subset_faceFibre {u : J → ℝ} {β : ℝ} {v : J → ℝ} (hv : dotJ u v = β) :
    statFibre S v ⊆ {x | dirLoss S u x = β} := by
  intro x hx
  have hx' : statPoint S x = v := hx
  change dirLoss S u x = β
  rw [dirLoss_eq_dotJ_statPoint, hx', hv]

omit [MeasurableSpace X] in
theorem famWeight_eq_of_mem_statFibre (θ : J → ℝ) {v : J → ℝ} {x : X}
    (hx : x ∈ statFibre S v) : famWeight S θ x = Real.exp (-dotJ θ v) := by
  have hx' : statPoint S x = v := hx
  rw [famWeight, dirLoss_eq_dotJ_statPoint, hx']

end Fibre

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ))
include hS

omit [Nonempty X] [Nonempty J] hS in
/-- A tight charged vertex makes the face fibre charged. -/
theorem faceFibre_pos_of_charged (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {u : J → ℝ}
    {β : ℝ} {v : J → ℝ} (hvV : v ∈ V) (hv : dotJ u v = β) :
    0 < ν.real {x | dirLoss S u x = β} :=
  lt_of_lt_of_le (hcharged v hvV) (measureReal_mono (statFibre_subset_faceFibre hv))

omit [MeasurableSpace X] [Nonempty X] hS [IsProbabilityMeasure ν] in
theorem exists_charged_vertex [Nonempty V] {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) : ∃ v : V, 0 < vertexSection V M v := by
  have hpos : ∑ v : V, (0 : ℝ) < ∑ v : V, vertexSection V M v := by
    rw [(vertexSection_mem_stdSimplex V hM).2]
    simp
  obtain ⟨v, -, hv⟩ := Finset.exists_lt_of_sum_lt hpos
  exact ⟨v, hv⟩

omit [Nonempty X] hS in
/-- **Every point of a charged polytope is exposed with a charged face fibre.** -/
theorem exists_exposing_polytope [Nonempty V] (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ∃ u : J → ℝ, ∃ β : ℝ, (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u M = β ∧ (∃ v ∈ V, dotJ u v = β) ∧
      0 < ν.real {x | dirLoss S u x = β} ∧
      M ∈ intrinsicInterior ℝ
        (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))) ∧
      minimalFacePoly V M =
        convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) := by
  obtain ⟨u, β, hV, hMβ, hvert, hF⟩ := exists_exposing_minimalFacePoly hM
  obtain ⟨v, hv⟩ := exists_charged_vertex V hM
  refine ⟨u, β, hV, hMβ, ⟨v, v.2, (hvert v).2 hv⟩,
    faceFibre_pos_of_charged ν V hcharged v.2 ((hvert v).2 hv), ?_, hF⟩
  rw [← hF]
  exact mem_intrinsicInterior_minimalFacePoly hM

/-- **Every response projection on a charged polytope is the total-variation limit of a natural
ray.** -/
theorem exists_ray_tendsto_responseProjection_of_mem_polytope [Nonempty V]
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ∃ u : J → ℝ, ∃ β : ℝ, ∃ θ : J → ℝ, (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u M = β ∧
      0 < ν.real {x | dirLoss S u x = β} ∧
      responseProjection hS ν M = ν.withDensity (fun x ↦ ENNReal.ofReal (faceDens S ν θ u β x)) ∧
      (∀ t, ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν =
        2 * offFaceMass S ν θ u β t / (faceMass S ν θ u β + offFaceMass S ν θ u β t)) ∧
      Tendsto (fun t : ℝ ↦ ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν) atTop
        (𝓝 0) := by
  obtain ⟨u, β, hV, hMβ, -, hp, hrel, -⟩ := exists_exposing_polytope ν V hcharged hM
  obtain ⟨θ, hθ⟩ :=
    exists_ray_tendsto_responseProjection_polytope hS ν V u β hpoly hcharged hV hp hMβ hrel
  exact ⟨u, β, θ, hV, hMβ, hp, hθ⟩

/-- **Essential support**: the response projection is carried by the face fibre of any exposing
functional. -/
theorem responseProjection_compl_faceFibre_eq_zero
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {u : J → ℝ} {β : ℝ}
    (hV : ∀ v ∈ V, dotJ u v ≤ β) {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u M = β) :
    responseProjection hS ν M {x | dirLoss S u x = β}ᶜ = 0 := by
  have hfin := genRate_ne_top_of_mem_momentBody_polytope hS ν V hcharged hpoly (hpoly ▸ hM)
  have hspec := responseProjection_spec hS ν hfin
  have := hspec.1
  have hac : responseProjection hS ν M ≪ ν := by
    rw [responseProjection_eq_withDensity_projDens hS ν hfin]
    exact withDensity_absolutelyContinuous _ _
  exact compl_eq_zero_of_mean_face ν hS _ hac (ae_dirLoss_le_of_polytope hS ν V u β hpoly hV)
    (by rw [hspec.2.1]; exact hMβ)

/-- **The projection is the projection of the conditioned law on the exposed face.** -/
theorem responseProjection_eq_faceMeasure_of_exposed
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {u : J → ℝ} {β : ℝ}
    (hV : ∀ v ∈ V, dotJ u v ≤ β) (hp : 0 < ν.real {x | dirLoss S u x = β}) {M : J → ℝ}
    (hMβ : dotJ u M = β)
    (hrel : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))) :
    responseProjection hS ν M =
      responseProjection hS (faceMeasure ν {x | dirLoss S u x = β}) M := by
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  refine responseProjection_faceMeasure hS ν (ae_dirLoss_le_of_polytope hS ν V u β hpoly hV) hp
    hMβ (genRate_ne_top_of_mem_intrinsicInterior hS _ ?_)
  rwa [momentBody_faceMeasure_eq_of_exposed hS ν V u β hpoly hcharged hV hp]

/-- Every response projection on a charged polytope is the projection of a conditioned law. -/
theorem responseProjection_eq_faceMeasure_of_mem_polytope [Nonempty V]
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ∃ u : J → ℝ, ∃ β : ℝ, (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u M = β ∧
      0 < ν.real {x | dirLoss S u x = β} ∧
      responseProjection hS ν M {x | dirLoss S u x = β}ᶜ = 0 ∧
      responseProjection hS ν M =
        responseProjection hS (faceMeasure ν {x | dirLoss S u x = β}) M := by
  obtain ⟨u, β, hV, hMβ, -, hp, hrel, -⟩ := exists_exposing_polytope ν V hcharged hM
  exact ⟨u, β, hV, hMβ, hp, responseProjection_compl_faceFibre_eq_zero hS ν V hpoly hcharged hV hM
    hMβ, responseProjection_eq_faceMeasure_of_exposed hS ν V hpoly hcharged hV hp hMβ hrel⟩

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- On the face fibre the statistic lies a.e. in the tight hull. -/
theorem ae_statPoint_mem_tightHull
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ))) {u : J → ℝ}
    {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) :
    ∀ᵐ x ∂ν, dirLoss S u x = β →
      statPoint S x ∈
        convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) := by
  filter_upwards [ae_statPoint_mem_essRange (μ := ν) measurable_const (fun _ ↦ one_pos) hS]
    with x hx hxβ
  have hmem : statPoint S x ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := essRange_subset_momentBody S hx
  rw [hpoly] at hmem
  rw [← convexHull_inter_hyperplane V u β hV]
  exact ⟨hmem, by rwa [mem_ofPred_eq, ← dirLoss_eq_dotJ_statPoint]⟩

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem measurable_faceDens (θ u : J → ℝ) (β : ℝ) : Measurable (faceDens S ν θ u β) := by
  have hw : Measurable (famWeight S θ) := Real.measurable_exp.comp (bdd_dirLoss hS θ).1.neg
  exact (hw.div_const _).indicator (measurableSet_faceFibre hS u β)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem faceDens_nonneg (θ u : J → ℝ) (β : ℝ) (x : X) : 0 ≤ faceDens S ν θ u β x :=
  Set.indicator_nonneg (fun x _ ↦ div_nonneg (famWeight_pos θ x).le
    (integral_nonneg fun x ↦ (famWeight_pos θ x).le)) x

omit [Nonempty X] [Nonempty J] in
/-- **The face density is bounded by the reciprocal of the smallest vertex mass**: the exponential
weight attains its supremum over the face at a tight vertex, whose fibre lies in the normaliser. -/
theorem ae_faceDens_le
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ))) {u : J → ℝ}
    {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ v ∈ V, m ≤ ν.real (statFibre S v)) {v₀ : J → ℝ} (hv₀ : v₀ ∈ V) (hv₀β : dotJ u v₀ = β)
    (θ : J → ℝ) : ∀ᵐ x ∂ν, faceDens S ν θ u β x ≤ 1 / m := by
  have hTne : (V.filter fun v ↦ dotJ u v = β).Nonempty := ⟨v₀, Finset.mem_filter.2 ⟨hv₀, hv₀β⟩⟩
  obtain ⟨w, hwT, hwmin⟩ := Finset.exists_min_image _ (fun v ↦ dotJ θ v) hTne
  obtain ⟨hwV, hwβ⟩ := Finset.mem_filter.1 hwT
  have hmass : Real.exp (-dotJ θ w) * m ≤ faceMass S ν θ u β := by
    have h1 : ∫ x in statFibre S w, famWeight S θ x ∂ν =
        Real.exp (-dotJ θ w) * ν.real (statFibre S w) := by
      rw [setIntegral_congr_fun (measurableSet_statFibre hS w)
        (fun x hx ↦ famWeight_eq_of_mem_statFibre θ hx), setIntegral_const, smul_eq_mul, mul_comm]
    have h2 : ∫ x in statFibre S w, famWeight S θ x ∂ν ≤ faceMass S ν θ u β :=
      setIntegral_mono_set (integrable_famWeight hS ν θ).integrableOn
        (Eventually.of_forall fun x ↦ (famWeight_pos θ x).le)
        (Eventually.of_forall (statFibre_subset_faceFibre hwβ))
    calc Real.exp (-dotJ θ w) * m ≤ Real.exp (-dotJ θ w) * ν.real (statFibre S w) :=
          mul_le_mul_of_nonneg_left (hm w hwV) (Real.exp_pos _).le
      _ = _ := h1.symm
      _ ≤ _ := h2
  filter_upwards [ae_statPoint_mem_tightHull hS ν V hpoly hV] with x hx
  unfold faceDens
  by_cases hxF : dirLoss S u x = β
  · rw [Set.indicator_of_mem (show x ∈ {x | dirLoss S u x = β} from hxF)]
    have hlow : dotJ θ w ≤ dotJ θ (statPoint S x) := by
      have hconv : convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) ⊆
          {y | dotJ ((-1 : ℝ) • θ) y ≤ -dotJ θ w} := by
        refine convexHull_min (fun v hv ↦ ?_) (convex_halfspace_dotJ _ _)
        rw [mem_ofPred_eq, dotJ_smul_left, neg_one_mul, neg_le_neg_iff]
        exact hwmin v (Finset.mem_coe.1 hv)
      have := hconv (hx hxF)
      rw [mem_ofPred_eq, dotJ_smul_left, neg_one_mul, neg_le_neg_iff] at this
      exact this
    have hw' : famWeight S θ x ≤ Real.exp (-dotJ θ w) := by
      rw [famWeight, dirLoss_eq_dotJ_statPoint]
      exact Real.exp_le_exp.2 (neg_le_neg hlow)
    calc famWeight S θ x / faceMass S ν θ u β
        ≤ Real.exp (-dotJ θ w) / (Real.exp (-dotJ θ w) * m) :=
          div_le_div₀ (Real.exp_pos _).le hw' (mul_pos (Real.exp_pos _) hm0) hmass
      _ = 1 / m := by rw [div_mul_eq_div_div, div_self (Real.exp_pos _).ne']
  · rw [Set.indicator_of_notMem (show x ∉ {x | dirLoss S u x = β} from hxF)]
    exact (one_div_pos.2 hm0).le

/-- **Uniform density bound on a charged polytope**: `dq_M/dν ≤ 1/m` for every `M`, when every
vertex fibre has mass at least `m`. -/
theorem ae_projDens_le_of_mem_polytope [Nonempty V]
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ v ∈ V, m ≤ ν.real (statFibre S v)) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) : ∀ᵐ x ∂ν, projDens hS ν M x ≤ 1 / m := by
  obtain ⟨u, β, hV, hMβ, ⟨v₀, hv₀V, hv₀β⟩, hp, hrel, -⟩ := exists_exposing_polytope ν V hcharged hM
  obtain ⟨θ, hq, -, -⟩ :=
    exists_ray_tendsto_responseProjection_polytope hS ν V u β hpoly hcharged hV hp hMβ hrel
  have hae := projDens_ae_eq hS ν (measurable_faceDens hS ν θ u β) (faceDens_nonneg ν θ u β) hq
  filter_upwards [hae, ae_faceDens_le hS ν V hpoly hV hm0 hm hv₀V hv₀β θ] with x h1 h2
  rw [h1]
  exact h2

/-- The completed family of a charged polytope has uniformly bounded densities. -/
theorem exists_uniform_projDens_bound [Nonempty V]
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)), ∀ᵐ x ∂ν, projDens hS ν M x ≤ C := by
  have hVne : V.Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨v, v.2⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = V.inf' hVne fun v ↦ ν.real (statFibre S v) := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    rw [hmdef, Finset.lt_inf'_iff hVne]
    exact hcharged
  have hm : ∀ v ∈ V, m ≤ ν.real (statFibre S v) := fun v hv ↦ by
    rw [hmdef]
    exact Finset.inf'_le _ hv
  exact ⟨1 / m, one_div_pos.2 hm0, fun M hM ↦
    ae_projDens_le_of_mem_polytope hS ν V hpoly hcharged hm0 hm hM⟩

/-- Bounded densities: a power of the `L¹` difference is dominated by the difference. -/
theorem integral_abs_projDens_sub_pow_le {C : ℝ} {M N : J → ℝ}
    (hM : ∀ᵐ x ∂ν, projDens hS ν M x ≤ C) (hN : ∀ᵐ x ∂ν, projDens hS ν N x ≤ C) (p : ℕ) :
    ∫ x, |projDens hS ν M x - projDens hS ν N x| ^ (p + 1) ∂ν ≤
      C ^ p * ∫ x, |projDens hS ν M x - projDens hS ν N x| ∂ν := by
  have hint : Integrable (fun x ↦ |projDens hS ν M x - projDens hS ν N x|) ν :=
    ((integrable_projDens hS ν M).sub (integrable_projDens hS ν N)).abs
  have hbound : ∀ᵐ x ∂ν, |projDens hS ν M x - projDens hS ν N x| ^ (p + 1) ≤
      C ^ p * |projDens hS ν M x - projDens hS ν N x| := by
    filter_upwards [hM, hN] with x h1 h2
    have h0M := projDens_nonneg hS ν M x
    have h0N := projDens_nonneg hS ν N x
    have habs : |projDens hS ν M x - projDens hS ν N x| ≤ C := by
      rw [abs_le]
      constructor <;> linarith
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) habs p) (abs_nonneg _)
  rw [← integral_const_mul]
  refine integral_mono_ae ?_ (hint.const_mul _) hbound
  refine Integrable.mono' (hint.const_mul (C ^ p)) ?_ ?_
  · exact (((measurable_projDens hS ν M).sub (measurable_projDens hS ν N)).abs.pow_const
      (p + 1)).aestronglyMeasurable
  · filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hx

/-- **`L^p` continuity of the completed family** on a charged polytope, for every finite `p`. -/
theorem tendsto_integral_abs_projDens_sub_pow [Nonempty V]
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) {Ms : ℕ → J → ℝ}
    (hMs : ∀ n, Ms n ∈ convexHull ℝ (V : Set (J → ℝ))) (hlim : Tendsto Ms atTop (𝓝 M)) (p : ℕ) :
    Tendsto (fun n ↦ ∫ x, |projDens hS ν (Ms n) x - projDens hS ν M x| ^ (p + 1) ∂ν) atTop
      (𝓝 0) := by
  obtain ⟨C, -, hbdd⟩ := exists_uniform_projDens_bound hS ν V hpoly hcharged
  have hL1 : Tendsto (fun n ↦ ∫ x, |projDens hS ν (Ms n) x - projDens hS ν M x| ∂ν) atTop
      (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.1
      (tendsto_projL1_of_tendsto hS ν V hcharged hM hMs hlim)
    simpa only [norm_projL1_sub] using this
  refine squeeze_zero (fun n ↦ integral_nonneg fun x ↦ by positivity)
    (fun n ↦ integral_abs_projDens_sub_pow_le hS ν (hbdd _ (hMs n)) (hbdd M hM) p) ?_
  simpa using hL1.const_mul (C ^ p)

end Face

end Laplace.Multi
