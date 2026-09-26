/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolyhedralRecovery

/-!
# Polyhedral completion V: the completed family in `L¹(ν)`

On a charged polytope the map `M ↦ dq_M/dν ∈ L¹(ν)` (`projL1`) is **continuous on the whole
closed moment body** (`continuousOn_projL1_polytope`): the recovery laws `g_n` of the previous
module satisfy `KL(g_n ν ‖ q_{M_n}) = KL(g_n ν ‖ ν) − 𝓘(M_n) → 0` by Pythagoras, so Pinsker in
`L¹` form (`integral_abs_sub_le_sqrt_klDiv`) gives `‖g_n − q_{M_n}‖₁ → 0`, while
`‖g_n − q_M‖₁ ≤ ε_n → 0`.
Consequently the completed family `projL1 '' P` is compact, homeomorphic to the polytope through the
mean map (`completedHomeomorphL1`), and is the closure of the interior exponential family
(`closure_image_intrinsicInterior`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Pinsker

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]

omit [Nonempty X] [IsProbabilityMeasure ν] in
/-- The measure of a set under a bounded density. -/
theorem measureReal_withDensity_ofReal {p : X → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hpi : Integrable p ν)
    {A : Set X} (hA : MeasurableSet A) :
    (ν.withDensity fun x ↦ ENNReal.ofReal (p x)).real A = ∫ x in A, p x ∂ν := by
  rw [measureReal_def, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hpi.integrableOn (Eventually.of_forall hp0),
    ENNReal.toReal_ofReal (setIntegral_nonneg hA fun x _ ↦ hp0 x)]

omit [IsProbabilityMeasure ν] in
/-- **Pinsker in `L¹` form**: `(∫ |p − q|)² / 2 ≤ KL(pν ‖ qν)` for probability densities. -/
theorem ofReal_sq_integral_abs_sub_le_klDiv {p q : X → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hpi : Integrable p ν) (hqi : Integrable q ν)
    (hP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (p x)))
    (hQ : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (q x))) :
    ENNReal.ofReal ((∫ x, |p x - q x| ∂ν) ^ 2 / 2) ≤
      klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (p x))
        (ν.withDensity fun x ↦ ENNReal.ofReal (q x)) := by
  have hA : MeasurableSet {x | q x ≤ p x} := measurableSet_le hq hp
  have hp1 := integral_eq_one_of_isProbabilityMeasure_withDensity ν hp0 hpi hP
  have hq1 := integral_eq_one_of_isProbabilityMeasure_withDensity ν hq0 hqi hQ
  have hsub : Integrable (fun x ↦ p x - q x) ν := hpi.sub hqi
  -- the two halves of the total variation agree
  have hhalf : ∫ x in {x | q x ≤ p x}ᶜ, (p x - q x) ∂ν =
      -∫ x in {x | q x ≤ p x}, (p x - q x) ∂ν := by
    have := integral_add_compl₀ hA.nullMeasurableSet hsub
    rw [integral_sub hpi hqi, hp1, hq1, sub_self] at this
    linarith
  have hI : ∫ x, |p x - q x| ∂ν = 2 * ∫ x in {x | q x ≤ p x}, (p x - q x) ∂ν := by
    rw [← integral_add_compl₀ hA.nullMeasurableSet hsub.abs]
    have e1 : ∫ x in {x | q x ≤ p x}, |p x - q x| ∂ν = ∫ x in {x | q x ≤ p x}, (p x - q x) ∂ν :=
      setIntegral_congr_fun hA fun x hx ↦ abs_of_nonneg (sub_nonneg.2 hx)
    have e2 : ∫ x in {x | q x ≤ p x}ᶜ, |p x - q x| ∂ν =
        -∫ x in {x | q x ≤ p x}ᶜ, (p x - q x) ∂ν := by
      rw [← integral_neg]
      refine setIntegral_congr_fun hA.compl fun x hx ↦ ?_
      have hx' : p x < q x := lt_of_not_ge hx
      rw [abs_of_neg (by linarith)]
    rw [e1, e2, hhalf]
    ring
  have hpin := pinsker_event (ν.withDensity fun x ↦ ENNReal.ofReal (p x))
    (ν.withDensity fun x ↦ ENNReal.ofReal (q x)) hA
  rw [measureReal_withDensity_ofReal ν hp0 hpi hA, measureReal_withDensity_ofReal ν hq0 hqi hA,
    ← integral_sub hpi.integrableOn hqi.integrableOn] at hpin
  refine le_trans (le_of_eq ?_) hpin
  rw [hI]
  congr 1
  ring

omit [IsProbabilityMeasure ν] in
/-- **Pinsker in `L¹` form, real version**: `∫ |p − q| ≤ √(2 KL(pν ‖ qν))` when the entropy is
finite. -/
theorem integral_abs_sub_le_sqrt_klDiv {p q : X → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hpi : Integrable p ν) (hqi : Integrable q ν)
    (hP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (p x)))
    (hQ : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (q x)))
    (hkl : klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (p x))
      (ν.withDensity fun x ↦ ENNReal.ofReal (q x)) ≠ ⊤) :
    ∫ x, |p x - q x| ∂ν ≤ √(2 * (klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (p x))
      (ν.withDensity fun x ↦ ENNReal.ofReal (q x))).toReal) := by
  have h := (ENNReal.ofReal_le_iff_le_toReal hkl).1
    (ofReal_sq_integral_abs_sub_le_klDiv ν hp hq hp0 hq0 hpi hqi hP hQ)
  exact Real.le_sqrt_of_sq_le (by linarith)

end Pinsker

section ProjL1

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

instance isFiniteMeasure_responseProjection (M : J → ℝ) :
    IsFiniteMeasure (responseProjection hS ν M) := by
  by_cases hfin : genRate ν S M ≠ ⊤
  · have := (responseProjection_spec hS ν hfin).1
    infer_instance
  · rw [responseProjection, dif_neg fun h ↦ hfin h.2]
    infer_instance

/-- The density `dq_M/dν` of the response projection, as a real function. -/
noncomputable def projDens (M : J → ℝ) (x : X) : ℝ :=
  ((responseProjection hS ν M).rnDeriv ν x).toReal

omit [IsProbabilityMeasure ν] in
theorem measurable_projDens (M : J → ℝ) : Measurable (projDens hS ν M) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

omit [IsProbabilityMeasure ν] in
theorem projDens_nonneg (M : J → ℝ) (x : X) : 0 ≤ projDens hS ν M x := ENNReal.toReal_nonneg

theorem integrable_projDens (M : J → ℝ) : Integrable (projDens hS ν M) ν :=
  Measure.integrable_toReal_rnDeriv

/-- **The response projection as an element of `L¹(ν)`.** -/
noncomputable def projL1 (M : J → ℝ) : X →₁[ν] ℝ := (integrable_projDens hS ν M).toL1 _

theorem responseProjection_eq_withDensity_projDens {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    responseProjection hS ν M = ν.withDensity fun x ↦ ENNReal.ofReal (projDens hS ν M x) := by
  have hP := (responseProjection_spec hS ν hfin).1
  have hac : responseProjection hS ν M ≪ ν := (klDiv_ne_top_iff.1 (by
    rw [(responseProjection_spec hS ν hfin).2.2.1]
    exact hfin)).1
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hac]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_ne_top (responseProjection hS ν M) ν] with x hx
  rw [projDens, ENNReal.ofReal_toReal hx]

theorem isProbabilityMeasure_withDensity_projDens {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (projDens hS ν M x)) :=
  responseProjection_eq_withDensity_projDens hS ν hfin ▸ (responseProjection_spec hS ν hfin).1

/-- Any representative of `dq_M/dν` agrees a.e. with `projDens`. -/
theorem projDens_ae_eq {M : J → ℝ} {f : X → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf : responseProjection hS ν M = ν.withDensity fun x ↦ ENNReal.ofReal (f x)) :
    projDens hS ν M =ᵐ[ν] f := by
  have h := Measure.rnDeriv_withDensity ν hfm.ennreal_ofReal
  rw [← hf] at h
  filter_upwards [h] with x hx
  rw [projDens, show (responseProjection hS ν M).rnDeriv ν x = ENNReal.ofReal (f x) from hx,
    ENNReal.toReal_ofReal (hf0 x)]

theorem integral_stat_mul_projDens {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) (j : J) :
    ∫ x, S j x * projDens hS ν M x ∂ν = M j := by
  have := congrFun (responseProjection_spec hS ν hfin).2.1 j
  rw [responseProjection_eq_withDensity_projDens hS ν hfin,
    integral_withDensity_ofReal ν (measurable_projDens hS ν M) (projDens_nonneg hS ν M)] at this
  rw [← this]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)

theorem norm_projL1_sub (M M' : J → ℝ) :
    ‖projL1 hS ν M - projL1 hS ν M'‖ = ∫ x, |projDens hS ν M x - projDens hS ν M' x| ∂ν := by
  unfold projL1
  rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
  simp only [Pi.sub_apply, Real.norm_eq_abs]

end ProjL1

section Continuity

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V] (hV : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hV

/-- **`L¹` continuity of the completed family along sequences in the polytope.** -/
theorem tendsto_projL1_of_tendsto {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    {m : ℕ → J → ℝ} (hm : ∀ n, m n ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hlim : Tendsto m atTop (𝓝 M)) :
    Tendsto (fun n ↦ projL1 hS ν (m n)) atTop (𝓝 (projL1 hS ν M)) := by
  obtain ⟨f, g, C, ε, hfm, hf0, hfC, hf, hgm, hg1, hgmean, hgf, hε, hgnn, hKL⟩ :=
    exists_recovery hS ν V hV hM hm hlim
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hV hM
  have hfinn : ∀ n, genRate ν S (m n) ≠ ⊤ := fun n ↦
    genRate_ne_top_of_mem_convexHull_vertices hS ν V hV (hm n)
  have hrate := tendsto_genRate_of_tendsto hS ν V hV hM hm hlim
  have hC0 : 0 ≤ C := (hf0 (Classical.arbitrary X)).trans (hfC _)
  have hgC : ∀ᶠ n in atTop, ∀ x, g n x ≤ C + 1 := by
    filter_upwards [hε.eventually (eventually_le_nhds one_pos)] with n hn x
    linarith [(abs_le.1 (hgf n x)).2, hfC x]
  have hgint : ∀ᶠ n in atTop, Integrable (g n) ν := by
    filter_upwards [hgnn, hgC] with n hn hnC
    exact integrable_of_bdd_prob ν ⟨hgm n, C + 1, fun x ↦ abs_le.2 ⟨by linarith [hn x], hnC x⟩⟩
  have hgP : ∀ᶠ n in atTop,
      IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (g n x)) := by
    filter_upwards [hgnn, hgint] with n hn hni
    exact isProbabilityMeasure_withDensity_ofReal ν hn hni (hg1 n)
  -- Pythagoras at the moving mean
  have hpy : ∀ᶠ n in atTop, klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g n x))
      (ν.withDensity fun x ↦ ENNReal.ofReal (projDens hS ν (m n) x)) =
      klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g n x)) ν - genRate ν S (m n) := by
    filter_upwards [hgnn, hgP] with n hn hP
    have hmean : (fun i ↦ ∫ x, S i x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (g n x))) = m n := by
      funext j
      rw [integral_withDensity_ofReal ν (hgm n) hn, ← hgmean n j]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    have := (responseProjection_spec hS ν (hfinn n)).2.2.2 _ hP hmean
    rw [responseProjection_eq_withDensity_projDens hS ν (hfinn n)] at this
    rw [this, ENNReal.add_sub_cancel_right (hfinn n)]
  have hkq : Tendsto (fun n ↦ klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g n x))
      (ν.withDensity fun x ↦ ENNReal.ofReal (projDens hS ν (m n) x))) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.sub hKL hrate (Or.inl hfin)
    rw [tsub_self] at h
    exact h.congr' (hpy.mono fun n hn ↦ hn.symm)
  have hkqR : Tendsto (fun n ↦ √(2 * (klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g n x))
      (ν.withDensity fun x ↦ ENNReal.ofReal (projDens hS ν (m n) x))).toReal) + ε n) atTop
      (𝓝 0) := by
    have h := ((((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hkq).const_mul 2).sqrt).add hε
    simpa using h
  have hfint : Integrable f ν :=
    integrable_of_bdd_prob ν ⟨hfm, C, fun x ↦ abs_le.2 ⟨by linarith [hf0 x], hfC x⟩⟩
  have hpM := projDens_ae_eq hS ν hfm hf0 hf
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hkqR
  filter_upwards [hgnn, hgC, hgint, hgP, hpy] with n hn hnC hni hP hpyn
  rw [norm_projL1_sub]
  have hkl : klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g n x))
      (ν.withDensity fun x ↦ ENNReal.ofReal (projDens hS ν (m n) x)) ≠ ⊤ := by
    rw [hpyn]
    exact ENNReal.sub_ne_top (klDiv_withDensity_ne_top_of_bdd ν (hgm n) hn hnC)
  have hpn := isProbabilityMeasure_withDensity_projDens hS ν (hfinn n)
  have hpins := integral_abs_sub_le_sqrt_klDiv ν (hgm n) (measurable_projDens hS ν (m n)) hn
    (projDens_nonneg hS ν _) hni (integrable_projDens hS ν _) hP hpn hkl
  have hgfI : ∫ x, |g n x - f x| ∂ν ≤ ε n := by
    calc ∫ x, |g n x - f x| ∂ν ≤ ∫ _x, ε n ∂ν :=
          integral_mono (hni.sub hfint).abs (integrable_const _) fun x ↦ hgf n x
      _ = ε n := by rw [integral_const, probReal_univ, one_smul]
  calc ∫ x, |projDens hS ν (m n) x - projDens hS ν M x| ∂ν
      = ∫ x, |projDens hS ν (m n) x - f x| ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hpM] with x hx
        rw [hx]
    _ ≤ ∫ x, (|g n x - projDens hS ν (m n) x| + |g n x - f x|) ∂ν := by
        refine integral_mono ((integrable_projDens hS ν _).sub hfint).abs
          ((hni.sub (integrable_projDens hS ν _)).abs.add (hni.sub hfint).abs) fun x ↦ ?_
        rw [abs_sub_comm (g n x) (projDens hS ν (m n) x)]
        exact abs_sub_le _ _ _
    _ = (∫ x, |g n x - projDens hS ν (m n) x| ∂ν) + ∫ x, |g n x - f x| ∂ν :=
        integral_add (hni.sub (integrable_projDens hS ν _)).abs (hni.sub hfint).abs
    _ ≤ √(2 * (klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g n x))
          (ν.withDensity fun x ↦ ENNReal.ofReal (projDens hS ν (m n) x))).toReal) + ε n :=
        add_le_add hpins hgfI

/-- **The completed family is continuous in `L¹(ν)` on the whole polytope.** -/
theorem continuousOn_projL1_polytope :
    ContinuousOn (projL1 hS ν) (convexHull ℝ (V : Set (J → ℝ))) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_iff_seqContinuous.2 fun u M hu ↦ ?_
  exact tendsto_projL1_of_tendsto hS ν V hV M.2 (fun n ↦ (u n).2)
    ((continuous_subtype_val.tendsto M).comp hu)

/-- **The completed family is continuous in `L¹(ν)` on the whole closed moment body.** -/
theorem continuousOn_projL1_momentBody
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ))) :
    ContinuousOn (projL1 hS ν) (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
  hpoly ▸ continuousOn_projL1_polytope hS ν V hV

end Continuity

section Topology

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V] (hV : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The mean map on `L¹(ν)`, `f ↦ (∫ S_j f dν)_j`. -/
noncomputable def meanL1 (f : X →₁[ν] ℝ) : J → ℝ := fun j ↦ obsL1 ν (hS j) f

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem continuous_meanL1 : Continuous (meanL1 hS ν) :=
  continuous_pi fun j ↦ (obsL1 ν (hS j)).continuous

/-- The mean map inverts the response map. -/
theorem meanL1_projL1 {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    meanL1 hS ν (projL1 hS ν M) = M := by
  funext j
  unfold meanL1 projL1
  rw [obsL1_apply, ← integral_stat_mul_projDens hS ν hfin j]
  exact integral_congr_ae ((integrable_projDens hS ν M).coeFn_toL1.mono fun x hx ↦ by
    beta_reduce
    rw [hx])

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The completed family in `L¹(ν)`: the response projections of the whole polytope. -/
def completedFamilyL1 : Set (X →₁[ν] ℝ) := projL1 hS ν '' convexHull ℝ (V : Set (J → ℝ))

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] [Nonempty V] in
theorem isCompact_polytope : IsCompact (convexHull ℝ (V : Set (J → ℝ))) :=
  V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)

include hV

/-- **The completed family is compact.** -/
theorem isCompact_completedFamilyL1 : IsCompact (completedFamilyL1 hS ν V) :=
  (isCompact_polytope V).image_of_continuousOn (continuousOn_projL1_polytope hS ν V hV)

omit [Nonempty V] in
theorem meanL1_mem_of_mem_completedFamilyL1 {f : X →₁[ν] ℝ} (hf : f ∈ completedFamilyL1 hS ν V) :
    meanL1 hS ν f ∈ convexHull ℝ (V : Set (J → ℝ)) := by
  obtain ⟨M, hM, rfl⟩ := hf
  rw [meanL1_projL1 hS ν (genRate_ne_top_of_mem_convexHull_vertices hS ν V hV hM)]
  exact hM

omit [Nonempty V] in
theorem projL1_meanL1_of_mem {f : X →₁[ν] ℝ} (hf : f ∈ completedFamilyL1 hS ν V) :
    projL1 hS ν (meanL1 hS ν f) = f := by
  obtain ⟨M, hM, rfl⟩ := hf
  rw [meanL1_projL1 hS ν (genRate_ne_top_of_mem_convexHull_vertices hS ν V hV hM)]

/-- **The completed family is homeomorphic to the polytope** through the response map and the
mean map. -/
noncomputable def completedHomeomorphL1 :
    convexHull ℝ (V : Set (J → ℝ)) ≃ₜ completedFamilyL1 hS ν V where
  toFun M := ⟨projL1 hS ν M, M, M.2, rfl⟩
  invFun f := ⟨meanL1 hS ν f, meanL1_mem_of_mem_completedFamilyL1 hS ν V hV f.2⟩
  left_inv M := Subtype.ext
    (meanL1_projL1 hS ν (genRate_ne_top_of_mem_convexHull_vertices hS ν V hV M.2))
  right_inv f := Subtype.ext (projL1_meanL1_of_mem hS ν V hV f.2)
  continuous_toFun :=
    ((continuousOn_projL1_polytope hS ν V hV).comp_continuous continuous_subtype_val
      fun M ↦ M.2).subtype_mk _
  continuous_invFun := ((continuous_meanL1 hS ν).comp continuous_subtype_val).subtype_mk _

/-- **The completed family is the closure of the interior exponential family.** -/
theorem closure_image_intrinsicInterior
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ))) :
    closure (projL1 hS ν '' intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) =
      completedFamilyL1 hS ν V := by
  refine subset_antisymm ?_ fun p hp ↦ ?_
  · refine closure_minimal (Set.image_mono ?_) (isCompact_completedFamilyL1 hS ν V hV).isClosed
    rw [← hpoly]
    exact intrinsicInterior_subset
  · obtain ⟨M, hM, rfl⟩ := hp
    have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hV hM
    obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 2) := ⟨_, rfl⟩
    have hu0 : ∀ n, 0 ≤ u n := fun n ↦ by
      rw [hu]
      have h2 : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      simp only
      linarith
    have hu1 : ∀ n, u n < 1 := fun n ↦ by
      rw [hu]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      simp only
      linarith
    have hulim : Tendsto u atTop (𝓝 1) := by
      rw [hu]
      have h' : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub h'
      rwa [sub_zero] at this
    have hpath : Tendsto (fun n ↦ atlasPath S ν M (u n)) atTop (𝓝 M) := by
      have hc : ContinuousAt (atlasPath S ν M) 1 :=
        (hasDerivAt_atlasPath ν (S := S) (M := M) 1).continuousAt
      have := hc.tendsto.comp hulim
      rwa [atlasPath_one] at this
    have hmem : ∀ n, atlasPath S ν M (u n) ∈
        intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := fun n ↦
      atlas_mem_intrinsicInterior hS ν hfin (hu0 n) (hu1 n)
    have hmemP : ∀ n, atlasPath S ν M (u n) ∈ convexHull ℝ (V : Set (J → ℝ)) := fun n ↦
      hpoly ▸ intrinsicInterior_subset (hmem n)
    exact mem_closure_of_tendsto (tendsto_projL1_of_tendsto hS ν V hV hM hmemP hpath)
      (Eventually.of_forall fun n ↦ mem_image_of_mem _ (hmem n))

end Topology

end Laplace.Multi
