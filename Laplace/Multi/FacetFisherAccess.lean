/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FaceCoercivity
import Laplace.Multi.PathLengthPrimitive
import Laplace.Multi.RayFisherLengthClassification

/-!
# Facet accessibility: helpers

Continuity of the ray speed in the ray parameter, orthogonality of the face directions to the
exposing normal, linearity of the normal depth, the facet condition `T' = W ∩ u^⊥` implying that
the only directions invisible on the face are the normals, the a.e. halfspace bound of a
polytope, and the a.e./constant invariances of the covariance.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Helpers

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty J] in
/-- The ray law is the tilt of the base member by `t ⟨u, S⟩`. -/
theorem familyMeasure_sub_smul_eq_tilted_base (θ u : J → ℝ) (t : ℝ) :
    familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u) =
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ).tilted
        (fun x ↦ t * dirLoss S u x) := by
  rw [familyMeasure_one_zero_eq_tilted hS ν, familyMeasure_one_zero_eq_tilted hS ν,
    tilted_tilted (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))]
  congr 1
  funext x
  simp only [Pi.add_apply, dirLoss_sub', dirLoss_smul]
  ring

omit [Nonempty J] in
/-- The ray speed is continuous in the ray parameter. -/
theorem continuous_raySpeedSq (θ u : J → ℝ) : Continuous fun t ↦ raySpeedSq S ν θ u t := by
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) := by
    rw [familyMeasure_one_zero_eq_tilted hS ν]
    exact isProbabilityMeasure_tilted
      (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))
  have e : (fun t ↦ raySpeedSq S ν θ u t) = fun t ↦
      (∫ x, dirLoss S u x * dirLoss S u x
        ∂(familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ).tilted
          (fun x ↦ t * dirLoss S u x)) -
      (∫ x, dirLoss S u x ∂(familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ).tilted
          (fun x ↦ t * dirLoss S u x)) *
      ∫ x, dirLoss S u x ∂(familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ).tilted
          (fun x ↦ t * dirLoss S u x) := by
    funext t
    rw [raySpeedSq, familyMeasure_sub_smul_eq_tilted_base hS ν θ u t, lawCov]
  rw [e]
  have h1 : Continuous fun t ↦ ∫ x, dirLoss S u x * dirLoss S u x
      ∂(familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ).tilted
        (fun x ↦ t * dirLoss S u x) :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_integral_tilted _ (bdd_dirLoss hS u)
      ((bdd_dirLoss hS u).mul (bdd_dirLoss hS u)) t).continuousAt
  have h2 : Continuous fun t ↦ ∫ x, dirLoss S u x
      ∂(familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ).tilted
        (fun x ↦ t * dirLoss S u x) :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_integral_tilted _ (bdd_dirLoss hS u)
      (bdd_dirLoss hS u) t).continuousAt
  exact h1.sub (h2.mul h2)

omit [Nonempty J] in
theorem continuous_sqrt_raySpeedSq (θ u : J → ℝ) :
    Continuous fun t ↦ √(raySpeedSq S ν θ u t) :=
  (continuous_raySpeedSq hS ν θ u).sqrt

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem dotJ_comm' (a b : J → ℝ) : dotJ a b = dotJ b a := by
  simp [dotJ, mul_comm]

omit [Nonempty X] [Nonempty J] in
/-- **Face directions are orthogonal to the exposing normal.** -/
theorem dotJ_eq_zero_of_mem_dirSpan_faceMeasure (u : J → ℝ) (β : ℝ)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {w : J → ℝ}
    (hw : w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) :
    dotJ u w = 0 := by
  have hsub := momentBody_faceMeasure_subset_hyperplane ν (measurableSet_faceFibre hS u β) hS hp
    (e := u) (β := β) rfl
  have h1 : dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S ≤
      LinearMap.ker (IsLinearMap.mk' _ (isLinearMap_dotJ u)) := by
    change (affineSpan ℝ _).direction ≤ _
    rw [direction_affineSpan, vectorSpan_def]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, IsLinearMap.mk'_apply]
    change dotJ u (y₁ -ᵥ y₂) = 0
    rw [vsub_eq_sub, (isLinearMap_dotJ u).map_sub, hsub hy₁, hsub hy₂, sub_self]
  have := h1 hw
  rwa [LinearMap.mem_ker, IsLinearMap.mk'_apply] at this

omit [Nonempty X] [Nonempty J] hS in
/-- The covariance only depends on a.e. classes. -/
theorem lawCov_congr_ae (q : Measure X) {f f' g g' : X → ℝ} (hf : f =ᵐ[q] f') (hg : g =ᵐ[q] g') :
    lawCov q f g = lawCov q f' g' := by
  unfold lawCov
  have hfg : (fun x ↦ f x * g x) =ᵐ[q] fun x ↦ f' x * g' x := hf.mul hg
  rw [integral_congr_ae hfg, integral_congr_ae hf, integral_congr_ae hg]

omit [Nonempty X] [Nonempty J] hS in
/-- The variance is invariant under subtracting a constant. -/
theorem lawCov_sub_const_self (q : Measure X) [IsProbabilityMeasure q] {f : X → ℝ} (hf : Bdd f)
    (c : ℝ) : lawCov q (fun x ↦ f x - c) (fun x ↦ f x - c) = lawCov q f f := by
  rw [lawCov_sub_self q hf (Bdd.const c), lawCov_comm q f (fun _ ↦ c), lawCov_const_left_eq_zero,
    lawCov_const_left_eq_zero]
  ring

variable (u : J → ℝ) (β : ℝ) (hp : 0 < ν.real {x | dirLoss S u x = β})
include hp

/-- The normal depth is linear. -/
theorem normalDepth_eq [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
    (η : J → ℝ) :
    normalDepth hS ν {x | dirLoss S u x = β} u η = -dotJ η u / dotJ u u := by
  rw [normalDepth, dotJ_sub_left, dotJ_comm' (faceTheta hS ν _ η : J → ℝ),
    dotJ_eq_zero_of_mem_dirSpan_faceMeasure hS ν u β hp (faceTheta hS ν _ η).2, sub_zero]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] hp in
/-- **The facet condition `T' = W ∩ u^⊥` makes the normals the only invisible directions of
`W`.** -/
theorem facet_invisible_of_orth [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
    (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) :
    ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      w ∈ invisibleSet (faceMeasure ν {x | dirLoss S u x = β}) S → ∃ c : ℝ, w = c • u := by
  intro w hw hinv
  refine ⟨dotJ w u / dotJ u u, ?_⟩
  have hw₀ : w - (dotJ w u / dotJ u u) • u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
    Submodule.sub_mem _ hw (Submodule.smul_mem _ _ huW)
  have hperp : dotJ (w - (dotJ w u / dotJ u u) • u) u = 0 := by
    rw [dotJ_sub_left, dotJ_smul_left, div_mul_cancel₀ _ hu, sub_self]
  have hT' := hT _ hw₀ hperp
  have hinv' : w - (dotJ w u / dotJ u u) • u ∈
      invisibleSet (faceMeasure ν {x | dirLoss S u x = β}) S := by
    have h := neg_smul_mem_invisible_faceMeasure hS ν u β (-(dotJ w u / dotJ u u))
    rw [neg_smul, neg_neg] at h
    exact (invisibleSubmodule (faceMeasure ν {x | dirLoss S u x = β}) S).sub_mem hinv h
  have := eq_zero_of_invisible_of_mem_dirSpan measurable_const (fun _ ↦ one_pos) hS hinv' hT'
  rw [sub_eq_zero] at this
  exact this

end Helpers

section Assembly

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS hpoly hcharged in
theorem sum_abs_le_card_mul_norm (w : J → ℝ) : ∑ i, |w i| ≤ (Fintype.card J : ℝ) * ‖w‖ := by
  calc ∑ i, |w i| ≤ ∑ _i : J, ‖w‖ := Finset.sum_le_sum fun i _ ↦ by
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm w i
    _ = (Fintype.card J : ℝ) * ‖w‖ := by simp

omit [Nonempty X] [Nonempty J] hS hpoly hcharged in
theorem abs_max_sub_zero_le {β d K : ℝ} (hd : |d| ≤ K) : |max (β - d) 0| ≤ |β| + K := by
  rw [abs_of_nonneg (le_max_right _ _)]
  refine max_le ((le_abs_self _).trans ((abs_sub β d).trans ?_)) ?_
  · linarith
  · linarith [abs_nonneg d, abs_nonneg β]

/-- **Facet accessibility (forward)**: a `C¹` path in the direction space whose means converge to
a point of the relative interior of a facet and whose Fisher length is finite forces the normal
ray to the facet to have finite Fisher length. -/
theorem lintegral_sqrt_raySpeedSq_lt_top_of_path {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β)
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)
    {η : ℝ → J → ℝ} (hη : ∀ s, η s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {η' : ℝ → J → ℝ}
    (hd : ∀ s, 0 ≤ s → HasDerivAt η (η' s) s) (hd' : ContinuousOn η' (Ici 0))
    (hlim : Tendsto (fun s ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η s)) atTop
      (𝓝 M))
    (hI : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
      (√(lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η s))
        (dirLoss S (η' s)) (dirLoss S (η' s))))) < ⊤) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) u r))) < ⊤ := by
  -- the face
  have hp : 0 < ν.real {x | dirLoss S u x = β} := faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hF' := measurableSet_faceFibre hS u β
  have hA0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPA := isProbabilityMeasure_faceMeasure ν hA0
  have hβ := ae_dirLoss_le_of_polytope hS ν V u β hpoly hV
  have hM' : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) := by
    rw [momentBody_faceMeasure_eq_of_exposed hS ν V u β hpoly hcharged hV hp]
    exact hMint
  set vM : J → ℝ := (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) with hvM
  have hfacet := facet_invisible_of_orth hS ν u β huW hu hT
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  obtain ⟨-, Ku, hKu⟩ := bdd_dirLoss hS u
  have hPf : ∀ θ : J → ℝ,
      IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) := by
    intro θ
    rw [familyMeasure_one_zero_eq_tilted hS ν]
    exact isProbabilityMeasure_tilted
      (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))
  -- the linear depth and the tangential part
  set r : ℝ → ℝ := fun s ↦ -dotJ (η s) u / dotJ u u with hr_def
  set v : ℝ → J → ℝ := fun s ↦ η s + r s • u with hv_def
  have hdecomp : ∀ s, η s = v s - r s • u := fun s ↦ by simp [hv_def]
  have hvT : ∀ s, (faceTheta hS ν {x | dirLoss S u x = β} (η s) : J → ℝ) = v s := fun s ↦ by
    have h := eq_faceTheta_sub_smul hS ν _ u hF' hp hfacet hu (hη s)
    rw [normalDepth_eq hS ν u β hp] at h
    calc (faceTheta hS ν {x | dirLoss S u x = β} (η s) : J → ℝ)
        = (faceTheta hS ν {x | dirLoss S u x = β} (η s) : J → ℝ) - r s • u + r s • u :=
          (sub_add_cancel _ _).symm
      _ = v s := by rw [← h]
  -- the sequential criterion, transported to the real parameter
  have hcrit : ∀ x : ℕ → ℝ, Tendsto x atTop atTop →
      Tendsto (fun n ↦ meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 (η (x n))) atTop (𝓝 M) ∧
      ∀ w ∈ V, dotJ u w < β → Tendsto (fun n ↦ dotJ (η (x n)) (w - v₀)) atTop atTop :=
    fun x hx ↦ (tendsto_meanMap_iff_faceMean_and_vertexGaps hS ν V hpoly hcharged hV hM hMβ hF
      hv₀V hv₀β (η ∘ x)).1 (hlim.comp hx)
  have hface : Tendsto (fun s ↦ meanMap (faceMeasure ν {x | dirLoss S u x = β})
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η s)) atTop (𝓝 M) :=
    tendsto_iff_seq_tendsto.2 fun x hx ↦ (hcrit x hx).1
  have hgap : Tendsto (fun s ↦ dotJ (η s) (z - v₀)) atTop atTop :=
    tendsto_iff_seq_tendsto.2 fun x hx ↦ (hcrit x hx).2 z hzV hz
  have hvθ : Tendsto (fun s ↦ (faceTheta hS ν {x | dirLoss S u x = β} (η s) : J → ℝ)) atTop
      (𝓝 vM) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_faceTheta hS ν _ hM' hface)
  have hv : Tendsto v atTop (𝓝 vM) := hvθ.congr hvT
  have hr : Tendsto r atTop atTop := by
    have := tendsto_normalDepth_atTop hS ν _ u hF' hp hfacet hu hη hz hv₀β hgap hvθ
    exact this.congr fun s ↦ normalDepth_eq hS ν u β hp (η s)
  -- concentration and coercivity
  have hmass : Tendsto (fun s ↦ (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (η s)).real {x | dirLoss S u x = β}) atTop (𝓝 1) := by
    have := tendsto_measureReal_family_faceFibre_of_components hS ν u β hβ hp hv hr
    exact this.congr fun s ↦ by rw [← hdecomp s]
  obtain ⟨lam, hlam, hcoer⟩ := eventually_coercive_of_components hS ν u β hβ hp hv hr
  -- the tilt sizes tend to zero
  have hc : Tendsto (fun s ↦ (∑ i, |(v s - vM) i|) * B) atTop (𝓝 0) := by
    have h0 : Tendsto (fun s ↦ v s - vM) atTop (𝓝 0) := by simpa using hv.sub_const vM
    have h1 : Tendsto (fun s ↦ ∑ i, |(v s - vM) i|) atTop (𝓝 (∑ i, |(0 : J → ℝ) i|)) :=
      tendsto_finsetSum _ fun i _ ↦
        ((continuous_abs.comp (continuous_apply i)).tendsto _).comp h0
    simpa using h1.mul_const B
  -- derivatives of the depth and of the tangential part
  set r' : ℝ → ℝ := fun s ↦ -dotJ (η' s) u / dotJ u u with hr'_def
  have hdr : ∀ s, 0 ≤ s → HasDerivAt r (r' s) s := fun s hs ↦ by
    have h1 : HasDerivAt (fun s ↦ dotJ (η s) u) (dotJ (η' s) u) s := by
      have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
        (hasDerivAt_pi.1 (hd s hs) i).mul_const (u i)
      exact this
    exact h1.neg.div_const _
  set v' : ℝ → J → ℝ := fun s ↦ η' s + r' s • u with hv'_def
  have hη'W : ∀ s, 0 ≤ s → η' s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun s hs ↦
    mem_of_hasDerivAt_subtype (Submodule.closed_of_finiteDimensional _)
      (γ := fun s ↦ (⟨η s, hη s⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S)) (hd s hs)
  have hv'T : ∀ s, 0 ≤ s →
      v' s ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S := fun s hs ↦ by
    refine hT _ (Submodule.add_mem _ (hη'W s hs) (Submodule.smul_mem _ _ huW)) ?_
    rw [dotJ_comm', (isLinearMap_dotJ u).map_add, (isLinearMap_dotJ u).map_smul, smul_eq_mul,
      dotJ_comm' u (η' s)]
    simp only [hr'_def]
    field_simp
    ring
  -- the slack and its positive part
  set ℓ : X → ℝ := fun x ↦ β - dirLoss S u x with hℓ_def
  set ℓp : X → ℝ := fun x ↦ max (β - dirLoss S u x) 0 with hℓp_def
  have hℓ_bdd : Bdd ℓ := (Bdd.const β).sub (bdd_dirLoss hS u)
  have hℓp_bdd : Bdd ℓp :=
    ⟨((bdd_dirLoss hS u).1.const_sub β).max measurable_const, |β| + Ku,
      fun x ↦ abs_max_sub_zero_le (hKu x)⟩
  have hℓp0 : ∀ x, 0 ≤ ℓp x := fun x ↦ le_max_right _ _
  have hℓp_meas : MeasurableSet {x | ℓp x = 0} := measurableSet_eq_fun hℓp_bdd.1 measurable_const
  have hac : ∀ θ : J → ℝ, familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ ≪ ν :=
    fun θ ↦ by
      rw [familyMeasure_eq_withDensity_famDens]
      exact withDensity_absolutelyContinuous _ _
  have hβq : ∀ θ : J → ℝ, ∀ᵐ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ,
      dirLoss S u x ≤ β := fun θ ↦ (hac θ).ae_le hβ
  have hℓ_ae : ∀ θ : J → ℝ, ℓ =ᵐ[familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ] ℓp :=
    fun θ ↦ (hβq θ).mono fun x hx ↦ by
      simp only [hℓ_def, hℓp_def]
      rw [max_eq_left (sub_nonneg.2 hx)]
  have hset_ae : ∀ θ : J → ℝ, ({x | ℓp x = 0} : Set X)
      =ᵐ[familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ] {x | dirLoss S u x = β} :=
    fun θ ↦ Filter.eventuallyEq_set.2 ((hβq θ).mono fun x hx ↦ by
      simp only [hℓp_def, Set.mem_ofPred_eq]
      constructor
      · intro h
        have := max_eq_right_iff.1 h
        exact le_antisymm hx (by linarith)
      · intro h
        rw [max_eq_right_iff]
        linarith)
  -- constants
  set κ : ℝ := ((Fintype.card J : ℝ) * B) ^ 2 / lam with hκ_def
  have hκ0 : 0 ≤ κ := by positivity
  set δ : ℝ := 1 / (16 * κ + 1) with hδ_def
  have hδ0 : 0 < δ := by positivity
  set g : ℝ → ℝ := fun t ↦ √(raySpeedSq S ν vM u t) with hg_def
  have hg_cont : Continuous g := continuous_sqrt_raySpeedSq hS ν vM u
  have hg0 : ∀ t, 0 ≤ g t := fun t ↦ Real.sqrt_nonneg _
  set c₀ : ℝ := exp (-1) / √2 with hc₀_def
  have hc₀pos : 0 < c₀ := by positivity
  -- the eventual speed lower bound
  have hev : ∀ᶠ s in atTop, c₀ * (|r' s| * g (r s)) ≤
      √(lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η s))
        (dirLoss S (η' s)) (dirLoss S (η' s))) := by
    filter_upwards [hcoer, hmass.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hmass.eventually (Ici_mem_nhds (by linarith : 1 - δ < 1)),
      hc.eventually (Iic_mem_nhds one_pos), eventually_ge_atTop (0 : ℝ)]
      with s hcs hms hms' hcs' hs0
    set q := familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η s) with hq_def
    have hqP : IsProbabilityMeasure q := hPf _
    -- the tangential observable
    set f : X → ℝ := dirLoss S (v' s) with hf_def
    have hf_bdd : Bdd f := bdd_dirLoss hS _
    have hK : ∀ x, |f x| ≤ (∑ i, |v' s i|) * B := fun x ↦ abs_dirLoss_le_sum_mul hB _ x
    have hKV : ((∑ i, |v' s i|) * B) ^ 2 ≤ κ * lawCov q f f := by
      have h1 : (∑ i, |v' s i|) * B ≤ (Fintype.card J : ℝ) * ‖v' s‖ * B :=
        mul_le_mul_of_nonneg_right (sum_abs_le_card_mul_norm _) hB0
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      have h4 : ‖v' s‖ ^ 2 ≤ lawCov q f f / lam := by
        have := hcs _ (hv'T s hs0)
        rw [← hdecomp s] at this
        exact (le_div_iff₀' hlam).2 this
      calc ((∑ i, |v' s i|) * B) ^ 2 ≤ ((Fintype.card J : ℝ) * ‖v' s‖ * B) ^ 2 := h2
        _ = ((Fintype.card J : ℝ) * B) ^ 2 * ‖v' s‖ ^ 2 := by ring
        _ ≤ ((Fintype.card J : ℝ) * B) ^ 2 * (lawCov q f f / lam) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = κ * lawCov q f f := by rw [hκ_def]; ring
    -- the face masses of the positive part
    have hpp : q.real {x | ℓp x = 0} = q.real {x | dirLoss S u x = β} :=
      measureReal_congr (hset_ae _)
    have hp' : 0 < q.real {x | ℓp x = 0} := by rw [hpp]; linarith
    have hεp : q.real {x | ℓp x = 0}ᶜ = 1 - q.real {x | ℓp x = 0} := by
      rw [measureReal_compl hℓp_meas, probReal_univ]
    have hfactor : 1 / 2 ≤ 1 - 4 * κ * (q.real {x | ℓp x = 0}ᶜ / q.real {x | ℓp x = 0}) := by
      rw [hεp, hpp]
      have hpp2 : 1 / 2 ≤ q.real {x | dirLoss S u x = β} := hms
      have hpp3 : 1 - δ ≤ q.real {x | dirLoss S u x = β} := hms'
      rw [div_le_iff₀ (by linarith)] at *
      have h5 : 4 * κ * ((1 - q.real {x | dirLoss S u x = β}) / q.real {x | dirLoss S u x = β})
          ≤ 1 / 2 := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        have h6 : 4 * κ * (1 - q.real {x | dirLoss S u x = β}) ≤ 4 * κ * δ :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h7 : 4 * κ * δ ≤ 1 / 4 := by
          rw [hδ_def, mul_one_div, div_le_iff₀ (by positivity)]
          linarith
        linarith
      linarith
    -- the Schur bound
    have hschur := facet_schur_bound q hℓp_bdd hℓp0 hp' hf_bdd hK hκ0 hKV (r' s)
    -- the speed identity
    have eη' : dirLoss S (η' s) = fun x ↦ (r' s * ℓ x + f x) - r' s * β := by
      funext x
      have e1 : η' s = v' s - r' s • u := (add_sub_cancel_right _ _).symm
      rw [e1, dirLoss_sub', dirLoss_smul]
      simp only [hℓ_def, hf_def]
      ring
    have hF_bdd : Bdd fun x ↦ r' s * ℓ x + f x := (Bdd.const_mul _ hℓ_bdd).add hf_bdd
    have hFp : (fun x ↦ r' s * ℓ x + f x) =ᵐ[q] fun x ↦ r' s * ℓp x + f x :=
      (hℓ_ae _).mono fun x hx ↦ by simp only [hx]
    have hspeed : lawCov q (dirLoss S (η' s)) (dirLoss S (η' s)) =
        lawCov q (fun x ↦ r' s * ℓp x + f x) (fun x ↦ r' s * ℓp x + f x) := by
      rw [eη', lawCov_sub_const_self q hF_bdd, lawCov_congr_ae q hFp hFp]
    -- the normal variance is the tilted ray variance
    have hVar : lawCov q ℓp ℓp = lawCov q (dirLoss S u) (dirLoss S u) := by
      rw [← lawCov_congr_ae q (hℓ_ae _) (hℓ_ae _), hℓ_def,
        lawCov_const_sub_self q (bdd_dirLoss hS u)]
    have hray : exp (-(2 * 1)) * raySpeedSq S ν vM u (r s) ≤
        lawCov q (dirLoss S u) (dirLoss S u) := by
      have hPr := hPf (vM - r s • u)
      have hc' : ∀ x, |(fun x ↦ -(dirLoss S (v s - vM) x)) x| ≤ 1 := fun x ↦ by
        simp only [abs_neg]
        exact (abs_dirLoss_le_sum_mul hB _ x).trans hcs'
      have h := le_lawCov_tilted (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (vM - r s • u)) (bdd_neg (bdd_dirLoss hS _)) hc' (bdd_dirLoss hS u)
      rw [← familyMeasure_sub_smul_eq_tilted hS ν (v s) vM u (r s), ← hdecomp s] at h
      exact h
    -- assemble
    have hV0 : 0 ≤ lawCov q ℓp ℓp := lawCov_self_nonneg q hℓp_bdd
    have hsq : (c₀ * (|r' s| * g (r s))) ^ 2 ≤
        lawCov q (dirLoss S (η' s)) (dirLoss S (η' s)) := by
      have hg2 : g (r s) ^ 2 = raySpeedSq S ν vM u (r s) := by
        rw [hg_def]
        exact Real.sq_sqrt (lawCov_self_nonneg _ (bdd_dirLoss hS u))
      have hc2 : c₀ ^ 2 = exp (-(2 * 1)) / 2 := by
        rw [hc₀_def, div_pow, Real.sq_sqrt (by norm_num), ← Real.exp_nat_mul]
        norm_num
      rw [hspeed, mul_pow, mul_pow, hg2, hc2, sq_abs]
      calc exp (-(2 * 1)) / 2 * (r' s ^ 2 * raySpeedSq S ν vM u (r s))
          = r' s ^ 2 * (exp (-(2 * 1)) * raySpeedSq S ν vM u (r s)) * (1 / 2) := by ring
        _ ≤ r' s ^ 2 * lawCov q ℓp ℓp * (1 / 2) := by
            rw [hVar]; gcongr
        _ ≤ r' s ^ 2 * lawCov q ℓp ℓp *
            (1 - 4 * κ * (q.real {x | ℓp x = 0}ᶜ / q.real {x | ℓp x = 0})) := by
            gcongr
        _ ≤ _ := hschur
    exact Real.le_sqrt_of_sq_le hsq
  -- the eventual bound holds from some time on
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.1 (hev.and (eventually_ge_atTop (0 : ℝ)))
  have hs₀0 : 0 ≤ s₀ := (hs₀ s₀ le_rfl).2
  -- the weighted depth length is finite
  set speed : ℝ → ℝ := fun s ↦ √(lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
    (η s)) (dirLoss S (η' s)) (dirLoss S (η' s))) with hspeed_def
  have hItop : (∫⁻ s in Ioi s₀, ENNReal.ofReal (speed s)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set (Ioi_subset_Ioi hs₀0)) hI
  have hr'cont : ContinuousOn r' (Ici s₀) := by
    have : ContinuousOn r' (Ici 0) :=
      (((continuous_dotJ_left u).comp_continuousOn hd').neg).div_const _
    exact this.mono (Ici_subset_Ici.2 hs₀0)
  have hI' : ∀ b, s₀ ≤ b → ∫ s in s₀..b, |r' s| * g (r s) ≤
      (ENNReal.ofReal (1 / c₀) * ∫⁻ s in Ioi s₀, ENNReal.ofReal (speed s)).toReal := by
    intro b hb
    have hcontOn : ContinuousOn (fun s ↦ |r' s| * g (r s)) (Ioc s₀ b) := by
      refine (hr'cont.abs.mul (hg_cont.comp_continuousOn ?_)).mono fun x hx ↦ hx.1.le
      exact HasDerivAt.continuousOn (fun s hs ↦ hdr s (hs₀0.trans hs))
    rw [intervalIntegral.integral_of_le hb, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun s ↦ mul_nonneg (abs_nonneg _) (hg0 _))
      (hcontOn.aestronglyMeasurable measurableSet_Ioc)]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hItop.ne) ?_
    calc ∫⁻ s in Ioc s₀ b, ENNReal.ofReal (|r' s| * g (r s))
        ≤ ∫⁻ s in Ioc s₀ b, ENNReal.ofReal (1 / c₀) * ENNReal.ofReal (speed s) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _
            fun s hs ↦ ?_))
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := (hs₀ s hs.1.le).1
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc₀pos]
          linarith
      _ = ENNReal.ofReal (1 / c₀) * ∫⁻ s in Ioc s₀ b, ENNReal.ofReal (speed s) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / c₀) * ∫⁻ s in Ioi s₀, ENNReal.ofReal (speed s) :=
          mul_le_mul' le_rfl (lintegral_mono_set Ioc_subset_Ioi_self)
  have hint := integrableOn_Ioi_of_tendsto_atTop_of_integral_abs_deriv_mul_le hg_cont hg0
    (a := s₀) (fun s hs ↦ hdr s (hs₀0.trans hs)) hr'cont hr hI'
  -- extend to the whole half-line
  have hint0 : IntegrableOn g (Ioi (0 : ℝ)) := by
    rcases le_or_gt (r s₀) 0 with h | h
    · exact hint.mono_set (Ioi_subset_Ioi h)
    · rw [← Set.Ioc_union_Ioi_eq_Ioi h.le]
      exact hg_cont.integrableOn_Ioc.union hint
  have hvM : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν vM u t))) < ⊤ :=
    hint0.lintegral_lt_top
  exact (lintegral_sqrt_raySpeedSq_lt_top_iff_tilt hS ν 0 vM u).2 hvM

end Assembly

section Converse

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Nonempty J] in
/-- **Means along a natural ray converge to the face-family mean.** -/
theorem tendsto_meanMap_ray (θ u : J → ℝ) (β : ℝ) (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) :
    Tendsto (fun t : ℝ ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u)) atTop
      (𝓝 (meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ))
        S 1 θ)) := by
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  have hL1 := tendsto_tv_ray hS ν θ u β hβ hp
  refine tendsto_pi_nhds.2 fun j ↦ ?_
  obtain ⟨-, B, hB⟩ := hS j
  have hcoord : ∀ t : ℝ, meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u) j =
      ∫ x, S j x * famDens S ν (θ - t • u) x ∂ν := fun t ↦ by
    rw [← mean_familyMeasure_one_zero hS ν (θ - t • u)]
    simp only
    rw [familyMeasure_eq_withDensity_famDens, integral_withDensity_ofReal ν
      (measurable_famDens hS ν _) (famDens_nonneg hS ν _)]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  have hface : meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 θ j = ∫ x, S j x * faceDens S ν θ u β x ∂ν := by
    rw [← mean_familyMeasure_one_zero hS (faceMeasure ν {x | dirLoss S u x = β}) θ]
    simp only
    rw [familyMeasure_faceMeasure_eq hS ν θ u β hp, integral_withDensity_ofReal ν
      (measurable_faceDens hS ν θ u β) (faceDens_nonneg ν θ u β)]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  simp only [hcoord]
  rw [hface, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t ↦ norm_nonneg _)
    (Eventually.of_forall fun t ↦ ?_) (by simpa using hL1.const_mul B)
  have hbound : ∀ᵐ x ∂ν, ‖S j x‖ ≤ B := Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs]
    exact hB x
  have h1 : Integrable (fun x ↦ S j x * famDens S ν (θ - t • u) x) ν :=
    (integrable_famDens hS ν _).bdd_mul (hS j).1.aestronglyMeasurable hbound
  have h2 : Integrable (fun x ↦ S j x * faceDens S ν θ u β x) ν :=
    (integrable_faceDens hS ν θ u β).bdd_mul (hS j).1.aestronglyMeasurable hbound
  have h3 : Integrable (fun x ↦ |famDens S ν (θ - t • u) x - faceDens S ν θ u β x|) ν :=
    ((integrable_famDens hS ν _).sub (integrable_faceDens hS ν θ u β)).abs
  rw [Real.norm_eq_abs, ← integral_sub h1 h2]
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_const_mul]
  refine integral_mono (h1.sub h2).abs (h3.const_mul B) fun x ↦ ?_
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)

variable (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hpoly hcharged

omit [Nonempty V] in
/-- **Facet accessibility (converse)**: a finite-length normal ray is itself a `C¹` path in the
direction space of finite Fisher length whose means converge to `M`. -/
theorem exists_path_of_lintegral_sqrt_raySpeedSq_lt_top {u : J → ℝ} {β : ℝ}
    (hV : ∀ v ∈ V, dotJ u v ≤ β) {M : J → ℝ}
    (hMint : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (hray : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) u r))) < ⊤) :
    ∃ η η' : ℝ → J → ℝ, (∀ s, η s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) ∧
      (∀ s, HasDerivAt η (η' s) s) ∧ Continuous η' ∧
      Tendsto (fun s ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η s)) atTop (𝓝 M) ∧
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
        (√(lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η s))
          (dirLoss S (η' s)) (dirLoss S (η' s))))) < ⊤ := by
  have hp : 0 < ν.real {x | dirLoss S u x = β} := faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hF' := measurableSet_faceFibre hS u β
  have hA0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPA := isProbabilityMeasure_faceMeasure ν hA0
  have hβ := ae_dirLoss_le_of_polytope hS ν V u β hpoly hV
  have hM' : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) := by
    rw [momentBody_faceMeasure_eq_of_exposed hS ν V u β hpoly hcharged hV hp]
    exact hMint
  set vM : J → ℝ := (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) with hvM
  have hvMW : vM ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
    dirSpan_faceMeasure_le hS ν _ hF' hp (faceThetaOf hS ν {x | dirLoss S u x = β} hM').2
  have hPf : ∀ θ : J → ℝ,
      IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) := by
    intro θ
    rw [familyMeasure_one_zero_eq_tilted hS ν]
    exact isProbabilityMeasure_tilted
      (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))
  refine ⟨fun s ↦ vM - s • u, fun _ ↦ -u,
    fun s ↦ Submodule.sub_mem _ hvMW (Submodule.smul_mem _ _ huW), fun s ↦ ?_, continuous_const,
    ?_, ?_⟩
  · have := ((hasDerivAt_id s).smul_const u).const_sub vM
    simpa using this
  · have h := tendsto_meanMap_ray hS ν vM u β hβ hp
    rwa [meanMap_faceThetaOf hS ν _ hM'] at h
  · have e : ∀ s : ℝ, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (vM - s • u))
        (dirLoss S (-u)) (dirLoss S (-u)) = raySpeedSq S ν vM u s := fun s ↦ by
      have := hPf (vM - s • u)
      have hn : dirLoss S (-u) = fun x ↦ -dirLoss S u x := funext (dirLoss_neg u)
      rw [raySpeedSq, hn, lawCov_neg_left, lawCov_neg_right_eq, neg_neg]
    simp_rw [e]
    exact (lintegral_sqrt_raySpeedSq_lt_top_iff_tilt hS ν vM 0 u).2 hray

/-- **Facet accessibility**: on a charged polytope with an exposed facet, a point of the relative
interior of the facet is reached by some `C¹` path of finite Fisher length in the direction space
iff the normal ray has finite Fisher length. -/
theorem facet_fisher_access_iff {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β)
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) :
    (∃ η η' : ℝ → J → ℝ, (∀ s, η s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) ∧
      (∀ s, 0 ≤ s → HasDerivAt η (η' s) s) ∧ ContinuousOn η' (Ici 0) ∧
      Tendsto (fun s ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η s)) atTop (𝓝 M) ∧
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
        (√(lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η s))
          (dirLoss S (η' s)) (dirLoss S (η' s))))) < ⊤) ↔
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) u r))) < ⊤ := by
  constructor
  · rintro ⟨η, η', hη, hd, hd', hlim, hI⟩
    exact lintegral_sqrt_raySpeedSq_lt_top_of_path hS ν V hpoly hcharged hV hM hMβ hF hMint hv₀V
      hv₀β hzV hz huW hu hT hη hd hd' hlim hI
  · intro hray
    obtain ⟨η, η', hη, hd, hd', hlim, hI⟩ := exists_path_of_lintegral_sqrt_raySpeedSq_lt_top hS ν
      V hpoly hcharged hV hMint hv₀V hv₀β huW hray
    exact ⟨η, η', hη, fun s _ ↦ hd s, hd'.continuousOn, hlim, hI⟩

end Converse

end Laplace.Multi
