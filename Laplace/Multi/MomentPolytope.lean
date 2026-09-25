/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MeanMapEmbedding
import Laplace.Multi.NaturalCoordinates

/-!
# The moment-polytope theorem: the image of the response chart

On a finite alphabet with a positive prior and a nondegenerate statistic `S : J → X → ℝ` (no
nonzero direction `v` with `S_v` constant), the mean map `η(θ) = E_θ[S]` of the exponential family
`P_θ ∝ π e^{-⟨θ,S⟩}` is an open embedding of natural-parameter space (`MeanMapEmbedding`) whose
image is exactly the interior of the moment polytope `conv{S(x) : x ∈ X}`:

  `range η = interior (convexHull ℝ (range S))`   (`range_meanMap_eq_interior_convexHull`).

The inclusion `⊆` is the open-map theorem together with `η(θ) ∈ conv S(X)`; the inclusion `⊇` is the
variational argument: for `x` in the interior, `θ ↦ ψ(θ) + ⟨θ, x⟩` is coercive
(`ψ(θ) + ⟨θ,x⟩ ≥ log π_min + (δ/2)‖θ‖`, from the supporting half-space inequality
`ψ(θ) ≥ log π_min − ⟨θ, y⟩` for every `y` in the polytope), hence attains its minimum, and at the
minimiser the first-order condition reads `η(θ*) = x`. Applied to the augmented statistic
`S = (L₀, R)` of `NaturalCoordinates` this is the global description of the response chart of the
joint family of temperature and data: every interior point of the moment polytope is realised by
exactly one posterior, and the boundary faces are the endpoints of the natural rays
(`FiniteEndpoint`).
-/

open MeasureTheory Filter Topology Set

-- `Measure.count` and `integral_count` need `Fintype X` although the statements do not mention it.
set_option linter.unusedFintypeInType false

namespace Laplace.Multi

section

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J]

/-- The statistic as a map into the parameter space. -/
def statPoint (S : J → X → ℝ) (x : X) : J → ℝ := fun j ↦ S j x

/-- The dot product on `J → ℝ`. -/
def dotJ (θ y : J → ℝ) : ℝ := ∑ j, θ j * y j

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] in
theorem isLinearMap_dotJ (θ : J → ℝ) : IsLinearMap ℝ (dotJ θ) where
  map_add a b := by simp [dotJ, mul_add, Finset.sum_add_distrib]
  map_smul c a := by simp [dotJ, Finset.mul_sum, mul_left_comm]

/-- The smallest prior weight. -/
noncomputable def piMin (π : X → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty π

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty J] in
theorem piMin_le (π : X → ℝ) (x : X) : piMin π ≤ π x := Finset.inf'_le _ (Finset.mem_univ x)

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty J] in
theorem piMin_pos {π : X → ℝ} (hπ : ∀ x, 0 < π x) : 0 < piMin π :=
  (Finset.lt_inf'_iff _).2 fun x _ ↦ hπ x

variable {π : X → ℝ} (hπ : ∀ x, 0 < π x) (S : J → X → ℝ)
include hπ

/-! ### The finite-alphabet instance of the affine-family hypotheses -/

omit [Nonempty J] in
theorem count_hπpos : 0 < ∫ x, π x ∂(Measure.count : Measure X) := by
  rw [integral_count]
  exact Finset.sum_pos (fun x _ ↦ hπ x) Finset.univ_nonempty

omit hπ [Fintype J] [Nonempty J] in
theorem bdd_finite (j : J) : Bdd (S j) := by
  obtain ⟨x₀, _, hx₀⟩ := Finset.exists_max_image Finset.univ (fun x ↦ |S j x|) Finset.univ_nonempty
  exact ⟨measurable_of_finite _, |S j x₀|, fun x ↦ hx₀ x (Finset.mem_univ x)⟩

omit hπ [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] in
theorem zero_bdd : ∀ x : X, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun _ ↦ by simp

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] in
/-- The nondegeneracy hypothesis of the finite alphabet in the a.e. form the embedding theorem
wants. -/
theorem hnd_count (hnd : ∀ v : J → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ x, dirLoss S v x = c) :
    ∀ v : J → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂(Measure.count : Measure X), π x ≠ 0 →
      dirLoss S v x = c := by
  intro v hv ⟨c, hc⟩
  rw [Measure.ae_count_iff] at hc
  exact hnd v hv ⟨c, fun x ↦ hc x (hπ x).ne'⟩

/-! ### The mean map lands in the polytope -/

omit [Nonempty X] [Nonempty J] hπ in
/-- `η(θ) = ∑ₓ w_θ(x) S(x)` with the posterior weights. -/
theorem meanMap_eq_sum_weights (θ : J → ℝ) :
    meanMap Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ =
      ∑ x, (Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * π x /
        priorZ Measure.count π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1) • statPoint S x := by
  funext j
  unfold meanMap priorExp
  rw [integral_count, Finset.sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul, statPoint]
  ring

omit [Nonempty J] in
theorem priorZ_count_pos (θ : J → ℝ) :
    0 < priorZ Measure.count π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 := by
  unfold priorZ
  rw [integral_count]
  exact Finset.sum_pos (fun x _ ↦ by have := hπ x; positivity) Finset.univ_nonempty

omit [Nonempty J] in
/-- The mean map lands in the moment polytope. -/
theorem meanMap_mem_convexHull (θ : J → ℝ) :
    meanMap Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ ∈ convexHull ℝ (Set.range (statPoint S)) := by
  rw [meanMap_eq_sum_weights S θ]
  have hZ := priorZ_count_pos hπ S θ
  refine (convex_convexHull ℝ _).sum_mem (fun x _ ↦ by have := hπ x; positivity) ?_
    fun x _ ↦ subset_convexHull ℝ _ ⟨x, rfl⟩
  rw [← Finset.sum_div, div_eq_one_iff_eq hZ.ne']
  unfold priorZ
  rw [integral_count]

/-! ### Coercivity of the variational functional -/

omit [Nonempty J] in
/-- The supporting half-space inequality: `ψ(θ) ≥ log π_min − ⟨θ, y⟩` for every `y` in the
polytope. -/
theorem affLogZ_ge_of_mem_convexHull (θ : J → ℝ) {y : J → ℝ}
    (hy : y ∈ convexHull ℝ (Set.range (statPoint S))) :
    Real.log (piMin π) - dotJ θ y ≤ affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ := by
  -- every atom satisfies the bound, and the bound is a half-space
  set c := Real.log (piMin π) - affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ with hc
  have hsub : Set.range (statPoint S) ⊆ {w | c ≤ dotJ θ w} := by
    rintro _ ⟨x₀, rfl⟩
    change c ≤ dotJ θ (statPoint S x₀)
    rw [hc, sub_le_iff_le_add]
    unfold affLogZ priorZ
    rw [integral_count]
    have hterm : piMin π * Real.exp (-(dotJ θ (statPoint S x₀))) ≤
        ∑ x, Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * π x := by
      have e : affLoss (fun _ ↦ (0 : ℝ)) S θ x₀ = dotJ θ (statPoint S x₀) := by
        simp [affLoss, dotJ, statPoint]
      calc piMin π * Real.exp (-(dotJ θ (statPoint S x₀)))
          ≤ π x₀ * Real.exp (-(dotJ θ (statPoint S x₀))) :=
            mul_le_mul_of_nonneg_right (piMin_le π x₀) (Real.exp_pos _).le
        _ = Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x₀)) * π x₀ := by
            rw [e, one_mul, mul_comm]
        _ ≤ ∑ x, Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * π x :=
            Finset.single_le_sum (f := fun x ↦ Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) *
              π x) (fun x _ ↦ by have := hπ x; positivity) (Finset.mem_univ x₀)
    have hpm := piMin_pos hπ
    have := Real.log_le_log (by positivity) hterm
    rw [Real.log_mul hpm.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    linarith
  have := convexHull_min hsub (convex_halfSpace_ge (isLinearMap_dotJ θ) c) hy
  simp only [mem_ofPred_eq] at this
  rw [hc] at this
  linarith

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hπ in
theorem dotJ_add_left (a b y : J → ℝ) : dotJ (a + b) y = dotJ a y + dotJ b y := by
  simp [dotJ, add_mul, Finset.sum_add_distrib]

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hπ in
theorem dotJ_smul_left (c : ℝ) (a y : J → ℝ) : dotJ (c • a) y = c * dotJ a y := by
  simp [dotJ, Finset.mul_sum, mul_assoc]

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hπ in
theorem dotJ_single_left [DecidableEq J] (j : J) (y : J → ℝ) : dotJ (Pi.single j 1) y = y j := by
  simp only [dotJ]
  rw [Finset.sum_eq_single j (fun i _ hi ↦ by simp [hi]) (by simp)]
  simp

/-- **Coercivity**: for `x` with `ball x δ ⊆ conv S(X)`,
`ψ(θ) + ⟨θ, x⟩ ≥ log(∑π) − log card X + (δ/2)‖θ‖`. -/
theorem coercive_bound {x : J → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball x δ ⊆ convexHull ℝ (Set.range (statPoint S))) (θ : J → ℝ) :
    Real.log (piMin π) + δ / 2 * ‖θ‖ ≤
      affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x := by
  classical
  -- the coordinate of largest modulus
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j ↦ |θ j|) Finset.univ_nonempty
  have hnorm : ‖θ‖ ≤ |θ j₀| :=
    (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j ↦ by
      rw [Real.norm_eq_abs]; exact hj₀ j (Finset.mem_univ j)
  -- the sign of the leading coordinate
  set sgn : ℝ := if 0 ≤ θ j₀ then 1 else -1 with hsgn
  have hsgn1 : |sgn| = 1 := by rw [hsgn]; split_ifs <;> simp
  have hsgnmul : sgn * θ j₀ = |θ j₀| := by
    rw [hsgn]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.1 h)]; ring
  -- the test point `y = x − (δ/2) sgn e_{j₀}`
  obtain ⟨y, hy⟩ : ∃ y : J → ℝ, y = x - (δ / 2 * sgn) • Pi.single j₀ 1 := ⟨_, rfl⟩
  have hymem : y ∈ convexHull ℝ (Set.range (statPoint S)) := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, hy, sub_sub_cancel_left, norm_neg, norm_smul,
      Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_mul, hsgn1, mul_one,
      abs_of_pos (half_pos hδ)]
    linarith
  have hlin := isLinearMap_dotJ θ
  have hdot : dotJ θ x - dotJ θ y = δ / 2 * |θ j₀| := by
    rw [hy, hlin.map_sub, hlin.map_smul, sub_sub_cancel, smul_eq_mul]
    simp only [dotJ]
    rw [Finset.sum_eq_single j₀ (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp only [Pi.single_eq_same, mul_one]
    rw [mul_assoc, hsgnmul]
  have h := affLogZ_ge_of_mem_convexHull hπ S θ hymem
  have : δ / 2 * ‖θ‖ ≤ δ / 2 * |θ j₀| := mul_le_mul_of_nonneg_left hnorm (by positivity)
  linarith

/-! ### The variational functional attains its minimum -/

omit [Nonempty J] in
theorem continuous_affLogZ_count : Continuous (affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1) := by
  have hL : ∀ x, Continuous (fun θ : J → ℝ ↦ affLoss (fun _ ↦ (0 : ℝ)) S θ x) := fun x ↦ by
    have e : (fun θ : J → ℝ ↦ affLoss (fun _ ↦ (0 : ℝ)) S θ x) = fun θ ↦ ∑ j, θ j * S j x := by
      funext θ; simp [affLoss]
    rw [e]
    exact continuous_finsetSum _ fun j _ ↦ (continuous_apply j).mul continuous_const
  have hZ : Continuous
      (fun θ : J → ℝ ↦ priorZ Measure.count π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1) := by
    have e : (fun θ : J → ℝ ↦ priorZ Measure.count π (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1) =
        fun θ ↦ ∑ x, Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * π x := by
      funext θ; unfold priorZ; rw [integral_count]
    rw [e]
    exact continuous_finsetSum _ fun x _ ↦
      (Real.continuous_exp.comp ((hL x).const_mul 1).neg).mul continuous_const
  exact hZ.log fun θ ↦ (priorZ_count_pos hπ S θ).ne'

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hπ in
theorem continuous_dotJ_left (y : J → ℝ) : Continuous (fun θ : J → ℝ ↦ dotJ θ y) :=
  continuous_finsetSum _ fun j _ ↦ (continuous_apply j).mul continuous_const

/-- The variational functional `θ ↦ ψ(θ) + ⟨θ, x⟩` attains its minimum when `x` is interior. -/
theorem exists_min_variational {x : J → ℝ}
    (hx : x ∈ interior (convexHull ℝ (Set.range (statPoint S)))) :
    ∃ θ₀ : J → ℝ, ∀ θ, affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ₀ + dotJ θ₀ x ≤
      affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨δ, hδ, hball⟩ := hx
  have hcont : Continuous (fun θ : J → ℝ ↦ affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ +
      dotJ θ x) := (continuous_affLogZ_count hπ S).add (continuous_dotJ_left x)
  refine hcont.exists_forall_le ?_
  have hlim : Tendsto (fun θ : J → ℝ ↦ Real.log (piMin π) + δ / 2 * ‖θ‖) (cocompact _) atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_norm_cocompact_atTop.const_mul_atTop (by positivity))
  exact tendsto_atTop_mono (coercive_bound hπ S hδ hball) hlim

omit [Nonempty J] in
/-- The first-order condition at a minimiser: `η(θ₀) = x`. -/
theorem meanMap_eq_of_min {x θ₀ : J → ℝ}
    (hmin : ∀ θ, affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ₀ + dotJ θ₀ x ≤
      affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ + dotJ θ x) :
    meanMap Measure.count π (fun _ ↦ (0 : ℝ)) S 1 θ₀ = x := by
  classical
  have hπ' : ∀ x, 0 ≤ π x := fun x ↦ (hπ x).le
  obtain ⟨hLm, ML, hLb⟩ := bdd_affLoss (L₀ := fun _ : X ↦ (0 : ℝ)) measurable_const
    (zero_bdd (X := X)) (bdd_finite S) θ₀
  have hT : TiltData Measure.count (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) 1)
      (fun _ ↦ 0) 0 :=
    tiltData_baseWeight_of_bounded Measure.count (measurable_of_finite π) Integrable.of_finite hπ'
      (count_hπpos hπ) hLm hLb measurable_const (fun _ ↦ by simp) 1
  funext j
  -- the directional derivative of the functional along `e_j` vanishes
  set v : J → ℝ := Pi.single j 1 with hv
  have hψ := hT.hasDerivAt_affLogZ_dir' (bdd_finite S) v
  have hd : HasDerivAt (fun ε : ℝ ↦ dotJ (θ₀ + ε • v) x) (dotJ v x) 0 := by
    have e : (fun ε : ℝ ↦ dotJ (θ₀ + ε • v) x) = fun ε ↦ dotJ θ₀ x + ε * dotJ v x := by
      funext ε; rw [dotJ_add_left, dotJ_smul_left]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotJ v x)).const_add (dotJ θ₀ x)
  have hsum := hψ.add hd
  have hloc : IsLocalMin (fun ε : ℝ ↦ affLogZ Measure.count π (fun _ ↦ (0 : ℝ)) S 1 (θ₀ + ε • v) +
      dotJ (θ₀ + ε • v) x) 0 := by
    refine Filter.Eventually.of_forall fun ε ↦ ?_
    simp only [zero_smul, add_zero]
    exact hmin _
  have h0 := hloc.hasDerivAt_eq_zero hsum
  rw [hv, dotJ_single_left] at h0
  rw [Finset.sum_eq_single j (fun i _ hi ↦ by simp [hi]) (by simp)] at h0
  simp only [Pi.single_eq_same, one_mul, neg_mul] at h0
  linarith

/-! ### The moment-polytope theorem -/

/-- **The moment-polytope theorem**: on a finite alphabet with a positive prior and a nondegenerate
statistic, the image of the mean map is exactly the interior of the moment polytope. -/
theorem range_meanMap_eq_interior_convexHull
    (hnd : ∀ v : J → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ x, dirLoss S v x = c) :
    Set.range (meanMap Measure.count π (fun _ ↦ (0 : ℝ)) S 1) =
      interior (convexHull ℝ (Set.range (statPoint S))) := by
  refine Set.Subset.antisymm ?_ fun x hx ↦ ?_
  · refine interior_maximal (Set.range_subset_iff.2 fun θ ↦ meanMap_mem_convexHull hπ S θ) ?_
    exact isOpen_range_meanMap (measurable_of_finite π) Integrable.of_finite (fun x ↦ (hπ x).le)
      (count_hπpos hπ) measurable_const (zero_bdd (X := X)) (bdd_finite S) one_pos
      (hnd_count hπ S hnd)
  · obtain ⟨θ₀, hmin⟩ := exists_min_variational hπ S hx
    exact ⟨θ₀, meanMap_eq_of_min hπ S hmin⟩

end

end Laplace.Multi
