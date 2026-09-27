/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSimplexSphere
import Laplace.Multi.FisherTopology
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# The Fisher completion of a saturated finite family is the spherical closed simplex

The sphere theorem (`ResponseSimplexSphere`) identifies the Fisher distance of a saturated finite
family with the spherical distance `2 arccos ∑_x √(p_x q_x)` of the laws. Here the missing boundary
laws are given their geometric home:

* `SphSimplex X` is the **closed** probability simplex on `X` with the spherical (Fisher–Rao)
  metric `dist p q = 2 ∠(√p, √q) = 2 arccos ∑_x √(p_x q_x)` (`SphSimplex.dist_eq`), a metric space
  by the triangle inequality for angles; the root map `p ↦ √p` is a bi-Lipschitz embedding into the
  unit sphere of `ℝ^X` (`dist_rootVec_le`, `le_dist_rootVec`), so the spherical simplex is
  **compact** (`SphSimplex.compactSpace`), of diameter `π` attained at distinct Dirac laws
  (`SphSimplex.dist_le_pi`, `SphSimplex.dist_dirac`), and its positive part is dense
  (`SphSimplex.dense_pos`);
* the response-to-law map `θ ↦ B(θ)` is an isometry of the Fisher space into the spherical simplex
  (`isometry_toSph`) whose range is the open simplex (`range_toSph`);
* **the completion theorem** (`fisherCompletionIso`): the intrinsic Fisher completion of a
  saturated finite family is isometric to the spherical closed simplex, `Ŵ ≃ᵢ Δ̄(X)`; hence the
  Fisher completion is compact (`compactSpace_fisherCompletion`) and every completion point is a
  law on `X`, the boundary points being exactly the laws that lose an atom.
-/

open MeasureTheory Filter Topology InnerProductGeometry

namespace Laplace.Multi

section SphSimplex

variable (X : Type*) [Fintype X]

/-- The closed probability simplex on a finite set, to carry the spherical metric. -/
@[ext]
structure SphSimplex where
  /-- The law. -/
  law : X → ℝ
  nonneg : ∀ x, 0 ≤ law x
  sum_one : ∑ x, law x = 1

namespace SphSimplex

variable {X}

/-- The root vector `√p ∈ ℝ^X`. -/
noncomputable def rootVec (p : SphSimplex X) : EuclideanSpace ℝ X :=
  WithLp.toLp 2 fun x ↦ √(p.law x)

theorem rootVec_apply (p : SphSimplex X) (x : X) : rootVec p x = √(p.law x) := rfl

theorem inner_rootVec (p q : SphSimplex X) :
    inner ℝ (rootVec p) (rootVec q) = ∑ x, √(p.law x) * √(q.law x) := by
  unfold rootVec
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun x _ ↦ mul_comm _ _

theorem sum_sq_rootVec (p : SphSimplex X) : ∑ x, rootVec p x ^ 2 = 1 := by
  rw [← p.sum_one]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [rootVec_apply, Real.sq_sqrt (p.nonneg x)]

theorem norm_rootVec (p : SphSimplex X) : ‖rootVec p‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have : ∑ x, ‖rootVec p x‖ ^ 2 = 1 := by
    rw [← sum_sq_rootVec p]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [Real.norm_eq_abs, sq_abs]
  rw [this, Real.sqrt_one]

theorem rootVec_ne_zero (p : SphSimplex X) : rootVec p ≠ 0 := by
  intro h
  have := norm_rootVec p
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem rootVec_injective : Function.Injective (rootVec (X := X)) := by
  intro p q h
  ext x
  have hx := congrArg (fun y : EuclideanSpace ℝ X ↦ y x) h
  simp only [rootVec_apply] at hx
  exact (Real.sqrt_inj (p.nonneg x) (q.nonneg x)).1 hx

/-- **The spherical metric** `dist p q = 2 ∠(√p, √q)`. -/
noncomputable instance : MetricSpace (SphSimplex X) where
  dist p q := 2 * angle (rootVec p) (rootVec q)
  dist_self p := by
    rw [angle_self (rootVec_ne_zero p), mul_zero]
  dist_comm p q := by
    rw [angle_comm]
  dist_triangle p q r := by
    have := angle_le_angle_add_angle (rootVec p) (rootVec q) (rootVec r)
    linarith
  eq_of_dist_eq_zero := by
    intro p q h
    change 2 * angle (rootVec p) (rootVec q) = 0 at h
    have h' : angle (rootVec p) (rootVec q) = 0 := by linarith
    obtain ⟨-, r, hr, hq⟩ := angle_eq_zero_iff.1 h'
    have hn := congrArg norm hq
    rw [norm_smul, norm_rootVec, norm_rootVec, Real.norm_eq_abs, abs_of_pos hr, mul_one] at hn
    rw [← hn, one_smul] at hq
    exact rootVec_injective hq.symm

theorem dist_def (p q : SphSimplex X) : dist p q = 2 * angle (rootVec p) (rootVec q) := rfl

/-- `dist p q = 2 arccos ∑_x √(p_x q_x)`. -/
theorem dist_eq (p q : SphSimplex X) :
    dist p q = 2 * Real.arccos (∑ x, √(p.law x) * √(q.law x)) := by
  rw [dist_def]
  unfold angle
  rw [inner_rootVec, norm_rootVec, norm_rootVec, mul_one, div_one]

/-- The spherical simplex has diameter at most `π`. -/
theorem dist_le_pi (p q : SphSimplex X) : dist p q ≤ Real.pi := by
  rw [dist_eq]
  have h0 : 0 ≤ ∑ x, √(p.law x) * √(q.law x) :=
    Finset.sum_nonneg fun x _ ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have := Real.arccos_le_pi_div_two.2 h0
  linarith

/-- The Dirac law at a point: a vertex of the simplex. -/
def dirac [DecidableEq X] (x₀ : X) : SphSimplex X where
  law := fun x ↦ if x = x₀ then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_one := by simp

/-- **Distinct vertices are at distance `π`**: the diameter is attained. -/
theorem dist_dirac [DecidableEq X] {x y : X} (hxy : x ≠ y) :
    dist (dirac x) (dirac y) = Real.pi := by
  rw [dist_eq]
  have : ∑ z, √((dirac x).law z) * √((dirac y).law z) = 0 := by
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    simp only [dirac]
    by_cases hz : z = x
    · subst hz
      rw [if_neg hxy, Real.sqrt_zero, mul_zero]
    · rw [if_neg hz, Real.sqrt_zero, zero_mul]
  rw [this, Real.arccos_zero]
  ring

theorem norm_sub_rootVec_sq (p q : SphSimplex X) :
    ‖rootVec p - rootVec q‖ ^ 2 = 2 - 2 * Real.cos (angle (rootVec p) (rootVec q)) := by
  rw [norm_sub_sq_real, cos_angle, norm_rootVec, norm_rootVec, mul_one, div_one]
  ring

/-- **The chord is at most the arc**: `‖√p − √q‖ ≤ dist p q`. -/
theorem dist_rootVec_le (p q : SphSimplex X) : dist (rootVec p) (rootVec q) ≤ dist p q := by
  rw [dist_eq_norm, dist_def]
  have h1 := norm_sub_rootVec_sq p q
  have h2 := Real.one_sub_sq_div_two_le_cos (x := angle (rootVec p) (rootVec q))
  have h3 := angle_nonneg (rootVec p) (rootVec q)
  have h4 : ‖rootVec p - rootVec q‖ ^ 2 ≤ (2 * angle (rootVec p) (rootVec q)) ^ 2 := by
    rw [h1]
    nlinarith
  have := Real.sqrt_le_sqrt h4
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by linarith)] at this

/-- **The arc is at most `π` times the chord**: `dist p q ≤ π ‖√p − √q‖` (the root vectors are
unit vectors, the Fisher sphere has radius `2`). -/
theorem le_dist_rootVec (p q : SphSimplex X) :
    dist p q ≤ Real.pi * dist (rootVec p) (rootVec q) := by
  rw [dist_eq_norm, dist_def]
  have h0 : 0 ≤ angle (rootVec p) (rootVec q) := angle_nonneg _ _
  have hπ : angle (rootVec p) (rootVec q) ≤ Real.pi := angle_le_pi _ _
  have hpi := Real.pi_pos
  have h1 : ‖rootVec p - rootVec q‖ ^ 2 =
      (2 * Real.sin (angle (rootVec p) (rootVec q) / 2)) ^ 2 := by
    rw [norm_sub_rootVec_sq]
    conv_lhs => rw [show angle (rootVec p) (rootVec q) =
      2 * (angle (rootVec p) (rootVec q) / 2) by ring]
    rw [Real.cos_two_mul, Real.cos_sq']
    ring
  have hj := Real.mul_le_sin (x := angle (rootVec p) (rootVec q) / 2) (by linarith) (by linarith)
  have hs : 0 ≤ Real.sin (angle (rootVec p) (rootVec q) / 2) :=
    le_trans (by positivity) hj
  have hn : ‖rootVec p - rootVec q‖ = 2 * Real.sin (angle (rootVec p) (rootVec q) / 2) := by
    have := congrArg Real.sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by linarith)] at this
  rw [hn]
  have key : angle (rootVec p) (rootVec q) ≤
      Real.pi * Real.sin (angle (rootVec p) (rootVec q) / 2) := by
    have := mul_le_mul_of_nonneg_left hj hpi.le
    rwa [show Real.pi * (2 / Real.pi * (angle (rootVec p) (rootVec q) / 2)) =
      angle (rootVec p) (rootVec q) by field_simp] at this
  linarith

theorem lipschitzWith_rootVec : LipschitzWith 1 (rootVec (X := X)) :=
  LipschitzWith.of_dist_le_mul fun p q ↦ by
    rw [NNReal.coe_one, one_mul]
    exact dist_rootVec_le p q

theorem antilipschitzWith_rootVec :
    AntilipschitzWith ⟨Real.pi, Real.pi_pos.le⟩ (rootVec (X := X)) :=
  AntilipschitzWith.of_le_mul_dist fun p q ↦ le_dist_rootVec p q

theorem isUniformInducing_rootVec : IsUniformInducing (rootVec (X := X)) :=
  antilipschitzWith_rootVec.isUniformInducing lipschitzWith_rootVec.uniformContinuous

/-- The root vectors are exactly the nonnegative unit vectors. -/
theorem range_rootVec : Set.range (rootVec (X := X)) =
    {y : EuclideanSpace ℝ X | (∀ x, 0 ≤ y x) ∧ ∑ x, y x ^ 2 = 1} := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨fun x ↦ Real.sqrt_nonneg _, sum_sq_rootVec p⟩
  · rintro ⟨hy0, hy1⟩
    refine ⟨⟨fun x ↦ y x ^ 2, fun x ↦ sq_nonneg _, hy1⟩, ?_⟩
    ext x
    rw [rootVec_apply]
    exact Real.sqrt_sq (hy0 x)

theorem isClosed_range_rootVec : IsClosed (Set.range (rootVec (X := X))) := by
  rw [range_rootVec, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter (isClosed_iInter fun x ↦ isClosed_le continuous_const
    (PiLp.continuous_apply 2 (fun _ : X ↦ ℝ) x)) (isClosed_eq ?_ continuous_const)
  exact continuous_finsetSum _ fun x _ ↦ (PiLp.continuous_apply 2 (fun _ : X ↦ ℝ) x).pow 2

theorem isCompact_range_rootVec : IsCompact (Set.range (rootVec (X := X))) :=
  (isCompact_sphere (0 : EuclideanSpace ℝ X) 1).of_isClosed_subset isClosed_range_rootVec
    (by
      rintro _ ⟨p, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      exact norm_rootVec p)

/-- **The spherical closed simplex is compact.** -/
instance compactSpace : CompactSpace (SphSimplex X) := by
  refine ⟨?_⟩
  rw [isUniformInducing_rootVec.isInducing.isCompact_iff, Set.image_univ]
  exact isCompact_range_rootVec

/-- The positive part of the simplex. -/
def pos : Set (SphSimplex X) := {p | ∀ x, 0 < p.law x}

/-- The mixture `(1 − δ) p + δ u` with the uniform law. -/
noncomputable def mix [Nonempty X] (p : SphSimplex X) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    SphSimplex X where
  law := fun x ↦ (1 - δ) * p.law x + δ / Fintype.card X
  nonneg x :=
    add_nonneg (mul_nonneg (by linarith) (p.nonneg x)) (div_nonneg h0 (Nat.cast_nonneg _))
  sum_one := by
    have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, p.sum_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp
    ring

theorem mix_mem_pos [Nonempty X] (p : SphSimplex X) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (hδ : 0 < δ) :
    mix p h0 h1 ∈ pos := fun x ↦
  add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (p.nonneg x))
    (div_pos hδ (by exact_mod_cast Fintype.card_pos))

theorem step_mem (k : ℕ) : (0 : ℝ) < 1 / (k + 2) ∧ (1 : ℝ) / (k + 2) ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

/-- The mixtures `(1 − 1/(k+2)) p + u/(k+2)`, a positive sequence converging to `p`. -/
noncomputable def mixSeq [Nonempty X] (p : SphSimplex X) (k : ℕ) : SphSimplex X :=
  mix p (step_mem k).1.le (step_mem k).2

theorem tendsto_step : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 2)) atTop (𝓝 0) := by
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine (h0.comp (tendsto_add_atTop_nat 1)).congr fun k ↦ ?_
  simp only [Function.comp_apply]
  push_cast
  ring_nf

theorem tendsto_mixSeq [Nonempty X] (p : SphSimplex X) : Tendsto (mixSeq p) atTop (𝓝 p) := by
  have h : Tendsto (fun k ↦ rootVec (mixSeq p k)) atTop (𝓝 (rootVec p)) := by
    unfold rootVec
    refine ((PiLp.continuous_toLp 2 (fun _ : X ↦ ℝ)).tendsto _).comp
      (tendsto_pi_nhds.2 fun x ↦ (Real.continuous_sqrt.tendsto _).comp ?_)
    simp only [mixSeq, mix]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_step).mul
      (tendsto_const_nhds (x := p.law x)) |>.add (tendsto_step.div_const (Fintype.card X : ℝ))
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ le_dist_rootVec _ _) ?_
  have := (tendsto_iff_dist_tendsto_zero.1 h).const_mul Real.pi
  simpa using this

/-- **The positive laws are dense in the spherical closed simplex.** -/
theorem dense_pos [Nonempty X] : Dense (pos (X := X)) := fun p ↦
  mem_closure_of_tendsto (tendsto_mixSeq p)
    (Eventually.of_forall fun k ↦ mix_mem_pos p _ _ (step_mem k).1)

end SphSimplex

end SphSimplex

section Completion

variable {X : Type*} [MeasurableSpace X] [Nonempty X] [Fintype X] [MeasurableSingletonClass X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} ≠ 0) (hspan : SpansAffine S ν)
include hS hν

/-- The response as a law: `θ ↦ B(θ)`, into the spherical simplex. -/
noncomputable def toSph (θ : FisherPoint hS ν) : SphSimplex X where
  law := atomMass S ν (θ.param : J → ℝ)
  nonneg x := (atomMass_pos hS ν hν _ x).le
  sum_one := sum_atomMass hS ν _

include hspan in
/-- **The response-to-law map is an isometry** of the Fisher space into the spherical simplex. -/
theorem isometry_toSph : Isometry (toSph hS ν hν) :=
  Isometry.of_dist_eq fun θ₀ θ₁ ↦ by
    rw [SphSimplex.dist_eq, FisherPoint.dist_eq, fisherDist_eq_two_arccos hS ν hν hspan]
    rfl

include hspan in
/-- The responses are exactly the positive laws. -/
theorem range_toSph : Set.range (toSph hS ν hν) = SphSimplex.pos := by
  ext p
  constructor
  · rintro ⟨θ, rfl⟩ x
    exact atomMass_pos hS ν hν _ x
  · intro hp
    refine ⟨⟨simplexInv hS ν hν hspan p.law⟩, ?_⟩
    ext x
    change atomMass S ν (simplexInv hS ν hν hspan p.law : J → ℝ) x = p.law x
    rw [atomMass_simplexInv hS ν hν hspan ⟨hp, p.sum_one⟩]

/-- The extension of the response-to-law map to the Fisher completion. -/
noncomputable def completionToSph : FisherCompletion hS ν → SphSimplex X :=
  UniformSpace.Completion.extension (toSph hS ν hν)

include hspan in
theorem isometry_completionToSph : Isometry (completionToSph hS ν hν) :=
  (isometry_toSph hS ν hν hspan).completion_extension

include hspan in
theorem completionToSph_coe (θ : FisherPoint hS ν) :
    completionToSph hS ν hν θ = toSph hS ν hν θ :=
  UniformSpace.Completion.extension_coe (isometry_toSph hS ν hν hspan).uniformContinuous θ

include hspan in
/-- The extended map is onto: its range is closed and contains the dense positive part. -/
theorem surjective_completionToSph : Function.Surjective (completionToSph hS ν hν) := by
  have hclosed : IsClosed (Set.range (completionToSph hS ν hν)) :=
    (isometry_completionToSph hS ν hν hspan).isClosedEmbedding.isClosed_range
  have hsub : SphSimplex.pos ⊆ Set.range (completionToSph hS ν hν) := by
    rw [← range_toSph hS ν hν hspan]
    rintro _ ⟨θ, rfl⟩
    exact ⟨θ, completionToSph_coe hS ν hν hspan θ⟩
  have : Set.range (completionToSph hS ν hν) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← SphSimplex.dense_pos.closure_eq]
    exact closure_minimal hsub hclosed
  exact Set.range_eq_univ.1 this

include hspan in
/-- **THE COMPLETION THEOREM**: the intrinsic Fisher completion of a saturated finite family is
isometric to the spherical closed simplex `Δ̄(X)` with `dist p q = 2 arccos ∑_x √(p_x q_x)`. -/
noncomputable def fisherCompletionIso : FisherCompletion hS ν ≃ᵢ SphSimplex X where
  toEquiv := Equiv.ofBijective (completionToSph hS ν hν)
    ⟨(isometry_completionToSph hS ν hν hspan).injective, surjective_completionToSph hS ν hν hspan⟩
  isometry_toFun := isometry_completionToSph hS ν hν hspan

include hspan in
theorem fisherCompletionIso_apply (x : FisherCompletion hS ν) :
    fisherCompletionIso hS ν hν hspan x = completionToSph hS ν hν x := rfl

set_option linter.unusedFintypeInType false in
include hspan in
/-- **The Fisher completion of a saturated finite family is compact.** -/
theorem compactSpace_fisherCompletion : CompactSpace (FisherCompletion hS ν) :=
  (fisherCompletionIso hS ν hν hspan).toHomeomorph.symm.compactSpace

set_option linter.unusedFintypeInType false in
include hspan in
/-- The Fisher completion has diameter at most `π`. -/
theorem dist_fisherCompletion_le_pi (x y : FisherCompletion hS ν) : dist x y ≤ Real.pi := by
  rw [← (isometry_completionToSph hS ν hν hspan).dist_eq]
  exact SphSimplex.dist_le_pi _ _

end Completion

end Laplace.Multi
