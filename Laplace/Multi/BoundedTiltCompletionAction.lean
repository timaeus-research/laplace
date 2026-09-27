/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BoundedTiltFisherComparison
import Laplace.Multi.FisherCompletionMeasure

/-!
# The bounded-tilt action on the Fisher completion

Translation by a direction `h ∈ W` is `e^K`-Lipschitz for the intrinsic distance
(`BoundedTiltFisherComparison`), so it extends to a Lipschitz map `tiltExt h` of the Fisher
completion `Ŵ`, with `tiltExt (−h)` as inverse: **bounded tilts act on the completion**. On the
completion laws the action is exactly exponential tilting,

`Q_{tiltExt h x} = Q_x.tilted (−⟨h,S⟩)`   (`completionLaw_tiltExt`),

proved by continuity of `x ↦ ∫ f dQ_x` for bounded `f` on both sides and the interior identity
`P_{θ+h} = P_θ.tilted (−⟨h,S⟩)`. Consequently the extended mean of `tiltExt h x` is the mean of
the tilted law, and (`AccessibleFaceOrbit`) one accessible face-family law over a face carries
the whole open face family: if `Q_x = P^A_{v₀}` then `Q_{tiltExt (v − v₀) x} = P^A_v` for every
`v ∈ W`, so every face-family mean is an extended mean.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Action

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- Translation of a Fisher point by a direction. -/
noncomputable def tiltPoint (h : 𝕍) (p : FisherPoint hS ν) : FisherPoint hS ν :=
  ⟨⟨(p.param : J → ℝ) + h, Submodule.add_mem _ p.param.2 h.2⟩⟩

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem tiltPoint_param (h : 𝕍) (p : FisherPoint hS ν) :
    ((tiltPoint hS ν h p).param : J → ℝ) = (p.param : J → ℝ) + h := rfl

theorem lipschitzWith_tiltPoint (h : 𝕍) {K : ℝ} (hK : ∀ x, |dirLoss S (h : J → ℝ) x| ≤ K) :
    LipschitzWith (Real.exp K).toNNReal (tiltPoint hS ν h) := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  rw [Real.coe_toNNReal _ (Real.exp_pos K).le, FisherPoint.dist_eq, FisherPoint.dist_eq]
  exact fisherDist_add_le_exp hS ν h.2 hK p.param q.param

theorem uniformContinuous_tiltPoint (h : 𝕍) : UniformContinuous (tiltPoint hS ν h) := by
  obtain ⟨K, hK⟩ := (bdd_dirLoss hS (h : J → ℝ)).2
  exact (lipschitzWith_tiltPoint hS ν h hK).uniformContinuous

/-- **The bounded-tilt action on the completion.** -/
noncomputable def tiltExt (h : 𝕍) : FisherCompletion hS ν → FisherCompletion hS ν :=
  UniformSpace.Completion.map (tiltPoint hS ν h)

theorem tiltExt_coe (h : 𝕍) (p : FisherPoint hS ν) :
    tiltExt hS ν h (p : FisherCompletion hS ν) = (tiltPoint hS ν h p : FisherCompletion hS ν) :=
  UniformSpace.Completion.map_coe (uniformContinuous_tiltPoint hS ν h) p

theorem continuous_tiltExt (h : 𝕍) : Continuous (tiltExt hS ν h) :=
  UniformSpace.Completion.continuous_map

theorem lipschitzWith_tiltExt (h : 𝕍) {K : ℝ} (hK : ∀ x, |dirLoss S (h : J → ℝ) x| ≤ K) :
    LipschitzWith (Real.exp K).toNNReal (tiltExt hS ν h) :=
  (lipschitzWith_tiltPoint hS ν h hK).completion_map

/-- The action is additive in the direction. -/
theorem tiltExt_tiltExt (h h' : 𝕍) (x : FisherCompletion hS ν) :
    tiltExt hS ν h (tiltExt hS ν h' x) = tiltExt hS ν (h' + h) x := by
  refine UniformSpace.Completion.induction_on x ?_ fun p ↦ ?_
  · exact isClosed_eq ((continuous_tiltExt hS ν h).comp (continuous_tiltExt hS ν h'))
      (continuous_tiltExt hS ν _)
  · rw [tiltExt_coe, tiltExt_coe, tiltExt_coe]
    congr 1
    refine FisherPoint.ext (Subtype.ext ?_)
    simp only [tiltPoint_param, Submodule.coe_add]
    abel

theorem tiltExt_zero (x : FisherCompletion hS ν) : tiltExt hS ν 0 x = x := by
  refine UniformSpace.Completion.induction_on x ?_ fun p ↦ ?_
  · exact isClosed_eq (continuous_tiltExt hS ν 0) continuous_id
  · rw [tiltExt_coe]
    congr 1
    exact FisherPoint.ext (Subtype.ext (by simp [tiltPoint_param]))

/-- `tiltExt (−h)` inverts `tiltExt h`. -/
theorem tiltExt_neg_tiltExt (h : 𝕍) (x : FisherCompletion hS ν) :
    tiltExt hS ν (-h) (tiltExt hS ν h x) = x := by
  rw [tiltExt_tiltExt, add_neg_cancel, tiltExt_zero]

end Action

section Laws

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- For bounded `f`, `x ↦ ∫ f dQ_x` is continuous on the completion. -/
theorem continuous_integral_completionLaw {f : X → ℝ} (hf : Bdd f) :
    Continuous fun x : FisherCompletion hS ν ↦ ∫ y, f y ∂completionLaw hS ν x := by
  have e : ∀ x : FisherCompletion hS ν, ∫ y, f y ∂completionLaw hS ν x =
      ∫ y, f y * (rootDensExt hS ν x y * rootDensExt hS ν x y) ∂ν := fun x ↦ by
    rw [integral_completionLaw hS ν x f]
    exact integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)
  simp_rw [e]
  exact (continuous_integral_mul_sq ν hf).comp (continuous_rootDensExt hS ν)

/-- The tilted normaliser is bounded below on the completion. -/
theorem integral_exp_completionLaw_ge (x : FisherCompletion hS ν) {g : X → ℝ} (hg : Bdd g) {K : ℝ}
    (hK : ∀ y, |g y| ≤ K) :
    Real.exp (-K) ≤ ∫ y, Real.exp (g y) ∂completionLaw hS ν x := by
  have hexp : Bdd fun y ↦ Real.exp (g y) := ⟨hg.1.exp, Real.exp K, fun y ↦ by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (abs_le.1 (hK y)).2⟩
  calc Real.exp (-K) = ∫ _, Real.exp (-K) ∂completionLaw hS ν x := by simp
    _ ≤ ∫ y, Real.exp (g y) ∂completionLaw hS ν x :=
        integral_mono (integrable_const _) (integrable_of_bdd_prob _ hexp)
          fun y ↦ Real.exp_le_exp.2 (abs_le.1 (hK y)).1

/-- **The completion action tilts the integrals**: for bounded `f`,
`∫ f dQ_{tiltExt h x} = ∫ f e^{−⟨h,S⟩} dQ_x / ∫ e^{−⟨h,S⟩} dQ_x`. -/
theorem integral_completionLaw_tiltExt (h : 𝕍) (x : FisherCompletion hS ν) {f : X → ℝ}
    (hf : Bdd f) :
    ∫ y, f y ∂completionLaw hS ν (tiltExt hS ν h x) =
      (∫ y, f y * Real.exp (-dirLoss S (h : J → ℝ) y) ∂completionLaw hS ν x) /
        ∫ y, Real.exp (-dirLoss S (h : J → ℝ) y) ∂completionLaw hS ν x := by
  have hgb : Bdd fun y ↦ -dirLoss S (h : J → ℝ) y := bdd_neg (bdd_dirLoss hS _)
  obtain ⟨K, hK⟩ := hgb.2
  have hexp : Bdd fun y ↦ Real.exp (-dirLoss S (h : J → ℝ) y) := ⟨hgb.1.exp, Real.exp K, fun y ↦ by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (abs_le.1 (hK y)).2⟩
  refine UniformSpace.Completion.induction_on x ?_ fun p ↦ ?_
  · refine isClosed_eq ((continuous_integral_completionLaw hS ν hf).comp
      (continuous_tiltExt hS ν h)) ?_
    exact (continuous_integral_completionLaw hS ν (hf.mul hexp)).div
      (continuous_integral_completionLaw hS ν hexp) fun x ↦
        ((Real.exp_pos _).trans_le (integral_exp_completionLaw_ge hS ν x hgb hK)).ne'
  · rw [tiltExt_coe, completionLaw_coe, completionLaw_coe, tiltPoint_param,
      familyMeasure_add_eq_tilted hS ν _ _ 0, integral_tilted]
    simp only [smul_eq_mul, sub_zero]
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    ring

/-- **The completion action is exponential tilting of the completion laws**:
`Q_{tiltExt h x} = Q_x.tilted (−⟨h,S⟩)`. -/
theorem completionLaw_tiltExt (h : 𝕍) (x : FisherCompletion hS ν) :
    completionLaw hS ν (tiltExt hS ν h x) =
      (completionLaw hS ν x).tilted fun y ↦ -dirLoss S (h : J → ℝ) y := by
  ext A hA
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _),
    tilted_apply_eq_ofReal_integral' _ hA,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ by positivity), ← measureReal_def,
    ← integral_indicator_one hA,
    integral_completionLaw_tiltExt hS ν h x (f := A.indicator 1)
      ⟨measurable_one.indicator hA, 1, fun y ↦ by by_cases hy : y ∈ A <;> simp [hy]⟩,
    integral_div]
  congr 1
  rw [← integral_indicator hA]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  by_cases hy : y ∈ A <;> simp [hy]

/-- The extended mean of a tilted point is the mean of the tilted law. -/
theorem meanExt_tiltExt (h : 𝕍) (x : FisherCompletion hS ν) (i : J) :
    meanExt hS ν (tiltExt hS ν h x) i =
      ∫ y, S i y ∂((completionLaw hS ν x).tilted fun y ↦ -dirLoss S (h : J → ℝ) y) := by
  rw [← integral_completionLaw_eq_meanExt, completionLaw_tiltExt]

end Laws

section FaceOrbit

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (A : Set X) [IsProbabilityMeasure (faceMeasure ν A)]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- **One accessible face-family law carries the whole face family**: if `Q_x = P^A_{v₀}` then
`Q_{tiltExt h x} = P^A_{v₀ + h}`. -/
theorem completionLaw_tiltExt_faceFamily (h : 𝕍) (x : FisherCompletion hS ν) {v₀ : J → ℝ}
    (hx : completionLaw hS ν x =
      familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 v₀) :
    completionLaw hS ν (tiltExt hS ν h x) =
      familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀ + h) := by
  rw [completionLaw_tiltExt, hx, familyMeasure_add_eq_tilted hS (faceMeasure ν A) v₀ h 0]
  simp only [sub_zero]

/-- The extended mean of the tilted point is the face-family mean. -/
theorem meanExt_tiltExt_faceFamily (h : 𝕍) (x : FisherCompletion hS ν) {v₀ : J → ℝ}
    (hx : completionLaw hS ν x =
      familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 v₀) :
    meanExt hS ν (tiltExt hS ν h x) =
      meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀ + h) := by
  rw [← mean_familyMeasure_one_zero hS (faceMeasure ν A),
    ← completionLaw_tiltExt_faceFamily hS ν A h x hx]
  funext i
  exact (integral_completionLaw_eq_meanExt hS ν _ i).symm

/-- **Accessibility of the whole open face family**: every face-family mean `m_A(v₀ + h)` is an
extended mean once one face-family law is a completion law. -/
theorem exists_meanExt_eq_faceFamily (x : FisherCompletion hS ν) {v₀ : J → ℝ}
    (hx : completionLaw hS ν x =
      familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 v₀) (h : 𝕍) :
    ∃ x' : FisherCompletion hS ν, meanExt hS ν x' =
      meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀ + h) :=
  ⟨tiltExt hS ν h x, meanExt_tiltExt_faceFamily hS ν A h x hx⟩

end FaceOrbit

end Laplace.Multi
