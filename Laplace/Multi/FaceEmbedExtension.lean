/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AccessibleFaceNonexpansion
import Laplace.Multi.PathEnergy

/-!
# The face embedding extends to the face completion

The nonexpansive face embedding `j_A : W_A → Ŵ` of `AccessibleFaceNonexpansion` is `1`-Lipschitz
for the face Fisher metric, so it extends uniquely to a `1`-Lipschitz map of completions

`ĵ_A : Ŵ_A → Ŵ`   (`faceEmbedExt`, `lipschitzWith_faceEmbedExt`),

and the **mean diagrams commute**: `meanExt ∘ ĵ_A = meanExt_A` (`meanExt_faceEmbedExt`, by density
from `Q_{j_A w} = P^A_w`). Consequently **intrinsic face accessibility transfers to ambient
accessibility**: every extended mean of the face completion is an extended mean of `Ŵ`
(`exists_meanExt_eq_of_faceCompletion`). These are the law, mean and nonexpansion
compatibilities of the coherent nonexpanding boundary atlas; chain compatibility along nested faces
is the next step.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Ext

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (A : Set X) [IsProbabilityMeasure (faceMeasure ν A)] (hA : MeasurableSet A)
  (hp : 0 < ν.real A)
include hS hA hp

/-- The face direction space. -/
local notation "𝕍A" => dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S

/-- The face embedding on face Fisher points. -/
noncomputable def faceEmbedPoint (x₀ : FisherCompletion hS ν) (v₀ : 𝕍A)
    (p : FisherPoint hS (faceMeasure ν A)) : FisherCompletion hS ν :=
  faceEmbed hS ν A hA hp x₀ v₀ p.param

/-- **The face embedding extended to the face completion** `ĵ_A : Ŵ_A → Ŵ`. -/
noncomputable def faceEmbedExt (x₀ : FisherCompletion hS ν) (v₀ : 𝕍A) :
    FisherCompletion hS (faceMeasure ν A) → FisherCompletion hS ν :=
  UniformSpace.Completion.extension (faceEmbedPoint hS ν A hA hp x₀ v₀)

variable {x₀ : FisherCompletion hS ν} {v₀ : dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S}
  (hx₀ : completionLaw hS ν x₀ =
    familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀ : J → ℝ))
include hx₀

theorem lipschitzWith_faceEmbedPoint : LipschitzWith 1 (faceEmbedPoint hS ν A hA hp x₀ v₀) := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  rw [NNReal.coe_one, one_mul, FisherPoint.dist_eq]
  exact dist_faceEmbed_le hS ν A hA hp hx₀ p.param q.param

theorem faceEmbedExt_coe (p : FisherPoint hS (faceMeasure ν A)) :
    faceEmbedExt hS ν A hA hp x₀ v₀ (p : FisherCompletion hS (faceMeasure ν A)) =
      faceEmbed hS ν A hA hp x₀ v₀ p.param :=
  UniformSpace.Completion.extension_coe
    (lipschitzWith_faceEmbedPoint hS ν A hA hp hx₀).uniformContinuous p

/-- **The extended face embedding is `1`-Lipschitz.** -/
theorem lipschitzWith_faceEmbedExt : LipschitzWith 1 (faceEmbedExt hS ν A hA hp x₀ v₀) :=
  (lipschitzWith_faceEmbedPoint hS ν A hA hp hx₀).completion_extension

theorem continuous_faceEmbedExt : Continuous (faceEmbedExt hS ν A hA hp x₀ v₀) :=
  (lipschitzWith_faceEmbedExt hS ν A hA hp hx₀).continuous

/-- The extended mean of an embedded face point is its face mean. -/
theorem meanExt_faceEmbed (w : 𝕍A) :
    meanExt hS ν (faceEmbed hS ν A hA hp x₀ v₀ w) =
      meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (w : J → ℝ) := by
  funext i
  rw [← integral_completionLaw_eq_meanExt hS ν _ i, completionLaw_faceEmbed hS ν A hA hp hx₀ w]
  exact congrFun (mean_familyMeasure_one_zero hS (faceMeasure ν A) (w : J → ℝ)) i

/-- **Mean compatibility**: `meanExt ∘ ĵ_A = meanExt_A`. -/
theorem meanExt_faceEmbedExt (y : FisherCompletion hS (faceMeasure ν A)) :
    meanExt hS ν (faceEmbedExt hS ν A hA hp x₀ v₀ y) = meanExt hS (faceMeasure ν A) y := by
  refine UniformSpace.Completion.induction_on y ?_ fun p ↦ ?_
  · exact isClosed_eq ((continuous_meanExt hS ν).comp (continuous_faceEmbedExt hS ν A hA hp hx₀))
      (continuous_meanExt hS (faceMeasure ν A))
  · rw [faceEmbedExt_coe hS ν A hA hp hx₀, meanExt_faceEmbed hS ν A hA hp hx₀, meanExt_coe]

/-- **Intrinsic face accessibility transfers to ambient accessibility**: every extended mean of the
face completion is an extended mean of `Ŵ`. -/
theorem exists_meanExt_eq_of_faceCompletion (y : FisherCompletion hS (faceMeasure ν A)) :
    ∃ x : FisherCompletion hS ν, meanExt hS ν x = meanExt hS (faceMeasure ν A) y :=
  ⟨_, meanExt_faceEmbedExt hS ν A hA hp hx₀ y⟩

end Ext

end Laplace.Multi
