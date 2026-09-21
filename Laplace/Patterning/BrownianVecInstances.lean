/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.OUBrownian
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Brownian motion in `d` dimensions from independent real Brownian motions

The hypothesis package `IsBrownianVec` of `OUBrownian.lean` is satisfied by the standard
construction: `d` independent copies of Mathlib's real Brownian motion `IsBrownianReal`, assembled
coordinatewise (`isBrownianVec_of_iIndepFun`). Joint Gaussianity of the vector process comes from
`iIndepFun.hasGaussianLaw` (independent Gaussians are jointly Gaussian), the cross-covariances vanish
by independence, and the paths are continuous coordinatewise. The one-dimensional case
(`IsBrownianReal.isBrownianVec`) needs no independence hypothesis.

Mathlib on this pin provides the Gaussian projective family of Brownian motion but not yet the
continuous modification, so the existence of an `IsBrownianReal` is not available here; these
bridges show that `IsBrownianVec` is exactly the standard notion once it is.
-/

namespace Laplace.Patterning

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

noncomputable section

/-- Assemble real processes coordinatewise into a Euclidean-valued process. -/
def vecProcess (B : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => B i t ω

@[simp] lemma vecProcess_apply (B : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) (i : ι) :
    vecProcess B t ω i = B i t ω := rfl

/-- The linear map `(i ↦ k ↦ zᵢₖ) ↦ (k ↦ (zᵢₖ)ᵢ)` assembling coordinate paths. -/
def assembleₗ (κ : Type*) [Fintype κ] : (ι → κ → ℝ) →ₗ[ℝ] (κ → EuclideanSpace ℝ ι) where
  toFun z k := WithLp.toLp 2 fun i => z i k
  map_add' z z' := by
    funext k
    ext i
    simp
  map_smul' c z := by
    funext k
    ext i
    simp

/-- The assembly map as a continuous linear map. -/
def assembleCLM (κ : Type*) [Fintype κ] : (ι → κ → ℝ) →L[ℝ] (κ → EuclideanSpace ℝ ι) :=
  LinearMap.toContinuousLinearMap (assembleₗ κ)

@[simp] lemma assembleCLM_apply {κ : Type*} [Fintype κ] (z : ι → κ → ℝ) (k : κ) (i : ι) :
    assembleCLM κ z k i = z i k := rfl

/-- **Independent real Brownian motions form a vector Brownian motion.** -/
theorem isBrownianVec_of_iIndepFun (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω => fun t => B i t ω) P) :
    IsBrownianVec (vecProcess B) P := by
  have hmemLp : ∀ i t, MemLp (B i t) 2 P := fun i t =>
    ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  refine ⟨⟨fun I => ?_⟩, fun t i => ?_, fun s t i j => ?_, ?_⟩
  · -- joint Gaussianity over the finite set of times `I`
    have hind' : iIndepFun (fun i ω => I.restrict fun t => B i t ω) P :=
      hind.comp (fun _ => I.restrict) fun _ => Finset.measurable_restrict I
    have hg : ∀ i, HasGaussianLaw (fun ω => I.restrict fun t => B i t ω) P := fun i =>
      (hB i).isGaussianProcess.hasGaussianLaw I
    have hjoint := hind'.hasGaussianLaw hg
    refine (hjoint.map_fun (assembleCLM I)).congr (Filter.Eventually.of_forall fun ω => ?_)
    funext k
    ext i
    first
    | rfl
    | simp [Finset.restrict_def]
  · simpa using (hB i).integral_eval t
  · by_cases hij : i = j
    · subst hij
      simpa using (hB i).covariance_eval s t
    · rw [if_neg hij]
      have h := (hind.indepFun hij).comp (measurable_pi_apply s) (measurable_pi_apply t)
      exact h.covariance_eq_zero (hmemLp i s) (hmemLp j t)
  · have := ae_all_iff.mpr fun i => (hB i).cont
    filter_upwards [this] with ω hω
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : ι => ℝ)).comp (continuous_pi fun i => hω i)

/-- **A real Brownian motion is a one-dimensional vector Brownian motion.** -/
theorem isBrownianVec_of_isBrownianReal {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    IsBrownianVec (vecProcess fun _ : Unit => B) P :=
  have := hB.isGaussianProcess.isProbabilityMeasure
  isBrownianVec_of_iIndepFun (fun _ : Unit => B) (fun _ => hB) iIndepFun.of_subsingleton

end

end Laplace.Patterning
