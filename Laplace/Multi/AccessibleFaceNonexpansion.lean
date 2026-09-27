/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiltedCovarianceStability
import Laplace.Multi.FaceGauge
import Laplace.Multi.FisherMeanControl
import Laplace.Multi.FacetCompletionUnique

/-!
# The face embedding is nonexpansive: intrinsic geometry of an accessible stratum

Let `A` be a face event with face law `ν_A`, and let `x₀ ∈ Ŵ` be an accessible point whose law is
the face-family law `Q_{x₀} = P^A_{v₀}` with `v₀ ∈ W_A` (the face's own direction space). The
bounded tilt action embeds the whole face parameter space into the completion,

`j_A : W_A → Ŵ,  j_A(w) = tiltExt (w − v₀) x₀`,   with `Q_{j_A w} = P^A_w`
(`completionLaw_faceEmbed`),

and this embedding is **nonexpansive** for the face's own Fisher metric:

`d̂(j_A w, j_A w') ≤ d_F^{(A)}(w, w')`   (`dist_faceEmbed_le`).

The proof approximates `x₀` by family points `θ_n`, transports a face path `γ` from `w` to `w'` to
the ambient path `θ_n + (γ_t − v₀)`, bounds the ambient Fisher distance by the ambient length
(`fisherDist_le_integral`), and lets `n → ∞`: the ambient Fisher speeds converge to the face Fisher
speeds uniformly in `t`, by the covariance stability along the completion action
(`TiltedCovarianceStability`). Taking the infimum over `γ` gives the face Fisher distance. Boundary
paths are therefore controlled by the face Fisher metric, and `j_A` extends to a `1`-Lipschitz map
from the face completion into `Ŵ`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Embed

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (A : Set X) [IsProbabilityMeasure (faceMeasure ν A)] (hA : MeasurableSet A)
  (hp : 0 < ν.real A)
include hS hA hp

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The face direction space. -/
local notation "𝕍A" => dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S

/-- The face family. -/
local notation "Qface" => familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- A face direction `w − v₀` as an ambient direction. -/
def faceDir (v₀ w : 𝕍A) : 𝕍 :=
  ⟨(w : J → ℝ) - (v₀ : J → ℝ), dirSpan_faceMeasure_le hS ν A hA hp (sub_mem w.2 v₀.2)⟩

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure (faceMeasure ν A)] in
theorem faceDir_coe (v₀ w : 𝕍A) :
    (faceDir hS ν A hA hp v₀ w : J → ℝ) = (w : J → ℝ) - (v₀ : J → ℝ) := rfl

/-- **The face embedding** `j_A(w) = tiltExt (w − v₀) x₀`. -/
noncomputable def faceEmbed (x₀ : FisherCompletion hS ν) (v₀ w : 𝕍A) : FisherCompletion hS ν :=
  tiltExt hS ν (faceDir hS ν A hA hp v₀ w) x₀

variable {x₀ : FisherCompletion hS ν} {v₀ : dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S}
  (hx₀ : completionLaw hS ν x₀ =
    familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀ : J → ℝ))
include hx₀

/-- **The law of the embedded point is the face-family law**: `Q_{j_A w} = P^A_w`. -/
theorem completionLaw_faceEmbed (w : 𝕍A) :
    completionLaw hS ν (faceEmbed hS ν A hA hp x₀ v₀ w) = Qface (w : J → ℝ) := by
  rw [faceEmbed, completionLaw_tiltExt_faceFamily hS ν A _ x₀ hx₀, faceDir_coe, add_sub_cancel]

/-- **The face embedding is nonexpansive**: `d̂(j_A w, j_A w') ≤ d_F^{(A)}(w, w')`. -/
theorem dist_faceEmbed_le (w w' : 𝕍A) :
    dist (faceEmbed hS ν A hA hp x₀ v₀ w) (faceEmbed hS ν A hA hp x₀ v₀ w') ≤
      fisherDist S (faceMeasure ν A) w w' := by
  obtain ⟨u, hu⟩ := exists_seq_tendsto_completion hS ν x₀
  have hε := tendsto_integral_abs_famDens_sub_completionDens hS ν hu
  have hd : Tendsto (fun n ↦ dist (tiltExt hS ν (faceDir hS ν A hA hp v₀ w) (u n))
      (tiltExt hS ν (faceDir hS ν A hA hp v₀ w') (u n))) atTop
      (𝓝 (dist (faceEmbed hS ν A hA hp x₀ v₀ w) (faceEmbed hS ν A hA hp x₀ v₀ w'))) :=
    (((continuous_tiltExt hS ν _).tendsto _).comp hu).dist
      (((continuous_tiltExt hS ν _).tendsto _).comp hu)
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  refine le_csInf fisherLengths_nonempty fun _ ⟨γ, hγ⟩ ↦ hγ ▸ ?_
  -- uniform bounds along the face path
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (E := J → ℝ)
    ((continuous_subtype_val.comp γ.continuous_toFun).continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨C', hC'⟩ := isCompact_Icc.exists_bound_of_continuousOn (E := J → ℝ)
    ((continuous_subtype_val.comp γ.continuous_vel).continuousOn (s := Icc (0 : ℝ) 1))
  have hC'0 : 0 ≤ C' := (norm_nonneg _).trans (hC' 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (Fintype.card J : ℝ) * B * (C + ‖(v₀ : J → ℝ)‖) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = (Fintype.card J : ℝ) * B * C' := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y,
      |dirLoss S (faceDir hS ν A hA hp v₀ (γ.toFun t) : J → ℝ) y| ≤ K := fun t ht y ↦ by
    rw [hKdef, faceDir_coe]
    refine (abs_dirLoss_le_card_mul hB0 hB _ y).trans
      (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hC t ht) le_rfl))
        (by positivity))
  have hL : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, |dirLoss S (γ.vel t : J → ℝ) y| ≤ L := fun t ht y ↦ by
    rw [hLdef]
    exact (abs_dirLoss_le_card_mul hB0 hB _ y).trans
      (mul_le_mul_of_nonneg_left (hC' t ht) (by positivity))
  -- the vanishing error
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℝ, c = fun n ↦ 3 * L * L * (2 * Real.exp (2 * K) *
      ∫ y, |famDens S ν ((u n).param : J → ℝ) y -
        rootDensExt hS ν x₀ y * rootDensExt hS ν x₀ y| ∂ν) := ⟨_, rfl⟩
  have hc0 : ∀ n, 0 ≤ c n := fun n ↦ by
    rw [hcdef]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
      (integral_nonneg fun y ↦ abs_nonneg _))
  have hc : Tendsto c atTop (𝓝 0) := by
    rw [hcdef]
    have := (hε.const_mul (2 * Real.exp (2 * K))).const_mul (3 * L * L)
    simpa using this
  have hsq : Tendsto (fun n ↦ √(c n)) atTop (𝓝 0) := by
    have := hc.sqrt
    rwa [Real.sqrt_zero] at this
  -- the per-`n` bound
  have hdn : ∀ n, dist (tiltExt hS ν (faceDir hS ν A hA hp v₀ w) (u n))
      (tiltExt hS ν (faceDir hS ν A hA hp v₀ w') (u n)) ≤ γ.length + √(c n) := fun n ↦ by
    obtain ⟨θ, hθ⟩ : ∃ θ : J → ℝ, θ = ((u n).param : J → ℝ) := ⟨_, rfl⟩
    have hmem : ∀ t, θ + ((γ.toFun t : J → ℝ) - (v₀ : J → ℝ)) ∈ 𝕍 := fun t ↦ by
      rw [hθ]
      exact add_mem (u n).param.2 (dirSpan_faceMeasure_le hS ν A hA hp (sub_mem (γ.toFun t).2 v₀.2))
    have hder : ∀ t, HasDerivAt (fun s ↦ θ + ((γ.toFun s : J → ℝ) - (v₀ : J → ℝ)))
        (γ.vel t : J → ℝ) t := fun t ↦
      ((γ.hasDerivAt_coe (faceMeasure ν A) t).sub_const _).const_add _
    have hdist := fisherDist_le_integral hS ν hmem hder
      (continuous_subtype_val.comp γ.continuous_vel) zero_le_one
    have e0 : (⟨θ + ((γ.toFun 0 : J → ℝ) - (v₀ : J → ℝ)), hmem 0⟩ : 𝕍) =
        (tiltPoint hS ν (faceDir hS ν A hA hp v₀ w) (u n)).param :=
      Subtype.ext (by
        change θ + ((γ.toFun 0 : J → ℝ) - (v₀ : J → ℝ)) =
          ((tiltPoint hS ν (faceDir hS ν A hA hp v₀ w) (u n)).param : J → ℝ)
        rw [tiltPoint_param, faceDir_coe, hθ, γ.source])
    have e1 : (⟨θ + ((γ.toFun 1 : J → ℝ) - (v₀ : J → ℝ)), hmem 1⟩ : 𝕍) =
        (tiltPoint hS ν (faceDir hS ν A hA hp v₀ w') (u n)).param :=
      Subtype.ext (by
        change θ + ((γ.toFun 1 : J → ℝ) - (v₀ : J → ℝ)) =
          ((tiltPoint hS ν (faceDir hS ν A hA hp v₀ w') (u n)).param : J → ℝ)
        rw [tiltPoint_param, faceDir_coe, hθ, γ.target])
    rw [e0, e1] at hdist
    rw [tiltExt_coe, tiltExt_coe, UniformSpace.Completion.dist_eq, FisherPoint.dist_eq]
    refine hdist.trans ?_
    -- pointwise comparison of the speeds
    have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
        fisherNorm S ν (θ + ((γ.toFun t : J → ℝ) - (v₀ : J → ℝ))) (γ.vel t : J → ℝ) ≤
          fisherNorm S (faceMeasure ν A) (γ.toFun t : J → ℝ) (γ.vel t : J → ℝ) + √(c n) := by
      intro t ht
      have hV := abs_lawCov_family_add_sub_completion_tiltExt_le hS ν θ x₀
        (faceDir hS ν A hA hp v₀ (γ.toFun t)) (hK t ht) (bdd_dirLoss hS _).1 (bdd_dirLoss hS _).1
        hL0 hL0 (hL t ht) (hL t ht)
      have hQ : completionLaw hS ν (tiltExt hS ν (faceDir hS ν A hA hp v₀ (γ.toFun t)) x₀) =
          Qface (γ.toFun t : J → ℝ) := by
        rw [completionLaw_tiltExt_faceFamily hS ν A _ x₀ hx₀, faceDir_coe, add_sub_cancel]
      rw [hQ, hθ] at hV
      have hab : |fisherVar S ν (θ + ((γ.toFun t : J → ℝ) - (v₀ : J → ℝ))) (γ.vel t : J → ℝ) -
          fisherVar S (faceMeasure ν A) (γ.toFun t : J → ℝ) (γ.vel t : J → ℝ)| ≤ c n := by
        rw [hcdef, hθ]
        exact hV
      have ha0 := fisherVar_nonneg hS ν (θ + ((γ.toFun t : J → ℝ) - (v₀ : J → ℝ)))
        (γ.vel t : J → ℝ)
      have hb0 := fisherVar_nonneg hS (faceMeasure ν A) (γ.toFun t : J → ℝ) (γ.vel t : J → ℝ)
      have h1 : fisherVar S ν (θ + ((γ.toFun t : J → ℝ) - (v₀ : J → ℝ))) (γ.vel t : J → ℝ) ≤
          fisherVar S (faceMeasure ν A) (γ.toFun t : J → ℝ) (γ.vel t : J → ℝ) + c n := by
        linarith [le_abs_self (fisherVar S ν (θ + ((γ.toFun t : J → ℝ) - (v₀ : J → ℝ)))
          (γ.vel t : J → ℝ) - fisherVar S (faceMeasure ν A) (γ.toFun t : J → ℝ)
          (γ.vel t : J → ℝ))]
      unfold fisherNorm
      calc √(fisherVar S ν (θ + ((γ.toFun t : J → ℝ) - (v₀ : J → ℝ))) (γ.vel t : J → ℝ)) ≤
            √(fisherVar S (faceMeasure ν A) (γ.toFun t : J → ℝ) (γ.vel t : J → ℝ) + c n) :=
            Real.sqrt_le_sqrt h1
        _ ≤ √(fisherVar S (faceMeasure ν A) (γ.toFun t : J → ℝ) (γ.vel t : J → ℝ)) + √(c n) := by
            rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
            nlinarith [Real.sq_sqrt hb0, Real.sq_sqrt (hc0 n),
              mul_nonneg (Real.sqrt_nonneg (fisherVar S (faceMeasure ν A) (γ.toFun t : J → ℝ)
                (γ.vel t : J → ℝ))) (Real.sqrt_nonneg (c n))]
    have hint1 : IntervalIntegrable (fun t ↦ fisherNorm S ν
        (θ + ((γ.toFun t : J → ℝ) - (v₀ : J → ℝ))) (γ.vel t : J → ℝ)) volume 0 1 :=
      (continuous_fisherNorm_comp hS ν (continuous_const.add
        ((continuous_subtype_val.comp γ.continuous_toFun).sub continuous_const))
        (continuous_subtype_val.comp γ.continuous_vel)).intervalIntegrable 0 1
    have hs : IntervalIntegrable (fun t ↦ fisherNorm S (faceMeasure ν A) (γ.toFun t : J → ℝ)
        (γ.vel t : J → ℝ)) volume 0 1 :=
      (continuous_fisherNorm_comp hS (faceMeasure ν A)
        (continuous_subtype_val.comp γ.continuous_toFun)
        (continuous_subtype_val.comp γ.continuous_vel)).intervalIntegrable 0 1
    have hcst : IntervalIntegrable (fun _ : ℝ ↦ √(c n)) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    calc ∫ s in (0 : ℝ)..1, fisherNorm S ν (θ + ((γ.toFun s : J → ℝ) - (v₀ : J → ℝ)))
          (γ.vel s : J → ℝ) ≤
        ∫ s in (0 : ℝ)..1, (fisherNorm S (faceMeasure ν A) (γ.toFun s : J → ℝ)
          (γ.vel s : J → ℝ) + √(c n)) :=
          intervalIntegral.integral_mono_on zero_le_one hint1 (hs.add hcst) hpt
      _ = γ.length + √(c n) := by
          rw [intervalIntegral.integral_add hs hcst, intervalIntegral.integral_const, sub_zero,
            one_smul]
          rfl
  have hlim : Tendsto (fun n ↦ γ.length + √(c n)) atTop (𝓝 γ.length) := by
    have := (tendsto_const_nhds (x := γ.length)).add hsq
    rwa [add_zero] at this
  exact le_of_tendsto_of_tendsto' hd hlim hdn

end Embed

end Laplace.Multi
