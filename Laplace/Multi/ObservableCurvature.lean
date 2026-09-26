/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.FisherVariational
import Laplace.Multi.CubicResponse

/-!
# Second-order transport of an arbitrary observable along the atlas

Along the straight path `M_s = m₀ + sΔ` with natural coordinates `θ_s` and velocity
`v_s = θ_s' = (Dm|_𝕍)⁻¹Δ`, the response `F(s) = E_{P_{θ_s}} φ` of a bounded observable satisfies

  `F'(s) = −Cov_{P_{θ_s}}(φ, ⟨v_s, S⟩)`             (`hasDerivAt_integral_familyMeasure_atlas`)

(first order: the visible regression of `φ` moves) and, **freezing the regression residual at the
base point** `s₀` — `r₀ = φ − ⟨β₀, S⟩` with `Cov_{P_{s₀}}(S_i, ⟨β₀,S⟩) = Cov_{P_{s₀}}(S_i, φ)` —

  `F''(s₀) = T_{P_{s₀}}(r₀, ⟨v_{s₀}, S⟩, ⟨v_{s₀}, S⟩)`
                                            (`hasDerivAt_deriv_integral_familyMeasure_atlas`)

the third central moment of the residual against the squared score of the velocity: **second-order
motion is the interaction of the regression residual with the squared score**. The proof needs no
derivative of the inverse covariance: `F'(s) = ⟨β₀,Δ⟩ − Cov_{P_s}(r₀, ⟨v_s,S⟩)` for every `s`, and
the covariance factor vanishes at `s₀`, so its product with the merely continuous velocity is
differentiable with the product of the derivative and the value
(`hasDerivAt_mul_of_eq_zero_of_continuousAt`).

Ingredients: the Fréchet derivative of the observable map in the natural coordinates
(`hasFDerivAt_obsMap`) composed with any `C¹` path (`hasDerivAt_integral_familyMeasure_path`,
`hasDerivAt_lawCov_familyMeasure_path`: `d/ds Cov_{P_{θ_s}}(f, g) = −T(f, g, ⟨θ_s', S⟩)`), and the
continuity of the atlas velocity. The canonical regression coefficient is supplied by the chart
(`exists_regression_coefficient`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Calculus

/-- If `a` is differentiable at `s₀` with `a s₀ = 0` and `b` is merely continuous at `s₀`, then
`a · b` is differentiable at `s₀` with derivative `a'(s₀) b(s₀)`. -/
theorem hasDerivAt_mul_of_eq_zero_of_continuousAt {a b : ℝ → ℝ} {a' s₀ : ℝ}
    (ha : HasDerivAt a a' s₀) (ha0 : a s₀ = 0) (hb : ContinuousAt b s₀) :
    HasDerivAt (fun s ↦ a s * b s) (a' * b s₀) s₀ := by
  have h1 : HasDerivAt (fun s ↦ a s * (b s - b s₀)) 0 s₀ := by
    rw [hasDerivAt_iff_isLittleO]
    simp only [ha0, zero_mul, sub_zero, smul_zero]
    have hA : (fun s ↦ a s) =O[𝓝 s₀] fun s ↦ s - s₀ := by
      have := ha.isBigO_sub
      simpa [ha0] using this
    have hB : (fun s ↦ b s - b s₀) =o[𝓝 s₀] (fun _ ↦ (1 : ℝ)) := by
      rw [Asymptotics.isLittleO_one_iff]
      exact tendsto_sub_nhds_zero_iff.2 hb.tendsto
    simpa using hA.mul_isLittleO hB
  have h2 : HasDerivAt (fun s ↦ a s * b s₀) (a' * b s₀) s₀ := ha.mul_const _
  have h := h1.add h2
  rw [zero_add] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ by simp only [Pi.add_apply]; ring)

end Calculus

section Cubic

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]
  {J : Type*} [Fintype J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hS

/-- The third central moment is linear in a visible contrast in its first slot. -/
theorem thirdCentral_dirLoss_left (v : J → ℝ) {k f : X → ℝ} (hk : Bdd k) (hf : Bdd f) :
    thirdCentral ρ (dirLoss S v) k f = ∑ i, v i * thirdCentral ρ (S i) k f := by
  unfold thirdCentral
  have hmean : ∫ y, dirLoss S v y ∂ρ = ∑ i, v i * ∫ y, S i y ∂ρ := by
    simp only [dirLoss]
    rw [integral_finsetSum _ fun i _ ↦ (integrable_of_bdd_prob ρ (hS i)).const_mul _]
    exact Finset.sum_congr rfl fun i _ ↦ integral_const_mul _ _
  rw [hmean]
  have e : ∀ x, (dirLoss S v x - ∑ i, v i * ∫ y, S i y ∂ρ) * (k x - ∫ y, k y ∂ρ) *
      (f x - ∫ y, f y ∂ρ) = ∑ i, v i * ((S i x - ∫ y, S i y ∂ρ) * (k x - ∫ y, k y ∂ρ) *
        (f x - ∫ y, f y ∂ρ)) := by
    intro x
    simp only [dirLoss, ← Finset.sum_sub_distrib, ← mul_sub, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · exact Finset.sum_congr rfl fun i _ ↦ integral_const_mul _ _
  · exact (integrable_of_bdd_prob ρ ((((hS i).sub (Bdd.const _)).mul (hk.sub (Bdd.const _))).mul
      (hf.sub (Bdd.const _)))).const_mul _

end Cubic

section Path

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] in
/-- The expectation of a family member as a prior expectation. -/
theorem integral_familyMeasure_one_zero (θ : J → ℝ) (f : X → ℝ) :
    ∫ x, f x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ =
      priorExp ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S θ) f 1 :=
  integral_familyMeasure (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ)) measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0)
    (fun _ ↦ by simp) hS θ f

/-- **The response of a bounded observable along a `C¹` path of natural coordinates**:
`d/ds E_{P_{θ_s}} φ = −Cov_{P_{θ_s}}(φ, ⟨θ_s', S⟩)`. -/
theorem hasDerivAt_integral_familyMeasure_path {θ : ℝ → J → ℝ} {θ' : J → ℝ} {s₀ : ℝ}
    (hθ : HasDerivAt θ θ' s₀) {φ : X → ℝ} (hφ : Bdd φ) :
    HasDerivAt (fun s ↦ ∫ x, φ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ s))
      (-lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ s₀)) φ
        (dirLoss S θ')) s₀ := by
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  have h := (hasFDerivAt_obsMap (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ)) measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0)
    (fun _ ↦ by simp) hS hφm hφb one_pos (θ s₀)).comp_hasDerivAt s₀ hθ
  have e : (fun s ↦ ∫ x, φ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ s)) =
      fun s ↦ priorExp ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S (θ s)) φ 1 :=
    funext fun s ↦ integral_familyMeasure_one_zero hS ν (θ s) φ
  rw [e]
  refine h.congr_deriv ?_
  rw [obsMapDeriv_apply (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
    measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const
    (M₀ := 0) (fun _ ↦ by simp) hS hφm hφb one_pos, priorCov_eq_lawCov_familyMeasure hS ν]
  ring

/-- **The covariance along a `C¹` path of natural coordinates**:
`d/ds Cov_{P_{θ_s}}(f, g) = −T_{P_{θ_s}}(f, g, ⟨θ_s', S⟩)`. -/
theorem hasDerivAt_lawCov_familyMeasure_path {θ : ℝ → J → ℝ} {θ' : J → ℝ} {s₀ : ℝ}
    (hθ : HasDerivAt θ θ' s₀) {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    HasDerivAt (fun s ↦ lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ s)) f g)
      (-thirdCentral (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ s₀)) f g
        (dirLoss S θ')) s₀ := by
  have hfg := hasDerivAt_integral_familyMeasure_path hS ν hθ (hf.mul hg)
  have hf' := hasDerivAt_integral_familyMeasure_path hS ν hθ hf
  have hg' := hasDerivAt_integral_familyMeasure_path hS ν hθ hg
  have h := hfg.sub (hf'.mul hg')
  refine h.congr_deriv ?_
  obtain ⟨P, hP⟩ : ∃ P : Measure X, P = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
    (θ s₀) := ⟨_, rfl⟩
  have hPP : IsProbabilityMeasure P := by
    rw [hP]
    exact isProbabilityMeasure_familyMeasure (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
      measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const
      (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) (θ s₀)
  rw [← hP, thirdCentral_eq P hf hg (bdd_dirLoss hS θ')]
  unfold lawCov
  have e1 : ∫ x, f x * g x * dirLoss S θ' x ∂P = ∫ x, f x * g x * dirLoss S θ' x ∂P := rfl
  ring

end Path

section Atlas

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The natural coordinates of the atlas as a `C¹` path in `J → ℝ`. -/
theorem hasDerivAt_atlasTheta_coe {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt (fun s ↦ (atlasTheta hS ν M s : J → ℝ)) (atlasVel hS ν hfin s : J → ℝ) s :=
  (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_atlasTheta hS ν hfin hs0 hs1)

/-- The atlas velocity is continuous. -/
theorem continuousAt_atlasVel {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ContinuousAt (atlasVel hS ν hfin) s := by
  have hθ : ContinuousAt (atlasTheta hS ν M) s :=
    (hasDerivAt_atlasTheta hS ν hfin hs0 hs1).continuousAt
  have hsymm : ContinuousAt (fun s ↦ ((chartDerivEquiv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasTheta hS ν M s)).symm :
        dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S)) s :=
    (continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).continuousAt.comp hθ
  exact hsymm.clm_apply continuousAt_const

/-- **First-order transport along the atlas**:
`d/ds E_{P_{θ_s}} φ = −Cov_{P_{θ_s}}(φ, ⟨v_s, S⟩)`. -/
theorem hasDerivAt_integral_familyMeasure_atlas {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {φ : X → ℝ}
    (hφ : Bdd φ) :
    HasDerivAt (fun s ↦ ∫ x, φ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s))
      (-lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) φ
        (dirLoss S (atlasVel hS ν hfin s))) s :=
  hasDerivAt_integral_familyMeasure_path hS ν (hasDerivAt_atlasTheta_coe hS ν hfin hs0 hs1) hφ

/-- The first-order transport of a visible contrast is constant along the atlas:
`Cov_{P_{θ_s}}(⟨e,S⟩, ⟨v_s,S⟩) = −⟨e, Δ⟩`. -/
theorem lawCov_dirLoss_atlasVel (s : ℝ) (e : J → ℝ) :
    lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s))
        (dirLoss S e) (dirLoss S (atlasVel hS ν hfin s)) =
      -dotJ e (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  have h := lawCov_dirLoss_neg_atlasVel hS ν hfin s e
  have hneg : dirLoss S (-(atlasVel hS ν hfin s : J → ℝ)) =
      fun x ↦ -dirLoss S (atlasVel hS ν hfin s : J → ℝ) x :=
    funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [hneg, lawCov_comm, lawCov_neg_left, lawCov_comm] at h
  linarith

/-- **Second-order transport along the atlas (frozen residual)**: for a regression coefficient
`β₀` at `s₀` (`Cov_{P_{s₀}}(S_i, ⟨β₀,S⟩) = Cov_{P_{s₀}}(S_i, φ)` for all `i`) and the residual
`r₀ = φ − ⟨β₀,S⟩`, the first-order transport `s ↦ −Cov_{P_{θ_s}}(φ, ⟨v_s,S⟩)` is differentiable at
`s₀` with derivative `T_{P_{s₀}}(r₀, ⟨v_{s₀},S⟩, ⟨v_{s₀},S⟩)`. -/
theorem hasDerivAt_neg_lawCov_atlasVel {s₀ : ℝ} (hs0 : 0 ≤ s₀) (hs1 : s₀ < 1) {φ : X → ℝ}
    (hφ : Bdd φ) {β₀ : J → ℝ}
    (hβ : ∀ i, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s₀)) (S i) (dirLoss S β₀) =
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s₀))
        (S i) φ) :
    HasDerivAt (fun s ↦ -lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) φ (dirLoss S (atlasVel hS ν hfin s)))
      (thirdCentral (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν M s₀)) (fun x ↦ φ x - dirLoss S β₀ x)
        (dirLoss S (atlasVel hS ν hfin s₀)) (dirLoss S (atlasVel hS ν hfin s₀))) s₀ := by
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : X → ℝ, r₀ = fun x ↦ φ x - dirLoss S β₀ x := ⟨_, rfl⟩
  rw [← hr₀]
  have hr₀b : Bdd r₀ := hr₀ ▸ hφ.sub (bdd_dirLoss hS β₀)
  have hprob : ∀ s, IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) := fun s ↦
    isProbabilityMeasure_familyMeasure (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
      measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const
      (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) (atlasTheta hS ν M s : J → ℝ)
  -- the decomposition of the first-order transport for every `s`
  have hsplit : ∀ s, -lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) φ (dirLoss S (atlasVel hS ν hfin s)) =
      -(∑ i, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν M s)) (S i) r₀ * (atlasVel hS ν hfin s : J → ℝ) i) +
        dotJ β₀ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
    intro s
    have := hprob s
    have hφe : φ = fun x ↦ r₀ x + dirLoss S β₀ x := by
      rw [hr₀]
      funext x
      ring
    have hadd : lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν M s)) φ (dirLoss S (atlasVel hS ν hfin s)) =
        lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) r₀
          (dirLoss S (atlasVel hS ν hfin s)) +
        lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s))
          (dirLoss S β₀) (dirLoss S (atlasVel hS ν hfin s)) := by
      rw [hφe]
      unfold lawCov
      have hv := bdd_dirLoss hS (atlasVel hS ν hfin s : J → ℝ)
      have hb := bdd_dirLoss hS β₀
      have e : ∀ x, (r₀ x + dirLoss S β₀ x) * dirLoss S (atlasVel hS ν hfin s) x =
          r₀ x * dirLoss S (atlasVel hS ν hfin s) x +
            dirLoss S β₀ x * dirLoss S (atlasVel hS ν hfin s) x := fun x ↦ by ring
      simp_rw [e]
      rw [integral_add (integrable_of_bdd_prob _ (hr₀b.mul hv))
        (integrable_of_bdd_prob _ (hb.mul hv)),
        integral_add (integrable_of_bdd_prob _ hr₀b) (integrable_of_bdd_prob _ hb)]
      ring
    rw [hadd, lawCov_dirLoss_atlasVel hS ν hfin s β₀, lawCov_comm,
      lawCov_dirLoss_left hS _ _ _ hr₀b]
    have e : ∑ i, (atlasVel hS ν hfin s : J → ℝ) i * lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) (S i) r₀ =
        ∑ i, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          (atlasTheta hS ν M s)) (S i) r₀ * (atlasVel hS ν hfin s : J → ℝ) i :=
      Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    rw [e]
    ring
  have hfun : (fun s ↦ -lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) φ (dirLoss S (atlasVel hS ν hfin s))) =
      fun s ↦ -(∑ i, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν M s)) (S i) r₀ * (atlasVel hS ν hfin s : J → ℝ) i) +
        dotJ β₀ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := funext hsplit
  rw [hfun]
  -- each summand: a vanishing differentiable factor times a continuous one
  have hθ := hasDerivAt_atlasTheta_coe hS ν hfin hs0 hs1
  have hvel := continuousAt_atlasVel hS ν hfin hs0 hs1
  have hterm : ∀ i, HasDerivAt (fun s ↦ lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) (S i) r₀ * (atlasVel hS ν hfin s : J → ℝ) i)
      (-thirdCentral (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν M s₀)) (S i) r₀ (dirLoss S (atlasVel hS ν hfin s₀)) *
        (atlasVel hS ν hfin s₀ : J → ℝ) i) s₀ := by
    intro i
    refine hasDerivAt_mul_of_eq_zero_of_continuousAt
      (hasDerivAt_lawCov_familyMeasure_path hS ν hθ (hS i) hr₀b) ?_
      ((continuous_apply i).continuousAt.comp (continuous_subtype_val.continuousAt.comp hvel))
    have := hprob s₀
    rw [hr₀]
    unfold lawCov
    have hb := bdd_dirLoss hS β₀
    have e : ∀ x, S i x * (φ x - dirLoss S β₀ x) = S i x * φ x - S i x * dirLoss S β₀ x :=
      fun x ↦ by ring
    simp_rw [e]
    rw [integral_sub (integrable_of_bdd_prob _ ((hS i).mul hφ))
      (integrable_of_bdd_prob _ ((hS i).mul hb)),
      integral_sub (integrable_of_bdd_prob _ hφ) (integrable_of_bdd_prob _ hb)]
    have := hβ i
    unfold lawCov at this
    linarith
  have hsum := (HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hterm i).neg.add_const
    (dotJ β₀ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0))
  refine hsum.congr_deriv ?_
  have := hprob s₀
  rw [thirdCentral_comm₁₂, thirdCentral_dirLoss_left _ hS _ hr₀b (bdd_dirLoss hS _)]
  simp only [neg_mul, Finset.sum_neg_distrib, neg_neg]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **The second derivative of the response of an observable along the atlas**: for
`s₀ ∈ (0, 1)`, a regression coefficient `β₀` at `s₀` and the residual `r₀ = φ − ⟨β₀, S⟩`,
`F''(s₀) = T_{P_{s₀}}(r₀, ⟨v_{s₀},S⟩, ⟨v_{s₀},S⟩)` where `F(s) = E_{P_{θ_s}} φ`. -/
theorem hasDerivAt_deriv_integral_familyMeasure_atlas {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    {φ : X → ℝ} (hφ : Bdd φ) {β₀ : J → ℝ}
    (hβ : ∀ i, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s₀)) (S i) (dirLoss S β₀) =
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s₀))
        (S i) φ) :
    HasDerivAt (deriv fun s ↦ ∫ x, φ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s))
      (thirdCentral (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν M s₀)) (fun x ↦ φ x - dirLoss S β₀ x)
        (dirLoss S (atlasVel hS ν hfin s₀)) (dirLoss S (atlasVel hS ν hfin s₀))) s₀ := by
  have h := hasDerivAt_neg_lawCov_atlasVel hS ν hfin hs₀.1.le hs₀.2 hφ hβ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs₀.1 hs₀.2] with s hs
  exact (hasDerivAt_integral_familyMeasure_atlas hS ν hfin hs.1.le hs.2 hφ).deriv

omit hfin in
/-- **The canonical regression coefficient exists**: the covariance vector of `φ` with the
statistics lies in the visible subspace, and the chart derivative solves the regression
equations. -/
theorem exists_regression_coefficient (s₀ : ℝ) {φ : X → ℝ} (hφ : Bdd φ) :
    ∃ β₀ ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, ∀ i,
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s₀))
        (S i) (dirLoss S β₀) =
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s₀))
        (S i) φ := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Measure X, P = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
    (atlasTheta hS ν M s₀) := ⟨_, rfl⟩
  have hPP : IsProbabilityMeasure P := by
    rw [hP]
    exact isProbabilityMeasure_familyMeasure (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
      measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const
      (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) (atlasTheta hS ν M s₀ : J → ℝ)
  -- the covariance vector lies in the visible subspace
  have hc : (fun i ↦ lawCov P (S i) φ) ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := by
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (dirSpan ν (fun _ ↦ (1 : ℝ)) S)
      _).1 fun ψ hψ ↦ ?_
    obtain ⟨e, he⟩ : ∃ e : J → ℝ, ∀ w, ψ w = dotJ e w := by
      refine ⟨fun j ↦ ψ (Pi.single j 1), fun w ↦ ?_⟩
      have hw : w = ∑ j, w j • Pi.single j 1 := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hw]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, dotJ]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    rw [he]
    obtain ⟨c, hcst⟩ := mem_invisibleSet_of_dotJ_eq_zero_on_dirSpan measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS e fun v hv ↦ by
        rw [← he]
        exact (Submodule.mem_dualAnnihilator ψ).1 hψ v hv
    have h1 : dotJ e (fun i ↦ lawCov P (S i) φ) = lawCov P (dirLoss S e) φ := by
      rw [lawCov_dirLoss_left hS _ _ _ hφ]
      rfl
    rw [h1, hP, ← priorCov_eq_lawCov_familyMeasure hS ν]
    exact priorCov_eq_zero_of_ae_eq_const hcst
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        (atlasTheta hS ν M s₀) β₀ = ⟨-(fun i ↦ lawCov P (S i) φ), Submodule.neg_mem _ hc⟩ := by
    refine ⟨(chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (atlasTheta hS ν M s₀)).symm ⟨-(fun i ↦ lawCov P (S i) φ),
        Submodule.neg_mem _ hc⟩, ?_⟩
    rw [← coe_chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (atlasTheta hS ν M s₀)]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  refine ⟨β₀, β₀.2, fun i ↦ ?_⟩
  have h := dotJ_chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (atlasTheta hS ν M s₀) (Pi.single i 1) β₀
  rw [hβ₀, priorCov_eq_lawCov_familyMeasure hS ν, ← hP] at h
  have hsingle : dirLoss S (Pi.single i (1 : ℝ)) = S i := by
    funext x
    simp only [dirLoss]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (fun h ↦ absurd (Finset.mem_univ i) h)]
    simp
  rw [hsingle] at h
  have h2 : dotJ (Pi.single i (1 : ℝ)) ((⟨-(fun i ↦ lawCov P (S i) φ), Submodule.neg_mem _ hc⟩ :
      dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) = -lawCov P (S i) φ := by
    simp only [dotJ, Pi.neg_apply]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (fun h ↦ absurd (Finset.mem_univ i) h)]
    simp
  rw [← hP]
  linarith

end Atlas

end Laplace.Multi
