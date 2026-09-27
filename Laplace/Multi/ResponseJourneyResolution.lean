/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseIntrinsicResolution
import Laplace.Multi.ResponseClassResolution
import Laplace.Multi.ResponseTiltPathBudget

/-!
# Journey resolution: estimation radii, separation certificates and patch margins

Three notions of resolution are kept apart.

* **Patch margins** (`fisherDist_le_sqrt_mul_of_segment`, `fisherDist_lt_of_dotJ_lt`): on a
  chamber where the Fisher form is bounded by `Λ` along a segment, `d_F(θ,η) ≤ √Λ ‖η − θ‖₂`, so
  `√Λ r < δ` puts the Euclidean `r`-ball inside the Fisher `δ`-ball. The segment condition is part
  of the theorem.
* **Displacement is bounded by length** (`fisherDist_coeffResponse_le`): along a journey through
  data the response moves at most the integrated pulled-back speed, `d_F(Φ(g_{t₁}),Φ(g_{t₂})) ≤ L`.
  Hence a disjoint-ball separation certificate `ρ₀ + ρ₁ ≤ D` is impossible once `L < ρ₀ + ρ₁`
  (`fisherDist_coeffResponse_lt_of_length_lt`) — which says nothing about statistical
  indistinguishability, only about this certificate.
* **The intrinsic confidence radius** (`measureReal_sampleResponse_notMem_fisherBall_le`): the
  empirical response leaves the intrinsic Fisher ball of radius `√(Λ/λ) r` about the response of
  its data law with probability at most `tr(R C_D)/(n r²)`.
* **The response-ball classifier** (`ballClassifier`): decide class `0` when the empirical
  response lies in the intrinsic ball of the first response. Its two error probabilities are
  bounded by the two ball-exit probabilities whenever the balls are disjoint
  (`measureReal_ballClassifier_ne_true_le`, `measureReal_ballClassifier_ne_false_le`): this is
  the sufficient separation theorem, with the dimension-dependent estimation radii on one side
  and, in `ResponseProductAffinity`, the dimension-free testing bound on the other.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Margin

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty J] in
/-- **The segment bound under a chamber Fisher bound**: if `|w|²_{F,η} ≤ Λ ⟨w,w⟩` along the
segment `[x, y]`, then `d_F(x, y) ≤ √Λ · ‖y − x‖₂`. -/
theorem fisherDist_le_sqrt_mul_of_segment {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (x y : 𝕍)
    (hΛ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : J → ℝ,
      fisherVar S ν ((x + t • (y - x) : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) w ≤
        Λ * dotJ w w) :
    fisherDist S ν x y ≤
      √Λ * √(dotJ ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)
        ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)) := by
  refine (fisherDist_le_length (FisherPath.segment x y)).trans ?_
  rw [FisherPath.segment, FisherPath.length_flat hS ν]
  calc ∫ t in (0 : ℝ)..1, fisherNorm S ν ((x + t • (y - x) : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)
        ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)
      ≤ ∫ _ in (0 : ℝ)..1, √Λ * √(dotJ ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)
          ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)) := by
        refine intervalIntegral.integral_mono_on zero_le_one ?_ (by simp) fun t ht ↦ ?_
        · exact (continuous_fisherNorm_comp hS ν (continuous_subtype_val.comp (by fun_prop))
            continuous_const).intervalIntegrable _ _
        · rw [fisherNorm, ← Real.sqrt_mul hΛ0]
          exact Real.sqrt_le_sqrt (hΛ t ht _)
    _ = _ := by simp

omit [Nonempty J] in
/-- **Patch clearance**: `√Λ r < δ` puts the Euclidean `r`-ball inside the Fisher `δ`-ball, on a
chamber where the Fisher form is bounded by `Λ` along segments. -/
theorem fisherDist_lt_of_dotJ_lt {Λ r δ : ℝ} (hΛ0 : 0 ≤ Λ) (hr : 0 ≤ r) (hrδ : √Λ * r < δ)
    (x y : 𝕍)
    (hΛ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : J → ℝ,
      fisherVar S ν ((x + t • (y - x) : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) w ≤
        Λ * dotJ w w)
    (hy : dotJ ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)
      ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) < r ^ 2) :
    fisherDist S ν x y < δ := by
  refine (fisherDist_le_sqrt_mul_of_segment hS ν hΛ0 x y hΛ).trans_lt ?_
  calc √Λ * √(dotJ ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)
        ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)) ≤ √Λ * r := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [← Real.sqrt_sq hr]
        exact Real.sqrt_le_sqrt hy.le
    _ < δ := hrδ

end Margin

section Journey

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ j, Bdd (h j)) {a a' : ℝ → ι → ℝ}
  (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
include hS hh ha ha'

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- **Displacement is bounded by length**: along a journey through data,
`d_F(Φ(g_{t₁}), Φ(g_{t₂})) ≤ ∫_{t₁}^{t₂} √G^{resp}_{g_s}(ġ_s) ds`. -/
theorem fisherDist_coeffResponse_le {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) :
    fisherDist S ν (coeffResponse hS ν h a t₁) (coeffResponse hS ν h a t₂) ≤
      ∫ s in t₁..t₂, √(pullbackForm hS ν (bdd_dirLoss hh (a s)) (bdd_dirLoss hh (a' s))) := by
  have hη : ∀ s, (coeffResponse hS ν h a s : J → ℝ) ∈ 𝕍 := fun s ↦
    (coeffResponse hS ν h a s).2
  have hd : ∀ s, HasDerivAt (fun t ↦ (coeffResponse hS ν h a t : J → ℝ))
      (responseVel hS ν (bdd_dirLoss hh (a s)) (bdd_dirLoss hh (a' s)) : J → ℝ) s := fun s ↦
    (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_coeffResponse hS ν hh ha ha' s)
  have hd' := continuous_responseVel_tilt hS ν hh ha ha'
  exact fisherDist_le_integral hS ν hη hd hd' h12

/-- **A short journey admits no disjoint-ball certificate**: if the length between `t₁` and `t₂`
is below `ρ₀ + ρ₁`, the two responses are closer than `ρ₀ + ρ₁`. This is a statement about the
certificate, not about statistical indistinguishability. -/
theorem fisherDist_coeffResponse_lt_of_length_lt {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) {ρ₀ ρ₁ : ℝ}
    (hL : (∫ s in t₁..t₂, √(pullbackForm hS ν (bdd_dirLoss hh (a s)) (bdd_dirLoss hh (a' s)))) <
      ρ₀ + ρ₁) :
    fisherDist S ν (coeffResponse hS ν h a t₁) (coeffResponse hS ν h a t₂) < ρ₀ + ρ₁ :=
  (fisherDist_coeffResponse_le hS ν hh ha ha' h12).trans_lt hL

end Journey

section Confidence

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
  {U : Set (J → ℝ)} (hU : Convex ℝ U)
  (hUint : U ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hS hDν hXm hid hlaw hind hU hUint

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The intrinsic confidence radius**: the empirical response leaves the intrinsic Fisher ball
of radius `√(Λ/λ) r` about the response of its data law with probability at most
`tr(R C_D)/(n r²)`. -/
theorem measureReal_sampleResponse_notMem_fisherBall_le {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    (hm : (fun j ↦ ∫ x, S j x ∂D) ∈ U) {Λ : ℝ} (hΛ : 0 < Λ)
    (hΛ' : ∀ w : J → ℝ, fisherVar S ν (θr (fun j ↦ ∫ x, S j x ∂D) : J → ℝ) w ≤ Λ * dotJ w w)
    (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {r : ℝ} (hr : 0 < r)
    (hell : ∀ z ∈ 𝕍, samplingEnergy hS ν (θr (fun j ↦ ∫ x, S j x ∂D)) p z < r ^ 2 →
      (fun j ↦ ∫ x, S j x ∂D) + z ∈ U) {n : ℕ} (hn : 0 < n) :
    P.real {ω | sampleResponse S Xs n ω ∉
        {M' | fisherDist S ν (θr (fun j ↦ ∫ x, S j x ∂D)) (θr M') < √(Λ / lam) * r}} ≤
      -(∑ a, ∑ b, samplingOp hS ν (θr (fun j ↦ ∫ x, S j x ∂D)) p (Pi.single b 1) a *
        lawCov D (S a) (S b)) / n / r ^ 2 :=
  measureReal_sampleResponse_notMem_le hS ν P D hDν Xs hXm hid hlaw hind _ p hp hr
    (fun _ hz hlt ↦ (mem_fisherBall_of_samplingEnergy_lt hS ν hU hUint hlam hcoer hm hΛ.le hΛ' p hp
      hr hell hz hlt).resolve_right hΛ.ne') hn

end Confidence

section Classifier

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The intrinsic Fisher ball of radius `ρ` about a response, in mean coordinates. -/
def fisherBall (θ₀ : 𝕍) (ρ : ℝ) : Set (J → ℝ) := {M' | fisherDist S ν θ₀ (θr M') < ρ}

/-- **The response-ball classifier**: class `0` (`true`) when the empirical response lies in the
intrinsic Fisher ball of radius `ρ₀` about `θ₀`. -/
noncomputable def ballClassifier (θ₀ : 𝕍) (ρ₀ : ℝ) (M' : J → ℝ) : Bool :=
  @decide (M' ∈ fisherBall hS ν θ₀ ρ₀) (Classical.propDecidable _)

theorem ballClassifier_eq_true_iff (θ₀ : 𝕍) (ρ₀ : ℝ) (M' : J → ℝ) :
    ballClassifier hS ν θ₀ ρ₀ M' = true ↔ M' ∈ fisherBall hS ν θ₀ ρ₀ := by
  unfold ballClassifier
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- On a disjoint second ball the classifier answers `false`. -/
theorem ballClassifier_eq_false_of_disjoint {θ₀ θ₁ : 𝕍} {ρ₀ ρ₁ : ℝ}
    (hdisj : Disjoint (fisherBall hS ν θ₀ ρ₀) (fisherBall hS ν θ₁ ρ₁)) {M' : J → ℝ}
    (hM' : M' ∈ fisherBall hS ν θ₁ ρ₁) : ballClassifier hS ν θ₀ ρ₀ M' = false := by
  rw [← Bool.not_eq_true, ballClassifier_eq_true_iff]
  exact fun h ↦ Set.disjoint_left.1 hdisj h hM'

/-- The first error event of the classifier lies in the exit event of the first ball. -/
theorem measureReal_ballClassifier_ne_true_le (θ₀ : 𝕍) (ρ₀ : ℝ) (M' : Ω → J → ℝ) :
    P.real {ω | ballClassifier hS ν θ₀ ρ₀ (M' ω) ≠ true} ≤
      P.real {ω | M' ω ∉ fisherBall hS ν θ₀ ρ₀} :=
  measureReal_mono fun ω hω h ↦ hω ((ballClassifier_eq_true_iff hS ν θ₀ ρ₀ (M' ω)).2 h)

/-- The second error event of the classifier lies in the exit event of the second ball, once the
two balls are disjoint. -/
theorem measureReal_ballClassifier_ne_false_le {θ₀ θ₁ : 𝕍} {ρ₀ ρ₁ : ℝ}
    (hdisj : Disjoint (fisherBall hS ν θ₀ ρ₀) (fisherBall hS ν θ₁ ρ₁)) (M' : Ω → J → ℝ) :
    P.real {ω | ballClassifier hS ν θ₀ ρ₀ (M' ω) ≠ false} ≤
      P.real {ω | M' ω ∉ fisherBall hS ν θ₁ ρ₁} :=
  measureReal_mono fun ω hω h ↦ hω (ballClassifier_eq_false_of_disjoint hS ν hdisj h)

/-- **Separated responses give disjoint balls**: `ρ₀ + ρ₁ ≤ d_F(θ₀, θ₁)`. -/
theorem disjoint_fisherBall {θ₀ θ₁ : 𝕍} {ρ₀ ρ₁ : ℝ} (hsep : ρ₀ + ρ₁ ≤ fisherDist S ν θ₀ θ₁) :
    Disjoint (fisherBall hS ν θ₀ ρ₀) (fisherBall hS ν θ₁ ρ₁) := by
  rw [Set.disjoint_left]
  intro M' h₀ h₁
  have htri := fisherDist_triangle hS ν θ₀ (θr M') θ₁
  rw [fisherDist_comm hS ν (x := θr M')] at htri
  simp only [fisherBall, mem_ofPred_eq] at h₀ h₁
  linarith

end Classifier

end Laplace.Multi
