/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.LocatedCutoff
import Laplace.Multi.ShiftNormalization

/-!
# The located grand headline

Composes the translation bridge, the located cutoff removal, location
recovery, and the base-case-free centred jet headline into the
located form of the germbij Theorem 3.1 inverse direction: two losses
located at unknown centres, one physical compactly-supported data
premise on a common actual region containing balls around both
centres, conclusion `p₁ = p₂` and equality of all positive-order
centred derivative tensors
(`located_positive_jet_recovery_of_ccData`).

The step the deliberation flagged as delicate — transporting the
data premise to centred form — is done by observable
reparametrization: once the centres coincide, the located moment of
`Q (· - p)` IS the centred moment of `Q`, and the located
cutoff-removal theorem already supplies data for every smooth
polynomial-growth actual observable, so the centred superPoly
headline applies with no further support conditions.
-/

open Real MeasureTheory Filter Topology Asymptotics Metric
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ} {L₁ L₂ : EuclidD d → ℝ}
  {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}

/-- Coordinate observables are smooth. -/
theorem contDiff_coord (i : Fin d) :
    ContDiff ℝ ∞ (fun w : EuclidD d ↦ w i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

/-- Coordinate observables have polynomial growth. -/
theorem hasPolynomialGrowth_coord (i : Fin d) :
    HasPolynomialGrowth (fun w : EuclidD d ↦ w i) := by
  refine ⟨1, 1, zero_le_one, fun x ↦ ?_⟩
  rw [one_mul, pow_one]
  have := euclid_abs_coord_le_norm x i
  linarith [norm_nonneg x]

/-- Reparametrization of the located moment: once located at `p`,
the located moment of `Q (· - p)` is the centred moment of `Q`. -/
theorem LocalLaplaceDomain.locatedMomentT_sub_observable
    {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}
    (A : LocalLaplaceDomain L H) (p : EuclidD d)
    (Q : EuclidD d → ℝ) (t : ℝ) :
    A.locatedMomentT p (fun w ↦ Q (w - p)) t =
      A.posteriorMomentT Q t := by
  unfold locatedMomentT
  congr 1
  funext y
  simp

open LocalLaplaceDomain in
/-- **The located grand headline** (germbij Theorem 3.1, inverse
direction, located form): two localized nondegenerate losses at
unknown centres whose physical moment families agree beyond all
orders on every smooth compactly supported test in a common actual
region containing balls around both centres have the same centre and
equal derivative tensors at every positive order. -/
theorem located_positive_jet_recovery_of_ccData
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H₁)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H₂)
    (hsymm₁ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    {p₁ p₂ : EuclidD d} {V : Set (EuclidD d)} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hb₁ : Metric.ball p₁ r₁ ⊆ V) (hb₂ : Metric.ball p₂ r₂ ⊆ V)
    (hdata : ∀ k (h2 : 2 < k), ∀ φ : EuclidD d → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      Laplace.SuperPoly (fun t : ℝ ↦
        regionMomentT (fun w ↦ L₁ (w - p₁))
          (translatedRegion p₁ (A k h2).toLocalLaplaceDomain.U) φ t -
        regionMomentT (fun w ↦ L₂ (w - p₂))
          (translatedRegion p₂ (B k h2).toLocalLaplaceDomain.U) φ t)) :
    p₁ = p₂ ∧
      ∀ j, 0 < j → iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 := by
  -- located data for every smooth polynomial-growth observable, per k
  have hloc : ∀ k (h2 : 2 < k), ∀ P : EuclidD d → ℝ,
      ContDiff ℝ ∞ P → HasPolynomialGrowth P →
      Laplace.SuperPoly (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.locatedMomentT p₁ P t -
        (B k h2).toLocalLaplaceDomain.locatedMomentT p₂ P t) :=
    fun k h2 P hPs hPg ↦
      superPoly_locatedMoment_of_ccData
        (A k h2).toLocalLaplaceDomain (B k h2).toLocalLaplaceDomain
        p₁ p₂ hr₁ hr₂ hb₁ hb₂ (hdata k h2) hPs hPg
  -- location recovery from the coordinate observables
  have hp : p₁ = p₂ := by
    refine location_eq_of_superPoly_first_moments
      (A 3 (by norm_num)).toLocalLaplaceDomain
      (B 3 (by norm_num)).toLocalLaplaceDomain p₁ p₂ fun i ↦ ?_
    exact hloc 3 (by norm_num) (fun w ↦ w i)
      (contDiff_coord i) (hasPolynomialGrowth_coord i)
  subst hp
  refine ⟨rfl, ?_⟩
  -- centred data through the reparametrization Q ↦ Q (· - p₁)
  have hcentred : ∀ k (h2 : 2 < k), ∀ Q : EuclidD d → ℝ,
      ContDiff ℝ ∞ Q → HasPolynomialGrowth Q →
      Laplace.SuperPoly (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT Q t -
        (B k h2).toLocalLaplaceDomain.posteriorMomentT Q t) := by
    intro k h2 Q hQs hQg
    have hPs : ContDiff ℝ ∞ fun w ↦ Q (w - p₁) :=
      hQs.comp (contDiff_id.sub contDiff_const)
    have hPg : HasPolynomialGrowth fun w ↦ Q (w - p₁) := by
      simpa [sub_eq_neg_add] using hQg.comp_const_add (-p₁)
    have h := hloc k h2 (fun w ↦ Q (w - p₁)) hPs hPg
    refine h.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    beta_reduce
    rw [locatedMomentT_sub_observable, locatedMomentT_sub_observable]
  -- feed the base-case-free centred headline
  refine smooth_positive_jet_recovery_of_superPoly_moments A B
    hsymm₁ hsymm₂ ?_ ?_
  · intro i j
    exact hcentred 3 (by norm_num) (fun w ↦ w i * w j)
      (contDiff_coord_mul i j) (hasPolynomialGrowth_coord_mul i j)
  · intro k h2 m
    exact hcentred k h2 (monomialTest m)
      (contDiff_monomialTest m) (monomialTest_hasPolynomialGrowth m)

end Laplace.Multi
