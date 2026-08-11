/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.HessianRecovery
import Laplace.Multi.ExpansionBridge

/-!
# The k = 2 superPoly covariance bridge

The 2026-08-10 fidelity review found the superPoly-language headline
`smooth_jet_recovery_of_superPoly_moments` assuming the Hessian
equality (`hbase` at `j = 2`, and a shared `H`) that the germbij
note's Theorem 3.1 derives from the data. This file supplies the
missing `k = 2` bridge at the matrix level: two losses whose localized
second-moment families, as functions of the temperature, agree beyond
all orders have equal package matrices
(`hessian_recovery_of_superPoly_moments`). No first-moment agreement
is needed — each package's first moments are `o(q)` on their own
(`posteriorMoment_coord_isLittleO`), so the product terms in the
covariance difference are `o(q²)` per package, and only the
second-moment difference consumes data, transported through the
`t = q⁻²` substitution at rate `o(q²)` and fed to the merged
`hessian_recovery`.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

namespace LocalLaplaceDomain

variable {d : ℕ}

/-- The covariance form in the expansion bridge's moment
vocabulary. -/
theorem covariance_eq_posteriorMoment {L : EuclidD d → ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ} (A : LocalLaplaceDomain L H)
    (i j : Fin d) (q : ℝ) :
    A.covariance i j q =
      A.posteriorMoment (fun w ↦ w i * w j) q -
        A.posteriorMoment (fun w ↦ w i) q *
          A.posteriorMoment (fun w ↦ w j) q := rfl

/-- **Bare first moments are `o(q)`**, per package: the little-o form
of the merged first-moment rate. -/
theorem posteriorMoment_coord_isLittleO {L : EuclidD d → ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ} (A : LocalLaplaceDomain L H)
    (i : Fin d) :
    (fun q : ℝ ↦ A.posteriorMoment (fun w ↦ w i) q)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q := by
  rw [Asymptotics.isLittleO_iff_tendsto' ?hne]
  case hne =>
    filter_upwards [self_mem_nhdsWithin] with q hq h0
    exact absurd h0 (ne_of_gt hq)
  exact A.tendsto_normalized_first_moment i

/-- **Rate transport for moment differences**: a superpolynomially
small temperature-level moment difference is `o(q^r)` at `0⁺` for
every `r`. -/
theorem posteriorMoment_sub_isLittleO {L₁ L₂ : EuclidD d → ℝ}
    {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A : LocalLaplaceDomain L₁ H₁) (B : LocalLaplaceDomain L₂ H₂)
    (f : EuclidD d → ℝ)
    (hf : Laplace.SuperPoly (fun t : ℝ ↦
      A.posteriorMomentT f t - B.posteriorMomentT f t)) (r : ℕ) :
    (fun q : ℝ ↦ A.posteriorMoment f q - B.posteriorMoment f q)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ r := by
  have h := isLittleO_pow_of_superPoly hf 0 r
  refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [pow_zero, div_one, posteriorMomentT_inv_sq _ _ hq,
    posteriorMomentT_inv_sq _ _ hq]

/-- Products of bare first moments are `o(q²)`, per package. -/
theorem posteriorMoment_coord_mul_isLittleO {L : EuclidD d → ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ} (A : LocalLaplaceDomain L H)
    (i j : Fin d) :
    (fun q : ℝ ↦ A.posteriorMoment (fun w ↦ w i) q *
        A.posteriorMoment (fun w ↦ w j) q)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ 2 := by
  have h := (A.posteriorMoment_coord_isLittleO i).mul
    (A.posteriorMoment_coord_isLittleO j)
  refine h.congr' (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards with q
  rw [sq]

end LocalLaplaceDomain

/-- **The k = 2 superPoly covariance bridge** (germbij Theorem 3.1,
Hessian step, in the note's data language): two localized losses whose
second-moment families, as functions of the temperature, agree beyond
all orders have equal package matrices. -/
theorem hessian_recovery_of_superPoly_moments {d : ℕ}
    {L₁ L₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A : LocalLaplaceDomain L₁ H₁) (B : LocalLaplaceDomain L₂ H₂)
    (hdata : ∀ i j : Fin d, Laplace.SuperPoly (fun t : ℝ ↦
      A.posteriorMomentT (fun w ↦ w i * w j) t -
        B.posteriorMomentT (fun w ↦ w i * w j) t)) :
    H₁ = H₂ := by
  refine LocalLaplaceDomain.hessian_recovery A B fun i j ↦ ?_
  have h2 := LocalLaplaceDomain.posteriorMoment_sub_isLittleO A B _
    (hdata i j) 2
  have hA := A.posteriorMoment_coord_mul_isLittleO i j
  have hB := B.posteriorMoment_coord_mul_isLittleO i j
  refine (h2.sub (hA.sub hB)).congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with q
  rw [A.covariance_eq_posteriorMoment, B.covariance_eq_posteriorMoment]
  ring

end Laplace.Multi
