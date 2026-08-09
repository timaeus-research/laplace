/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.DegreeRecovery

/-!
# The jet induction: full recovery from moment data

Stage J7, closing the tensor programme: strong induction over the
first unknown degree. Two losses with higher-order domain packages at
each degree `2 < k ≤ N`, matched jets below three (degree zero is
observationally undetermined — constants shift nothing; degrees one
and two follow for a common `H` from the shared quadratic
approximation and `hessian_recovery`, so they enter as the base
hypothesis), permutation-symmetric tensors, and `o(q^(k-2))` moment
data at every degree have equal derivative tensors through order `N`
(`finite_jet_recovery`); with packages and data at every degree,
every derivative tensor agrees (`smooth_jet_recovery_multi`).
-/

open Real Filter Topology Asymptotics

namespace Laplace.Multi

namespace HigherLaplaceDomain

variable {d : ℕ} {L₁ L₂ : EuclidD d → ℝ}
  {H : Matrix (Fin d) (Fin d) ℝ}

/-- **Finite-jet recovery** (J7): moment data at every degree up to
`N` identifies the full jet through order `N`. -/
theorem finite_jet_recovery {N : ℕ}
    (A : ∀ k, 2 < k → k ≤ N → HigherLaplaceDomain k L₁ H)
    (B : ∀ k, 2 < k → k ≤ N → HigherLaplaceDomain k L₂ H)
    (hbase : ∀ j < 3,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : ∀ k, 2 < k → k ≤ N →
      (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 2 < k → k ≤ N →
      (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ k (h2 : 2 < k) (hN : k ≤ N),
      ∀ P : EuclidD d → ℝ, Continuous P →
      HasPolynomialGrowth P → IsHomogeneousOfDegree k P →
      (fun q : ℝ ↦ (A k h2 hN).rescaledMoment P q -
        (B k h2 hN).rescaledMoment P q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) :
    ∀ j, j ≤ N →
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjN
    by_cases hj3 : j < 3
    · exact hbase j hj3
    · have h2j : 2 < j := by omega
      exact iteratedFDeriv_recovery_of_moment_rates h2j
        (A j h2j hjN) (B j h2j hjN)
        (fun i hi ↦ ih i hi (by omega))
        (hsymm₁ j h2j hjN) (hsymm₂ j h2j hjN)
        (hdata j h2j hjN)

/-- **Smooth-jet recovery** (J7, all orders): packages and moment
data at every degree identify every derivative tensor at the
origin. -/
theorem smooth_jet_recovery_multi
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H)
    (hbase : ∀ j < 3,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ k (h2 : 2 < k),
      ∀ P : EuclidD d → ℝ, Continuous P →
      HasPolynomialGrowth P → IsHomogeneousOfDegree k P →
      (fun q : ℝ ↦ (A k h2).rescaledMoment P q -
        (B k h2).rescaledMoment P q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) :
    ∀ j, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 := by
  intro j
  exact finite_jet_recovery (N := j)
    (fun k h2 _ ↦ A k h2) (fun k h2 _ ↦ B k h2)
    hbase
    (fun k h2 _ ↦ hsymm₁ k h2) (fun k h2 _ ↦ hsymm₂ k h2)
    (fun k h2 hN ↦ hdata k h2)
    j le_rfl

end HigherLaplaceDomain

end Laplace.Multi
