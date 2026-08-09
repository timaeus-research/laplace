/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.LambdaPackage

/-!
# The asymptotically stable recovery interface

Stage C1 of the smooth-germ programme. The Taylor polynomial of a
smooth loss never has *exactly* the moment data of the loss — the
replacement carries order-controlled errors — so the smooth-germ
transfer needs recovery theorems whose data hypotheses are
`Tendsto`-to-zero at the coefficient-sensitive scales rather than
eventual equality. The pieces already exist
(`base_recovery_of_tendsto`, and `jet_recovery`'s hypotheses are
already limits); this file combines them into the variable-base
stable theorem (`jet_recovery_stable`) and its `k = 1` nondegenerate
form (`nondegenerateJet_recovery_stable`), the exact interfaces
stages C2-C6 will consume.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- **The asymptotically stable variable-base recovery** (stage C1):
if the difference of normalized second moments vanishes at scale
`q²`'s leading order (i.e. tends to `0`), and for each rung `r` the
difference of the matching moments vanishes at scale `q^r`, then the
bases and all coefficients agree. No exact-equality data anywhere. -/
theorem jet_recovery_stable
    {k R : ℕ} {a₁ a₂ ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ} (hk : 1 ≤ k)
    (h1 : HasPositiveJetProfile R a₁ ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a₂ ρ₂ c₂)
    (hdata2 : Tendsto (fun q : ℝ ↦
      normalizedJetMoment k R 2 a₁ q c₁ -
        normalizedJetMoment k R 2 a₂ q c₂) (𝓝[>] 0) (𝓝 0))
    (hdataR : ∀ i : Fin R, Tendsto (fun q : ℝ ↦
      (normalizedJetMoment k R (2 * k + (i.1 + 1)) a₁ q c₁ -
        normalizedJetMoment k R (2 * k + (i.1 + 1)) a₂ q c₂) /
        q ^ (i.1 + 1)) (𝓝[>] 0) (𝓝 0)) :
    a₁ = a₂ ∧ c₁ = c₂ := by
  have ha := base_recovery_of_tendsto hk h1 h2 hdata2
  subst ha
  exact ⟨rfl, jet_recovery hk h1.base_pos h1 h2 hdataR⟩

/-- **The `k = 1` nondegenerate stable recovery**: the interface the
smooth-loss reduction consumes, in the note's `λ/2` normalisation. -/
theorem nondegenerateJet_recovery_stable
    {R : ℕ} {lam₁ lam₂ ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ}
    (h1 : HasPositiveJetProfile R (lam₁ / 2) ρ₁ c₁)
    (h2 : HasPositiveJetProfile R (lam₂ / 2) ρ₂ c₂)
    (hdata2 : Tendsto (fun q : ℝ ↦
      normalizedJetMoment 1 R 2 (lam₁ / 2) q c₁ -
        normalizedJetMoment 1 R 2 (lam₂ / 2) q c₂) (𝓝[>] 0) (𝓝 0))
    (hdataR : ∀ i : Fin R, Tendsto (fun q : ℝ ↦
      (normalizedJetMoment 1 R (2 + (i.1 + 1)) (lam₁ / 2) q c₁ -
        normalizedJetMoment 1 R (2 + (i.1 + 1)) (lam₂ / 2) q c₂) /
        q ^ (i.1 + 1)) (𝓝[>] 0) (𝓝 0)) :
    lam₁ = lam₂ ∧ c₁ = c₂ := by
  have h := jet_recovery_stable (k := 1) le_rfl h1 h2 hdata2 hdataR
  exact ⟨by linarith [h.1], h.2⟩

end Laplace.OneD
