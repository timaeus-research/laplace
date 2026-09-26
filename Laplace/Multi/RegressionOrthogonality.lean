/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DualFlat

/-!
# The regression projection is the `L²(Q)`-orthogonal projection onto the scores

For an interior response `M` with `Q = Π(M)` and a bounded observable `g`:

* the normal part is orthogonal to every score, `⟨N_M g, ℓ_{M,u}⟩_{L²(Q)} = 0`
  (`integral_normalProj_mul_responseScore`, recalled), and to the regression part, `⟨B_M g, N_M
  g⟩_{L²(Q)} = 0` (`integral_regProj_mul_normalProj`);
* the centred observable decomposes as `g − E_Q g = B_M g + N_M g`
  (`sub_integral_eq_regProj_add_normalProj`);
* Pythagoras: `E_Q (g − E_Q g)² = E_Q (B_M g)² + E_Q (N_M g)²`
  (`integral_sq_sub_eq_regProj_add_normalProj`).

So `B_M` is the orthogonal projection of `L²(Q)` (centred functions) onto the tangent scores, and
`N_M` the projection onto their orthogonal complement; this is the Hilbert-space meaning of the
tangent retraction and of the normal Hessian. It is orthogonality in `L²(Q)`, not in `L²(ν)`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The centred observable is the sum of its regression and normal parts. -/
theorem sub_integral_eq_regProj_add_normalProj {g : X → ℝ} (hg : Bdd g) (x : X) :
    g x - (∫ y, g y ∂(Pfam (θr M))) = regProj hS ν M hg x + normalProj hS ν M hg x := by
  unfold normalProj
  ring

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- The regression and normal parts are orthogonal in `L²(Q)`. -/
theorem integral_regProj_mul_normalProj {g : X → ℝ} (hg : Bdd g) :
    ∫ x, regProj hS ν M hg x * normalProj hS ν M hg x ∂(Pfam (θr M)) = 0 := by
  have h := integral_normalProj_mul_responseScore hS ν hrel hg
    ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩
  unfold regProj
  refine (integral_congr_ae (Eventually.of_forall fun x ↦ ?_)).trans h
  ring

/-- **Pythagoras for the regression projection**:
`E_Q (g − E_Q g)² = E_Q (B_M g)² + E_Q (N_M g)²`. -/
theorem integral_sq_sub_eq_regProj_add_normalProj {g : X → ℝ} (hg : Bdd g) :
    ∫ x, (g x - ∫ y, g y ∂(Pfam (θr M))) ^ 2 ∂(Pfam (θr M)) =
      (∫ x, regProj hS ν M hg x ^ 2 ∂(Pfam (θr M))) +
        ∫ x, normalProj hS ν M hg x ^ 2 ∂(Pfam (θr M)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hB : Bdd (regProj hS ν M hg) := bdd_responseScore hS ν M _
  have hN : Bdd (normalProj hS ν M hg) := bdd_normalProj hS ν hg
  have h1 : Integrable (fun x ↦ regProj hS ν M hg x ^ 2) (Pfam (θr M)) := by
    have := integrable_of_bdd_prob (Pfam (θr M)) (hB.mul hB)
    exact this.congr (Eventually.of_forall fun x ↦ by simp [sq])
  have h2 : Integrable (fun x ↦ normalProj hS ν M hg x ^ 2) (Pfam (θr M)) := by
    have := integrable_of_bdd_prob (Pfam (θr M)) (hN.mul hN)
    exact this.congr (Eventually.of_forall fun x ↦ by simp [sq])
  have h3 : Integrable (fun x ↦ 2 * (regProj hS ν M hg x * normalProj hS ν M hg x))
      (Pfam (θr M)) := (integrable_of_bdd_prob (Pfam (θr M)) (hB.mul hN)).const_mul 2
  have h12 : Integrable (fun x ↦ regProj hS ν M hg x ^ 2 + normalProj hS ν M hg x ^ 2)
      (Pfam (θr M)) := h1.add h2
  have e : ∀ x, (g x - ∫ y, g y ∂(Pfam (θr M))) ^ 2 =
      (regProj hS ν M hg x ^ 2 + normalProj hS ν M hg x ^ 2) +
        2 * (regProj hS ν M hg x * normalProj hS ν M hg x) := fun x ↦ by
    rw [sub_integral_eq_regProj_add_normalProj hS ν hg x]
    ring
  simp_rw [e]
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul,
    integral_regProj_mul_normalProj hS ν hrel hg, mul_zero, add_zero]

end Laplace.Multi
