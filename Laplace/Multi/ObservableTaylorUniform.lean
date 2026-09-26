/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DensityPeanoUniform

/-!
# The compact-uniform observable Taylor expansion

The form of the second-order response most users of the atlas apply: for a bounded observable `F`
with `|F| ≤ B_F`, uniformly on compact convex sets `C` of interior responses,

`E_{Π(M+z)}F = E_{Π(M)}F + E_{Π(M)}[F ℓ_{M,z}] + ½ E_{Π(M)}[F N_M(ℓ_{M,z}²)] + o(‖z‖²) B_F`

(`integral_response_peano_uniform`), read off from the compact-uniform total-variation expansion.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The compact-uniform observable Taylor expansion.** -/
theorem integral_response_peano_uniform {C : Set (J → ℝ)} (hC : IsCompact C) (hCc : Convex ℝ C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {F : X → ℝ} (hF : Bdd F)
    {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) :
    ∀ ε > 0, ∃ δ > 0, ∀ M ∈ C, ∀ z : 𝕍, M + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |(∫ x, F x ∂(Pfam (θr (M + z)))) - (∫ x, F x ∂(Pfam (θr M))) -
        (∫ x, F x * responseScore hS ν M z x ∂(Pfam (θr M))) -
        (1 / 2) * ∫ x, F x * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x ∂(Pfam (θr M))| ≤
      BF * (ε * ‖z‖ ^ 2) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := integral_abs_famDens_response_peano_uniform hS ν hC hCc hCK ε hε
  refine ⟨δ, hδ, fun M hM z hMz hz ↦ ?_⟩
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF (Classical.arbitrary X))
  obtain ⟨hFm, -⟩ := hF
  have hN := bdd_normalProj hS ν (M := M)
    ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z))
  have hI : ∀ (N : J → ℝ) (g : X → ℝ), Bdd g → Integrable (fun x ↦ famDens S ν N x * g x) ν :=
    fun N g hg ↦ by
      obtain ⟨hgm, Bg, hBg⟩ := hg
      exact (integrable_famDens hS ν N).mul_bdd hgm.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hBg x)
  have h1 := hI (θr (M + z)) F ⟨hFm, BF, hBF⟩
  have h2 := hI (θr M) F ⟨hFm, BF, hBF⟩
  have h3 := hI (θr M) _ (Bdd.mul ⟨hFm, BF, hBF⟩ (bdd_responseScore hS ν M z))
  have h4 := (hI (θr M) _ (Bdd.mul ⟨hFm, BF, hBF⟩ hN)).const_mul (1 / 2 : ℝ)
  have h12 : Integrable (fun x ↦ famDens S ν (θr (M + z)) x * F x -
      famDens S ν (θr M) x * F x) ν := h1.sub h2
  have h123 : Integrable (fun x ↦ famDens S ν (θr (M + z)) x * F x -
      famDens S ν (θr M) x * F x -
      famDens S ν (θr M) x * (F x * responseScore hS ν M z x)) ν := h12.sub h3
  rw [integral_famDens_mul hS ν, integral_famDens_mul hS ν, integral_famDens_mul hS ν,
    integral_famDens_mul hS ν, ← integral_const_mul, ← integral_sub h1 h2,
    ← integral_sub h12 h3, ← integral_sub h123 h4]
  have hI5 : Integrable (fun x ↦ |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x *
      (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
        ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)|) ν := by
    have hb : Bdd fun x ↦ 1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
        ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x :=
      ((Bdd.const 1).add (bdd_responseScore hS ν M z)).add (Bdd.const_mul _ hN)
    exact ((integrable_famDens hS ν _).sub (hI (θr M) _ hb)).abs
  calc |∫ x, famDens S ν (θr (M + z)) x * F x - famDens S ν (θr M) x * F x -
        famDens S ν (θr M) x * (F x * responseScore hS ν M z x) -
        1 / 2 * (famDens S ν (θr M) x * (F x * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)) ∂ν|
      ≤ ∫ x, |famDens S ν (θr (M + z)) x * F x - famDens S ν (θr M) x * F x -
        famDens S ν (θr M) x * (F x * responseScore hS ν M z x) -
        1 / 2 * (famDens S ν (θr M) x * (F x * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x))| ∂ν := by
        have := norm_integral_le_integral_norm (μ := ν)
          (fun x ↦ famDens S ν (θr (M + z)) x * F x - famDens S ν (θr M) x * F x -
            famDens S ν (θr M) x * (F x * responseScore hS ν M z x) -
            1 / 2 * (famDens S ν (θr M) x * (F x * normalProj hS ν M
              ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)))
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ x, BF * |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x *
        (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ∂ν := by
        refine integral_mono (h123.sub h4).abs (hI5.const_mul BF) fun x ↦ ?_
        have e : famDens S ν (θr (M + z)) x * F x - famDens S ν (θr M) x * F x -
            famDens S ν (θr M) x * (F x * responseScore hS ν M z x) -
            1 / 2 * (famDens S ν (θr M) x * (F x * normalProj hS ν M
              ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)) =
            F x * (famDens S ν (θr (M + z)) x - famDens S ν (θr M) x *
              (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
                ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)) := by ring
        rw [e, abs_mul]
        exact mul_le_mul_of_nonneg_right (hBF x) (abs_nonneg _)
    _ = BF * ∫ x, |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x *
        (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ∂ν :=
        integral_const_mul _ _
    _ ≤ BF * (ε * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left (h M hM z hMz hz) hBF0

end Laplace.Multi
