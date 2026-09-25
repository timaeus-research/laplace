/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TermScoreResponse

/-!
# The normalised response of the assembled leading measure

The leading measure of the atlas is the sum `μ_a = ∑_k μ_{k,a}` of the dominant chart terms, each
of exponential form with its own weight `H_k`, profile `P_k`, face map and constant `B_k`, all
sharing the affine unit `U_a = ∑ aᵢ hᵢ` of the mixture. Astra's round-20 "single most valuable
next theorem": the normalised leading law `⟨φ⟩_a = ∑_k ∫φ dμ_{k,a} / ∑_k μ_{k,a}(X)` responds to a
data direction `v` by

  `D_v ⟨φ⟩_a = −(∑_k ∫ φ S_{k,v} dμ_{k,a} − ⟨φ⟩_a ∑_k ∫ S_{k,v} dμ_{k,a}) / ∑_k μ_{k,a}(X)`
  (`hasDerivAt_assembledPosterior`),

which is `−Cov_{μ̄_a}(φ, S_v)` on the disjoint union of the terms, with the piecewise score
`S_v|_k = B_k R_v(u∞_k) P_k`. This includes the movement of the **relative masses** of the chart
terms with the weight: it is the response of the assembled law, not an average of the separately
normalised term responses.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {ι κ : Type*} [Fintype ι]
  [Fintype κ]

/-- The assembled unnormalised integral `∑_k ∫ φ dμ_{k,a}` of a finite family of exponential-form
terms (on a common base measure `m`, with a common unit family `h`). -/
noncomputable def assembledCoef (m : Measure X) (H P : κ → X → ℝ) (uw : κ → X → Y)
    (h : ι → Y → ℝ) (B : κ → ℝ) (φ : X → ℝ) (a : ι → ℝ) : ℝ :=
  ∑ k, termCoef m (H k) (P k) (uw k) h (B k) φ a

/-- The assembled normalised law `⟨φ⟩_a`. -/
noncomputable def assembledPosterior (m : Measure X) (H P : κ → X → ℝ) (uw : κ → X → Y)
    (h : ι → Y → ℝ) (B : κ → ℝ) (φ : X → ℝ) (a : ι → ℝ) : ℝ :=
  assembledCoef m H P uw h B φ a / assembledCoef m H P uw h B (fun _ ↦ 1) a

/-- The score-weighted assembled integral `∑_k ∫ φ S_{k,v} dμ_{k,a}`. -/
noncomputable def assembledScoreCoef (m : Measure X) (H P : κ → X → ℝ) (uw : κ → X → Y)
    (h : ι → Y → ℝ) (B : κ → ℝ) (φ : X → ℝ) (a v : ι → ℝ) : ℝ :=
  ∑ k, ∫ x, φ x * termScore (P k) (uw k) h (B k) v x * H k x *
    Real.exp (-(B k * faceUnit h a (uw k x) * P k x)) ∂m

/-- **The score identity for the assembled measure**:
`D_v ∑_k ∫ φ dμ_{k,a} = −∑_k ∫ φ S_{k,v} dμ_{k,a}`. -/
theorem hasDerivAt_assembledCoef [Nonempty ι] [Nonempty Y] {m : Measure X} {H P : κ → X → ℝ}
    {uw : κ → X → Y} {h : ι → Y → ℝ} {a : ι → ℝ} {B c : κ → ℝ} {Mh : ℝ}
    (hd : ∀ k, ScoreData m (H k) (P k) (uw k) h a (B k) (c k) Mh) {φ : X → ℝ}
    (hφm : Measurable φ) (hdom : ∀ k, Integrable ((hd k).envelope φ) m) (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ assembledCoef m H P uw h B φ (a + ε • v))
      (-assembledScoreCoef m H P uw h B φ a v) 0 := by
  have h1 : ∀ k ∈ Finset.univ, HasDerivAt
      (fun ε : ℝ ↦ termCoef m (H k) (P k) (uw k) h (B k) φ (a + ε • v))
      (-∫ x, φ x * termScore (P k) (uw k) h (B k) v x * H k x *
        Real.exp (-(B k * faceUnit h a (uw k x) * P k x)) ∂m) 0 := fun k _ ↦
    (hd k).hasDerivAt_termCoef hφm (hdom k) v
  have := HasDerivAt.fun_sum h1
  unfold assembledCoef assembledScoreCoef
  rw [Finset.sum_neg_distrib] at this
  exact this

/-- **The normalised response of the assembled leading measure** (Astra round 20):
`D_v ⟨φ⟩_a = −(∑_k ∫ φ S_{k,v} dμ_{k,a} − ⟨φ⟩_a · ∑_k ∫ S_{k,v} dμ_{k,a}) / ∑_k μ_{k,a}(X)`, i.e.
`−Cov_{μ̄_a}(φ, S_v)` on the disjoint union of the terms, relative masses included. -/
theorem hasDerivAt_assembledPosterior [Nonempty ι] [Nonempty Y] {m : Measure X}
    {H P : κ → X → ℝ} {uw : κ → X → Y} {h : ι → Y → ℝ} {a : ι → ℝ} {B c : κ → ℝ} {Mh : ℝ}
    (hd : ∀ k, ScoreData m (H k) (P k) (uw k) h a (B k) (c k) Mh) {φ : X → ℝ}
    (hφm : Measurable φ) (hdom : ∀ k, Integrable ((hd k).envelope φ) m)
    (hdom1 : ∀ k, Integrable ((hd k).envelope fun _ ↦ 1) m)
    (hZ : assembledCoef m H P uw h B (fun _ ↦ 1) a ≠ 0) (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ assembledPosterior m H P uw h B φ (a + ε • v))
      (-(assembledScoreCoef m H P uw h B φ a v -
          assembledPosterior m H P uw h B φ a * assembledScoreCoef m H P uw h B (fun _ ↦ 1) a v) /
        assembledCoef m H P uw h B (fun _ ↦ 1) a) 0 := by
  have hN := hasDerivAt_assembledCoef hd hφm hdom v
  have hZ' := hasDerivAt_assembledCoef hd (φ := fun _ ↦ (1 : ℝ)) measurable_const hdom1 v
  have hZ0 : assembledCoef m H P uw h B (fun _ ↦ (1 : ℝ)) (a + (0 : ℝ) • v) ≠ 0 := by
    simpa using hZ
  have hdiv := hN.div hZ' hZ0
  refine hdiv.congr_deriv ?_
  simp only [zero_smul, add_zero, assembledPosterior]
  set N := assembledCoef m H P uw h B φ a with hN'
  set Z := assembledCoef m H P uw h B (fun _ ↦ (1 : ℝ)) a with hZ''
  set NS := assembledScoreCoef m H P uw h B φ a v with hNS
  set ZS := assembledScoreCoef m H P uw h B (fun _ ↦ (1 : ℝ)) a v with hZS
  clear_value N Z NS ZS
  field_simp
  ring

end Laplace.Multi
