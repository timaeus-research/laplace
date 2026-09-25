/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.CertificateLP
import Laplace.Multi.VertexCertificate
import Laplace.Multi.WallTiedTruth
import Laplace.Multi.TermData

/-!
# Certificates from the chart's linear programme

The certificate-coverage audit (Astra round 15, item 2). The term theorems of a wall chart take
a scale `α` with two certificates: feasibility for the chart's constrained LP
(`ConstrainedFeasible`) and integrability of the limiting profile (`ProfileIntegrableOf`). The
profile certificate was proved from explicit dual conditions at the two nondegenerate shapes of
an isolated LP optimum (`ProfileIntegrableOf.of_vertex`, `ProfileIntegrableOf.of_twoScaled`),
and `CertificateLP` identified those conditions with unique minimality (`UniqueLPMin`) of `α`
for the LP `min ∑ (r_j + 1) α_j` over `α ≥ 0`, `Q·α ≤ γ`, `κ·α ≥ δ`. This file composes the two:

* `ProfileIntegrableOf.of_uniqueLPMin_vertex`: a strict-truth vertex `α = (δ/κ_j) e_j` that is the
  unique LP minimiser (all `κ > 0`) carries the profile certificate;
* `ProfileIntegrableOf.of_uniqueLPMin_twoScaled`: a tied-truth optimum on two scaled coordinates
  with `Δ ≠ 0` and the dual decomposition `r_S + 1 = ηκ_S − θQ_S` that is the unique LP minimiser
  carries the profile certificate (`UniqueLPMin.comp_equiv` reindexes the LP along the
  coordinate splitting);
* `TermData.vertexOfUniqueLPMin`, `TermData.twoScaledOfUniqueLPMin`: the term data of an
  admissible branch from LP uniqueness alone (feasibility is the first half of `UniqueLPMin`).

So at both nondegenerate shapes the certificate is *read off the chart's exponents*: no analytic
input beyond the phase record is needed, and the remaining regimes (tied optimum with a face of
minimisers) are the logarithmic ones handled by the tied, partial, active-truth and degenerate
constructors.
-/

open Filter MeasureTheory Set Topology Real

namespace Laplace.Multi

/-- Reindexing a unique LP minimiser along an equivalence of the coordinate set. -/
theorem UniqueLPMin.comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] {Q κ a α : ι → ℝ}
    {γ δ : ℝ} (e : ι' ≃ ι) (h : UniqueLPMin Q κ γ δ a α) :
    UniqueLPMin (Q ∘ e) (κ ∘ e) γ δ (a ∘ e) (α ∘ e) := by
  obtain ⟨⟨hα0, hQα, hκα⟩, huniq⟩ := h
  have hsum : ∀ f g : ι → ℝ, ∑ j, f (e j) * g (e j) = ∑ i, f i * g i := fun f g ↦
    Equiv.sum_comp e fun i ↦ f i * g i
  refine ⟨⟨fun j ↦ hα0 (e j), ?_, ?_⟩, fun β' hβ' hne ↦ ?_⟩
  · change ∑ j, Q (e j) * α (e j) ≤ γ
    rw [hsum]
    exact hQα
  · change δ ≤ ∑ j, κ (e j) * α (e j)
    rw [hsum]
    exact hκα
  · obtain ⟨hβ0, hQβ, hκβ⟩ := hβ'
    have hβe : ∀ i, (β' ∘ e.symm) (e i) = β' i := fun i ↦ by simp
    have hfeas : ConstrainedFeasible Q κ γ δ (β' ∘ e.symm) := by
      refine ⟨fun i ↦ hβ0 (e.symm i), ?_, ?_⟩
      · rw [← hsum Q (β' ∘ e.symm)]
        simpa only [hβe, Function.comp_apply] using hQβ
      · rw [← hsum κ (β' ∘ e.symm)]
        simpa only [hβe, Function.comp_apply] using hκβ
    have hne' : β' ∘ e.symm ≠ α := fun h ↦ hne (by
      funext j
      have := congrFun h (e j)
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using this)
    have h := huniq _ hfeas hne'
    rw [← hsum a α, ← hsum a (β' ∘ e.symm)] at h
    simpa only [hβe, Function.comp_apply] using h

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- **The profile certificate from LP uniqueness at a strict-truth vertex.** -/
theorem TruthChartsData.Phase.ProfileIntegrableOf.of_uniqueLPMin_vertex {i : D.ι}
    {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ} {α : Fin m → ℝ} (hσ : σ ≠ 0)
    (hκ : ∀ j, 0 < P.kappa i j) (j : Fin m)
    (hα : ∀ l, α l = if l = j then P.phaseExp i γ / P.kappa i j else 0)
    (hδ : 0 < P.phaseExp i γ) (hstrict : ∑ l, D.Qexp i l * α l < γ)
    (hmin : UniqueLPMin (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) (fun l ↦ P.rExp i l + 1) α) :
    P.ProfileIntegrableOf i ε b σ γ α := by
  obtain ⟨hη, hgap⟩ := (uniqueLPMin_vertex_iff hκ j hα hδ hstrict).mp hmin
  exact TruthChartsData.Phase.ProfileIntegrableOf.of_vertex P hσ j (hκ j).ne' hη
    (div_pos hδ (hκ j)) hα hstrict hgap

/-- **The profile certificate from LP uniqueness at a tied-truth two-scaled optimum.** -/
theorem TruthChartsData.Phase.ProfileIntegrableOf.of_uniqueLPMin_twoScaled {i : D.ι}
    {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ} {α : Fin m → ℝ} {ν : Type*} [Finite ν]
    (e : Fin 2 ⊕ ν ≃ Fin m) {αS : Fin 2 → ℝ} (hαS : ∀ s, 0 < αS s)
    (hα : α = fun j ↦ Sum.elim αS 0 (e.symm j)) (hσ : σ ≠ 0)
    (htied : ∑ j, P.kappa i j * α j = P.phaseExp i γ)
    (hQα : ∑ j, D.Qexp i j * α j = γ) {η θ : ℝ}
    (hΔ : P.kappa i (e (Sum.inl 0)) * D.Qexp i (e (Sum.inl 1)) -
      P.kappa i (e (Sum.inl 1)) * D.Qexp i (e (Sum.inl 0)) ≠ 0)
    (haS : ∀ s, P.rExp i (e (Sum.inl s)) + 1 =
      η * P.kappa i (e (Sum.inl s)) - θ * D.Qexp i (e (Sum.inl s)))
    (hmin : UniqueLPMin (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) (fun l ↦ P.rExp i l + 1) α) :
    P.ProfileIntegrableOf i ε b σ γ α := by
  cases nonempty_fintype ν
  have hαe : α ∘ e = Sum.elim αS 0 := by
    funext x
    simp [hα]
  have hmin' := hmin.comp_equiv e
  rw [hαe] at hmin'
  have hκα' : ∑ j, (P.kappa i ∘ e) j * Sum.elim αS 0 j = P.phaseExp i γ := by
    rw [← hαe, ← htied]
    exact Equiv.sum_comp e fun j ↦ P.kappa i j * α j
  have hQα' : ∑ j, (D.Qexp i ∘ e) j * Sum.elim αS 0 j = γ := by
    rw [← hαe, ← hQα]
    exact Equiv.sum_comp e fun j ↦ D.Qexp i j * α j
  obtain ⟨hη, hθ, hβ⟩ := (uniqueLPMin_twoScaled_iff (a := (fun l ↦ P.rExp i l + 1) ∘ e) hαS
    hκα' hQα' hΔ haS).mp hmin'
  exact TruthChartsData.Phase.ProfileIntegrableOf.of_twoScaled P e hαS hα hσ htied hQα hη hθ hΔ
    haS fun j ↦ by simpa only [Function.comp] using hβ j

/-- **Term data from LP uniqueness at a strict-truth vertex.** -/
noncomputable def TruthChartsData.Phase.TermData.vertexOfUniqueLPMin (hS : ∀ i, |D.S i| = 1)
    {σ γ : ℝ} (hσ : σ ≠ 0)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      T (D.rep i u) = truthMono (D.S i) (D.q i) u)
    {α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ} {p : TruthChartsData.Phase.TermIdx D}
    (hadm : D.admissible p.1 p.2.1 p.2.2 σ) (hκ : ∀ j, 0 < P.kappa p.1 j) (j : Fin m)
    (hα : ∀ l, α p.1 p.2.1 p.2.2 l = if l = j then P.phaseExp p.1 γ / P.kappa p.1 j else 0)
    (hδ : 0 < P.phaseExp p.1 γ) (hstrict : ∑ l, D.Qexp p.1 l * α p.1 p.2.1 p.2.2 l < γ)
    (hmin : UniqueLPMin (D.Qexp p.1) (P.kappa p.1) γ (P.phaseExp p.1 γ)
      (fun l ↦ P.rExp p.1 l + 1) (α p.1 p.2.1 p.2.2)) :
    P.TermData σ γ p :=
  TruthChartsData.Phase.TermData.vertex P hS hσ htruth hadm hmin.1
    (TruthChartsData.Phase.ProfileIntegrableOf.of_uniqueLPMin_vertex P hσ hκ j hα hδ hstrict hmin)

/-- **Term data from LP uniqueness at a tied-truth two-scaled optimum.** -/
noncomputable def TruthChartsData.Phase.TermData.twoScaledOfUniqueLPMin (hS : ∀ i, |D.S i| = 1)
    {σ γ : ℝ} (hσ : σ ≠ 0)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      T (D.rep i u) = truthMono (D.S i) (D.q i) u)
    {α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ} {p : TruthChartsData.Phase.TermIdx D}
    (hadm : D.admissible p.1 p.2.1 p.2.2 σ) {ν : Type*} [Finite ν] (e : Fin 2 ⊕ ν ≃ Fin m)
    {αS : Fin 2 → ℝ} (hαS : ∀ s, 0 < αS s)
    (hα : α p.1 p.2.1 p.2.2 = fun j ↦ Sum.elim αS 0 (e.symm j))
    (htied : ∑ j, P.kappa p.1 j * α p.1 p.2.1 p.2.2 j = P.phaseExp p.1 γ)
    (hQα : ∑ j, D.Qexp p.1 j * α p.1 p.2.1 p.2.2 j = γ) {η θ : ℝ}
    (hΔ : P.kappa p.1 (e (Sum.inl 0)) * D.Qexp p.1 (e (Sum.inl 1)) -
      P.kappa p.1 (e (Sum.inl 1)) * D.Qexp p.1 (e (Sum.inl 0)) ≠ 0)
    (haS : ∀ s, P.rExp p.1 (e (Sum.inl s)) + 1 =
      η * P.kappa p.1 (e (Sum.inl s)) - θ * D.Qexp p.1 (e (Sum.inl s)))
    (hmin : UniqueLPMin (D.Qexp p.1) (P.kappa p.1) γ (P.phaseExp p.1 γ)
      (fun l ↦ P.rExp p.1 l + 1) (α p.1 p.2.1 p.2.2)) :
    P.TermData σ γ p :=
  TruthChartsData.Phase.TermData.vertex P hS hσ htruth hadm hmin.1
    (TruthChartsData.Phase.ProfileIntegrableOf.of_uniqueLPMin_twoScaled P e hαS hα hσ htied hQα
      hΔ haS hmin)

end Laplace.Multi
