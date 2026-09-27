/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.NormalShiftBoundaryCost
import Laplace.Multi.FaceMassHellinger

/-!
# Normal-cone Cauchy coalescence

Two Fisher-Cauchy sequences `v + a n` and `v + b n` with a common base `v`, offsets in the
normal cone of a face event `A` (each `⟨a n, S⟩` constant on `A`, `≥` that constant a.e., and
bounded), both concentrating on the face (`P(A) → 1`), are asymptotically at Fisher distance
zero from each other, hence **have the same limit in the Fisher completion**.

The proof is the translated grid
`d(θ_n, η_m) ≤ d(θ_n, θ_n + b_m) + d(θ_n + b_m, θ_N + b_m) + d(θ_N + b_m, η_m)`:
the first side is a fixed normal shift along a face-concentrating sequence (cheap by
`NormalShiftBoundaryCost`), the middle side is a translated short path near face mass one
(at most twice a Cauchy tail by `FaceMassHellinger`), and the last side is again a fixed
normal shift since `θ_N + b_m = η_m + a_N`. No preferred normal ray and no quantitative gaps
are needed: the theorem is codimension-free.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Coalescence

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- Face mass tending to one means complement mass tending to zero. -/
theorem tendsto_real_compl_of_tendsto_real {θ : ℕ → J → ℝ} {A : Set X} (hA : MeasurableSet A)
    (h : Tendsto (fun n ↦ (Pfam (θ n)).real A) atTop (𝓝 1)) :
    Tendsto (fun n ↦ (Pfam (θ n)).real Aᶜ) atTop (𝓝 0) := by
  have e : ∀ n, (Pfam (θ n)).real Aᶜ = 1 - (Pfam (θ n)).real A := fun n ↦ by
    have := isProbabilityMeasure_family hS ν (θ n)
    rw [measureReal_compl hA, probReal_univ]
  simp_rw [e]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

/-- A fixed normal shift is eventually cheap along a face-concentrating sequence. -/
theorem eventually_fisherDist_add_normal_lt {θ : ℕ → J → ℝ}
    (hθ : ∀ n, θ n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {A : Set X} (hA : MeasurableSet A)
    (hcompl : Tendsto (fun n ↦ (Pfam (θ n)).real Aᶜ) atTop (𝓝 0)) {h : J → ℝ}
    (hh : h ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {c B : ℝ} (hc : ∀ x ∈ A, dirLoss S h x = c)
    (hge : ∀ᵐ x ∂ν, c ≤ dirLoss S h x) (hB : ∀ x, |dirLoss S h x - c| ≤ B) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      fisherDist S ν ⟨θ n, hθ n⟩ ⟨θ n + h, Submodule.add_mem _ (hθ n) hh⟩ < δ := by
  have hlim : Tendsto (fun n ↦ B * √((Pfam (θ n)).real Aᶜ)) atTop (𝓝 0) := by
    simpa using hcompl.sqrt.const_mul B
  filter_upwards [hlim.eventually (Iio_mem_nhds hδ)] with n hn
  exact (fisherDist_add_normal_le hS ν (θ n) h (hθ n) hh hA hc hge hB).trans_lt hn

variable [Nonempty J]

/-- A sequence of parameters converging in the completion is Cauchy. -/
theorem cauchySeq_of_tendsto_completion {u : ℕ → FisherPoint hS ν} {x : FisherCompletion hS ν}
    (hu : Tendsto (fun n ↦ (u n : FisherCompletion hS ν)) atTop (𝓝 x)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq ε hε
  exact ⟨N, fun m hm n hn ↦ by
    have := hN m hm n hn
    rwa [UniformSpace.Completion.dist_eq] at this⟩

/-- **Normal-cone Cauchy coalescence**: two face-concentrating Fisher-Cauchy sequences with a
common base and normal-cone offsets are asymptotically at Fisher distance zero. -/
theorem tendsto_dist_normalCone (v : J → ℝ) (hv : v ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    {a b : ℕ → J → ℝ} (ha : ∀ n, a n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (hb : ∀ n, b n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {A : Set X} (hA : MeasurableSet A)
    {ca cb Ba Bb : ℕ → ℝ} (hca : ∀ n, ∀ x ∈ A, dirLoss S (a n) x = ca n)
    (hgea : ∀ n, ∀ᵐ x ∂ν, ca n ≤ dirLoss S (a n) x)
    (hBa : ∀ n x, |dirLoss S (a n) x - ca n| ≤ Ba n)
    (hcb : ∀ n, ∀ x ∈ A, dirLoss S (b n) x = cb n)
    (hgeb : ∀ n, ∀ᵐ x ∂ν, cb n ≤ dirLoss S (b n) x)
    (hBb : ∀ n x, |dirLoss S (b n) x - cb n| ≤ Bb n)
    (hθ : CauchySeq fun n ↦ (⟨⟨v + a n, Submodule.add_mem _ hv (ha n)⟩⟩ : FisherPoint hS ν))
    (hη : CauchySeq fun n ↦ (⟨⟨v + b n, Submodule.add_mem _ hv (hb n)⟩⟩ : FisherPoint hS ν))
    (hθA : Tendsto (fun n ↦ (Pfam (v + a n)).real A) atTop (𝓝 1))
    (hηA : Tendsto (fun n ↦ (Pfam (v + b n)).real A) atTop (𝓝 1)) :
    Tendsto (fun n ↦ dist (⟨⟨v + a n, Submodule.add_mem _ hv (ha n)⟩⟩ : FisherPoint hS ν)
      ⟨⟨v + b n, Submodule.add_mem _ hv (hb n)⟩⟩) atTop (𝓝 0) := by
  have hθc := tendsto_real_compl_of_tendsto_real hS ν hA hθA
  have hηc := tendsto_real_compl_of_tendsto_real hS ν hA hηA
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (ε / 8) (1 / 4) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδdef ▸ lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 8 := hδdef ▸ min_le_left _ _
  have hδ4 : δ ≤ 1 / 4 := hδdef ▸ min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hθ δ hδ0
  obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.1 hη δ hδ0
  obtain ⟨N₃, hN₃⟩ :=
    eventually_atTop.1 (hθA.eventually (Ici_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1)))
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = max N₁ (max N₂ N₃) := ⟨_, rfl⟩
  have hN₁N : N₁ ≤ N := hNdef ▸ le_max_left _ _
  have hN₂N : N₂ ≤ N := hNdef ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hN₃N : N₃ ≤ N := hNdef ▸ (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (eventually_fisherDist_add_normal_lt hS ν
    (fun m ↦ Submodule.add_mem _ hv (hb m)) hA hηc (ha N) (hca N) (hgea N) (hBa N) hδ0)
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = max M₀ N := ⟨_, rfl⟩
  have hM₀M : M₀ ≤ M := hMdef ▸ le_max_left _ _
  have hNM : N ≤ M := hMdef ▸ le_max_right _ _
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 (eventually_fisherDist_add_normal_lt hS ν
    (fun n ↦ Submodule.add_mem _ hv (ha n)) hA hθc (hb M) (hcb M) (hgeb M) (hBb M) hδ0)
  refine ⟨max N₄ M, fun n hn ↦ ?_⟩
  have hnN₄ : N₄ ≤ n := le_of_max_le_left hn
  have hnM : M ≤ n := le_of_max_le_right hn
  have hnN : N ≤ n := hNM.trans hnM
  -- the four sides
  have d1 : fisherDist S ν ⟨v + a n, Submodule.add_mem _ hv (ha n)⟩
      ⟨v + a n + b M, Submodule.add_mem _ (Submodule.add_mem _ hv (ha n)) (hb M)⟩ < δ :=
    hN₄ n hnN₄
  have d4 : fisherDist S ν ⟨v + b M, Submodule.add_mem _ hv (hb M)⟩
      ⟨v + b n, Submodule.add_mem _ hv (hb n)⟩ < δ :=
    hN₂ M (hN₂N.trans hNM) n (hN₂N.trans hnN)
  have d3 : fisherDist S ν
      ⟨v + a N + b M, Submodule.add_mem _ (Submodule.add_mem _ hv (ha N)) (hb M)⟩
      ⟨v + b M, Submodule.add_mem _ hv (hb M)⟩ < δ := by
    have h := hM₀ M hM₀M
    rw [fisherDist_comm hS ν] at h
    have e : (⟨v + b M + a N, Submodule.add_mem _ (Submodule.add_mem _ hv (hb M)) (ha N)⟩ :
        dirSpan ν (fun _ ↦ (1 : ℝ)) S) =
        ⟨v + a N + b M, Submodule.add_mem _ (Submodule.add_mem _ hv (ha N)) (hb M)⟩ :=
      Subtype.ext (add_right_comm _ _ _)
    rwa [e] at h
  have hdNn : fisherDist S ν ⟨v + a N, Submodule.add_mem _ hv (ha N)⟩
      ⟨v + a n, Submodule.add_mem _ hv (ha n)⟩ < δ := hN₁ N hN₁N n (hN₁N.trans hnN)
  obtain ⟨p, hp⟩ := exists_fisherPath_length_lt (x := (⟨v + a N, Submodule.add_mem _ hv (ha N)⟩ :
    dirSpan ν (fun _ ↦ (1 : ℝ)) S)) (y := ⟨v + a n, Submodule.add_mem _ hv (ha n)⟩) hδ0
  have hlen : p.length < 2 * δ := by linarith
  have hxA : 3 / 4 ≤ (Pfam (v + a N)).real A := hN₃ N hN₃N
  have d2 : fisherDist S ν
      ⟨v + a N + b M, Submodule.add_mem _ (Submodule.add_mem _ hv (ha N)) (hb M)⟩
      ⟨v + a n + b M, Submodule.add_mem _ (Submodule.add_mem _ hv (ha n)) (hb M)⟩ ≤
      2 * p.length :=
    fisherDist_add_le_two_mul_length hS ν p hA hxA (by linarith) (hb M) (hcb M) (hgeb M)
  -- assemble
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  change fisherDist S ν ⟨v + a n, Submodule.add_mem _ hv (ha n)⟩
    ⟨v + b n, Submodule.add_mem _ hv (hb n)⟩ < ε
  have t1 := fisherDist_triangle hS ν ⟨v + a n, Submodule.add_mem _ hv (ha n)⟩
    ⟨v + b M, Submodule.add_mem _ hv (hb M)⟩ ⟨v + b n, Submodule.add_mem _ hv (hb n)⟩
  have t2 := fisherDist_triangle hS ν ⟨v + a n, Submodule.add_mem _ hv (ha n)⟩
    ⟨v + a n + b M, Submodule.add_mem _ (Submodule.add_mem _ hv (ha n)) (hb M)⟩
    ⟨v + b M, Submodule.add_mem _ hv (hb M)⟩
  have t3 := fisherDist_triangle hS ν
    ⟨v + a n + b M, Submodule.add_mem _ (Submodule.add_mem _ hv (ha n)) (hb M)⟩
    ⟨v + a N + b M, Submodule.add_mem _ (Submodule.add_mem _ hv (ha N)) (hb M)⟩
    ⟨v + b M, Submodule.add_mem _ hv (hb M)⟩
  rw [fisherDist_comm hS ν] at d2
  linarith

/-- **Coalescence of completion limits**: the two sequences have the same limit in the
Fisher completion. -/
theorem completion_limit_eq_of_normalCone (v : J → ℝ) (hv : v ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    {a b : ℕ → J → ℝ} (ha : ∀ n, a n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (hb : ∀ n, b n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {A : Set X} (hA : MeasurableSet A)
    {ca cb Ba Bb : ℕ → ℝ} (hca : ∀ n, ∀ x ∈ A, dirLoss S (a n) x = ca n)
    (hgea : ∀ n, ∀ᵐ x ∂ν, ca n ≤ dirLoss S (a n) x)
    (hBa : ∀ n x, |dirLoss S (a n) x - ca n| ≤ Ba n)
    (hcb : ∀ n, ∀ x ∈ A, dirLoss S (b n) x = cb n)
    (hgeb : ∀ n, ∀ᵐ x ∂ν, cb n ≤ dirLoss S (b n) x)
    (hBb : ∀ n x, |dirLoss S (b n) x - cb n| ≤ Bb n)
    (hθA : Tendsto (fun n ↦ (Pfam (v + a n)).real A) atTop (𝓝 1))
    (hηA : Tendsto (fun n ↦ (Pfam (v + b n)).real A) atTop (𝓝 1)) {x y : FisherCompletion hS ν}
    (hx : Tendsto (fun n ↦ ((⟨⟨v + a n, Submodule.add_mem _ hv (ha n)⟩⟩ : FisherPoint hS ν) :
      FisherCompletion hS ν)) atTop (𝓝 x))
    (hy : Tendsto (fun n ↦ ((⟨⟨v + b n, Submodule.add_mem _ hv (hb n)⟩⟩ : FisherPoint hS ν) :
      FisherCompletion hS ν)) atTop (𝓝 y)) : x = y := by
  have hθ := cauchySeq_of_tendsto_completion hS ν hx
  have hη := cauchySeq_of_tendsto_completion hS ν hy
  have h := tendsto_dist_normalCone hS ν v hv ha hb hA hca hgea hBa hcb hgeb hBb hθ hη hθA hηA
  have h2 := hx.dist hy
  simp only [UniformSpace.Completion.dist_eq] at h2
  exact dist_eq_zero.1 (tendsto_nhds_unique h2 h)

end Coalescence

end Laplace.Multi
