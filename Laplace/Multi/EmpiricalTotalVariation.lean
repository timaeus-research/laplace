/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ReconstructionLipschitz
import Laplace.Multi.EmpiricalProjection
import Laplace.Multi.FibreHessian

/-!
# Total-variation consistency of the empirical reconstruction

For i.i.d. samples from a data law `D` whose response `M_D` is interior, the strong law gives
`M̂_n → M_D` almost surely; the compact-uniform total-variation Lipschitz bound on a compact convex
neighbourhood of `M_D` (`exists_compact_convex_nhd`) then gives

`∫ |q_{M̂_n} − q_{M_D}| dν → 0` almost surely (`ae_tendsto_integral_abs_famDens_sampleResponse`),

and hence `E_{Π(M̂_n)} φ → E_{Π(M_D)} φ` almost surely for every bounded observable
(`ae_tendsto_integral_responseProjection_sampleResponse`): the reconstruction of the empirical
response converges in total variation to the reconstruction of the data.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **Every interior response has a compact convex interior neighbourhood** containing every
response of the moment body within distance `r`. -/
theorem exists_compact_convex_nhd {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∃ r > 0, ∃ C : Set (J → ℝ), IsCompact C ∧ Convex ℝ C ∧
      C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) ∧
      ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - M‖ ≤ r → M' ∈ C := by
  obtain ⟨r₀, hr₀, hball⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_add_mem_intrinsicInterior hS ν hrel)
  refine ⟨r₀ / 2, by positivity, (fun z : 𝕍 ↦ M + (z : J → ℝ)) '' Metric.closedBall 0 (r₀ / 2),
    (isCompact_closedBall (0 : 𝕍) (r₀ / 2)).image (continuous_const.add continuous_subtype_val),
    ?_, ?_, ?_⟩
  · rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩ a b ha hb hab
    refine ⟨a • z₁ + b • z₂, convex_closedBall (0 : 𝕍) (r₀ / 2) hz₁ hz₂ ha hb hab, ?_⟩
    simp only [Submodule.coe_add, Submodule.coe_smul]
    calc M + (a • (z₁ : J → ℝ) + b • (z₂ : J → ℝ))
        = (a + b) • M + (a • (z₁ : J → ℝ) + b • (z₂ : J → ℝ)) := by rw [hab, one_smul]
      _ = a • (M + (z₁ : J → ℝ)) + b • (M + (z₂ : J → ℝ)) := by module
  · rintro _ ⟨z, hz, rfl⟩
    refine hball ?_
    rw [dist_zero_right]
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    linarith
  · intro M' hM' hMM
    have hmem : M' - M ∈ 𝕍 := by
      have h1 := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (one_integral_pos ν) hS hM'
      have h2 := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (one_integral_pos ν) hS (intrinsicInterior_subset hrel)
      have e : M' - M = (M' - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) -
          (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by abel
      rw [e]
      exact Submodule.sub_mem _ h1 h2
    refine ⟨⟨M' - M, hmem⟩, ?_, by simp⟩
    rw [Metric.mem_closedBall, dist_zero_right, ← Submodule.norm_coe]
    exact hMM

/-- **Total-variation consistency of the empirical reconstruction**: for i.i.d. samples from a data
law with interior response, `∫ |q_{M̂_n} − q_{M_D}| dν → 0` almost surely. -/
theorem ae_tendsto_integral_abs_famDens_sampleResponse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X) (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
    (hXm : ∀ i, Measurable (Xs i)) (hind : Pairwise fun i k ↦ IndepFun (Xs i) (Xs k) P)
    (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
    (hrel : (fun j ↦ ∫ x, S j x ∂D) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ ∫ x, |famDens S ν (θr (sampleResponse S Xs n ω)) x -
      famDens S ν (θr fun j ↦ ∫ x, S j x ∂D) x| ∂ν) atTop (𝓝 0) := by
  obtain ⟨MD, hMD⟩ : ∃ MD : J → ℝ, MD = fun j ↦ ∫ x, S j x ∂D := ⟨_, rfl⟩
  rw [← hMD] at hrel ⊢
  have hlim0 := ae_tendsto_sampleResponse hS P D Xs hXm hind hid hlaw
  rw [← hMD] at hlim0
  obtain ⟨r, hr, C, hC, hCc, hCK, hCr⟩ := exists_compact_convex_nhd hS ν hrel
  obtain ⟨L, hL0, hL⟩ := exists_tv_lipschitz_of_isCompact_convex hS ν hC hCc hCK
  have hMC : MD ∈ C := hCr MD (intrinsicInterior_subset hrel) (by simp [hr.le])
  filter_upwards [hlim0, ae_sampleResponse_mem_momentBody hS ν P D hDν Xs hXm hid hlaw] with ω hlim
    hmem
  rw [← tendsto_add_atTop_iff_nat 1]
  have hlim' : Tendsto (fun n ↦ sampleResponse S Xs (n + 1) ω) atTop (𝓝 MD) :=
    (tendsto_add_atTop_iff_nat 1).2 hlim
  have hup : Tendsto (fun n ↦ L * ‖sampleResponse S Xs (n + 1) ω - MD‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hlim').const_mul L
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n ↦ integral_nonneg fun x ↦ abs_nonneg _) ?_
  filter_upwards [hlim'.eventually (Metric.closedBall_mem_nhds MD hr)] with n hn
  rw [dist_eq_norm] at hn
  exact hL MD hMC _ (hCr _ (hmem (n + 1) n.succ_pos) hn)

/-- **Consistency of the reconstructed responses**: for i.i.d. samples from a data law with interior
response and every bounded observable, `E_{Π(M̂_n)} φ → E_{Π(M_D)} φ` almost surely. -/
theorem ae_tendsto_integral_responseProjection_sampleResponse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X) (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
    (hXm : ∀ i, Measurable (Xs i)) (hind : Pairwise fun i k ↦ IndepFun (Xs i) (Xs k) P)
    (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
    (hrel : (fun j ↦ ∫ x, S j x ∂D) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {φ : X → ℝ} (hφ : Bdd φ) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ ∫ x, φ x ∂responseProjection hS ν (sampleResponse S Xs n ω))
      atTop (𝓝 (∫ x, φ x ∂responseProjection hS ν fun j ↦ ∫ x, S j x ∂D)) := by
  obtain ⟨MD, hMD⟩ : ∃ MD : J → ℝ, MD = fun j ↦ ∫ x, S j x ∂D := ⟨_, rfl⟩
  rw [← hMD] at hrel ⊢
  obtain ⟨hφm, Bφ, hBφ⟩ := hφ
  have hBφ0 : 0 ≤ Bφ := (abs_nonneg _).trans (hBφ (Classical.arbitrary X))
  have hlim0 := ae_tendsto_sampleResponse hS P D Xs hXm hind hid hlaw
  rw [← hMD] at hlim0
  filter_upwards [hlim0, ae_sampleResponse_mem_momentBody hS ν P D hDν Xs hXm hid hlaw,
    ae_tendsto_integral_abs_famDens_sampleResponse hS ν P D hDν Xs hXm hind hid hlaw
      (hMD ▸ hrel)] with ω hlim hmem htv
  rw [← hMD] at htv
  have hev : ∀ᶠ n in atTop, sampleResponse S Xs n ω ∈
      intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    have h := eventually_mem_intrinsicInterior_of_tendsto
      (M := fun n ↦ sampleResponse S Xs (n + 1) ω) (fun n ↦ hmem (n + 1) n.succ_pos) hrel
      ((tendsto_add_atTop_iff_nat 1).2 hlim)
    obtain ⟨N, hN⟩ := eventually_atTop.1 h
    refine eventually_atTop.2 ⟨N + 1, fun n hn ↦ ?_⟩
    have := hN (n - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hup : Tendsto (fun n ↦ Bφ * ∫ x, |famDens S ν (θr (sampleResponse S Xs n ω)) x -
      famDens S ν (θr MD) x| ∂ν) atTop (𝓝 0) := by
    simpa using htv.const_mul Bφ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n ↦ norm_nonneg _) ?_
  filter_upwards [hev] with n hn
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hn,
    responseProjection_eq_familyMeasure_responseTheta hS ν hrel, integral_famDens_mul hS ν,
    integral_famDens_mul hS ν, Real.norm_eq_abs]
  have hI : ∀ N : J → ℝ, Integrable (fun x ↦ famDens S ν N x * φ x) ν := fun N ↦
    (integrable_famDens hS ν N).mul_bdd hφm.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact hBφ x)
  rw [← integral_sub (hI _) (hI _)]
  have hI2 : Integrable (fun x ↦ famDens S ν (θr (sampleResponse S Xs n ω)) x * φ x -
      famDens S ν (θr MD) x * φ x) ν := (hI _).sub (hI _)
  calc |∫ x, famDens S ν (θr (sampleResponse S Xs n ω)) x * φ x -
        famDens S ν (θr MD) x * φ x ∂ν|
      ≤ ∫ x, |famDens S ν (θr (sampleResponse S Xs n ω)) x * φ x -
          famDens S ν (θr MD) x * φ x| ∂ν := by
        have := norm_integral_le_integral_norm (μ := ν)
          (fun x ↦ famDens S ν (θr (sampleResponse S Xs n ω)) x * φ x -
            famDens S ν (θr MD) x * φ x)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ x, Bφ * |famDens S ν (θr (sampleResponse S Xs n ω)) x - famDens S ν (θr MD) x| ∂ν := by
        refine integral_mono hI2.abs (((integrable_famDens hS ν _).sub
          (integrable_famDens hS ν _)).abs.const_mul Bφ) fun x ↦ ?_
        rw [← sub_mul, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hBφ x) (abs_nonneg _)
    _ = Bφ * ∫ x, |famDens S ν (θr (sampleResponse S Xs n ω)) x - famDens S ν (θr MD) x| ∂ν :=
        integral_const_mul _ _

end Laplace.Multi
