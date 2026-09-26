/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ReconstructionBias

/-!
# The plug-in bias schema

The reconstruction-bias argument depends on the reconstructed response only through a uniform
second-order expansion around the data response and continuity on a compact convex interior
neighbourhood. We isolate this **schema**: for any functional `Φ` of the response with such an
expansion `Φ(M + z) = Φ(M) + L z + ½ b(z, z) + O(ε‖z‖²)`, the truncated plug-in
`Φ̃_n = Φ(M̂_n)` on `{M̂_n ∈ C}` (fallback `Φ(M)`) satisfies
`n (E Φ̃_n − Φ(M)) → ½ Σ_{a,b} Γ_{ab} b(e_a, e_b)` (`plugInGen_bias_tendsto_of_nhd`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory

namespace Laplace.Multi

/-- **The truncated plug-in of a functional** `Φ`: `Φ(M')` on `C`, the fallback `Φ(M)` outside. -/
noncomputable def plugInGen {J : Type*} (Φ : (J → ℝ) → ℝ) (C : Set (J → ℝ))
    [DecidablePred (· ∈ C)] (M M' : J → ℝ) : ℝ :=
  C.piecewise Φ (fun _ ↦ Φ M) M'

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X)
  [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hind : iIndepFun Xs P) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hXm hind hid hlaw

/-- **The core estimate of the plug-in bias schema** at a fixed sample size. -/
theorem plugInGen_bias_core [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {Φ : (J → ℝ) → ℝ} {L : (J → ℝ) →ₗ[ℝ] ℝ} {b : (J → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ}
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B) {C : Set (J → ℝ)} [DecidablePred (· ∈ C)]
    (hC : IsCompact C) (hΦc : ContinuousOn Φ C) {BΦ : ℝ} (hBΦ : ∀ M' ∈ C, |Φ M'| ≤ BΦ)
    {r : ℝ} (hr : 0 < r)
    (hCnhd : ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - dataMoment D S‖ ≤ r → M' ∈ C)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hpe : ∀ z : 𝕍, dataMoment D S + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |Φ (dataMoment D S + z) - Φ (dataMoment D S) - L (z : J → ℝ) -
        (1 / 2) * b (z : J → ℝ) (z : J → ℝ)| ≤ ε * ‖z‖ ^ 2)
    {n : ℕ} (hn : 0 < n) :
    |(n : ℝ) * ((∫ ω, plugInGen Φ C (dataMoment D S) (sampleResponse S Xs n ω) ∂P) -
        Φ (dataMoment D S)) -
      (1 / 2) * ∑ a, ∑ c, (∫ x, (S a x - dataMoment D S a) * (S c x - dataMoment D S c) ∂D) *
        b (coordUnit a) (coordUnit c)| ≤
      ε * ∑ a, (∫ x, (S a x - dataMoment D S a) ^ 2 ∂D) +
        (n : ℝ) * (2 * BΦ + 2 * B * (∑ a, |L (coordUnit a)|) +
          (1 / 2) * (4 * B ^ 2 * ∑ a, ∑ c, |b (coordUnit a) (coordUnit c)|)) *
        P.real {ω | min r δ < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} := by
  classical
  have hMmb : dataMoment D S ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := intrinsicInterior_subset hrel
  have hMC : dataMoment D S ∈ C := hCnhd _ hMmb (by simp [hr.le])
  have hBΦ0 : 0 ≤ BΦ := (abs_nonneg _).trans (hBΦ _ hMC)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨M, hM⟩ : ∃ M : J → ℝ, M = dataMoment D S := ⟨_, rfl⟩
  rw [← hM] at hpe hrel hMmb hMC hCnhd ⊢
  obtain ⟨h, hh⟩ : ∃ h : Ω → J → ℝ, h = fun ω ↦ sampleResponse S Xs n ω - M := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : J → J → ℝ,
    ∀ a c, Γ a c = ∫ x, (S a x - M a) * (S c x - M c) ∂D := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * BΦ + 2 * B * (∑ a, |L (coordUnit a)|) +
    (1 / 2) * (4 * B ^ 2 * ∑ a, ∑ c, |b (coordUnit a) (coordUnit c)|) := ⟨_, rfl⟩
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min r δ := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := hδ' ▸ lt_min hr hδ
  rw [← hK, ← hδ']
  simp only [← hΓ]
  have hset : {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} =
      {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - M j‖} := by rw [hM]; rfl
  rw [hset]
  -- coordinate bounds
  have hMabs : ∀ j, |M j| ≤ B := fun j ↦ by
    rw [hM]
    have := norm_integral_le_of_norm_le_const (μ := D) (f := S j) (C := B)
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB j x)
    rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this
  have hhabs : ∀ ω a, |h ω a| ≤ 2 * B := fun ω a ↦ by
    rw [hh]
    simp only [Pi.sub_apply]
    have h1 := abs_le.mp (abs_sampleResponse_le Xs hB hn ω a)
    have h2 := abs_le.mp (hMabs a)
    rw [abs_le]
    constructor <;> linarith
  have hhn : ∀ ω, ‖h ω‖ ≤ 2 * B := fun ω ↦
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a ↦ by
      rw [Real.norm_eq_abs]; exact hhabs ω a
  -- measurability and integrability
  have hmeasR : Measurable fun ω ↦ sampleResponse S Xs n ω :=
    measurable_sampleResponse hS Xs hXm n
  have hmeash : ∀ a, Measurable fun ω ↦ h ω a := fun a ↦ by
    rw [hh]; exact ((measurable_pi_apply a).comp hmeasR).sub measurable_const
  have hmeashv : Measurable h := measurable_pi_iff.2 hmeash
  have hintR : ∀ a, Integrable (fun ω ↦ sampleResponse S Xs n ω a) P := fun a ↦
    Integrable.of_bound ((measurable_pi_apply a).comp hmeasR).aestronglyMeasurable B
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]; exact abs_sampleResponse_le Xs hB hn ω a)
  have hinth : ∀ a, Integrable (fun ω ↦ h ω a) P := fun a ↦
    Integrable.of_bound (hmeash a).aestronglyMeasurable (2 * B)
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hhabs ω a)
  have hinthh : ∀ a c, Integrable (fun ω ↦ h ω a * h ω c) P := fun a c ↦
    Integrable.of_bound ((hmeash a).mul (hmeash c)).aestronglyMeasurable (2 * B * (2 * B))
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hhabs ω a) (hhabs ω c) (abs_nonneg _) (by positivity))
  -- first and second moments
  have hmean : ∀ a, ∫ ω, h ω a ∂P = 0 := fun a ↦ by
    rw [hh]
    simp only [Pi.sub_apply]
    rw [integral_sub (hintR a) (integrable_const _), integral_const,
      probReal_univ, one_smul, hM]
    exact sub_eq_zero.2 (integral_sampleResponse hS P D Xs hXm hid hlaw hn a)
  have hsec : ∀ a c, ∫ ω, h ω a * h ω c ∂P = Γ a c / n := fun a c ↦ by
    rw [hh, hΓ a c, hM]
    simp only [Pi.sub_apply]
    exact integral_sampleResponse_sub_mul_sub hS P D Xs hXm hid hlaw
      (fun i k hik ↦ hind.indepFun hik) hn a c
  have hintL : ∫ ω, L (h ω) ∂P = 0 := by
    rw [show (fun ω ↦ L (h ω)) = fun ω ↦ ∑ a, h ω a * L (coordUnit a) from
      funext fun ω ↦ linearMap_eq_sum_coordUnit L (h ω)]
    rw [integral_finsetSum _ fun a _ ↦ (hinth a).mul_const _]
    simp only [integral_mul_const, hmean, zero_mul, Finset.sum_const_zero]
  have hbsum : ∀ u : J → ℝ, b u u = ∑ a, ∑ c, u a * u c * b (coordUnit a) (coordUnit c) := by
    intro u
    rw [linearMap_eq_sum_coordUnit (b u) u, LinearMap.pi_apply_eq_sum_univ b u]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    change u c * (u a * b (coordUnit a) (coordUnit c)) = _
    ring
  have hintb : ∫ ω, b (h ω) (h ω) ∂P = ∑ a, ∑ c, Γ a c / n * b (coordUnit a) (coordUnit c) := by
    have e : (fun ω ↦ b (h ω) (h ω)) =
        fun ω ↦ ∑ a, ∑ c, h ω a * h ω c * b (coordUnit a) (coordUnit c) := funext fun ω ↦ hbsum _
    rw [e]
    rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun c _ ↦ (hinthh a c).mul_const _]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [integral_finsetSum _ fun c _ ↦ (hinthh a c).mul_const _]
    simp only [integral_mul_const, hsec]
  have hintsq' : Integrable (fun ω ↦ ‖h ω‖ ^ 2) P :=
    Integrable.of_bound ((hmeashv.norm).pow_const 2).aestronglyMeasurable ((2 * B) ^ 2)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hhn ω) 2)
  have hintsq : ∫ ω, ‖h ω‖ ^ 2 ∂P ≤ (∑ a, ∫ x, (S a x - M a) ^ 2 ∂D) / n := by
    have hint1 : Integrable (fun ω ↦ ∑ a, h ω a ^ 2) P :=
      integrable_finsetSum _ fun a _ ↦ by simpa [sq] using hinthh a a
    calc ∫ ω, ‖h ω‖ ^ 2 ∂P ≤ ∫ ω, ∑ a, h ω a ^ 2 ∂P :=
        integral_mono hintsq' hint1 fun ω ↦ norm_sq_le_sum_sq _
      _ = ∑ a, Γ a a / n := by
        rw [integral_finsetSum _ fun a _ ↦ by simpa [sq] using hinthh a a]
        exact Finset.sum_congr rfl fun a _ ↦ by rw [← hsec a a]; simp only [sq]
      _ = (∑ a, ∫ x, (S a x - M a) ^ 2 ∂D) / n := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun a _ ↦ by simp only [hΓ, sq]
  -- bounds on the linear and quadratic terms
  have hLbd : ∀ v : J → ℝ, (∀ a, |v a| ≤ 2 * B) → |L v| ≤ 2 * B * ∑ a, |L (coordUnit a)| := by
    intro v hv
    rw [linearMap_eq_sum_coordUnit L v, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hv a) (abs_nonneg _)
  have hbbd : ∀ v : J → ℝ, (∀ a, |v a| ≤ 2 * B) →
      |b v v| ≤ 4 * B ^ 2 * ∑ a, ∑ c, |b (coordUnit a) (coordUnit c)| := by
    intro v hv
    rw [hbsum v, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
    rw [abs_mul, abs_mul]
    have : |v a| * |v c| ≤ 4 * B ^ 2 := by
      calc |v a| * |v c| ≤ 2 * B * (2 * B) :=
          mul_le_mul (hv a) (hv c) (abs_nonneg _) (by positivity)
        _ = 4 * B ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  -- the pointwise bound on the moment body
  have hpt : ∀ ω, sampleResponse S Xs n ω ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S →
      |plugInGen Φ C M (sampleResponse S Xs n ω) - Φ M -
        (L (h ω) + (1 / 2) * b (h ω) (h ω))| ≤
        ε * ‖h ω‖ ^ 2 + K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω := by
    intro ω hω
    have hhω : h ω = sampleResponse S Xs n ω - M := by rw [hh]
    by_cases hsmall : ‖h ω‖ ≤ δ'
    · have hinC : sampleResponse S Xs n ω ∈ C :=
        hCnhd _ hω (by rw [← hhω]; exact hsmall.trans (hδ' ▸ min_le_left r δ))
      have hmem : sampleResponse S Xs n ω - M ∈ 𝕍 := sub_mem_dirSpan_of_mem_momentBody' hS ν hMmb hω
      have hz := hpe ⟨_, hmem⟩ (by simpa using hinC) (by
        change ‖sampleResponse S Xs n ω - M‖ ≤ δ
        rw [← hhω]; exact hsmall.trans (hδ' ▸ min_le_right r δ))
      have hnorm : ‖(⟨sampleResponse S Xs n ω - M, hmem⟩ : 𝕍)‖ = ‖sampleResponse S Xs n ω - M‖ :=
        rfl
      simp only [add_sub_cancel, hnorm] at hz
      rw [Set.indicator_of_notMem (by simpa using hsmall), mul_zero, add_zero]
      unfold plugInGen
      rw [Set.piecewise_eq_of_mem _ _ _ hinC, hhω]
      have e : Φ (sampleResponse S Xs n ω) - Φ M - (L (sampleResponse S Xs n ω - M) +
          1 / 2 * b (sampleResponse S Xs n ω - M) (sampleResponse S Xs n ω - M)) =
          Φ (sampleResponse S Xs n ω) - Φ M - L (sampleResponse S Xs n ω - M) -
          1 / 2 * b (sampleResponse S Xs n ω - M) (sampleResponse S Xs n ω - M) := by ring
      rw [e]
      exact hz
    · rw [Set.indicator_of_mem (show ω ∈ {ω | δ' < ‖h ω‖} from not_le.mp hsmall), Pi.one_apply,
        mul_one]
      have hplug : |plugInGen Φ C M (sampleResponse S Xs n ω) - Φ M| ≤ 2 * BΦ := by
        unfold plugInGen
        by_cases hc : sampleResponse S Xs n ω ∈ C
        · rw [Set.piecewise_eq_of_mem _ _ _ hc]
          linarith [abs_sub (Φ (sampleResponse S Xs n ω)) (Φ M), hBΦ _ hc, hBΦ _ hMC]
        · rw [Set.piecewise_eq_of_notMem _ _ _ hc, sub_self, abs_zero]
          linarith [hBΦ _ hMC]
      have hL' := hLbd (h ω) (hhabs ω)
      have hb' := hbbd (h ω) (hhabs ω)
      have hnn : 0 ≤ ε * ‖h ω‖ ^ 2 := by positivity
      calc |plugInGen Φ C M (sampleResponse S Xs n ω) - Φ M -
            (L (h ω) + 1 / 2 * b (h ω) (h ω))|
          ≤ |plugInGen Φ C M (sampleResponse S Xs n ω) - Φ M| +
            (|L (h ω)| + 1 / 2 * |b (h ω) (h ω)|) := by
            refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
            refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        _ ≤ K := by rw [hK]; linarith
        _ ≤ ε * ‖h ω‖ ^ 2 + K := by linarith
  -- integrate the pointwise bound
  have hae : ∀ᵐ ω ∂P, ‖plugInGen Φ C M (sampleResponse S Xs n ω) - Φ M -
      (L (h ω) + (1 / 2) * b (h ω) (h ω))‖ ≤
      ε * ‖h ω‖ ^ 2 + K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω := by
    filter_upwards [ae_sampleResponse_mem_momentBody hS ν P D hDν Xs hXm hid hlaw] with ω hω
    rw [Real.norm_eq_abs]
    exact hpt ω (hω n hn)
  have hmeasS : MeasurableSet {ω | δ' < ‖h ω‖} := measurableSet_lt measurable_const hmeashv.norm
  have hI0 : Integrable (fun ω ↦ ε * ‖h ω‖ ^ 2) P := hintsq'.const_mul _
  have hI1 : Integrable (fun ω ↦ K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hmeasS).const_mul _
  have hintbd : Integrable (fun ω ↦ ε * ‖h ω‖ ^ 2 +
      K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω) P := hI0.add hI1
  have hintplug : Integrable (fun ω ↦ plugInGen Φ C M (sampleResponse S Xs n ω)) P := by
    have hm : Measurable fun ω ↦ plugInGen Φ C M (sampleResponse S Xs n ω) :=
      (ContinuousOn.measurable_piecewise hΦc continuousOn_const
        hC.isClosed.measurableSet).comp hmeasR
    refine Integrable.of_bound hm.aestronglyMeasurable BΦ (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    unfold plugInGen
    by_cases hc : sampleResponse S Xs n ω ∈ C
    · rw [Set.piecewise_eq_of_mem _ _ _ hc]; exact hBΦ _ hc
    · rw [Set.piecewise_eq_of_notMem _ _ _ hc]; exact hBΦ _ hMC
  have hintL' : Integrable (fun ω ↦ L (h ω)) P := by
    rw [show (fun ω ↦ L (h ω)) = fun ω ↦ ∑ a, h ω a * L (coordUnit a) from
      funext fun ω ↦ linearMap_eq_sum_coordUnit L (h ω)]
    exact integrable_finsetSum _ fun a _ ↦ (hinth a).mul_const _
  have hintb' : Integrable (fun ω ↦ b (h ω) (h ω)) P := by
    rw [show (fun ω ↦ b (h ω) (h ω)) =
        fun ω ↦ ∑ a, ∑ c, h ω a * h ω c * b (coordUnit a) (coordUnit c) from
      funext fun ω ↦ hbsum _]
    exact integrable_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun c _ ↦
      (hinthh a c).mul_const _
  have hΨ : Integrable (fun ω ↦ L (h ω) + (1 / 2) * b (h ω) (h ω)) P :=
    hintL'.add (hintb'.const_mul _)
  have hΦ : Integrable (fun ω ↦ plugInGen Φ C M (sampleResponse S Xs n ω) - Φ M) P :=
    hintplug.sub (integrable_const _)
  have hkey := norm_integral_le_of_norm_le hintbd hae
  rw [integral_sub hΦ hΨ, integral_sub hintplug (integrable_const _), integral_const,
    probReal_univ, one_smul, integral_add hintL' (hintb'.const_mul _), hintL,
    integral_const_mul, hintb, zero_add, integral_add hI0 hI1, integral_const_mul,
    integral_const_mul, integral_indicator_one hmeasS, Real.norm_eq_abs] at hkey
  have hκ : (1 / 2) * ∑ a, ∑ c, Γ a c * b (coordUnit a) (coordUnit c) =
      (n : ℝ) * ((1 / 2) * ∑ a, ∑ c, Γ a c / n * b (coordUnit a) (coordUnit c)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    field_simp
  rw [hκ, ← mul_sub, abs_mul, abs_of_pos hn']
  have hset' : {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - M j‖} = {ω | δ' < ‖h ω‖} := by
    rw [hh]; rfl
  rw [hset']
  calc (n : ℝ) * |(∫ ω, plugInGen Φ C M (sampleResponse S Xs n ω) ∂P - Φ M) -
        (1 / 2 * ∑ a, ∑ c, Γ a c / n * b (coordUnit a) (coordUnit c))|
      ≤ (n : ℝ) * (ε * ∫ ω, ‖h ω‖ ^ 2 ∂P + K * P.real {ω | δ' < ‖h ω‖}) :=
        mul_le_mul_of_nonneg_left hkey hn'.le
    _ ≤ (n : ℝ) * (ε * ((∑ a, ∫ x, (S a x - M a) ^ 2 ∂D) / n) +
          K * P.real {ω | δ' < ‖h ω‖}) := by
        gcongr
    _ = ε * ∑ a, (∫ x, (S a x - M a) ^ 2 ∂D) + (n : ℝ) * K * P.real {ω | δ' < ‖h ω‖} := by
        field_simp

/-- **The plug-in bias schema**: a functional `Φ` of the response with a uniform second-order
expansion `Φ(M + z) = Φ(M) + L z + ½ b(z,z) + o(‖z‖²)` at the data response, continuous on a
compact convex interior neighbourhood `C`, has truncated plug-in bias
`n (E Φ̃_n − Φ(M)) → ½ Σ_{a,b} Γ_{ab} b(e_a, e_b)`. -/
theorem plugInGen_bias_tendsto_of_nhd [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {Φ : (J → ℝ) → ℝ} {L : (J → ℝ) →ₗ[ℝ] ℝ} {b : (J → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ}
    {C : Set (J → ℝ)} [DecidablePred (· ∈ C)] (hC : IsCompact C)
    (hΦc : ContinuousOn Φ C) {r : ℝ} (hr : 0 < r)
    (hCnhd : ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - dataMoment D S‖ ≤ r → M' ∈ C)
    (hpe : ∀ ε > 0, ∃ δ > 0, ∀ z : 𝕍, dataMoment D S + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |Φ (dataMoment D S + z) - Φ (dataMoment D S) - L (z : J → ℝ) -
        (1 / 2) * b (z : J → ℝ) (z : J → ℝ)| ≤ ε * ‖z‖ ^ 2) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
        ((∫ ω, plugInGen Φ C (dataMoment D S) (sampleResponse S Xs n ω) ∂P) -
          Φ (dataMoment D S))) atTop
      (𝓝 ((1 / 2) * ∑ a, ∑ c,
        (∫ x, (S a x - dataMoment D S a) * (S c x - dataMoment D S c) ∂D) *
          b (coordUnit a) (coordUnit c))) := by
  have hMmb := intrinsicInterior_subset hrel
  have hMC : dataMoment D S ∈ C := hCnhd _ hMmb (by simp [hr.le])
  have hB' : ∀ j, ∃ M, ∀ x, |S j x| ≤ M := fun j ↦ (hS j).2
  choose Bj hBj using hB'
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ j, |Bj j| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hBdef ▸ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hB : ∀ j x, |S j x| ≤ B := fun j x ↦
    (hBj j x).trans ((le_abs_self _).trans (hBdef ▸ Finset.single_le_sum (f := fun j ↦ |Bj j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)))
  obtain ⟨BΦ, hBΦ⟩ := hC.exists_bound_of_continuousOn hΦc
  have hBΦ' : ∀ M' ∈ C, |Φ M'| ≤ BΦ := fun M' hM' ↦ by
    rw [← Real.norm_eq_abs]; exact hBΦ M' hM'
  have hBΦ0 : 0 ≤ BΦ := (abs_nonneg _).trans (hBΦ' _ hMC)
  obtain ⟨c, hc, htail⟩ := exists_tail_sampleResponse hS P D Xs hXm hid hlaw hind
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ a, ∫ x, (S a x - dataMoment D S a) ^ 2 ∂D := ⟨_, rfl⟩
  obtain ⟨KK, hKK⟩ : ∃ KK : ℝ, KK = 2 * BΦ + 2 * B * (∑ a, |L (coordUnit a)|) +
      (1 / 2) * (4 * B ^ 2 * ∑ a, ∑ c, |b (coordUnit a) (coordUnit c)|) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hT ▸ Finset.sum_nonneg fun a _ ↦ integral_nonneg fun x ↦ sq_nonneg _
  have hKK0 : 0 ≤ KK := by
    rw [hKK]
    have h1 : 0 ≤ ∑ a, |L (coordUnit a)| := Finset.sum_nonneg fun a _ ↦ abs_nonneg _
    have h2 : 0 ≤ ∑ a, ∑ c, |b (coordUnit a) (coordUnit c)| :=
      Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun c _ ↦ abs_nonneg _
    positivity
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = η / (2 * (T + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ by positivity
  obtain ⟨δ, hδ, hpeδ⟩ := hpe ε hε0
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min r δ := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := hδ' ▸ lt_min hr hδ
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) *
      (KK * (2 * Fintype.card J * Real.exp (-(c * n * δ' ^ 2))))) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (c * δ' ^ 2)
      (by positivity)).comp tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul (KK * (2 * Fintype.card J))
    rw [mul_zero] at h2
    refine h2.congr' (Eventually.of_forall fun n ↦ ?_)
    simp only [Function.comp_def, Real.rpow_one]
    rw [show -(c * n * δ' ^ 2) = -(c * δ' ^ 2) * n by ring]
    ring
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (η / 2) (by positivity)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hcore := plugInGen_bias_core hS ν P D Xs hXm hind hid hlaw hDν hrel hB0 hB hC hΦc hBΦ'
    hr hCnhd hε0.le hδ hpeδ hn1
  rw [← hT, ← hKK, ← hδ'] at hcore
  have htail' := htail n hn1 δ' hδ'0
  have hN' := hN n hnN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hN'
  have hεT : ε * T ≤ η / 2 := by
    rw [hε, show η / (2 * (T + 1)) * T = η / 2 * (T / (T + 1)) by field_simp]
    exact mul_le_of_le_one_right (by positivity)
      (div_le_one_of_le₀ (by linarith) (by positivity))
  rw [Real.dist_eq]
  calc _ ≤ ε * T + (n : ℝ) * KK *
        P.real {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} := hcore
    _ ≤ ε * T + (n : ℝ) * KK * (2 * Fintype.card J * Real.exp (-(c * n * δ' ^ 2))) := by
        gcongr
    _ < η := by nlinarith

end Assembly

end Laplace.Multi
