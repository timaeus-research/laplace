/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ReconstructionBias
import Laplace.Multi.ResponseTransport

/-!
# The joint covariance of plug-in reconstructions

For two bounded observables `F, G` the truncated plug-in estimators `Ĝ_{F,n}, Ĝ_{G,n}` of the
reconstructed responses have

  `n Cov(Ĝ_{F,n}, Ĝ_{G,n}) → Σ_{a,b} Γ_{ab} lin_F(e_a) lin_G(e_b) = E_D[lin_F(S − M) lin_G(S − M)]`

(`plugIn_covariance_tendsto`, `plugIn_covariance_tendsto_integral`): the **sandwich covariance** of
the influence functions under the data law. In particular `n Var(Ĝ_{F,n}) → E_D[ψ_{F,M}²]`
(`plugIn_variance_tendsto`). The proof is the first-order uniform expansion, the exact second
moments `Γ/n` of the empirical response, and the Hoeffding tail on the exceptional set; the
reconstruction bias is `O(1/n)` and its product is negligible at scale `n`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory

namespace Laplace.Multi

section Bilinear

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- A linear functional on `J → ℝ` is bounded by its coordinate sum times the sup norm. -/
theorem abs_linearMap_le_norm (L : (J → ℝ) →ₗ[ℝ] ℝ) (u : J → ℝ) :
    |L u| ≤ (∑ a, |L (coordUnit a)|) * ‖u‖ := by
  rw [LinearMap.pi_apply_eq_sum_univ L u, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  rw [smul_eq_mul, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  exact norm_le_pi_norm u a

/-- A bilinear form on `J → ℝ` is bounded on the diagonal by its coordinate sum times the squared
sup norm. -/
theorem abs_bilinear_le_norm_sq (b : (J → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ) (u : J → ℝ) :
    |b u u| ≤ (∑ a, ∑ c, |b (coordUnit a) (coordUnit c)|) * ‖u‖ ^ 2 := by
  have e : b u u = ∑ a, ∑ c, u a * u c * b (coordUnit a) (coordUnit c) := by
    rw [LinearMap.pi_apply_eq_sum_univ b u]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [LinearMap.pi_apply_eq_sum_univ (b _) u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp only [smul_eq_mul]
    change u a * (u c * b (coordUnit a) (coordUnit c)) = _
    ring
  rw [e, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
  rw [abs_mul, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [sq]
  refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u a
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u c

/-- The product of two linear functionals expands in coordinates. -/
theorem linearMap_mul_linearMap_eq_sum (L L' : (J → ℝ) →ₗ[ℝ] ℝ) (u : J → ℝ) :
    L u * L' u = ∑ a, ∑ c, u a * u c * (L (coordUnit a) * L' (coordUnit c)) := by
  rw [LinearMap.pi_apply_eq_sum_univ L u, LinearMap.pi_apply_eq_sum_univ L' u,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [smul_eq_mul]
  change u a * L (coordUnit a) * (u c * L' (coordUnit c)) = _
  ring

end Bilinear

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

/-- **The first-order uniform expansion** at an interior response, with an explicit quadratic
constant: `|G_F(M + z) − G_F(M) − lin_{F,M}(z)| ≤ (B_F + ½ ‖b_F‖) ‖z‖²` for small visible `z`
staying in a compact convex interior set. -/
theorem exists_first_order_remainder [DecidableEq J] {C : Set (J → ℝ)} (hC : IsCompact C)
    (hCc : Convex ℝ C) (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {M : J → ℝ} (hM : M ∈ C) {F : X → ℝ} (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) :
    ∃ δ > 0, ∀ z : 𝕍, M + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |obsResponse hS ν F (M + z) - obsResponse hS ν F M - linForm hS ν M hF (z : J → ℝ)| ≤
        (BF + (1 / 2) * ∑ a, ∑ c, |biasForm hS ν M hF (coordUnit a) (coordUnit c)|) * ‖z‖ ^ 2 := by
  obtain ⟨δ, hδ, h⟩ := integral_response_peano_biasForm hS ν hC hCc hCK hF hBF 1 one_pos
  refine ⟨δ, hδ, fun z hz hzδ ↦ ?_⟩
  have h1 := h M hM z hz hzδ
  have h2 := abs_bilinear_le_norm_sq (biasForm hS ν M hF) (z : J → ℝ)
  have hnorm : ‖(z : J → ℝ)‖ = ‖z‖ := rfl
  rw [hnorm] at h2
  simp only [obsResponse, one_mul] at h1 ⊢
  have e : (∫ x, F x ∂(Pfam (θr (M + z)))) - (∫ x, F x ∂(Pfam (θr M))) -
      linForm hS ν M hF (z : J → ℝ) =
      ((∫ x, F x ∂(Pfam (θr (M + z)))) - (∫ x, F x ∂(Pfam (θr M))) -
        linForm hS ν M hF (z : J → ℝ) -
        (1 / 2) * biasForm hS ν M hF (z : J → ℝ) (z : J → ℝ)) +
        (1 / 2) * biasForm hS ν M hF (z : J → ℝ) (z : J → ℝ) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X)
  [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hind : iIndepFun Xs P) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hXm hind hid hlaw

omit hind hid hlaw in
/-- The plug-in estimator is integrable (bounded and measurable). -/
theorem integrable_plugIn_sampleResponse {C : Set (J → ℝ)} [DecidablePred (· ∈ C)]
    (hC : IsCompact C) (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {F : X → ℝ} (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) (M : J → ℝ) (n : ℕ) :
    Integrable (fun ω ↦ plugIn hS ν F C M (sampleResponse S Xs n ω)) P := by
  have hm : Measurable fun ω ↦ plugIn hS ν F C M (sampleResponse S Xs n ω) :=
    (ContinuousOn.measurable_piecewise (continuousOn_obsResponse hS ν hF hCK)
      continuousOn_const hC.isClosed.measurableSet).comp (measurable_sampleResponse hS Xs hXm n)
  refine Integrable.of_bound hm.aestronglyMeasurable BF (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs]
  unfold plugIn
  by_cases hc : sampleResponse S Xs n ω ∈ C
  · rw [Set.piecewise_eq_of_mem _ _ _ hc]; exact abs_obsResponse_le hS ν hBF _
  · rw [Set.piecewise_eq_of_notMem _ _ _ hc]; exact abs_obsResponse_le hS ν hBF _

/-- **The core estimate for the product of two plug-in deviations** at a fixed sample size. -/
theorem plugIn_product_core [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {F G : X → ℝ} (hF : Bdd F) (hG : Bdd G) {BF BG : ℝ} (hBF : ∀ x, |F x| ≤ BF)
    (hBG : ∀ x, |G x| ≤ BG) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B) {C : Set (J → ℝ)}
    [DecidablePred (· ∈ C)] (hC : IsCompact C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {r : ℝ} (hr : 0 < r)
    (hCnhd : ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - dataMoment D S‖ ≤ r → M' ∈ C)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {CF CG : ℝ} (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hpeF : ∀ z : 𝕍, dataMoment D S + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |obsResponse hS ν F (dataMoment D S + z) - obsResponse hS ν F (dataMoment D S) -
        linForm hS ν (dataMoment D S) hF (z : J → ℝ)| ≤ CF * ‖z‖ ^ 2)
    (hpeG : ∀ z : 𝕍, dataMoment D S + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |obsResponse hS ν G (dataMoment D S + z) - obsResponse hS ν G (dataMoment D S) -
        linForm hS ν (dataMoment D S) hG (z : J → ℝ)| ≤ CG * ‖z‖ ^ 2)
    {n : ℕ} (hn : 0 < n) :
    |(n : ℝ) * (∫ ω, (plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) -
          obsResponse hS ν F (dataMoment D S)) *
        (plugIn hS ν G C (dataMoment D S) (sampleResponse S Xs n ω) -
          obsResponse hS ν G (dataMoment D S)) ∂P) -
      ∑ a, ∑ b, (∫ x, (S a x - dataMoment D S a) * (S b x - dataMoment D S b) ∂D) *
        (linForm hS ν (dataMoment D S) hF (coordUnit a) *
          linForm hS ν (dataMoment D S) hG (coordUnit b))| ≤
      ((∑ a, |linForm hS ν (dataMoment D S) hF (coordUnit a)|) * CG +
          (∑ a, |linForm hS ν (dataMoment D S) hG (coordUnit a)|) * CF + CF * CG) * δ *
        ∑ a, (∫ x, (S a x - dataMoment D S a) ^ 2 ∂D) +
      (n : ℝ) * (2 * BF * (2 * BG) +
          2 * B * (∑ a, |linForm hS ν (dataMoment D S) hF (coordUnit a)|) *
            (2 * B * ∑ a, |linForm hS ν (dataMoment D S) hG (coordUnit a)|)) *
        P.real {ω | min r δ < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} := by
  classical
  have hMmb : dataMoment D S ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := intrinsicInterior_subset hrel
  have hMC : dataMoment D S ∈ C := hCnhd _ hMmb (by simp [hr.le])
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF (Classical.arbitrary X))
  have hBG0 : 0 ≤ BG := (abs_nonneg _).trans (hBG (Classical.arbitrary X))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- abbreviations
  obtain ⟨M, hM⟩ : ∃ M : J → ℝ, M = dataMoment D S := ⟨_, rfl⟩
  rw [← hM] at hpeF hpeG hrel hMmb hMC hCnhd ⊢
  obtain ⟨LF, hLF⟩ : ∃ LF : (J → ℝ) →ₗ[ℝ] ℝ, LF = linForm hS ν M hF := ⟨_, rfl⟩
  obtain ⟨LG, hLG⟩ : ∃ LG : (J → ℝ) →ₗ[ℝ] ℝ, LG = linForm hS ν M hG := ⟨_, rfl⟩
  obtain ⟨GF, hGF⟩ : ∃ GF : (J → ℝ) → ℝ, GF = obsResponse hS ν F := ⟨_, rfl⟩
  obtain ⟨GG, hGG⟩ : ∃ GG : (J → ℝ) → ℝ, GG = obsResponse hS ν G := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : Ω → J → ℝ, h = fun ω ↦ sampleResponse S Xs n ω - M := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : J → J → ℝ,
    ∀ a b, Γ a b = ∫ x, (S a x - M a) * (S b x - M b) ∂D := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨KF, hKF⟩ : ∃ KF : ℝ, KF = ∑ a, |LF (coordUnit a)| := ⟨_, rfl⟩
  obtain ⟨KG, hKG⟩ : ∃ KG : ℝ, KG = ∑ a, |LG (coordUnit a)| := ⟨_, rfl⟩
  obtain ⟨Cq, hCq⟩ : ∃ Cq : ℝ, Cq = KF * CG + KG * CF + CF * CG := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * BF * (2 * BG) + 2 * B * KF * (2 * B * KG) := ⟨_, rfl⟩
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min r δ := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := hδ' ▸ lt_min hr hδ0
  have hδ'δ : δ' ≤ δ := hδ' ▸ min_le_right r δ
  rw [← hLF, ← hLG, ← hGF, ← hGG, ← hKF, ← hKG, ← hCq, ← hK, ← hδ']
  simp only [← hΓ]
  rw [← hLF, ← hGF] at hpeF
  rw [← hLG, ← hGG] at hpeG
  have hset : {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} =
      {ω | δ' < ‖h ω‖} := by rw [hh, hM]; rfl
  rw [hset]
  have hKF0 : 0 ≤ KF := hKF ▸ Finset.sum_nonneg fun a _ ↦ abs_nonneg _
  have hKG0 : 0 ≤ KG := hKG ▸ Finset.sum_nonneg fun a _ ↦ abs_nonneg _
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
  have hLFh : ∀ ω, |LF (h ω)| ≤ KF * ‖h ω‖ := fun ω ↦ hKF ▸ abs_linearMap_le_norm LF (h ω)
  have hLGh : ∀ ω, |LG (h ω)| ≤ KG * ‖h ω‖ := fun ω ↦ hKG ▸ abs_linearMap_le_norm LG (h ω)
  -- measurability and integrability
  have hmeasR : Measurable fun ω ↦ sampleResponse S Xs n ω :=
    measurable_sampleResponse hS Xs hXm n
  have hmeash : ∀ a, Measurable fun ω ↦ h ω a := fun a ↦ by
    rw [hh]; exact ((measurable_pi_apply a).comp hmeasR).sub measurable_const
  have hmeashv : Measurable h := measurable_pi_iff.2 hmeash
  have hinthh : ∀ a b, Integrable (fun ω ↦ h ω a * h ω b) P := fun a b ↦
    Integrable.of_bound ((hmeash a).mul (hmeash b)).aestronglyMeasurable (2 * B * (2 * B))
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hhabs ω a) (hhabs ω b) (abs_nonneg _) (by positivity))
  have hsec : ∀ a b, ∫ ω, h ω a * h ω b ∂P = Γ a b / n := fun a b ↦ by
    rw [hh, hΓ a b, hM]
    simp only [Pi.sub_apply]
    exact integral_sampleResponse_sub_mul_sub hS P D Xs hXm hid hlaw
      (fun i k hik ↦ hind.indepFun hik) hn a b
  have hintLL : ∫ ω, LF (h ω) * LG (h ω) ∂P =
      ∑ a, ∑ b, Γ a b / n * (LF (coordUnit a) * LG (coordUnit b)) := by
    rw [show (fun ω ↦ LF (h ω) * LG (h ω)) =
        fun ω ↦ ∑ a, ∑ b, h ω a * h ω b * (LF (coordUnit a) * LG (coordUnit b)) from
      funext fun ω ↦ linearMap_mul_linearMap_eq_sum LF LG (h ω)]
    rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦ (hinthh a b).mul_const _]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [integral_finsetSum _ fun b _ ↦ (hinthh a b).mul_const _]
    simp only [integral_mul_const, hsec]
  have hintLL' : Integrable (fun ω ↦ LF (h ω) * LG (h ω)) P := by
    rw [show (fun ω ↦ LF (h ω) * LG (h ω)) =
        fun ω ↦ ∑ a, ∑ b, h ω a * h ω b * (LF (coordUnit a) * LG (coordUnit b)) from
      funext fun ω ↦ linearMap_mul_linearMap_eq_sum LF LG (h ω)]
    exact integrable_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦
      (hinthh a b).mul_const _
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
  -- the plug-in deviations are bounded
  have hplugF : ∀ ω, |plugIn hS ν F C M (sampleResponse S Xs n ω) - GF M| ≤ 2 * BF := fun ω ↦ by
    have h1 : ∀ v, |GF v| ≤ BF := fun v ↦ hGF ▸ abs_obsResponse_le hS ν hBF v
    unfold plugIn
    by_cases hc : sampleResponse S Xs n ω ∈ C
    · rw [Set.piecewise_eq_of_mem _ _ _ hc, ← hGF]
      linarith [abs_sub (GF (sampleResponse S Xs n ω)) (GF M), h1 (sampleResponse S Xs n ω), h1 M]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hc, ← hGF, sub_self, abs_zero]
      linarith [h1 M]
  have hplugG : ∀ ω, |plugIn hS ν G C M (sampleResponse S Xs n ω) - GG M| ≤ 2 * BG := fun ω ↦ by
    have h1 : ∀ v, |GG v| ≤ BG := fun v ↦ hGG ▸ abs_obsResponse_le hS ν hBG v
    unfold plugIn
    by_cases hc : sampleResponse S Xs n ω ∈ C
    · rw [Set.piecewise_eq_of_mem _ _ _ hc, ← hGG]
      linarith [abs_sub (GG (sampleResponse S Xs n ω)) (GG M), h1 (sampleResponse S Xs n ω), h1 M]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hc, ← hGG, sub_self, abs_zero]
      linarith [h1 M]
  -- the pointwise bound on the moment body
  have hpt : ∀ ω, sampleResponse S Xs n ω ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S →
      |(plugIn hS ν F C M (sampleResponse S Xs n ω) - GF M) *
          (plugIn hS ν G C M (sampleResponse S Xs n ω) - GG M) - LF (h ω) * LG (h ω)| ≤
        Cq * δ * ‖h ω‖ ^ 2 + K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω := by
    intro ω hω
    have hhω : h ω = sampleResponse S Xs n ω - M := by rw [hh]
    by_cases hsmall : ‖h ω‖ ≤ δ'
    · have hinC : sampleResponse S Xs n ω ∈ C :=
        hCnhd _ hω (by rw [← hhω]; exact hsmall.trans (hδ' ▸ min_le_left r δ))
      have hmem : sampleResponse S Xs n ω - M ∈ 𝕍 := sub_mem_dirSpan_of_mem_momentBody' hS ν hMmb hω
      have hnorm : ‖(⟨sampleResponse S Xs n ω - M, hmem⟩ : 𝕍)‖ = ‖sampleResponse S Xs n ω - M‖ :=
        rfl
      have hzδ : ‖(⟨sampleResponse S Xs n ω - M, hmem⟩ : 𝕍)‖ ≤ δ := by
        rw [hnorm, ← hhω]; exact hsmall.trans hδ'δ
      have hzF := hpeF ⟨_, hmem⟩ (by simpa using hinC) hzδ
      have hzG := hpeG ⟨_, hmem⟩ (by simpa using hinC) hzδ
      simp only [add_sub_cancel, hnorm] at hzF hzG
      rw [Set.indicator_of_notMem (by simpa using hsmall), mul_zero, add_zero]
      unfold plugIn
      rw [Set.piecewise_eq_of_mem _ _ _ hinC, Set.piecewise_eq_of_mem _ _ _ hinC, ← hGF, ← hGG, hhω]
      -- write the deviations as linear part plus remainder
      obtain ⟨rF, hrF⟩ : ∃ rF : ℝ, rF = GF (sampleResponse S Xs n ω) - GF M -
        LF (sampleResponse S Xs n ω - M) := ⟨_, rfl⟩
      obtain ⟨rG, hrG⟩ : ∃ rG : ℝ, rG = GG (sampleResponse S Xs n ω) - GG M -
        LG (sampleResponse S Xs n ω - M) := ⟨_, rfl⟩
      rw [← hrF] at hzF
      rw [← hrG] at hzG
      have eF : GF (sampleResponse S Xs n ω) - GF M = LF (sampleResponse S Xs n ω - M) + rF := by
        rw [hrF]; ring
      have eG : GG (sampleResponse S Xs n ω) - GG M = LG (sampleResponse S Xs n ω - M) + rG := by
        rw [hrG]; ring
      rw [eF, eG]
      have hLFb := hLFh ω
      have hLGb := hLGh ω
      rw [hhω] at hLFb hLGb
      obtain ⟨u, hu⟩ : ∃ u : ℝ, u = ‖sampleResponse S Xs n ω - M‖ := ⟨_, rfl⟩
      rw [← hu] at hzF hzG hLFb hLGb ⊢
      have hu0 : 0 ≤ u := hu ▸ norm_nonneg _
      have huδ : u ≤ δ := by rw [hu, ← hhω]; exact hsmall.trans hδ'δ
      have e : (LF (sampleResponse S Xs n ω - M) + rF) * (LG (sampleResponse S Xs n ω - M) + rG) -
          LF (sampleResponse S Xs n ω - M) * LG (sampleResponse S Xs n ω - M) =
          LF (sampleResponse S Xs n ω - M) * rG + rF * LG (sampleResponse S Xs n ω - M) +
            rF * rG := by ring
      rw [e]
      calc |LF (sampleResponse S Xs n ω - M) * rG + rF * LG (sampleResponse S Xs n ω - M) +
            rF * rG|
          ≤ |LF (sampleResponse S Xs n ω - M)| * |rG| + |rF| * |LG (sampleResponse S Xs n ω - M)| +
            |rF| * |rG| := by
            refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
            · rw [abs_mul, abs_mul]
            · rw [abs_mul]
        _ ≤ KF * u * (CG * u ^ 2) + CF * u ^ 2 * (KG * u) + CF * u ^ 2 * (CG * u ^ 2) := by
            gcongr
        _ = (KF * CG * u + KG * CF * u + CF * CG * u ^ 2) * u ^ 2 := by ring
        _ ≤ (KF * CG * δ + KG * CF * δ + CF * CG * δ) * u ^ 2 := by
            have hu2 : u ^ 2 ≤ δ := by nlinarith
            gcongr
        _ = Cq * δ * u ^ 2 := by rw [hCq]; ring
    · rw [Set.indicator_of_mem (show ω ∈ {ω | δ' < ‖h ω‖} from not_le.mp hsmall), Pi.one_apply,
        mul_one]
      have hnn : 0 ≤ Cq * δ * ‖h ω‖ ^ 2 := by
        have : 0 ≤ Cq := by rw [hCq]; positivity
        positivity
      have hb1 := hplugF ω
      have hb2 := hplugG ω
      have hb3 : |LF (h ω)| ≤ KF * (2 * B) :=
        (hLFh ω).trans (mul_le_mul_of_nonneg_left (hhn ω) hKF0)
      have hb4 : |LG (h ω)| ≤ KG * (2 * B) :=
        (hLGh ω).trans (mul_le_mul_of_nonneg_left (hhn ω) hKG0)
      calc |(plugIn hS ν F C M (sampleResponse S Xs n ω) - GF M) *
            (plugIn hS ν G C M (sampleResponse S Xs n ω) - GG M) - LF (h ω) * LG (h ω)|
          ≤ |plugIn hS ν F C M (sampleResponse S Xs n ω) - GF M| *
              |plugIn hS ν G C M (sampleResponse S Xs n ω) - GG M| + |LF (h ω)| * |LG (h ω)| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_mul]
        _ ≤ 2 * BF * (2 * BG) + KF * (2 * B) * (KG * (2 * B)) := by
            gcongr
        _ = K := by rw [hK]; ring
        _ ≤ Cq * δ * ‖h ω‖ ^ 2 + K := by linarith
  -- integrate the pointwise bound
  have hae : ∀ᵐ ω ∂P, ‖(plugIn hS ν F C M (sampleResponse S Xs n ω) - GF M) *
      (plugIn hS ν G C M (sampleResponse S Xs n ω) - GG M) - LF (h ω) * LG (h ω)‖ ≤
      Cq * δ * ‖h ω‖ ^ 2 + K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω := by
    filter_upwards [ae_sampleResponse_mem_momentBody hS ν P D hDν Xs hXm hid hlaw] with ω hω
    rw [Real.norm_eq_abs]
    exact hpt ω (hω n hn)
  have hmeasS : MeasurableSet {ω | δ' < ‖h ω‖} := measurableSet_lt measurable_const hmeashv.norm
  have hI0 : Integrable (fun ω ↦ Cq * δ * ‖h ω‖ ^ 2) P := hintsq'.const_mul _
  have hI1 : Integrable (fun ω ↦ K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hmeasS).const_mul _
  have hintbd : Integrable (fun ω ↦ Cq * δ * ‖h ω‖ ^ 2 +
      K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω) P := hI0.add hI1
  have hmplug : ∀ {H : X → ℝ} (hH : Bdd H),
      Measurable fun ω ↦ plugIn hS ν H C M (sampleResponse S Xs n ω) := fun hH ↦
    (ContinuousOn.measurable_piecewise (continuousOn_obsResponse hS ν hH hCK)
      continuousOn_const hC.isClosed.measurableSet).comp hmeasR
  have hΦ : Integrable (fun ω ↦ (plugIn hS ν F C M (sampleResponse S Xs n ω) - GF M) *
      (plugIn hS ν G C M (sampleResponse S Xs n ω) - GG M)) P :=
    Integrable.of_bound (((hmplug hF).sub measurable_const).mul
      ((hmplug hG).sub measurable_const)).aestronglyMeasurable (2 * BF * (2 * BG))
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hplugF ω) (hplugG ω) (abs_nonneg _) (by positivity))
  have hkey := norm_integral_le_of_norm_le hintbd hae
  rw [integral_sub hΦ hintLL', hintLL, integral_add hI0 hI1, integral_const_mul,
    integral_const_mul, integral_indicator_one hmeasS, Real.norm_eq_abs] at hkey
  have hκ : ∑ a, ∑ b, Γ a b * (LF (coordUnit a) * LG (coordUnit b)) =
      (n : ℝ) * ∑ a, ∑ b, Γ a b / n * (LF (coordUnit a) * LG (coordUnit b)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    field_simp
  rw [hκ, ← mul_sub, abs_mul, abs_of_pos hn']
  calc (n : ℝ) * |(∫ ω, (plugIn hS ν F C M (sampleResponse S Xs n ω) - GF M) *
          (plugIn hS ν G C M (sampleResponse S Xs n ω) - GG M) ∂P) -
        ∑ a, ∑ b, Γ a b / n * (LF (coordUnit a) * LG (coordUnit b))|
      ≤ (n : ℝ) * (Cq * δ * ∫ ω, ‖h ω‖ ^ 2 ∂P + K * P.real {ω | δ' < ‖h ω‖}) :=
        mul_le_mul_of_nonneg_left hkey hn'.le
    _ ≤ (n : ℝ) * (Cq * δ * ((∑ a, ∫ x, (S a x - M a) ^ 2 ∂D) / n) +
          K * P.real {ω | δ' < ‖h ω‖}) := by
        have : 0 ≤ Cq := by rw [hCq]; positivity
        gcongr
    _ = Cq * δ * ∑ a, (∫ x, (S a x - M a) ^ 2 ∂D) + (n : ℝ) * K * P.real {ω | δ' < ‖h ω‖} := by
        field_simp

/-- **The second moment of the plug-in deviations**, on a given neighbourhood:
`n E[(Ĝ_{F,n} − G_F(M))(Ĝ_{G,n} − G_G(M))] → Σ_{a,b} Γ_{ab} lin_F(e_a) lin_G(e_b)`. -/
theorem plugIn_product_tendsto_of_nhd [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {F G : X → ℝ} (hF : Bdd F) (hG : Bdd G) {BF BG : ℝ} (hBF : ∀ x, |F x| ≤ BF)
    (hBG : ∀ x, |G x| ≤ BG) {C : Set (J → ℝ)} [DecidablePred (· ∈ C)] (hC : IsCompact C)
    (hCc : Convex ℝ C) (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {r : ℝ} (hr : 0 < r)
    (hCnhd : ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - dataMoment D S‖ ≤ r → M' ∈ C) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
        ∫ ω, (plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) -
            obsResponse hS ν F (dataMoment D S)) *
          (plugIn hS ν G C (dataMoment D S) (sampleResponse S Xs n ω) -
            obsResponse hS ν G (dataMoment D S)) ∂P) atTop
      (𝓝 (∑ a, ∑ b, (∫ x, (S a x - dataMoment D S a) * (S b x - dataMoment D S b) ∂D) *
        (linForm hS ν (dataMoment D S) hF (coordUnit a) *
          linForm hS ν (dataMoment D S) hG (coordUnit b)))) := by
  have hMmb := intrinsicInterior_subset hrel
  have hMC : dataMoment D S ∈ C := hCnhd _ hMmb (by simp [hr.le])
  have hB' : ∀ j, ∃ M, ∀ x, |S j x| ≤ M := fun j ↦ (hS j).2
  choose Bj hBj using hB'
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ j, |Bj j| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hBdef ▸ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hB : ∀ j x, |S j x| ≤ B := fun j x ↦
    (hBj j x).trans ((le_abs_self _).trans (hBdef ▸ Finset.single_le_sum (f := fun j ↦ |Bj j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)))
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF (Classical.arbitrary X))
  have hBG0 : 0 ≤ BG := (abs_nonneg _).trans (hBG (Classical.arbitrary X))
  obtain ⟨c, hc, htail⟩ := exists_tail_sampleResponse hS P D Xs hXm hid hlaw hind
  obtain ⟨δF, hδF, hpeF⟩ := exists_first_order_remainder hS ν hC hCc hCK hMC hF hBF
  obtain ⟨δG, hδG, hpeG⟩ := exists_first_order_remainder hS ν hC hCc hCK hMC hG hBG
  obtain ⟨CF, hCF⟩ : ∃ CF : ℝ, CF = BF + (1 / 2) *
    ∑ a, ∑ c, |biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit c)| := ⟨_, rfl⟩
  obtain ⟨CG, hCG⟩ : ∃ CG : ℝ, CG = BG + (1 / 2) *
    ∑ a, ∑ c, |biasForm hS ν (dataMoment D S) hG (coordUnit a) (coordUnit c)| := ⟨_, rfl⟩
  rw [← hCF] at hpeF
  rw [← hCG] at hpeG
  have hCF0 : 0 ≤ CF := by
    rw [hCF]
    have : 0 ≤ ∑ a, ∑ c, |biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit c)| :=
      Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun c _ ↦ abs_nonneg _
    positivity
  have hCG0 : 0 ≤ CG := by
    rw [hCG]
    have : 0 ≤ ∑ a, ∑ c, |biasForm hS ν (dataMoment D S) hG (coordUnit a) (coordUnit c)| :=
      Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun c _ ↦ abs_nonneg _
    positivity
  obtain ⟨KF, hKF⟩ : ∃ KF : ℝ, KF = ∑ a, |linForm hS ν (dataMoment D S) hF (coordUnit a)| :=
    ⟨_, rfl⟩
  obtain ⟨KG, hKG⟩ : ∃ KG : ℝ, KG = ∑ a, |linForm hS ν (dataMoment D S) hG (coordUnit a)| :=
    ⟨_, rfl⟩
  have hKF0 : 0 ≤ KF := hKF ▸ Finset.sum_nonneg fun a _ ↦ abs_nonneg _
  have hKG0 : 0 ≤ KG := hKG ▸ Finset.sum_nonneg fun a _ ↦ abs_nonneg _
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ a, ∫ x, (S a x - dataMoment D S a) ^ 2 ∂D := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hT ▸ Finset.sum_nonneg fun a _ ↦ integral_nonneg fun x ↦ sq_nonneg _
  obtain ⟨Cq, hCq⟩ : ∃ Cq : ℝ, Cq = KF * CG + KG * CF + CF * CG := ⟨_, rfl⟩
  have hCq0 : 0 ≤ Cq := by rw [hCq]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * BF * (2 * BG) + 2 * B * KF * (2 * B * KG) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min 1 (min (min δF δG) (η / (2 * (Cq * T + 1)))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact lt_min one_pos (lt_min (lt_min hδF hδG) (by positivity))
  have hδ1 : δ ≤ 1 := hδ ▸ min_le_left _ _
  have hδF' : δ ≤ δF := hδ ▸ ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδG' : δ ≤ δG :=
    hδ ▸ ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδη : δ ≤ η / (2 * (Cq * T + 1)) := hδ ▸ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min r δ := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := hδ' ▸ lt_min hr hδ0
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) *
      (K * (2 * Fintype.card J * Real.exp (-(c * n * δ' ^ 2))))) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (c * δ' ^ 2)
      (by positivity)).comp tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul (K * (2 * Fintype.card J))
    rw [mul_zero] at h2
    refine h2.congr' (Eventually.of_forall fun n ↦ ?_)
    simp only [Function.comp_def, Real.rpow_one]
    rw [show -(c * n * δ' ^ 2) = -(c * δ' ^ 2) * n by ring]
    ring
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (η / 2) (by positivity)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hcore := plugIn_product_core hS ν P D Xs hXm hind hid hlaw hDν hrel hF hG hBF hBG hB0 hB hC
    hCK hr hCnhd hδ0 hδ1 hCF0 hCG0 (fun z hz hz' ↦ hpeF z hz (hz'.trans hδF'))
    (fun z hz hz' ↦ hpeG z hz (hz'.trans hδG')) hn1
  rw [← hKF, ← hKG, ← hT, ← hδ'] at hcore
  have htail' := htail n hn1 δ' hδ'0
  have hN' := hN n hnN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hN'
  have hεT : (KF * CG + KG * CF + CF * CG) * δ * T ≤ η / 2 := by
    rw [← hCq]
    calc Cq * δ * T ≤ Cq * (η / (2 * (Cq * T + 1))) * T := by gcongr
      _ = η / 2 * (Cq * T / (Cq * T + 1)) := by field_simp
      _ ≤ η / 2 := mul_le_of_le_one_right (by positivity)
          (div_le_one_of_le₀ (by linarith) (by positivity))
  rw [Real.dist_eq]
  calc _ ≤ (KF * CG + KG * CF + CF * CG) * δ * T + (n : ℝ) *
        (2 * BF * (2 * BG) + 2 * B * KF * (2 * B * KG)) *
        P.real {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} := hcore
    _ ≤ (KF * CG + KG * CF + CF * CG) * δ * T + (n : ℝ) *
        (2 * BF * (2 * BG) + 2 * B * KF * (2 * B * KG)) *
        (2 * Fintype.card J * Real.exp (-(c * n * δ' ^ 2))) := by
        gcongr
    _ < η := by rw [← hK]; nlinarith

/-- **The joint covariance of plug-in reconstructions**, on a given neighbourhood:
`n Cov(Ĝ_{F,n}, Ĝ_{G,n}) → Σ_{a,b} Γ_{ab} lin_F(e_a) lin_G(e_b)`, the sandwich covariance. -/
theorem plugIn_covariance_tendsto_of_nhd [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {F G : X → ℝ} (hF : Bdd F) (hG : Bdd G) {BF BG : ℝ} (hBF : ∀ x, |F x| ≤ BF)
    (hBG : ∀ x, |G x| ≤ BG) {C : Set (J → ℝ)} [DecidablePred (· ∈ C)] (hC : IsCompact C)
    (hCc : Convex ℝ C) (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {r : ℝ} (hr : 0 < r)
    (hCnhd : ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - dataMoment D S‖ ≤ r → M' ∈ C) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
        ((∫ ω, (plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) -
            obsResponse hS ν F (dataMoment D S)) *
          (plugIn hS ν G C (dataMoment D S) (sampleResponse S Xs n ω) -
            obsResponse hS ν G (dataMoment D S)) ∂P) -
        (∫ ω, plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) -
            obsResponse hS ν F (dataMoment D S) ∂P) *
          ∫ ω, plugIn hS ν G C (dataMoment D S) (sampleResponse S Xs n ω) -
            obsResponse hS ν G (dataMoment D S) ∂P)) atTop
      (𝓝 (∑ a, ∑ b, (∫ x, (S a x - dataMoment D S a) * (S b x - dataMoment D S b) ∂D) *
        (linForm hS ν (dataMoment D S) hF (coordUnit a) *
          linForm hS ν (dataMoment D S) hG (coordUnit b)))) := by
  have hprod := plugIn_product_tendsto_of_nhd hS ν P D Xs hXm hind hid hlaw hDν hrel hF hG hBF
    hBG hC hCc hCK hr hCnhd
  have hbF := reconstruction_bias_of_nhd hS ν P D Xs hXm hind hid hlaw hDν hrel hF hBF hC hCc hCK
    hr hCnhd
  have hbG := reconstruction_bias_of_nhd hS ν P D Xs hXm hind hid hlaw hDν hrel hG hBG hC hCc hCK
    hr hCnhd
  -- the mean deviations are `O(1/n)`, so their scaled product vanishes
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hG0 : Tendsto (fun n : ℕ ↦ (∫ ω, plugIn hS ν G C (dataMoment D S)
      (sampleResponse S Xs n ω) ∂P) - obsResponse hS ν G (dataMoment D S)) atTop (𝓝 0) := by
    have h := hbG.mul hinv
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hcross := hbF.mul hG0
  rw [mul_zero] at hcross
  have h := hprod.sub hcross
  rw [sub_zero] at h
  refine h.congr' (Eventually.of_forall fun n ↦ ?_)
  simp only
  rw [integral_sub, integral_sub, integral_const, integral_const, probReal_univ, one_smul,
    one_smul]
  · ring
  all_goals first
    | exact integrable_const _
    | exact integrable_plugIn_sampleResponse hS ν P Xs hXm hC hCK hF hBF _ _
    | exact integrable_plugIn_sampleResponse hS ν P Xs hXm hC hCK hG hBG _ _

omit [IsProbabilityMeasure P] hXm hind hid hlaw in
/-- The sandwich covariance is the data expectation of the product of the linear forms on the
centred features: `Σ_{a,b} Γ_{ab} lin_F(e_a) lin_G(e_b) = E_D[lin_F(S − M) lin_G(S − M)]`. -/
theorem sum_dataCov_mul_linForm_eq_integral [DecidableEq J] {F G : X → ℝ} (hF : Bdd F)
    (hG : Bdd G) (M : J → ℝ) :
    ∑ a, ∑ b, (∫ x, (S a x - dataMoment D S a) * (S b x - dataMoment D S b) ∂D) *
        (linForm hS ν M hF (coordUnit a) * linForm hS ν M hG (coordUnit b)) =
      ∫ x, linForm hS ν M hF (fun j ↦ S j x - dataMoment D S j) *
        linForm hS ν M hG (fun j ↦ S j x - dataMoment D S j) ∂D := by
  have hint : ∀ a b, Integrable (fun x ↦ (S a x - dataMoment D S a) * (S b x - dataMoment D S b) *
      (linForm hS ν M hF (coordUnit a) * linForm hS ν M hG (coordUnit b))) D := fun a b ↦
    (integrable_of_bdd_prob _ (((hS a).sub (Bdd.const _)).mul ((hS b).sub (Bdd.const _)))).mul_const
      _
  rw [show (fun x ↦ linForm hS ν M hF (fun j ↦ S j x - dataMoment D S j) *
      linForm hS ν M hG (fun j ↦ S j x - dataMoment D S j)) = fun x ↦ ∑ a, ∑ b,
      (S a x - dataMoment D S a) * (S b x - dataMoment D S b) *
        (linForm hS ν M hF (coordUnit a) * linForm hS ν M hG (coordUnit b)) from
    funext fun x ↦ linearMap_mul_linearMap_eq_sum _ _ _]
  rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦ hint a b]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [integral_finsetSum _ fun b _ ↦ hint a b]
  exact Finset.sum_congr rfl fun b _ ↦ by rw [integral_mul_const]

/-- **The joint covariance of plug-in reconstructions.** For i.i.d. samples of `D ≪ ν` with
interior response `M = E_D S`, there is a compact convex interior neighbourhood `C` of `M` such
that for the truncated plug-in estimators of any two bounded observables,
`n Cov(Ĝ_{F,n}, Ĝ_{G,n}) → Σ_{a,b} Γ_{ab} lin_F(e_a) lin_G(e_b)`, which is
`E_D[lin_F(S − M) lin_G(S − M)]`: the sandwich covariance of the influence functions. -/
theorem plugIn_covariance_tendsto (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∃ C : Set (J → ℝ), IsCompact C ∧ Convex ℝ C ∧
      C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) ∧ dataMoment D S ∈ C ∧
      ∀ [DecidablePred (· ∈ C)], ∀ {F G : X → ℝ} (hF : Bdd F) (hG : Bdd G) {BF BG : ℝ},
        (∀ x, |F x| ≤ BF) → (∀ x, |G x| ≤ BG) →
        Tendsto (fun n : ℕ ↦ (n : ℝ) *
          ((∫ ω, (plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) -
              obsResponse hS ν F (dataMoment D S)) *
            (plugIn hS ν G C (dataMoment D S) (sampleResponse S Xs n ω) -
              obsResponse hS ν G (dataMoment D S)) ∂P) -
          (∫ ω, plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) -
              obsResponse hS ν F (dataMoment D S) ∂P) *
            ∫ ω, plugIn hS ν G C (dataMoment D S) (sampleResponse S Xs n ω) -
              obsResponse hS ν G (dataMoment D S) ∂P)) atTop
        (𝓝 (∫ x, linForm hS ν (dataMoment D S) hF (fun j ↦ S j x - dataMoment D S j) *
          linForm hS ν (dataMoment D S) hG (fun j ↦ S j x - dataMoment D S j) ∂D)) := by
  obtain ⟨r, hr, C, hC, hCc, hCK, hCnhd⟩ := exists_compact_convex_nhd hS ν hrel
  have hMC : dataMoment D S ∈ C := hCnhd _ (intrinsicInterior_subset hrel) (by simp [hr.le])
  refine ⟨C, hC, hCc, hCK, hMC, ?_⟩
  intro _ F G hF hG BF BG hBF hBG
  classical
  rw [← sum_dataCov_mul_linForm_eq_integral hS ν D hF hG]
  exact plugIn_covariance_tendsto_of_nhd hS ν P D Xs hXm hind hid hlaw hDν hrel hF hG hBF hBG hC
    hCc hCK hr hCnhd

end Assembly

end Laplace.Multi
