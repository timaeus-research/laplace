/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BiasForm
import Laplace.Multi.EmpiricalMoments
import Laplace.Multi.EmpiricalTotalVariation

/-!
# The reconstruction-bias theorem

For i.i.d. samples of a data distribution `D ≪ ν` with interior response `M`, the truncated plug-in
estimator `Ĝ_n = G_F(M̂_n)` (falling back to `G_F(M)` outside a compact convex neighbourhood `C`
of `M`) of the reconstructed response `G_F(M) = ∫ F dQ_M` has bias

  `n (E Ĝ_n − G_F(M)) → ½ Σ_{a,b} Γ_{ab} b_F(e_a, e_b)`,

with `Γ = Cov_D(S)` the data covariance of the features and `b_F` the bias form
(`reconstruction_bias`). The proof assembles the uniform Peano expansion in bias-form notation,
unbiasedness and the `Γ/n` second moments of `M̂_n`, and the Hoeffding tail for the exceptional set.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory

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

/-- The reconstructed response of an observable, `G_F(M') = ∫ F dQ_{M'}`. -/
noncomputable def obsResponse (F : X → ℝ) (M' : J → ℝ) : ℝ := ∫ x, F x ∂(Pfam (θr M'))

/-- The reconstructed response is bounded by the observable's bound. -/
theorem abs_obsResponse_le {F : X → ℝ} {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) (M' : J → ℝ) :
    |obsResponse hS ν F M'| ≤ BF := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M')
  have := norm_integral_le_of_norm_le_const (μ := Pfam (θr M')) (f := F) (C := BF)
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hBF x)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this

set_option linter.unusedFintypeInType false in
/-- Differences of points of the moment body lie in the direction subspace. -/
theorem sub_mem_dirSpan_of_mem_momentBody' {M M' : J → ℝ}
    (hM : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S) (hM' : M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S) :
    M' - M ∈ 𝕍 := by
  have h1 := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS hM'
  have h2 := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS hM
  have := (dirSpan ν (fun _ ↦ (1 : ℝ)) S).sub_mem h1 h2
  rwa [sub_sub_sub_cancel_right] at this

/-- The reconstructed response is continuous on interior subsets of the moment body. -/
theorem continuousOn_obsResponse {F : X → ℝ} (hF : Bdd F) {C : Set (J → ℝ)}
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ContinuousOn (obsResponse hS ν F) C := by
  have hCm : C ⊆ momentBody ν (fun _ ↦ (1 : ℝ)) S := hCK.trans intrinsicInterior_subset
  obtain ⟨M, hMdef⟩ : ∃ M : J → ℝ, M = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 :=
    ⟨_, rfl⟩
  have hfix : ∀ M' ∈ C, M + ((dirProj S ν (M' - M) : 𝕍) : J → ℝ) = M' := fun M' hM' ↦ by
    have hmem : M' - M ∈ 𝕍 := hMdef ▸ sub_mem_dirSpan_of_mem_momentBody measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (hCm hM')
    rw [show dirProj S ν (M' - M) = ⟨M' - M, hmem⟩ from dirProj_coe S ν ⟨M' - M, hmem⟩]
    simp
  have hθ : ContinuousOn (fun w : 𝕍 ↦ θr (M + (w : J → ℝ)))
      ((fun M' ↦ dirProj S ν (M' - M)) '' C) := by
    subst hMdef
    refine continuousOn_responseTheta_add hS ν fun z hz ↦ ?_
    obtain ⟨M', hM', rfl⟩ := hz
    exact (hfix M' hM').symm ▸ hCK hM'
  have hπ : Continuous fun M' : J → ℝ ↦ dirProj S ν (M' - M) :=
    (LinearMap.continuous_of_finiteDimensional _).comp (continuous_id.sub continuous_const)
  have hcomp : ContinuousOn (fun M' : J → ℝ ↦
      ∫ x, F x ∂(Pfam (θr (M + ((dirProj S ν (M' - M) : 𝕍) : J → ℝ))))) C :=
    (continuous_integral_family hS ν hF).comp_continuousOn
      ((continuous_subtype_val.comp_continuousOn hθ).comp hπ.continuousOn (mapsTo_image _ _))
  refine hcomp.congr fun M' hM' ↦ ?_
  simp only [obsResponse, hfix M' hM']

/-- The data response `M_D = E_D S`. -/
noncomputable def dataMoment (D : Measure X) (S : J → X → ℝ) : J → ℝ := fun j ↦ ∫ x, S j x ∂D

/-- **The truncated plug-in estimator**: `G_F(M')` on `C`, the fallback `G_F(M)` outside. -/
noncomputable def plugIn (F : X → ℝ) (C : Set (J → ℝ)) [DecidablePred (· ∈ C)] (M M' : J → ℝ) :
    ℝ :=
  C.piecewise (obsResponse hS ν F) (fun _ ↦ obsResponse hS ν F M) M'

omit [Nonempty X] [Nonempty J] hS in
/-- The sup norm is dominated by the Euclidean sum of squares. -/
theorem norm_sq_le_sum_sq (h : J → ℝ) : ‖h‖ ^ 2 ≤ ∑ a, h a ^ 2 := by
  have hs : 0 ≤ ∑ a, h a ^ 2 := Finset.sum_nonneg fun a _ ↦ sq_nonneg _
  have : ‖h‖ ≤ Real.sqrt (∑ a, h a ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a ↦ ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun a ↦ h a ^ 2)
      (fun a _ ↦ sq_nonneg _) (Finset.mem_univ a))
  calc ‖h‖ ^ 2 ≤ Real.sqrt (∑ a, h a ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = ∑ a, h a ^ 2 := Real.sq_sqrt hs

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X)
  [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hind : iIndepFun Xs P) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hXm hind hid hlaw

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [MeasurableSpace Ω]
  [IsProbabilityMeasure P] [IsProbabilityMeasure D] hXm hind hid hlaw in
/-- The empirical response is bounded by the feature bound. -/
theorem abs_sampleResponse_le {B : ℝ} (hB : ∀ j x, |S j x| ≤ B) {n : ℕ} (hn : 0 < n) (ω : Ω)
    (j : J) : |sampleResponse S Xs n ω j| ≤ B := by
  unfold sampleResponse
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_div, abs_of_pos hn', div_le_iff₀ hn']
  calc |∑ i ∈ Finset.range n, S j (Xs i ω)| ≤ ∑ i ∈ Finset.range n, |S j (Xs i ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, B := Finset.sum_le_sum fun i _ ↦ hB j _
    _ = B * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-- **The core estimate of the reconstruction-bias theorem** at a fixed sample size: the scaled
bias differs from `½ Σ Γ_ab b_F(e_a, e_b)` by at most `BF ε Σ_a Γ_aa` plus `n K` times the
probability of the exceptional set `{‖M̂_n − M‖ > min r δ}`. -/
theorem reconstruction_bias_core [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {F : X → ℝ} (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j x, |S j x| ≤ B) {C : Set (J → ℝ)} [DecidablePred (· ∈ C)] (hC : IsCompact C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {r : ℝ} (hr : 0 < r)
    (hCnhd : ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - dataMoment D S‖ ≤ r → M' ∈ C)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hpe : ∀ z : 𝕍, dataMoment D S + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |obsResponse hS ν F (dataMoment D S + z) - obsResponse hS ν F (dataMoment D S) -
        linForm hS ν (dataMoment D S) hF (z : J → ℝ) -
        (1 / 2) * biasForm hS ν (dataMoment D S) hF (z : J → ℝ) (z : J → ℝ)| ≤
        BF * (ε * ‖z‖ ^ 2))
    {n : ℕ} (hn : 0 < n) :
    |(n : ℝ) * ((∫ ω, plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) ∂P) -
        obsResponse hS ν F (dataMoment D S)) -
      (1 / 2) * ∑ a, ∑ b, (∫ x, (S a x - dataMoment D S a) * (S b x - dataMoment D S b) ∂D) *
        biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b)| ≤
      BF * ε * ∑ a, (∫ x, (S a x - dataMoment D S a) ^ 2 ∂D) +
        (n : ℝ) * (2 * BF + 2 * B * (∑ a, |linForm hS ν (dataMoment D S) hF (coordUnit a)|) +
          (1 / 2) * (4 * B ^ 2 * ∑ a, ∑ b,
            |biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b)|)) *
        P.real {ω | min r δ < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} := by
  classical
  have hMmb : dataMoment D S ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := intrinsicInterior_subset hrel
  have hMC : dataMoment D S ∈ C := hCnhd _ hMmb (by simp [hr.le])
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF (Classical.arbitrary X))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- abbreviations
  obtain ⟨M, hM⟩ : ∃ M : J → ℝ, M = dataMoment D S := ⟨_, rfl⟩
  rw [← hM] at hpe hrel hMmb hMC hCnhd ⊢
  obtain ⟨L, hL⟩ : ∃ L : (J → ℝ) →ₗ[ℝ] ℝ, L = linForm hS ν M hF := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : (J → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ, b = biasForm hS ν M hF := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : (J → ℝ) → ℝ, G = obsResponse hS ν F := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : Ω → J → ℝ, h = fun ω ↦ sampleResponse S Xs n ω - M := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : J → J → ℝ,
    ∀ a b, Γ a b = ∫ x, (S a x - M a) * (S b x - M b) ∂D := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * BF + 2 * B * (∑ a, |L (coordUnit a)|) +
    (1 / 2) * (4 * B ^ 2 * ∑ a, ∑ b', |b (coordUnit a) (coordUnit b')|) := ⟨_, rfl⟩
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min r δ := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := hδ' ▸ lt_min hr hδ
  rw [← hL, ← hb, ← hG, ← hK, ← hδ']
  simp only [← hΓ]
  rw [← hL, ← hb, ← hG] at hpe
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
  have hinthh : ∀ a b', Integrable (fun ω ↦ h ω a * h ω b') P := fun a b' ↦
    Integrable.of_bound ((hmeash a).mul (hmeash b')).aestronglyMeasurable (2 * B * (2 * B))
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hhabs ω a) (hhabs ω b') (abs_nonneg _) (by positivity))
  -- first and second moments
  have hmean : ∀ a, ∫ ω, h ω a ∂P = 0 := fun a ↦ by
    rw [hh]
    simp only [Pi.sub_apply]
    rw [integral_sub (hintR a) (integrable_const _), integral_const,
      probReal_univ, one_smul, hM]
    exact sub_eq_zero.2 (integral_sampleResponse hS P D Xs hXm hid hlaw hn a)
  have hsec : ∀ a b', ∫ ω, h ω a * h ω b' ∂P = Γ a b' / n := fun a b' ↦ by
    rw [hh, hΓ a b', hM]
    simp only [Pi.sub_apply]
    exact integral_sampleResponse_sub_mul_sub hS P D Xs hXm hid hlaw
      (fun i k hik ↦ hind.indepFun hik) hn a b'
  have hintL : ∫ ω, L (h ω) ∂P = 0 := by
    rw [show (fun ω ↦ L (h ω)) = fun ω ↦ ∑ a, h ω a * L (coordUnit a) from
      funext fun ω ↦ linearMap_eq_sum_coordUnit L (h ω)]
    rw [integral_finsetSum _ fun a _ ↦ (hinth a).mul_const _]
    simp only [integral_mul_const, hmean, zero_mul, Finset.sum_const_zero]
  have hintb : ∫ ω, b (h ω) (h ω) ∂P = ∑ a, ∑ b', Γ a b' / n * b (coordUnit a) (coordUnit b') := by
    have e : (fun ω ↦ b (h ω) (h ω)) =
        fun ω ↦ ∑ a, ∑ b', h ω a * h ω b' * b (coordUnit a) (coordUnit b') :=
      funext fun ω ↦ by rw [hb]; exact biasForm_eq_sum hS ν hF _ _
    rw [e]
    rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b' _ ↦ (hinthh a b').mul_const _]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [integral_finsetSum _ fun b' _ ↦ (hinthh a b').mul_const _]
    simp only [integral_mul_const, hsec]
  have hintsq : ∫ ω, ‖h ω‖ ^ 2 ∂P ≤ (∑ a, ∫ x, (S a x - M a) ^ 2 ∂D) / n := by
    have hint1 : Integrable (fun ω ↦ ∑ a, h ω a ^ 2) P :=
      integrable_finsetSum _ fun a _ ↦ by simpa [sq] using hinthh a a
    have hint0 : Integrable (fun ω ↦ ‖h ω‖ ^ 2) P :=
      Integrable.of_bound ((hmeashv.norm).pow_const 2).aestronglyMeasurable ((2 * B) ^ 2)
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hhn ω) 2)
    calc ∫ ω, ‖h ω‖ ^ 2 ∂P ≤ ∫ ω, ∑ a, h ω a ^ 2 ∂P :=
        integral_mono hint0 hint1 fun ω ↦ norm_sq_le_sum_sq _
      _ = ∑ a, Γ a a / n := by
        rw [integral_finsetSum _ fun a _ ↦ by simpa [sq] using hinthh a a]
        exact Finset.sum_congr rfl fun a _ ↦ by rw [← hsec a a]; simp only [sq]
      _ = (∑ a, ∫ x, (S a x - M a) ^ 2 ∂D) / n := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun a _ ↦ by simp only [hΓ, sq]
  -- bounds on the linear and bias terms
  have hLbd : ∀ v : J → ℝ, (∀ a, |v a| ≤ 2 * B) → |L v| ≤ 2 * B * ∑ a, |L (coordUnit a)| := by
    intro v hv
    rw [linearMap_eq_sum_coordUnit L v, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hv a) (abs_nonneg _)
  have hbbd : ∀ v : J → ℝ, (∀ a, |v a| ≤ 2 * B) →
      |b v v| ≤ 4 * B ^ 2 * ∑ a, ∑ b', |b (coordUnit a) (coordUnit b')| := by
    intro v hv
    rw [hb, biasForm_eq_sum hS ν hF v v, ← hb, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ ↦ ?_)
    rw [abs_mul, abs_mul]
    have : |v a| * |v b'| ≤ 4 * B ^ 2 := by
      calc |v a| * |v b'| ≤ 2 * B * (2 * B) :=
          mul_le_mul (hv a) (hv b') (abs_nonneg _) (by positivity)
        _ = 4 * B ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  -- the pointwise bound on the moment body
  have hpt : ∀ ω, sampleResponse S Xs n ω ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S →
      |plugIn hS ν F C M (sampleResponse S Xs n ω) - G M -
        (L (h ω) + (1 / 2) * b (h ω) (h ω))| ≤
        BF * ε * ‖h ω‖ ^ 2 + K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω := by
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
      unfold plugIn
      rw [Set.piecewise_eq_of_mem _ _ _ hinC, ← hG, hhω]
      have e : G (sampleResponse S Xs n ω) - G M - (L (sampleResponse S Xs n ω - M) +
          1 / 2 * b (sampleResponse S Xs n ω - M) (sampleResponse S Xs n ω - M)) =
          G (sampleResponse S Xs n ω) - G M - L (sampleResponse S Xs n ω - M) -
          1 / 2 * b (sampleResponse S Xs n ω - M) (sampleResponse S Xs n ω - M) := by ring
      rw [e]
      exact hz.trans (le_of_eq (by ring))
    · rw [Set.indicator_of_mem (show ω ∈ {ω | δ' < ‖h ω‖} from not_le.mp hsmall), Pi.one_apply,
        mul_one]
      have hplug : |plugIn hS ν F C M (sampleResponse S Xs n ω) - G M| ≤ 2 * BF := by
        have h1 : ∀ v, |G v| ≤ BF := fun v ↦ hG ▸ abs_obsResponse_le hS ν hBF v
        unfold plugIn
        by_cases hc : sampleResponse S Xs n ω ∈ C
        · rw [Set.piecewise_eq_of_mem _ _ _ hc, ← hG]
          linarith [abs_sub (G (sampleResponse S Xs n ω)) (G M), h1 (sampleResponse S Xs n ω),
            h1 M]
        · rw [Set.piecewise_eq_of_notMem _ _ _ hc, ← hG, sub_self, abs_zero]
          linarith [h1 M]
      have hL' := hLbd (h ω) (hhabs ω)
      have hb' := hbbd (h ω) (hhabs ω)
      have hnn : 0 ≤ BF * ε * ‖h ω‖ ^ 2 := by positivity
      calc |plugIn hS ν F C M (sampleResponse S Xs n ω) - G M -
            (L (h ω) + 1 / 2 * b (h ω) (h ω))|
          ≤ |plugIn hS ν F C M (sampleResponse S Xs n ω) - G M| +
            (|L (h ω)| + 1 / 2 * |b (h ω) (h ω)|) := by
            refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
            refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        _ ≤ K := by rw [hK]; linarith
        _ ≤ BF * ε * ‖h ω‖ ^ 2 + K := by linarith
  -- integrate the pointwise bound
  have hae : ∀ᵐ ω ∂P, ‖plugIn hS ν F C M (sampleResponse S Xs n ω) - G M -
      (L (h ω) + (1 / 2) * b (h ω) (h ω))‖ ≤
      BF * ε * ‖h ω‖ ^ 2 + K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω := by
    filter_upwards [ae_sampleResponse_mem_momentBody hS ν P D hDν Xs hXm hid hlaw] with ω hω
    rw [Real.norm_eq_abs]
    exact hpt ω (hω n hn)
  have hmeasS : MeasurableSet {ω | δ' < ‖h ω‖} := measurableSet_lt measurable_const hmeashv.norm
  have hintsq' : Integrable (fun ω ↦ ‖h ω‖ ^ 2) P :=
    Integrable.of_bound ((hmeashv.norm).pow_const 2).aestronglyMeasurable ((2 * B) ^ 2)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hhn ω) 2)
  have hI0 : Integrable (fun ω ↦ BF * ε * ‖h ω‖ ^ 2) P := hintsq'.const_mul _
  have hI1 : Integrable (fun ω ↦ K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hmeasS).const_mul _
  have hintbd : Integrable (fun ω ↦ BF * ε * ‖h ω‖ ^ 2 +
      K * {ω | δ' < ‖h ω‖}.indicator (1 : Ω → ℝ) ω) P := hI0.add hI1
  have hintplug : Integrable (fun ω ↦ plugIn hS ν F C M (sampleResponse S Xs n ω)) P := by
    have hm : Measurable fun ω ↦ plugIn hS ν F C M (sampleResponse S Xs n ω) :=
      (ContinuousOn.measurable_piecewise (continuousOn_obsResponse hS ν hF hCK)
        continuousOn_const hC.isClosed.measurableSet).comp hmeasR
    refine Integrable.of_bound hm.aestronglyMeasurable BF (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    unfold plugIn
    by_cases hc : sampleResponse S Xs n ω ∈ C
    · rw [Set.piecewise_eq_of_mem _ _ _ hc]; exact abs_obsResponse_le hS ν hBF _
    · rw [Set.piecewise_eq_of_notMem _ _ _ hc]; exact abs_obsResponse_le hS ν hBF _
  have hintL' : Integrable (fun ω ↦ L (h ω)) P := by
    rw [show (fun ω ↦ L (h ω)) = fun ω ↦ ∑ a, h ω a * L (coordUnit a) from
      funext fun ω ↦ linearMap_eq_sum_coordUnit L (h ω)]
    exact integrable_finsetSum _ fun a _ ↦ (hinth a).mul_const _
  have hintb' : Integrable (fun ω ↦ b (h ω) (h ω)) P := by
    rw [show (fun ω ↦ b (h ω) (h ω)) =
        fun ω ↦ ∑ a, ∑ b', h ω a * h ω b' * b (coordUnit a) (coordUnit b') from
      funext fun ω ↦ by rw [hb]; exact biasForm_eq_sum hS ν hF _ _]
    exact integrable_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b' _ ↦
      (hinthh a b').mul_const _
  have hΨ : Integrable (fun ω ↦ L (h ω) + (1 / 2) * b (h ω) (h ω)) P :=
    hintL'.add (hintb'.const_mul _)
  have hΦ : Integrable (fun ω ↦ plugIn hS ν F C M (sampleResponse S Xs n ω) - G M) P :=
    hintplug.sub (integrable_const _)
  have hkey := norm_integral_le_of_norm_le hintbd hae
  rw [integral_sub hΦ hΨ, integral_sub hintplug (integrable_const _), integral_const,
    probReal_univ, one_smul, integral_add hintL' (hintb'.const_mul _), hintL,
    integral_const_mul, hintb, zero_add, integral_add hI0 hI1, integral_const_mul,
    integral_const_mul, integral_indicator_one hmeasS, Real.norm_eq_abs] at hkey
  have hκ : (1 / 2) * ∑ a, ∑ b', Γ a b' * b (coordUnit a) (coordUnit b') =
      (n : ℝ) * ((1 / 2) * ∑ a, ∑ b', Γ a b' / n * b (coordUnit a) (coordUnit b')) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b' _ ↦ ?_
    field_simp
  rw [hκ, ← mul_sub, abs_mul, abs_of_pos hn']
  have hset' : {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - M j‖} = {ω | δ' < ‖h ω‖} := by
    rw [hh]; rfl
  rw [hset']
  calc (n : ℝ) * |(∫ ω, plugIn hS ν F C M (sampleResponse S Xs n ω) ∂P - G M) -
        (1 / 2 * ∑ a, ∑ b', Γ a b' / n * b (coordUnit a) (coordUnit b'))|
      ≤ (n : ℝ) * (BF * ε * ∫ ω, ‖h ω‖ ^ 2 ∂P + K * P.real {ω | δ' < ‖h ω‖}) :=
        mul_le_mul_of_nonneg_left hkey hn'.le
    _ ≤ (n : ℝ) * (BF * ε * ((∑ a, ∫ x, (S a x - M a) ^ 2 ∂D) / n) +
          K * P.real {ω | δ' < ‖h ω‖}) := by
        gcongr
    _ = BF * ε * ∑ a, (∫ x, (S a x - M a) ^ 2 ∂D) + (n : ℝ) * K * P.real {ω | δ' < ‖h ω‖} := by
        field_simp

/-- **The reconstruction-bias theorem.** For i.i.d. samples of `D ≪ ν` with interior response
`M = E_D S`, there is a compact convex interior neighbourhood `C` of `M` such that the truncated
plug-in estimator `Ĝ_n = G_F(M̂_n)` (fallback `G_F(M)` off `C`) has
`n (E Ĝ_n − G_F(M)) → ½ Σ_{a,b} Γ_{ab} b_F(e_a, e_b)`, `Γ = Cov_D(S)`. -/
theorem reconstruction_bias [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {F : X → ℝ} (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) :
    ∃ C : Set (J → ℝ), IsCompact C ∧ Convex ℝ C ∧
      C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) ∧ dataMoment D S ∈ C ∧
      ∀ [DecidablePred (· ∈ C)], Tendsto (fun n : ℕ ↦ (n : ℝ) *
        ((∫ ω, plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) ∂P) -
          obsResponse hS ν F (dataMoment D S))) atTop
        (𝓝 ((1 / 2) * ∑ a, ∑ b,
          (∫ x, (S a x - dataMoment D S a) * (S b x - dataMoment D S b) ∂D) *
            biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b))) := by
  obtain ⟨r, hr, C, hC, hCc, hCK, hCnhd⟩ := exists_compact_convex_nhd hS ν hrel
  have hMmb := intrinsicInterior_subset hrel
  have hMC : dataMoment D S ∈ C := hCnhd _ hMmb (by simp [hr.le])
  refine ⟨C, hC, hCc, hCK, hMC, ?_⟩
  intro _
  have hB' : ∀ j, ∃ M, ∀ x, |S j x| ≤ M := fun j ↦ (hS j).2
  choose Bj hBj using hB'
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ j, |Bj j| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hBdef ▸ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hB : ∀ j x, |S j x| ≤ B := fun j x ↦
    (hBj j x).trans ((le_abs_self _).trans (hBdef ▸ Finset.single_le_sum (f := fun j ↦ |Bj j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)))
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF (Classical.arbitrary X))
  obtain ⟨c, hc, htail⟩ := exists_tail_sampleResponse hS P D Xs hXm hid hlaw hind
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ a, ∫ x, (S a x - dataMoment D S a) ^ 2 ∂D := ⟨_, rfl⟩
  obtain ⟨KK, hKK⟩ : ∃ KK : ℝ, KK = 2 * BF +
      2 * B * (∑ a, |linForm hS ν (dataMoment D S) hF (coordUnit a)|) +
      (1 / 2) * (4 * B ^ 2 * ∑ a, ∑ b,
        |biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b)|) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hT ▸ Finset.sum_nonneg fun a _ ↦ integral_nonneg fun x ↦ sq_nonneg _
  have hKK0 : 0 ≤ KK := by
    rw [hKK]
    have h1 : 0 ≤ ∑ a, |linForm hS ν (dataMoment D S) hF (coordUnit a)| :=
      Finset.sum_nonneg fun a _ ↦ abs_nonneg _
    have h2 : 0 ≤ ∑ a, ∑ b, |biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b)| :=
      Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦ abs_nonneg _
    positivity
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = η / (2 * (BF * T + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ by positivity
  obtain ⟨δ, hδ, hpe⟩ := integral_response_peano_biasForm hS ν hC hCc hCK hF hBF ε hε0
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
  have hcore := reconstruction_bias_core hS ν P D Xs hXm hind hid hlaw hDν hrel hF hBF hB0 hB hC
    hCK hr hCnhd hε0.le hδ (fun z hz hz' ↦ hpe _ hMC z hz hz') hn1
  rw [← hT, ← hKK, ← hδ'] at hcore
  have htail' := htail n hn1 δ' hδ'0
  have hN' := hN n hnN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hN'
  have hεT : BF * ε * T ≤ η / 2 := by
    rw [hε, show BF * (η / (2 * (BF * T + 1))) * T = η / 2 * (BF * T / (BF * T + 1)) by
      field_simp]
    exact mul_le_of_le_one_right (by positivity)
      (div_le_one_of_le₀ (by linarith) (by positivity))
  rw [Real.dist_eq]
  calc _ ≤ BF * ε * T + (n : ℝ) * KK *
        P.real {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} := hcore
    _ ≤ BF * ε * T + (n : ℝ) * KK * (2 * Fintype.card J * Real.exp (-(c * n * δ' ^ 2))) := by
        gcongr
    _ < η := by nlinarith

omit [IsProbabilityMeasure P] hXm hind hid hlaw in
/-- **The bias coefficient is intrinsic**: `Σ_{a,b} Γ_ab b_F(e_a, e_b) = E_D b_F(S(x) − M, S(x) − M)`,
the data expectation of the bias form on the centred feature vector (independent of `π`). -/
theorem sum_dataCov_mul_biasForm_eq [DecidableEq J] {F : X → ℝ}
    (hF : Bdd F) (M : J → ℝ) :
    ∑ a, ∑ b, (∫ x, (S a x - dataMoment D S a) * (S b x - dataMoment D S b) ∂D) *
        biasForm hS ν M hF (coordUnit a) (coordUnit b) =
      ∫ x, biasForm hS ν M hF (fun j ↦ S j x - dataMoment D S j)
        (fun j ↦ S j x - dataMoment D S j) ∂D := by
  have hint : ∀ a b, Integrable (fun x ↦ (S a x - dataMoment D S a) * (S b x - dataMoment D S b) *
      biasForm hS ν M hF (coordUnit a) (coordUnit b)) D := fun a b ↦
    (integrable_of_bdd_prob _ (((hS a).sub (Bdd.const _)).mul ((hS b).sub (Bdd.const _)))).mul_const
      _
  rw [show (fun x ↦ biasForm hS ν M hF (fun j ↦ S j x - dataMoment D S j)
      (fun j ↦ S j x - dataMoment D S j)) = fun x ↦ ∑ a, ∑ b,
      (S a x - dataMoment D S a) * (S b x - dataMoment D S b) *
        biasForm hS ν M hF (coordUnit a) (coordUnit b) from
    funext fun x ↦ biasForm_eq_sum hS ν hF _ _]
  rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦ hint a b]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [integral_finsetSum _ fun b _ ↦ hint a b]
  exact Finset.sum_congr rfl fun b _ ↦ by rw [integral_mul_const]

end Assembly

end Laplace.Multi
