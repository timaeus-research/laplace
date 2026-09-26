/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ObservableTaylorUniform
import Laplace.Multi.BiasForm
import Laplace.Multi.ReconstructionBias

/-!
# The reconstruction bias, uniformly over observables

The uniform total-variation Peano expansion of the reconstruction density
(`integral_abs_famDens_response_peano_uniform`) is a statement about the whole law, so the
observable Taylor expansion holds with a modulus `δ` that does not depend on the observable
(`integral_response_peano_uniform_all`, `integral_response_peano_biasForm_all`). Since the linear
and bias coefficients of an observable `F` are bounded by `‖F‖∞` times fixed constants
(`abs_linForm_le_of_bound`, `abs_biasForm_le_of_bound`), the reconstruction-bias schema yields
the
bias limit **uniformly over the unit ball of bounded observables**
(`reconstruction_bias_uniform_of_nhd`): this is the dual form of the `L¹`-valued signed-measure bias
`n (E[q̃_n] − q_M) → ½ E_D[H_M[S−M, S−M]]`, the law-valued flagship of the response programme.
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

/-- **The observable Taylor expansion with a modulus uniform over all bounded observables.** -/
theorem integral_response_peano_uniform_all {C : Set (J → ℝ)} (hC : IsCompact C)
    (hCc : Convex ℝ C) (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∀ ε > 0, ∃ δ > 0, ∀ (F : X → ℝ), Bdd F → ∀ (BF : ℝ), (∀ x, |F x| ≤ BF) →
      ∀ M ∈ C, ∀ z : 𝕍, M + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |(∫ x, F x ∂(Pfam (θr (M + z)))) - (∫ x, F x ∂(Pfam (θr M))) -
        (∫ x, F x * responseScore hS ν M z x ∂(Pfam (θr M))) -
        (1 / 2) * ∫ x, F x * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x ∂(Pfam (θr M))| ≤
      BF * (ε * ‖z‖ ^ 2) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := integral_abs_famDens_response_peano_uniform hS ν hC hCc hCK ε hε
  refine ⟨δ, hδ, fun F hF BF hBF M hM z hMz hz ↦ ?_⟩
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

/-- The bias-form version of the uniform observable expansion. -/
theorem integral_response_peano_biasForm_all {C : Set (J → ℝ)} (hC : IsCompact C)
    (hCc : Convex ℝ C) (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∀ ε > 0, ∃ δ > 0, ∀ {F : X → ℝ} (hF : Bdd F) {BF : ℝ}, (∀ x, |F x| ≤ BF) →
      ∀ M ∈ C, ∀ z : 𝕍, M + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |(∫ x, F x ∂(Pfam (θr (M + z)))) - (∫ x, F x ∂(Pfam (θr M))) -
        linForm hS ν M hF (z : J → ℝ) -
        (1 / 2) * biasForm hS ν M hF (z : J → ℝ) (z : J → ℝ)| ≤ BF * (ε * ‖z‖ ^ 2) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := integral_response_peano_uniform_all hS ν hC hCc hCK ε hε
  refine ⟨δ, hδ, fun {F} hF {BF} hBF M hM z hMz hz ↦ ?_⟩
  rw [← integral_mul_responseScore_eq_linForm hS ν hF z,
    ← integral_mul_normalProj_sq_eq_biasForm hS ν (hCK hM) hF z]
  exact h F hF BF hBF M hM z hMz hz

variable {M : J → ℝ}

/-- The linear coefficient is bounded by the sup norm of the observable. -/
theorem abs_linForm_le_of_bound {F : X → ℝ} (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF)
    (u : J → ℝ) :
    |linForm hS ν M hF u| ≤
      BF * ∫ x, |responseScore hS ν M (dirProj S ν u) x| ∂(Pfam (θr M)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  rw [linForm_apply, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono ((integrable_of_bdd_prob _ (hF.mul (bdd_responseScore hS ν M _))).norm)
    ((integrable_of_bdd_prob _ (bdd_responseScore hS ν M _)).abs.const_mul _) fun x ↦ ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hBF x) (abs_nonneg _)

/-- The bias coefficient is bounded by the sup norm of the observable. -/
theorem abs_biasForm_le_of_bound
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {F : X → ℝ}
    (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) (u v : J → ℝ) :
    |biasForm hS ν M hF u v| ≤ BF * ∫ x, |normalProj hS ν M
      ((bdd_responseScore hS ν M (dirProj S ν u)).mul (bdd_responseScore hS ν M (dirProj S ν v)))
        x| ∂(Pfam (θr M)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hN := bdd_normalProj hS ν (M := M)
    ((bdd_responseScore hS ν M (dirProj S ν u)).mul (bdd_responseScore hS ν M (dirProj S ν v)))
  rw [biasForm_apply, ← integral_mul_normalProj_comm hS ν hrel hF
    ((bdd_responseScore hS ν M (dirProj S ν u)).mul (bdd_responseScore hS ν M (dirProj S ν v))),
    ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono ((integrable_of_bdd_prob _ (hF.mul hN)).norm)
    ((integrable_of_bdd_prob _ hN).abs.const_mul _) fun x ↦ ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hBF x) (abs_nonneg _)

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X)
  [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hind : iIndepFun Xs P) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hXm hind hid hlaw

/-- **The reconstruction bias, uniformly over the unit ball of bounded observables**: on a
compact convex interior neighbourhood `C` of the data response,
`sup_{‖F‖∞ ≤ 1} |n (E Ĝ_{F,n} − G_F(M)) − ½ Σ_{a,b} Γ_{ab} b_F(e_a, e_b)| → 0`.
This is the dual form of the `L¹`-valued signed-measure bias of the reconstruction. -/
theorem reconstruction_bias_uniform_of_nhd [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {C : Set (J → ℝ)} [DecidablePred (· ∈ C)] (hC : IsCompact C) (hCc : Convex ℝ C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {r : ℝ} (hr : 0 < r)
    (hCnhd : ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - dataMoment D S‖ ≤ r → M' ∈ C) :
    ∀ η > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ {F : X → ℝ} (hF : Bdd F), (∀ x, |F x| ≤ 1) →
      |(n : ℝ) * ((∫ ω, plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) ∂P) -
          obsResponse hS ν F (dataMoment D S)) -
        (1 / 2) * ∑ a, ∑ b,
          (∫ x, (S a x - dataMoment D S a) * (S b x - dataMoment D S b) ∂D) *
            biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b)| < η := by
  have hMmb := intrinsicInterior_subset hrel
  have hMC : dataMoment D S ∈ C := hCnhd _ hMmb (by simp [hr.le])
  have hB' : ∀ j, ∃ M, ∀ x, |S j x| ≤ M := fun j ↦ (hS j).2
  choose Bj hBj using hB'
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ j, |Bj j| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hBdef ▸ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hB : ∀ j x, |S j x| ≤ B := fun j x ↦
    (hBj j x).trans ((le_abs_self _).trans (hBdef ▸ Finset.single_le_sum (f := fun j ↦ |Bj j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)))
  obtain ⟨c, hc, htail⟩ := exists_tail_sampleResponse hS P D Xs hXm hid hlaw hind
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ a, ∫ x, (S a x - dataMoment D S a) ^ 2 ∂D := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hT ▸ Finset.sum_nonneg fun a _ ↦ integral_nonneg fun x ↦ sq_nonneg _
  -- observable-free constants
  obtain ⟨AL, hAL⟩ : ∃ AL : ℝ, AL = ∑ a, ∫ x, |responseScore hS ν (dataMoment D S)
    (dirProj S ν (coordUnit a)) x| ∂(Pfam (θr (dataMoment D S))) := ⟨_, rfl⟩
  obtain ⟨AB, hAB⟩ : ∃ AB : ℝ, AB = ∑ a, ∑ b, ∫ x, |normalProj hS ν (dataMoment D S)
    ((bdd_responseScore hS ν (dataMoment D S) (dirProj S ν (coordUnit a))).mul
      (bdd_responseScore hS ν (dataMoment D S) (dirProj S ν (coordUnit b)))) x|
    ∂(Pfam (θr (dataMoment D S))) := ⟨_, rfl⟩
  have hAL0 : 0 ≤ AL := hAL ▸ Finset.sum_nonneg fun a _ ↦ integral_nonneg fun x ↦ abs_nonneg _
  have hAB0 : 0 ≤ AB := hAB ▸ Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦
    integral_nonneg fun x ↦ abs_nonneg _
  obtain ⟨KK, hKK⟩ : ∃ KK : ℝ, KK = 2 * 1 + 2 * B * AL + (1 / 2) * (4 * B ^ 2 * AB) := ⟨_, rfl⟩
  have hKK0 : 0 ≤ KK := by rw [hKK]; positivity
  intro η hη
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = η / (2 * (T + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ by positivity
  obtain ⟨δ, hδ, hpe⟩ := integral_response_peano_biasForm_all hS ν hC hCc hCK ε hε0
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
  refine ⟨max N 1, fun n hn F hF hBF ↦ ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hcore := reconstruction_bias_core hS ν P D Xs hXm hind hid hlaw hDν hrel hF hBF hB0 hB hC
    hCK hr hCnhd hε0.le hδ (fun z hz hz' ↦ hpe hF hBF _ hMC z hz hz') hn1
  rw [← hT, ← hδ'] at hcore
  have htail' := htail n hn1 δ' hδ'0
  have hN' := hN n hnN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hN'
  -- the observable's constant is dominated by the observable-free constant
  have hKF : 2 * 1 + 2 * B * (∑ a, |linForm hS ν (dataMoment D S) hF (coordUnit a)|) +
      (1 / 2) * (4 * B ^ 2 * ∑ a, ∑ b,
        |biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b)|) ≤ KK := by
    rw [hKK]
    have h1 : ∑ a, |linForm hS ν (dataMoment D S) hF (coordUnit a)| ≤ AL := by
      rw [hAL]
      refine Finset.sum_le_sum fun a _ ↦ ?_
      have := abs_linForm_le_of_bound hS ν (M := dataMoment D S) hF hBF (coordUnit a)
      rwa [one_mul] at this
    have h2 : ∑ a, ∑ b, |biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b)| ≤ AB := by
      rw [hAB]
      refine Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ ?_
      have := abs_biasForm_le_of_bound hS ν hrel hF hBF (coordUnit a) (coordUnit b)
      rwa [one_mul] at this
    have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
    nlinarith
  have hεT : 1 * ε * T ≤ η / 2 := by
    rw [hε, one_mul, show η / (2 * (T + 1)) * T = η / 2 * (T / (T + 1)) by field_simp]
    exact mul_le_of_le_one_right (by positivity)
      (div_le_one_of_le₀ (by linarith) (by positivity))
  have hP0 : 0 ≤ P.real {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} :=
    measureReal_nonneg
  calc _ ≤ 1 * ε * T + (n : ℝ) * (2 * 1 + 2 * B *
        (∑ a, |linForm hS ν (dataMoment D S) hF (coordUnit a)|) +
        (1 / 2) * (4 * B ^ 2 * ∑ a, ∑ b,
          |biasForm hS ν (dataMoment D S) hF (coordUnit a) (coordUnit b)|)) *
        P.real {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} := hcore
    _ ≤ 1 * ε * T + (n : ℝ) * KK *
        P.real {ω | δ' < ‖fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D‖} := by
        gcongr
    _ ≤ 1 * ε * T + (n : ℝ) * KK * (2 * Fintype.card J * Real.exp (-(c * n * δ' ^ 2))) := by
        gcongr
    _ < η := by nlinarith

end Assembly

end Laplace.Multi
