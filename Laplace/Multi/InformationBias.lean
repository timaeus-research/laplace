/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PlugInBias
import Laplace.Multi.InformationTaylor

/-!
# The bias of the empirical visible information

Applying the plug-in bias schema to the visible information `𝓘(M) = KL(Π(M) ‖ ν)`, whose
expansion at the data response is `𝓘(M + h) = 𝓘(M) − ⟨h, θ(M)⟩ + ½ g_M(h, h) + o(‖h‖²)`, gives the
**information-bias theorem**: the truncated plug-in `𝓘̃_n = 𝓘(M̂_n)` satisfies

  `n (E 𝓘̃_n − 𝓘(M)) → ½ Σ_{a,b} Γ_{ab} g_M(e_a, e_b) = ½ E_D[g_M(S − M, S − M)]`

(`information_bias_tendsto`): the expected excess visible information of a sample of size `n` is
half the Fisher-quadratic mean of the centred features under the data law, divided by `n`. This is
an observable-free calibration of reconstruction complexity, `½ tr(Γ H_M)` in matrix terms.
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

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The visible information is continuous on interior subsets of the moment body. -/
theorem continuousOn_toReal_genRate {C : Set (J → ℝ)}
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ContinuousOn (fun M' ↦ (genRate ν S M').toReal) C := by
  have hCm : C ⊆ momentBody ν (fun _ ↦ (1 : ℝ)) S := hCK.trans intrinsicInterior_subset
  obtain ⟨M, hMdef⟩ : ∃ M : J → ℝ, M = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 :=
    ⟨_, rfl⟩
  have hfix : ∀ M' ∈ C, M + ((dirProj S ν (M' - M) : 𝕍) : J → ℝ) = M' := fun M' hM' ↦ by
    have hmem : M' - M ∈ 𝕍 := hMdef ▸ sub_mem_dirSpan_of_mem_momentBody measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (hCm hM')
    rw [show dirProj S ν (M' - M) = ⟨M' - M, hmem⟩ from dirProj_coe S ν ⟨M' - M, hmem⟩]
    simp
  have hI : ContinuousOn (fun w : 𝕍 ↦ (genRate ν S (M + (w : J → ℝ))).toReal)
      ((fun M' ↦ dirProj S ν (M' - M)) '' C) := by
    subst hMdef
    intro z hz
    obtain ⟨M', hM', rfl⟩ := hz
    exact (hasFDerivAt_rate_add hS ν ((hfix M' hM').symm ▸ hCK hM')).continuousAt.continuousWithinAt
  have hπ : Continuous fun M' : J → ℝ ↦ dirProj S ν (M' - M) :=
    (LinearMap.continuous_of_finiteDimensional _).comp (continuous_id.sub continuous_const)
  refine (hI.comp hπ.continuousOn (mapsTo_image _ _)).congr fun M' hM' ↦ ?_
  simp only [Function.comp_def, hfix M' hM']

/-- The gradient of the visible information as a linear functional on the coordinate space,
`u ↦ −⟨u, θ(M)⟩`. -/
noncomputable def rateGrad (M : J → ℝ) : (J → ℝ) →ₗ[ℝ] ℝ :=
  -((dotCLM (θr M : J → ℝ) : (J → ℝ) →L[ℝ] ℝ) : (J → ℝ) →ₗ[ℝ] ℝ)

theorem rateGrad_apply (M u : J → ℝ) : rateGrad hS ν M u = -dotJ u (θr M : J → ℝ) := by
  simp [rateGrad, dotCLM_apply]

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X)
  [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hind : iIndepFun Xs P) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hXm hind hid hlaw

/-- **The information-bias theorem on a given neighbourhood**:
`n (E 𝓘̃_n − 𝓘(M)) → ½ Σ_{a,b} Γ_{ab} g_M(e_a, e_b)`. -/
theorem information_bias_tendsto_of_nhd [DecidableEq J] (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {C : Set (J → ℝ)} [DecidablePred (· ∈ C)] (hC : IsCompact C) (hCc : Convex ℝ C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {r : ℝ} (hr : 0 < r)
    (hCnhd : ∀ M' ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, ‖M' - dataMoment D S‖ ≤ r → M' ∈ C) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
        ((∫ ω, plugInGen (fun M' ↦ (genRate ν S M').toReal) C (dataMoment D S)
            (sampleResponse S Xs n ω) ∂P) - (genRate ν S (dataMoment D S)).toReal)) atTop
      (𝓝 ((1 / 2) * ∑ a, ∑ c,
        (∫ x, (S a x - dataMoment D S a) * (S c x - dataMoment D S c) ∂D) *
          fisherAmb hS ν (dataMoment D S) (coordUnit a) (coordUnit c))) := by
  have hMC : dataMoment D S ∈ C := hCnhd _ (intrinsicInterior_subset hrel) (by simp [hr.le])
  refine plugInGen_bias_tendsto_of_nhd hS ν P D Xs hXm hind hid hlaw hDν hrel
    (L := rateGrad hS ν (dataMoment D S)) hC (continuousOn_toReal_genRate hS ν hCK) hr hCnhd ?_
  intro ε hε
  obtain ⟨δ, hδ, hpe⟩ := rate_peano_at hS ν hC hCc hCK hMC ε hε
  refine ⟨δ, hδ, fun z hz hzδ ↦ ?_⟩
  have h := hpe z hz hzδ
  rw [rateGrad_apply]
  have e : (genRate ν S (dataMoment D S + z)).toReal - (genRate ν S (dataMoment D S)).toReal -
      -dotJ (z : J → ℝ) (θr (dataMoment D S) : J → ℝ) -
      1 / 2 * fisherAmb hS ν (dataMoment D S) (z : J → ℝ) (z : J → ℝ) =
      (genRate ν S (dataMoment D S + z)).toReal - (genRate ν S (dataMoment D S)).toReal +
      dotJ (z : J → ℝ) (θr (dataMoment D S) : J → ℝ) -
      1 / 2 * fisherAmb hS ν (dataMoment D S) (z : J → ℝ) (z : J → ℝ) := by ring
  rw [e]
  exact h

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure P] hXm hind hid hlaw in
/-- For any bilinear form, `Σ_{a,b} Γ_{ab} b(e_a, e_b) = E_D[b(S − M, S − M)]`. -/
theorem sum_dataCov_mul_bilinear_eq_integral [DecidableEq J]
    (b : (J → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ) :
    ∑ a, ∑ c, (∫ x, (S a x - dataMoment D S a) * (S c x - dataMoment D S c) ∂D) *
        b (coordUnit a) (coordUnit c) =
      ∫ x, b (fun j ↦ S j x - dataMoment D S j) (fun j ↦ S j x - dataMoment D S j) ∂D := by
  have hbsum : ∀ u : J → ℝ, b u u = ∑ a, ∑ c, u a * u c * b (coordUnit a) (coordUnit c) := by
    intro u
    rw [linearMap_eq_sum_coordUnit (b u) u, LinearMap.pi_apply_eq_sum_univ b u]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    change u c * (u a * b (coordUnit a) (coordUnit c)) = _
    ring
  have hint : ∀ a c, Integrable (fun x ↦ (S a x - dataMoment D S a) * (S c x - dataMoment D S c) *
      b (coordUnit a) (coordUnit c)) D := fun a c ↦
    (integrable_of_bdd_prob _ (((hS a).sub (Bdd.const _)).mul ((hS c).sub (Bdd.const _)))).mul_const
      _
  rw [show (fun x ↦ b (fun j ↦ S j x - dataMoment D S j) (fun j ↦ S j x - dataMoment D S j)) =
      fun x ↦ ∑ a, ∑ c, (S a x - dataMoment D S a) * (S c x - dataMoment D S c) *
        b (coordUnit a) (coordUnit c) from funext fun x ↦ hbsum _]
  rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun c _ ↦ hint a c]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [integral_finsetSum _ fun c _ ↦ hint a c]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [integral_mul_const]

/-- **The information-bias theorem.** For i.i.d. samples of `D ≪ ν` with interior response
`M = E_D S`, there is a compact convex interior neighbourhood `C` of `M` such that the truncated
plug-in visible information `𝓘̃_n = 𝓘(M̂_n)` (fallback `𝓘(M)` off `C`) satisfies
`n (E 𝓘̃_n − 𝓘(M)) → ½ E_D[g_M(S − M, S − M)]`: the expected excess visible information of a
sample is half the Fisher-quadratic mean of the centred features, divided by `n`. -/
theorem information_bias_tendsto (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∃ C : Set (J → ℝ), IsCompact C ∧ Convex ℝ C ∧
      C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) ∧ dataMoment D S ∈ C ∧
      ∀ [DecidablePred (· ∈ C)], Tendsto (fun n : ℕ ↦ (n : ℝ) *
        ((∫ ω, plugInGen (fun M' ↦ (genRate ν S M').toReal) C (dataMoment D S)
            (sampleResponse S Xs n ω) ∂P) - (genRate ν S (dataMoment D S)).toReal)) atTop
        (𝓝 ((1 / 2) * ∫ x, fisherAmb hS ν (dataMoment D S) (fun j ↦ S j x - dataMoment D S j)
          (fun j ↦ S j x - dataMoment D S j) ∂D)) := by
  obtain ⟨r, hr, C, hC, hCc, hCK, hCnhd⟩ := exists_compact_convex_nhd hS ν hrel
  have hMC : dataMoment D S ∈ C := hCnhd _ (intrinsicInterior_subset hrel) (by simp [hr.le])
  refine ⟨C, hC, hCc, hCK, hMC, ?_⟩
  intro _
  classical
  rw [← sum_dataCov_mul_bilinear_eq_integral hS D (fisherAmb hS ν (dataMoment D S))]
  exact information_bias_tendsto_of_nhd hS ν P D Xs hXm hind hid hlaw hDν hrel hC hCc hCK hr hCnhd

end Assembly

end Laplace.Multi
