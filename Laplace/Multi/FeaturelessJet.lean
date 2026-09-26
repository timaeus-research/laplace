/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AtlasJetL1

/-!
# The featureless jets: the reconstruction's Taylor coefficients at maximal entropy

At the featureless law the reconstruction curve `p(s) = [q_{M_s}]` along the atlas has
`p(0) = [1]`, `p'(0) = [ℓ]` and `p''(0) = [N(ℓ²)]`, where `ℓ = ℓ_{m₀, M−m₀}` is the tangent score of
the data displacement under `ν` and `N = N_{m₀}` the normal projection at the reference
(`reconstructionL1_atlas_zero`, `iteratedDeriv_one_reconstructionL1_atlas_zero`,
`iteratedDeriv_two_reconstructionL1_atlas_zero`). The second jet is identified by uniqueness of
Peano coefficients: the total-variation Peano expansion of the density gives the observable-level
expansion with coefficients `lin_F` and `b_F`, while Taylor's theorem for the smooth curve gives it
with the iterated derivatives. Consequently the response of every bounded observable has the
explicit second-order featureless expansion
`E_{Q_{M_s}}F = E_ν F + s E_ν[Fℓ] + ½ s² E_ν[(N F) ℓ²] + O(‖F‖∞ s³)`
(`obsResponse_atlas_second_order_featureless`), with a constant independent of `F`.
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ContDiff

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

omit [Nonempty X] [Nonempty J] hS in
/-- **Uniqueness of Peano coefficients**: if `a s + b s² = o(s²)` as `s → 0⁺` then `a = b = 0`. -/
theorem eq_zero_of_isLittleO_sq {a b : ℝ}
    (h : (fun s : ℝ ↦ a * s + b * s ^ 2) =o[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s ^ 2) :
    a = 0 ∧ b = 0 := by
  have hne : NeBot (𝓝[Ioo (0 : ℝ) 1] 0) := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo zero_ne_one]
    exact left_mem_Icc.2 zero_le_one
  -- divide by `s`: `a + b s → 0`
  have h1 : (fun s : ℝ ↦ a * s + b * s ^ 2) =o[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s := by
    refine h.trans_isBigO (IsBigO.of_bound 1 ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs.1, abs_of_pos (pow_pos hs.1 2), one_mul]
    nlinarith [hs.1, hs.2]
  have h2 := h1.tendsto_div_nhds_zero
  have h3 : Tendsto (fun s : ℝ ↦ (a * s + b * s ^ 2) / s) (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 a) := by
    have e : ∀ s ∈ Ioo (0 : ℝ) 1, (a * s + b * s ^ 2) / s = a + b * s := fun s hs ↦ by
      field_simp [hs.1.ne']
    refine (Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn e).symm ?_)
    have : Tendsto (fun s : ℝ ↦ a + b * s) (𝓝 0) (𝓝 (a + b * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    rw [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have ha : a = 0 := (tendsto_nhds_unique h3 h2).symm ▸ rfl
  subst ha
  -- now `b s² = o(s²)` gives `b = 0`
  have h4 := h.tendsto_div_nhds_zero
  have h5 : Tendsto (fun s : ℝ ↦ (0 * s + b * s ^ 2) / s ^ 2) (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 b) := by
    have e : ∀ s ∈ Ioo (0 : ℝ) 1, (0 * s + b * s ^ 2) / s ^ 2 = b := fun s hs ↦ by
      field_simp [hs.1.ne']
      ring
    exact (tendsto_const_nhds.congr' (eventuallyEq_nhdsWithin_of_eqOn e).symm)
  exact ⟨rfl, (tendsto_nhds_unique h5 h4)⟩

/-- The featureless density is `1`. -/
theorem famDens_featureless (x : X) : famDens S ν (θr m₀) x = 1 := by
  rw [responseTheta_featureless hS ν, Submodule.coe_zero]
  simp [famDens, famWeight, famZ, dirLoss]

/-- **`p(0) = [1]`**: the reconstruction of the featureless response is the reference law. -/
theorem reconstructionL1_featureless :
    reconstructionL1 hS ν m₀ = (integrable_const (1 : ℝ)).toL1 (fun _ ↦ 1) := by
  unfold reconstructionL1
  rw [Integrable.toL1_eq_toL1_iff]
  exact Eventually.of_forall fun x ↦ famDens_featureless hS ν x

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- The reconstruction curve along the atlas. -/
local notation "p" => fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)

/-- The atlas increment `M − m₀ ∈ 𝕍`. -/
local notation "δ" => atlasInc hS ν (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel)

omit hrel in
/-- The pairing of the zeroth featureless jet: `∫ F p(0) = E_ν F`. -/
theorem integral_mul_iteratedDeriv_zero_atlas_zero {F : X → ℝ} (hF : Bdd F) :
    ∫ x, F x * (iteratedDeriv 0 p 0) x ∂ν = obsResponse hS ν F m₀ := by
  rw [iteratedDeriv_zero, ← obsL1_apply ν hF, obsL1_reconstructionL1 hS ν hF, atlasPath_zero]

/-- **`p'(0) = [ℓ]`**: the first featureless jet is the tangent score of the displacement. -/
theorem iteratedDeriv_one_reconstructionL1_atlas_zero :
    iteratedDeriv 1 p 0 =
      (integrable_of_bdd_prob ν (bdd_responseScore hS ν m₀ δ)).toL1 (responseScore hS ν m₀ δ) := by
  have h0 : (0 : ℝ) ∈ atlasDomain S ν M :=
    Icc_subset_atlasDomain hS ν hrel (left_mem_Icc.2 zero_le_one)
  rw [iteratedDeriv_one_reconstructionL1_atlas hS ν
    (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel) h0, atlasPath_zero,
    reconstructionDeriv_apply, Integrable.toL1_eq_toL1_iff]
  refine Eventually.of_forall fun x ↦ ?_
  beta_reduce
  rw [famDens_featureless hS ν x, one_mul]

/-- The pairing of the first featureless jet: `∫ F p'(0) = lin_{F,m₀}(M − m₀)`. -/
theorem integral_mul_iteratedDeriv_one_atlas_zero {F : X → ℝ} (hF : Bdd F) :
    ∫ x, F x * (iteratedDeriv 1 p 0) x ∂ν = linForm hS ν m₀ hF (M - m₀) := by
  rw [iteratedDeriv_one_reconstructionL1_atlas_zero hS ν hrel]
  have hl := integral_mul_responseScore_eq_linForm hS ν (M := m₀) hF δ
  rw [atlasInc_coe, familyMeasure_responseTheta_featureless hS ν] at hl
  rw [← hl]
  refine integral_congr_ae ?_
  filter_upwards [Integrable.coeFn_toL1 (integrable_of_bdd_prob ν (bdd_responseScore hS ν m₀ δ))]
    with x hx
  rw [hx]

/-- The observable-level Peano expansion at the featureless law along the atlas:
`E_{Q_{M_s}}F − E_ν F − s lin_F(δ) − ½ s² b_F(δ,δ) = o(s²)`. -/
theorem isLittleO_obsResponse_atlas_zero {F : X → ℝ} (hF : Bdd F) :
    (fun s : ℝ ↦ obsResponse hS ν F (atlasPath S ν M s) - obsResponse hS ν F m₀ -
      s * linForm hS ν m₀ hF (M - m₀) -
      (1 / 2) * (s ^ 2 * biasForm hS ν m₀ hF (M - m₀) (M - m₀)))
      =o[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s ^ 2 := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  have hrel₀ := featureless_mem_intrinsicInterior hS ν
  obtain ⟨BF, hBF⟩ := hF.2
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := m₀)
  -- the density-level Peano expansion, composed with `z = s • δ`
  have hz : Tendsto (fun s : ℝ ↦ s • δ) (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ ↦ s • δ) (𝓝 0) (𝓝 ((0 : ℝ) • δ)) := tendsto_id.smul_const _
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hd := (isLittleO_integral_famDens_response_peano hS ν hrel₀).comp_tendsto hz
  have hnorm : (fun s : ℝ ↦ ‖s • δ‖ ^ 2) =O[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s ^ 2 := by
    refine IsBigO.of_bound (‖δ‖ ^ 2) (Eventually.of_forall fun s ↦ ?_)
    have e : ‖s • δ‖ ^ 2 = ‖δ‖ ^ 2 * s ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
  refine IsBigO.trans_isLittleO (IsBigO.of_bound BF ?_) (hd.trans_isBigO hnorm)
  filter_upwards [self_mem_nhdsWithin] with s _
  -- identify the pointwise expression with the pairing of the density remainder
  have hb := (bdd_responseScore hS ν m₀ (s • δ)).mul (bdd_responseScore hS ν m₀ (s • δ))
  have hint1 := integrable_famDens hS ν (θr (m₀ + (s • δ : 𝕍)))
  have hint2 : Integrable (fun x ↦ famDens S ν (θr m₀) x *
      (1 + responseScore hS ν m₀ (s • δ) x + (1 / 2) * normalProj hS ν m₀ hb x)) ν :=
    integrable_famDens_mul_of_bdd hS ν
      (((Bdd.const 1).add (bdd_responseScore hS ν m₀ _)).add
        (Bdd.const_mul (1 / 2) (bdd_normalProj hS ν hb)))
  have hr : Integrable (fun x ↦ famDens S ν (θr (m₀ + (s • δ : 𝕍))) x -
      famDens S ν (θr m₀) x *
        (1 + responseScore hS ν m₀ (s • δ) x + (1 / 2) * normalProj hS ν m₀ hb x)) ν :=
    hint1.sub hint2
  have e1 : atlasPath S ν M s = m₀ + ((s • δ : 𝕍) : J → ℝ) :=
    atlasPath_eq_add_smul_atlasInc hS ν hfin s
  have e2 : obsResponse hS ν F (atlasPath S ν M s) - obsResponse hS ν F m₀ -
      s * linForm hS ν m₀ hF (M - m₀) -
      (1 / 2) * (s ^ 2 * biasForm hS ν m₀ hF (M - m₀) (M - m₀)) =
      ∫ x, F x * (famDens S ν (θr (m₀ + (s • δ : 𝕍))) x -
        famDens S ν (θr m₀) x * (1 + responseScore hS ν m₀ (s • δ) x +
          (1 / 2) * normalProj hS ν m₀ hb x)) ∂ν := by
    have l1 : s * linForm hS ν m₀ hF (M - m₀) =
        ∫ x, F x * responseScore hS ν m₀ (s • δ) x ∂(Pfam (θr m₀)) := by
      rw [integral_mul_responseScore_eq_linForm hS ν hF, Submodule.coe_smul, atlasInc_coe,
        map_smul, smul_eq_mul]
    have l2 : s ^ 2 * biasForm hS ν m₀ hF (M - m₀) (M - m₀) =
        ∫ x, F x * normalProj hS ν m₀ hb x ∂(Pfam (θr m₀)) := by
      rw [integral_mul_normalProj_sq_eq_biasForm hS ν hrel₀ hF, Submodule.coe_smul, atlasInc_coe,
        LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, sq]
      ring
    rw [l1, l2]
    unfold obsResponse
    rw [e1, integral_famDens_mul hS ν, integral_famDens_mul hS ν, integral_famDens_mul hS ν,
      integral_famDens_mul hS ν]
    have hA : Integrable (fun x ↦ famDens S ν (θr (m₀ + (s • δ : 𝕍))) x * F x) ν :=
      integrable_famDens_mul_of_bdd hS ν hF
    have hB : Integrable (fun x ↦ famDens S ν (θr m₀) x * F x) ν :=
      integrable_famDens_mul_of_bdd hS ν hF
    have hC : Integrable (fun x ↦ famDens S ν (θr m₀) x *
        (F x * responseScore hS ν m₀ (s • δ) x)) ν :=
      integrable_famDens_mul_of_bdd hS ν (hF.mul (bdd_responseScore hS ν m₀ _))
    have hD : Integrable (fun x ↦ famDens S ν (θr m₀) x * (F x * normalProj hS ν m₀ hb x)) ν :=
      integrable_famDens_mul_of_bdd hS ν (hF.mul (bdd_normalProj hS ν hb))
    have hAB : Integrable (fun x ↦ famDens S ν (θr (m₀ + (s • δ : 𝕍))) x * F x -
        famDens S ν (θr m₀) x * F x) ν := hA.sub hB
    have hABC : Integrable (fun x ↦ (famDens S ν (θr (m₀ + (s • δ : 𝕍))) x * F x -
        famDens S ν (θr m₀) x * F x) -
        famDens S ν (θr m₀) x * (F x * responseScore hS ν m₀ (s • δ) x)) ν := hAB.sub hC
    have hD' : Integrable (fun x ↦ (1 / 2) *
        (famDens S ν (θr m₀) x * (F x * normalProj hS ν m₀ hb x))) ν := hD.const_mul _
    rw [← integral_sub hA hB, ← integral_sub hAB hC, ← integral_const_mul, ← integral_sub hABC hD']
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    ring
  rw [e2, Function.comp_apply, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg _)]
  have hFr : Integrable (fun x ↦ F x * (famDens S ν (θr (m₀ + (s • δ : 𝕍))) x -
      famDens S ν (θr m₀) x *
        (1 + responseScore hS ν m₀ (s • δ) x + (1 / 2) * normalProj hS ν m₀ hb x))) ν :=
    hr.bdd_mul hF.1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hBF x)
  calc _ ≤ ∫ x, |F x * (famDens S ν (θr (m₀ + (s • δ : 𝕍))) x -
      famDens S ν (θr m₀) x *
        (1 + responseScore hS ν m₀ (s • δ) x + (1 / 2) * normalProj hS ν m₀ hb x))| ∂ν :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, BF * |famDens S ν (θr (m₀ + (s • δ : 𝕍))) x -
      famDens S ν (θr m₀) x *
        (1 + responseScore hS ν m₀ (s • δ) x + (1 / 2) * normalProj hS ν m₀ hb x)| ∂ν := by
        refine integral_mono hFr.abs (hr.abs.const_mul BF) fun x ↦ ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hBF x) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The Taylor expansion of the observable response at the featureless law:
`E_{Q_{M_s}}F − Σ_{k≤2} s^k/k! ∫ F p^{(k)}(0) = o(s²)`. -/
theorem isLittleO_obsResponse_atlas_taylor_two {F : X → ℝ} (hF : Bdd F) :
    (fun s : ℝ ↦ obsResponse hS ν F (atlasPath S ν M s) -
      ∑ k ∈ Finset.range 3, ((k.factorial : ℝ)⁻¹ * s ^ k) * ∫ x, F x * (iteratedDeriv k p 0) x ∂ν)
      =o[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s ^ 2 := by
  have hf : ContDiffOn ℝ (2 : ℕ) p (Icc (0 : ℝ) 1) :=
    (contDiffOn_reconstructionL1_atlas_Icc hS ν hrel).of_le (natCast_le_infty 2)
  have h := taylor_isLittleO (convex_Icc (0 : ℝ) 1) (left_mem_Icc.2 zero_le_one) hf
  simp only [sub_zero] at h
  have h' := h.mono (nhdsWithin_mono _ Ioo_subset_Icc_self)
  -- pair with the observable
  have hL := ((obsL1 ν hF).isBigO_comp _ _).trans_isLittleO h'
  refine hL.congr_left fun s ↦ ?_
  simp only [map_sub, obsL1_reconstructionL1 hS ν hF,
    taylorWithinEval_reconstructionL1_atlas hS ν hrel, map_sum, map_smul, smul_eq_mul, obsL1_apply]

/-- The pairing of the second featureless jet: `∫ F p''(0) = b_{F,m₀}(M − m₀, M − m₀)`, by
uniqueness of Peano coefficients. -/
theorem integral_mul_iteratedDeriv_two_atlas_zero {F : X → ℝ} (hF : Bdd F) :
    ∫ x, F x * (iteratedDeriv 2 p 0) x ∂ν = biasForm hS ν m₀ hF (M - m₀) (M - m₀) := by
  have hA := isLittleO_obsResponse_atlas_zero hS ν hrel hF
  have hB := isLittleO_obsResponse_atlas_taylor_two hS ν hrel hF
  have hc0 := integral_mul_iteratedDeriv_zero_atlas_zero hS ν (M := M) hF
  have hc1 := integral_mul_iteratedDeriv_one_atlas_zero hS ν hrel hF
  have hdiff : (fun s : ℝ ↦ 0 * s + ((1 / 2) * (biasForm hS ν m₀ hF (M - m₀) (M - m₀) -
      ∫ x, F x * (iteratedDeriv 2 p 0) x ∂ν)) * s ^ 2) =o[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s ^ 2 := by
    refine (hB.sub hA).congr_left fun s ↦ ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc0, hc1, Nat.factorial]
    push_cast
    ring
  obtain ⟨-, hb⟩ := eq_zero_of_isLittleO_sq hdiff
  linarith

/-- **`p''(0) = [N(ℓ²)]`**: the second featureless jet is the normal projection of the squared
tangent score (the density acceleration at the reference). -/
theorem iteratedDeriv_two_reconstructionL1_atlas_zero :
    iteratedDeriv 2 p 0 =
      ((integrable_famDens_mul_of_bdd hS ν (M := atlasPath S ν M 0)
          (bdd_normalProj hS ν (bdd_atlasScore_sq hS ν
            (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel) (s := 0)))).congr
        (Eventually.of_forall fun x ↦ (atlasHess_eq_normalProj hS ν
          (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel) hrel le_rfl zero_le_one x).symm)).toL1
        (atlasHess hS ν (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel) hrel le_rfl
          zero_le_one) := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  refine L1_ext_of_forall_integral_mul ν _ _ fun F hF ↦ ?_
  have hh := integral_mul_atlasHess_eq_biasForm hS ν hfin hrel le_rfl zero_le_one hF
  rw [atlasPath_zero] at hh
  rw [integral_mul_iteratedDeriv_two_atlas_zero hS ν hrel hF, ← hh]
  refine integral_congr_ae ?_
  filter_upwards [Integrable.coeFn_toL1 ((integrable_famDens_mul_of_bdd hS ν
    (M := atlasPath S ν M 0) (bdd_normalProj hS ν (bdd_atlasScore_sq hS ν hfin (s := 0)))).congr
      (Eventually.of_forall fun x ↦
        (atlasHess_eq_normalProj hS ν hfin hrel le_rfl zero_le_one x).symm))] with x hx
  rw [hx]

/-- **The second-order featureless expansion of the response map**: for every bounded `F`,
`|E_{Q_{M_s}}F − (E_ν F + s lin_{F,m₀}(δ) + ½ s² b_{F,m₀}(δ,δ))| ≤ ‖F‖∞ · C s³/2` on `[0,1]`,
with `C` independent of `F`. -/
theorem obsResponse_atlas_second_order_featureless : ∃ C : ℝ, 0 ≤ C ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ {F : X → ℝ} (hF : Bdd F) {BF : ℝ}, (∀ x, |F x| ≤ BF) →
      |obsResponse hS ν F (atlasPath S ν M s) -
          ((∫ x, F x ∂ν) + s * linForm hS ν m₀ hF (M - m₀) +
            (1 / 2) * s ^ 2 * biasForm hS ν m₀ hF (M - m₀) (M - m₀))| ≤
        BF * (C * s ^ 3 / 2) := by
  obtain ⟨C, hC0, hC⟩ := obsResponse_atlas_taylor hS ν hrel 2
  refine ⟨C, hC0, fun s hs F hF BF hBF ↦ ?_⟩
  have h := hC s hs hF hBF
  have hc0 := integral_mul_iteratedDeriv_zero_atlas_zero hS ν (M := M) hF
  have hc1 := integral_mul_iteratedDeriv_one_atlas_zero hS ν hrel hF
  have hc2 := integral_mul_iteratedDeriv_two_atlas_zero hS ν hrel hF
  have hm : obsResponse hS ν F m₀ = ∫ x, F x ∂ν := by
    unfold obsResponse
    rw [familyMeasure_responseTheta_featureless hS ν]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc0, hc1, hc2, hm, Nat.factorial] at h
  push_cast at h
  have e : obsResponse hS ν F (atlasPath S ν M s) - ((∫ x, F x ∂ν) +
      s * linForm hS ν m₀ hF (M - m₀) + (1 / 2) * s ^ 2 * biasForm hS ν m₀ hF (M - m₀) (M - m₀)) =
      obsResponse hS ν F (atlasPath S ν M s) - (0 + (1 : ℝ)⁻¹ * s ^ 0 * (∫ x, F x ∂ν) +
        (1 : ℝ)⁻¹ * s ^ 1 * linForm hS ν m₀ hF (M - m₀) +
        (2 : ℝ)⁻¹ * s ^ 2 * biasForm hS ν m₀ hF (M - m₀) (M - m₀)) := by ring
  rw [e]
  refine h.trans (le_of_eq ?_)
  ring

end Laplace.Multi
