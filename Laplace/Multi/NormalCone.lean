/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.BoundaryEscape
import Laplace.Multi.VisibleBudget

/-!
# Escape directions are inward normals

Let `θ_n` be parameters with `‖θ_n‖ → ∞` whose responses `m(θ_n)` converge to `M`, and suppose the
normalised parameters `θ_n/‖θ_n‖` converge to `u`. Then `u` is an inward normal of the moment body
at `M`:

  `⟨u, M⟩ ≤ ⟨u, x⟩` for every `x` in the moment body          (`dotJ_sub_nonneg_of_escape`)

with the sign convention `P_θ ∝ e^{−⟨θ,S⟩} ν`. The proof is a Laplace-principle bound: the
nonnegativity of `KL(P_θ ‖ ν)` gives `⟨θ, m(θ)⟩ ≤ −log ∫ e^{−⟨θ,S⟩} dν`
(`dotJ_meanMap_le_neg_featCgf`), and for `θ = r w` with `w` close to `u`
`∫ e^{−r⟨w,S⟩} dν ≥ e^{−rδ} e^{−r(c+ε)} ν(⟨u,S⟩ < c + ε)`, so
`⟨w, m(rw)⟩ ≤ c + ε + δ − log ν(⟨u,S⟩ < c + ε)/r`; letting `r → ∞`, `δ → 0`, `ε → 0` gives
`⟨u, M⟩ ≤ c` for every `c` with `ν(⟨u,S⟩ < c + ε) > 0` for all `ε > 0` (`dotJ_le_of_escape`), and
the half-space lemma for the moment body turns this into the normal-cone statement.

Along the straight path of the atlas the escape is automatic at boundary responses
(`tendsto_norm_atlasTheta_atTop`), so every accumulation direction of the normalised natural
coordinates `θ(M_s)/‖θ(M_s)‖` as `s ↑ 1` is an inward normal at `M`
(`dotJ_le_of_tendsto_normalized_atlasTheta`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- `⟨θ, m(θ)⟩ ≤ −log ∫ e^{−⟨θ,S⟩} dν`: the nonnegativity of `KL(P_θ ‖ ν)`. -/
theorem dotJ_meanMap_le_neg_featCgf (θ : J → ℝ) :
    dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) ≤ -featCgf ν S (-θ) := by
  have h0 := famKL_nonneg (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ)) measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0)
    (fun _ ↦ by simp) hS one_pos θ 0
  rw [famKL_eq measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
    measurable_const (M₀ := 0) (fun _ ↦ by simp) hS, affLogZ_one_zero_eq_featCgf,
    affLogZ_one_zero_eq_featCgf, neg_zero, featCgf_zero'] at h0
  simp only [Pi.zero_apply, zero_sub, one_mul] at h0
  have : ∑ i, -θ i * meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ i =
      -dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) := by
    rw [dotJ, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  linarith

omit [Nonempty X] hS in
/-- **Laplace lower bound**: `e^{−rc} ν(g < c) ≤ ∫ e^{−r g} dν` for bounded measurable `g`,
`r ≥ 0`. -/
theorem exp_mul_real_le_integral_exp_neg {g : X → ℝ} (hg : Bdd g) {r c : ℝ} (hr : 0 ≤ r) :
    Real.exp (-(r * c)) * ν.real {x | g x < c} ≤ ∫ x, Real.exp (-(r * g x)) ∂ν := by
  have hA : MeasurableSet {x | g x < c} := measurableSet_lt hg.1 measurable_const
  have hint : Integrable (fun x ↦ Real.exp (-(r * g x))) ν :=
    (integrable_exp_mul_of_bdd ν hg (-r)).congr (Eventually.of_forall fun x ↦ by
      simp only [neg_mul])
  calc Real.exp (-(r * c)) * ν.real {x | g x < c}
      = ∫ x in {x | g x < c}, Real.exp (-(r * c)) ∂ν := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ x in {x | g x < c}, Real.exp (-(r * g x)) ∂ν := by
        refine setIntegral_mono_on (integrable_const _).integrableOn hint.integrableOn hA
          fun x hx ↦ ?_
        exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (le_of_lt hx) hr))
    _ ≤ ∫ x, Real.exp (-(r * g x)) ∂ν :=
        setIntegral_le_integral hint (Eventually.of_forall fun x ↦ (Real.exp_pos _).le)

omit [MeasurableSpace X] [Nonempty X] [IsProbabilityMeasure ν] hS in
theorem dirLoss_sub' (v w : J → ℝ) (x : X) :
    dirLoss S (v - w) x = dirLoss S v x - dirLoss S w x := by
  simp only [dirLoss, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

omit [Nonempty X] in
/-- The log-partition function along an almost-normalised direction: if
`⟨w,S⟩ ≤ ⟨u,S⟩ + δ` pointwise and `ν(⟨u,S⟩ < c) > 0`, then
`−rδ − rc + log ν(⟨u,S⟩ < c) ≤ log ∫ e^{−r⟨w,S⟩} dν`. -/
theorem featCgf_neg_smul_ge {w u : J → ℝ} {δ : ℝ} (hδ : ∀ x, dirLoss S w x ≤ dirLoss S u x + δ)
    {r c : ℝ} (hr : 0 ≤ r) (hp : 0 < ν.real {x | dirLoss S u x < c}) :
    -(r * δ) - r * c + Real.log (ν.real {x | dirLoss S u x < c}) ≤ featCgf ν S (-(r • w)) := by
  have hint_w : Integrable (fun x ↦ Real.exp (-(r * dirLoss S w x))) ν :=
    (integrable_exp_mul_of_bdd ν (bdd_dirLoss hS w) (-r)).congr
      (Eventually.of_forall fun x ↦ by simp only [neg_mul])
  have hint_u : Integrable (fun x ↦ Real.exp (-(r * δ)) * Real.exp (-(r * dirLoss S u x))) ν :=
    ((integrable_exp_mul_of_bdd ν (bdd_dirLoss hS u) (-r)).congr
      (Eventually.of_forall fun x ↦ by simp only [neg_mul])).const_mul _
  have h1 : Real.exp (-(r * δ)) * ∫ x, Real.exp (-(r * dirLoss S u x)) ∂ν ≤
      ∫ x, Real.exp (-(r * dirLoss S w x)) ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono hint_u hint_w fun x ↦ ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [hδ x])
  have h2 := exp_mul_real_le_integral_exp_neg ν (bdd_dirLoss hS u) (r := r) (c := c) hr
  have hpos : 0 < Real.exp (-(r * δ)) * (Real.exp (-(r * c)) * ν.real {x | dirLoss S u x < c}) :=
    mul_pos (Real.exp_pos _) (mul_pos (Real.exp_pos _) hp)
  have h3 : Real.exp (-(r * δ)) * (Real.exp (-(r * c)) * ν.real {x | dirLoss S u x < c}) ≤
      ∫ x, Real.exp (dirLoss S (-(r • w)) x) ∂ν := by
    refine le_trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) (h1.trans (le_of_eq ?_))
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [dirLoss_neg (S := S), dirLoss_smul]
  unfold featCgf
  have := Real.log_le_log hpos h3
  rw [Real.log_mul (Real.exp_pos _).ne' (mul_pos (Real.exp_pos _) hp).ne',
    Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp, Real.log_exp] at this
  linarith

/-- **Escape directions are inward normals** (general form): if `‖θ_n‖ → ∞`, `m(θ_n) → M` and
`θ_n/‖θ_n‖ → u`, then `⟨u, M⟩ ≤ c` for every `c` with `ν(⟨u,S⟩ < c + ε) > 0` for all `ε > 0`. -/
theorem dotJ_le_of_escape {θ : ℕ → J → ℝ} (hr : Tendsto (fun n ↦ ‖θ n‖) atTop atTop) {M : J → ℝ}
    (hm : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ n)) atTop (𝓝 M))
    {u : J → ℝ} (hu : Tendsto (fun n ↦ ‖θ n‖⁻¹ • θ n) atTop (𝓝 u))
    {c : ℝ} (hc : ∀ ε > 0, 0 < ν.real {x | dirLoss S u x < c + ε}) :
    dotJ u M ≤ c := by
  choose B hB using fun j ↦ (hS j).2
  have hpt : ∀ (v : J → ℝ) (x : X), |dirLoss S v x| ≤ ‖v‖ * ∑ j, B j := by
    intro v x
    calc |dirLoss S v x| = |∑ j, v j * S j x| := rfl
      _ ≤ ∑ j, |v j * S j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ‖v‖ * B j := Finset.sum_le_sum fun j _ ↦ by
          rw [abs_mul]
          exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v j) (hB j x)
            (abs_nonneg _) (norm_nonneg _)
      _ = ‖v‖ * ∑ j, B j := by rw [Finset.mul_sum]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hp := hc ε hε
  have hev : ∀ᶠ n in atTop, 0 < ‖θ n‖ := hr.eventually (eventually_gt_atTop 0)
  have key : ∀ n, 0 < ‖θ n‖ →
      dotJ (‖θ n‖⁻¹ • θ n) (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ n)) ≤
        c + ε + ‖‖θ n‖⁻¹ • θ n - u‖ * ∑ j, B j -
          Real.log (ν.real {x | dirLoss S u x < c + ε}) / ‖θ n‖ := by
    intro n hn
    have h1 := dotJ_meanMap_le_neg_featCgf hS ν (θ n)
    have hθ : θ n = ‖θ n‖ • (‖θ n‖⁻¹ • θ n) := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hδ : ∀ x, dirLoss S (‖θ n‖⁻¹ • θ n) x ≤
        dirLoss S u x + ‖‖θ n‖⁻¹ • θ n - u‖ * ∑ j, B j := by
      intro x
      have := (abs_le.1 (hpt (‖θ n‖⁻¹ • θ n - u) x)).2
      rw [dirLoss_sub'] at this
      linarith
    have h2 := featCgf_neg_smul_ge hS ν hδ (r := ‖θ n‖) (c := c + ε) hn.le hp
    rw [← hθ] at h2
    rw [dotJ_smul_left, inv_mul_le_iff₀ hn]
    have e : ‖θ n‖ * (c + ε + ‖‖θ n‖⁻¹ • θ n - u‖ * ∑ j, B j -
        Real.log (ν.real {x | dirLoss S u x < c + ε}) / ‖θ n‖) =
        ‖θ n‖ * (c + ε) + ‖θ n‖ * (‖‖θ n‖⁻¹ • θ n - u‖ * ∑ j, B j) -
          Real.log (ν.real {x | dirLoss S u x < c + ε}) := by
      field_simp
    rw [e]
    linarith
  have hL : Tendsto (fun n ↦ dotJ (‖θ n‖⁻¹ • θ n)
      (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ n))) atTop (𝓝 (dotJ u M)) :=
    tendsto_finsetSum Finset.univ fun j _ ↦ (tendsto_pi_nhds.1 hu j).mul (tendsto_pi_nhds.1 hm j)
  have hδ0 : Tendsto (fun n ↦ ‖‖θ n‖⁻¹ • θ n - u‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hu
  have hlog : Tendsto (fun n ↦ Real.log (ν.real {x | dirLoss S u x < c + ε}) / ‖θ n‖) atTop
      (𝓝 0) := tendsto_const_nhds.div_atTop hr
  have hR := ((tendsto_const_nhds (x := c + ε)).add (hδ0.mul_const (∑ j, B j))).sub hlog
  have := le_of_tendsto_of_tendsto hL hR (hev.mono key)
  simpa using this

/-- **Escape directions are inward normals of the moment body**: under the hypotheses of
`dotJ_le_of_escape`, `⟨u, x − M⟩ ≥ 0` for every `x` in the moment body. -/
theorem dotJ_sub_nonneg_of_escape {θ : ℕ → J → ℝ} (hr : Tendsto (fun n ↦ ‖θ n‖) atTop atTop)
    {M : J → ℝ}
    (hm : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ n)) atTop (𝓝 M))
    {u : J → ℝ} (hu : Tendsto (fun n ↦ ‖θ n‖⁻¹ • θ n) atTop (𝓝 u))
    {x : J → ℝ} (hx : x ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S) :
    0 ≤ dotJ u (x - M) := by
  have hc : ∀ ε > 0, 0 < ν.real {y | dirLoss S u y < dotJ u x + ε} := by
    intro ε hε
    by_contra hcon
    have h0 : ν {y | dirLoss S u y < dotJ u x + ε} = 0 := by
      have := le_antisymm (not_lt.1 hcon) measureReal_nonneg
      exact (measureReal_eq_zero_iff (measure_ne_top ν _)).1 this
    have hae : ∀ᵐ y ∂ν, dirLoss S (-u) y ≤ -(dotJ u x + ε) := by
      have : ∀ᵐ y ∂ν, ¬ dirLoss S u y < dotJ u x + ε := ae_iff.2 (by simpa using h0)
      filter_upwards [this] with y hy
      rw [dirLoss_neg]
      linarith [not_lt.1 hy]
    have := momentBody_subset_halfspace measurable_const (fun _ ↦ one_pos) hS hae hx
    simp only [Set.mem_ofPred_eq, dotJ_neg_left] at this
    linarith
  have := dotJ_le_of_escape hS ν hr hm hu hc
  rw [(isLinearMap_dotJ u).map_sub]
  linarith

/-- **Normal-cone refinement of boundary escape along the atlas**: for a finite-rate response
`M` outside the relative interior and `s_n ↑ 1`, every limit `u` of the normalised natural
coordinates `θ(M_{s_n})/‖θ(M_{s_n})‖` satisfies `⟨u, M⟩ ≤ c` whenever `ν(⟨u,S⟩ < c + ε) > 0` for
all `ε > 0`; in particular `⟨u, x − M⟩ ≥ 0` on the moment body. -/
theorem dotJ_le_of_tendsto_normalized_atlasTheta [Nonempty J] {M : J → ℝ}
    (hfin : genRate ν S M ≠ ⊤)
    (hM : M ∉ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Ioo (0 : ℝ) 1) (hs1 : Tendsto s atTop (𝓝 1)) {u : J → ℝ}
    (hu : Tendsto (fun n ↦ ‖(atlasTheta hS ν M (s n) : J → ℝ)‖⁻¹ •
      (atlasTheta hS ν M (s n) : J → ℝ)) atTop (𝓝 u))
    {c : ℝ} (hc : ∀ ε > 0, 0 < ν.real {x | dirLoss S u x < c + ε}) :
    dotJ u M ≤ c := by
  refine dotJ_le_of_escape hS ν (θ := fun n ↦ (atlasTheta hS ν M (s n) : J → ℝ)) ?_ ?_ hu hc
  · have h := (tendsto_norm_atlasTheta_atTop hS ν hfin hM).comp
      (tendsto_nhdsWithin_iff.2 ⟨hs1, Eventually.of_forall fun n ↦ (hs n).2⟩)
    exact h
  · have := ((continuous_atlasPath ν (S := S) (M := M)).tendsto 1).comp hs1
    rw [atlasPath_one] at this
    refine this.congr fun n ↦ ?_
    exact (meanMap_atlasTheta hS ν hfin (hs n).1.le (hs n).2).symm

end Laplace.Multi
