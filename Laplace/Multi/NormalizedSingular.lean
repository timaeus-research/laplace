/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SingularSmooth
import Laplace.Multi.CutoffRemoval
import Laplace.Multi.LocatedCutoff
import Laplace.Anchoring

/-!
# The normalized singular identifiability theorem

The germbij note's Question 7.7 asks whether two nonnegative analytic
losses with a common zero locus can have *projectively* equal Laplace
families: `∫ φ e^{-tL₂} ≃ C(t) ∫ φ e^{-tL₁}` for every `φ ∈ C_c^∞` and some
scalar `C(t)`. This is exactly what the normalized expectation values
`⟨φ⟩_t = ∫ φ e^{-tL} / Z(t)` determine about the unnormalized families,
so the question is the normalized form of the singular identifiability
problem. The note's answer (2026-08-26) is *no*, by integration by parts:
`∫ ∂_vφ e^{-tL} = t ∫ φ ∂_vL e^{-tL}`, so feeding the observables `∂_vφ`
and `φ ∂_vL₁` to the projective hypothesis and combining them cancels
`C(t)` exactly,

`R_{∂_vφ}(t) / t - R_{φ ∂_vL₁}(t) = ∫ φ ∂_v(L₂ - L₁) e^{-tL₂}`,

leaving a *plain* (unnormalized) family that is beyond all orders. Taking
`φ = ψ ∂_v(L₂ - L₁)` makes the amplitude a square, and the sector lower
bound (`sector_lower_bound_multi`) forces the germ of `∂_v(L₂ - L₁)` at
every common zero to vanish; finitely many directions then make
`L₂ - L₁` locally constant, hence zero.

* `integral_fderiv_mul_exp`: the directional integration by parts against
  the Boltzmann weight (Mathlib's
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`).
* `superPoly_integral_fderiv_sub_mul_exp`: the cancellation identity, as a
  `SuperPoly` statement.
* `analytic_square_weight_eq_zero_near`: **square-weight rigidity** — if
  `∫ ψ a² e^{-tK}` is beyond all orders for every smooth compactly
  supported `ψ`, with `a` analytic at `p`, `a p = 0`, and `K ≥ 0` of class
  `C²` with `K p = 0`, then `a = 0` near `p`.
* `eventually_eq_zero_of_fderiv_single_eventually_zero`: vanishing
  coordinate derivatives near `p` force a function vanishing at `p` to
  vanish near `p`.
* `normalized_families_force_germ_eq_at`, `normalized_families_force_eq_near`:
  the theorem, point and locus forms.
* `normalized_expectations_force_eq_near`: the form with the `1/Z`
  incorporated — agreement beyond all orders of the expectation values
  normalized by a common nonnegative window `χ`.

The regularity hypotheses are global smoothness of `L₁, L₂` (so that
`φ ∂_vL₁` is again an admissible observable) and analyticity at the common
zeros; the scalar `C : ℝ → ℝ` is arbitrary.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff Pointwise

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-! ### Closure properties of `SuperPoly`

`SuperPoly.sub` (`Laplace.Multi.CutoffRemoval`) and `SuperPoly.congr`
(`Laplace.Multi.LocatedCutoff`) are imported; the two below are new. -/

/-- Dividing a beyond-all-orders function by `t` keeps it beyond all orders. -/
theorem SuperPoly.div_id {f : ℝ → ℝ} (hf : SuperPoly f) :
    SuperPoly fun t ↦ f t / t := by
  intro N
  have hinv : (fun t : ℝ ↦ t⁻¹) =O[atTop] fun _ : ℝ ↦ (1 : ℝ) :=
    isBigO_const_of_tendsto tendsto_inv_atTop_zero one_ne_zero
  have := (hf N).mul_isBigO hinv
  simpa [div_eq_mul_inv] using this

/-- Multiplying a beyond-all-orders function by a bounded one keeps it
beyond all orders. -/
theorem SuperPoly.bounded_mul {f B : ℝ → ℝ} (hf : SuperPoly f)
    (hB : B =O[atTop] fun _ : ℝ ↦ (1 : ℝ)) :
    SuperPoly fun t ↦ B t * f t := by
  intro N
  have := hB.mul_isLittleO (hf N)
  simpa using this

/-! ### Integration by parts against the Boltzmann weight -/

/-- **Directional integration by parts against `e^{-tL}`**: for a smooth
compactly supported `φ` and a smooth `L`,
`∫ ∂_vφ e^{-tL} = t ∫ φ ∂_vL e^{-tL}`. -/
theorem integral_fderiv_mul_exp {φ L : (ι → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hL : ContDiff ℝ ∞ L) (t : ℝ) (v : ι → ℝ) :
    ∫ w, fderiv ℝ φ w v * Real.exp (-(t * L w))
      = t * ∫ w, φ w * (fderiv ℝ L w v * Real.exp (-(t * L w))) := by
  set g : (ι → ℝ) → ℝ := fun w ↦ Real.exp (-(t * L w)) with hg_def
  have hLd : Differentiable ℝ L := hL.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hgd : ∀ w, HasFDerivAt g
      (Real.exp (-(t * L w)) • (-(t • fderiv ℝ L w))) w := by
    intro w
    have h1 : HasFDerivAt (fun w ↦ -(t * L w)) (-(t • fderiv ℝ L w)) w :=
      ((hLd w).hasFDerivAt.const_mul t).neg
    exact h1.exp
  have hgfd : ∀ w, fderiv ℝ g w v
      = Real.exp (-(t * L w)) * (-(t * fderiv ℝ L w v)) := by
    intro w
    rw [(hgd w).fderiv]
    simp [smul_eq_mul]
  -- Continuity and compact support of the factors.
  have hφ'c : Continuous fun w ↦ fderiv ℝ φ w v :=
    (hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hφ's : HasCompactSupport fun w ↦ fderiv ℝ φ w v :=
    (hφs.fderiv ℝ).comp_left (g := fun T : (ι → ℝ) →L[ℝ] ℝ ↦ T v) rfl
  have hL'c : Continuous fun w ↦ fderiv ℝ L w v :=
    (hL.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hgc : Continuous g := by
    rw [hg_def]; fun_prop
  have hg'c : Continuous fun w ↦ fderiv ℝ g w v := by
    have : (fun w ↦ fderiv ℝ g w v)
        = fun w ↦ Real.exp (-(t * L w)) * (-(t * fderiv ℝ L w v)) := funext hgfd
    rw [this]
    exact hgc.mul ((continuous_const.mul hL'c).neg)
  have hA : Integrable fun w ↦ fderiv ℝ φ w v * g w :=
    (hφ'c.mul hgc).integrable_of_hasCompactSupport hφ's.mul_right
  have hB : Integrable fun w ↦ φ w * fderiv ℝ g w v :=
    (hφ.continuous.mul hg'c).integrable_of_hasCompactSupport hφs.mul_right
  have hC : Integrable fun w ↦ φ w * g w :=
    (hφ.continuous.mul hgc).integrable_of_hasCompactSupport hφs.mul_right
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hA hB hC
    (fun x _ ↦ hφd x) (fun x _ ↦ (hgd x).differentiableAt)
  -- key : ∫ φ * fderiv g v = -∫ fderiv φ v * g
  have hrhs : (fun w ↦ φ w * fderiv ℝ g w v)
      = fun w ↦ -(t * (φ w * (fderiv ℝ L w v * Real.exp (-(t * L w))))) := by
    funext w
    rw [hgfd w]
    ring
  rw [hrhs, integral_neg, integral_const_mul] at key
  have : ∫ w, fderiv ℝ φ w v * g w
      = t * ∫ w, φ w * (fderiv ℝ L w v * Real.exp (-(t * L w))) := by
    linarith
  simpa [hg_def] using this

/-! ### The cancellation identity -/

/-- **Projective cancellation.** If the Laplace families of `L₂` and `L₁`
agree projectively beyond all orders against every smooth compactly
supported observable, then for every such `φ` and every direction `v` the
plain family `t ↦ ∫ φ ∂_v(L₂ - L₁) e^{-tL₂}` is beyond all orders: the
scalar `C` cancels between the observables `∂_vφ` and `φ ∂_vL₁`. -/
theorem superPoly_integral_fderiv_sub_mul_exp {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂) {C : ℝ → ℝ}
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w)))
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (v : ι → ℝ) :
    SuperPoly fun t ↦ ∫ w, φ w *
      (fderiv ℝ (fun w ↦ L₂ w - L₁ w) w v * Real.exp (-(t * L₂ w))) := by
  -- The two observables.
  have hφ₁ : ContDiff ℝ ∞ fun w ↦ fderiv ℝ φ w v :=
    (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
  have hφ₁s : HasCompactSupport fun w ↦ fderiv ℝ φ w v :=
    (hφs.fderiv ℝ).comp_left (g := fun T : (ι → ℝ) →L[ℝ] ℝ ↦ T v) rfl
  have hL₁' : ContDiff ℝ ∞ fun w ↦ fderiv ℝ L₁ w v :=
    (contDiff_infty_iff_fderiv.mp h1).2.clm_apply contDiff_const
  have hφ₂ : ContDiff ℝ ∞ fun w ↦ φ w * fderiv ℝ L₁ w v := hφ.mul hL₁'
  have hφ₂s : HasCompactSupport fun w ↦ φ w * fderiv ℝ L₁ w v := hφs.mul_right
  have hR₁ := hfam _ hφ₁ hφ₁s
  have hR₂ := hfam _ hφ₂ hφ₂s
  refine (hR₁.div_id.sub hR₂).congr ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  -- Integration by parts on both families of the first observable.
  rw [integral_fderiv_mul_exp hφ hφs h2 t v, integral_fderiv_mul_exp hφ hφs h1 t v]
  -- Integrability of the pieces.
  have hL₂'c : Continuous fun w ↦ fderiv ℝ L₂ w v :=
    (h2.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hL₁'c : Continuous fun w ↦ fderiv ℝ L₁ w v :=
    (h1.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hec : Continuous fun w ↦ Real.exp (-(t * L₂ w)) := by fun_prop
  have hI₂ : Integrable fun w ↦ φ w * (fderiv ℝ L₂ w v * Real.exp (-(t * L₂ w))) :=
    (hφ.continuous.mul (hL₂'c.mul hec)).integrable_of_hasCompactSupport hφs.mul_right
  have hI₁ : Integrable fun w ↦ φ w * (fderiv ℝ L₁ w v * Real.exp (-(t * L₂ w))) :=
    (hφ.continuous.mul (hL₁'c.mul hec)).integrable_of_hasCompactSupport hφs.mul_right
  have hsub : ∫ w, φ w * (fderiv ℝ (fun w ↦ L₂ w - L₁ w) w v * Real.exp (-(t * L₂ w)))
      = (∫ w, φ w * (fderiv ℝ L₂ w v * Real.exp (-(t * L₂ w))))
        - ∫ w, φ w * (fderiv ℝ L₁ w v * Real.exp (-(t * L₂ w))) := by
    rw [← integral_sub hI₂ hI₁]
    congr 1
    funext w
    have hd : fderiv ℝ (fun w ↦ L₂ w - L₁ w) w = fderiv ℝ L₂ w - fderiv ℝ L₁ w :=
      ((h2.differentiable (by simp) w).hasFDerivAt.sub
        (h1.differentiable (by simp) w).hasFDerivAt).fderiv
    rw [hd]
    simp only [sub_apply]
    ring
  rw [hsub]
  field_simp
  ring

/-! ### Square-weight rigidity -/

/-- **Analytic square-weight rigidity.** Let `K ≥ 0` be continuous, `C²` at
`p` with `K p = 0`, and let `a` be continuous and analytic at `p` with
`a p = 0`. If `t ↦ ∫ ψ a² e^{-tK}` is beyond all orders for every smooth
compactly supported `ψ`, then `a` vanishes on a neighborhood of `p`. This
packages the sector lower bound of `sector_lower_bound_multi`. -/
theorem analytic_square_weight_eq_zero_near {K a : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hKc : Continuous K) (hK0 : ∀ w, 0 ≤ K w) (hKp : K p = 0)
    (hK2 : ContDiffAt ℝ 2 K p)
    (hac : Continuous a) (haA : AnalyticAt ℝ a p) (hap : a p = 0)
    (hfam : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      SuperPoly fun t ↦ ∫ w, ψ w * (a w ^ 2 * Real.exp (-(t * K w)))) :
    ∀ᶠ w in 𝓝 p, a w = 0 := by
  by_contra h
  -- Translate `p` to the origin.
  have hshift : AnalyticAt ℝ (fun w : ι → ℝ ↦ p + w) 0 :=
    analyticAt_const.add analyticAt_id
  have hshift0 : (fun w : ι → ℝ ↦ p + w) 0 = p := AddMonoid.add_zero p
  have hA' : AnalyticAt ℝ (fun w ↦ a (p + w)) 0 := by
    have hg : AnalyticAt ℝ a ((fun w : ι → ℝ ↦ p + w) 0) := by simpa using haA
    exact hg.comp hshift
  obtain ⟨q, r, hqr⟩ := hA'
  obtain ⟨ε, hε0, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ r := by
    rcases eq_or_ne r ⊤ with hr | hr
    · exact ⟨1, one_pos, by rw [hr]; exact le_top⟩
    · exact ⟨r.toReal, ENNReal.toReal_pos hqr.r_pos.ne' hr,
        (ENNReal.ofReal_toReal hr).le⟩
  have hfreq : ∃ᶠ w in 𝓝 p, a w ≠ 0 := Filter.not_eventually.mp h
  have hball : ∀ᶠ w in 𝓝 p, w ∈ Metric.ball p ε :=
    Metric.isOpen_ball.eventually_mem (Metric.mem_ball_self hε0)
  obtain ⟨u, hu_ne, hu_mem⟩ := (hfreq.and_eventually hball).exists
  have hG0 : (fun w ↦ a (p + w)) 0 = 0 := by simp [hap]
  have hne : ∃ w ∈ Metric.eball (0 : ι → ℝ) r, (fun w ↦ a (p + w)) w ≠ 0 := by
    refine ⟨u - p, ?_, ?_⟩
    · have hd : dist (u - p) (0 : ι → ℝ) = dist u p := by
        rw [dist_zero_right, dist_eq_norm]
      have hlt : edist (u - p) (0 : ι → ℝ) < ENNReal.ofReal ε := by
        rw [edist_dist, hd]
        exact (ENNReal.ofReal_lt_ofReal_iff hε0).mpr hu_mem
      exact Metric.mem_eball.mpr (lt_of_lt_of_le hlt hεr)
    · have hu : p + (u - p) = u := add_sub_cancel p u
      simpa [hu] using hu_ne
  obtain ⟨m, hlow, x₀, hx₀, hx₀n⟩ := Multi.exists_least_nonzero_diagonal hqr hG0 hne
  -- The leading part and the scaled set.
  obtain ⟨Cr, u₁, hCr, hu₁, hrem⟩ := analytic_remainder_bound hqr m hlow
  have hPc : Continuous fun x : ι → ℝ ↦ (q m) (fun _ ↦ x) :=
    (q m).coe_continuous.comp (continuous_pi fun _ ↦ continuous_id)
  have hPh : ∀ (c : ℝ) (x : ι → ℝ), 0 ≤ c →
      (q m) (fun _ ↦ c • x) = c ^ m * (q m) (fun _ ↦ x) := by
    intro c x _
    simpa [Finset.prod_const, smul_eq_mul] using
      (q m).map_smul_univ (fun _ : Fin m ↦ c) (fun _ ↦ x)
  obtain ⟨S, c, u₀, hS, hSfin, hSvol0, hSnorm, hc, hu₀, hbound⟩ :=
    leading_part_scaled_set (fun w ↦ a (p + w)) (fun x ↦ (q m) (fun _ ↦ x)) m
      hPc hPh hx₀ hx₀n hCr hu₁ hrem
  have hvolpos : 0 < (volume S).toReal := ENNReal.toReal_pos hSvol0 hSfin
  -- The quadratic upper bound on the shifted weight.
  have hK2' : ContDiffAt ℝ 2 (fun w ↦ K (p + w)) 0 := by
    have hg : ContDiffAt ℝ 2 K ((fun w : ι → ℝ ↦ p + w) 0) := by simpa using hK2
    exact hg.comp 0 (contDiffAt_const.add contDiffAt_id)
  have hK0' : (fun w ↦ K (p + w)) 0 = 0 := by simp [hKp]
  have hKnn : ∀ᶠ w in 𝓝 (0 : ι → ℝ), 0 ≤ K (p + w) :=
    Eventually.of_forall fun w ↦ hK0 _
  obtain ⟨C0, R, hC0, hR, hsum⟩ := Multi.quadratic_upper_bound_of_nonneg hK2' hK0' hKnn
  -- The smooth bump equal to `1` on the ball of radius `R`.
  set f : ContDiffBump (0 : ι → ℝ) :=
    { rIn := R, rOut := 2 * R, rIn_pos := hR,
      rIn_lt_rOut := by exact lt_two_mul_self hR } with hf_def
  have hf1 : ∀ w : ι → ℝ, ‖w‖ ≤ R → f w = 1 := fun w hw ↦
    f.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hw)
  have hψ : ContDiff ℝ ∞ (fun u : ι → ℝ ↦ f (u - p)) :=
    f.contDiff.comp (contDiff_id.sub contDiff_const)
  have hψs : HasCompactSupport (fun u : ι → ℝ ↦ f (u - p)) :=
    f.hasCompactSupport.comp_homeomorph (Homeomorph.subRight p)
  have hsp := hfam _ hψ hψs
  -- Translate the family to the origin.
  set Δ : ℝ → ℝ := fun t ↦ ∫ w, f w * (a (p + w) ^ 2 * Real.exp (-(t * K (p + w))))
    with hΔ_def
  have hΔeq : ∀ t, (∫ u, f (u - p) * (a u ^ 2 * Real.exp (-(t * K u)))) = Δ t := by
    intro t
    rw [hΔ_def]
    beta_reduce
    rw [← integral_add_left_eq_self
      (fun u ↦ f (u - p) * (a u ^ 2 * Real.exp (-(t * K u)))) p]
    simp only [add_sub_cancel_left]
  have hdecay : ∀ N : ℕ, Δ =o[atTop] fun t : ℝ ↦ t ^ (-(N : ℝ)) := by
    intro N
    exact (hsp N).congr' (Eventually.of_forall hΔeq) EventuallyEq.rfl
  -- The lower bound for large `t`.
  refine lower_bound_not_superpolynomial
    (κ := (volume S).toReal * (c ^ 2 * Real.exp (-(4 * C0))))
    (T₀ := max (4 / R ^ 2) (u₀⁻¹ ^ 2))
    (γ := -(m : ℝ) - (Fintype.card ι : ℝ) / 2) (by positivity) ?_ hdecay
  intro t ht
  have htpos : 0 < t :=
    lt_of_lt_of_le (lt_max_of_lt_left (by positivity : (0:ℝ) < 4 / R ^ 2)) ht
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have ht4 : 4 ≤ R ^ 2 * t := by
    have h1 : 4 / R ^ 2 ≤ t := le_trans (le_max_left _ _) ht
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    exact (div_le_iff₀' hR2).mp h1
  have hinvle : (Real.sqrt t)⁻¹ ≤ u₀ := by
    have h2 : u₀⁻¹ ^ 2 ≤ t := le_trans (le_max_right _ _) ht
    have h3 : u₀⁻¹ ≤ Real.sqrt t := Real.le_sqrt_of_sq_le h2
    rw [inv_le_comm₀ hst hu₀]
    exact h3
  have hgrow : ∀ x ∈ S, c * ((Real.sqrt t)⁻¹) ^ m ≤ |a (p + (Real.sqrt t)⁻¹ • x)| :=
    fun x hx ↦ hbound ((Real.sqrt t)⁻¹) ⟨inv_pos.mpr hst, hinvle⟩ x hx
  -- On the scaled set the bump is `1`.
  have hscaled_norm : ∀ w ∈ ((Real.sqrt t)⁻¹) • S, ‖w‖ ≤ R := by
    rintro w ⟨x, hxS, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hst)]
    have h2 : 2 * (Real.sqrt t)⁻¹ ≤ R := by
      have h3 : 2 / R ≤ Real.sqrt t := by
        apply Real.le_sqrt_of_sq_le
        rw [div_pow, div_le_iff₀ (by positivity)]
        linarith
      have h4 : (2 : ℝ) ≤ Real.sqrt t * R := (div_le_iff₀ hR).mp h3
      calc 2 * (Real.sqrt t)⁻¹ = 2 / Real.sqrt t := by ring
        _ ≤ R := by rw [div_le_iff₀ hst]; linarith
    calc (Real.sqrt t)⁻¹ * ‖x‖ ≤ (Real.sqrt t)⁻¹ * 2 :=
          mul_le_mul_of_nonneg_left (hSnorm x hxS) (inv_pos.mpr hst).le
      _ ≤ R := by linarith
  -- Integrability of the shifted integrand on the whole space (compact support).
  have hshiftc : Continuous (fun w : ι → ℝ ↦ p + w) := continuous_const.add continuous_id
  have hintf : Integrable fun w ↦ f w * (a (p + w) ^ 2 * Real.exp (-(t * K (p + w)))) := by
    have hcont : Continuous fun w ↦ f w * (a (p + w) ^ 2 * Real.exp (-(t * K (p + w)))) :=
      f.continuous.mul (((hac.comp hshiftc).pow 2).mul
        (Real.continuous_exp.comp ((continuous_const.mul (hKc.comp hshiftc)).neg)))
    exact hcont.integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  have hSm : MeasurableSet (((Real.sqrt t)⁻¹) • S) := hS.const_smul_of_ne_zero (inv_pos.mpr hst).ne'
  have hcongr : Set.EqOn (fun w ↦ a (p + w) ^ 2 * Real.exp (-(t * K (p + w))))
      (fun w ↦ f w * (a (p + w) ^ 2 * Real.exp (-(t * K (p + w))))) (((Real.sqrt t)⁻¹) • S) := by
    intro w hw
    simp [hf1 w (hscaled_norm w hw)]
  have hintS : IntegrableOn (fun w ↦ a (p + w) ^ 2 * Real.exp (-(t * K (p + w))))
      (((Real.sqrt t)⁻¹) • S) volume :=
    (hintf.integrableOn).congr_fun hcongr.symm hSm
  have hsec := sector_lower_bound_multi (fun w ↦ K (p + w)) (fun w ↦ a (p + w)) m
    hS hSfin hc.le hC0 hR ht4 hSnorm hgrow hsum hintS
  have hnonneg : ∀ w, 0 ≤ f w * (a (p + w) ^ 2 * Real.exp (-(t * K (p + w)))) :=
    fun w ↦ mul_nonneg (f.nonneg' w) (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
  have hle : ∫ w in ((Real.sqrt t)⁻¹) • S, a (p + w) ^ 2 * Real.exp (-(t * K (p + w)))
      ≤ Δ t := by
    rw [setIntegral_congr_fun hSm hcongr]
    exact setIntegral_le_integral hintf (Eventually.of_forall hnonneg)
  calc (volume S).toReal * (c ^ 2 * Real.exp (-(4 * C0)))
        * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2)
      = (volume S).toReal * (c ^ 2 * Real.exp (-(4 * C0))
          * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2)) := by ring
    _ ≤ ∫ w in ((Real.sqrt t)⁻¹) • S, a (p + w) ^ 2 * Real.exp (-(t * K (p + w))) := hsec
    _ ≤ Δ t := hle

/-! ### Local constancy from vanishing coordinate derivatives -/

omit [Fintype ι] in
/-- If every coordinate derivative of a differentiable `g` vanishes on a
neighborhood of `p` and `g p = 0`, then `g` vanishes on a neighborhood of
`p` (the ball is convex). -/
theorem eventually_eq_zero_of_fderiv_single_eventually_zero [Finite ι] [DecidableEq ι]
    {g : (ι → ℝ) → ℝ} {p : ι → ℝ} (hg : Differentiable ℝ g) (hgp : g p = 0)
    (h : ∀ i : ι, ∀ᶠ w in 𝓝 p, fderiv ℝ g w (Pi.single i 1) = 0) :
    ∀ᶠ w in 𝓝 p, g w = 0 := by
  cases nonempty_fintype ι
  have hall : ∀ᶠ w in 𝓝 p, ∀ i, fderiv ℝ g w (Pi.single i 1) = 0 :=
    eventually_all.mpr h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  have hzero : ∀ w ∈ Metric.ball p ε, fderiv ℝ g w = 0 := by
    intro w hw
    apply ContinuousLinearMap.ext
    intro x
    have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq]
    have hw' : dist w p < ε := Metric.mem_ball.mp hw
    rw [hx, map_sum]
    simp [map_smul, hball hw']
  filter_upwards [Metric.ball_mem_nhds p hε] with w hw
  have hconst := (convex_ball p ε).is_const_of_fderivWithin_eq_zero
    hg.differentiableOn
    (fun x hx ↦ by rw [fderivWithin_of_isOpen Metric.isOpen_ball hx]; exact hzero x hx)
    hw (Metric.mem_ball_self hε)
  rw [hconst, hgp]

/-! ### The theorem -/

/-- **Normalized singular identifiability, point form** (the note's answer
to Question 7.7). Let `L₁, L₂` be smooth and nonnegative, analytic at a
common zero `p`, and suppose their Laplace families agree *projectively*
beyond all orders against every smooth compactly supported observable:
for some scalar `C : ℝ → ℝ` and every such `φ`,
`∫ φ e^{-tL₂} - C(t) ∫ φ e^{-tL₁}` is beyond all orders. Then `L₁ = L₂` on
a neighborhood of `p`. -/
theorem normalized_families_force_germ_eq_at
    {L₁ L₂ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p)
    (hp1 : L₁ p = 0) (hp2 : L₂ p = 0) {C : ℝ → ℝ}
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  classical
  set g : (ι → ℝ) → ℝ := fun w ↦ L₂ w - L₁ w with hg_def
  have hgs : ContDiff ℝ ∞ g := h2.sub h1
  have hgd : Differentiable ℝ g := hgs.differentiable (by simp)
  have hgp : g p = 0 := by simp [hg_def, hp1, hp2]
  have hgA : AnalyticAt ℝ g p := hA2.sub hA1
  -- Both losses have a local minimum at `p`, so the derivatives vanish there.
  have hmin1 : IsLocalMin L₁ p := Eventually.of_forall fun w ↦ hp1 ▸ hL1 w
  have hmin2 : IsLocalMin L₂ p := Eventually.of_forall fun w ↦ hp2 ▸ hL2 w
  have hfg : fderiv ℝ g p = 0 := by
    have hd : fderiv ℝ g p = fderiv ℝ L₂ p - fderiv ℝ L₁ p :=
      ((h2.differentiable (by simp) p).hasFDerivAt.sub
        (h1.differentiable (by simp) p).hasFDerivAt).fderiv
    rw [hd, hmin1.fderiv_eq_zero, hmin2.fderiv_eq_zero, sub_zero]
  have hderiv : ∀ i : ι, ∀ᶠ w in 𝓝 p, fderiv ℝ g w (Pi.single i 1) = 0 := by
    intro i
    set v : ι → ℝ := Pi.single i 1 with hv_def
    -- The amplitude `a = ∂_v g`.
    have hac : Continuous fun w ↦ fderiv ℝ g w v :=
      (hgs.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    have has : ContDiff ℝ ∞ fun w ↦ fderiv ℝ g w v :=
      (contDiff_infty_iff_fderiv.mp hgs).2.clm_apply contDiff_const
    have haA : AnalyticAt ℝ (fun w ↦ fderiv ℝ g w v) p :=
      ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hgA.fderiv
    have hap : fderiv ℝ g p v = 0 := by rw [hfg]; rfl
    refine analytic_square_weight_eq_zero_near h2.continuous hL2 hp2 hA2.contDiffAt
      hac haA hap ?_
    intro ψ hψ hψs
    have hcanc := superPoly_integral_fderiv_sub_mul_exp h1 h2 hfam
      (φ := fun w ↦ ψ w * fderiv ℝ g w v) (hψ.mul has) hψs.mul_right v
    refine hcanc.congr (Eventually.of_forall fun t ↦ ?_)
    beta_reduce
    congr 1
    funext w
    simp only [hg_def]
    ring
  have := eventually_eq_zero_of_fderiv_single_eventually_zero hgd hgp hderiv
  filter_upwards [this] with w hw
  simp only [hg_def] at hw
  linarith

/-- **Normalized singular identifiability, locus form.** Under the
hypotheses of `normalized_families_force_germ_eq_at` at every point of a
set `W₀` of common zeros, `L₁ = L₂` on an open neighborhood of `W₀`. -/
theorem normalized_families_force_eq_near
    {L₁ L₂ : (ι → ℝ) → ℝ} {W₀ : Set (ι → ℝ)}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p ∈ W₀, AnalyticAt ℝ L₁ p) (hA2 : ∀ p ∈ W₀, AnalyticAt ℝ L₂ p)
    (hzero1 : ∀ p ∈ W₀, L₁ p = 0) (hzero2 : ∀ p ∈ W₀, L₂ p = 0) {C : ℝ → ℝ}
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w := by
  have h : ∀ p ∈ W₀, ∃ V : Set (ι → ℝ),
      (∀ w ∈ V, L₁ w = L₂ w) ∧ IsOpen V ∧ p ∈ V := fun p hp ↦
    eventually_nhds_iff.mp
      (normalized_families_force_germ_eq_at h1 h2 hL1 hL2 (hA1 p hp) (hA2 p hp)
        (hzero1 p hp) (hzero2 p hp) hfam)
  choose V hVeq hVopen hVmem using h
  refine ⟨⋃ p, ⋃ hp : p ∈ W₀, V p hp, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun p ↦ isOpen_iUnion fun hp ↦ hVopen p hp
  · exact fun p hp ↦ Set.mem_iUnion₂.mpr ⟨p, hp, hVmem p hp⟩
  · intro w hw
    obtain ⟨p, hp, hwV⟩ := Set.mem_iUnion₂.mp hw
    exact hVeq p hp w hwV

/-! ### The form with the normalization -/

/-- **Identifiability from normalized expectation values.** Normalize both
families by a common continuous, compactly supported, nonnegative window
`χ` whose Boltzmann integrals are positive, and suppose the normalized
expectations `∫ φ e^{-tL₂} / ∫ χ e^{-tL₂} - ∫ φ e^{-tL₁} / ∫ χ e^{-tL₁}` are
beyond all orders for every smooth compactly supported `φ`. Then `L₁ = L₂`
on an open neighborhood of any set `W₀` of common zeros at which both are
analytic. The scalar of the projective form is `C(t) = Z₂(t)/Z₁(t)`, and
`0 ≤ Z₂(t) ≤ ∫ χ` for `t ≥ 0` bounds it. -/
theorem normalized_expectations_force_eq_near
    {L₁ L₂ χ : (ι → ℝ) → ℝ} {W₀ : Set (ι → ℝ)}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p ∈ W₀, AnalyticAt ℝ L₁ p) (hA2 : ∀ p ∈ W₀, AnalyticAt ℝ L₂ p)
    (hzero1 : ∀ p ∈ W₀, L₁ p = 0) (hzero2 : ∀ p ∈ W₀, L₂ p = 0)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₂ w)))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦
        (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
        - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w)))) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w := by
  set Z₁ : ℝ → ℝ := fun t ↦ ∫ w, χ w * Real.exp (-(t * L₁ w)) with hZ₁_def
  set Z₂ : ℝ → ℝ := fun t ↦ ∫ w, χ w * Real.exp (-(t * L₂ w)) with hZ₂_def
  -- `Z₂` is bounded for large `t`.
  have hχint : Integrable χ := hχc.integrable_of_hasCompactSupport hχs
  have hZ₂le : ∀ t : ℝ, 0 ≤ t → Z₂ t ≤ ∫ w, χ w := by
    intro t ht
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun w ↦ mul_nonneg (hχ0 w) (Real.exp_nonneg _)
    · exact hχint
    · refine Eventually.of_forall fun w ↦ ?_
      have : Real.exp (-(t * L₂ w)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg ht (hL2 w))
      calc χ w * Real.exp (-(t * L₂ w)) ≤ χ w * 1 :=
            mul_le_mul_of_nonneg_left this (hχ0 w)
        _ = χ w := mul_one _
  have hZ₂O : Z₂ =O[atTop] fun _ : ℝ ↦ (1 : ℝ) := by
    refine IsBigO.of_bound (∫ w, χ w) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (hZ2 t), norm_one, mul_one]
    exact hZ₂le t ht
  refine normalized_families_force_eq_near h1 h2 hL1 hL2 hA1 hA2 hzero1 hzero2
    (C := fun t ↦ Z₂ t / Z₁ t) ?_
  intro φ hφ hφs
  have hφ' := (hfam φ hφ hφs).bounded_mul hZ₂O
  refine hφ'.congr (Eventually.of_forall fun t ↦ ?_)
  have h1t : Z₁ t ≠ 0 := (hZ1 t).ne'
  have h2t : Z₂ t ≠ 0 := (hZ2 t).ne'
  simp only [hZ₁_def, hZ₂_def] at h1t h2t ⊢
  field_simp

end Laplace
