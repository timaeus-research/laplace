/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NormalizedSingular
import Laplace.Multi.SingularSufficientTests

/-!
# Localised singular identifiability

The normalized singular identifiability theorem of `NormalizedSingular` needs
the projective hypothesis for all smooth compactly supported tests. Its proof
uses only tests supported in a small ball around the zero under study: the
square-weight rigidity picks a bump at the zero whose radius can be taken as
small as desired, and the cancellation identity is applied to tests built from
that bump. This file records the localised statements:
`analytic_square_weight_eq_zero_near_local` (bumps supported in `ball p ρ`
suffice) and `normalized_families_force_germ_eq_at_local` (the projective
hypothesis is needed only for tests supported in `ball p ρ`). These are the
inputs for the fixed cutoff-monomial family of `CutoffMonomialFamily`.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff Pointwise

namespace Laplace

variable {ι : Type*} [Fintype ι]

theorem analytic_square_weight_eq_zero_near_local {K a : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hKc : Continuous K) (hK0 : ∀ w, 0 ≤ K w) (hKp : K p = 0)
    (hK2 : ContDiffAt ℝ 2 K p)
    (hac : Continuous a) (haA : AnalyticAt ℝ a p) (hap : a p = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hfam : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball p ρ →
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
  obtain ⟨C0, R₀, hC0, hR₀, hsum₀⟩ := Multi.quadratic_upper_bound_of_nonneg hK2' hK0' hKnn
  -- shrink the radius so that the bump below is supported in `ball p ρ`
  set R : ℝ := min R₀ (ρ / 4) with hR_def
  have hR : 0 < R := lt_min hR₀ (by positivity)
  have hRρ : 2 * R < ρ := by
    have : R ≤ ρ / 4 := min_le_right _ _
    linarith
  have hsum : ∀ w : ι → ℝ, ‖w‖ ≤ R → K (p + w) ≤ C0 * ‖w‖ ^ 2 := fun w hw ↦
    hsum₀ w (hw.trans (min_le_left _ _))
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
  have hψsupp : tsupport (fun u : ι → ℝ ↦ f (u - p)) ⊆ Metric.ball p ρ := by
    refine (closure_minimal ?_ Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hRρ)
    intro u hu
    have hmem : u - p ∈ tsupport f := subset_tsupport f hu
    rw [f.tsupport_eq, mem_closedBall_zero_iff] at hmem
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hmem
  have hsp := hfam _ hψ hψs hψsupp
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


/-- **Localised normalized singular identifiability.** The projective hypothesis
is needed only for tests supported in a ball `ball p ρ` around the common zero. -/
theorem normalized_families_force_germ_eq_at_local
    {L₁ L₂ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p)
    (hp1 : L₁ p = 0) (hp2 : L₂ p = 0) {C : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball p ρ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  classical
  set g : (ι → ℝ) → ℝ := fun w ↦ L₂ w - L₁ w with hg_def
  have hgs : ContDiff ℝ ∞ g := h2.sub h1
  have hgd : Differentiable ℝ g := hgs.differentiable (by simp)
  have hgp : g p = 0 := by simp [hg_def, hp1, hp2]
  have hgA : AnalyticAt ℝ g p := hA2.sub hA1
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
    have hac : Continuous fun w ↦ fderiv ℝ g w v :=
      (hgs.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    have has : ContDiff ℝ ∞ fun w ↦ fderiv ℝ g w v :=
      (contDiff_infty_iff_fderiv.mp hgs).2.clm_apply contDiff_const
    have haA : AnalyticAt ℝ (fun w ↦ fderiv ℝ g w v) p :=
      ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hgA.fderiv
    have hap : fderiv ℝ g p v = 0 := by rw [hfg]; rfl
    refine analytic_square_weight_eq_zero_near_local h2.continuous hL2 hp2 hA2.contDiffAt
      hac haA hap hρ ?_
    intro ψ hψ hψs hψsupp
    -- the two observables, both supported in `tsupport ψ ⊆ ball p ρ`
    set φ : (ι → ℝ) → ℝ := fun w ↦ ψ w * fderiv ℝ g w v with hφ_def
    have hφ : ContDiff ℝ ∞ φ := hψ.mul has
    have hφs : HasCompactSupport φ := hψs.mul_right
    have hφsupp : tsupport φ ⊆ Metric.ball p ρ :=
      (closure_mono fun w hw ↦ left_ne_zero_of_mul hw).trans hψsupp
    have hL₁' : ContDiff ℝ ∞ fun w ↦ fderiv ℝ L₁ w v :=
      (contDiff_infty_iff_fderiv.mp h1).2.clm_apply contDiff_const
    have hR₁ := hfam (fun w ↦ fderiv ℝ φ w v)
      ((contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const)
      ((hφs.fderiv ℝ).comp_left (g := fun T : (ι → ℝ) →L[ℝ] ℝ ↦ T v) rfl)
      (by
        refine (closure_minimal ?_ (isClosed_tsupport φ)).trans hφsupp
        intro w hw
        refine support_fderiv_subset ℝ ?_
        intro h0
        apply hw
        change fderiv ℝ φ w v = 0
        rw [h0]
        rfl)
    have hR₂ := hfam (fun w ↦ φ w * fderiv ℝ L₁ w v) (hφ.mul hL₁') hφs.mul_right
      ((closure_mono fun w hw ↦ left_ne_zero_of_mul hw).trans hφsupp)
    have hcanc := superPoly_integral_fderiv_sub_mul_exp_of_pair h1 h2 hφ hφs v hR₁ hR₂
    refine hcanc.congr (Eventually.of_forall fun t ↦ ?_)
    beta_reduce
    congr 1
    funext w
    simp only [hφ_def, hg_def]
    ring
  have := eventually_eq_zero_of_fderiv_single_eventually_zero hgd hgp hderiv
  filter_upwards [this] with w hw
  simp only [hg_def] at hw
  linarith

end Laplace
