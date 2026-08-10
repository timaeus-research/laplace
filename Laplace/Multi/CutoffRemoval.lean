/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.ShiftNormalization

/-!
# Cutoff removal: from compactly supported tests to monomial data

The germbij note's Theorem 3.1 premise quantifies over observables
`φ ∈ C_c^∞(U)`, while the merged recovery headlines consume bare
monomial moment families. The 2026-08-10 fidelity review flagged the
implication between the two as unformalised (finding F3). This file
closes it. The mechanism is the loss gap: on the support of `1 - χ`
(with `χ` a bump equal to `1` near the minimum) the rescaled exponent
dominates both `c‖x‖²` and `c r²/q²`, so the un-cut part of any
polynomial-growth moment is exponentially small in the temperature —
smaller than every power (`posteriorMoment_cutoff_tail`, via
`superPoly_of_eventually_abs_le_exp`). Consequently, superPoly
agreement of moment families over smooth compactly supported tests in
the common localization region yields superPoly agreement for every
smooth polynomial-growth observable (`superPoly_moment_of_ccData`),
and the base-case-free recovery headlines compose to the
compactly-supported-data forms `smooth_positive_jet_recovery_of_ccData`
and `analytic_germ_recovery_of_ccData`.

These are the CENTRED, PACKAGE-LEVEL forms of the note's inverse
direction (2026-08-10 perimeter review): both losses are packaged
around the common minimum `0` (location recovery is separate,
`location_eq_of_superPoly_first_moments`); the certified package
family `∀ k, 2 < k → HigherLaplaceDomain k L H` and the `IsSymm`
hypotheses are assumed rather than derived from the note's
smooth-nondegenerate setup; and the data premise quantifies per
package order `k` over tests supported in that order's pair of
localization regions, rather than over one fixed `U`.
-/

open Real MeasureTheory Filter Topology Asymptotics

/-! ## SuperPoly algebra and the exponential source -/

namespace Laplace

theorem SuperPoly.add {f g : ℝ → ℝ} (hf : SuperPoly f)
    (hg : SuperPoly g) : SuperPoly (fun t ↦ f t + g t) :=
  fun N ↦ (hf N).add (hg N)

theorem SuperPoly.sub {f g : ℝ → ℝ} (hf : SuperPoly f)
    (hg : SuperPoly g) : SuperPoly (fun t ↦ f t - g t) :=
  fun N ↦ (hf N).sub (hg N)

/-- **Exponential decay is beyond all orders**: an eventual bound
`|f t| ≤ K e^{-δt}` with `δ > 0` makes `f` superpolynomially small. -/
theorem superPoly_of_eventually_abs_le_exp {f : ℝ → ℝ} {K δ : ℝ}
    (hδ : 0 < δ)
    (h : ∀ᶠ t in atTop, |f t| ≤ K * Real.exp (-(δ * t))) :
    SuperPoly f := by
  intro N
  have hbig : f =O[atTop] fun t : ℝ ↦ Real.exp (-(δ * t)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨K, ?_⟩
    filter_upwards [h] with t ht
    rwa [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  refine hbig.trans_isLittleO ?_
  have hatTop : Tendsto (fun t : ℝ ↦ t ^ N * Real.exp (-(δ * t)))
      atTop (𝓝 0) := by
    have hbase := tendsto_pow_mul_exp_neg_atTop_nhds_zero N
    have hcomp := hbase.comp (tendsto_id.const_mul_atTop hδ)
    have h2 : Tendsto (fun t : ℝ ↦
        (δ * t) ^ N * Real.exp (-(δ * t))) atTop (𝓝 0) := hcomp
    have h3 := h2.const_mul ((δ ^ N)⁻¹)
    rw [mul_zero] at h3
    refine h3.congr fun t ↦ ?_
    rw [mul_pow]
    have hδN : (δ : ℝ) ^ N ≠ 0 := (pow_pos hδ N).ne'
    field_simp
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hatTop.eventually_le_const hε,
    eventually_gt_atTop (0 : ℝ)] with t hle ht0
  have hpow : (0 : ℝ) < t ^ N := pow_pos ht0 N
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.rpow_pos_of_pos ht0 _),
    Real.rpow_neg ht0.le, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ hpow, mul_comm]
  exact hle

end Laplace

namespace Laplace.Multi

variable {d : ℕ}

/-! ## Observables under dilation -/

theorem HasPolynomialGrowth.comp_smul {P : EuclidD d → ℝ}
    (hP : HasPolynomialGrowth P) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    HasPolynomialGrowth (fun x ↦ P (q • x)) := by
  obtain ⟨C, n, hC, h⟩ := hP
  refine ⟨C, n, hC, fun x ↦ ?_⟩
  have hnorm : ‖q • x‖ ≤ ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
    nlinarith [norm_nonneg x]
  calc |P (q • x)| ≤ C * (1 + ‖q • x‖ ^ n) := h _
    _ ≤ C * (1 + ‖x‖ ^ n) := by
        have := pow_le_pow_left₀ (norm_nonneg _) hnorm n
        have h1 : 1 + ‖q • x‖ ^ n ≤ 1 + ‖x‖ ^ n := by linarith
        exact mul_le_mul_of_nonneg_left h1 hC

namespace LocalLaplaceDomain

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The normalized moment as a quotient of rescaled integrals: the
dilation prefactors cancel exactly. -/
theorem posteriorMoment_eq_integrand_div (A : LocalLaplaceDomain L H)
    (f : EuclidD d → ℝ) {q : ℝ} (hq : 0 < q) :
    A.posteriorMoment f q =
      (∫ x : EuclidD d, A.integrand (fun x ↦ f (q • x)) q x) /
        ∫ x : EuclidD d, A.integrand (fun _ ↦ 1) q x := by
  unfold posteriorMoment
  rw [A.posteriorIntegral_eq f hq, A.posteriorIntegral_eq _ hq]
  have hpref : (0 : ℝ) < q ^ d * Real.exp (-(L 0 / q ^ 2)) := by
    positivity
  rw [mul_div_mul_left _ _ hpref.ne']

/-- **The cutoff tail is beyond all orders**: for a polynomial-growth
observable `P` and a cutoff `χ` with `0 ≤ χ ≤ 1` equal to `1` on a
ball around the minimum, the moments of `P` and of `P·χ` agree up to
a superpolynomially small function of the temperature — the loss gap
makes the un-cut region exponentially subdominant. -/
theorem posteriorMoment_cutoff_tail (A : LocalLaplaceDomain L H)
    {P χ : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P)
    (hχ_cont : Continuous χ) (hχ0 : ∀ w, 0 ≤ χ w) (hχ1 : ∀ w, χ w ≤ 1)
    {r : ℝ} (hr : 0 < r)
    (hχ_one : ∀ w ∈ Metric.ball (0 : EuclidD d) r, χ w = 1) :
    Laplace.SuperPoly (fun t : ℝ ↦
      A.posteriorMomentT P t -
        A.posteriorMomentT (fun w ↦ P w * χ w) t) := by
  obtain ⟨CP, n, hCP, hPb⟩ := hP_growth
  set δ : ℝ := A.c * r ^ 2 / 2 with hδ_def
  have hδ : 0 < δ := by
    have := A.c_pos
    positivity
  set M : ℝ := ∫ x : EuclidD d,
    (1 + ‖x‖ ^ n) * Real.exp (-(A.c / 2) * ‖x‖ ^ 2) with hM_def
  have hMint : Integrable (fun x : EuclidD d ↦
      (1 + ‖x‖ ^ n) * Real.exp (-(A.c / 2) * ‖x‖ ^ 2)) := by
    have hc2 : (0 : ℝ) < A.c / 2 := by have := A.c_pos; positivity
    have h1 : Integrable (fun x : EuclidD d ↦
        Real.exp (-(A.c / 2) * ‖x‖ ^ 2)) := by
      have := integrable_pow_mul_exp_neg_mul_sq (d := d) hc2 0
      refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
      simp
    have h2 := integrable_pow_mul_exp_neg_mul_sq (d := d) hc2 n
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have hM0 : 0 ≤ M :=
    integral_nonneg fun x ↦ by positivity
  set Z : ℝ := jacInv H * (2 * π) ^ ((d : ℝ) / 2) with hZ_def
  have hZ0 : 0 < Z := by
    have := jacInv_pos A.hH_posDef
    positivity
  -- the scale-level bound
  have hq_bound : ∀ᶠ q in 𝓝[>] (0 : ℝ),
      |A.posteriorMoment P q -
        A.posteriorMoment (fun w ↦ P w * χ w) q| ≤
      2 * CP * M / Z * Real.exp (-(δ / q ^ 2)) := by
    have hZev : ∀ᶠ q in 𝓝[>] (0 : ℝ), Z / 2 ≤
        ∫ x : EuclidD d, A.integrand (fun _ ↦ 1) q x :=
      A.tendsto_integral_rescaled_one.eventually_const_le
        (by linarith : Z / 2 < Z)
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0:ℝ) < 1), hZev]
      with q hq hZq
    obtain ⟨hq0, hq1⟩ := hq
    have hden_pos : (0 : ℝ) <
        ∫ x : EuclidD d, A.integrand (fun _ ↦ 1) q x := by
      linarith
    have hPq : ∀ x : EuclidD d, |P (q • x)| ≤ CP * (1 + ‖x‖ ^ n) := by
      intro x
      have hnorm : ‖q • x‖ ≤ ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
        nlinarith [norm_nonneg x]
      calc |P (q • x)| ≤ CP * (1 + ‖q • x‖ ^ n) := hPb _
        _ ≤ CP * (1 + ‖x‖ ^ n) := by
            have := pow_le_pow_left₀ (norm_nonneg _) hnorm n
            have h1 : 1 + ‖q • x‖ ^ n ≤ 1 + ‖x‖ ^ n := by linarith
            exact mul_le_mul_of_nonneg_left h1 hCP
    rw [A.posteriorMoment_eq_integrand_div P hq0,
      A.posteriorMoment_eq_integrand_div _ hq0, div_sub_div_same]
    have hint1 : Integrable (fun x : EuclidD d ↦
        A.integrand (fun x ↦ P (q • x)) q x) :=
      A.integrable_integrand (hP_cont.comp (continuous_const_smul q))
        (⟨CP, n, hCP, hPq⟩) hq0
    have hint2 : Integrable (fun x : EuclidD d ↦
        A.integrand (fun x ↦ P (q • x) * χ (q • x)) q x) := by
      refine A.integrable_integrand
        ((hP_cont.comp (continuous_const_smul q)).mul
          (hχ_cont.comp (continuous_const_smul q))) ?_ hq0
      refine ⟨CP, n, hCP, fun x ↦ ?_⟩
      have h1 : |P (q • x) * χ (q • x)| ≤ |P (q • x)| := by
        rw [abs_mul]
        have hχa : |χ (q • x)| ≤ 1 :=
          abs_le.mpr ⟨by linarith [hχ0 (q • x)], hχ1 (q • x)⟩
        nlinarith [abs_nonneg (P (q • x))]
      exact le_trans h1 (hPq x)
    rw [← integral_sub hint1 hint2]
    -- pointwise bound on the difference integrand
    have hpw : ∀ x : EuclidD d,
        ‖A.integrand (fun x ↦ P (q • x)) q x -
          A.integrand (fun x ↦ P (q • x) * χ (q • x)) q x‖ ≤
        Real.exp (-(δ / q ^ 2)) * CP *
          ((1 + ‖x‖ ^ n) * Real.exp (-(A.c / 2) * ‖x‖ ^ 2)) := by
      intro x
      unfold integrand
      by_cases hm : x ∈ {x : EuclidD d | q • x ∈ A.U}
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
        beta_reduce
        by_cases hball : q • x ∈ Metric.ball (0 : EuclidD d) r
        · rw [hχ_one _ hball]
          rw [show P (q • x) * Real.exp (-((L (q • x) - L 0) / q ^ 2)) -
              P (q • x) * 1 * Real.exp (-((L (q • x) - L 0) / q ^ 2)) =
              0 from by ring, norm_zero]
          positivity
        · have hGlow : A.c * ‖x‖ ^ 2 ≤ (L (q • x) - L 0) / q ^ 2 :=
            A.rescaled_lower hq0 hm
          have hxr : r / q ≤ ‖x‖ := by
            have hnq : ‖q • x‖ = q * ‖x‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
            have hge : r ≤ ‖q • x‖ := by
              rw [Metric.mem_ball, dist_zero_right, not_lt] at hball
              exact hball
            rw [hnq] at hge
            rw [div_le_iff₀ hq0, mul_comm]
            exact hge
          have hGr : A.c * r ^ 2 / q ^ 2 ≤ (L (q • x) - L 0) / q ^ 2 := by
            refine le_trans ?_ hGlow
            have hx2 : r ^ 2 / q ^ 2 ≤ ‖x‖ ^ 2 := by
              calc r ^ 2 / q ^ 2 = (r / q) ^ 2 := (div_pow r q 2).symm
                _ ≤ ‖x‖ ^ 2 := by
                    have h0 : (0 : ℝ) ≤ r / q := by positivity
                    nlinarith [hxr]
            calc A.c * r ^ 2 / q ^ 2 = A.c * (r ^ 2 / q ^ 2) := by ring
              _ ≤ A.c * ‖x‖ ^ 2 :=
                  mul_le_mul_of_nonneg_left hx2 A.c_pos.le
          have hGsplit : δ / q ^ 2 + A.c / 2 * ‖x‖ ^ 2 ≤
              (L (q • x) - L 0) / q ^ 2 := by
            rw [hδ_def]
            have hhalf : A.c * r ^ 2 / 2 / q ^ 2 =
                A.c * r ^ 2 / q ^ 2 / 2 := by ring
            rw [hhalf]
            linarith
          have hexp : Real.exp (-((L (q • x) - L 0) / q ^ 2)) ≤
              Real.exp (-(δ / q ^ 2)) *
                Real.exp (-(A.c / 2) * ‖x‖ ^ 2) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hh : -(δ / q ^ 2) + -(A.c / 2) * ‖x‖ ^ 2 =
                -(δ / q ^ 2 + A.c / 2 * ‖x‖ ^ 2) := by ring
            rw [hh]
            linarith
          have hPq : |P (q • x)| ≤ CP * (1 + ‖x‖ ^ n) := by
            have hnorm : ‖q • x‖ ≤ ‖x‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
              nlinarith [norm_nonneg x]
            calc |P (q • x)| ≤ CP * (1 + ‖q • x‖ ^ n) := hPb _
              _ ≤ CP * (1 + ‖x‖ ^ n) := by
                  have := pow_le_pow_left₀ (norm_nonneg _) hnorm n
                  have h1 : 1 + ‖q • x‖ ^ n ≤ 1 + ‖x‖ ^ n := by
                    linarith
                  exact mul_le_mul_of_nonneg_left h1 hCP
          have hfac : ‖P (q • x) *
              Real.exp (-((L (q • x) - L 0) / q ^ 2)) -
              P (q • x) * χ (q • x) *
                Real.exp (-((L (q • x) - L 0) / q ^ 2))‖ =
              |P (q • x)| * |1 - χ (q • x)| *
                Real.exp (-((L (q • x) - L 0) / q ^ 2)) := by
            rw [Real.norm_eq_abs,
              show P (q • x) * Real.exp (-((L (q • x) - L 0) / q ^ 2)) -
                P (q • x) * χ (q • x) *
                  Real.exp (-((L (q • x) - L 0) / q ^ 2)) =
                P (q • x) * (1 - χ (q • x)) *
                  Real.exp (-((L (q • x) - L 0) / q ^ 2)) from by ring,
              abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          rw [hfac]
          have hχd : |1 - χ (q • x)| ≤ 1 := by
            rw [abs_le]
            constructor
            · linarith [hχ1 (q • x)]
            · linarith [hχ0 (q • x)]
          calc |P (q • x)| * |1 - χ (q • x)| *
                Real.exp (-((L (q • x) - L 0) / q ^ 2))
              ≤ CP * (1 + ‖x‖ ^ n) * 1 *
                (Real.exp (-(δ / q ^ 2)) *
                  Real.exp (-(A.c / 2) * ‖x‖ ^ 2)) := by
                refine mul_le_mul ?_ hexp (Real.exp_pos _).le
                  (by positivity)
                exact mul_le_mul hPq hχd (abs_nonneg _)
                  (by positivity)
            _ = Real.exp (-(δ / q ^ 2)) * CP *
                ((1 + ‖x‖ ^ n) * Real.exp (-(A.c / 2) * ‖x‖ ^ 2)) := by
                ring
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm,
          sub_zero, norm_zero]
        positivity
    have hnum : ‖∫ x : EuclidD d,
        (A.integrand (fun x ↦ P (q • x)) q x -
          A.integrand (fun x ↦ P (q • x) * χ (q • x)) q x)‖ ≤
        Real.exp (-(δ / q ^ 2)) * CP * M := by
      have hgint : Integrable (fun x : EuclidD d ↦
          Real.exp (-(δ / q ^ 2)) * CP *
            ((1 + ‖x‖ ^ n) * Real.exp (-(A.c / 2) * ‖x‖ ^ 2))) :=
        hMint.const_mul _
      have h := norm_integral_le_of_norm_le hgint
        (Filter.Eventually.of_forall hpw)
      rwa [integral_const_mul] at h
    rw [abs_div, abs_of_pos hden_pos]
    calc |∫ x : EuclidD d,
          (A.integrand (fun x ↦ P (q • x)) q x -
            A.integrand (fun x ↦ P (q • x) * χ (q • x)) q x)| /
          (∫ x : EuclidD d, A.integrand (fun _ ↦ 1) q x)
        ≤ (Real.exp (-(δ / q ^ 2)) * CP * M) /
          (∫ x : EuclidD d, A.integrand (fun _ ↦ 1) q x) := by
          refine div_le_div_of_nonneg_right ?_ hden_pos.le
          rw [← Real.norm_eq_abs]
          exact hnum
      _ ≤ (Real.exp (-(δ / q ^ 2)) * CP * M) / (Z / 2) := by
          exact div_le_div_of_nonneg_left (by positivity)
            (by linarith) hZq
      _ = 2 * CP * M / Z * Real.exp (-(δ / q ^ 2)) := by
          field_simp
  -- transport to the temperature
  refine Laplace.superPoly_of_eventually_abs_le_exp
    (K := 2 * CP * M / Z) hδ ?_
  have htend := LocalLaplaceDomain.tendsto_inv_sqrt_nhdsGT_zero
  filter_upwards [htend.eventually hq_bound,
    eventually_gt_atTop (0 : ℝ)] with t hb ht0
  unfold posteriorMomentT
  refine le_trans hb (le_of_eq ?_)
  congr 1
  have hq2 : ((Real.sqrt t)⁻¹ : ℝ) ^ 2 = t⁻¹ := by
    rw [← Real.sqrt_inv]
    exact Real.sq_sqrt (by positivity)
  rw [hq2]
  congr 1
  rw [div_inv_eq_mul]

end LocalLaplaceDomain

/-! ## The compactly-supported-data bridge -/

open LocalLaplaceDomain in
/-- **Cutoff removal**: superPoly agreement of moment families over
smooth compactly supported tests in the common localization region
implies superPoly agreement for every smooth polynomial-growth
observable. -/
theorem superPoly_moment_of_ccData
    {L₁ L₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A : LocalLaplaceDomain L₁ H₁) (B : LocalLaplaceDomain L₂ H₂)
    (hdata : ∀ φ : EuclidD d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ A.U → tsupport φ ⊆ B.U →
      Laplace.SuperPoly (fun t : ℝ ↦
        A.posteriorMomentT φ t - B.posteriorMomentT φ t))
    {P : EuclidD d → ℝ} (hP_smooth : ContDiff ℝ (⊤ : ℕ∞) P)
    (hP_growth : HasPolynomialGrowth P) :
    Laplace.SuperPoly (fun t : ℝ ↦
      A.posteriorMomentT P t - B.posteriorMomentT P t) := by
  set ρ : ℝ := min A.delta B.delta with hρ_def
  have hρ : 0 < ρ := lt_min A.delta_pos B.delta_pos
  set f : ContDiffBump (0 : EuclidD d) :=
    ⟨ρ / 2, 3 * ρ / 4, by linarith, by linarith⟩ with hf_def
  have hχ_one : ∀ w ∈ Metric.ball (0 : EuclidD d) (ρ / 2),
      f w = 1 := fun w hw ↦
    f.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
  have hsupp : tsupport (fun w ↦ P w * f w) ⊆
      Metric.closedBall (0 : EuclidD d) (3 * ρ / 4) := by
    have hsub : Function.support (fun w ↦ P w * f w) ⊆
        Function.support (⇑f) := by
      intro w hw
      simp only [Function.mem_support] at hw ⊢
      intro h0
      exact hw (by rw [h0, mul_zero])
    have hclos := closure_mono hsub
    rw [← f.tsupport_eq]
    exact hclos
  have hsubA : tsupport (fun w ↦ P w * f w) ⊆ A.U := by
    refine subset_trans hsupp (subset_trans
      (Metric.closedBall_subset_ball ?_) A.ball_subset_U)
    have := min_le_left A.delta B.delta
    rw [hρ_def] at hρ ⊢
    linarith
  have hsubB : tsupport (fun w ↦ P w * f w) ⊆ B.U := by
    refine subset_trans hsupp (subset_trans
      (Metric.closedBall_subset_ball ?_) B.ball_subset_U)
    have := min_le_right A.delta B.delta
    rw [hρ_def] at hρ ⊢
    linarith
  have hcs : HasCompactSupport (fun w ↦ P w * f w) := by
    have := f.hasCompactSupport.mul_left (f := P)
    exact this
  have hT2 := hdata (fun w ↦ P w * f w)
    (hP_smooth.mul f.contDiff) hcs hsubA hsubB
  have hT1 := A.posteriorMoment_cutoff_tail hP_smooth.continuous
    hP_growth f.continuous (fun w ↦ f.nonneg) (fun w ↦ f.le_one)
    (by linarith : (0:ℝ) < ρ / 2) hχ_one
  have hT3 := B.posteriorMoment_cutoff_tail hP_smooth.continuous
    hP_growth f.continuous (fun w ↦ f.nonneg) (fun w ↦ f.le_one)
    (by linarith : (0:ℝ) < ρ / 2) hχ_one
  have hcomb := (hT1.add hT2).sub hT3
  have heq : (fun t : ℝ ↦
      A.posteriorMomentT P t - B.posteriorMomentT P t) =
      fun t : ℝ ↦
        ((A.posteriorMomentT P t -
            A.posteriorMomentT (fun w ↦ P w * f w) t) +
          (A.posteriorMomentT (fun w ↦ P w * f w) t -
            B.posteriorMomentT (fun w ↦ P w * f w) t)) -
        (B.posteriorMomentT P t -
          B.posteriorMomentT (fun w ↦ P w * f w) t) := by
    funext t
    ring
  rw [heq]
  exact hcomb

/-! ## Smoothness of the standard observables -/

theorem contDiff_monomialTest {k : ℕ} (m : Fin k → Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (monomialTest m) := by
  unfold monomialTest
  exact contDiff_prod fun j _ ↦
    (EuclideanSpace.proj (𝕜 := ℝ) (m j)).contDiff

theorem contDiff_coord_mul (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : EuclidD d ↦ w i * w j) :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).mul
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff)

theorem hasPolynomialGrowth_coord_mul (i j : Fin d) :
    HasPolynomialGrowth (fun w : EuclidD d ↦ w i * w j) := by
  refine ⟨1, 2, zero_le_one, fun x ↦ ?_⟩
  rw [abs_mul, one_mul]
  calc |x i| * |x j| ≤ ‖x‖ * ‖x‖ :=
        mul_le_mul (euclid_abs_coord_le_norm x i)
          (euclid_abs_coord_le_norm x j) (abs_nonneg _) (norm_nonneg _)
    _ = ‖x‖ ^ 2 := (sq ‖x‖).symm
    _ ≤ 1 + ‖x‖ ^ 2 := by linarith

/-! ## The note-literal recovery corollaries -/

open HigherLaplaceDomain in
/-- **Positive-order jet recovery from compactly supported test data**
(germbij Theorem 3.1, inverse direction, centred package-level form):
two localized nondegenerate losses whose moment families agree beyond
all orders on every smooth compactly supported test in the common
localization region have equal derivative tensors at every positive
order. Centred at the shared minimum `0`; the package family and the
symmetry of the derivative tensors are hypotheses (see the module
docstring for the remaining distance to the note's literal
statement). -/
theorem smooth_positive_jet_recovery_of_ccData
    {L₁ L₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H₁)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H₂)
    (hsymm₁ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ k (h2 : 2 < k), ∀ φ : EuclidD d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (A k h2).toLocalLaplaceDomain.U →
      tsupport φ ⊆ (B k h2).toLocalLaplaceDomain.U →
      Laplace.SuperPoly (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT φ t -
        (B k h2).toLocalLaplaceDomain.posteriorMomentT φ t)) :
    ∀ j, 0 < j → iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 := by
  refine smooth_positive_jet_recovery_of_superPoly_moments A B
    hsymm₁ hsymm₂ ?_ ?_
  · intro i j
    exact superPoly_moment_of_ccData _ _ (hdata 3 (by norm_num))
      (contDiff_coord_mul i j) (hasPolynomialGrowth_coord_mul i j)
  · intro k h2 m
    exact superPoly_moment_of_ccData _ _ (hdata k h2)
      (contDiff_monomialTest m) (monomialTest_hasPolynomialGrowth m)

/-- **The analytic germ corollary from compactly supported test data**
(germbij Corollary 3.2, inverse direction, centred package-level
form): for losses analytic at the minimum, moment agreement beyond
all orders on smooth compactly supported tests determines the germ
modulo the additive constant. Same caveats as
`smooth_positive_jet_recovery_of_ccData`. -/
theorem analytic_germ_recovery_of_ccData
    {L₁ L₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H₁)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H₂)
    (hsymm₁ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ k (h2 : 2 < k), ∀ φ : EuclidD d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (A k h2).toLocalLaplaceDomain.U →
      tsupport φ ⊆ (B k h2).toLocalLaplaceDomain.U →
      Laplace.SuperPoly (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT φ t -
        (B k h2).toLocalLaplaceDomain.posteriorMomentT φ t))
    (hL₁ : AnalyticAt ℝ L₁ 0) (hL₂ : AnalyticAt ℝ L₂ 0) :
    ∀ᶠ y in 𝓝 (0 : EuclidD d), L₁ y - L₁ 0 = L₂ y - L₂ 0 :=
  analytic_germ_eq_of_jet_eq hL₁ hL₂
    (smooth_positive_jet_recovery_of_ccData A B hsymm₁ hsymm₂ hdata)

end Laplace.Multi
