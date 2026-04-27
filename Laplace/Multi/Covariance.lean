import Laplace.Multi.RescaledIntegrals

/-!
# Multivariate Laplace covariance theorem (`lem:laplace_cov`)

For a smooth potential `V : (ι → ℝ) → ℝ` with nondegenerate minimum at
`0` (Hessian `H = ∇²V(0) > 0`, inverse `Σ = H⁻¹`) and observables `φ, ψ`
vanishing at `0` with gradients `a = ∇φ(0)`, `b = ∇ψ(0)`,

  `Cov_t[φ, ψ] = (1/t) · ⟨a, Σ b⟩ + O(t⁻²)`.

This file states and (eventually) proves the explicit-rate version

  `∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
    |t · gibbsCov V t φ ψ - ⟨a, Hinv b⟩| ≤ K / t`.

## Strategy (per GPT-5.5 Pro Phase 5 memo)

1. Use the change-of-variables bridge `gibbsCov_eq_rescaledCov`
   (`RescaledIntegrals.lean`) to move to the rescaled `u`-space.
2. Express the rescaled numerator as
   `∫ F(u) · gaussianWeight H u · exp(-rescaledPerturbation V H t u) du`
   via `rescaling_identity`.
3. Use the Gaussian-bilinear-moment lemma `gaussian_dot_mul_dot` to
   identify the leading-order term.
4. Use the odd-Gaussian-vanishing lemma `integral_odd_mul_gaussian_eq_zero`
   to kill the half-power correction terms (sharp track only).
5. Use scalar `exp` bounds to control the perturbation expansion.
6. Compose via a quotient-algebra lemma: `N_t / D_t - (M_t/D_t)·(N'_t/D_t)
   = A/(Z·t) + O(t⁻²)`.

## Hypothesis package

We work with explicit local Taylor estimates + global coercivity, no
auto-derivation from `ContDiff`. The two structures `PotentialApprox`
and `ObservableApprox` package the necessary inequalities.

The `FubiniIBPHypothesis` from Phase 4 + the analytic prerequisites of
the main theorem are bundled into `LaplaceCovHypotheses` for clarity.
-/

namespace Laplace.Multi

open MeasureTheory Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section HypothesisPackage

/-- **Polynomial-growth predicate**: `f` is bounded above by some
polynomial `K · (1 + ‖w‖^p)` everywhere on `ι → ℝ`. Used to ensure
that observable integrals against the Gibbs measure converge. -/
def HasPolyGrowth (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ K : ℝ, ∃ p : ℕ, 0 ≤ K ∧ ∀ w, |f w| ≤ K * (1 + ‖w‖ ^ p)

/-- **Approximation package for the potential**. Captures the local
Taylor estimate and global coercivity needed for the weak-rate theorem.

For the sharp `O(t⁻²)` rate, the cubic remainder needs to be split into
an odd cubic jet and a quartic remainder; that's `PotentialJetApprox`
(future work). -/
structure PotentialApprox (V : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) where
  /-- `V` is continuous (needed for global integrability bounds). -/
  V_continuous : Continuous V
  /-- `V` vanishes at the minimum. -/
  V_zero : V 0 = 0
  /-- Local cubic remainder: `|V(w) - (1/2) quadForm H w| ≤ C · ‖w‖³`
  on the closed ball of radius `R`. -/
  local_radius : ℝ
  local_const : ℝ
  local_radius_pos : 0 < local_radius
  local_const_nonneg : 0 ≤ local_const
  local_bound : ∀ w : ι → ℝ, ‖w‖ ≤ local_radius →
    |V w - (1/2) * quadForm H w| ≤ local_const * ‖w‖ ^ 3
  /-- Global coercivity: `V(w) ≥ c · ‖w‖²` for some `c > 0`. -/
  coercive_const : ℝ
  coercive_const_pos : 0 < coercive_const
  coercive_bound : ∀ w : ι → ℝ, coercive_const * ‖w‖ ^ 2 ≤ V w
  /-- Polynomial growth above (for integrability of observables · exp(-tV)). -/
  poly_growth : HasPolyGrowth V

/-- **Approximation package for an observable** with gradient `a`. -/
structure ObservableApprox (φ : (ι → ℝ) → ℝ) (a : ι → ℝ) where
  /-- `φ` vanishes at the minimum. -/
  phi_zero : φ 0 = 0
  /-- Local linear remainder: `|φ(w) - ⟨a, w⟩| ≤ C · ‖w‖²`
  on the closed ball of radius `R`. -/
  local_radius : ℝ
  local_const : ℝ
  local_radius_pos : 0 < local_radius
  local_const_nonneg : 0 ≤ local_const
  local_bound : ∀ w : ι → ℝ, ‖w‖ ≤ local_radius →
    |φ w - dot a w| ≤ local_const * ‖w‖ ^ 2
  /-- Polynomial growth. -/
  poly_growth : HasPolyGrowth φ

/-- **Bundled analytic input for `gibbsCov_first_order_rate_weak`**.

Packages:
- positive-definiteness of `H` (we phrase it via injectivity + a right
  inverse `Hinv`, which is what the column-form moment lemmas use);
- symmetry of `H`;
- positivity of the Gaussian normalising constant `gaussianZ H`;
- the integrability hypotheses needed by `gaussian_dot_mul_dot` and
  the IBP package;
- the Fubini-IBP hypothesis from Phase 4.

In a downstream `GaussianDecay.lean`, all of these will be derived from
`coercive_bound` of `PotentialApprox`. Here we take them as explicit
hypotheses (Option A from the GPT memo). -/
structure LaplaceCovHypotheses
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) where
  H_symm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k
  H_inv_right : H.comp Hinv = ContinuousLinearMap.id ℝ (ι → ℝ)
  H_inj : Function.Injective H
  Z_pos : 0 < gaussianZ H
  int_gW : Integrable (gaussianWeight H)
  int_uk_uj_gW : ∀ k j : ι,
    Integrable (fun u : ι → ℝ => u k * u j * gaussianWeight H u)
  int_uj_Hi_gW : ∀ j i : ι,
    Integrable (fun u : ι → ℝ => u j * (H u) i * gaussianWeight H u)
  fubini_ibp : ∀ i j : ι, FubiniIBPHypothesis H i j

end HypothesisPackage

section GaussianMomentInfrastructure

open MeasureTheory

/-- **Sum-of-squares Gaussian moment integrability**: under
`LaplaceCovHypotheses`, `(∑_i u_i²) · gaussianWeight H u` is integrable. -/
lemma integrable_sum_sq_mul_gaussianWeight
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hGauss : LaplaceCovHypotheses H Hinv) :
    Integrable (fun u : ι → ℝ =>
      (∑ i, (u i) ^ 2) * gaussianWeight H u) := by
  -- Each term `u_i^2 · gW = u_i * u_i * gW` is integrable from
  -- `int_uk_uj_gW i i`. Sum gives `(∑ u_i^2) · gW`.
  have h_each : ∀ i : ι,
      Integrable (fun u : ι → ℝ => (u i) ^ 2 * gaussianWeight H u) := by
    intro i
    have h := hGauss.int_uk_uj_gW i i
    apply h.congr
    filter_upwards with u
    show u i * u i * gaussianWeight H u = u i ^ 2 * gaussianWeight H u
    ring
  have h_sum : Integrable
      (fun u : ι → ℝ => ∑ i, (u i) ^ 2 * gaussianWeight H u) :=
    integrable_finset_sum Finset.univ (fun i _ => h_each i)
  apply h_sum.congr
  filter_upwards with u
  show ∑ i, u i ^ 2 * gaussianWeight H u = (∑ i, u i ^ 2) * gaussianWeight H u
  rw [Finset.sum_mul]

-- Pi-norm coordinate bridges (`abs_apply_le_norm`, `sq_norm_le_sum_sq`,
-- `sum_sq_le_card_mul_sq_norm`) live in `Multi/RescaledIntegrals.lean` so
-- that the coercive-domination lemmas there can use them.

/-- **`‖u‖² · gaussianWeight H u` integrability**: under
`LaplaceCovHypotheses`, dominated pointwise by `(∑ u_i²) · gaussianWeight H u`
which is integrable from `integrable_sum_sq_mul_gaussianWeight`. -/
lemma integrable_sq_norm_mul_gaussianWeight
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hGauss : LaplaceCovHypotheses H Hinv) :
    Integrable (fun u : ι → ℝ => ‖u‖ ^ 2 * gaussianWeight H u) := by
  have h_dom := integrable_sum_sq_mul_gaussianWeight hGauss
  refine h_dom.mono' ?_ ?_
  · -- AE strongly measurable: ‖·‖² · gaussianWeight is continuous.
    have h_quad : Continuous (fun u : ι → ℝ => quadForm H u) := by
      unfold quadForm
      apply continuous_finset_sum
      intro i _
      exact (continuous_apply i).mul ((continuous_apply i).comp H.continuous)
    have h_gW : Continuous (fun u : ι → ℝ => gaussianWeight H u) := by
      unfold gaussianWeight
      exact Real.continuous_exp.comp (continuous_const.mul h_quad)
    exact ((continuous_norm.pow 2).mul h_gW).aestronglyMeasurable
  · filter_upwards with u
    have h_le : ‖u‖ ^ 2 ≤ ∑ i, (u i) ^ 2 := sq_norm_le_sum_sq u
    have h_gW_pos : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    have h_lhs_nn : 0 ≤ ‖u‖ ^ 2 * gaussianWeight H u :=
      mul_nonneg (sq_nonneg _) h_gW_pos
    rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nn]
    exact mul_le_mul_of_nonneg_right h_le h_gW_pos

end GaussianMomentInfrastructure

section AsymptoticIntegrals

/-- **Partition asymptote (weak rate)**.

Under the bundled `LaplaceCovHypotheses` and `PotentialApprox`, the
rescaled partition function approaches `gaussianZ H` at rate `O(1/√t)`:

  `∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
     |rescaledPartition V t - gaussianZ H| ≤ K / √t`.

The proof splits the integral
`rescaledPartition V t - gaussianZ H
  = ∫ gaussianWeight H u · (exp(-rescaledPerturbation V H t u) - 1) du`
into a local region (bounded `‖u‖ ≤ M`) where the rescaled cubic bound
gives `|exp(-s_t) - 1| ≤ K · ‖u‖³ / √t`, and a coercive tail. -/
theorem rescaledPartition_eq_gaussianZ_add_O_inv_sqrt
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    (hV : PotentialApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |rescaledPartition V t - gaussianZ H| ≤ K / Real.sqrt t := by
  -- Constants from hV.
  set c := hV.coercive_const with hc_def
  set R := hV.local_radius with hR_def
  set Cs := hV.local_const with hCs_def
  have hc_pos : 0 < c := hV.coercive_const_pos
  have hR_pos : 0 < R := hV.local_radius_pos
  have hCs_nn : 0 ≤ Cs := hV.local_const_nonneg
  have h_coer := hV.coercive_bound
  have h_local := hV.local_bound
  have hV_cont := hV.V_continuous
  -- Choose δ.
  set δ : ℝ := min R (c / (4 * (Cs + 1))) with hδ_def
  have hCs1_pos : (0 : ℝ) < Cs + 1 := by linarith
  have hδ_pos : 0 < δ := lt_min hR_pos (by positivity)
  have hδ_le_R : δ ≤ R := min_le_left _ _
  have hδ_const : Cs * δ ≤ c / 4 := by
    have h_le : δ ≤ c / (4 * (Cs + 1)) := min_le_right _ _
    calc Cs * δ ≤ Cs * (c / (4 * (Cs + 1))) :=
          mul_le_mul_of_nonneg_left h_le hCs_nn
      _ = (Cs / (Cs + 1)) * (c / 4) := by field_simp
      _ ≤ 1 * (c / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : (0:ℝ) ≤ c/4)
          rw [div_le_one hCs1_pos]; linarith
      _ = c / 4 := one_mul _
  set α : ℝ := c / 4 with hα_def
  set β : ℝ := c * δ ^ 2 / 4 with hβ_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith
  have hβ_pos : 0 < β := by rw [hβ_def]; positivity
  -- M constants.
  set Mlocal : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 3 * Real.exp (-(α * ‖u‖ ^ 2))
    with hMlocal_def
  set Mtail : ℝ := ∫ u : ι → ℝ, Real.exp (-(α * ‖u‖ ^ 2)) with hMtail_def
  have hMlocal_nn : 0 ≤ Mlocal := by
    rw [hMlocal_def]
    apply MeasureTheory.integral_nonneg
    intro u
    exact mul_nonneg (pow_nonneg (norm_nonneg _) 3) (Real.exp_pos _).le
  have hMtail_nn : 0 ≤ Mtail := by
    rw [hMtail_def]
    apply MeasureTheory.integral_nonneg
    intro u
    exact (Real.exp_pos _).le
  -- K and T₀.
  refine ⟨Cs * Mlocal + 2 * Mtail, max 1 (1 / β ^ 2), le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have htβ : 1 / β ^ 2 ≤ t := le_trans (le_max_right _ _) ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_inv_pos : 0 < 1 / Real.sqrt t := by positivity
  -- Integrability + difference identity.
  have h_int_rw :=
    integrable_rescaled_weight V hV_cont H hc_pos h_coer ht_pos
  have h_part_id :=
    rescaledPartition_sub_gaussianZ_eq_integral V H t hGauss.int_gW h_int_rw
  -- F = the integrand.
  set F : (ι → ℝ) → ℝ := fun u =>
    gaussianWeight H u *
      (Real.exp (-(rescaledPerturbation V H t u)) - 1) with hF_def
  -- F integrable.
  have hF_int : MeasureTheory.Integrable F := by
    have h_diff : MeasureTheory.Integrable (fun u : ι → ℝ =>
        gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)) -
          gaussianWeight H u) :=
      h_int_rw.sub hGauss.int_gW
    apply h_diff.congr
    filter_upwards with u
    show gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)) -
        gaussianWeight H u =
      gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)
    ring
  -- Glocal, Gtail majorants.
  set Glocal : (ι → ℝ) → ℝ := fun u =>
    (Cs / Real.sqrt t) * (‖u‖ ^ 3 * Real.exp (-(α * ‖u‖ ^ 2)))
    with hGlocal_def
  set Gtail : (ι → ℝ) → ℝ := fun u =>
    (2 * Real.exp (-(β * t))) * Real.exp (-(α * ‖u‖ ^ 2))
    with hGtail_def
  -- Glocal, Gtail integrable.
  have hGlocal_int : MeasureTheory.Integrable Glocal := by
    rw [hGlocal_def]
    exact (integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hα_pos 3).const_mul _
  have hGtail_int : MeasureTheory.Integrable Gtail := by
    rw [hGtail_def]
    exact (integrable_exp_neg_const_norm_sq (ι := ι) hα_pos).const_mul _
  -- Glocal integral = (Cs/√t) * Mlocal.
  have hGlocal_eq : ∫ u : ι → ℝ, Glocal u = (Cs / Real.sqrt t) * Mlocal := by
    rw [hGlocal_def, hMlocal_def, MeasureTheory.integral_const_mul]
  have hGtail_eq : ∫ u : ι → ℝ, Gtail u = (2 * Real.exp (-(β * t))) * Mtail := by
    rw [hGtail_def, hMtail_def, MeasureTheory.integral_const_mul]
  -- Pointwise bound |F u| ≤ Glocal u + Gtail u.
  have hpt : ∀ u : ι → ℝ, |F u| ≤ Glocal u + Gtail u := by
    intro u
    by_cases hu : ‖u‖ ≤ δ * Real.sqrt t
    · -- Local case
      have h_local_bound :=
        abs_gaussianWeight_mul_exp_sub_one_le_local V H hc_pos hR_pos hCs_nn
          h_coer h_local hδ_pos hδ_le_R hδ_const ht_pos u hu
      have h_match :
          (Cs * ‖u‖ ^ 3 / Real.sqrt t) * Real.exp (-((c / 4) * ‖u‖ ^ 2))
            = Glocal u := by
        rw [hGlocal_def, hα_def]
        ring
      have h_F_le : |F u| ≤ Glocal u := by
        rw [hF_def]
        rw [← h_match]
        exact h_local_bound
      have h_tail_nn : 0 ≤ Gtail u := by
        rw [hGtail_def]
        exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
          (Real.exp_pos _).le
      linarith
    · -- Tail case
      push_neg at hu
      have h_tail_bound :=
        abs_gaussianWeight_mul_exp_sub_one_le_tail V H hc_pos hR_pos hCs_nn
          h_coer h_local hδ_pos ht_pos u hu
      have h_match :
          2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
              Real.exp (-((c * δ ^ 2 / 4) * t)) = Gtail u := by
        rw [hGtail_def, hα_def, hβ_def]
        ring
      have h_F_le : |F u| ≤ Gtail u := by
        rw [hF_def]
        rw [← h_match]
        exact h_tail_bound
      have h_loc_nn : 0 ≤ Glocal u := by
        rw [hGlocal_def]
        positivity
      linarith
  -- Final calculation.
  have htail_sqrt : Real.exp (-(β * t)) ≤ 1 / Real.sqrt t :=
    exp_neg_const_mul_le_inv_sqrt hβ_pos htβ
  calc |rescaledPartition V t - gaussianZ H|
      = |∫ u : ι → ℝ, F u| := by rw [h_part_id]
    _ ≤ ∫ u : ι → ℝ, |F u| := by
          rw [show |∫ u : ι → ℝ, F u| = ‖∫ u : ι → ℝ, F u‖ from
            (Real.norm_eq_abs _).symm]
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ u : ι → ℝ, (Glocal u + Gtail u) := by
          apply MeasureTheory.integral_mono_ae hF_int.norm
            (hGlocal_int.add hGtail_int)
          filter_upwards with u
          rw [Real.norm_eq_abs]
          exact hpt u
    _ = (∫ u : ι → ℝ, Glocal u) + ∫ u : ι → ℝ, Gtail u :=
          MeasureTheory.integral_add hGlocal_int hGtail_int
    _ = (Cs / Real.sqrt t) * Mlocal + (2 * Real.exp (-(β * t))) * Mtail := by
          rw [hGlocal_eq, hGtail_eq]
    _ ≤ (Cs / Real.sqrt t) * Mlocal + (2 * (1 / Real.sqrt t)) * Mtail := by
          have h_step : (2 * Real.exp (-(β * t))) * Mtail
              ≤ (2 * (1 / Real.sqrt t)) * Mtail := by
            apply mul_le_mul_of_nonneg_right _ hMtail_nn
            apply mul_le_mul_of_nonneg_left htail_sqrt (by norm_num : (0:ℝ) ≤ 2)
          linarith
    _ = (Cs * Mlocal + 2 * Mtail) / Real.sqrt t := by
          field_simp

/-- **Denominator lower bound** for `t` large enough:
`gaussianZ H / 2 ≤ rescaledPartition V t`.

Direct corollary of the partition asymptote: for `t ≥ ((2|K|)/Z)²`,
`|partition - Z| ≤ |K|/√t ≤ Z/2`, hence `partition ≥ Z - Z/2 = Z/2`. -/
theorem rescaledPartition_ge_half_gaussianZ
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    (hV : PotentialApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ t : ℝ, T₁ ≤ t →
      gaussianZ H / 2 ≤ rescaledPartition V t := by
  obtain ⟨K, T, hT, hpart⟩ :=
    rescaledPartition_eq_gaussianZ_add_O_inv_sqrt V H Hinv hV hGauss
  refine ⟨max T (max 1 (((2 * |K|) / gaussianZ H) ^ 2)),
    le_max_of_le_right (le_max_left _ _), ?_⟩
  intro t ht
  have htT : T ≤ t := le_of_max_le_left ht
  have ht' : max 1 (((2 * |K|) / gaussianZ H) ^ 2) ≤ t := le_of_max_le_right ht
  have ht1 : 1 ≤ t := le_of_max_le_left ht'
  have htsq : ((2 * |K|) / gaussianZ H) ^ 2 ≤ t := le_of_max_le_right ht'
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hZ_pos := hGauss.Z_pos
  have hpart' : |rescaledPartition V t - gaussianZ H| ≤ |K| / Real.sqrt t := by
    calc |rescaledPartition V t - gaussianZ H|
        ≤ K / Real.sqrt t := hpart t htT
      _ ≤ |K| / Real.sqrt t :=
          div_le_div_of_nonneg_right (le_abs_self K) hsqrt_pos.le
  have h_K_div_nn : 0 ≤ (2 * |K|) / gaussianZ H :=
    div_nonneg (by positivity) hZ_pos.le
  have h_sqrt_lb : (2 * |K|) / gaussianZ H ≤ Real.sqrt t := by
    have h := Real.sqrt_le_sqrt htsq
    rw [Real.sqrt_sq h_K_div_nn] at h
    exact h
  have hhalf : |K| / Real.sqrt t ≤ gaussianZ H / 2 := by
    rw [div_le_div_iff₀ hsqrt_pos (by linarith : (0:ℝ) < 2)]
    rw [div_le_iff₀ hZ_pos] at h_sqrt_lb
    linarith
  have habs_le := abs_le.mp hpart'
  linarith

/-- **Linear-correction bound (in-progress, contains internal sorries)**:
for the linear part `(1/√t) · ⟨a, u⟩` of the rescaled observable, the
correction `∫ ⟨a, u⟩ · gW · (exp(-s_t) - 1) du` is `O(1/√t)`.

The GPT-5.5 Pro "linear correction" bound from Q5. The proof structure
mirrors the partition asymptote with an extra `|⟨a, u⟩| ≤ A · ‖u‖`
factor; integrability of `dot a u · rescaledWeight` and `dot a u · gW`
remain as internal sorries (each follows from `‖u‖ · rescaledWeight`
integrability + the `abs_dot_le_l1_mul_norm` bound). -/
private lemma abs_integral_dot_mul_rescaled_weight_correction_le
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |∫ u : ι → ℝ, dot a u * gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
        ≤ K / Real.sqrt t := by
  -- Constants from hV (same as partition asymptote).
  set c := hV.coercive_const with hc_def
  set R := hV.local_radius with hR_def
  set Cs := hV.local_const with hCs_def
  have hc_pos : 0 < c := hV.coercive_const_pos
  have hR_pos : 0 < R := hV.local_radius_pos
  have hCs_nn : 0 ≤ Cs := hV.local_const_nonneg
  have h_coer := hV.coercive_bound
  have h_local := hV.local_bound
  set δ : ℝ := min R (c / (4 * (Cs + 1))) with hδ_def
  have hCs1_pos : (0 : ℝ) < Cs + 1 := by linarith
  have hδ_pos : 0 < δ := lt_min hR_pos (by positivity)
  have hδ_le_R : δ ≤ R := min_le_left _ _
  have hδ_const : Cs * δ ≤ c / 4 := by
    have h_le : δ ≤ c / (4 * (Cs + 1)) := min_le_right _ _
    calc Cs * δ ≤ Cs * (c / (4 * (Cs + 1))) :=
          mul_le_mul_of_nonneg_left h_le hCs_nn
      _ = (Cs / (Cs + 1)) * (c / 4) := by field_simp
      _ ≤ 1 * (c / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : (0:ℝ) ≤ c/4)
          rw [div_le_one hCs1_pos]; linarith
      _ = c / 4 := one_mul _
  set α : ℝ := c / 4 with hα_def
  set β : ℝ := c * δ ^ 2 / 4 with hβ_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith
  have hβ_pos : 0 < β := by rw [hβ_def]; positivity
  set A : ℝ := ∑ i, |a i| with hA_def
  have hA_nn : 0 ≤ A := by rw [hA_def]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  -- M constants for the integral bounds.
  set M4 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 4 * Real.exp (-(α * ‖u‖ ^ 2)) with hM4_def
  set M1 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 1 * Real.exp (-(α * ‖u‖ ^ 2)) with hM1_def
  have hM4_nn : 0 ≤ M4 := by
    rw [hM4_def]
    apply MeasureTheory.integral_nonneg
    intro u
    exact mul_nonneg (pow_nonneg (norm_nonneg _) 4) (Real.exp_pos _).le
  have hM1_nn : 0 ≤ M1 := by
    rw [hM1_def]
    apply MeasureTheory.integral_nonneg
    intro u
    exact mul_nonneg (pow_nonneg (norm_nonneg _) 1) (Real.exp_pos _).le
  -- K and T₀.
  refine ⟨A * Cs * M4 + 2 * A * M1, max 1 (1 / β ^ 2), le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have htβ : 1 / β ^ 2 ≤ t := le_trans (le_max_right _ _) ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  -- Integrability of the integrand.
  have h_int_rw :=
    integrable_rescaled_weight V hV.V_continuous H hc_pos h_coer ht_pos
  have h_int_norm :=
    integrable_pow_norm_mul_rescaled_weight V hV.V_continuous H hc_pos h_coer 1 ht_pos
  -- The linear-times-rescaled integrand.
  set F : (ι → ℝ) → ℝ := fun u =>
    dot a u * gaussianWeight H u *
      (Real.exp (-(rescaledPerturbation V H t u)) - 1) with hF_def
  have hF_int : MeasureTheory.Integrable F := by
    have h_diff : MeasureTheory.Integrable (fun u : ι → ℝ =>
        dot a u * (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) -
          dot a u * gaussianWeight H u) := by
      have h_lin1 : MeasureTheory.Integrable (fun u : ι → ℝ =>
          dot a u * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))) := by
        -- Bound by A · ‖u‖ · rescaledWeight, dominated by
        -- `integrable_pow_norm_mul_rescaled_weight` (k = 1).
        have h_dom : MeasureTheory.Integrable (fun u : ι → ℝ =>
            A * (‖u‖ ^ 1 *
              (gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u))))) :=
          (integrable_pow_norm_mul_rescaled_weight V hV.V_continuous H
            hc_pos h_coer 1 ht_pos).const_mul A
        refine h_dom.mono' ?_ ?_
        · -- AE strongly measurable.
          have h_dot_cont : Continuous (fun u : ι → ℝ => dot a u) := by
            unfold dot
            apply continuous_finset_sum
            intro i _
            exact continuous_const.mul (continuous_apply i)
          have h_rw_cont :
              Continuous (fun u : ι → ℝ =>
                gaussianWeight H u *
                  Real.exp (-(rescaledPerturbation V H t u))) :=
            (continuous_gaussianWeight H).mul
              (Real.continuous_exp.comp
                (continuous_rescaledPerturbation hV.V_continuous H t).neg)
          exact (h_dot_cont.mul h_rw_cont).aestronglyMeasurable
        · filter_upwards with u
          have h_dot_le : |dot a u| ≤ A * ‖u‖ := by
            rw [hA_def]; exact abs_dot_le_l1_mul_norm a u
          have h_rw_nn : 0 ≤ gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)) :=
            mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_rw_nn]
          calc |dot a u| * (gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))
              ≤ A * ‖u‖ * (gaussianWeight H u *
                  Real.exp (-(rescaledPerturbation V H t u))) :=
                mul_le_mul_of_nonneg_right h_dot_le h_rw_nn
            _ = A * (‖u‖ ^ 1 *
                  (gaussianWeight H u *
                    Real.exp (-(rescaledPerturbation V H t u)))) := by
                rw [pow_one]; ring
      have h_lin2 : MeasureTheory.Integrable (fun u : ι → ℝ =>
          dot a u * gaussianWeight H u) := by
        -- Bound by A · ‖u‖ · gW. The latter is integrable from the
        -- second-moment package: ‖u‖ ≤ 1 + ‖u‖², and ‖u‖² · gW is
        -- integrable (`integrable_sq_norm_mul_gaussianWeight`).
        have h_dom : MeasureTheory.Integrable (fun u : ι → ℝ =>
            A * (gaussianWeight H u + ‖u‖ ^ 2 * gaussianWeight H u)) := by
          have h_int_sq := integrable_sq_norm_mul_gaussianWeight hGauss
          have h_int_gW := hGauss.int_gW
          have h_sum : MeasureTheory.Integrable (fun u : ι → ℝ =>
              gaussianWeight H u + ‖u‖ ^ 2 * gaussianWeight H u) :=
            h_int_gW.add h_int_sq
          exact h_sum.const_mul A
        refine h_dom.mono' ?_ ?_
        · have h_dot_cont : Continuous (fun u : ι → ℝ => dot a u) := by
            unfold dot
            apply continuous_finset_sum
            intro i _
            exact continuous_const.mul (continuous_apply i)
          exact (h_dot_cont.mul (continuous_gaussianWeight H)).aestronglyMeasurable
        · filter_upwards with u
          have h_dot_le : |dot a u| ≤ A * ‖u‖ := by
            rw [hA_def]; exact abs_dot_le_l1_mul_norm a u
          have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
          have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_gW_nn]
          calc |dot a u| * gaussianWeight H u
              ≤ A * ‖u‖ * gaussianWeight H u :=
                mul_le_mul_of_nonneg_right h_dot_le h_gW_nn
            _ = A * (‖u‖ * gaussianWeight H u) := by ring
            _ ≤ A * ((1 + ‖u‖ ^ 2) * gaussianWeight H u) := by
                apply mul_le_mul_of_nonneg_left _ hA_nn
                apply mul_le_mul_of_nonneg_right _ h_gW_nn
                -- ‖u‖ ≤ 1 + ‖u‖²: split on ‖u‖ ≤ 1 vs > 1.
                by_cases h1 : ‖u‖ ≤ 1
                · linarith [sq_nonneg ‖u‖]
                · push_neg at h1
                  have h_sq_le : ‖u‖ ≤ ‖u‖ ^ 2 := by
                    have := mul_le_mul_of_nonneg_left h1.le h_norm_nn
                    rw [mul_one] at this
                    rw [show ‖u‖ ^ 2 = ‖u‖ * ‖u‖ from sq _]
                    exact this
                  linarith
            _ = A * (gaussianWeight H u + ‖u‖ ^ 2 * gaussianWeight H u) := by ring
      exact h_lin1.sub h_lin2
    apply h_diff.congr
    filter_upwards with u
    show dot a u * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) -
        dot a u * gaussianWeight H u =
      dot a u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)
    ring
  -- Glocal, Gtail majorants.
  set Glocal : (ι → ℝ) → ℝ := fun u =>
    (A * Cs / Real.sqrt t) * (‖u‖ ^ 4 * Real.exp (-(α * ‖u‖ ^ 2))) with hGlocal_def
  set Gtail : (ι → ℝ) → ℝ := fun u =>
    (2 * A * Real.exp (-(β * t))) *
      (‖u‖ ^ 1 * Real.exp (-(α * ‖u‖ ^ 2))) with hGtail_def
  have hGlocal_int : MeasureTheory.Integrable Glocal := by
    rw [hGlocal_def]
    exact (integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hα_pos 4).const_mul _
  have hGtail_int : MeasureTheory.Integrable Gtail := by
    rw [hGtail_def]
    exact (integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hα_pos 1).const_mul _
  have hGlocal_eq : ∫ u : ι → ℝ, Glocal u = (A * Cs / Real.sqrt t) * M4 := by
    rw [hGlocal_def, hM4_def, MeasureTheory.integral_const_mul]
  have hGtail_eq : ∫ u : ι → ℝ, Gtail u = (2 * A * Real.exp (-(β * t))) * M1 := by
    rw [hGtail_def, hM1_def, MeasureTheory.integral_const_mul]
  -- Pointwise bound |F u| ≤ Glocal u + Gtail u.
  have hpt : ∀ u : ι → ℝ, |F u| ≤ Glocal u + Gtail u := by
    intro u
    have h_dot : |dot a u| ≤ A * ‖u‖ := by
      rw [hA_def]; exact abs_dot_le_l1_mul_norm a u
    by_cases hu : ‖u‖ ≤ δ * Real.sqrt t
    · -- Local
      have h_local_part :=
        abs_gaussianWeight_mul_exp_sub_one_le_local V H hc_pos hR_pos hCs_nn
          h_coer h_local hδ_pos hδ_le_R hδ_const ht_pos u hu
      have h_F_local : |F u| ≤ A * ‖u‖ *
          ((Cs * ‖u‖ ^ 3 / Real.sqrt t) * Real.exp (-((c / 4) * ‖u‖ ^ 2))) := by
        show |dot a u * gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
            ≤ A * ‖u‖ *
              ((Cs * ‖u‖ ^ 3 / Real.sqrt t) * Real.exp (-((c / 4) * ‖u‖ ^ 2)))
        rw [show dot a u * gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            = dot a u * (gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)) from by ring]
        rw [abs_mul]
        apply mul_le_mul h_dot h_local_part (abs_nonneg _) (mul_nonneg hA_nn (norm_nonneg _))
      have h_match :
          A * ‖u‖ *
            ((Cs * ‖u‖ ^ 3 / Real.sqrt t) * Real.exp (-((c / 4) * ‖u‖ ^ 2)))
            = Glocal u := by
        rw [hGlocal_def, hα_def]
        ring
      rw [h_match] at h_F_local
      have h_tail_nn : 0 ≤ Gtail u := by
        rw [hGtail_def]
        positivity
      linarith
    · -- Tail
      push_neg at hu
      have h_tail_part :=
        abs_gaussianWeight_mul_exp_sub_one_le_tail V H hc_pos hR_pos hCs_nn
          h_coer h_local hδ_pos ht_pos u hu
      have h_F_tail : |F u| ≤ A * ‖u‖ *
          (2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) * Real.exp (-((c * δ ^ 2 / 4) * t))) := by
        show |dot a u * gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
            ≤ A * ‖u‖ *
              (2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
                Real.exp (-((c * δ ^ 2 / 4) * t)))
        rw [show dot a u * gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            = dot a u * (gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)) from by ring]
        rw [abs_mul]
        apply mul_le_mul h_dot h_tail_part (abs_nonneg _) (mul_nonneg hA_nn (norm_nonneg _))
      have h_match :
          A * ‖u‖ *
            (2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
              Real.exp (-((c * δ ^ 2 / 4) * t)))
            = Gtail u := by
        show A * ‖u‖ *
            (2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
              Real.exp (-((c * δ ^ 2 / 4) * t)))
            = (2 * A * Real.exp (-(β * t))) *
              (‖u‖ ^ 1 * Real.exp (-(α * ‖u‖ ^ 2)))
        rw [hα_def, hβ_def, pow_one]
        ring
      rw [h_match] at h_F_tail
      have h_loc_nn : 0 ≤ Glocal u := by
        rw [hGlocal_def]
        positivity
      linarith
  -- Final calculation.
  have htail_sqrt : Real.exp (-(β * t)) ≤ 1 / Real.sqrt t :=
    exp_neg_const_mul_le_inv_sqrt hβ_pos htβ
  calc |∫ u : ι → ℝ, dot a u * gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      = |∫ u : ι → ℝ, F u| := rfl
    _ ≤ ∫ u : ι → ℝ, |F u| := by
          rw [show |∫ u : ι → ℝ, F u| = ‖∫ u : ι → ℝ, F u‖ from
            (Real.norm_eq_abs _).symm]
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ u : ι → ℝ, (Glocal u + Gtail u) := by
          apply MeasureTheory.integral_mono_ae hF_int.norm
            (hGlocal_int.add hGtail_int)
          filter_upwards with u
          rw [Real.norm_eq_abs]
          exact hpt u
    _ = (∫ u : ι → ℝ, Glocal u) + ∫ u : ι → ℝ, Gtail u :=
          MeasureTheory.integral_add hGlocal_int hGtail_int
    _ = (A * Cs / Real.sqrt t) * M4 + (2 * A * Real.exp (-(β * t))) * M1 := by
          rw [hGlocal_eq, hGtail_eq]
    _ ≤ (A * Cs / Real.sqrt t) * M4 + (2 * A * (1 / Real.sqrt t)) * M1 := by
          have h_step : (2 * A * Real.exp (-(β * t))) * M1
              ≤ (2 * A * (1 / Real.sqrt t)) * M1 := by
            apply mul_le_mul_of_nonneg_right _ hM1_nn
            apply mul_le_mul_of_nonneg_left htail_sqrt
              (by positivity : (0:ℝ) ≤ 2 * A)
          linarith
    _ = (A * Cs * M4 + 2 * A * M1) / Real.sqrt t := by field_simp

/-- **Remainder bound (placeholder)**: for the rescaled-observable
remainder `rem(u) = φ((√t)⁻¹ u) - (√t)⁻¹ · ⟨a, u⟩`, the integral
`∫ rem(u) · gW · exp(-rescaledPerturbation) du` is `O(1/t)`.

The local part follows from `abs_rescaledObservable_linear_error_le`
(quadratic remainder bound `|rem| ≤ Cφ·‖u‖²/t` on `‖u‖ ≤ R√t`),
combined with `rescaled_weight_le_coercive` and integrability of
`‖u‖² · exp(-c‖u‖²)`. The tail requires polynomial growth of `φ`
(`HasPolyGrowth`) plus exponential rescaled-weight decay.

Substantial integral assembly omitted; see `gpt_responses/phase5_assembly.md`
for the recipe. -/
private lemma abs_integral_remainder_mul_rescaled_weight_le
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialApprox V H)
    (hφ : ObservableApprox φ a)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |∫ u : ι → ℝ,
          (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))|
        ≤ K / t := by
  sorry  -- ~150 LOC structurally same as linear-correction but with ‖u‖² · exp instead of ‖u‖⁴ · exp

/-- **Quotient reduction lemma**: from a numerator bound, deduce the
expectation bound via the denominator lower bound. -/
private lemma rescaledExpectation_observable_bound_inv_of_num
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    (hV : PotentialApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv)
    (h_num_bound : ∃ K_N T_N : ℝ, 1 ≤ T_N ∧ ∀ t : ℝ, T_N ≤ t →
      |rescaledNumerator V t φ| ≤ K_N / t) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |rescaledExpectation V t φ| ≤ K / t := by
  obtain ⟨K_N, T_N, hT_N, hN⟩ := h_num_bound
  obtain ⟨T_D, hT_D, hD⟩ :=
    rescaledPartition_ge_half_gaussianZ V H Hinv hV hGauss
  have hZ_pos := hGauss.Z_pos
  refine ⟨2 * K_N / gaussianZ H, max T_N T_D, le_max_of_le_left hT_N, ?_⟩
  intro t ht
  have htN : T_N ≤ t := le_of_max_le_left ht
  have htD : T_D ≤ t := le_of_max_le_right ht
  have ht_pos : 0 < t := lt_of_lt_of_le (by linarith [hT_N]) htN
  have hD_t : gaussianZ H / 2 ≤ rescaledPartition V t := hD t htD
  have hD_pos : 0 < rescaledPartition V t :=
    lt_of_lt_of_le (by linarith) hD_t
  have hN_t : |rescaledNumerator V t φ| ≤ K_N / t := hN t htN
  calc |rescaledExpectation V t φ|
      = |rescaledNumerator V t φ| / rescaledPartition V t := by
        unfold rescaledExpectation
        rw [abs_div, abs_of_pos hD_pos]
    _ ≤ |rescaledNumerator V t φ| / (gaussianZ H / 2) := by
        apply div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hD_t
    _ ≤ (K_N / t) / (gaussianZ H / 2) := by
        apply div_le_div_of_nonneg_right hN_t (by linarith)
    _ = (2 * K_N / gaussianZ H) / t := by
        field_simp

/-- **Single-observable asymptote (weak rate)**.

For an observable `φ` with gradient `a`, `rescaledExpectation V t φ` is
`O(1/t)`:

  `∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
     |rescaledExpectation V t φ| ≤ K / t`.

The leading-order term of `rescaledExpectation V t φ` would be
`(1/√t) · ⟨a, ⟨u⟩_t⟩` but the linear-times-Gaussian integral vanishes
by oddness (`integral_odd_mul_gaussian_eq_zero`); the residual is
`O(1/t)` from the quadratic remainder of `φ` and the cubic perturbation
`s_t = O(‖u‖³ / √t)`. -/
theorem rescaledExpectation_observable_bound_inv
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialApprox V H)
    (_hφ : ObservableApprox φ a)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |rescaledExpectation V t φ| ≤ K / t := by
  apply rescaledExpectation_observable_bound_inv_of_num V φ H Hinv hV hGauss
  -- Numerator bound `|N_t(φ)| ≤ K/t`: composes
  -- (1) `abs_integral_dot_mul_rescaled_weight_correction_le` for the linear
  --     part (gives `|(1/√t)·I_lin| = K_lc/t` since the leading
  --     `∫ ⟨a,u⟩·gW = 0` cancels by oddness),
  -- (2) `abs_integral_remainder_mul_rescaled_weight_le` for the remainder
  --     (gives `|I_rem| ≤ K_r/t`),
  -- via `rescaledNumerator_eq_linear_plus_remainder` (with appropriate
  -- integrability hypotheses) and triangle inequality. Substantial
  -- integral-bookkeeping omitted.
  sorry

-- (Theorem statement moved below the private quotient-reduction lemma; see
-- `rescaledExpectation_pair_eq_main_add_O_inv_sqrt` further down.)

/-- **Pair quotient reduction lemma**: from a pair-numerator asymptote
plus the partition asymptote, derive the pair expectation asymptote.

Uses the algebraic identity
`N_t/D_t - m = (N_t - Zm)/D_t + m·(Z - D_t)/D_t` (per GPT-5.5 Pro
Phase 5 assembly memo Q6) plus the denominator lower bound. -/
private lemma rescaledExpectation_pair_eq_main_add_O_inv_sqrt_of_num
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (φψ : (ι → ℝ) → ℝ) (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv)
    (h_num_bound : ∃ K_N T_N : ℝ, 1 ≤ T_N ∧ ∀ t : ℝ, T_N ≤ t →
      |t * rescaledNumerator V t φψ - gaussianZ H * dot a (Hinv b)|
        ≤ K_N / Real.sqrt t) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * rescaledExpectation V t φψ - dot a (Hinv b)| ≤ K / Real.sqrt t := by
  obtain ⟨K_N, T_N, hT_N, hN⟩ := h_num_bound
  obtain ⟨T_D, hT_D, hD⟩ :=
    rescaledPartition_ge_half_gaussianZ V H Hinv hV hGauss
  obtain ⟨K_part, T_part, hT_part, hpart⟩ :=
    rescaledPartition_eq_gaussianZ_add_O_inv_sqrt V H Hinv hV hGauss
  have hZ_pos := hGauss.Z_pos
  -- Construct K and T₀.
  set m : ℝ := dot a (Hinv b) with hm_def
  set K : ℝ := 2 * K_N / gaussianZ H + 2 * |m| * |K_part| / gaussianZ H
    with hK_def
  refine ⟨K, max T_N (max T_D T_part), ?_, ?_⟩
  · exact le_max_of_le_left hT_N
  · intro t ht
    have htN : T_N ≤ t := le_of_max_le_left ht
    have ht' : max T_D T_part ≤ t := le_of_max_le_right ht
    have htD : T_D ≤ t := le_of_max_le_left ht'
    have htP : T_part ≤ t := le_of_max_le_right ht'
    have ht_pos : 0 < t := lt_of_lt_of_le (by linarith [hT_N]) htN
    have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
    have hD_t : gaussianZ H / 2 ≤ rescaledPartition V t := hD t htD
    have hD_pos : 0 < rescaledPartition V t :=
      lt_of_lt_of_le (by linarith) hD_t
    have hN_t : |t * rescaledNumerator V t φψ - gaussianZ H * m| ≤
        K_N / Real.sqrt t := hN t htN
    have hpart_t : |rescaledPartition V t - gaussianZ H| ≤
        K_part / Real.sqrt t := hpart t htP
    have hpart_t' : |rescaledPartition V t - gaussianZ H| ≤
        |K_part| / Real.sqrt t :=
      le_trans hpart_t (div_le_div_of_nonneg_right (le_abs_self _) hsqrt_pos.le)
    -- Algebraic decomposition:
    -- t·E_t - m = t·N_t/D_t - m = (t·N_t - Z·m)/D_t + m·(Z - D_t)/D_t.
    have h_alg :
        t * rescaledExpectation V t φψ - m
          = (t * rescaledNumerator V t φψ - gaussianZ H * m) /
              rescaledPartition V t
            + m * (gaussianZ H - rescaledPartition V t) /
              rescaledPartition V t := by
      unfold rescaledExpectation
      field_simp
      ring
    rw [h_alg]
    -- Triangle inequality.
    have h_tri :
        |(t * rescaledNumerator V t φψ - gaussianZ H * m) /
              rescaledPartition V t
            + m * (gaussianZ H - rescaledPartition V t) /
              rescaledPartition V t|
          ≤ |(t * rescaledNumerator V t φψ - gaussianZ H * m) /
                rescaledPartition V t|
            + |m * (gaussianZ H - rescaledPartition V t) /
                rescaledPartition V t| := abs_add_le _ _
    refine le_trans h_tri ?_
    -- First piece: |(N_t - Z·m)/D_t| ≤ (K_N/√t) / (Z/2) = 2K_N / (Z · √t).
    have h_part1 :
        |(t * rescaledNumerator V t φψ - gaussianZ H * m) /
            rescaledPartition V t|
          ≤ 2 * K_N / gaussianZ H / Real.sqrt t := by
      rw [abs_div, abs_of_pos hD_pos]
      calc |t * rescaledNumerator V t φψ - gaussianZ H * m| /
              rescaledPartition V t
          ≤ |t * rescaledNumerator V t φψ - gaussianZ H * m| /
              (gaussianZ H / 2) :=
            div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hD_t
        _ ≤ (K_N / Real.sqrt t) / (gaussianZ H / 2) :=
            div_le_div_of_nonneg_right hN_t (by linarith)
        _ = 2 * K_N / gaussianZ H / Real.sqrt t := by field_simp
    -- Second piece: |m·(Z - D_t)/D_t| ≤ |m| · (|K_part|/√t) / (Z/2) = 2|m|·|K_part|/(Z·√t).
    have h_part2 :
        |m * (gaussianZ H - rescaledPartition V t) /
            rescaledPartition V t|
          ≤ 2 * |m| * |K_part| / gaussianZ H / Real.sqrt t := by
      rw [abs_div, abs_of_pos hD_pos, abs_mul]
      have habs_diff_eq : |gaussianZ H - rescaledPartition V t|
          = |rescaledPartition V t - gaussianZ H| := abs_sub_comm _ _
      rw [habs_diff_eq]
      calc |m| * |rescaledPartition V t - gaussianZ H| /
              rescaledPartition V t
          ≤ |m| * (|K_part| / Real.sqrt t) / rescaledPartition V t := by
            apply div_le_div_of_nonneg_right _ hD_pos.le
            apply mul_le_mul_of_nonneg_left hpart_t' (abs_nonneg _)
        _ ≤ |m| * (|K_part| / Real.sqrt t) / (gaussianZ H / 2) := by
            apply div_le_div_of_nonneg_left
              (mul_nonneg (abs_nonneg _) (div_nonneg (abs_nonneg _) hsqrt_pos.le))
              (by linarith) hD_t
        _ = 2 * |m| * |K_part| / gaussianZ H / Real.sqrt t := by field_simp
    -- Combine.
    calc |(t * rescaledNumerator V t φψ - gaussianZ H * m) /
              rescaledPartition V t|
          + |m * (gaussianZ H - rescaledPartition V t) /
              rescaledPartition V t|
        ≤ 2 * K_N / gaussianZ H / Real.sqrt t
            + 2 * |m| * |K_part| / gaussianZ H / Real.sqrt t :=
          add_le_add h_part1 h_part2
      _ = K / Real.sqrt t := by rw [hK_def]; ring

theorem rescaledExpectation_pair_eq_main_add_O_inv_sqrt
    (V φ ψ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialApprox V H)
    (_hφ : ObservableApprox φ a)
    (_hψ : ObservableApprox ψ b)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b)|
        ≤ K / Real.sqrt t := by
  apply rescaledExpectation_pair_eq_main_add_O_inv_sqrt_of_num
    V H Hinv (fun w => φ w * ψ w) a b hV hGauss
  -- The pair-numerator asymptote follows from `pair_product_expansion` +
  -- `gaussian_dot_mul_dot` for the leading term + bounds for cross/quadratic
  -- residuals. Substantial integral assembly omitted here.
  sorry

end AsymptoticIntegrals

section MainStatement

/-- **`lem:laplace_cov` (weak-rate version, statement only)**.

For potential `V` with quadratic part `H`, observables `φ, ψ` with
gradients `a, b`, and analytic hypotheses bundled in `LaplaceCovHypotheses`,

  `∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
     |t · gibbsCov V t φ ψ - ⟨a, Hinv b⟩| ≤ K / Real.sqrt t`.

This is the weak track per the GPT-5.5 Pro memo. The sharp `O(t⁻²)`
track requires parity-resolved jets and odd-Gaussian vanishing, and is
deferred to a follow-on file `Covariance.Sharp.lean`.

The proof is in progress; statement is locked in here so that downstream
work can rely on the hypothesis package. -/
theorem gibbsCov_first_order_rate_weak
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialApprox V H)
    (hφ : ObservableApprox φ a)
    (hψ : ObservableApprox ψ b)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / Real.sqrt t := by
  -- Pull asymptote constants from the three asymptote stubs.
  obtain ⟨K_pair, T_pair, hT_pair, h_pair⟩ :=
    rescaledExpectation_pair_eq_main_add_O_inv_sqrt V φ ψ H Hinv a b hV hφ hψ hGauss
  obtain ⟨K_phi, T_phi, hT_phi, h_phi⟩ :=
    rescaledExpectation_observable_bound_inv V φ H Hinv a hV hφ hGauss
  obtain ⟨K_psi, T_psi, hT_psi, h_psi⟩ :=
    rescaledExpectation_observable_bound_inv V ψ H Hinv b hV hψ hGauss
  -- K and T₀ bookkeeping.
  refine ⟨K_pair + |K_phi * K_psi|, max T_pair (max T_phi T_psi), ?_, ?_⟩
  · -- 1 ≤ max T_pair (max T_phi T_psi).
    exact le_max_of_le_left hT_pair
  · intro t ht_max
    have ht_pair : T_pair ≤ t := le_of_max_le_left ht_max
    have ht_other : max T_phi T_psi ≤ t := le_of_max_le_right ht_max
    have ht_phi : T_phi ≤ t := le_of_max_le_left ht_other
    have ht_psi : T_psi ≤ t := le_of_max_le_right ht_other
    have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hT_pair) ht_pair
    -- Switch to rescaled side.
    rw [gibbsCov_eq_rescaledCov V φ ψ ht_pos]
    unfold rescaledCov
    -- t · (E[φψ] - E[φ]·E[ψ]) = (t · E[φψ]) - (t · E[φ] · E[ψ]).
    -- Apply triangle inequality.
    have hpair_use := h_pair t ht_pair
    have hphi_use := h_phi t ht_phi
    have hpsi_use := h_psi t ht_psi
    have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
    have ht_ge_one : 1 ≤ t := le_trans hT_pair ht_pair
    have hsqrt_ge_one : 1 ≤ Real.sqrt t :=
      Real.one_le_sqrt.mpr ht_ge_one
    -- Step A: bound the cross term `t · E[φ] · E[ψ]`.
    have habs_phi_nonneg : 0 ≤ K_phi / t :=
      le_trans (abs_nonneg _) hphi_use
    have habs_psi_nonneg : 0 ≤ K_psi / t :=
      le_trans (abs_nonneg _) hpsi_use
    have h_cross :
        |t * (rescaledExpectation V t φ * rescaledExpectation V t ψ)|
          ≤ |K_phi * K_psi| / t := by
      rw [abs_mul, abs_of_pos ht_pos, abs_mul]
      have h_prod_le :
          |rescaledExpectation V t φ| * |rescaledExpectation V t ψ|
            ≤ (K_phi / t) * (K_psi / t) :=
        mul_le_mul hphi_use hpsi_use (abs_nonneg _) habs_phi_nonneg
      have h1 : t * (|rescaledExpectation V t φ| * |rescaledExpectation V t ψ|)
          ≤ t * ((K_phi / t) * (K_psi / t)) :=
        mul_le_mul_of_nonneg_left h_prod_le ht_pos.le
      have h2 : t * ((K_phi / t) * (K_psi / t)) = K_phi * K_psi / t := by
        field_simp
      have h3 : K_phi * K_psi / t ≤ |K_phi * K_psi| / t :=
        div_le_div_of_nonneg_right (le_abs_self _) ht_pos.le
      linarith
    -- Step B: triangle inequality.
    have h_split :
        t * (rescaledExpectation V t (fun w => φ w * ψ w)
              - rescaledExpectation V t φ * rescaledExpectation V t ψ)
            - dot a (Hinv b)
        = (t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b))
            - t * (rescaledExpectation V t φ * rescaledExpectation V t ψ) := by
      ring
    rw [h_split]
    calc |(t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b))
              - t * (rescaledExpectation V t φ * rescaledExpectation V t ψ)|
        ≤ |t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b)|
            + |t * (rescaledExpectation V t φ * rescaledExpectation V t ψ)| := by
          exact abs_sub _ _
      _ ≤ K_pair / Real.sqrt t + |K_phi * K_psi| / t := by
          exact add_le_add hpair_use h_cross
      _ ≤ K_pair / Real.sqrt t + |K_phi * K_psi| / Real.sqrt t := by
          have h_sqrt_le_t : Real.sqrt t ≤ t := by
            calc Real.sqrt t ≤ Real.sqrt t * Real.sqrt t :=
                    le_mul_of_one_le_right hsqrt_pos.le hsqrt_ge_one
              _ = t := Real.mul_self_sqrt ht_pos.le
          have h_div : |K_phi * K_psi| / t ≤ |K_phi * K_psi| / Real.sqrt t :=
            div_le_div_of_nonneg_left (abs_nonneg _) hsqrt_pos h_sqrt_le_t
          linarith
      _ = (K_pair + |K_phi * K_psi|) / Real.sqrt t := by ring

end MainStatement

end Laplace.Multi
