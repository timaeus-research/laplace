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

/-- **Coordinate bound by sup-norm**: `|u i| ≤ ‖u‖` for the standard
Pi sup-norm. (Mathlib's `norm_le_pi_norm`, restated.) -/
lemma abs_apply_le_norm (u : ι → ℝ) (i : ι) : |u i| ≤ ‖u‖ := by
  have := norm_le_pi_norm u i
  simpa [Real.norm_eq_abs] using this

/-- Sum-of-squares bounded by `card ι · ‖u‖²` (componentwise sup bound). -/
lemma sum_sq_le_card_mul_sq_norm (u : ι → ℝ) :
    ∑ i, (u i) ^ 2 ≤ Fintype.card ι * ‖u‖ ^ 2 := by
  have h_each : ∀ i : ι, (u i) ^ 2 ≤ ‖u‖ ^ 2 := by
    intro i
    have h := abs_apply_le_norm u i
    have h_sq : (u i) ^ 2 = |u i| * |u i| := by rw [← sq_abs, sq]
    have h_norm_sq : ‖u‖ ^ 2 = ‖u‖ * ‖u‖ := sq ‖u‖
    rw [h_sq, h_norm_sq]
    exact mul_self_le_mul_self (abs_nonneg _) h
  calc ∑ i, (u i) ^ 2 ≤ ∑ _i : ι, ‖u‖ ^ 2 := Finset.sum_le_sum (fun i _ => h_each i)
    _ = Fintype.card ι * ‖u‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ]
        ring

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
    (_hV : PotentialApprox V H)
    (_hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |rescaledPartition V t - gaussianZ H| ≤ K / Real.sqrt t := by
  sorry

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
    (_hV : PotentialApprox V H)
    (_hφ : ObservableApprox φ a)
    (_hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |rescaledExpectation V t φ| ≤ K / t := by
  sorry

/-- **Pair-observable asymptote (weak rate)**.

For observables `φ, ψ` with gradients `a, b`, the rescaled pair
expectation equals `(1/t) · ⟨a, Hinv b⟩` up to `O(1/t^{3/2})`:

  `∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
     |t · rescaledExpectation V t (φ · ψ) - ⟨a, Hinv b⟩| ≤ K / √t`.

This is the main quantitative content of the weak `lem:laplace_cov`. -/
theorem rescaledExpectation_pair_eq_main_add_O_inv_sqrt
    (V φ ψ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    (_hV : PotentialApprox V H)
    (_hφ : ObservableApprox φ a)
    (_hψ : ObservableApprox ψ b)
    (_hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b)|
        ≤ K / Real.sqrt t := by
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
