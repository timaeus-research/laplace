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
`O(1/√t)`:

  `∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
     |rescaledExpectation V t φ| ≤ K / √t`.

The leading-order term of `rescaledExpectation V t φ` is
`(1/√t) · ⟨a, ⟨u⟩_t⟩ ≈ 0` since the Gaussian mean is `0`; the residual
is `O(1/√t)` from the quadratic remainder. -/
theorem rescaledExpectation_observable_bound_inv_sqrt
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    (_hV : PotentialApprox V H)
    (_hφ : ObservableApprox φ a)
    (_hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |rescaledExpectation V t φ| ≤ K / Real.sqrt t := by
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
    (_hV : PotentialApprox V H)
    (_hφ : ObservableApprox φ a)
    (_hψ : ObservableApprox ψ b)
    (_hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / Real.sqrt t := by
  sorry

end MainStatement

end Laplace.Multi
