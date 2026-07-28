/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Core definitions of the multivariate Laplace–Gibbs track

The statement vocabulary of the multivariate covariance asymptotics, with a
Mathlib-only import closure: the Gibbs objects (`partitionFunction`,
`gibbsExpectation`, `gibbsCov`), the Gaussian data (`quadForm`,
`gaussianWeight`, `gaussianZ`, `dot`), the Fubini-IBP identities, and the
analytic hypothesis packages for the weak (`O(t^{-3/2})`), sharp (`O(t^{-2})`)
and explicit-coefficient covariance theorems
(`PotentialApprox` ⊂ `PotentialJetApprox` ⊂ `PotentialTensorApprox` ⊂
`PotentialQuinticApprox`, mirrored on the observable side, and the
`LaplaceCovHypotheses` ⊂ `LaplaceCov4MomentHypotheses` ⊂
`LaplaceCov6MomentHypotheses` Gaussian-moment packages).
-/

open MeasureTheory

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Partition function `Z(t) = ∫ exp(-t · L(w)) dw` over `ι → ℝ`. -/
noncomputable def partitionFunction (L : (ι → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ w : ι → ℝ, Real.exp (-(t * L w))

/-- Gibbs expectation `⟨φ⟩_t = (1/Z(t)) · ∫ φ(w) exp(-t · L(w)) dw`. -/
noncomputable def gibbsExpectation
    (L : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → ℝ) : ℝ :=
  (∫ w : ι → ℝ, φ w * Real.exp (-(t * L w))) / partitionFunction L t

/-- Gibbs covariance `Cov_t[φ, ψ] = ⟨φψ⟩_t - ⟨φ⟩_t ⟨ψ⟩_t`. -/
noncomputable def gibbsCov
    (L : (ι → ℝ) → ℝ) (t : ℝ) (φ ψ : (ι → ℝ) → ℝ) : ℝ :=
  gibbsExpectation L t (fun w => φ w * ψ w)
    - gibbsExpectation L t φ * gibbsExpectation L t ψ

/-- Quadratic form `⟨z, H z⟩ = ∑ i, z i * (H z) i` on `ι → ℝ` for a
continuous linear operator `H`. -/
noncomputable def quadForm
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (z : ι → ℝ) : ℝ :=
  ∑ i, z i * (H z) i

/-- The Gaussian weight `exp(-(1/2) · quadForm H u)`. -/
noncomputable def gaussianWeight
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) : ℝ :=
  Real.exp (-(1/2) * quadForm H u)

/-- The Gaussian normalising constant `Z := ∫ exp(-(1/2) quadForm H u) du`. -/
noncomputable def gaussianZ
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) : ℝ :=
  ∫ u : ι → ℝ, gaussianWeight H u

/-- The standard inner product on `ι → ℝ`: `dot a b = ∑ i, a i * b i`. -/
noncomputable def dot (a b : ι → ℝ) : ℝ := ∑ i, a i * b i

/-- **Fubini-IBP hypothesis** for the global integral:

For each `(i, j)`, the global integral of `sliceDeriv H i j u₀` over the
basepoint and `s` reduces, by Fubini on the product measure
`(ι → ℝ) ≃ᵐ ((ι\{i}) → ℝ) × ℝ`, to a slice-by-slice integral that vanishes
by `integral_sliceDeriv_eq_zero` (Step 4b).

Concretely, the hypothesis `h_fubini` asserts:

  `∫ u : ι → ℝ, sliceDeriv H i j u s_at_u_i evaluated at s = u_i = 0`

stated more directly as: the global integral of the *natural* expression

  `(if i = j then 1 else 0) · gW(u) - u_j · (H u)_i · gW(u)`

equals `0`. This is the Fubini-mediated content of the IBP identity,
which we state as a hypothesis (Option A from the GPT-5.5 Pro Phase 4
memo). -/
def FubiniIBPHypothesis
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (i j : ι) : Prop :=
  ∫ u : ι → ℝ, ((if i = j then (1 : ℝ) else 0) * gaussianWeight H u
      - u j * (H u) i * gaussianWeight H u) = 0

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
  /-- `φ` is continuous (needed for measurability/integrability). -/
  phi_continuous : Continuous φ
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

/-- **Sharp local approximation package for the potential**.

Extends `PotentialApprox` with an *odd* cubic-scale jet `cV` and a quartic
local remainder. Together with the existing local cubic remainder of
`PotentialApprox`, this controls the rescaled potential to one extra Taylor
order — sufficient for the parity-resolved sharp covariance rate.

The cubic jet is *not* required to be exactly homogeneous; oddness plus
the global cubic-growth bound `|cV w| ≤ Cc · ‖w‖³` is enough for the sharp
rate (see `gpt_responses/strategy_sharp_track.md`, §2). Imposing exact
cubic homogeneity (or the full symmetric trilinear tensor data) is a
strict strengthening, and is the natural route for the *explicit-coefficient*
companion theorem `lem:laplace_cov2`. -/
structure PotentialJetApprox
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    extends PotentialApprox V H where
  /-- Cubic-scale jet. -/
  cV : (ι → ℝ) → ℝ
  /-- Continuity of the cubic jet (needed for measurability). -/
  cV_continuous : Continuous cV
  /-- Oddness of the cubic jet: `cV (-w) = -(cV w)`. -/
  cV_odd : Function.Odd cV
  /-- Global cubic-growth constant. -/
  cV_bound_const : ℝ
  cV_bound_const_nonneg : 0 ≤ cV_bound_const
  /-- Global cubic-growth bound: `|cV w| ≤ C · ‖w‖³`. -/
  cV_bound : ∀ w : ι → ℝ, |cV w| ≤ cV_bound_const * ‖w‖ ^ 3
  /-- Radius for the quartic local remainder (may differ from `local_radius`). -/
  jet_radius : ℝ
  /-- Constant for the quartic local remainder. -/
  jet_const : ℝ
  jet_radius_pos : 0 < jet_radius
  jet_const_nonneg : 0 ≤ jet_const
  /-- Local quartic remainder: on `‖w‖ ≤ jet_radius`,
  `|V w - ((1/2) · quadForm H w + cV w)| ≤ jet_const · ‖w‖^4`. -/
  jet_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |V w - ((1 / 2 : ℝ) * quadForm H w + cV w)| ≤ jet_const * ‖w‖ ^ 4
  /-- Higher-moment integrability for the *bare* Gaussian weight:
  `‖u‖^k · gaussianWeight H u` is integrable for every `k : ℕ`.

  The corrected-bracket sharp-track decomposition (helper 1) requires
  `B · gW · c_t` integrability, which dominates by `polynomial(‖u‖) · gW`
  with degrees up to 5–6. The existing `LaplaceCovHypotheses.int_uk_uj_gW`
  only delivers quadratic Gaussian moments, so we include this stronger
  integrability hypothesis here. -/
  int_norm_pow_gW : ∀ k : ℕ,
    Integrable (fun u : ι → ℝ => ‖u‖ ^ k * gaussianWeight H u)
  /-- Coercive lower bound on the Gaussian quadratic form: there is a
  positive constant `H_coercive_const` such that `H_coercive_const · ‖u‖² ≤
  quadForm H u`. Used by the corrected-bracket pointwise bound to write
  `gW(u) ≤ exp(-(H_coercive_const/2)·‖u‖²)` and combine with `exp|s_t|`
  for Gaussian decay on the local ball.

  This is equivalent to *positive-definiteness* of `H` (which is implied
  by `LaplaceCovHypotheses.int_gW` plus injectivity, but the implication
  is non-trivial to formalise). The coercive constant also implies
  `int_norm_pow_gW` (via `integrable_norm_pow_mul_exp_neg_const_sq`),
  but we keep both fields for direct use. -/
  H_coercive_const : ℝ
  H_coercive_const_pos : 0 < H_coercive_const
  H_coercive_bound : ∀ u : ι → ℝ, H_coercive_const * ‖u‖ ^ 2 ≤ quadForm H u

/-- **Sharp local approximation package for an observable**.

Extends `ObservableApprox` with an *even* quadratic-scale jet `qφ` and a
cubic local remainder. The quadratic jet is not required to be exactly
homogeneous; evenness plus `|qφ w| ≤ Cq · ‖w‖²` suffices for the
parity-resolved sharp rate. -/
structure ObservableJetApprox
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    extends ObservableApprox φ a where
  /-- Quadratic-scale jet. -/
  qφ : (ι → ℝ) → ℝ
  /-- Continuity of the quadratic jet (needed for measurability). -/
  qφ_continuous : Continuous qφ
  /-- Evenness of the quadratic jet: `qφ (-w) = qφ w`. -/
  qφ_even : Function.Even qφ
  /-- Global quadratic-growth constant. -/
  qφ_bound_const : ℝ
  qφ_bound_const_nonneg : 0 ≤ qφ_bound_const
  /-- Global quadratic-growth bound: `|qφ w| ≤ C · ‖w‖²`. -/
  qφ_bound : ∀ w : ι → ℝ, |qφ w| ≤ qφ_bound_const * ‖w‖ ^ 2
  /-- Radius for the cubic local remainder. -/
  jet_radius : ℝ
  /-- Constant for the cubic local remainder. -/
  jet_const : ℝ
  jet_radius_pos : 0 < jet_radius
  jet_const_nonneg : 0 ≤ jet_const
  /-- Local cubic remainder: on `‖w‖ ≤ jet_radius`,
  `|φ w - (dot a w + qφ w)| ≤ jet_const · ‖w‖³`. -/
  jet_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |φ w - (dot a w + qφ w)| ≤ jet_const * ‖w‖ ^ 3

/-- **Exact-tensor potential package**.

Extends `PotentialJetApprox` with an *exact* symmetric trilinear cubic
tensor `T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => (ι → ℝ)) ℝ` such
that the cubic-scale jet `cV` is its diagonal up to a `1/6` factor:
`cV w = (1/6) · T (fun _ => w)` (cubic *homogeneity*, the strict
strengthening of the parity-only `cV_odd` hypothesis used by the sharp
track). The local quartic remainder upgrades to the *exact*
$V - \tfrac12 H w \cdot w - \tfrac16 T(w,w,w) = O(\|w\|^4)$ form. -/
structure PotentialTensorApprox
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    extends PotentialJetApprox V H where
  /-- Symmetric trilinear cubic tensor `T = ∇³V(0)`. -/
  T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ
  /-- Symmetry of `T` under permutations of arguments. -/
  T_symm : ∀ σ : Equiv.Perm (Fin 3), ∀ v : Fin 3 → (ι → ℝ),
    T (fun i => v (σ i)) = T v
  /-- Cubic homogeneity: the scalar cubic jet `cV` is the diagonal of `T`. -/
  cV_eq_T_diag : ∀ w : ι → ℝ, cV w = (1 / 6 : ℝ) * T (fun _ => w)
  /-- Local quartic remainder, upgraded from `jet_bound` to use the
  exact `T`-tensor form: on `‖w‖ ≤ jet_radius`,
  `|V w - ((1/2) · quadForm H w + (1/6) · T(w,w,w))| ≤ jet_const · ‖w‖^4`. -/
  T_jet_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |V w - ((1 / 2 : ℝ) * quadForm H w + (1 / 6 : ℝ) * T (fun _ => w))|
      ≤ jet_const * ‖w‖ ^ 4

/-- **Quintic-remainder strengthening** of `PotentialTensorApprox`.

Adds a sharper bound on the *odd* part of `V`'s Taylor remainder, needed
specifically for `expNumErr_3_bound` (J₃) where the parity symmetrization
reduces to bounding `s_t(u) - s_t(-u) - 2·C_t(u)`.

The bound `|V w - V(-w) - (1/3) · T(w,w,w)| ≤ Q_const · ‖w‖^5` says the
odd part of `V`'s Taylor expansion is captured by `(1/6)·T(w,w,w)` modulo
a quintic remainder. Equivalently,
`V w + (1/6)·T(w,w,w) = V(-w) + (1/6)·T(-w,-w,-w) - (1/3)·T(w,w,w)`,
i.e. the symmetric (even) part of `V` is captured by quartic-or-higher terms.

Holds when `V` is `C^5` near 0 (the explicit Taylor coefficient at order 5
gives the bound). Independent from `T_jet_bound` (quartic bound) since the
odd part has its own structure. -/
structure PotentialQuinticApprox
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    extends PotentialTensorApprox V H where
  /-- Constant for the odd-quintic remainder. -/
  Q_const : ℝ
  Q_const_nn : 0 ≤ Q_const
  /-- Odd-part quintic remainder: on `‖w‖ ≤ jet_radius`,
  `|V w - V(-w) - (1/3)·T(w,w,w)| ≤ Q_const · ‖w‖^5`. -/
  V_odd_quintic_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |V w - V (-w) - (1 / 3 : ℝ) * T (fun _ => w)|
      ≤ Q_const * ‖w‖ ^ 5

/-- **Exact-tensor observable package**.

Extends `ObservableJetApprox` with an *exact* symmetric bilinear quadratic
form `A : (ι → ℝ) →L[ℝ] (ι → ℝ)` (so the Hessian quadratic part is
`(1/2) · quadForm A w`) and an *exact* symmetric trilinear cubic tensor
`Φ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => (ι → ℝ)) ℝ`. The local
remainder is now *quartic* against `dot a w + (1/2) quadForm A w + (1/6) Φ(w,w,w)`.

For `lem:laplace_exp` we only need the `A` data (and the existing `qφ`
linkage `qφ w = (1/2) quadForm A w`); `Φ` is needed for `lem:laplace_cov2`'s
$\langle \phi_3 \psi_1\rangle$ term when $\phi$ vanishes to second order. -/
structure ObservableTensorApprox
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    extends ObservableJetApprox φ a where
  /-- Symmetric bilinear quadratic Hessian, as a continuous linear map
  `(ι → ℝ) →L[ℝ] (ι → ℝ)`. The bilinear form is `quadForm A`. -/
  A : (ι → ℝ) →L[ℝ] (ι → ℝ)
  /-- Symmetry of `A`: `dot u (A v) = dot v (A u)`. -/
  A_symm : ∀ u v : ι → ℝ, dot u (A v) = dot v (A u)
  /-- Quadratic-jet linkage: `qφ w = (1/2) · quadForm A w`. -/
  qφ_eq_A_diag : ∀ w : ι → ℝ, qφ w = (1 / 2 : ℝ) * quadForm A w
  /-- Symmetric trilinear cubic tensor `Φ = ∇³φ(0)`. -/
  Φ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ
  /-- Symmetry of `Φ` under permutations of arguments. -/
  Φ_symm : ∀ σ : Equiv.Perm (Fin 3), ∀ v : Fin 3 → (ι → ℝ),
    Φ (fun i => v (σ i)) = Φ v
  /-- Local quartic remainder (exact-tensor form): on `‖w‖ ≤ jet_radius`,
  `|φ w - (dot a w + (1/2) quadForm A w + (1/6) Φ(w,w,w))| ≤ jet_const · ‖w‖^4`. -/
  Φ_jet_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |φ w - (dot a w + (1 / 2 : ℝ) * quadForm A w
            + (1 / 6 : ℝ) * Φ (fun _ => w))| ≤ jet_const * ‖w‖ ^ 4

/-- **Quintic-remainder strengthening for observables**.

Adds a sharper bound on the *odd* part of `φ`'s Taylor remainder, needed
specifically for Lemma A's bulk-block bound (`abs_integral_bulkErrA_le`).
Without this stronger control, Lemma A is genuinely false: one can
construct a φ satisfying `ObservableTensorApprox` (with a = 0, A = 0,
Φ = 0) for which `|φ(w)| ≤ ‖w‖^4` but with non-trivial odd quartic
remainder, giving a Θ(t⁻¹/²) bulk contribution rather than O(t⁻¹). See
`gpt_responses/strategy_stage5_bulk_O1t.md` for the counterexample.

The bound `|φ w - φ(-w) - 2·a·w - (1/3)·Φ(w,w,w)| ≤ Q_const · ‖w‖^5` says
the odd part of `φ`'s Taylor expansion is captured by `a·w + (1/6)·Φ(w³)`
modulo a quintic remainder. Holds when `φ` is `C^5` near 0 (the explicit
Taylor coefficient at order 5 gives the bound). Independent from
`Φ_jet_bound` (quartic bound) since the odd part has its own structure.

Mirrors the analogous V-side `PotentialQuinticApprox` from `CovarianceSharp.lean`. -/
structure ObservableQuinticApprox
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    extends ObservableTensorApprox φ a where
  /-- Constant for the odd-quintic remainder. -/
  Q_const : ℝ
  Q_const_nn : 0 ≤ Q_const
  /-- Odd-part quintic remainder: on `‖w‖ ≤ jet_radius`,
  `|φ w - φ(-w) - 2·dot a w - (1/3)·Φ(w,w,w)| ≤ Q_const · ‖w‖^5`. -/
  φ_odd_quintic_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |φ w - φ (-w) - 2 * dot a w - (1 / 3 : ℝ) * Φ (fun _ => w)|
      ≤ Q_const * ‖w‖ ^ 5

/-- Contraction `(T : Sig)_i := ∑_{jk} T_ijk Sig_jk`, where `T` is a symmetric
trilinear form (read as `T_ijk = T(eᵢ, eⱼ, e_k)` for the standard basis)
and `Sig : (ι → ℝ) →L[ℝ] (ι → ℝ)` represents `Sig_jk = Sig(e_k)_j`. The result
is a vector in `(ι → ℝ)`. -/
noncomputable def tensorContractMatrix
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (Sig : (ι → ℝ) →L[ℝ] (ι → ℝ)) : ι → ℝ :=
  fun i => ∑ j, T (fun k =>
    match k with
    | 0 => Pi.single i (1 : ℝ)
    | 1 => Pi.single j (1 : ℝ)
    | 2 => Sig (Pi.single j (1 : ℝ)))

/-- Trace `tr(A Sig) := ∑_i (A (Sig eᵢ))_i`, for a symmetric bilinear form `A` and
its conjugate against `Sig : (ι → ℝ) →L[ℝ] (ι → ℝ)`. -/
noncomputable def trASig
    (A Sig : (ι → ℝ) →L[ℝ] (ι → ℝ)) : ℝ :=
  ∑ i, (A (Sig (Pi.single i (1 : ℝ)))) i

/-- **Cubic Fubini-IBP hypothesis**: the multivariate analog of
`FubiniIBPHypothesis` for cubic test functions `f(u) = u_a u_b u_c`. The
content is that the boundary terms in the integration-by-parts identity
$\int (\partial_l f) \cdot gW = \int f \cdot (Hu)_l \cdot gW$
vanish; concretely,
$$
  \int \big[(\delta_{la} u_b u_c + \delta_{lb} u_a u_c + \delta_{lc} u_a u_b)
  \,gW - u_a u_b u_c (Hu)_l \, gW\big] = 0.
$$
This is provable under coercivity hypotheses on `H` via Fubini + 1D-FTC
slice-by-slice, as in the existing `FubiniIBPHypothesis`. We expose it as
a hypothesis here, packaged into `LaplaceCov4MomentHypotheses` below. -/
def FubiniIBPHypothesisCubic
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (a b c l : ι) : Prop :=
  ∫ u : ι → ℝ,
    (((if l = a then u b * u c else 0) +
      (if l = b then u a * u c else 0) +
      (if l = c then u a * u b else 0)) * gaussianWeight H u
      - u a * u b * u c * (H u) l * gaussianWeight H u) = 0

/-- **4th-moment hypothesis package**: extends `LaplaceCovHypotheses` with
the integrability and Fubini-IBP fields needed to prove the 4th-moment
Wick formula `gaussian_fourth_moment_formula`. -/
structure LaplaceCov4MomentHypotheses
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    extends LaplaceCovHypotheses H Hinv where
  /-- 4th-moment integrability. -/
  int_4moment : ∀ a b c d : ι,
    Integrable (fun u : ι → ℝ => u a * u b * u c * u d * gaussianWeight H u)
  /-- Cubic-IBP integrand integrability: `u_a · u_b · u_c · (Hu)_l · gW`
  is integrable. -/
  int_3_Hl : ∀ a b c l : ι,
    Integrable (fun u : ι → ℝ => u a * u b * u c * (H u) l * gaussianWeight H u)
  /-- Cubic Fubini-IBP. -/
  fubini_ibp_cubic : ∀ a b c l : ι, FubiniIBPHypothesisCubic H a b c l

/-- **Quintic Fubini-IBP hypothesis**: the multivariate analog of
`FubiniIBPHypothesisCubic` for quintic test functions
`f(u) = u_a u_b u_c u_d u_e`. The content is that the boundary terms in
the integration-by-parts identity
$\int (\partial_l f) \cdot gW = \int f \cdot (Hu)_l \cdot gW$
vanish; concretely (writing `δ_xy` for Kronecker `δ`):
$$
  \int \big[(\delta_{la} u_b u_c u_d u_e + \delta_{lb} u_a u_c u_d u_e
            + \delta_{lc} u_a u_b u_d u_e + \delta_{ld} u_a u_b u_c u_e
            + \delta_{le} u_a u_b u_c u_d) \, gW
  - u_a u_b u_c u_d u_e \cdot (Hu)_l \, gW\big] = 0.
$$
This is provable under coercivity hypotheses on `H` via Fubini + 1D-FTC
slice-by-slice, as in the existing cubic version. We expose it as a
hypothesis here, packaged into `LaplaceCov6MomentHypotheses` below.

Used in `gaussian_sixth_moment_formula` (which reduces 6-moment to 4-moment
via Stein's identity) → `gaussian_quad_linear_cubic_explicit` → Lemma A. -/
def FubiniIBPHypothesisQuintic
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (a b c d e l : ι) : Prop :=
  ∫ u : ι → ℝ,
    (((if l = a then u b * u c * u d * u e else 0) +
      (if l = b then u a * u c * u d * u e else 0) +
      (if l = c then u a * u b * u d * u e else 0) +
      (if l = d then u a * u b * u c * u e else 0) +
      (if l = e then u a * u b * u c * u d else 0)) * gaussianWeight H u
      - u a * u b * u c * u d * u e * (H u) l * gaussianWeight H u) = 0

/-- **6th-moment hypothesis package** (Stage 3 prerequisite for `lem:laplace_cov2`):
extends `LaplaceCov4MomentHypotheses` with 6th-moment integrability and the
quintic Fubini-IBP needed for `gaussian_quad_linear_cubic`. -/
structure LaplaceCov6MomentHypotheses
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    extends LaplaceCov4MomentHypotheses H Hinv where
  /-- 6th-moment integrability. -/
  int_6moment : ∀ a b c d e f : ι,
    Integrable (fun u : ι → ℝ =>
      u a * u b * u c * u d * u e * u f * gaussianWeight H u)
  /-- Quintic-IBP integrand integrability:
  `u_a · u_b · u_c · u_d · u_e · (Hu)_l · gW` is integrable. -/
  int_5_Hl : ∀ a b c d e l : ι,
    Integrable (fun u : ι → ℝ =>
      u a * u b * u c * u d * u e * (H u) l * gaussianWeight H u)
  /-- Quintic Fubini-IBP. -/
  fubini_ibp_quintic : ∀ a b c d e l : ι,
    FubiniIBPHypothesisQuintic H a b c d e l

end Laplace.Multi
