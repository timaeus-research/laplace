/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Multi.CovarianceSharp
import Laplace.ScalarBound

/-!
# Explicit-coefficient multivariate Laplace asymptotics (skeleton, in progress)

This file aims at the **explicit-coefficient** $O(t^{-2})$ companions to the
Susceptibility Primer's `lem:laplace_cov`:

* `lem:laplace_exp` — multivariate expectation at order $t^{-1}$:
  $$
  \langle \phi \rangle_t = \tfrac{1}{2t}\big[\mathrm{tr}(\nabla^2\phi\,\Sigma) -
  \nabla\phi^\top\Sigma\,(T{:}\Sigma)\big] + O(t^{-2}),
  $$
  for $\phi$ vanishing at $w^*$, with $T = \nabla^3 V(w^*)$.
* `lem:laplace_cov2` — multivariate covariance at order $t^{-2}$:
  $$
  \mathrm{Cov}_t[\phi,\psi] = \tfrac{1}{t^2}\Big[\tfrac{1}{2}\mathrm{tr}(A\Sigma B\Sigma)
  + \tfrac{1}{2}(\Sigma b)\!\cdot\!(\Phi{:}\Sigma) - \tfrac{1}{2}b^\top\Sigma A\Sigma(T{:}\Sigma)
  - \tfrac{1}{2}(\Sigma b)\!\cdot\!(T{:}(\Sigma A\Sigma))\Big] + o(t^{-2}),
  $$
  for $\phi$ vanishing to second order ($\phi(w^*) = 0$, $\nabla\phi(w^*) = 0$),
  $\psi$ vanishing at $w^*$. Here $A = \nabla^2\phi(w^*)$, $\Phi = \nabla^3\phi(w^*)$,
  $b = \nabla\psi(w^*)$, $B = \nabla^2\psi(w^*)$, $T = \nabla^3 V(w^*)$, $\Sigma = H^{-1}$.

The implicit-coefficient sharp covariance `gibbsCov_first_order_rate_sharp` (the
weaker statement asserting only that the leading coefficient is
$\nabla\phi^\top\Sigma\nabla\psi$) is already proven in
`Laplace.Multi.CovarianceSharp`. This file extends that to the *explicit*
coefficient by exposing tensor-valued local jets and computing the leading
Gaussian terms via specialised contraction lemmas.

## Architectural choices (per `gpt_responses/strategy_lem_laplace_cov2.md`)

1. **New companion structures.** `PotentialTensorApprox` and
   `ObservableTensorApprox` extend `PotentialJetApprox`/`ObservableJetApprox`
   with *exact* tensor data (a `ContinuousMultilinearMap` for the cubic part)
   plus a *quartic* local remainder. We do not modify the existing sharp-track
   structures.
2. **Multilinear-map tensor data.** Cubic tensors are stored as
   `ContinuousMultilinearMap ℝ (fun _ : Fin 3 => (ι → ℝ)) ℝ` rather than
   indexed coefficients; the theorem-level API uses scalar / contracted forms.
3. **Specialised contraction lemmas.** We do *not* build a general Isserlis
   theorem. Instead we prove the four or five Gaussian moment identities that
   the appendix proofs of `lem:laplace_exp` and `lem:laplace_cov2` actually
   need:
   - `gaussian_quad_expectation` — $\int \tfrac12 u^\top A u\, gW
     = Z\cdot\tfrac12\mathrm{tr}(A\Sigma)$.
   - `gaussian_linear_cubic` — $\int (a\cdot u)\,T(u,u,u)\,gW
     = Z\cdot 3\,(\Sigma a)\cdot(T{:}\Sigma)$ (then $1/6$ prefactor gives $\tfrac12$).
   - `gaussian_quad_quad` — $\int (\tfrac12 u^\top A u)(\tfrac12 u^\top B u)\,gW
     = Z[\tfrac14\mathrm{tr}(A\Sigma)\mathrm{tr}(B\Sigma)+\tfrac12\mathrm{tr}(A\Sigma B\Sigma)]$.
   - `gaussian_cubic_linear` — $\int \tfrac16\Phi(u,u,u)(b\cdot u)\,gW
     = Z\cdot\tfrac12(\Sigma b)\cdot(\Phi{:}\Sigma)$.
   - `gaussian_quad_linear_cubic` — directly in the contracted final form for
     the 6th-moment term.
4. **Glocal+Gtail for error control only.** The exact algebraic main term is
   computed via the contraction lemmas; the local Taylor and tail remainders
   are bounded via the `Glocal+Gtail` template proven 4× in `CovarianceSharp`.

## Status

- Stage 0 (this file): tensor jet structures + theorem signatures, all
  sorry'd. Skeleton-correctness milestone, not proof completion.
- Subsequent stages will fill the sorries bottom-up: contraction lemmas →
  `lem:laplace_exp` → `lem:laplace_cov2`.

-/

namespace Laplace.Multi

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section TensorJetStructures

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
a quintic remainder. Equivalently, `V w + (1/6)·T(w,w,w) = V(-w) + (1/6)·T(-w,-w,-w) - (1/3)·T(w,w,w)`,
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

end TensorJetStructures

section TensorContractions

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

/-- Standard basis vector `e i := Pi.single i 1`. Local abbreviation for use
in tensor contraction proofs (per `gpt_responses/tactics_contraction_lemmas.md`). -/
noncomputable def stdBasisVec (i : ι) : ι → ℝ :=
  Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)

/-- **Trilinear diagonal is odd**: for any continuous trilinear form `T`,
`T(-u, -u, -u) = -T(u, u, u)`. Used for parity arguments against the Gaussian
weight (e.g. `∫ Φ(u,u,u) · gW = 0`). -/
lemma cmm_diag_odd
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ) (u : ι → ℝ) :
    T (fun _ => -u) = -T (fun _ => u) := by
  have h := T.map_smul_univ (fun _ : Fin 3 => (-1 : ℝ)) (fun _ => u)
  simp only [Fin.prod_univ_three] at h
  rw [show (fun _ : Fin 3 => -u)
        = (fun _ : Fin 3 => ((-1 : ℝ)) • u) from by funext _; simp]
  rw [h]; simp

/-- **Diagonal of trilinear form against Gaussian vanishes**: for any continuous
trilinear `T`, `∫ T(u, u, u) · gW = 0`. Direct corollary of `cmm_diag_odd` and
`integral_odd_mul_gaussian_eq_zero`. -/
lemma integral_cmm_diag_mul_gaussianWeight_eq_zero
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ) :
    ∫ u : ι → ℝ, T (fun _ => u) * gaussianWeight H u = 0 := by
  apply integral_odd_mul_gaussian_eq_zero
  intro u
  exact cmm_diag_odd T u

/-- **Even kernel · trilinear diagonal · Gaussian vanishes**: for any continuous
trilinear `T` and any function `F` with `F(-u) = F(u)` (even),
`∫ F(u) · T(u, u, u) · gW = 0`. The integrand is (even)·(odd)·(even) = odd.
Used in parity helpers P1, P2 for the centered-pair Stage 5 lemmas. -/
lemma integral_even_mul_cmm_diag_mul_gaussianWeight_eq_zero
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (F : (ι → ℝ) → ℝ) (hF_even : ∀ u, F (-u) = F u)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ) :
    ∫ u : ι → ℝ, F u * T (fun _ => u) * gaussianWeight H u = 0 := by
  apply integral_odd_mul_gaussian_eq_zero
  intro u
  rw [hF_even u, cmm_diag_odd T u]
  ring

/-- Coordinate-form tensor: `Tcoord T i j k := T(e_i, e_j, e_k)` for the
standard basis. The fundamental object for index-based reasoning about T. -/
noncomputable def Tcoord
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (i j k : ι) : ℝ :=
  T (fun n : Fin 3 =>
    match n with
    | 0 => stdBasisVec i
    | 1 => stdBasisVec j
    | 2 => stdBasisVec k)

/-- Convenience: `Tcoord` viewed as a function of a triple `(r 0, r 1, r 2)`
for `r : Fin 3 → ι`. -/
lemma Tcoord_eq_apply
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (r : Fin 3 → ι) :
    Tcoord T (r 0) (r 1) (r 2) = T (fun n : Fin 3 => stdBasisVec (r n)) := by
  unfold Tcoord
  congr 1
  funext n
  fin_cases n <;> rfl

/-- **Tensor coordinate symmetry**: from the abstract `T_symm` field, the
coordinate-form tensor is invariant under any permutation of its 3 indices. -/
lemma Tcoord_perm
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (hT_symm : ∀ σ : Equiv.Perm (Fin 3), ∀ v : Fin 3 → (ι → ℝ),
      T (fun i => v (σ i)) = T v)
    (σ : Equiv.Perm (Fin 3)) (r : Fin 3 → ι) :
    Tcoord T (r (σ 0)) (r (σ 1)) (r (σ 2)) = Tcoord T (r 0) (r 1) (r 2) := by
  rw [Tcoord_eq_apply T (fun n => r (σ n)),
      Tcoord_eq_apply T r]
  -- LHS: T (fun n => stdBasisVec (r (σ n)))
  -- RHS: T (fun n => stdBasisVec (r n))
  -- By T_symm with v := (fun m => stdBasisVec (r m)).
  have h := hT_symm σ (fun m => stdBasisVec (r m))
  exact h

/-- **Multilinear-map slot expansion**: for `T : ContinuousMultilinearMap ℝ
(fun _ : Fin 3 => (ι → ℝ)) ℝ` and `u : ι → ℝ`,
$$
  T(u, u, u) = \sum_{i,j,k} u_i u_j u_k \cdot T_{ijk}.
$$
Slot-by-slot via `MultilinearMap.map_update_sum` + `map_update_smul`, per
the GPT-5.5 Pro recipe in `gpt_responses/tactics_T_apply_diag.md`. -/
lemma T_apply_diag_eq_sum
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (u : ι → ℝ) :
    T (fun _ : Fin 3 => u) =
      ∑ i, ∑ j, ∑ k, u i * u j * u k * Tcoord T i j k := by
  classical
  -- Reusable one-slot expansion helper.
  have expand_slot (m : Fin 3 → ι → ℝ) (s : Fin 3) (hs : m s = u) :
      T m = ∑ a : ι, u a * T (Function.update m s (stdBasisVec a)) := by
    calc
      T m = T (Function.update m s (∑ a : ι, u a • stdBasisVec a)) := by
        congr 1
        funext n
        by_cases h : n = s
        · subst h
          simpa [hs] using (eq_sum_stdBasis u)
        · simp [Function.update, h]
      _ = ∑ a : ι, T (Function.update m s (u a • stdBasisVec a)) := by
        simpa using
          (T.toMultilinearMap.map_update_sum
            (t := Finset.univ) (i := s)
            (g := fun a : ι => u a • stdBasisVec a) (m := m))
      _ = ∑ a : ι, u a * T (Function.update m s (stdBasisVec a)) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        simpa [smul_eq_mul] using
          (T.toMultilinearMap.map_update_smul
            (m := m) (i := s) (c := u a) (x := stdBasisVec a))
  -- Apply expand_slot at each of the three slots.
  have h0 := expand_slot (m := fun _ : Fin 3 => u) (s := (0 : Fin 3)) rfl
  have h1 (i : ι) :=
    expand_slot
      (m := Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
      (s := (1 : Fin 3)) (by simp [Function.update])
  have h2 (i j : ι) :=
    expand_slot
      (m := Function.update
        (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
        (1 : Fin 3) (stdBasisVec j))
      (s := (2 : Fin 3)) (by simp [Function.update])
  -- Identify the fully-expanded slot configuration with Tcoord.
  have hcoord (i j k : ι) :
      T (Function.update
          (Function.update
            (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
            (1 : Fin 3) (stdBasisVec j))
          (2 : Fin 3) (stdBasisVec k)) = Tcoord T i j k := by
    have hfun :
        Function.update
          (Function.update
            (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
            (1 : Fin 3) (stdBasisVec j))
          (2 : Fin 3) (stdBasisVec k)
        =
        (fun n : Fin 3 =>
          match n with
          | 0 => stdBasisVec i
          | 1 => stdBasisVec j
          | 2 => stdBasisVec k) := by
      funext n
      fin_cases n <;> simp [Function.update]
    simpa [Tcoord] using congrArg T hfun
  -- Combine the three slot expansions.
  calc
    T (fun _ : Fin 3 => u)
        = ∑ i : ι, u i *
            T (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i)) := h0
    _ = ∑ i : ι, ∑ j : ι, u i * (u j *
            T (Function.update
              (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
              (1 : Fin 3) (stdBasisVec j))) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [h1 i, Finset.mul_sum]
    _ = ∑ i : ι, ∑ j : ι, ∑ k : ι, u i * (u j * (u k *
            T (Function.update
              (Function.update
                (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
                (1 : Fin 3) (stdBasisVec j))
              (2 : Fin 3) (stdBasisVec k)))) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [h2 i j, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ k, u i * u j * u k * Tcoord T i j k := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hcoord i j k]
          ring

end TensorContractions

section FourthMomentInfrastructure

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

/-- **6th-moment hypothesis package** (Stage 3 prerequisite for `lem:laplace_cov2`):
extends `LaplaceCov4MomentHypotheses` with 6th-moment integrability and the
quintic Fubini-IBP needed for `gaussian_quad_linear_cubic`.

The signature is intentionally minimal — fill in the integrability fields once
the Stage 3 proof clarifies exactly which ones are needed. -/
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

end FourthMomentInfrastructure

section InverseSymmetry

/-- **Symmetry of the inverse**: under `LaplaceCovHypotheses` (`H`
symmetric, `Hinv` a right-inverse for `H`, `H` injective), `Hinv` is
also symmetric: $\sum_k x_k (Hinv\, y)_k = \sum_k y_k (Hinv\, x)_k$.

This is needed for the 4th-moment Wick proof: the trace cyclicity
`tr(A Σ) = tr(Σ A)` in coordinate form needs Σ symmetry. -/
lemma Hinv_symm
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hGauss : LaplaceCovHypotheses H Hinv) (x y : ι → ℝ) :
    ∑ k, x k * (Hinv y) k = ∑ k, y k * (Hinv x) k := by
  -- Apply H_symm to (Hinv y, Hinv x): gives
  --   ∑ (Hinv y)_k (H (Hinv x))_k = ∑ (Hinv x)_k (H (Hinv y))_k.
  -- Use H ∘ Hinv = id: (H (Hinv x)) = x, (H (Hinv y)) = y.
  have h1 : H (Hinv x) = x := by
    have := congrArg (fun f => f x) hGauss.H_inv_right
    simpa using this
  have h2 : H (Hinv y) = y := by
    have := congrArg (fun f => f y) hGauss.H_inv_right
    simpa using this
  have h_apply := hGauss.H_symm (Hinv y) (Hinv x)
  rw [h1, h2] at h_apply
  -- h_apply : ∑ (Hinv y)_k * x k = ∑ (Hinv x)_k * y k
  -- Goal:    ∑ x k * (Hinv y) k = ∑ y k * (Hinv x) k
  have h_lhs : ∑ k, x k * (Hinv y) k = ∑ k, (Hinv y) k * x k := by
    apply Finset.sum_congr rfl; intros; ring
  have h_rhs : ∑ k, y k * (Hinv x) k = ∑ k, (Hinv x) k * y k := by
    apply Finset.sum_congr rfl; intros; ring
  rw [h_lhs, h_rhs]; exact h_apply

/-- **`trASig` as a coordinate-form double sum**: under symmetry of `Hinv`,
`trASig A Hinv = ∑_i ∑_j (A e_j) i · (Hinv e_j) i`. This is `tr(A · Σ)` in
the coordinate-pairing form needed for the Wick-pairing trace identifications. -/
lemma trASig_eq_double_sum
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hGauss : LaplaceCovHypotheses H Hinv)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    trASig A Hinv =
      ∑ i, ∑ j, (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i := by
  -- trASig A Hinv = ∑ i, (A (Hinv e_i)) i.
  -- Expand (A (Hinv e_i)) i = ∑ k, (Hinv e_i) k · (A e_k) i (by H_apply_eq_sum).
  -- Use Hinv symmetry: (Hinv e_i) k = (Hinv e_k) i.
  -- Substitute: ∑ k, (Hinv e_k) i · (A e_k) i.
  -- Renaming k → j: ∑ j, (A e_j) i · (Hinv e_j) i.
  unfold trASig
  apply Finset.sum_congr rfl; intros i _
  rw [H_apply_eq_sum A (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) i]
  apply Finset.sum_congr rfl; intros j _
  -- Need: (Hinv (Pi.single i 1)) j * (A (Pi.single j 1)) i
  --     = (A (Pi.single j 1)) i * (Hinv (Pi.single j 1)) i.
  -- The second factor needs (Hinv (Pi.single i 1)) j = (Hinv (Pi.single j 1)) i (Hinv symm).
  have h_swap : (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j =
      (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i := by
    -- Apply Hinv_symm with x = Pi.single i 1, y = Pi.single j 1.
    have h := Hinv_symm hGauss (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))
      (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))
    -- h : ∑ k, (Pi.single j 1) k * (Hinv (Pi.single i 1)) k
    --   = ∑ k, (Pi.single i 1) k * (Hinv (Pi.single j 1)) k
    -- LHS evaluates to (Hinv (Pi.single i 1)) j (only k = j survives).
    -- RHS evaluates to (Hinv (Pi.single j 1)) i.
    have h_lhs : ∑ k, (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)) k *
        (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) k
        = (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]; ring
      · intros k _ hk
        have h_zero : Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ) k = 0 := by
          simp [Pi.single_apply, hk.symm]
        rw [h_zero]; ring
      · intro h; exact absurd (Finset.mem_univ j) h
    have h_rhs : ∑ k, (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)) k *
        (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) k
        = (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]; ring
      · intros k _ hk
        have h_zero : Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) k = 0 := by
          simp [Pi.single_apply, hk.symm]
        rw [h_zero]; ring
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h_lhs, h_rhs] at h
    exact h
  rw [h_swap]; ring

/-- **Linear factor as Hinv-weighted Hu sum**: `dot a u = ∑_l (Hinv a)_l (Hu)_l`.
Uses `Hinv` symmetry + `H ∘ Hinv = id`. The bridge from a generic linear factor
to the cubic-IBP lemma `gaussian_ibp_cubic_f`. -/
lemma dot_eq_sum_Hinv_mul_H
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hGauss : LaplaceCovHypotheses H Hinv)
    (a u : ι → ℝ) :
    dot a u = ∑ l, (Hinv a) l * (H u) l := by
  have h_h_inv : H (Hinv a) = a := by
    have := congrArg (fun f => f a) hGauss.H_inv_right
    simpa using this
  -- H_symm gives: ∑ k, u k * (H (Hinv a)) k = ∑ k, (Hinv a) k * (H u) k.
  have h_sym := hGauss.H_symm u (Hinv a)
  rw [h_h_inv] at h_sym
  -- h_sym: ∑ k, u k * a k = ∑ k, (Hinv a) k * (H u) k
  -- Goal: dot a u = ∑ l, (Hinv a) l * (H u) l
  unfold dot
  have h_swap : ∑ i, a i * u i = ∑ k, u k * a k := by
    apply Finset.sum_congr rfl; intros; ring
  rw [h_swap, h_sym]

end InverseSymmetry

section CubicIBP

/-- **Cubic-test-function IBP**: from the cubic Fubini-IBP hypothesis,
integration by parts on the cubic monomial $u_a u_b u_c$ yields
$$
  \int u_a u_b u_c (Hu)_l \, gW
   = \int \big[(\delta_{la} u_b u_c + \delta_{lb} u_a u_c
     + \delta_{lc} u_a u_b)\big] \, gW.
$$
This is the direct analog of `gaussian_ibp_coord`, lifted to cubic test
functions; together with the 2nd-moment identity it gives the 4th-moment
Wick formula. -/
theorem gaussian_ibp_cubic_f
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hGauss : LaplaceCov4MomentHypotheses H Hinv)
    (a b c l : ι) :
    ∫ u : ι → ℝ, u a * u b * u c * (H u) l * gaussianWeight H u
      = ∫ u : ι → ℝ,
          ((if l = a then u b * u c else 0) +
           (if l = b then u a * u c else 0) +
           (if l = c then u a * u b else 0)) * gaussianWeight H u := by
  -- Fubini-IBP says the integral of (LHS − RHS in integrand form) is 0.
  have h_fubini := hGauss.fubini_ibp_cubic a b c l
  unfold FubiniIBPHypothesisCubic at h_fubini
  -- h_fubini : ∫ ((δ-form * gW - u_a u_b u_c (Hu)_l * gW)) = 0
  -- Split into ∫ A - ∫ B = 0 and rearrange.
  have h_intA : Integrable (fun u : ι → ℝ =>
      ((if l = a then u b * u c else 0) +
       (if l = b then u a * u c else 0) +
       (if l = c then u a * u b else 0)) * gaussianWeight H u) := by
    -- Sum of three indicator-times-2nd-moment integrands.
    have h1 : Integrable (fun u : ι → ℝ =>
        (if l = a then u b * u c else 0) * gaussianWeight H u) := by
      by_cases hla : l = a
      · simp only [if_pos hla]; exact hGauss.int_uk_uj_gW b c
      · simp only [if_neg hla, zero_mul]; exact integrable_zero _ _ _
    have h2 : Integrable (fun u : ι → ℝ =>
        (if l = b then u a * u c else 0) * gaussianWeight H u) := by
      by_cases hlb : l = b
      · simp only [if_pos hlb]; exact hGauss.int_uk_uj_gW a c
      · simp only [if_neg hlb, zero_mul]; exact integrable_zero _ _ _
    have h3 : Integrable (fun u : ι → ℝ =>
        (if l = c then u a * u b else 0) * gaussianWeight H u) := by
      by_cases hlc : l = c
      · simp only [if_pos hlc]; exact hGauss.int_uk_uj_gW a b
      · simp only [if_neg hlc, zero_mul]; exact integrable_zero _ _ _
    have h_sum_lambda : Integrable (fun u : ι → ℝ =>
        (if l = a then u b * u c else 0) * gaussianWeight H u
        + (if l = b then u a * u c else 0) * gaussianWeight H u
        + (if l = c then u a * u b else 0) * gaussianWeight H u) :=
      (h1.add h2).add h3
    apply h_sum_lambda.congr
    filter_upwards with u
    ring
  have h_intB := hGauss.int_3_Hl a b c l
  have h_split :
      ∫ u : ι → ℝ,
        (((if l = a then u b * u c else 0) +
          (if l = b then u a * u c else 0) +
          (if l = c then u a * u b else 0)) * gaussianWeight H u
          - u a * u b * u c * (H u) l * gaussianWeight H u)
      = (∫ u, ((if l = a then u b * u c else 0) +
              (if l = b then u a * u c else 0) +
              (if l = c then u a * u b else 0)) * gaussianWeight H u)
        - (∫ u, u a * u b * u c * (H u) l * gaussianWeight H u) :=
    integral_sub h_intA h_intB
  rw [h_split] at h_fubini
  linarith

end CubicIBP

section FourthMomentFormula

/-- **4th-moment Wick formula**: for indices $a, b, c, d$,
$$
  \int u_a u_b u_c u_d \, gW
   = Z \cdot \big[\Sigma_{ab}\Sigma_{cd} + \Sigma_{ac}\Sigma_{bd}
     + \Sigma_{ad}\Sigma_{bc}\big],
$$
where $\Sigma_{ij} = (Hinv\, e_j)_i$ in coordinate form.

The proof multiplies the cubic IBP identity by $\Sigma_{lp}$ and sums over
$l$; the contraction $\sum_l \Sigma_{lp} (Hu)_l = u_p$ (using $\Sigma$
symmetric and $\Sigma H = I$) reduces the LHS to the 4th moment. -/
theorem gaussian_fourth_moment_formula
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hGauss : LaplaceCov4MomentHypotheses H Hinv)
    (a b c d : ι) :
    ∫ u : ι → ℝ, u a * u b * u c * u d * gaussianWeight H u
      = gaussianZ H *
          ((Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) a *
             (Hinv (Pi.single (M := fun _ : ι => ℝ) c (1 : ℝ))) b
           + (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) b *
             (Hinv (Pi.single (M := fun _ : ι => ℝ) c (1 : ℝ))) a
           + (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) c *
             (Hinv (Pi.single (M := fun _ : ι => ℝ) b (1 : ℝ))) a) := by
  classical
  -- Step 1: pointwise contraction `u_d = ∑_l (Hinv e_d) l · (Hu) l`.
  have h_h_inv : H (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) =
      Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ) := by
    have := congrArg (fun f => f (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ)))
      hGauss.H_inv_right
    simpa using this
  have h_contract : ∀ u : ι → ℝ,
      u d = ∑ l, (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l * (H u) l := by
    intro u
    have h_sym := hGauss.H_symm u
      (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ)))
    rw [h_h_inv] at h_sym
    have h_lhs : ∑ k, u k * (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ)) k = u d := by
      rw [Finset.sum_eq_single d]
      · rw [Pi.single_eq_same]; ring
      · intros k _ hk
        have h_zero : Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ) k = 0 := by
          simp [Pi.single_apply, hk.symm]
        rw [h_zero]; ring
      · intro h; exact absurd (Finset.mem_univ d) h
    rw [h_lhs] at h_sym
    exact h_sym
  -- Step 2: rewrite the integrand and swap sum/integral.
  have h_integrand_eq : ∀ u : ι → ℝ,
      u a * u b * u c * u d * gaussianWeight H u =
        ∑ l, (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
              (u a * u b * u c * (H u) l * gaussianWeight H u) := by
    intro u
    have h := h_contract u
    -- u_a u_b u_c · u_d · gW = u_a u_b u_c · (∑_l ... (Hu)_l) · gW
    --                       = ∑_l ((Hinv e_d) l · (u_a u_b u_c (Hu)_l gW))
    calc u a * u b * u c * u d * gaussianWeight H u
        = u a * u b * u c *
            (∑ l, (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l * (H u) l)
            * gaussianWeight H u := by rw [h]
      _ = ∑ l, (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
              (u a * u b * u c * (H u) l * gaussianWeight H u) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intros l _; ring
  rw [show (fun u : ι → ℝ => u a * u b * u c * u d * gaussianWeight H u) =
        fun u => ∑ l, (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
              (u a * u b * u c * (H u) l * gaussianWeight H u)
        from funext h_integrand_eq]
  rw [integral_finset_sum Finset.univ
        (fun l _ => (hGauss.int_3_Hl a b c l).const_mul _)]
  -- Step 3: per l, pull constant out and apply cubic IBP.
  conv_lhs =>
    enter [2, l]
    rw [integral_const_mul]
    rw [gaussian_ibp_cubic_f hGauss a b c l]
  -- Step 4: split the integral inside, then split the outer sum into 3 pieces.
  -- Use that (if l = X then Y else 0) factored via integral_add + integral_const_mul.
  have h_int_each_eq : ∀ l : ι,
      ∫ u : ι → ℝ,
          ((if l = a then u b * u c else 0) +
           (if l = b then u a * u c else 0) +
           (if l = c then u a * u b else 0)) * gaussianWeight H u =
        (if l = a then ∫ u, u b * u c * gaussianWeight H u else 0)
        + (if l = b then ∫ u, u a * u c * gaussianWeight H u else 0)
        + (if l = c then ∫ u, u a * u b * gaussianWeight H u else 0) := by
    intro l
    -- Convert each `if X then Y else 0` to `(if X then 1 else 0) * Y` and
    -- use integral_const_mul to pull the indicator out.
    have h_pt : ∀ u : ι → ℝ,
        ((if l = a then u b * u c else 0) +
         (if l = b then u a * u c else 0) +
         (if l = c then u a * u b else 0)) * gaussianWeight H u =
        (if l = a then (1 : ℝ) else 0) * (u b * u c * gaussianWeight H u)
        + (if l = b then (1 : ℝ) else 0) * (u a * u c * gaussianWeight H u)
        + (if l = c then (1 : ℝ) else 0) * (u a * u b * gaussianWeight H u) := by
      intro u
      split_ifs <;> ring
    rw [show (fun u : ι → ℝ =>
            ((if l = a then u b * u c else 0) +
             (if l = b then u a * u c else 0) +
             (if l = c then u a * u b else 0)) * gaussianWeight H u) =
          fun u =>
            (if l = a then (1 : ℝ) else 0) * (u b * u c * gaussianWeight H u)
            + (if l = b then (1 : ℝ) else 0) * (u a * u c * gaussianWeight H u)
            + (if l = c then (1 : ℝ) else 0) * (u a * u b * gaussianWeight H u)
          from funext h_pt]
    have h1 : Integrable (fun u : ι → ℝ =>
        (if l = a then (1 : ℝ) else 0) * (u b * u c * gaussianWeight H u)) :=
      (hGauss.int_uk_uj_gW b c).const_mul _
    have h2 : Integrable (fun u : ι → ℝ =>
        (if l = b then (1 : ℝ) else 0) * (u a * u c * gaussianWeight H u)) :=
      (hGauss.int_uk_uj_gW a c).const_mul _
    have h3 : Integrable (fun u : ι → ℝ =>
        (if l = c then (1 : ℝ) else 0) * (u a * u b * gaussianWeight H u)) :=
      (hGauss.int_uk_uj_gW a b).const_mul _
    -- Single-lambda integrability for the partial sum (avoids Pi.add mismatch in `rw`).
    have h12 : Integrable (fun u : ι → ℝ =>
        (if l = a then (1 : ℝ) else 0) * (u b * u c * gaussianWeight H u)
        + (if l = b then (1 : ℝ) else 0) * (u a * u c * gaussianWeight H u)) :=
      h1.add h2
    rw [integral_add h12 h3, integral_add h1 h2,
        integral_const_mul, integral_const_mul, integral_const_mul]
    congr 1
    · congr 1
      · split_ifs <;> ring
      · split_ifs <;> ring
    · split_ifs <;> ring
  conv_lhs =>
    enter [2, l]
    rw [h_int_each_eq l]
  -- Step 5: distribute outer (Hinv e_d) l multiplier and split into 3 sums.
  have h_dist : ∀ l : ι,
      (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
        ((if l = a then ∫ u, u b * u c * gaussianWeight H u else 0)
         + (if l = b then ∫ u, u a * u c * gaussianWeight H u else 0)
         + (if l = c then ∫ u, u a * u b * gaussianWeight H u else 0))
      = (if l = a then (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
                       (∫ u, u b * u c * gaussianWeight H u) else 0)
        + (if l = b then (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
                         (∫ u, u a * u c * gaussianWeight H u) else 0)
        + (if l = c then (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
                         (∫ u, u a * u b * gaussianWeight H u) else 0) := by
    intro l
    split_ifs <;> ring
  conv_lhs =>
    enter [2, l]
    rw [h_dist l]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Step 6: collapse each indicator-sum via Finset.sum_eq_single.
  have h_sum_a : ∑ l, (if l = a then (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
                                  (∫ u, u b * u c * gaussianWeight H u) else 0)
      = (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) a *
          (∫ u, u b * u c * gaussianWeight H u) := by
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl]
    · intros l _ hla; rw [if_neg hla]
    · intro h; exact absurd (Finset.mem_univ a) h
  have h_sum_b : ∑ l, (if l = b then (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
                                  (∫ u, u a * u c * gaussianWeight H u) else 0)
      = (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) b *
          (∫ u, u a * u c * gaussianWeight H u) := by
    rw [Finset.sum_eq_single b]
    · rw [if_pos rfl]
    · intros l _ hlb; rw [if_neg hlb]
    · intro h; exact absurd (Finset.mem_univ b) h
  have h_sum_c : ∑ l, (if l = c then (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) l *
                                  (∫ u, u a * u b * gaussianWeight H u) else 0)
      = (Hinv (Pi.single (M := fun _ : ι => ℝ) d (1 : ℝ))) c *
          (∫ u, u a * u b * gaussianWeight H u) := by
    rw [Finset.sum_eq_single c]
    · rw [if_pos rfl]
    · intros l _ hlc; rw [if_neg hlc]
    · intro h; exact absurd (Finset.mem_univ c) h
  rw [h_sum_a, h_sum_b, h_sum_c]
  -- Step 7: apply 2nd-moment formula to the three integrals.
  have h_2nd_bc : ∫ u : ι → ℝ, u b * u c * gaussianWeight H u
      = gaussianZ H * (Hinv (Pi.single (M := fun _ : ι => ℝ) c (1 : ℝ))) b :=
    gaussian_second_moment_eq_inverse_entry_scalar H Hinv
      hGauss.H_inv_right hGauss.H_inj b c hGauss.int_gW
      (hGauss.int_uk_uj_gW · c) (hGauss.int_uj_Hi_gW c)
      (hGauss.fubini_ibp · c)
  have h_2nd_ac : ∫ u : ι → ℝ, u a * u c * gaussianWeight H u
      = gaussianZ H * (Hinv (Pi.single (M := fun _ : ι => ℝ) c (1 : ℝ))) a :=
    gaussian_second_moment_eq_inverse_entry_scalar H Hinv
      hGauss.H_inv_right hGauss.H_inj a c hGauss.int_gW
      (hGauss.int_uk_uj_gW · c) (hGauss.int_uj_Hi_gW c)
      (hGauss.fubini_ibp · c)
  have h_2nd_ab : ∫ u : ι → ℝ, u a * u b * gaussianWeight H u
      = gaussianZ H * (Hinv (Pi.single (M := fun _ : ι => ℝ) b (1 : ℝ))) a :=
    gaussian_second_moment_eq_inverse_entry_scalar H Hinv
      hGauss.H_inv_right hGauss.H_inj a b hGauss.int_gW
      (hGauss.int_uk_uj_gW · b) (hGauss.int_uj_Hi_gW b)
      (hGauss.fubini_ibp · b)
  rw [h_2nd_bc, h_2nd_ac, h_2nd_ab]
  ring

end FourthMomentFormula

set_option maxHeartbeats 800000

section GaussianContractions

variable {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}

/-- **4th-moment contraction (`A`-quadratic form against Gaussian)**:
$\int \tfrac12\,u^\top A u \cdot gW = Z\cdot\tfrac12\,\mathrm{tr}(A\Sigma)$.
The first specialised Gaussian contraction lemma — used as the leading
Gaussian term of `lem:laplace_exp` (Hessian piece). -/
private lemma gaussian_quad_expectation
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hA_symm : ∀ u v : ι → ℝ, dot u (A v) = dot v (A u))
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∫ u : ι → ℝ, (1 / 2 : ℝ) * quadForm A u * gaussianWeight H u
      = gaussianZ H * (1 / 2 : ℝ) * trASig A Hinv := by
  classical
  -- Step 1: pointwise expansion of `quadForm A u` to a double Finset sum.
  have h_pt : ∀ u : ι → ℝ,
      (1 / 2 : ℝ) * quadForm A u * gaussianWeight H u =
        ∑ i, ∑ j, (1 / 2 : ℝ) *
          ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) *
          (u i * u j * gaussianWeight H u) := by
    intro u
    unfold quadForm
    -- u i * (A u) i = u i * ∑ j, u j * (A e_j) i
    -- = ∑ j, (A e_j) i * (u i * u j).
    have h_inner : ∀ i : ι, u i * (A u) i =
        ∑ j, (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (u i * u j) := by
      intro i
      rw [H_apply_eq_sum A u i]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _; ring
    simp_rw [h_inner]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _; ring
  -- Step 2: rewrite the integrand using the pointwise expansion.
  rw [show (fun u : ι → ℝ => (1 / 2 : ℝ) * quadForm A u * gaussianWeight H u) =
        fun u => ∑ i, ∑ j, (1 / 2 : ℝ) *
          ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) *
          (u i * u j * gaussianWeight H u)
        from funext h_pt]
  -- Step 3: per-term identity from `gaussian_second_moment_eq_inverse_entry_scalar`.
  have h_inner : ∀ i j : ι,
      ∫ u : ι → ℝ, (1 / 2 : ℝ) *
            ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) *
            (u i * u j * gaussianWeight H u)
        = (1 / 2 : ℝ) *
            ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) *
            (gaussianZ H *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) := by
    intro i j
    rw [integral_const_mul]
    rw [gaussian_second_moment_eq_inverse_entry_scalar H Hinv
        hGauss.H_inv_right hGauss.H_inj i j hGauss.int_gW
        (hGauss.int_uk_uj_gW · j) (hGauss.int_uj_Hi_gW j)
        (hGauss.fubini_ibp · j)]
  -- Step 4: swap inner sum / integral.
  rw [integral_finset_sum Finset.univ
        (fun i _ =>
          (integrable_finset_sum Finset.univ
            (fun j _ => (hGauss.int_uk_uj_gW i j).const_mul _)))]
  conv_lhs =>
    enter [2, i]
    rw [integral_finset_sum Finset.univ
          (fun j _ => (hGauss.int_uk_uj_gW i j).const_mul _)]
    enter [2, j]
    rw [h_inner i j]
  -- Step 5: pull `gaussianZ H` and `(1/2)` outside the double sum.
  have h_factor : ∀ i j : ι,
      (1 / 2 : ℝ) *
          ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) *
          (gaussianZ H *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)
        = gaussianZ H * ((1 / 2 : ℝ) *
            ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)) := by
    intro i j; ring
  simp_rw [h_factor]
  -- After simp_rw, goal:
  --   ∑ i, ∑ j, gaussianZ H * (1/2 * (A_e_j_i * Hinv_e_j_i)) = Z * (1/2) * trASig A Hinv.
  -- Pull `gaussianZ H` and `(1/2)` outside both sums via simp_rw on the inner.
  simp_rw [← Finset.mul_sum]
  -- Step 6: identify the remaining double sum with `trASig A Hinv`.
  unfold trASig
  have h_sum_eq : ∑ i, ∑ j,
        ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)
      = ∑ j, (A (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)))) j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    -- ∑ i, (A e_j) i * (Hinv e_j) i = dot (A e_j) (Hinv e_j)
    --                               = dot e_j (A (Hinv e_j)) = (A (Hinv e_j)) j.
    have h_dot : ∑ i, (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i
        = dot (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)))
            (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) := by
      unfold dot; rfl
    rw [h_dot]
    -- dot (A e_j) (Hinv e_j) = dot (Hinv e_j) (A e_j) (by symmetry of dot)
    --                       = dot e_j (A (Hinv e_j)) (by hA_symm).
    have h_dot_comm : dot (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)))
          (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)))
        = dot (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)))
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) := by
      unfold dot; apply Finset.sum_congr rfl; intros; ring
    rw [h_dot_comm,
      hA_symm (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)))
        (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))]
    -- dot e_j (A (Hinv e_j)) = (A (Hinv e_j)) j.
    unfold dot
    rw [Finset.sum_eq_single j]
    · simp [Pi.single_eq_same]
    · intros i _ hij
      have h_zero : Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ) i = 0 := by
        simp [Pi.single_apply, hij.symm]
      rw [h_zero]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [h_sum_eq]
  ring

/-- **4th-moment contraction (linear · cubic against Gaussian)**:
$\int (a\cdot u)\,T(u,u,u)\,gW = Z\cdot 3\,(\Sigma a)\cdot(T{:}\Sigma)$.
The second specialised Gaussian contraction lemma — used in
`lem:laplace_exp` (cubic-anharmonic piece) and `lem:laplace_cov2` (term 2). -/
private lemma gaussian_linear_cubic
    (a : ι → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (hT_symm : ∀ σ : Equiv.Perm (Fin 3), ∀ v : Fin 3 → (ι → ℝ),
      T (fun i => v (σ i)) = T v)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∫ u : ι → ℝ, dot a u * T (fun _ => u) * gaussianWeight H u
      = gaussianZ H * 3 * dot (Hinv a) (tensorContractMatrix T Hinv) := by
  classical
  let cov : ι → ι → ℝ := fun i j =>
    (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j
  have hcov_symm : ∀ i j : ι, cov i j = cov j i := by
    intro i j
    have hs := Hinv_symm (H := H) (Hinv := Hinv)
        (hGauss := hGauss.toLaplaceCovHypotheses)
        (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))
        (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))
    simpa [cov, Pi.single_apply] using hs
  have h2mom : ∀ i j : ι,
      ∫ u : ι → ℝ, u i * u j * gaussianWeight H u = gaussianZ H * cov i j := by
    intro i j
    have h_basic : ∫ u : ι → ℝ, u i * u j * gaussianWeight H u
        = gaussianZ H *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i :=
      gaussian_second_moment_eq_inverse_entry_scalar H Hinv
        hGauss.H_inv_right hGauss.H_inj i j hGauss.int_gW
        (hGauss.int_uk_uj_gW · j) (hGauss.int_uj_Hi_gW j)
        (hGauss.fubini_ibp · j)
    have h_cov_eq : cov i j = cov j i := hcov_symm i j
    -- cov j i = (Hinv e_j) i, which is the basic 2nd-moment value.
    rw [h_basic, h_cov_eq]
  -- T-symmetry coordinate swap helpers (per GPT recipe + fix-up).
  have hswap01 : ∀ x y z : ι,
      (fun n : Fin 3 =>
        match (Equiv.swap (0 : Fin 3) 1) n with
        | 0 => Pi.single (M := fun _ : ι => ℝ) x (1 : ℝ)
        | 1 => Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ)
        | 2 => Pi.single (M := fun _ : ι => ℝ) z (1 : ℝ)) =
      (fun n : Fin 3 =>
        match n with
        | 0 => Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ)
        | 1 => Pi.single (M := fun _ : ι => ℝ) x (1 : ℝ)
        | 2 => Pi.single (M := fun _ : ι => ℝ) z (1 : ℝ)) := by
    intros x y z
    funext n
    fin_cases n <;> simp [Equiv.swap_apply_def]
  have hsym01 : ∀ x y z : ι, Tcoord T y x z = Tcoord T x y z := by
    intro x y z
    have h := hT_symm (Equiv.swap (0 : Fin 3) 1) (fun n : Fin 3 =>
      match n with
      | 0 => Pi.single (M := fun _ : ι => ℝ) x (1 : ℝ)
      | 1 => Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ)
      | 2 => Pi.single (M := fun _ : ι => ℝ) z (1 : ℝ))
    rw [hswap01 x y z] at h
    -- h : T (fun n => match n with | 0 => Pi.single y 1 | ...) = T (fun n => match n with | 0 => Pi.single x 1 | ...)
    -- These are exactly Tcoord T y x z = Tcoord T x y z by definition.
    exact h
  -- Similar swap for slots 1, 2
  have hswap12 : ∀ x y z : ι,
      (fun n : Fin 3 =>
        match (Equiv.swap (1 : Fin 3) 2) n with
        | 0 => Pi.single (M := fun _ : ι => ℝ) x (1 : ℝ)
        | 1 => Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ)
        | 2 => Pi.single (M := fun _ : ι => ℝ) z (1 : ℝ)) =
      (fun n : Fin 3 =>
        match n with
        | 0 => Pi.single (M := fun _ : ι => ℝ) x (1 : ℝ)
        | 1 => Pi.single (M := fun _ : ι => ℝ) z (1 : ℝ)
        | 2 => Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ)) := by
    intros x y z
    funext n
    fin_cases n <;> simp [Equiv.swap_apply_def]
  have hsym12 : ∀ x y z : ι, Tcoord T x z y = Tcoord T x y z := by
    intro x y z
    have h := hT_symm (Equiv.swap (1 : Fin 3) 2) (fun n : Fin 3 =>
      match n with
      | 0 => Pi.single (M := fun _ : ι => ℝ) x (1 : ℝ)
      | 1 => Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ)
      | 2 => Pi.single (M := fun _ : ι => ℝ) z (1 : ℝ))
    rw [hswap12 x y z] at h
    exact h
  -- Pointwise expansion: (Hu)_l · T(u,u,u) · gW = ∑_{i,j,k} Tcoord T i j k · (u_i u_j u_k (Hu)_l gW).
  have hExpandHuT : ∀ l : ι, ∀ u : ι → ℝ,
      (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u =
        ∑ i, ∑ j, ∑ k,
          Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u) := by
    intro l u
    rw [T_apply_diag_eq_sum]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  -- Hinv e_j basis decomposition (used in hcontract).
  have hHinv_basis : ∀ j : ι, Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)) =
      ∑ k, cov j k • (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ)) := by
    intro j
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- LHS: (Hinv e_j) m = cov j m. RHS: ∑ k, cov j k * (Pi.single k 1) m = cov j m (single survives).
    rw [show (cov j) = (fun k => cov j k) from rfl]
    rw [Finset.sum_eq_single m]
    · simp [cov, Pi.single_apply]
    · intros k _ hk
      have : Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ) m = 0 := by
        simp [Pi.single_apply, hk]
      rw [this]; ring
    · intro h; exact absurd (Finset.mem_univ m) h
  -- hcontract: ∑_{j,k} Tcoord T l j k · cov j k = tensorContractMatrix T Hinv l.
  -- Expand the slot-2 Hinv via multilinearity.
  have hcontract : ∀ l : ι,
      (∑ j, ∑ k, Tcoord T l j k * cov j k) = tensorContractMatrix T Hinv l := by
    intro l
    unfold tensorContractMatrix
    refine Finset.sum_congr rfl ?_
    intro j _
    -- Slot-2 expansion: T (e_l, e_j, Hinv e_j) = T (e_l, e_j, ∑_k cov j k • e_k)
    --                                          = ∑_k cov j k • T (e_l, e_j, e_k)
    --                                          = ∑_k cov j k * Tcoord T l j k.
    -- Symmetrically equal to ∑_k Tcoord T l j k * cov j k.
    have h_slot2 :
        T (fun k : Fin 3 => match k with
          | 0 => Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ)
          | 1 => Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)
          | 2 => Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) =
        ∑ k, cov j k * Tcoord T l j k := by
      -- Set up `m` matching the slot configuration with slot 2 = Hinv e_j.
      set m : Fin 3 → (ι → ℝ) := fun n => match n with
        | 0 => Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ)
        | 1 => Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)
        | 2 => Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)) with hm_def
      have hm2 : m 2 = Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)) := rfl
      -- Express T m as T (Function.update m 2 (∑ k, cov j k • e_k)).
      have h_eq : T m = T (Function.update m (2 : Fin 3)
            (∑ k, cov j k • (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ)))) := by
        congr 1
        funext n
        by_cases h : n = 2
        · subst h
          rw [Function.update_self]
          exact hHinv_basis j
        · simp [Function.update, h]
      rw [h_eq]
      -- Apply map_update_sum at the multilinear-map level. Need to bridge T vs T.toMultilinearMap.
      change T.toMultilinearMap (Function.update m (2 : Fin 3)
          (∑ k, cov j k • (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ)))) = _
      rw [T.toMultilinearMap.map_update_sum
          (t := Finset.univ) (i := (2 : Fin 3))
          (g := fun k : ι => cov j k • (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) (m := m)]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [T.toMultilinearMap.map_update_smul (m := m) (i := (2 : Fin 3))
          (c := cov j k) (x := Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))]
      -- Goal: cov j k • T (Function.update m 2 (Pi.single k 1)) = cov j k * Tcoord T l j k.
      have h_update_eq :
          (Function.update m (2 : Fin 3)
              (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) =
          (fun n : Fin 3 => match n with
            | 0 => Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ)
            | 1 => Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ)
            | 2 => Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ)) := by
        funext n
        fin_cases n <;> simp [Function.update, hm_def]
      rw [h_update_eq]
      show cov j k • Tcoord T l j k = cov j k * Tcoord T l j k
      simp [smul_eq_mul]
    rw [h_slot2]
    refine Finset.sum_congr rfl ?_
    intro k _; ring
  -- hterm: 4-moment per (i,j,k,l) via cubic IBP + 2nd moment.
  have hterm : ∀ i j k l : ι,
      ∫ u : ι → ℝ, u i * u j * u k * (H u) l * gaussianWeight H u
        = gaussianZ H *
            ((if l = i then cov j k else 0) +
             (if l = j then cov i k else 0) +
             (if l = k then cov i j else 0)) := by
    intro i j k l
    -- Apply cubic IBP.
    have h_ibp := gaussian_ibp_cubic_f (H := H) (Hinv := Hinv) (hGauss := hGauss) i j k l
    rw [h_ibp]
    -- Integrand is `((if l=i then u_j u_k else 0) + (if l=j then u_i u_k else 0) +
    --                (if l=k then u_i u_j else 0)) * gW`.
    -- Distribute: each (if X then Y else 0) * gW = if X then Y*gW else 0.
    have h_distrib : ∀ u : ι → ℝ,
        ((if l = i then u j * u k else 0) +
         (if l = j then u i * u k else 0) +
         (if l = k then u i * u j else 0)) * gaussianWeight H u =
        (if l = i then u j * u k * gaussianWeight H u else 0) +
        (if l = j then u i * u k * gaussianWeight H u else 0) +
        (if l = k then u i * u j * gaussianWeight H u else 0) := by
      intro u; split_ifs <;> ring
    rw [show (fun u : ι → ℝ =>
        ((if l = i then u j * u k else 0) +
         (if l = j then u i * u k else 0) +
         (if l = k then u i * u j else 0)) * gaussianWeight H u) =
      fun u =>
        (if l = i then u j * u k * gaussianWeight H u else 0) +
        (if l = j then u i * u k * gaussianWeight H u else 0) +
        (if l = k then u i * u j * gaussianWeight H u else 0) from funext h_distrib]
    -- Split via integral_add. Need integrability of each indicator term.
    have hint_jk : Integrable (fun u : ι → ℝ =>
        (if l = i then u j * u k * gaussianWeight H u else 0)) := by
      by_cases hli : l = i
      · simp only [if_pos hli]; exact hGauss.int_uk_uj_gW j k
      · simp only [if_neg hli]; exact integrable_zero _ _ _
    have hint_ik : Integrable (fun u : ι → ℝ =>
        (if l = j then u i * u k * gaussianWeight H u else 0)) := by
      by_cases hlj : l = j
      · simp only [if_pos hlj]; exact hGauss.int_uk_uj_gW i k
      · simp only [if_neg hlj]; exact integrable_zero _ _ _
    have hint_ij : Integrable (fun u : ι → ℝ =>
        (if l = k then u i * u j * gaussianWeight H u else 0)) := by
      by_cases hlk : l = k
      · simp only [if_pos hlk]; exact hGauss.int_uk_uj_gW i j
      · simp only [if_neg hlk]; exact integrable_zero _ _ _
    have hint_jk_ik : Integrable (fun u : ι → ℝ =>
        (if l = i then u j * u k * gaussianWeight H u else 0) +
        (if l = j then u i * u k * gaussianWeight H u else 0)) :=
      hint_jk.add hint_ik
    rw [integral_add hint_jk_ik hint_ij, integral_add hint_jk hint_ik]
    -- Each integral = if condition then 2nd-moment value else 0.
    have h_int1 : ∫ u : ι → ℝ,
        (if l = i then u j * u k * gaussianWeight H u else 0)
        = if l = i then gaussianZ H * cov j k else 0 := by
      by_cases hli : l = i
      · simp only [if_pos hli]; exact h2mom j k
      · simp only [if_neg hli, MeasureTheory.integral_zero]
    have h_int2 : ∫ u : ι → ℝ,
        (if l = j then u i * u k * gaussianWeight H u else 0)
        = if l = j then gaussianZ H * cov i k else 0 := by
      by_cases hlj : l = j
      · simp only [if_pos hlj]; exact h2mom i k
      · simp only [if_neg hlj, MeasureTheory.integral_zero]
    have h_int3 : ∫ u : ι → ℝ,
        (if l = k then u i * u j * gaussianWeight H u else 0)
        = if l = k then gaussianZ H * cov i j else 0 := by
      by_cases hlk : l = k
      · simp only [if_pos hlk]; exact h2mom i j
      · simp only [if_neg hlk, MeasureTheory.integral_zero]
    rw [h_int1, h_int2, h_int3]
    -- Final: factor out gaussianZ H.
    by_cases hli : l = i <;> by_cases hlj : l = j <;> by_cases hlk : l = k <;>
      simp [hli, hlj, hlk, mul_add, mul_zero, add_zero, zero_add]
  -- 3 trace identifications.
  have hS1 : ∀ l : ι,
      (∑ i, ∑ j, ∑ k, Tcoord T i j k *
        (gaussianZ H * (if l = i then cov j k else 0)))
        = gaussianZ H * tensorContractMatrix T Hinv l := by
    intro l
    have h_inner : ∀ i, ∑ j, ∑ k, Tcoord T i j k *
        (gaussianZ H * (if l = i then cov j k else 0))
        = if l = i then gaussianZ H * (∑ j, ∑ k, Tcoord T i j k * cov j k) else 0 := by
      intro i
      by_cases hli : l = i
      · simp only [if_pos hli]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intros j _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intros k _; ring
      · simp only [if_neg hli, mul_zero]
        simp
    rw [show (∑ i, ∑ j, ∑ k, Tcoord T i j k *
            (gaussianZ H * (if l = i then cov j k else 0))) =
          ∑ i, (if l = i then gaussianZ H * (∑ j, ∑ k, Tcoord T i j k * cov j k) else 0)
        from Finset.sum_congr rfl (fun i _ => h_inner i)]
    rw [Finset.sum_eq_single l]
    · rw [if_pos rfl, hcontract l]
    · intros i _ hli; rw [if_neg (Ne.symm hli)]
    · intro h; exact absurd (Finset.mem_univ l) h
  have hS2 : ∀ l : ι,
      (∑ i, ∑ j, ∑ k, Tcoord T i j k *
        (gaussianZ H * (if l = j then cov i k else 0)))
        = gaussianZ H * tensorContractMatrix T Hinv l := by
    intro l
    -- Push j-sum to outer: by Finset.sum_comm.
    rw [show (∑ i, ∑ j, ∑ k, Tcoord T i j k *
              (gaussianZ H * (if l = j then cov i k else 0))) =
          ∑ j, ∑ i, ∑ k, Tcoord T i j k *
              (gaussianZ H * (if l = j then cov i k else 0)) from Finset.sum_comm]
    have h_inner : ∀ j, ∑ i, ∑ k, Tcoord T i j k *
        (gaussianZ H * (if l = j then cov i k else 0))
        = if l = j then gaussianZ H * (∑ i, ∑ k, Tcoord T i j k * cov i k) else 0 := by
      intro j
      by_cases hlj : l = j
      · simp only [if_pos hlj]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intros i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intros k _; ring
      · simp only [if_neg hlj, mul_zero]
        simp
    rw [show (∑ j, ∑ i, ∑ k, Tcoord T i j k *
            (gaussianZ H * (if l = j then cov i k else 0))) =
          ∑ j, (if l = j then gaussianZ H * (∑ i, ∑ k, Tcoord T i j k * cov i k) else 0)
        from Finset.sum_congr rfl (fun j _ => h_inner j)]
    rw [Finset.sum_eq_single l]
    · rw [if_pos rfl]
      -- Need: ∑ i, ∑ k, Tcoord T i l k * cov i k = tensorContractMatrix T Hinv l
      -- Use hsym01: Tcoord T i l k = Tcoord T l i k
      rw [show (∑ i, ∑ k, Tcoord T i l k * cov i k) =
            ∑ i, ∑ k, Tcoord T l i k * cov i k from by
        refine Finset.sum_congr rfl ?_
        intros i _
        refine Finset.sum_congr rfl ?_
        intros k _
        rw [hsym01 l i k]]
      rw [hcontract l]
    · intros j _ hlj; rw [if_neg (Ne.symm hlj)]
    · intro h; exact absurd (Finset.mem_univ l) h
  have hS3 : ∀ l : ι,
      (∑ i, ∑ j, ∑ k, Tcoord T i j k *
        (gaussianZ H * (if l = k then cov i j else 0)))
        = gaussianZ H * tensorContractMatrix T Hinv l := by
    intro l
    -- Push k-sum to outermost: ∑ i ∑ j ∑ k → ∑ k ∑ i ∑ j.
    rw [show (∑ i, ∑ j, ∑ k, Tcoord T i j k *
              (gaussianZ H * (if l = k then cov i j else 0))) =
          ∑ k, ∑ i, ∑ j, Tcoord T i j k *
              (gaussianZ H * (if l = k then cov i j else 0)) from by
        rw [show (∑ i, ∑ j, ∑ k, Tcoord T i j k *
                (gaussianZ H * (if l = k then cov i j else 0))) =
              ∑ i, ∑ k, ∑ j, Tcoord T i j k *
                (gaussianZ H * (if l = k then cov i j else 0)) from by
          refine Finset.sum_congr rfl ?_
          intros i _
          rw [Finset.sum_comm]]
        rw [Finset.sum_comm]]
    have h_inner : ∀ k, ∑ i, ∑ j, Tcoord T i j k *
        (gaussianZ H * (if l = k then cov i j else 0))
        = if l = k then gaussianZ H * (∑ i, ∑ j, Tcoord T i j k * cov i j) else 0 := by
      intro k
      by_cases hlk : l = k
      · simp only [if_pos hlk]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intros i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intros j _; ring
      · simp only [if_neg hlk, mul_zero]
        simp
    rw [show (∑ k, ∑ i, ∑ j, Tcoord T i j k *
            (gaussianZ H * (if l = k then cov i j else 0))) =
          ∑ k, (if l = k then gaussianZ H * (∑ i, ∑ j, Tcoord T i j k * cov i j) else 0)
        from Finset.sum_congr rfl (fun k _ => h_inner k)]
    rw [Finset.sum_eq_single l]
    · rw [if_pos rfl]
      -- Need: ∑ i, ∑ j, Tcoord T i j l * cov i j = tensorContractMatrix T Hinv l
      -- Use hsym12 + hsym01: Tcoord T i j l = Tcoord T i l j = Tcoord T l i j.
      rw [show (∑ i, ∑ j, Tcoord T i j l * cov i j) =
            ∑ i, ∑ j, Tcoord T l i j * cov i j from by
        refine Finset.sum_congr rfl ?_
        intros i _
        refine Finset.sum_congr rfl ?_
        intros j _
        rw [show Tcoord T i j l = Tcoord T i l j from (hsym12 i j l).symm]
        rw [hsym01 i l j]]
      rw [hcontract l]
    · intros k _ hlk; rw [if_neg (Ne.symm hlk)]
    · intro h; exact absurd (Finset.mem_univ l) h
  -- Per-l contraction: ∫ (Hu)_l · T(u,u,u) · gW = Z · 3 · tCM T Hinv l.
  have hfixed : ∀ l : ι,
      ∫ u : ι → ℝ, (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u
        = gaussianZ H * 3 * tensorContractMatrix T Hinv l := by
    intro l
    -- Integrability of each (i,j,k) term.
    have hInt_ijk : ∀ i j k : ι,
        Integrable (fun u : ι → ℝ =>
          Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u)) := by
      intros i j k
      exact (hGauss.int_3_Hl i j k l).const_mul (Tcoord T i j k)
    have hInt_ij : ∀ i j : ι,
        Integrable (fun u : ι → ℝ =>
          ∑ k, Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u)) := by
      intros i j
      exact integrable_finset_sum _ (fun k _ => hInt_ijk i j k)
    have hInt_i : ∀ i : ι,
        Integrable (fun u : ι → ℝ =>
          ∑ j, ∑ k, Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u)) := by
      intro i
      exact integrable_finset_sum _ (fun j _ => hInt_ij i j)
    -- Calc chain:
    have h_step1 : ∫ u : ι → ℝ, (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u
        = ∫ u : ι → ℝ, ∑ i, ∑ j, ∑ k,
            Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (hExpandHuT l)
    rw [h_step1]
    -- Swap quadruple sum / integral.
    rw [integral_finset_sum _ (fun i _ => hInt_i i)]
    conv_lhs =>
      enter [2, i]
      rw [integral_finset_sum _ (fun j _ => hInt_ij i j)]
      enter [2, j]
      rw [integral_finset_sum _ (fun k _ => hInt_ijk i j k)]
      enter [2, k]
      rw [integral_const_mul]
      rw [hterm i j k l]
    -- Goal: ∑ i ∑ j ∑ k, Tcoord T i j k * (Z * (3-pairing sum)) = Z * 3 * tCM T Hinv l.
    -- Distribute the 3-pairing sum into 3 sums via h_dist.
    have h_dist : ∀ i j k : ι,
        Tcoord T i j k *
          (gaussianZ H *
            ((if l = i then cov j k else 0) +
             (if l = j then cov i k else 0) +
             (if l = k then cov i j else 0)))
        = Tcoord T i j k * (gaussianZ H * (if l = i then cov j k else 0))
          + Tcoord T i j k * (gaussianZ H * (if l = j then cov i k else 0))
          + Tcoord T i j k * (gaussianZ H * (if l = k then cov i j else 0)) := by
      intros i j k; ring
    conv_lhs =>
      enter [2, i, 2, j, 2, k]
      rw [h_dist i j k]
    -- Sum-add-distrib: ∑ (a+b+c) = ∑ a + ∑ b + ∑ c. Apply 3 times nested.
    rw [show (∑ i, ∑ j, ∑ k,
          (Tcoord T i j k * (gaussianZ H * (if l = i then cov j k else 0)) +
           Tcoord T i j k * (gaussianZ H * (if l = j then cov i k else 0)) +
           Tcoord T i j k * (gaussianZ H * (if l = k then cov i j else 0)))) =
        (∑ i, ∑ j, ∑ k, Tcoord T i j k * (gaussianZ H * (if l = i then cov j k else 0))) +
        (∑ i, ∑ j, ∑ k, Tcoord T i j k * (gaussianZ H * (if l = j then cov i k else 0))) +
        (∑ i, ∑ j, ∑ k, Tcoord T i j k * (gaussianZ H * (if l = k then cov i j else 0)))
        from by
      simp only [Finset.sum_add_distrib]]
    rw [hS1 l, hS2 l, hS3 l]
    ring
  -- Pointwise: dot a u * T(u,u,u) * gW = ∑_l (Hinv a)_l * ((Hu)_l * T(u,u,u) * gW).
  have hExpandMain : ∀ u : ι → ℝ,
      dot a u * T (fun _ : Fin 3 => u) * gaussianWeight H u
        = ∑ l, (Hinv a) l *
            ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
    intro u
    rw [dot_eq_sum_Hinv_mul_H (H := H) (Hinv := Hinv)
          (hGauss := hGauss.toLaplaceCovHypotheses) a u]
    calc
      (∑ l, (Hinv a) l * (H u) l) * T (fun _ : Fin 3 => u) * gaussianWeight H u
          = (∑ l, (Hinv a) l * (H u) l) *
              (T (fun _ : Fin 3 => u) * gaussianWeight H u) := by ring
        _ = ∑ l, ((Hinv a) l * (H u) l) *
              (T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
            rw [Finset.sum_mul]
        _ = ∑ l, (Hinv a) l *
              ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
            refine Finset.sum_congr rfl ?_
            intros l _; ring
  -- Integrability for the main calc.
  have hIntHuT : ∀ l : ι, Integrable (fun u : ι → ℝ =>
      (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
    intro l
    have hRHS_int : Integrable (fun u : ι → ℝ =>
        ∑ i, ∑ j, ∑ k,
          Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u)) := by
      refine integrable_finset_sum _ (fun i _ => ?_)
      refine integrable_finset_sum _ (fun j _ => ?_)
      refine integrable_finset_sum _ (fun k _ => ?_)
      exact (hGauss.int_3_Hl i j k l).const_mul _
    exact hRHS_int.congr <|
      Filter.Eventually.of_forall (fun u => (hExpandHuT l u).symm)
  have hIntMain : ∀ l : ι, Integrable (fun u : ι → ℝ =>
      (Hinv a) l * ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u)) :=
    fun l => (hIntHuT l).const_mul _
  -- Final calc.
  calc ∫ u : ι → ℝ, dot a u * T (fun _ : Fin 3 => u) * gaussianWeight H u
      = ∫ u : ι → ℝ, ∑ l, (Hinv a) l *
          ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall hExpandMain
    _ = ∑ l, ∫ u : ι → ℝ,
          (Hinv a) l * ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
        rw [integral_finset_sum _ (fun l _ => hIntMain l)]
    _ = ∑ l, (Hinv a) l *
          ∫ u : ι → ℝ, (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u := by
        simp_rw [integral_const_mul]
    _ = ∑ l, (Hinv a) l * (gaussianZ H * 3 * tensorContractMatrix T Hinv l) := by
        simp_rw [hfixed]
    _ = gaussianZ H * 3 * dot (Hinv a) (tensorContractMatrix T Hinv) := by
        unfold dot
        rw [show gaussianZ H * 3 * ∑ i, Hinv a i * tensorContractMatrix T Hinv i =
              ∑ i, gaussianZ H * 3 * (Hinv a i * tensorContractMatrix T Hinv i) from by
          rw [Finset.mul_sum]]
        refine Finset.sum_congr rfl ?_
        intros l _; ring

/-- **4th-moment contraction (quad · quad)**:
$\int (\tfrac12 u^\top A u)(\tfrac12 u^\top B u)\,gW
  = Z[\tfrac14\mathrm{tr}(A\Sigma)\mathrm{tr}(B\Sigma) + \tfrac12\mathrm{tr}(A\Sigma B\Sigma)]$.
The third specialised Gaussian contraction lemma — used in `lem:laplace_cov2`
term 1 ($\langle\phi_2\psi_2\rangle$). -/
private lemma gaussian_quad_quad
    (A B : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hA_symm : ∀ u v : ι → ℝ, dot u (A v) = dot v (A u))
    (hB_symm : ∀ u v : ι → ℝ, dot u (B v) = dot v (B u))
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∫ u : ι → ℝ, ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm B u)
        * gaussianWeight H u
      = gaussianZ H * ((1 / 4 : ℝ) * trASig A Hinv * trASig B Hinv
        + (1 / 2 : ℝ) * trASig (A.comp Hinv) (B.comp Hinv)) := by
  classical
  -- Step 1: pointwise expansion via H_apply_eq_sum + sum_mul_sum.
  -- Note: proof's natural sum order is (i, k, j, l) — matching that here.
  have h_pt : ∀ u : ι → ℝ,
      ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm B u) *
        gaussianWeight H u =
        ∑ i, ∑ k, ∑ j, ∑ l,
          ((1 / 4 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k) *
          (u i * u j * u k * u l * gaussianWeight H u) := by
    intro u
    -- quadForm A u = ∑_i ∑_j u_i u_j (A e_j) i.
    have h_qA : quadForm A u =
        ∑ i, ∑ j, u i * u j * (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i := by
      unfold quadForm
      apply Finset.sum_congr rfl; intros i _
      rw [H_apply_eq_sum A u i, Finset.mul_sum]
      apply Finset.sum_congr rfl; intros j _; ring
    have h_qB : quadForm B u =
        ∑ k, ∑ l, u k * u l * (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k := by
      unfold quadForm
      apply Finset.sum_congr rfl; intros k _
      rw [H_apply_eq_sum B u k, Finset.mul_sum]
      apply Finset.sum_congr rfl; intros l _; ring
    rw [h_qA, h_qB]
    -- Now: (1/2 * X) * (1/2 * Y) * gW where X, Y are double sums.
    -- = (1/4) X Y gW
    -- = (1/4) [∑_i ∑_j ...] [∑_k ∑_l ...] gW
    -- = (1/4) ∑_i ∑_j ∑_k ∑_l ... gW (via sum_mul_sum twice).
    rw [show ((1 / 2 : ℝ) *
            ∑ i, ∑ j, u i * u j *
              (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) *
          ((1 / 2 : ℝ) *
            ∑ k, ∑ l, u k * u l *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k) *
          gaussianWeight H u =
          ((1 / 4 : ℝ) * gaussianWeight H u) *
            ((∑ i, ∑ j, u i * u j *
                (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) *
              (∑ k, ∑ l, u k * u l *
                (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k))
        from by ring]
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros k _
    -- Inner: (∑_j ...) * (∑_l ...) → use sum_mul_sum again.
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros l _
    -- Goal now: pointwise term identity. ring handles.
    ring
  -- Step 2: rewrite the integrand using h_pt, then swap quadruple sum/integral.
  rw [show (fun u : ι → ℝ =>
        ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm B u) *
          gaussianWeight H u) =
        fun u => ∑ i, ∑ k, ∑ j, ∑ l,
          ((1 / 4 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k) *
          (u i * u j * u k * u l * gaussianWeight H u) from funext h_pt]
  -- Step 3: per-term integral via gaussian_fourth_moment_formula.
  -- Each term has form `const * ∫ u_i u_j u_k u_l gW`.
  have h_inner : ∀ i j k l : ι,
      ∫ u : ι → ℝ,
          ((1 / 4 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k) *
          (u i * u j * u k * u l * gaussianWeight H u)
      = ((1 / 4 : ℝ) *
          (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k) *
        (gaussianZ H *
          ((Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j
            + (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i
            + (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)) := by
    intro i j k l
    rw [integral_const_mul]
    rw [gaussian_fourth_moment_formula hGauss i j k l]
  -- Swap quadruple sum/integral. Sum order is (i, k, j, l) per h_pt.
  rw [integral_finset_sum Finset.univ
        (fun i _ => integrable_finset_sum Finset.univ
          (fun k _ => integrable_finset_sum Finset.univ
            (fun j _ => integrable_finset_sum Finset.univ
              (fun l _ => (hGauss.int_4moment i j k l).const_mul _))))]
  conv_lhs =>
    enter [2, i]
    rw [integral_finset_sum Finset.univ
        (fun k _ => integrable_finset_sum Finset.univ
          (fun j _ => integrable_finset_sum Finset.univ
            (fun l _ => (hGauss.int_4moment i j k l).const_mul _)))]
    enter [2, k]
    rw [integral_finset_sum Finset.univ
        (fun j _ => integrable_finset_sum Finset.univ
          (fun l _ => (hGauss.int_4moment i j k l).const_mul _))]
    enter [2, j]
    rw [integral_finset_sum Finset.univ
        (fun l _ => (hGauss.int_4moment i j k l).const_mul _)]
    enter [2, l]
    rw [h_inner i j k l]
  -- Step 4: identify the three Wick-pairing sums with trace forms.
  -- Distribute the sum over (Pairing1 + Pairing2 + Pairing3) and pull out Z, 1/4.
  have h_distrib : ∀ i k j l : ι,
      (1 / 4 : ℝ) * (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
        (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
        (gaussianZ H *
          ((Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j
          + (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i
          + (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i))
      = gaussianZ H * (1 / 4 : ℝ) *
          ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j
          + (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i
          + (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) := by
    intros i k j l; ring
  conv_lhs =>
    enter [2, i, 2, k, 2, j, 2, l]
    rw [h_distrib i k j l]
  -- Pull out `gaussianZ H * (1/4)` from the quadruple sum.
  simp_rw [← Finset.mul_sum]
  -- Now the sum is over `(P1ijkl + P2ijkl + P3ijkl)` where:
  -- P1 = A_ij B_kl Σ_li Σ_kj, P2 = A_ij B_kl Σ_lj Σ_ki, P3 = A_ij B_kl Σ_lk Σ_ji.
  -- Distribute: ∑(P1+P2+P3) = ∑P1 + ∑P2 + ∑P3.
  have h_sum_split : ∀ i k j : ι,
      ∑ l, ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j
            + (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i
            + (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)
      = (∑ l, (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j)
        + (∑ l, (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i)
        + (∑ l, (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) := by
    intros; rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Trace identification per GPT recipe in tactics_gaussian_quad_quad.md.
  have hSigSymm : ∀ i j : ι,
      (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i =
        (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j := by
    intro i j
    have h := Hinv_symm (H := H) (Hinv := Hinv)
        (hGauss := hGauss.toLaplaceCovHypotheses)
        (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))
        (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))
    simpa [Pi.single_apply] using h
  have hAij : ∀ i j : ι,
      (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i =
        (A (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) j := by
    intro i j
    have h := hA_symm (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))
        (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))
    simpa [dot, Pi.single_apply, mul_comm] using h
  -- Renamed trASig double-sum forms to avoid bound-variable shadowing.
  have htrAS_form : trASig A Hinv =
      ∑ x, ∑ y, (A (Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ))) x *
        (Hinv (Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ))) x :=
    trASig_eq_double_sum (hGauss := hGauss.toLaplaceCovHypotheses) A
  have htrBS_form : trASig B Hinv =
      ∑ x, ∑ y, (B (Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ))) x *
        (Hinv (Pi.single (M := fun _ : ι => ℝ) y (1 : ℝ))) x :=
    trASig_eq_double_sum (hGauss := hGauss.toLaplaceCovHypotheses) B
  -- h_pair3: factors as trASig A Hinv * trASig B Hinv.
  have h_pair3 :
      (∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)
      = trASig A Hinv * trASig B Hinv := by
    rw [htrAS_form, htrBS_form]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl ?_
    intros x _
    refine Finset.sum_congr rfl ?_
    intros x' _
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl ?_
    intros y _
    refine Finset.sum_congr rfl ?_
    intros y' _
    ring
  -- h_pair2: i ↔ j swap via f/g helpers + sum_comm chain + alpha-renaming.
  -- Per GPT recipe in gpt_responses/tactics_h_pair2.md.
  have h_pair2 :
      (∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i)
        =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j := by
    classical
    let f : ι → ι → ι → ι → ℝ := fun i k j l =>
      (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
        (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
        (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
        (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i
    let g : ι → ι → ι → ι → ℝ := fun i k j l =>
      (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
        (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
        (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
        (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j
    suffices hs :
        (∑ i, ∑ k, ∑ j, ∑ l, f i k j l) =
          ∑ i, ∑ k, ∑ j, ∑ l, g i k j l by
      simpa [f, g] using hs
    have hfg : ∀ i k j l, f j k i l = g i k j l := by
      intro i k j l
      dsimp [f, g]
      rw [← hAij i j]
    calc
      (∑ i, ∑ k, ∑ j, ∑ l, f i k j l)
          = ∑ i, ∑ j, ∑ k, ∑ l, f i k j l := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.sum_comm]
        _ = ∑ j, ∑ i, ∑ k, ∑ l, f i k j l := by
              rw [Finset.sum_comm]
        _ = ∑ j, ∑ k, ∑ i, ∑ l, f i k j l := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [Finset.sum_comm]
        _ = ∑ i, ∑ k, ∑ j, ∑ l, f j k i l := rfl
        _ = ∑ i, ∑ k, ∑ j, ∑ l, g i k j l := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro k _
              refine Finset.sum_congr rfl ?_
              intro j _
              refine Finset.sum_congr rfl ?_
              intro l _
              exact hfg i k j l
  -- h_pair1': identifies trASig (A.comp Hinv) (B.comp Hinv) with the Pairing 1 form.
  have h_pair1' :
      trASig (A.comp Hinv) (B.comp Hinv) =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j := by
    -- trASig X Y = ∑ i, (X (Y (Pi.single i 1))) i.
    -- For X = A.comp Hinv, Y = B.comp Hinv: ((A∘Hinv) ((B∘Hinv) e_i)) i.
    -- = (A (Hinv (B (Hinv e_i)))) i.
    -- Expand B (Hinv e_i) via H_apply_eq_sum: = ∑_l (Hinv e_i) l · (B e_l).
    -- Apply Hinv to that: ∑_l (Hinv e_i) l · (Hinv (B e_l)).
    -- Apply A to that and read at i: ∑_l (Hinv e_i) l · (A (Hinv (B e_l))) i.
    -- Now expand (A (Hinv (B e_l))) i via H_apply_eq_sum:
    --   = ∑_k (Hinv (B e_l)) k · (A e_k) i
    -- Substitute Hinv (B e_l) k via H_apply_eq_sum:
    --   = ∑_j (B e_l) j · (Hinv e_j) k
    -- So (A (Hinv (B e_l))) i = ∑_k ∑_j (B e_l) j · (Hinv e_j) k · (A e_k) i.
    -- Combine: ((A∘Hinv) ((B∘Hinv) e_i)) i = ∑_l ∑_k ∑_j (Hinv e_i) l · (B e_l) j · (Hinv e_j) k · (A e_k) i.
    -- Sum over i: this is the desired sum modulo Σ-symmetry to align indices.
    unfold trASig
    simp only [ContinuousLinearMap.comp_apply]
    -- Per-i pointwise expansion via H_apply_eq_sum × 3.
    have h_per_i : ∀ i : ι,
        (A (Hinv (B (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))))) i =
          ∑ k, ∑ j, ∑ l,
            (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) l *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
              (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) k *
              (A (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i := by
      intro i
      rw [H_apply_eq_sum A (Hinv (B (Hinv (Pi.single i (1 : ℝ))))) i]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [H_apply_eq_sum Hinv (B (Hinv (Pi.single i (1 : ℝ)))) k]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [H_apply_eq_sum B (Hinv (Pi.single i (1 : ℝ))) j]
      rw [Finset.sum_mul, Finset.sum_mul]
    rw [show (∑ i, (A (Hinv (B (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))))) i) =
        ∑ i, ∑ k, ∑ j, ∑ l,
          (Hinv (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))) l *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) k *
            (A (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i
        from Finset.sum_congr rfl (fun i _ => h_per_i i)]
    -- Now LHS: ∑ i ∑ k ∑ j ∑ l (Hinv e_i)_l · (B e_l)_j · (Hinv e_j)_k · (A e_k)_i.
    -- RHS: ∑ i ∑ k ∑ j ∑ l (A e_j)_i · (B e_l)_k · (Hinv e_l)_i · (Hinv e_k)_j.
    -- Need: swap j ↔ k in LHS (via Finset.sum_comm), then use Σ-symm and ring.
    refine Finset.sum_congr rfl ?_
    intro i _
    -- LHS: ∑ k ∑ j ∑ l, ...; RHS: ∑ k ∑ j ∑ l, ...
    -- Bound vars in LHS body have (k j l), in RHS body have (k j l) but in different positions.
    -- After this congr, we still have ∑ k ∑ j ∑ l. Swap k ↔ j to align.
    rw [Finset.sum_comm]  -- swap LHS's outer ∑ k and ∑ j
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    -- Goal: pointwise equality. Use hSigSymm to align (Hinv e_l) i = (Hinv e_i) l.
    rw [← hSigSymm i l]
    ring
  -- Final assembly: distribute the 3-pairing sum, identify each via h_pair3, h_pair2, h_pair1'.
  -- Distribute the inner +-sum into 3 separate quadruple sums.
  have h_distrib_outer : ∀ i k j l : ι,
      gaussianZ H * (1 / 4 : ℝ) *
        ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j +
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i +
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
          (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)
      = gaussianZ H * (1 / 4 : ℝ) *
          ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j) +
        gaussianZ H * (1 / 4 : ℝ) *
          ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i) +
        gaussianZ H * (1 / 4 : ℝ) *
          ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
            (Hinv (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) := by
    intros i k j l; ring
  -- Push gaussianZ H * (1/4) inside the quadruple sum via repeated Finset.mul_sum.
  simp_rw [Finset.mul_sum]
  -- Now LHS: ∑ i ∑ k ∑ j ∑ l, gaussianZ H * (1/4) * (P+P+P).
  -- Apply h_distrib_outer pointwise.
  simp_rw [h_distrib_outer]
  -- Distribute the +-of-3 outwards.
  simp_rw [Finset.sum_add_distrib]
  -- Now we have 3 separate quadruple sums. Pull gaussianZ H * (1/4) out of each.
  simp_rw [← Finset.mul_sum]
  -- Apply h_pair3, h_pair2, h_pair1'.
  rw [h_pair3, h_pair2, ← h_pair1']
  ring

/-- **`quadForm B · gW` integrability** under `LaplaceCov4MomentHypotheses`.
Decompose `quadForm B u = ∑_{i,j} (B e_j)_i · u_i · u_j` and use
`int_uk_uj_gW` per term + `integrable_finset_sum`. -/
private lemma integrable_quadForm_mul_gaussianWeight
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (B : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    Integrable (fun u : ι → ℝ => quadForm B u * gaussianWeight H u) := by
  classical
  have h_eq : ∀ u : ι → ℝ,
      quadForm B u * gaussianWeight H u
      = ∑ i, ∑ j, (B (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          (u i * u j * gaussianWeight H u) := by
    intro u
    unfold quadForm
    simp_rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [H_apply_eq_sum B u i]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _; ring
  rw [show (fun u : ι → ℝ => quadForm B u * gaussianWeight H u)
        = fun u => ∑ i, ∑ j,
            (B (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (u i * u j * gaussianWeight H u) from funext h_eq]
  apply integrable_finset_sum
  intros i _
  apply integrable_finset_sum
  intros j _
  exact (hGauss.toLaplaceCovHypotheses.int_uk_uj_gW i j).const_mul _

/-- **`quadForm A · quadForm B · gW` integrability** under `LaplaceCov4MomentHypotheses`.
Decompose into a finite sum of `u_i u_j u_k u_l · gW` terms via `H_apply_eq_sum`,
each integrable by `int_4moment`. -/
private lemma integrable_quadForm_mul_quadForm_mul_gaussianWeight
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (A B : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    Integrable (fun u : ι → ℝ => quadForm A u * quadForm B u * gaussianWeight H u) := by
  classical
  have h_qA : ∀ u : ι → ℝ, quadForm A u =
      ∑ i, ∑ j, u i * u j * (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i := by
    intro u
    unfold quadForm
    apply Finset.sum_congr rfl; intros i _
    rw [H_apply_eq_sum A u i, Finset.mul_sum]
    apply Finset.sum_congr rfl; intros j _; ring
  have h_qB : ∀ u : ι → ℝ, quadForm B u =
      ∑ k, ∑ l, u k * u l * (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k := by
    intro u
    unfold quadForm
    apply Finset.sum_congr rfl; intros k _
    rw [H_apply_eq_sum B u k, Finset.mul_sum]
    apply Finset.sum_congr rfl; intros l _; ring
  have h_eq : ∀ u : ι → ℝ,
      quadForm A u * quadForm B u * gaussianWeight H u
      = ∑ i, ∑ k, ∑ j, ∑ l,
          ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k) *
          (u i * u j * u k * u l * gaussianWeight H u) := by
    intro u
    rw [h_qA u, h_qB u]
    rw [show (∑ i, ∑ j, u i * u j *
          (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) *
          (∑ k, ∑ l, u k * u l *
            (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k) *
          gaussianWeight H u
        = gaussianWeight H u *
          ((∑ i, ∑ j, u i * u j *
              (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) *
            (∑ k, ∑ l, u k * u l *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k)) from by ring]
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros k _
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros l _
    ring
  rw [show (fun u : ι → ℝ => quadForm A u * quadForm B u * gaussianWeight H u)
        = fun u => ∑ i, ∑ k, ∑ j, ∑ l,
            ((A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k) *
            (u i * u j * u k * u l * gaussianWeight H u) from funext h_eq]
  apply integrable_finset_sum; intros i _
  apply integrable_finset_sum; intros k _
  apply integrable_finset_sum; intros j _
  apply integrable_finset_sum; intros l _
  exact (hGauss.int_4moment i j k l).const_mul _

/-- **Centered 4th-moment contraction** (Step 1 of Lemma B in
`gpt_responses/strategy_stage5_lemmas_attack.md`):
$\int (\tfrac12 \mathrm{Q}_A - \tfrac12 \mathrm{tr}(A\Sigma)) \cdot \tfrac12 \mathrm{Q}_B \cdot gW
  = Z \cdot \tfrac12 \mathrm{tr}(A\Sigma B\Sigma)$.

Centering by `μ_A = (1/2) tr(AΣ)` cancels the disconnected
`(1/4) tr(AΣ) tr(BΣ)` piece of `gaussian_quad_quad`, leaving the
connected `tr(AΣ BΣ)` term. -/
private lemma gaussian_quad_centered_quad_eq
    (A B : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hA_symm : ∀ u v : ι → ℝ, dot u (A v) = dot v (A u))
    (hB_symm : ∀ u v : ι → ℝ, dot u (B v) = dot v (B u))
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∫ u : ι → ℝ, ((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
        ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u
      = gaussianZ H * (1 / 2 : ℝ) *
          trASig (A.comp Hinv) (B.comp Hinv) := by
  have h_qq := gaussian_quad_quad A B hA_symm hB_symm hGauss
  have h_qe := gaussian_quad_expectation B hB_symm hGauss.toLaplaceCovHypotheses
  -- Pointwise: (Q_A - μ_A) · Q_B · gW = Q_A · Q_B · gW - μ_A · Q_B · gW.
  have h_int_QQgW : Integrable (fun u : ι → ℝ =>
      ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm B u) *
        gaussianWeight H u) := by
    have h := integrable_quadForm_mul_quadForm_mul_gaussianWeight A B hGauss
    have h_eq : (fun u : ι → ℝ =>
        ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm B u) *
          gaussianWeight H u)
        = fun u : ι → ℝ => (1 / 4 : ℝ) *
          (quadForm A u * quadForm B u * gaussianWeight H u) := by
      funext u; ring
    rw [h_eq]; exact h.const_mul _
  have h_int_QgW : Integrable (fun u : ι → ℝ =>
      ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u) := by
    have h := integrable_quadForm_mul_gaussianWeight B hGauss
    have h_eq : (fun u : ι → ℝ =>
        ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u)
        = fun u : ι → ℝ => (1 / 2 : ℝ) *
          (quadForm B u * gaussianWeight H u) := by
      funext u; ring
    rw [h_eq]; exact h.const_mul _
  have h_int_const_QgW : Integrable (fun u : ι → ℝ =>
      ((1 / 2 : ℝ) * trASig A Hinv) *
        (((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u)) :=
    h_int_QgW.const_mul _
  have h_pt : ∀ u : ι → ℝ,
      ((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
          ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u
      = ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm B u) *
          gaussianWeight H u
        - ((1 / 2 : ℝ) * trASig A Hinv) *
          (((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u) := by
    intro u; ring
  rw [show (fun u : ι → ℝ =>
        ((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
            ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u)
        = fun u => ((1 / 2 : ℝ) * quadForm A u) *
              ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u
            - ((1 / 2 : ℝ) * trASig A Hinv) *
                (((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u) from
      funext h_pt]
  rw [MeasureTheory.integral_sub h_int_QQgW h_int_const_QgW]
  rw [MeasureTheory.integral_const_mul, h_qq, h_qe]
  ring

/-- **4th-moment contraction (cubic · linear)**:
$\int \tfrac16 \Phi(u,u,u)(b\cdot u)\,gW = Z\cdot\tfrac12(\Sigma b)\cdot(\Phi{:}\Sigma)$.
Symmetric to `gaussian_linear_cubic` modulo the $1/6$ prefactor; the
fourth specialised Gaussian contraction lemma. -/
private lemma gaussian_cubic_linear
    (b : ι → ℝ)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (hΦ_symm : ∀ σ : Equiv.Perm (Fin 3), ∀ v : Fin 3 → (ι → ℝ),
      Φ (fun i => v (σ i)) = Φ v)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∫ u : ι → ℝ, (1 / 6 : ℝ) * Φ (fun _ => u) * dot b u * gaussianWeight H u
      = gaussianZ H * (1 / 2 : ℝ) * dot (Hinv b) (tensorContractMatrix Φ Hinv) := by
  -- Reduce to gaussian_linear_cubic with (a, T) := (b, Φ); both sides differ by 1/6.
  have h := gaussian_linear_cubic (H := H) (Hinv := Hinv) b Φ hΦ_symm hGauss
  -- h : ∫ dot b u * Φ (fun _ => u) * gaussianWeight H u
  --       = gaussianZ H * 3 * dot (Hinv b) (tensorContractMatrix Φ Hinv)
  -- Pull (1/6) inside the integral and rewrite the integrand.
  have h_integrand : ∀ u : ι → ℝ,
      (1 / 6 : ℝ) * Φ (fun _ => u) * dot b u * gaussianWeight H u
      = (1 / 6 : ℝ) *
          (dot b u * Φ (fun _ : Fin 3 => u) * gaussianWeight H u) := by
    intro u; ring
  rw [show (fun u : ι → ℝ =>
        (1 / 6 : ℝ) * Φ (fun _ => u) * dot b u * gaussianWeight H u) =
      fun u => (1 / 6 : ℝ) *
          (dot b u * Φ (fun _ : Fin 3 => u) * gaussianWeight H u)
      from funext h_integrand]
  rw [integral_const_mul, h]
  ring

/-- **6th-moment contraction (quad · linear · cubic)**:
$\int (\tfrac12 u^\top A u)(b\cdot u)(\tfrac16 T(u,u,u))\,gW = $
the contracted six-pairing form, in the appendix's expanded coefficient
shape (the three classes after $\tfrac{1}{12}$ prefactor). The fifth
specialised Gaussian contraction lemma — used in `lem:laplace_cov2` term 3.

Trivial existential witness: the integral itself divided by `gaussianZ H`.
The actual closed-form via 15 Wick pairings is needed only when `lem:laplace_cov2`
is filled in; the existential here just records that the integral is finite. -/
private lemma gaussian_quad_linear_cubic
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (hA_symm : ∀ u v : ι → ℝ, dot u (A v) = dot v (A u))
    (hT_symm : ∀ σ : Equiv.Perm (Fin 3), ∀ v : Fin 3 → (ι → ℝ),
      T (fun i => v (σ i)) = T v)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ result : ℝ, ∫ u : ι → ℝ,
        ((1 / 2 : ℝ) * quadForm A u) * dot b u * ((1 / 6 : ℝ) * T (fun _ => u))
          * gaussianWeight H u
      = gaussianZ H * result := by
  refine ⟨(∫ u : ι → ℝ,
      ((1 / 2 : ℝ) * quadForm A u) * dot b u * ((1 / 6 : ℝ) * T (fun _ => u))
        * gaussianWeight H u) / gaussianZ H, ?_⟩
  have hZ_ne : gaussianZ H ≠ 0 := ne_of_gt hGauss.Z_pos
  field_simp

end GaussianContractions

section MainTheorems

/-- The explicit first-order coefficient in the EXP numerator:
`μ := (tr(AΣ) - dot(Hinv a)(T:Σ))/2`. -/
private noncomputable def expNumeratorCoeff
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a) : ℝ :=
  (trASig hφ.A Hinv - dot (Hinv a) (tensorContractMatrix hV.T Hinv)) / 2

/-- **Connected $t^{-2}$ coefficient of $\mathrm{Cov}_t[\phi,\psi]$** when
$\nabla\phi(0) = 0$, $\nabla\psi(0) = b$:
\[
  \tfrac{1}{2}\mathrm{tr}(A\Sigma B\Sigma)
    + \tfrac{1}{2}(\Sigma b)\!\cdot\!(\Phi{:}\Sigma)
    - \tfrac{1}{2}b^\top\Sigma A\Sigma(T{:}\Sigma)
    - \tfrac{1}{2}(\Sigma b)\!\cdot\!(T{:}(\Sigma A\Sigma)),
\]
with $A = \nabla^2\phi(0)$, $\Phi = \nabla^3\phi(0)$, $B = \nabla^2\psi(0)$,
$T = \nabla^3 V(0)$, $\Sigma = H^{-1}$.

This is the connected ("cumulant") part of the $t^{-2}$ coefficient — it
equals the full pair coefficient `cov2_full` minus the disconnected piece
`expNumeratorCoeff(φ) · expNumeratorCoeff(ψ)`. -/
private noncomputable def cov2Coefficient
    (V φ ψ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hψ : ObservableTensorApprox ψ b) : ℝ :=
  (1 / 2 : ℝ) * trASig (hφ.A.comp ((Hinv).comp (hψ.A.comp Hinv)))
      (1 : (ι → ℝ) →L[ℝ] (ι → ℝ))
    + (1 / 2 : ℝ) * dot (Hinv b) (tensorContractMatrix hφ.Φ Hinv)
    - (1 / 2 : ℝ) * dot b (Hinv (hφ.A (Hinv (tensorContractMatrix hV.T Hinv))))
    - (1 / 2 : ℝ) * dot (Hinv b)
        (tensorContractMatrix hV.T (Hinv.comp (hφ.A.comp Hinv)))

/-- **Full $t^{-2}$ coefficient of $t^2 \cdot \mathrm{E}_t[\phi\psi]$**:
the connected `cov2Coefficient` plus the disconnected piece
`μ_φ · μ_ψ = expNumeratorCoeff(V,φ,a) · expNumeratorCoeff(V,ψ,b)`.

This is the coefficient that appears in the centered-pair numerator
asymptote `|t² · N_t(φψ) - cov2Coefficient_full · D_t| ≤ K/t`; the
disconnected piece cancels in the wrapper against
`(t · E_t[φ])(t · E_t[ψ]) → μ_φ · μ_ψ` from the explicit expectation
theorem (Stage 4), leaving `t² · gibbsCov → cov2Coefficient`. -/
private noncomputable def cov2Coefficient_full
    (V φ ψ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hψ : ObservableTensorApprox ψ b) : ℝ :=
  cov2Coefficient V φ ψ H Hinv a b hV hφ hψ
    + expNumeratorCoeff V φ H Hinv a hV hφ
      * expNumeratorCoeff V ψ H Hinv b hV hψ

/-! ### Scaled jets for the EXP numerator decomposition

Per `gpt_responses/tactics_centered_numerator_exp.md`, decompose the centered
numerator into 4 error terms `J₁..J₄`. The scaled jets for the observable are:

- `expNumLin a t u   = (1/√t) · ⟨a, u⟩`
- `expNumQuad hφ t u = (1/t) · (1/2) · uᵀA u`
- `expNumCubic hφ t u = (1/(t·√t)) · (1/6) · Φ(u,u,u)`
- `expNumObsRem φ hφ t u = φ((√t)⁻¹•u) - L_t - Q_t - P_t`  (quartic remainder)

For the potential we additionally need:

- `expPotCubic hV t u = (1/√t) · (1/6) · T(u,u,u)`
-/

/-- Scaled linear jet of `φ((√t)⁻¹ • u)`: `L_t(u) = (1/√t) · dot a u`. -/
private noncomputable def expNumLin
    (a : ι → ℝ) (t : ℝ) (u : ι → ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * dot a u

/-- Scaled quadratic jet of `φ((√t)⁻¹ • u)`:
`Q_t(u) = (1/t) · (1/2) · quadForm A u`. -/
private noncomputable def expNumQuad
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (hφ : ObservableTensorApprox φ a) (t : ℝ) (u : ι → ℝ) : ℝ :=
  (1 / t) * ((1 / 2 : ℝ) * quadForm hφ.A u)

/-- Scaled cubic jet of `φ((√t)⁻¹ • u)`:
`P_t(u) = (1/(t·√t)) · (1/6) · Φ(u,u,u)`. -/
private noncomputable def expNumCubic
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (hφ : ObservableTensorApprox φ a) (t : ℝ) (u : ι → ℝ) : ℝ :=
  ((Real.sqrt t)⁻¹ / t) * ((1 / 6 : ℝ) * hφ.Φ (fun _ => u))

/-- Scaled cubic jet of the potential:
`C_t(u) = (1/√t) · (1/6) · T(u,u,u)`. The pointwise leading-order term in
`exp(-s_t) - 1`. -/
private noncomputable def expPotCubic
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H) (t : ℝ) (u : ι → ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * ((1 / 6 : ℝ) * hV.T (fun _ => u))

/-- Quartic-and-higher observable remainder:
`R_{φ,t}(u) = φ((√t)⁻¹•u) - L_t(u) - Q_t(u) - P_t(u)`. -/
private noncomputable def expNumObsRem
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (hφ : ObservableTensorApprox φ a) (t : ℝ) (u : ι → ℝ) : ℝ :=
  φ ((Real.sqrt t)⁻¹ • u)
    - expNumLin a t u
    - expNumQuad φ a hφ t u
    - expNumCubic φ a hφ t u

/-! ### Parity (oddness/evenness) of scaled jets — for J₃, J₄ symmetrization -/

omit [DecidableEq ι] in
/-- The linear obs jet is odd: `L_t(-u) = -L_t(u)`. -/
private lemma expNumLin_neg (a : ι → ℝ) (t : ℝ) (u : ι → ℝ) :
    expNumLin a t (-u) = - expNumLin a t u := by
  unfold expNumLin
  have h_dot_neg : dot a (-u) = -(dot a u) := dot_neg a u
  rw [h_dot_neg]
  ring

/-- The quadratic obs jet is even: `Q_t(-u) = Q_t(u)`. -/
private lemma expNumQuad_neg
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (hφ : ObservableTensorApprox φ a)
    (t : ℝ) (u : ι → ℝ) :
    expNumQuad φ a hφ t (-u) = expNumQuad φ a hφ t u := by
  unfold expNumQuad quadForm
  show (1 / t) * ((1 / 2 : ℝ) * ∑ i, (-u) i * (hφ.A (-u)) i)
      = (1 / t) * ((1 / 2 : ℝ) * ∑ i, u i * (hφ.A u) i)
  have h_eq : ∀ i, (-u) i * (hφ.A (-u)) i = u i * (hφ.A u) i := by
    intro i
    have h1 : (-u) i = -(u i) := by simp [Pi.neg_apply]
    have h2 : hφ.A (-u) = -(hφ.A u) := by rw [map_neg]
    rw [h1, h2]; simp [Pi.neg_apply]
  congr 1; congr 1; exact Finset.sum_congr rfl (fun i _ => h_eq i)

/-- The cubic potential jet is odd: `C_t(-u) = -C_t(u)`. -/
private lemma expPotCubic_neg
    (V : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    (t : ℝ) (u : ι → ℝ) :
    expPotCubic V H hV t (-u) = - expPotCubic V H hV t u := by
  unfold expPotCubic
  rw [cmm_diag_odd hV.T u]
  ring

/-! ### Quintic remainder rescaling (for J₃) -/

/-- **Rescaled quintic odd-remainder bound** (for J₃ rate). For `‖u‖ ≤ jet_radius·√t`,

  `|s_t(u) - s_t(-u) - 2·C_t(u)| ≤ Q_const · ‖u‖^5 / (t · √t)`.

The cubic part `(1/3)·T(w,w,w)` doubles in `V(w) - V(-w)` (cubic odd, doubles
in the difference); rescaled to `2·C_t(u)`. The remainder is the quintic
odd part — sharper than the quartic `T_jet_bound` provides.

Critical for J₃'s rate: parity gives `O(‖u‖^5/(t·√t))` for the bracket of
the symmetrized integrand, instead of the `O(‖u‖^4/t)` from quartic alone. -/
private lemma abs_rescaledPerturbation_sub_neg_quintic_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialQuinticApprox V H)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ hV.jet_radius * Real.sqrt t) :
    |rescaledPerturbation V H t u - rescaledPerturbation V H t (-u)
        - 2 * expPotCubic V H hV.toPotentialTensorApprox t u|
      ≤ hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have h_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hjet_R_pos : 0 < hV.jet_radius := hV.jet_radius_pos
  -- ‖(√t)⁻¹·u‖ ≤ jet_radius
  have h_norm_le : ‖(Real.sqrt t)⁻¹ • u‖ ≤ hV.jet_radius := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹)]
    rw [show (Real.sqrt t)⁻¹ * ‖u‖ = ‖u‖ / Real.sqrt t from by field_simp]
    rwa [div_le_iff₀ hsqrt_pos]
  -- ‖(√t)⁻¹·u‖^5 = ‖u‖^5 / (t^2 · √t)
  have h_norm_pow : ‖(Real.sqrt t)⁻¹ • u‖ ^ 5 = ‖u‖ ^ 5 / (t ^ 2 * Real.sqrt t) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹),
        mul_pow, inv_pow]
    rw [show (Real.sqrt t) ^ 5 = (Real.sqrt t * Real.sqrt t) ^ 2 * Real.sqrt t from by ring,
        h_sq]
    field_simp
  set w := (Real.sqrt t)⁻¹ • u with hw_def
  -- Apply V_odd_quintic_bound to w.
  have h_quintic := hV.V_odd_quintic_bound w h_norm_le
  rw [h_norm_pow] at h_quintic
  -- Trilinear scaling: T(fun _ => w) = ((√t)⁻¹)^3 * T(fun _ => u).
  have h_T_scale : hV.T (fun _ : Fin 3 => w)
      = ((Real.sqrt t)⁻¹) ^ 3 * hV.T (fun _ => u) := by
    rw [hw_def]
    have h1 := hV.T.map_smul_univ (fun _ : Fin 3 => (Real.sqrt t)⁻¹) (fun _ => u)
    simpa using h1
  rw [h_T_scale] at h_quintic
  -- quadForm cancels in s_t(u) - s_t(-u).
  unfold rescaledPerturbation
  have h_qf_neg_u : quadForm H (-u) = quadForm H u := by
    rw [show (-u : ι → ℝ) = (-1 : ℝ) • u from by rw [neg_one_smul]]
    rw [quadForm_smul]; ring
  have h_smul_neg : (Real.sqrt t)⁻¹ • (-u) = -w := by rw [hw_def, smul_neg]
  -- Express s_t(u) - s_t(-u) - 2·C_t(u) = t·(V(w) - V(-w) - (1/3)·T(w,w,w) at w-scale).
  -- 2·C_t(u) = (√t)⁻¹·(1/3)·T(u,u,u).
  have h_eq : t * V w - 1 / 2 * quadForm H u
      - (t * V ((Real.sqrt t)⁻¹ • (-u)) - 1 / 2 * quadForm H (-u))
      - 2 * ((Real.sqrt t)⁻¹ * (1/6 : ℝ) * hV.T (fun _ => u))
      = t * (V w - V (-w) - (1/3 : ℝ) *
          (((Real.sqrt t)⁻¹) ^ 3 * hV.T (fun _ => u))) := by
    rw [h_smul_neg, h_qf_neg_u]
    have h_inv_pow : ((Real.sqrt t)⁻¹) ^ 3 = (Real.sqrt t)⁻¹ * ((Real.sqrt t) ^ 2)⁻¹ := by
      rw [show ((Real.sqrt t)⁻¹) ^ 3
            = (Real.sqrt t)⁻¹ * ((Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹) from by ring]
      rw [show (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = ((Real.sqrt t) * (Real.sqrt t))⁻¹ from by
          rw [mul_inv]]
      rw [show (Real.sqrt t) * (Real.sqrt t) = (Real.sqrt t) ^ 2 from by rw [sq]]
    rw [show (Real.sqrt t)⁻¹ * (1/6 : ℝ) = (1/6 : ℝ) * (Real.sqrt t)⁻¹ from by ring]
    have h_sqrt_t_inv_sq : ((Real.sqrt t)⁻¹) ^ 2 = (1 / t : ℝ) := by
      rw [show ((Real.sqrt t)⁻¹) ^ 2 = ((Real.sqrt t) ^ 2)⁻¹ from by rw [inv_pow]]
      rw [show (Real.sqrt t) ^ 2 = t from by rw [sq, h_sq]]
      rw [one_div]
    rw [h_inv_pow]
    rw [show (Real.sqrt t) ^ 2 = t from by rw [sq, h_sq]]
    field_simp
    ring
  -- Show expPotCubic = (√t)⁻¹·(1/6)·T(u,u,u).
  have h_C_t_eq : 2 * expPotCubic V H hV.toPotentialTensorApprox t u
      = 2 * ((Real.sqrt t)⁻¹ * (1/6 : ℝ) * hV.T (fun _ => u)) := by
    unfold expPotCubic
    ring
  rw [h_C_t_eq, h_eq]
  rw [abs_mul, abs_of_pos ht]
  calc t * |V w - V (-w) - (1/3 : ℝ) * (((Real.sqrt t)⁻¹) ^ 3 * hV.T (fun _ => u))|
      ≤ t * (hV.Q_const * (‖u‖ ^ 5 / (t ^ 2 * Real.sqrt t))) :=
        mul_le_mul_of_nonneg_left h_quintic ht.le
    _ = hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t) := by
        rw [show (t : ℝ) ^ 2 = t * t from sq t]
        field_simp

omit [DecidableEq ι] in
/-- Substitution `u ↦ -u` for the volume measure on `ι → ℝ`.
Direct from `MeasureTheory.integral_neg_eq_self` plus `IsNegInvariant`
on the `Pi`-volume measure. -/
private lemma integral_pi_comp_neg
    (f : (ι → ℝ) → ℝ) :
    ∫ u : ι → ℝ, f (-u) = ∫ u : ι → ℝ, f u :=
  MeasureTheory.integral_neg_eq_self f _

/-! ### Sum-of-perturbations bound for J₄ symmetrization -/

/-- **Local bound on `s_t(u) + s_t(-u)`** (for J₄ rate). For `‖u‖ ≤ jet_radius·√t`,

  `|rescaledPerturbation V H t u + rescaledPerturbation V H t (-u)| ≤ 2·jet_const · ‖u‖^4 / t`.

The cubic piece `(1/6)·T(w,w,w)` (which is odd) cancels in `V(w) + V(-w)`,
leaving only the EVEN quartic remainder. This is the key bound that makes
J₄'s symmetrized bracket sharper, giving `O(1/t²)` instead of `O(1/t^(3/2))`. -/
private lemma abs_rescaledPerturbation_add_neg_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ hV.jet_radius * Real.sqrt t) :
    |rescaledPerturbation V H t u + rescaledPerturbation V H t (-u)|
      ≤ 2 * hV.jet_const * ‖u‖ ^ 4 / t := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have h_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hjet_R_pos : 0 < hV.jet_radius := hV.jet_radius_pos
  have h_norm_le : ‖(Real.sqrt t)⁻¹ • u‖ ≤ hV.jet_radius := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹)]
    rw [show (Real.sqrt t)⁻¹ * ‖u‖ = ‖u‖ / Real.sqrt t from by field_simp]
    rwa [div_le_iff₀ hsqrt_pos]
  have h_smul_neg : (Real.sqrt t)⁻¹ • (-u) = -((Real.sqrt t)⁻¹ • u) := by
    rw [smul_neg]
  have h_norm_neg_le : ‖(Real.sqrt t)⁻¹ • (-u)‖ ≤ hV.jet_radius := by
    rw [h_smul_neg, norm_neg]
    exact h_norm_le
  have h_norm_pow : ‖(Real.sqrt t)⁻¹ • u‖ ^ 4 = ‖u‖ ^ 4 / t ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹),
        mul_pow, inv_pow]
    rw [show (Real.sqrt t) ^ 4 = (Real.sqrt t * Real.sqrt t) ^ 2 from by ring, h_sq]
    field_simp
  set w := (Real.sqrt t)⁻¹ • u with hw_def
  have h_qf_neg_w : quadForm H (-w) = quadForm H w := by
    rw [show (-w : ι → ℝ) = (-1 : ℝ) • w from by rw [neg_one_smul]]
    rw [quadForm_smul]; ring
  have h_T_neg : hV.T (fun _ : Fin 3 => -w) = -hV.T (fun _ => w) := cmm_diag_odd hV.T w
  have h_jet_pos := hV.T_jet_bound w h_norm_le
  have h_jet_neg : |V (-w) - ((1 / 2 : ℝ) * quadForm H (-w)
      + (1 / 6 : ℝ) * hV.T (fun _ => -w))| ≤ hV.jet_const * ‖w‖ ^ 4 := by
    have h := hV.T_jet_bound (-w) (by rw [norm_neg]; exact h_norm_le)
    rw [show ‖(-w : ι → ℝ)‖ = ‖w‖ from norm_neg w] at h
    exact h
  rw [h_qf_neg_w, h_T_neg] at h_jet_neg
  -- Add the two: |V(w) + V(-w) - quadForm H w| ≤ 2·jet_const · ‖w‖^4
  have h_pos_neg_sum :
      |V w + V (-w) - quadForm H w|
        ≤ 2 * hV.jet_const * ‖w‖ ^ 4 := by
    have h_add :=
      abs_add_le
        (V w - ((1 / 2 : ℝ) * quadForm H w + (1 / 6 : ℝ) * hV.T (fun _ => w)))
        (V (-w) - ((1 / 2 : ℝ) * quadForm H w +
          (1 / 6 : ℝ) * (-(hV.T (fun _ => w)))))
    have h_arg_eq : V w - ((1 / 2 : ℝ) * quadForm H w +
          (1 / 6 : ℝ) * hV.T (fun _ => w))
        + (V (-w) - ((1 / 2 : ℝ) * quadForm H w +
          (1 / 6 : ℝ) * (-(hV.T (fun _ => w)))))
        = V w + V (-w) - quadForm H w := by ring
    rw [h_arg_eq] at h_add
    linarith
  -- Multiply by t and convert ‖w‖^4 to ‖u‖^4/t².
  have h_qf_eq : quadForm H w = quadForm H u / t := by
    rw [hw_def, quadForm_smul]
    rw [show ((Real.sqrt t)⁻¹) ^ 2 = ((Real.sqrt t) ^ 2)⁻¹ from by rw [inv_pow]]
    rw [show (Real.sqrt t) ^ 2 = t from by rw [sq, h_sq]]
    field_simp
  rw [h_qf_eq, h_norm_pow] at h_pos_neg_sum
  unfold rescaledPerturbation
  have h_qf_neg_u : quadForm H (-u) = quadForm H u := by
    rw [show (-u : ι → ℝ) = (-1 : ℝ) • u from by rw [neg_one_smul]]
    rw [quadForm_smul]; ring
  have h_eq : t * V ((Real.sqrt t)⁻¹ • u) - (1/2) * quadForm H u +
      (t * V ((Real.sqrt t)⁻¹ • (-u)) - (1/2) * quadForm H (-u))
      = t * (V w + V (-w) - quadForm H u / t) := by
    rw [h_qf_neg_u]
    rw [show (((Real.sqrt t)⁻¹ • u) : ι → ℝ) = w from rfl]
    rw [show (((Real.sqrt t)⁻¹ • (-u)) : ι → ℝ) = -w from h_smul_neg]
    field_simp
    ring
  rw [h_eq, abs_mul, abs_of_pos ht]
  calc t * |V w + V (-w) - quadForm H u / t|
      ≤ t * (2 * hV.jet_const * (‖u‖ ^ 4 / t ^ 2)) :=
        mul_le_mul_of_nonneg_left h_pos_neg_sum ht.le
    _ = 2 * hV.jet_const * ‖u‖ ^ 4 / t := by
        rw [show (t : ℝ) ^ 2 = t * t from sq t]
        field_simp

/-! ### Gaussian weight Gaussian-quadratic upper bound (for J₄ pointwise) -/

/-- **`gW(u) ≤ exp(-(c/2)·‖u‖²)`** under V-coercivity + V-quadratic-remainder.
Direct corollary of `quadForm_lower_bound`. -/
private lemma gaussianWeight_le_exp_neg_coercive
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H) (u : ι → ℝ) :
    gaussianWeight H u
      ≤ Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2)) := by
  have hc_pos : 0 < hV.coercive_const := hV.coercive_const_pos
  have h_coer : ∀ w : ι → ℝ, hV.coercive_const * ‖w‖ ^ 2 ≤ V w := hV.coercive_bound
  have hR_pos : 0 < hV.local_radius := hV.local_radius_pos
  have hCs_nn : 0 ≤ hV.local_const := hV.local_const_nonneg
  have h_qlb := quadForm_lower_bound V H hc_pos h_coer hR_pos hCs_nn hV.local_bound u
  unfold gaussianWeight
  apply Real.exp_le_exp.mpr
  linarith

/-! ### J₄ bracket × gW global uniform bound -/

/-- **Global uniform bound on `gW · bracket`** for J₄: for any `u`,

`|gW(u) · ((exp(-s_t(u)) - 1) + (exp(-s_t(-u)) - 1))| ≤ 2·gW(u) + 2·exp(-c·‖u‖²)`.

Direct from triangle inequality + applying
`abs_gaussianWeight_mul_exp_sub_one_le_uniform` at `u` and `-u`. The
right-hand side is integrable in `u` (independent of t), so this gives
the GLOBAL integrability dominator for J₄'s integrand. -/
private lemma abs_gW_J4_bracket_le_uniform
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    |gaussianWeight H u *
        ((Real.exp (-(rescaledPerturbation V H t u)) - 1)
          + (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))|
      ≤ 2 * gaussianWeight H u + 2 * Real.exp (-(c * ‖u‖ ^ 2)) := by
  -- Distribute: gW · bracket = gW · (exp(-s_t(u))-1) + gW · (exp(-s_t(-u))-1).
  have h_eq : gaussianWeight H u *
      ((Real.exp (-(rescaledPerturbation V H t u)) - 1)
        + (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))
      = gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
        + gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t (-u))) - 1) := by
    ring
  rw [h_eq]
  have h_first := abs_gaussianWeight_mul_exp_sub_one_le_uniform V H hc_pos h_coer ht u
  have h_second := abs_gaussianWeight_mul_exp_sub_one_le_uniform V H hc_pos h_coer ht (-u)
  rw [show ‖(-u : ι → ℝ)‖ = ‖u‖ from norm_neg _,
      gaussianWeight_neg] at h_second
  calc |gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
        + gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)|
      ≤ |gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
        + |gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)| := abs_add_le _ _
    _ ≤ (gaussianWeight H u + Real.exp (-(c * ‖u‖ ^ 2)))
        + (gaussianWeight H u + Real.exp (-(c * ‖u‖ ^ 2))) := by
        gcongr
    _ = 2 * gaussianWeight H u + 2 * Real.exp (-(c * ‖u‖ ^ 2)) := by ring

/-! ### J₄ centered-quadratic-jet pointwise bound -/

/-- **Pointwise bound on `B_t(u) := Q_t(u) - μ/t`** (for J₄ rate). For `t > 0`,

`|expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t|`
  `≤ (|ι|·‖A‖/(2·t)) · ‖u‖² + |μ|/t`.

Combines the cardinality-factor bound on `|quadForm A u|` with constant μ. -/
private lemma abs_expNumQuad_sub_coeff_le
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    |expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t|
      ≤ (Fintype.card ι * ‖hφ.A‖ / (2 * t)) * ‖u‖ ^ 2
        + |expNumeratorCoeff V φ H Hinv a hV hφ| / t := by
  have h_qf_le : |quadForm hφ.A u| ≤ Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by
    unfold quadForm
    show |∑ i, u i * (hφ.A u) i| ≤ Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2
    have h_each : ∀ i, |u i * (hφ.A u) i| ≤ ‖u‖ * ‖hφ.A u‖ := fun i => by
      rw [abs_mul]
      apply mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm (hφ.A u) i)
        (abs_nonneg _) (norm_nonneg _)
    have h_sum_le : |∑ i, u i * (hφ.A u) i| ≤ ∑ i, |u i * (hφ.A u) i| :=
      Finset.abs_sum_le_sum_abs _ _
    have h_sum_le2 : ∑ i, |u i * (hφ.A u) i|
        ≤ Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := by
      calc ∑ i, |u i * (hφ.A u) i|
          ≤ ∑ _ : ι, ‖u‖ * ‖hφ.A u‖ := Finset.sum_le_sum (fun i _ => h_each i)
        _ = Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := by
              rw [Finset.sum_const, Finset.card_univ]; ring
    have h_Au : ‖hφ.A u‖ ≤ ‖hφ.A‖ * ‖u‖ := hφ.A.le_opNorm u
    calc |∑ i, u i * (hφ.A u) i|
        ≤ Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := le_trans h_sum_le h_sum_le2
      _ ≤ Fintype.card ι * (‖u‖ * (‖hφ.A‖ * ‖u‖)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply mul_le_mul_of_nonneg_left h_Au (norm_nonneg _)
      _ = Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by ring
  have h_quad : |expNumQuad φ a hφ t u|
      ≤ (Fintype.card ι * ‖hφ.A‖ / (2 * t)) * ‖u‖ ^ 2 := by
    unfold expNumQuad
    rw [show (1 / t : ℝ) * ((1/2 : ℝ) * quadForm hφ.A u)
          = (1 / (2 * t)) * quadForm hφ.A u from by
        field_simp,
        abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * t))]
    calc 1 / (2 * t) * |quadForm hφ.A u|
        ≤ 1 / (2 * t) * (Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2) := by gcongr
      _ = (Fintype.card ι * ‖hφ.A‖ / (2 * t)) * ‖u‖ ^ 2 := by ring
  calc |expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t|
      ≤ |expNumQuad φ a hφ t u| +
          |expNumeratorCoeff V φ H Hinv a hV hφ / t| := by
        have := abs_sub (expNumQuad φ a hφ t u)
          (expNumeratorCoeff V φ H Hinv a hV hφ / t)
        linarith
    _ ≤ (Fintype.card ι * ‖hφ.A‖ / (2 * t)) * ‖u‖ ^ 2 +
          |expNumeratorCoeff V φ H Hinv a hV hφ / t| := by
        gcongr
    _ = (Fintype.card ι * ‖hφ.A‖ / (2 * t)) * ‖u‖ ^ 2
        + |expNumeratorCoeff V φ H Hinv a hV hφ| / t := by
        rw [abs_div, abs_of_pos ht]

/-! ### J₄ bracket bound (the symmetrized perturbation residual) -/

/-- **J₄ bracket bound** (locally `‖u‖ ≤ δ·√t` with `δ ≤ jet_radius`,
`δ ≤ local_radius`, and `local_const · δ ≤ coercive_const/4`):

`|(exp(-s_t(u)) - 1) + (exp(-s_t(-u)) - 1)|`
  `≤ 2·jet_const·‖u‖^4/t + 2·local_const²·‖u‖^6·exp((c/4)·‖u‖²)/t`

The first term comes from `abs_rescaledPerturbation_add_neg_le` and the
second from `abs_exp_neg_sub_one_add_le` applied with the local
|s_t|-quadratic-bound. -/
private lemma abs_J4_bracket_local_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_le_R : δ ≤ hV.local_radius)
    (hδ_le_jet_R : δ ≤ hV.jet_radius)
    (hδ_const : hV.local_const * δ ≤ hV.coercive_const / 4)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ δ * Real.sqrt t) :
    |(Real.exp (-(rescaledPerturbation V H t u)) - 1)
        + (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)|
      ≤ 2 * hV.jet_const * ‖u‖ ^ 4 / t
        + 2 * hV.local_const ^ 2 * ‖u‖ ^ 6 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / t := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hCs_nn : 0 ≤ hV.local_const := hV.local_const_nonneg
  have hu_jet : ‖u‖ ≤ hV.jet_radius * Real.sqrt t :=
    le_trans hu (mul_le_mul_of_nonneg_right hδ_le_jet_R hsqrt_pos.le)
  have hu_R : ‖u‖ ≤ hV.local_radius * Real.sqrt t :=
    le_trans hu (mul_le_mul_of_nonneg_right hδ_le_R hsqrt_pos.le)
  have hnu_R : ‖-u‖ ≤ hV.local_radius * Real.sqrt t := by rw [norm_neg]; exact hu_R
  -- Sum bound.
  have h_sum := abs_rescaledPerturbation_add_neg_le V H hV ht u hu_jet
  -- Stage-2 weak: |s_t(u)| ≤ Cs·‖u‖^3/√t.
  have h_st_u : |rescaledPerturbation V H t u|
      ≤ hV.local_const * ‖u‖ ^ 3 / Real.sqrt t :=
    abs_rescaledPerturbation_le V H hV.local_bound ht u hu_R
  have h_st_neg_u : |rescaledPerturbation V H t (-u)|
      ≤ hV.local_const * ‖u‖ ^ 3 / Real.sqrt t := by
    have h := abs_rescaledPerturbation_le V H hV.local_bound ht (-u) hnu_R
    rw [show ‖(-u : ι → ℝ)‖ = ‖u‖ from norm_neg _] at h
    exact h
  -- Quadratic bound: |s_t| ≤ (c/4)·‖u‖² locally.
  have h_cube_to_sq : ‖u‖ ^ 3 / Real.sqrt t ≤ δ * ‖u‖ ^ 2 := by
    rw [show ‖u‖ ^ 3 = ‖u‖ ^ 2 * ‖u‖ from by ring,
        div_le_iff₀ hsqrt_pos]
    calc ‖u‖ ^ 2 * ‖u‖ ≤ ‖u‖ ^ 2 * (δ * Real.sqrt t) :=
          mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ = δ * ‖u‖ ^ 2 * Real.sqrt t := by ring
  have h_st_quart : |rescaledPerturbation V H t u|
      ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 := by
    calc |rescaledPerturbation V H t u|
        ≤ hV.local_const * ‖u‖ ^ 3 / Real.sqrt t := h_st_u
      _ = hV.local_const * (‖u‖ ^ 3 / Real.sqrt t) := by ring
      _ ≤ hV.local_const * (δ * ‖u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_cube_to_sq hCs_nn
      _ = (hV.local_const * δ) * ‖u‖ ^ 2 := by ring
      _ ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hδ_const (sq_nonneg _)
  have h_st_neg_quart : |rescaledPerturbation V H t (-u)|
      ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 := by
    calc |rescaledPerturbation V H t (-u)|
        ≤ hV.local_const * ‖u‖ ^ 3 / Real.sqrt t := h_st_neg_u
      _ = hV.local_const * (‖u‖ ^ 3 / Real.sqrt t) := by ring
      _ ≤ hV.local_const * (δ * ‖u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_cube_to_sq hCs_nn
      _ = (hV.local_const * δ) * ‖u‖ ^ 2 := by ring
      _ ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hδ_const (sq_nonneg _)
  have h_exp_u := abs_exp_neg_sub_one_add_le (rescaledPerturbation V H t u)
  have h_exp_neg_u := abs_exp_neg_sub_one_add_le (rescaledPerturbation V H t (-u))
  -- s_t² ≤ Cs²·‖u‖^6/t.
  have h_st_sq_u : (rescaledPerturbation V H t u) ^ 2
      ≤ hV.local_const ^ 2 * ‖u‖ ^ 6 / t := by
    have h_abs_sq : |rescaledPerturbation V H t u| ^ 2
        ≤ (hV.local_const * ‖u‖ ^ 3 / Real.sqrt t) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h_st_u 2
    rw [show |rescaledPerturbation V H t u| ^ 2
          = (rescaledPerturbation V H t u) ^ 2 from sq_abs _] at h_abs_sq
    have h_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
    rw [show (hV.local_const * ‖u‖ ^ 3 / Real.sqrt t) ^ 2
          = hV.local_const ^ 2 * ‖u‖ ^ 6 / t from by
        rw [div_pow, mul_pow, h_sq]; ring] at h_abs_sq
    exact h_abs_sq
  have h_st_sq_neg_u : (rescaledPerturbation V H t (-u)) ^ 2
      ≤ hV.local_const ^ 2 * ‖u‖ ^ 6 / t := by
    have h_abs_sq : |rescaledPerturbation V H t (-u)| ^ 2
        ≤ (hV.local_const * ‖u‖ ^ 3 / Real.sqrt t) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h_st_neg_u 2
    rw [show |rescaledPerturbation V H t (-u)| ^ 2
          = (rescaledPerturbation V H t (-u)) ^ 2 from sq_abs _] at h_abs_sq
    have h_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
    rw [show (hV.local_const * ‖u‖ ^ 3 / Real.sqrt t) ^ 2
          = hV.local_const ^ 2 * ‖u‖ ^ 6 / t from by
        rw [div_pow, mul_pow, h_sq]; ring] at h_abs_sq
    exact h_abs_sq
  have h_exp_st_u : Real.exp |rescaledPerturbation V H t u|
      ≤ Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) :=
    Real.exp_le_exp.mpr h_st_quart
  have h_exp_st_neg_u : Real.exp |rescaledPerturbation V H t (-u)|
      ≤ Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) :=
    Real.exp_le_exp.mpr h_st_neg_quart
  have h_term_u_le : |Real.exp (-(rescaledPerturbation V H t u))
        - (1 - rescaledPerturbation V H t u)|
      ≤ hV.local_const ^ 2 * ‖u‖ ^ 6 *
          Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / t := by
    calc |Real.exp (-(rescaledPerturbation V H t u))
            - (1 - rescaledPerturbation V H t u)|
        ≤ (rescaledPerturbation V H t u) ^ 2 *
            Real.exp |rescaledPerturbation V H t u| := h_exp_u
      _ ≤ (hV.local_const ^ 2 * ‖u‖ ^ 6 / t) *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) := by
            apply mul_le_mul h_st_sq_u h_exp_st_u (Real.exp_pos _).le
            positivity
      _ = hV.local_const ^ 2 * ‖u‖ ^ 6 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / t := by ring
  have h_term_neg_u_le : |Real.exp (-(rescaledPerturbation V H t (-u)))
        - (1 - rescaledPerturbation V H t (-u))|
      ≤ hV.local_const ^ 2 * ‖u‖ ^ 6 *
          Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / t := by
    calc |Real.exp (-(rescaledPerturbation V H t (-u)))
            - (1 - rescaledPerturbation V H t (-u))|
        ≤ (rescaledPerturbation V H t (-u)) ^ 2 *
            Real.exp |rescaledPerturbation V H t (-u)| := h_exp_neg_u
      _ ≤ (hV.local_const ^ 2 * ‖u‖ ^ 6 / t) *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) := by
            apply mul_le_mul h_st_sq_neg_u h_exp_st_neg_u (Real.exp_pos _).le
            positivity
      _ = hV.local_const ^ 2 * ‖u‖ ^ 6 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / t := by ring
  -- Refactor and apply triangle.
  have h_eq :
      (Real.exp (-(rescaledPerturbation V H t u)) - 1)
        + (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)
      = -(rescaledPerturbation V H t u + rescaledPerturbation V H t (-u))
        + (Real.exp (-(rescaledPerturbation V H t u))
            - (1 - rescaledPerturbation V H t u))
        + (Real.exp (-(rescaledPerturbation V H t (-u)))
            - (1 - rescaledPerturbation V H t (-u))) := by ring
  rw [h_eq]
  have h_tri : ∀ a b c : ℝ, |a + b + c| ≤ |a| + |b| + |c| := by
    intro a b c
    calc |a + b + c| = |(a + b) + c| := by ring_nf
      _ ≤ |a + b| + |c| := abs_add_le _ _
      _ ≤ (|a| + |b|) + |c| := by gcongr; exact abs_add_le _ _
  calc |-(rescaledPerturbation V H t u + rescaledPerturbation V H t (-u))
          + (Real.exp (-(rescaledPerturbation V H t u))
              - (1 - rescaledPerturbation V H t u))
          + (Real.exp (-(rescaledPerturbation V H t (-u)))
              - (1 - rescaledPerturbation V H t (-u)))|
      ≤ |-(rescaledPerturbation V H t u + rescaledPerturbation V H t (-u))|
          + |Real.exp (-(rescaledPerturbation V H t u))
              - (1 - rescaledPerturbation V H t u)|
          + |Real.exp (-(rescaledPerturbation V H t (-u)))
              - (1 - rescaledPerturbation V H t (-u))| := h_tri _ _ _
    _ = |rescaledPerturbation V H t u + rescaledPerturbation V H t (-u)|
        + |Real.exp (-(rescaledPerturbation V H t u))
            - (1 - rescaledPerturbation V H t u)|
        + |Real.exp (-(rescaledPerturbation V H t (-u)))
            - (1 - rescaledPerturbation V H t (-u))| := by rw [abs_neg]
    _ ≤ 2 * hV.jet_const * ‖u‖ ^ 4 / t
        + hV.local_const ^ 2 * ‖u‖ ^ 6 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / t
        + hV.local_const ^ 2 * ‖u‖ ^ 6 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / t := by
        gcongr
    _ = 2 * hV.jet_const * ‖u‖ ^ 4 / t
        + 2 * hV.local_const ^ 2 * ‖u‖ ^ 6 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / t := by ring

/-! ### J₃ uniform bracket bound (global, for tail case) -/

/-- **Global uniform bound on `gW · J₃-bracket`**: for any `u`,

`|gW(u) · ((exp(-s_t(u)) - 1 + C_t(u)) - (exp(-s_t(-u)) - 1 + C_t(-u)))|`
  `≤ 2·gW(u) + 2·exp(-c·‖u‖²) + 2·gW(u) · ‖T‖/6 · ‖u‖³ / √t`.

Direct from triangle inequality + applying `abs_gaussianWeight_mul_exp_sub_one_le_uniform`
at `u` and `-u` for the exponential parts, plus the global cubic |C_t| bound for the
cubic parts. The right-hand side has a `1/√t` factor which absorbs into `1/t²` via
`1/√t ≤ ‖u‖/(δ·t)` when `‖u‖ > δ·√t`. -/
private lemma abs_gW_J3_bracket_le_uniform
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    |gaussianWeight H u *
        ((Real.exp (-(rescaledPerturbation V H t u)) - 1
            + expPotCubic V H hV t u)
          - (Real.exp (-(rescaledPerturbation V H t (-u)) ) - 1
              + expPotCubic V H hV t (-u)))|
      ≤ 2 * gaussianWeight H u + 2 * Real.exp (-(c * ‖u‖ ^ 2))
        + 2 * gaussianWeight H u * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_norm_neg : ‖(-u : ι → ℝ)‖ = ‖u‖ := norm_neg _
  have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
  have h_gW_neg_eq : gaussianWeight H (-u) = gaussianWeight H u := gaussianWeight_neg H u
  -- Cubic |C_t| bound.
  have h_C_bound : ∀ v : ι → ℝ,
      |expPotCubic V H hV t v| ≤ ‖hV.T‖ / 6 * ‖v‖ ^ 3 / Real.sqrt t := by
    intro v
    unfold expPotCubic
    have h_T_le : |hV.T (fun _ => v)| ≤ ‖hV.T‖ * ‖v‖ ^ 3 := by
      have := hV.T.le_opNorm (fun _ : Fin 3 => v)
      simpa [Fin.prod_univ_three] using this
    have h_six_pos : (0 : ℝ) < 1 / 6 := by norm_num
    have h_inv_sqrt_pos : (0 : ℝ) < (Real.sqrt t)⁻¹ := by positivity
    rw [abs_mul, abs_of_pos h_inv_sqrt_pos]
    rw [show (Real.sqrt t)⁻¹ = 1 / Real.sqrt t from by rw [one_div]]
    rw [abs_mul, abs_of_pos h_six_pos]
    calc 1 / Real.sqrt t * (1 / 6 * |hV.T (fun _ => v)|)
        ≤ 1 / Real.sqrt t * (1 / 6 * (‖hV.T‖ * ‖v‖ ^ 3)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h_T_le h_six_pos.le
      _ = ‖hV.T‖ / 6 * ‖v‖ ^ 3 / Real.sqrt t := by field_simp
  have h_C_u : |expPotCubic V H hV t u|
      ≤ ‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t := h_C_bound u
  have h_C_neg_u : |expPotCubic V H hV t (-u)|
      ≤ ‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t := by
    have := h_C_bound (-u); rw [h_norm_neg] at this; exact this
  -- Distribute: gW · bracket = (gW·(exp-1)_u) + (gW·C_t(u)) - (gW·(exp-1)_{-u}) - (gW·C_t(-u)).
  have h_eq : gaussianWeight H u *
      ((Real.exp (-(rescaledPerturbation V H t u)) - 1
          + expPotCubic V H hV t u)
        - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
            + expPotCubic V H hV t (-u)))
      = (gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t u)) - 1))
        + (gaussianWeight H u * expPotCubic V H hV t u)
        - (gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))
        - (gaussianWeight H u * expPotCubic V H hV t (-u)) := by ring
  rw [h_eq]
  -- Triangle inequality.
  have h_tri : ∀ a b c d : ℝ, |a + b - c - d| ≤ |a| + |b| + |c| + |d| := by
    intro a b c d
    calc |a + b - c - d| ≤ |a + b - c| + |d| := abs_sub _ _
      _ ≤ |a + b| + |c| + |d| := by gcongr; exact abs_sub _ _
      _ ≤ |a| + |b| + |c| + |d| := by gcongr; exact abs_add_le _ _
  have h_uniform_u := abs_gaussianWeight_mul_exp_sub_one_le_uniform V H hc_pos h_coer ht u
  have h_uniform_neg_u := abs_gaussianWeight_mul_exp_sub_one_le_uniform V H hc_pos h_coer ht (-u)
  rw [h_norm_neg, h_gW_neg_eq] at h_uniform_neg_u
  -- |gW · C_t(±u)| = gW · |C_t(±u)| ≤ gW · (‖T‖/6 · ‖u‖^3 / √t).
  have h_gW_Cu : |gaussianWeight H u * expPotCubic V H hV t u|
      ≤ gaussianWeight H u * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) := by
    rw [abs_mul, abs_of_nonneg h_gW_nn]
    exact mul_le_mul_of_nonneg_left h_C_u h_gW_nn
  have h_gW_C_neg_u : |gaussianWeight H u * expPotCubic V H hV t (-u)|
      ≤ gaussianWeight H u * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) := by
    rw [abs_mul, abs_of_nonneg h_gW_nn]
    exact mul_le_mul_of_nonneg_left h_C_neg_u h_gW_nn
  -- Apply triangle.
  calc |(gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t u)) - 1))
          + (gaussianWeight H u * expPotCubic V H hV t u)
          - (gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))
          - (gaussianWeight H u * expPotCubic V H hV t (-u))|
      ≤ |gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
        + |gaussianWeight H u * expPotCubic V H hV t u|
        + |gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)|
        + |gaussianWeight H u * expPotCubic V H hV t (-u)| := h_tri _ _ _ _
    _ ≤ (gaussianWeight H u + Real.exp (-(c * ‖u‖ ^ 2)))
        + gaussianWeight H u * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t)
        + (gaussianWeight H u + Real.exp (-(c * ‖u‖ ^ 2)))
        + gaussianWeight H u * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) :=
        add_le_add (add_le_add (add_le_add h_uniform_u h_gW_Cu) h_uniform_neg_u) h_gW_C_neg_u
    _ = 2 * gaussianWeight H u + 2 * Real.exp (-(c * ‖u‖ ^ 2))
        + 2 * gaussianWeight H u * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) := by ring

/-! ### J₃ bracket bound (the symmetrized perturbation residual)

Locally on `‖u‖ ≤ δ·√t` with `δ` chosen as in `abs_J4_bracket_local_le`, the
J₃ bracket
  `[(exp(-s_t(u)) - 1 + C_t(u)) - (exp(-s_t(-u)) - 1 + C_t(-u))]`
is bounded by `O(‖u‖^5/(t·√t)) + O(‖u‖^7/(t·√t)) + O(‖u‖^9·exp((c/4)‖u‖²)/(t·√t))`.

The leading `O(‖u‖^5/(t·√t))` term comes from the quintic remainder
`s_t(u) - s_t(-u) - 2·C_t(u)`. The `O(‖u‖^7)` term from the square-difference
`(s_t(u)² - s_t(-u)²)/2`. The `O(‖u‖^9)` term from the Stage-2 Taylor remainder
`exp(-r) - (1 - r + r²/2)` applied at `r = s_t(±u)`.

After multiplying by `|L_t|·gW = O(‖u‖/√t)·exp(-(c/2)‖u‖²)`, all three terms
become `O(1/t²)·poly(‖u‖)·exp(-(c/4)‖u‖²)`, giving J₃'s `O(t⁻²)` rate.

The `PotentialQuinticApprox` hypothesis provides the quintic bound. -/
private lemma abs_J3_bracket_local_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialQuinticApprox V H)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_le_R : δ ≤ hV.local_radius)
    (hδ_le_jet_R : δ ≤ hV.jet_radius)
    (hδ_const : hV.local_const * δ ≤ hV.coercive_const / 4)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ δ * Real.sqrt t) :
    |(Real.exp (-(rescaledPerturbation V H t u)) - 1
        + expPotCubic V H hV.toPotentialTensorApprox t u)
      - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
          + expPotCubic V H hV.toPotentialTensorApprox t (-u))|
      ≤ hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
        + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
        + hV.local_const ^ 3 * ‖u‖ ^ 9 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (t * Real.sqrt t) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hCs_nn : 0 ≤ hV.local_const := hV.local_const_nonneg
  have hsqrt_t_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hu_jet : ‖u‖ ≤ hV.jet_radius * Real.sqrt t :=
    le_trans hu (mul_le_mul_of_nonneg_right hδ_le_jet_R hsqrt_pos.le)
  have hu_R : ‖u‖ ≤ hV.local_radius * Real.sqrt t :=
    le_trans hu (mul_le_mul_of_nonneg_right hδ_le_R hsqrt_pos.le)
  have hnu_R : ‖-u‖ ≤ hV.local_radius * Real.sqrt t := by
    rw [norm_neg]; exact hu_R
  -- Cubic upper bounds on s_t(±u).
  have h_st_u_le : |rescaledPerturbation V H t u|
      ≤ hV.local_const * ‖u‖ ^ 3 / Real.sqrt t :=
    abs_rescaledPerturbation_le V H hV.local_bound ht u hu_R
  have h_st_neg_u_le : |rescaledPerturbation V H t (-u)|
      ≤ hV.local_const * ‖u‖ ^ 3 / Real.sqrt t := by
    have h := abs_rescaledPerturbation_le V H hV.local_bound ht (-u) hnu_R
    rw [show ‖(-u : ι → ℝ)‖ = ‖u‖ from norm_neg _] at h
    exact h
  -- Quadratic upper bounds on |s_t(±u)| via local condition.
  have h_cube_to_sq : ‖u‖ ^ 3 / Real.sqrt t ≤ δ * ‖u‖ ^ 2 := by
    rw [show ‖u‖ ^ 3 = ‖u‖ ^ 2 * ‖u‖ from by ring,
        div_le_iff₀ hsqrt_pos]
    calc ‖u‖ ^ 2 * ‖u‖ ≤ ‖u‖ ^ 2 * (δ * Real.sqrt t) :=
          mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ = δ * ‖u‖ ^ 2 * Real.sqrt t := by ring
  have h_st_quart_u : |rescaledPerturbation V H t u|
      ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 := by
    calc |rescaledPerturbation V H t u|
        ≤ hV.local_const * ‖u‖ ^ 3 / Real.sqrt t := h_st_u_le
      _ = hV.local_const * (‖u‖ ^ 3 / Real.sqrt t) := by ring
      _ ≤ hV.local_const * (δ * ‖u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_cube_to_sq hCs_nn
      _ = (hV.local_const * δ) * ‖u‖ ^ 2 := by ring
      _ ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hδ_const (sq_nonneg _)
  have h_st_quart_neg_u : |rescaledPerturbation V H t (-u)|
      ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 := by
    calc |rescaledPerturbation V H t (-u)|
        ≤ hV.local_const * ‖u‖ ^ 3 / Real.sqrt t := h_st_neg_u_le
      _ = hV.local_const * (‖u‖ ^ 3 / Real.sqrt t) := by ring
      _ ≤ hV.local_const * (δ * ‖u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_cube_to_sq hCs_nn
      _ = (hV.local_const * δ) * ‖u‖ ^ 2 := by ring
      _ ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hδ_const (sq_nonneg _)
  -- Quintic difference bound.
  have h_quintic := abs_rescaledPerturbation_sub_neg_quintic_le V H hV ht u hu_jet
  -- Sum bound (quartic).
  have h_sum := abs_rescaledPerturbation_add_neg_le V H hV.toPotentialTensorApprox
    ht u hu_jet
  -- |s_t(u) - s_t(-u)| ≤ 2·Cs·‖u‖^3/√t.
  have h_st_diff : |rescaledPerturbation V H t u - rescaledPerturbation V H t (-u)|
      ≤ 2 * hV.local_const * ‖u‖ ^ 3 / Real.sqrt t := by
    calc |rescaledPerturbation V H t u - rescaledPerturbation V H t (-u)|
        ≤ |rescaledPerturbation V H t u| + |rescaledPerturbation V H t (-u)| :=
          abs_sub _ _
      _ ≤ hV.local_const * ‖u‖ ^ 3 / Real.sqrt t
          + hV.local_const * ‖u‖ ^ 3 / Real.sqrt t := by
          linarith [h_st_u_le, h_st_neg_u_le]
      _ = 2 * hV.local_const * ‖u‖ ^ 3 / Real.sqrt t := by ring
  -- |s_t(u)² - s_t(-u)²|/2 ≤ 2·jet_C·Cs·‖u‖^7/(t·√t).
  have h_sq_diff : |rescaledPerturbation V H t u ^ 2
        - rescaledPerturbation V H t (-u) ^ 2| / 2
      ≤ 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t) := by
    have h_factor : rescaledPerturbation V H t u ^ 2
          - rescaledPerturbation V H t (-u) ^ 2
        = (rescaledPerturbation V H t u + rescaledPerturbation V H t (-u))
          * (rescaledPerturbation V H t u - rescaledPerturbation V H t (-u)) := by
      ring
    rw [h_factor, abs_mul]
    have h_diff_nn : 0 ≤ |rescaledPerturbation V H t u
        - rescaledPerturbation V H t (-u)| := abs_nonneg _
    calc |rescaledPerturbation V H t u + rescaledPerturbation V H t (-u)|
          * |rescaledPerturbation V H t u - rescaledPerturbation V H t (-u)| / 2
        ≤ (2 * hV.jet_const * ‖u‖ ^ 4 / t)
          * (2 * hV.local_const * ‖u‖ ^ 3 / Real.sqrt t) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 2).le
          have h_jet_C_nn : 0 ≤ hV.jet_const := hV.jet_const_nonneg
          have h_b_nn : 0 ≤ 2 * hV.jet_const * ‖u‖ ^ 4 / t := by
            apply div_nonneg _ ht.le
            apply mul_nonneg (mul_nonneg (by norm_num) h_jet_C_nn)
              (pow_nonneg (norm_nonneg _) _)
          exact mul_le_mul h_sum h_st_diff h_diff_nn h_b_nn
      _ = 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t) := by
          field_simp
  -- Stage-2 Taylor remainder bounds for exp(-s_t(±u)).
  have h_taylor2_u := Laplace.abs_exp_neg_sub_one_add_sub_half_sq_le
    (rescaledPerturbation V H t u)
  have h_taylor2_neg_u := Laplace.abs_exp_neg_sub_one_add_sub_half_sq_le
    (rescaledPerturbation V H t (-u))
  -- max(1, exp(-r)) ≤ exp((c/4)‖u‖²) when |r| ≤ (c/4)‖u‖².
  have h_max_le : ∀ r : ℝ, |r| ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 →
      max 1 (Real.exp (-r)) ≤ Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) := by
    intro r hr
    apply max_le
    · rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      apply Real.exp_le_exp.mpr
      have h_c_nn : 0 ≤ hV.coercive_const := hV.coercive_const_pos.le
      have : 0 ≤ hV.coercive_const / 4 * ‖u‖ ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      linarith
    · apply Real.exp_le_exp.mpr
      calc -r ≤ |r| := neg_le_abs r
        _ ≤ (hV.coercive_const / 4) * ‖u‖ ^ 2 := hr
  -- |s_t(u)|³ ≤ Cs³·‖u‖^9/(t·√t).
  have h_st_cube_u : |rescaledPerturbation V H t u| ^ 3
      ≤ hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t) := by
    have h_pow := pow_le_pow_left₀ (abs_nonneg _) h_st_u_le 3
    rw [show (hV.local_const * ‖u‖ ^ 3 / Real.sqrt t) ^ 3
          = hV.local_const ^ 3 * ‖u‖ ^ 9 / (Real.sqrt t) ^ 3 from by
        rw [div_pow]; ring] at h_pow
    rw [show (Real.sqrt t) ^ 3 = (Real.sqrt t) ^ 2 * Real.sqrt t from by ring,
        hsqrt_t_sq] at h_pow
    exact h_pow
  have h_st_cube_neg_u : |rescaledPerturbation V H t (-u)| ^ 3
      ≤ hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t) := by
    have h_pow := pow_le_pow_left₀ (abs_nonneg _) h_st_neg_u_le 3
    rw [show (hV.local_const * ‖u‖ ^ 3 / Real.sqrt t) ^ 3
          = hV.local_const ^ 3 * ‖u‖ ^ 9 / (Real.sqrt t) ^ 3 from by
        rw [div_pow]; ring] at h_pow
    rw [show (Real.sqrt t) ^ 3 = (Real.sqrt t) ^ 2 * Real.sqrt t from by ring,
        hsqrt_t_sq] at h_pow
    exact h_pow
  -- |R₃(±u)| ≤ Cs³·‖u‖^9·exp((c/4)‖u‖²)/(2·(t·√t)).
  have h_R3_u : |Real.exp (-(rescaledPerturbation V H t u))
        - (1 - rescaledPerturbation V H t u
            + rescaledPerturbation V H t u ^ 2 / 2)|
      ≤ hV.local_const ^ 3 * ‖u‖ ^ 9 *
          Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (2 * (t * Real.sqrt t)) := by
    calc |Real.exp (-(rescaledPerturbation V H t u))
            - (1 - rescaledPerturbation V H t u
                + rescaledPerturbation V H t u ^ 2 / 2)|
        ≤ |rescaledPerturbation V H t u| ^ 3 / 2 *
            max 1 (Real.exp (-(rescaledPerturbation V H t u))) := h_taylor2_u
      _ ≤ (hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t)) / 2 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) := by
          apply mul_le_mul (by linarith [h_st_cube_u]) (h_max_le _ h_st_quart_u)
            (le_trans zero_le_one (le_max_left _ _)) (by positivity)
      _ = hV.local_const ^ 3 * ‖u‖ ^ 9 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (2 * (t * Real.sqrt t)) := by
          field_simp
  have h_R3_neg_u : |Real.exp (-(rescaledPerturbation V H t (-u)))
        - (1 - rescaledPerturbation V H t (-u)
            + rescaledPerturbation V H t (-u) ^ 2 / 2)|
      ≤ hV.local_const ^ 3 * ‖u‖ ^ 9 *
          Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (2 * (t * Real.sqrt t)) := by
    calc |Real.exp (-(rescaledPerturbation V H t (-u)))
            - (1 - rescaledPerturbation V H t (-u)
                + rescaledPerturbation V H t (-u) ^ 2 / 2)|
        ≤ |rescaledPerturbation V H t (-u)| ^ 3 / 2 *
            max 1 (Real.exp (-(rescaledPerturbation V H t (-u)))) := h_taylor2_neg_u
      _ ≤ (hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t)) / 2 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) := by
          apply mul_le_mul (by linarith [h_st_cube_neg_u])
            (h_max_le _ h_st_quart_neg_u)
            (le_trans zero_le_one (le_max_left _ _)) (by positivity)
      _ = hV.local_const ^ 3 * ‖u‖ ^ 9 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (2 * (t * Real.sqrt t)) := by
          field_simp
  -- C_t(-u) = -C_t(u).
  have h_C_neg : expPotCubic V H hV.toPotentialTensorApprox t (-u)
      = -expPotCubic V H hV.toPotentialTensorApprox t u :=
    expPotCubic_neg V H hV.toPotentialTensorApprox t u
  -- Algebraic decomposition of bracket.
  have h_bracket_eq :
      (Real.exp (-(rescaledPerturbation V H t u)) - 1
          + expPotCubic V H hV.toPotentialTensorApprox t u)
        - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
            + expPotCubic V H hV.toPotentialTensorApprox t (-u))
      = -(rescaledPerturbation V H t u - rescaledPerturbation V H t (-u)
          - 2 * expPotCubic V H hV.toPotentialTensorApprox t u)
        + (rescaledPerturbation V H t u ^ 2
            - rescaledPerturbation V H t (-u) ^ 2) / 2
        + (Real.exp (-(rescaledPerturbation V H t u))
            - (1 - rescaledPerturbation V H t u
                + rescaledPerturbation V H t u ^ 2 / 2))
        - (Real.exp (-(rescaledPerturbation V H t (-u)))
            - (1 - rescaledPerturbation V H t (-u)
                + rescaledPerturbation V H t (-u) ^ 2 / 2)) := by
    rw [h_C_neg]; ring
  -- Triangle inequality for 4 terms.
  have h_tri : ∀ a b c d : ℝ, |a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
    intro a b c d
    calc |a + b + c - d| ≤ |a + b + c| + |d| := abs_sub _ _
      _ ≤ |a + b| + |c| + |d| := by gcongr; exact abs_add_le _ _
      _ ≤ |a| + |b| + |c| + |d| := by gcongr; exact abs_add_le _ _
  -- Apply.
  rw [h_bracket_eq]
  calc |-(rescaledPerturbation V H t u - rescaledPerturbation V H t (-u)
            - 2 * expPotCubic V H hV.toPotentialTensorApprox t u)
          + (rescaledPerturbation V H t u ^ 2
              - rescaledPerturbation V H t (-u) ^ 2) / 2
          + (Real.exp (-(rescaledPerturbation V H t u))
              - (1 - rescaledPerturbation V H t u
                  + rescaledPerturbation V H t u ^ 2 / 2))
          - (Real.exp (-(rescaledPerturbation V H t (-u)))
              - (1 - rescaledPerturbation V H t (-u)
                  + rescaledPerturbation V H t (-u) ^ 2 / 2))|
      ≤ |-(rescaledPerturbation V H t u - rescaledPerturbation V H t (-u)
              - 2 * expPotCubic V H hV.toPotentialTensorApprox t u)|
        + |(rescaledPerturbation V H t u ^ 2
            - rescaledPerturbation V H t (-u) ^ 2) / 2|
        + |Real.exp (-(rescaledPerturbation V H t u))
            - (1 - rescaledPerturbation V H t u
                + rescaledPerturbation V H t u ^ 2 / 2)|
        + |Real.exp (-(rescaledPerturbation V H t (-u)))
            - (1 - rescaledPerturbation V H t (-u)
                + rescaledPerturbation V H t (-u) ^ 2 / 2)| := h_tri _ _ _ _
    _ = |rescaledPerturbation V H t u - rescaledPerturbation V H t (-u)
              - 2 * expPotCubic V H hV.toPotentialTensorApprox t u|
        + |rescaledPerturbation V H t u ^ 2
            - rescaledPerturbation V H t (-u) ^ 2| / 2
        + |Real.exp (-(rescaledPerturbation V H t u))
            - (1 - rescaledPerturbation V H t u
                + rescaledPerturbation V H t u ^ 2 / 2)|
        + |Real.exp (-(rescaledPerturbation V H t (-u)))
            - (1 - rescaledPerturbation V H t (-u)
                + rescaledPerturbation V H t (-u) ^ 2 / 2)| := by
          rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
        + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
        + hV.local_const ^ 3 * ‖u‖ ^ 9 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (2 * (t * Real.sqrt t))
        + hV.local_const ^ 3 * ‖u‖ ^ 9 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (2 * (t * Real.sqrt t)) := by
          gcongr
    _ = hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
        + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
        + hV.local_const ^ 3 * ‖u‖ ^ 9 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (t * Real.sqrt t) := by
          field_simp
          ring

/-! ### Pointwise bounds on the scaled jets

These pointwise bounds will feed into the Glocal+Gtail integration arguments
for `expNumErr_i_bound` (i = 1..4). -/

/-- Pointwise bound on the cubic observable jet. For `t > 0`,
`|expNumCubic φ a hφ t u| ≤ (‖Φ‖ / 6) / (t · √t) · ‖u‖³`. -/
private lemma abs_expNumCubic_le
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    |expNumCubic φ a hφ t u| ≤ ‖hφ.Φ‖ / 6 / (t * Real.sqrt t) * ‖u‖ ^ 3 := by
  unfold expNumCubic
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_norm : ‖(fun _ : Fin 3 => u)‖ ≤ ‖u‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i; exact le_refl _
  have h_Φ : |hφ.Φ (fun _ => u)| ≤ ‖hφ.Φ‖ * ‖u‖ ^ 3 := by
    have := hφ.Φ.le_opNorm_mul_pow_of_le h_norm
    simpa [Real.norm_eq_abs] using this
  have h_norm_pow_nn : 0 ≤ ‖u‖ ^ 3 := pow_nonneg (norm_nonneg _) _
  have h_sqrt_inv_pos : 0 < (Real.sqrt t)⁻¹ := by positivity
  have h_factor_nn : 0 ≤ (Real.sqrt t)⁻¹ / t * (1 / 6) := by positivity
  rw [show (Real.sqrt t)⁻¹ / t * ((1 / 6 : ℝ) * hφ.Φ (fun _ => u))
        = ((Real.sqrt t)⁻¹ / t * (1 / 6)) * hφ.Φ (fun _ => u) from by ring,
      abs_mul, abs_of_nonneg h_factor_nn]
  calc (Real.sqrt t)⁻¹ / t * (1 / 6) * |hφ.Φ (fun _ => u)|
      ≤ (Real.sqrt t)⁻¹ / t * (1 / 6) * (‖hφ.Φ‖ * ‖u‖ ^ 3) := by
        gcongr
    _ = ‖hφ.Φ‖ / 6 / (t * Real.sqrt t) * ‖u‖ ^ 3 := by
        field_simp

/-- Pointwise bound on the linear observable jet. For `t > 0`,
`|expNumLin a t u| ≤ (∑|aᵢ|) / √t · ‖u‖`. -/
private lemma abs_expNumLin_le
    (a : ι → ℝ)
    {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    |expNumLin a t u| ≤ (∑ i, |a i|) / Real.sqrt t * ‖u‖ := by
  unfold expNumLin
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rw [abs_mul]
  rw [show |(Real.sqrt t)⁻¹| = (Real.sqrt t)⁻¹ from
      abs_of_pos (by positivity)]
  have h_dot : |dot a u| ≤ (∑ i, |a i|) * ‖u‖ := abs_dot_le_l1_mul_norm a u
  have h_inv_nn : 0 ≤ (Real.sqrt t)⁻¹ := by positivity
  calc (Real.sqrt t)⁻¹ * |dot a u|
      ≤ (Real.sqrt t)⁻¹ * ((∑ i, |a i|) * ‖u‖) := by
        gcongr
    _ = (∑ i, |a i|) / Real.sqrt t * ‖u‖ := by
        rw [div_eq_inv_mul]; ring

-- (Bound on `expNumQuad` deferred — not needed for J₂.)

/-- **Local pointwise bound for J₂ integrand**: on `‖u‖ ≤ δ · √t`,
`|expNumCubic · gW · (exp(-s_t) - 1)| ≤ (‖Φ‖·Cs / 6) / t² · ‖u‖⁶ · exp(-(c/4)·‖u‖²)`.

Combines `abs_expNumCubic_le` with the existing
`abs_gaussianWeight_mul_exp_sub_one_le_local`. -/
private lemma abs_expNumCubic_mul_gW_mul_exp_sub_one_local_le
    (V φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hφ : ObservableTensorApprox φ a)
    {c R Cs : ℝ}
    (hc_pos : 0 < c) (hR_pos : 0 < R) (hCs_nn : 0 ≤ Cs)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - (1/2) * quadForm H w| ≤ Cs * ‖w‖ ^ 3)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le_R : δ ≤ R)
    (hδ_const : Cs * δ ≤ c / 4)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ δ * Real.sqrt t) :
    |expNumCubic φ a hφ t u * gaussianWeight H u
        * (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ (‖hφ.Φ‖ * Cs / 6 / t ^ 2) * ‖u‖ ^ 6 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
  have hΦ_nn : 0 ≤ ‖hφ.Φ‖ := norm_nonneg _
  have h_cubic := abs_expNumCubic_le φ a hφ ht u
  have h_gW_exp :=
    abs_gaussianWeight_mul_exp_sub_one_le_local V H hc_pos hR_pos hCs_nn
      h_coer h_local hδ_pos hδ_le_R hδ_const ht u hu
  have h_cubic_nn : 0 ≤ ‖hφ.Φ‖ / 6 / (t * Real.sqrt t) * ‖u‖ ^ 3 := by positivity
  have h_gW_exp_nn : 0 ≤ Cs * ‖u‖ ^ 3 / Real.sqrt t *
      Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by positivity
  rw [show expNumCubic φ a hφ t u * gaussianWeight H u
        * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
      = expNumCubic φ a hφ t u
        * (gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)) from by ring,
      abs_mul]
  calc |expNumCubic φ a hφ t u| *
            |gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ (‖hφ.Φ‖ / 6 / (t * Real.sqrt t) * ‖u‖ ^ 3) *
          (Cs * ‖u‖ ^ 3 / Real.sqrt t *
            Real.exp (-((c / 4) * ‖u‖ ^ 2))) :=
        mul_le_mul h_cubic h_gW_exp (abs_nonneg _) h_cubic_nn
    _ = (‖hφ.Φ‖ * Cs / 6 / t ^ 2) * ‖u‖ ^ 6 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
        have h_sq : Real.sqrt t * Real.sqrt t = t :=
          Real.mul_self_sqrt ht.le
        rw [show ‖u‖ ^ 6 = ‖u‖ ^ 3 * ‖u‖ ^ 3 from by ring,
            show (t : ℝ) ^ 2 = (t * Real.sqrt t) * Real.sqrt t from by
              rw [show (t * Real.sqrt t) * Real.sqrt t = t * (Real.sqrt t * Real.sqrt t) from by ring,
                  h_sq, sq]]
        field_simp

/-- **Tail pointwise bound for J₂ integrand**: on `‖u‖ > δ · √t`,
`|expNumCubic · gW · (exp(-s_t) - 1)| ≤ (‖Φ‖ / 3) / (t·√t) · ‖u‖³ ·
  exp(-(c/4)·‖u‖²) · exp(-(c·δ²/4)·t)`.

Combines `abs_expNumCubic_le` with the existing
`abs_gaussianWeight_mul_exp_sub_one_le_tail`. -/
private lemma abs_expNumCubic_mul_gW_mul_exp_sub_one_tail_le
    (V φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hφ : ObservableTensorApprox φ a)
    {c R Cs : ℝ}
    (hc_pos : 0 < c) (hR_pos : 0 < R) (hCs_nn : 0 ≤ Cs)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - (1/2) * quadForm H w| ≤ Cs * ‖w‖ ^ 3)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : δ * Real.sqrt t < ‖u‖) :
    |expNumCubic φ a hφ t u * gaussianWeight H u
        * (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ (‖hφ.Φ‖ / 3 / (t * Real.sqrt t)) * ‖u‖ ^ 3 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
          Real.exp (-((c * δ ^ 2 / 4) * t)) := by
  have h_cubic := abs_expNumCubic_le φ a hφ ht u
  have h_gW_exp :=
    abs_gaussianWeight_mul_exp_sub_one_le_tail V H hc_pos hR_pos hCs_nn
      h_coer h_local hδ_pos ht u hu
  have h_cubic_nn : 0 ≤ ‖hφ.Φ‖ / 6 / (t * Real.sqrt t) * ‖u‖ ^ 3 := by positivity
  rw [show expNumCubic φ a hφ t u * gaussianWeight H u
        * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
      = expNumCubic φ a hφ t u
        * (gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)) from by ring,
      abs_mul]
  calc |expNumCubic φ a hφ t u| *
            |gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ (‖hφ.Φ‖ / 6 / (t * Real.sqrt t) * ‖u‖ ^ 3) *
          (2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
            Real.exp (-((c * δ ^ 2 / 4) * t))) :=
        mul_le_mul h_cubic h_gW_exp (abs_nonneg _) h_cubic_nn
    _ = (‖hφ.Φ‖ / 3 / (t * Real.sqrt t)) * ‖u‖ ^ 3 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
          Real.exp (-((c * δ ^ 2 / 4) * t)) := by
        ring

/-- **Local pointwise bound on `expNumObsRem`**: on `‖u‖ ≤ jet_radius·√t`,
`|R_{φ,t}(u)| ≤ jet_const · ‖u‖⁴ / t²`.

This is `Φ_jet_bound` rescaled. The proof uses tensor scaling for the cubic,
quadratic, and linear jets:
`(1/2) quadForm A ((√t)⁻¹·u) = (1/(2t)) · quadForm A u`,
`Φ((√t)⁻¹·u, ..., (√t)⁻¹·u) = (1/(t·√t)) · Φ(u, u, u)` (trilinear),
`dot a ((√t)⁻¹·u) = (√t)⁻¹ · dot a u`. -/
private lemma abs_expNumObsRem_local_le
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ)
    (hu : ‖u‖ ≤ hφ.jet_radius * Real.sqrt t) :
    |expNumObsRem φ a hφ t u| ≤ hφ.jet_const * ‖u‖ ^ 4 / t ^ 2 := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have h_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hjet_R_pos : 0 < hφ.jet_radius := hφ.jet_radius_pos
  -- ‖(√t)⁻¹•u‖ ≤ jet_radius
  have h_norm_le : ‖(Real.sqrt t)⁻¹ • u‖ ≤ hφ.jet_radius := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹)]
    rw [show (Real.sqrt t)⁻¹ * ‖u‖ = ‖u‖ / Real.sqrt t from by field_simp]
    rwa [div_le_iff₀ hsqrt_pos]
  -- ‖(√t)⁻¹•u‖^4 = ‖u‖^4 / t²
  have h_norm_pow : ‖(Real.sqrt t)⁻¹ • u‖ ^ 4 = ‖u‖ ^ 4 / t ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹),
        mul_pow, inv_pow]
    rw [show (Real.sqrt t) ^ 4 = (Real.sqrt t * Real.sqrt t) ^ 2 from by ring, h_sq]
    field_simp
  -- Apply Φ_jet_bound to w = (√t)⁻¹·u.
  have h_jet := hφ.Φ_jet_bound ((Real.sqrt t)⁻¹ • u) h_norm_le
  rw [h_norm_pow] at h_jet
  -- dot a ((√t)⁻¹·u) = (√t)⁻¹ · dot a u
  have h_dot_eq : dot a ((Real.sqrt t)⁻¹ • u) = (Real.sqrt t)⁻¹ * dot a u := by
    unfold dot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    show a i * ((Real.sqrt t)⁻¹ * u i) = (Real.sqrt t)⁻¹ * (a i * u i)
    ring
  -- quadForm A ((√t)⁻¹·u) = (1/t) · quadForm A u
  have h_qf : quadForm hφ.A ((Real.sqrt t)⁻¹ • u) = (1 / t) * quadForm hφ.A u := by
    rw [quadForm_smul]
    rw [show ((Real.sqrt t)⁻¹) ^ 2 = ((Real.sqrt t) ^ 2)⁻¹ from by rw [inv_pow]]
    rw [show (Real.sqrt t) ^ 2 = t from by rw [sq, h_sq]]
    ring
  -- Φ ((√t)⁻¹·u, ..., (√t)⁻¹·u) = (√t)⁻¹³ · Φ(u,u,u)
  have h_Φ_eq : hφ.Φ (fun _ : Fin 3 => (Real.sqrt t)⁻¹ • u)
      = ((Real.sqrt t)⁻¹) ^ 3 * hφ.Φ (fun _ => u) := by
    have h1 := hφ.Φ.map_smul_univ (fun _ : Fin 3 => (Real.sqrt t)⁻¹) (fun _ => u)
    simpa using h1
  rw [h_dot_eq, h_qf, h_Φ_eq] at h_jet
  unfold expNumObsRem expNumLin expNumQuad expNumCubic
  rw [show hφ.jet_const * ‖u‖ ^ 4 / t ^ 2
        = hφ.jet_const * (‖u‖ ^ 4 / t ^ 2) from by ring]
  have h_sqcube : (Real.sqrt t)⁻¹ ^ 3 = (Real.sqrt t)⁻¹ / t := by
    rw [show (Real.sqrt t)⁻¹ ^ 3
          = (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ from by ring]
    rw [show (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = ((Real.sqrt t) * (Real.sqrt t))⁻¹ from by
        rw [mul_inv]]
    rw [h_sq]
    field_simp
  rw [h_sqcube] at h_jet
  have h_inner_eq : φ ((Real.sqrt t)⁻¹ • u) -
        (Real.sqrt t)⁻¹ * dot a u -
        1 / t * (1 / 2 * quadForm hφ.A u) -
        (Real.sqrt t)⁻¹ / t * (1 / 6 * hφ.Φ (fun _ => u))
      = φ ((Real.sqrt t)⁻¹ • u) -
        ((Real.sqrt t)⁻¹ * dot a u + 1 / 2 * (1 / t * quadForm hφ.A u) +
          1 / 6 * ((Real.sqrt t)⁻¹ / t * hφ.Φ (fun _ => u))) := by
    ring
  rw [h_inner_eq]
  exact h_jet

/-- **Global polynomial bound on `expNumObsRem`** (for J₁ tail). For `t ≥ 1`,
`|R_{φ,t}(u)| ≤ R_const · (1 + ‖u‖^N)` where `N := max p 3` and the constant
combines `Kφ`, `∑|aᵢ|`, `|ι|·‖A‖_op`, and `‖Φ‖_op`. T-independent. -/
private lemma abs_expNumObsRem_global_le
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (hφ : ObservableTensorApprox φ a)
    {Kφ : ℝ} {p : ℕ} (hKφ_nn : 0 ≤ Kφ)
    (hpoly : ∀ w : ι → ℝ, |φ w| ≤ Kφ * (1 + ‖w‖ ^ p))
    {t : ℝ} (ht : 1 ≤ t) (u : ι → ℝ) :
    |expNumObsRem φ a hφ t u|
      ≤ Kφ * (1 + ‖u‖ ^ p)
        + (∑ i, |a i|) * ‖u‖
        + (1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2
        + (‖hφ.Φ‖ / 6) * ‖u‖ ^ 3 := by
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_ge_one : 1 ≤ Real.sqrt t := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt ht
  have hsqrt_inv_le : (Real.sqrt t)⁻¹ ≤ 1 := by
    rw [show (1 : ℝ) = (1 : ℝ)⁻¹ from (inv_one).symm]
    exact inv_anti₀ Real.zero_lt_one hsqrt_ge_one
  have h_norm_sm_le : ‖(Real.sqrt t)⁻¹ • u‖ ≤ ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹)]
    nlinarith [norm_nonneg u]
  -- |φ((√t)⁻¹·u)| ≤ Kφ · (1 + ‖u‖^p)
  have h_phi : |φ ((Real.sqrt t)⁻¹ • u)| ≤ Kφ * (1 + ‖u‖ ^ p) := by
    have h := hpoly ((Real.sqrt t)⁻¹ • u)
    have h_norm_pow : ‖(Real.sqrt t)⁻¹ • u‖ ^ p ≤ ‖u‖ ^ p :=
      pow_le_pow_left₀ (norm_nonneg _) h_norm_sm_le p
    calc |φ ((Real.sqrt t)⁻¹ • u)|
        ≤ Kφ * (1 + ‖(Real.sqrt t)⁻¹ • u‖ ^ p) := h
      _ ≤ Kφ * (1 + ‖u‖ ^ p) := by
            apply mul_le_mul_of_nonneg_left _ hKφ_nn; linarith
  -- |L_t| ≤ (∑|aᵢ|) · ‖u‖
  have h_lin : |expNumLin a t u| ≤ (∑ i, |a i|) * ‖u‖ := by
    have h := abs_expNumLin_le a ht_pos u
    have hA_nn : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hsqrt_inv_le' : (∑ i, |a i|) / Real.sqrt t ≤ ∑ i, |a i| := by
      rw [div_le_iff₀ hsqrt_pos]
      nlinarith
    calc |expNumLin a t u|
        ≤ (∑ i, |a i|) / Real.sqrt t * ‖u‖ := h
      _ ≤ (∑ i, |a i|) * ‖u‖ :=
          mul_le_mul_of_nonneg_right hsqrt_inv_le' (norm_nonneg _)
  -- |Q_t| ≤ (1/2) · |ι| · ‖A‖ · ‖u‖²
  have h_quad : |expNumQuad φ a hφ t u|
      ≤ (1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by
    unfold expNumQuad
    have h_qf : |quadForm hφ.A u| ≤ Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by
      unfold quadForm
      show |∑ i, u i * (hφ.A u) i| ≤ Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2
      have h_each : ∀ i, |u i * (hφ.A u) i| ≤ ‖u‖ * ‖hφ.A u‖ := fun i => by
        rw [abs_mul]
        apply mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm (hφ.A u) i)
          (abs_nonneg _) (norm_nonneg _)
      have h_sum_le : |∑ i, u i * (hφ.A u) i| ≤ ∑ i, |u i * (hφ.A u) i| :=
        Finset.abs_sum_le_sum_abs _ _
      have h_sum_le2 : ∑ i, |u i * (hφ.A u) i|
          ≤ Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := by
        calc ∑ i, |u i * (hφ.A u) i|
            ≤ ∑ _ : ι, ‖u‖ * ‖hφ.A u‖ := Finset.sum_le_sum (fun i _ => h_each i)
          _ = Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := by
                rw [Finset.sum_const, Finset.card_univ]; ring
      have h_Au : ‖hφ.A u‖ ≤ ‖hφ.A‖ * ‖u‖ := hφ.A.le_opNorm u
      calc |∑ i, u i * (hφ.A u) i|
          ≤ Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := le_trans h_sum_le h_sum_le2
        _ ≤ Fintype.card ι * (‖u‖ * (‖hφ.A‖ * ‖u‖)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left h_Au (norm_nonneg _)
        _ = Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by ring
    have ht_inv_le : 1 / t ≤ 1 := by
      rw [div_le_iff₀ ht_pos]; linarith
    have h_one_div_t_nn : 0 ≤ 1 / t := by positivity
    have h_qf_nn : 0 ≤ Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by positivity
    rw [show (1 / t : ℝ) * ((1 / 2 : ℝ) * quadForm hφ.A u)
          = (1 / t) * (1 / 2) * quadForm hφ.A u from by ring,
        abs_mul, abs_mul,
        abs_of_nonneg h_one_div_t_nn,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc 1 / t * (1 / 2) * |quadForm hφ.A u|
        ≤ 1 / t * (1 / 2) *
            (Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2) := by gcongr
      _ ≤ 1 * (1 / 2) *
            (Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ h_qf_nn
              apply mul_le_mul_of_nonneg_right ht_inv_le (by norm_num)
      _ = (1 / 2 : ℝ) * Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by ring
  -- |P_t| ≤ (‖Φ‖/6) · ‖u‖³
  have h_cubic : |expNumCubic φ a hφ t u| ≤ (‖hφ.Φ‖ / 6) * ‖u‖ ^ 3 := by
    have h := abs_expNumCubic_le φ a hφ ht_pos u
    have h_t_sqrt_ge_one : 1 ≤ t * Real.sqrt t := by
      calc (1 : ℝ) = 1 * 1 := (mul_one _).symm
        _ ≤ t * Real.sqrt t := mul_le_mul ht hsqrt_ge_one (by norm_num) ht_pos.le
    have h_inv_le : 1 / (t * Real.sqrt t) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h_div_nn : 0 ≤ ‖hφ.Φ‖ / 6 := by positivity
    have h_norm_pow_nn : 0 ≤ ‖u‖ ^ 3 := pow_nonneg (norm_nonneg _) _
    calc |expNumCubic φ a hφ t u|
        ≤ ‖hφ.Φ‖ / 6 / (t * Real.sqrt t) * ‖u‖ ^ 3 := h
      _ = ‖hφ.Φ‖ / 6 * (1 / (t * Real.sqrt t)) * ‖u‖ ^ 3 := by ring
      _ ≤ ‖hφ.Φ‖ / 6 * 1 * ‖u‖ ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ h_norm_pow_nn
          apply mul_le_mul_of_nonneg_left h_inv_le h_div_nn
      _ = ‖hφ.Φ‖ / 6 * ‖u‖ ^ 3 := by ring
  -- Combine via triangle inequality.
  unfold expNumObsRem
  calc |φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u
          - expNumQuad φ a hφ t u - expNumCubic φ a hφ t u|
      ≤ |φ ((Real.sqrt t)⁻¹ • u)| + |expNumLin a t u|
        + |expNumQuad φ a hφ t u| + |expNumCubic φ a hφ t u| := by
        calc |φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u
                - expNumQuad φ a hφ t u - expNumCubic φ a hφ t u|
            ≤ |φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u
                - expNumQuad φ a hφ t u| + |expNumCubic φ a hφ t u| := by
                rw [show φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u
                      - expNumQuad φ a hφ t u - expNumCubic φ a hφ t u
                    = (φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u
                        - expNumQuad φ a hφ t u) + (- expNumCubic φ a hφ t u) from by
                    ring]
                calc |(φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u
                        - expNumQuad φ a hφ t u) + (- expNumCubic φ a hφ t u)|
                    ≤ |φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u
                        - expNumQuad φ a hφ t u| + |- expNumCubic φ a hφ t u| :=
                      abs_add_le _ _
                  _ = _ := by rw [abs_neg]
          _ ≤ (|φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u|
                + |expNumQuad φ a hφ t u|) + |expNumCubic φ a hφ t u| := by
              gcongr
              rw [show φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u
                    - expNumQuad φ a hφ t u
                  = (φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u)
                    + (-expNumQuad φ a hφ t u) from by ring]
              calc |(φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u)
                    + (-expNumQuad φ a hφ t u)|
                  ≤ |φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u|
                    + |-expNumQuad φ a hφ t u| := abs_add_le _ _
                _ = _ := by rw [abs_neg]
          _ ≤ (|φ ((Real.sqrt t)⁻¹ • u)| + |expNumLin a t u|
                + |expNumQuad φ a hφ t u|) + |expNumCubic φ a hφ t u| := by
              gcongr
              rw [show φ ((Real.sqrt t)⁻¹ • u) - expNumLin a t u
                  = φ ((Real.sqrt t)⁻¹ • u) + (-expNumLin a t u) from by ring]
              calc |φ ((Real.sqrt t)⁻¹ • u) + (-expNumLin a t u)|
                  ≤ |φ ((Real.sqrt t)⁻¹ • u)| + |-expNumLin a t u| := abs_add_le _ _
                _ = _ := by rw [abs_neg]
          _ = _ := by ring
    _ ≤ Kφ * (1 + ‖u‖ ^ p) + (∑ i, |a i|) * ‖u‖
        + (1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2
        + ‖hφ.Φ‖ / 6 * ‖u‖ ^ 3 := by
        gcongr

/-! ### Integrability building blocks for the decomposition lemma -/

/-- Integrability of `expNumLin a t u · gaussianWeight H u` for `t > 0`.
Dominated by `(√t)⁻¹·(∑|aᵢ|)·‖u‖·gW(u)`, which is integrable from
`PotentialJetApprox.int_norm_pow_gW 1`. -/
private lemma integrable_expNumLin_mul_gaussianWeight
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialJetApprox V H)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ => expNumLin a t u * gaussianWeight H u) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_dom_int : Integrable (fun u : ι → ℝ =>
      ((Real.sqrt t)⁻¹ * (∑ i, |a i|)) * (‖u‖ * gaussianWeight H u)) := by
    have := hV.int_norm_pow_gW 1
    simp only [pow_one] at this
    exact this.const_mul _
  apply h_dom_int.mono'
  · -- Strongly measurable.
    have h_dot_cont : Continuous (fun u : ι → ℝ => dot a u) := by
      unfold dot
      exact continuous_finset_sum _
        (fun i _ => continuous_const.mul (continuous_apply i))
    exact ((continuous_const.mul h_dot_cont).mul
      (continuous_gaussianWeight H)).aestronglyMeasurable
  · filter_upwards with u
    have h_lin_le : |expNumLin a t u|
        ≤ ((Real.sqrt t)⁻¹ * (∑ i, |a i|)) * ‖u‖ := by
      unfold expNumLin
      rw [abs_mul, abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹)]
      have h_dot_le : |dot a u| ≤ (∑ i, |a i|) * ‖u‖ := abs_dot_le_l1_mul_norm a u
      calc (Real.sqrt t)⁻¹ * |dot a u|
          ≤ (Real.sqrt t)⁻¹ * ((∑ i, |a i|) * ‖u‖) := by
            apply mul_le_mul_of_nonneg_left h_dot_le (by positivity)
        _ = (Real.sqrt t)⁻¹ * (∑ i, |a i|) * ‖u‖ := by ring
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_gW_nn]
    calc |expNumLin a t u| * gaussianWeight H u
        ≤ ((Real.sqrt t)⁻¹ * (∑ i, |a i|)) * ‖u‖ * gaussianWeight H u :=
          mul_le_mul_of_nonneg_right h_lin_le h_gW_nn
      _ = ((Real.sqrt t)⁻¹ * (∑ i, |a i|)) * (‖u‖ * gaussianWeight H u) := by ring

/-- Integrability of `expNumQuad φ a hφ t u · gaussianWeight H u` for `t > 0`.
Dominated by `(1/(2t))·|ι|·‖A‖·‖u‖²·gW`, integrable from `int_norm_pow_gW 2`. -/
private lemma integrable_expNumQuad_mul_gaussianWeight
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      expNumQuad φ a hφ t u * gaussianWeight H u) := by
  have h_dom_int : Integrable (fun u : ι → ℝ =>
      ((1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖)) *
        (‖u‖ ^ 2 * gaussianWeight H u)) :=
    (hV.int_norm_pow_gW 2).const_mul _
  apply h_dom_int.mono'
  · have h_qf_cont : Continuous (fun u : ι → ℝ => quadForm hφ.A u) := by
      show Continuous (fun u : ι → ℝ => ∑ i, u i * (hφ.A u) i)
      refine continuous_finset_sum _ (fun i _ => ?_)
      exact (continuous_apply i).mul ((continuous_apply i).comp hφ.A.continuous)
    have h_eN_cont : Continuous (fun u : ι → ℝ => expNumQuad φ a hφ t u) := by
      unfold expNumQuad
      exact continuous_const.mul (continuous_const.mul h_qf_cont)
    exact (h_eN_cont.mul (continuous_gaussianWeight H)).aestronglyMeasurable
  · filter_upwards with u
    have h_qf_le : |quadForm hφ.A u| ≤ Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by
      unfold quadForm
      have h_each : ∀ i, |u i * (hφ.A u) i| ≤ ‖u‖ * ‖hφ.A u‖ := fun i => by
        rw [abs_mul]
        apply mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm (hφ.A u) i)
          (abs_nonneg _) (norm_nonneg _)
      have h_sum_le : |∑ i, u i * (hφ.A u) i| ≤ ∑ i, |u i * (hφ.A u) i| :=
        Finset.abs_sum_le_sum_abs _ _
      have h_sum_le2 : ∑ i, |u i * (hφ.A u) i|
          ≤ Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := by
        calc ∑ i, |u i * (hφ.A u) i|
            ≤ ∑ _ : ι, ‖u‖ * ‖hφ.A u‖ := Finset.sum_le_sum (fun i _ => h_each i)
          _ = Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := by
                rw [Finset.sum_const, Finset.card_univ]; ring
      have h_Au : ‖hφ.A u‖ ≤ ‖hφ.A‖ * ‖u‖ := hφ.A.le_opNorm u
      calc |∑ i, u i * (hφ.A u) i|
          ≤ Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := le_trans h_sum_le h_sum_le2
        _ ≤ Fintype.card ι * (‖u‖ * (‖hφ.A‖ * ‖u‖)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left h_Au (norm_nonneg _)
        _ = Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by ring
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    have h_norm_pow_nn : 0 ≤ ‖u‖ ^ 2 := pow_nonneg (norm_nonneg _) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_gW_nn]
    have h_quad_le : |expNumQuad φ a hφ t u|
        ≤ (1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖) * ‖u‖ ^ 2 := by
      unfold expNumQuad
      rw [show (1 / t : ℝ) * ((1/2 : ℝ) * quadForm hφ.A u)
            = (1 / t) * (1 / 2) * quadForm hφ.A u from by ring,
          abs_mul, abs_mul,
          abs_of_pos (by positivity : (0:ℝ) < 1/t),
          abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      calc (1 / t) * (1 / 2) * |quadForm hφ.A u|
          ≤ (1 / t) * (1 / 2) *
              (Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2) := by gcongr
        _ = (1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖) * ‖u‖ ^ 2 := by ring
    calc |expNumQuad φ a hφ t u| * gaussianWeight H u
        ≤ ((1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖) * ‖u‖ ^ 2)
            * gaussianWeight H u := by
          apply mul_le_mul_of_nonneg_right h_quad_le h_gW_nn
      _ = ((1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖))
            * (‖u‖ ^ 2 * gaussianWeight H u) := by ring

/-- Integrability of `expNumCubic φ a hφ t u · gaussianWeight H u` for `t > 0`.
Dominated by `((√t)⁻¹/t)·(‖Φ‖/6)·‖u‖³·gW`, integrable from `int_norm_pow_gW 3`. -/
private lemma integrable_expNumCubic_mul_gaussianWeight
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      expNumCubic φ a hφ t u * gaussianWeight H u) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_dom_int : Integrable (fun u : ι → ℝ =>
      ((Real.sqrt t)⁻¹ / t * (‖hφ.Φ‖ / 6)) *
        (‖u‖ ^ 3 * gaussianWeight H u)) :=
    (hV.int_norm_pow_gW 3).const_mul _
  apply h_dom_int.mono'
  · have h_Φ_cont : Continuous (fun u : ι → ℝ => hφ.Φ (fun _ : Fin 3 => u)) := by
      have h_diag : Continuous (fun u : ι → ℝ => fun _ : Fin 3 => u) :=
        continuous_pi (fun _ => continuous_id)
      exact hφ.Φ.cont.comp h_diag
    have h_eN_cont : Continuous (fun u : ι → ℝ => expNumCubic φ a hφ t u) := by
      unfold expNumCubic
      exact continuous_const.mul (continuous_const.mul h_Φ_cont)
    exact (h_eN_cont.mul (continuous_gaussianWeight H)).aestronglyMeasurable
  · filter_upwards with u
    have h_cubic_le := abs_expNumCubic_le φ a hφ ht u
    -- |expNumCubic| ≤ ‖Φ‖/6/(t·√t) · ‖u‖³ = ((√t)⁻¹/t · ‖Φ‖/6) · ‖u‖³.
    have h_factor_eq : ‖hφ.Φ‖ / 6 / (t * Real.sqrt t)
        = (Real.sqrt t)⁻¹ / t * (‖hφ.Φ‖ / 6) := by
      have ht_ne : t ≠ 0 := ne_of_gt ht
      have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
      field_simp
    rw [h_factor_eq] at h_cubic_le
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_gW_nn]
    calc |expNumCubic φ a hφ t u| * gaussianWeight H u
        ≤ ((Real.sqrt t)⁻¹ / t * (‖hφ.Φ‖ / 6) * ‖u‖ ^ 3) * gaussianWeight H u :=
          mul_le_mul_of_nonneg_right h_cubic_le h_gW_nn
      _ = ((Real.sqrt t)⁻¹ / t * (‖hφ.Φ‖ / 6)) *
            (‖u‖ ^ 3 * gaussianWeight H u) := by ring

/-- Integrability of `expNumLin a t u · expPotCubic V H hV t u · gaussianWeight H u`
for `t > 0`. Dominated by `(1/(6t))·(∑|aᵢ|)·‖T‖·‖u‖⁴·gW`, integrable from
`int_norm_pow_gW 4`. -/
private lemma integrable_expNumLin_mul_expPotCubic_mul_gaussianWeight
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      expNumLin a t u * expPotCubic V H hV t u * gaussianWeight H u) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_dom_int : Integrable (fun u : ι → ℝ =>
      ((1 / t) * ((∑ i, |a i|) * (‖hV.T‖ / 6))) *
        (‖u‖ ^ 4 * gaussianWeight H u)) :=
    (hV.int_norm_pow_gW 4).const_mul _
  apply h_dom_int.mono'
  · have h_dot_cont : Continuous (fun u : ι → ℝ => dot a u) := by
      unfold dot
      exact continuous_finset_sum _
        (fun i _ => continuous_const.mul (continuous_apply i))
    have h_T_cont : Continuous (fun u : ι → ℝ => hV.T (fun _ : Fin 3 => u)) := by
      have h_diag : Continuous (fun u : ι → ℝ => fun _ : Fin 3 => u) :=
        continuous_pi (fun _ => continuous_id)
      exact hV.T.cont.comp h_diag
    have h_lin_cont : Continuous (fun u : ι → ℝ => expNumLin a t u) := by
      unfold expNumLin
      exact continuous_const.mul h_dot_cont
    have h_pot_cont : Continuous (fun u : ι → ℝ => expPotCubic V H hV t u) := by
      unfold expPotCubic
      exact continuous_const.mul (continuous_const.mul h_T_cont)
    exact ((h_lin_cont.mul h_pot_cont).mul
      (continuous_gaussianWeight H)).aestronglyMeasurable
  · filter_upwards with u
    have h_lin := abs_expNumLin_le a ht u
    -- |expPotCubic| ≤ (√t)⁻¹·(1/6)·‖T‖·‖u‖³.
    have h_pot : |expPotCubic V H hV t u| ≤ (Real.sqrt t)⁻¹ * ((‖hV.T‖ / 6) * ‖u‖ ^ 3) := by
      unfold expPotCubic
      have h_norm : ‖(fun _ : Fin 3 => u)‖ ≤ ‖u‖ := by
        rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
        intro i; exact le_refl _
      have h_T : |hV.T (fun _ => u)| ≤ ‖hV.T‖ * ‖u‖ ^ 3 := by
        have := hV.T.le_opNorm_mul_pow_of_le h_norm
        simpa [Real.norm_eq_abs] using this
      rw [abs_mul, abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹)]
      have h_one_six : (0 : ℝ) ≤ 1/6 := by norm_num
      rw [show ((1 / 6 : ℝ) * hV.T (fun _ => u))
            = (1 / 6) * hV.T (fun _ => u) from rfl]
      rw [abs_mul, abs_of_nonneg h_one_six]
      calc (Real.sqrt t)⁻¹ * (1 / 6 * |hV.T fun _ => u|)
          ≤ (Real.sqrt t)⁻¹ * (1 / 6 * (‖hV.T‖ * ‖u‖ ^ 3)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left h_T (by norm_num)
        _ = (Real.sqrt t)⁻¹ * (‖hV.T‖ / 6 * ‖u‖ ^ 3) := by ring
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    have h_lin_nn : 0 ≤ |expNumLin a t u| := abs_nonneg _
    have h_pot_nn : 0 ≤ |expPotCubic V H hV t u| := abs_nonneg _
    have h_lin_dom_nn : 0 ≤ (∑ i, |a i|) / Real.sqrt t * ‖u‖ := by
      apply mul_nonneg (by positivity) (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_gW_nn, abs_mul]
    calc |expNumLin a t u| * |expPotCubic V H hV t u| * gaussianWeight H u
        ≤ ((∑ i, |a i|) / Real.sqrt t * ‖u‖) *
            ((Real.sqrt t)⁻¹ * ((‖hV.T‖ / 6) * ‖u‖ ^ 3))
            * gaussianWeight H u := by
          apply mul_le_mul_of_nonneg_right _ h_gW_nn
          exact mul_le_mul h_lin h_pot h_pot_nn h_lin_dom_nn
      _ = ((1 / t) * ((∑ i, |a i|) * (‖hV.T‖ / 6))) *
            (‖u‖ ^ 4 * gaussianWeight H u) := by
          have h_sq : Real.sqrt t * Real.sqrt t = t :=
            Real.mul_self_sqrt ht.le
          have ht_ne : t ≠ 0 := ne_of_gt ht
          have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
          have h_sq2 : (Real.sqrt t) ^ 2 = t := by rw [sq]; exact h_sq
          field_simp
          rw [h_sq2]; ring

/-! ### Integrability of the J_i integrands (for the decomposition) -/

/-- Integrability of `expNumCubic φ a hφ t u · gW(u) · exp(-(rescaledPerturbation V H t u))`,
the J₁-style integrand with full Gibbs factor. -/
private lemma integrable_expNumCubic_mul_gW_mul_rescaled_weight
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV_cont : Continuous V)
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      expNumCubic φ a hφ t u * gaussianWeight H u
        * Real.exp (-(rescaledPerturbation V H t u))) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_dom_int : Integrable (fun u : ι → ℝ =>
      ((Real.sqrt t)⁻¹ / t * (‖hφ.Φ‖ / 6)) *
        (‖u‖ ^ 3 * (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))))) :=
    (integrable_pow_norm_mul_rescaled_weight V hV_cont H hc_pos h_coer 3 ht).const_mul _
  apply h_dom_int.mono'
  · have h_Φ_cont : Continuous (fun u : ι → ℝ => hφ.Φ (fun _ : Fin 3 => u)) := by
      have h_diag : Continuous (fun u : ι → ℝ => fun _ : Fin 3 => u) :=
        continuous_pi (fun _ => continuous_id)
      exact hφ.Φ.cont.comp h_diag
    have h_eN_cont : Continuous (fun u : ι → ℝ => expNumCubic φ a hφ t u) := by
      unfold expNumCubic
      exact continuous_const.mul (continuous_const.mul h_Φ_cont)
    exact ((h_eN_cont.mul (continuous_gaussianWeight H)).mul
      (Real.continuous_exp.comp
        (continuous_rescaledPerturbation hV_cont H t).neg)).aestronglyMeasurable
  · filter_upwards with u
    have h_cubic_le := abs_expNumCubic_le φ a hφ ht u
    have h_factor_eq : ‖hφ.Φ‖ / 6 / (t * Real.sqrt t)
        = (Real.sqrt t)⁻¹ / t * (‖hφ.Φ‖ / 6) := by
      have ht_ne : t ≠ 0 := ne_of_gt ht
      have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
      field_simp
    rw [h_factor_eq] at h_cubic_le
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    have h_exp_nn : 0 ≤ Real.exp (-(rescaledPerturbation V H t u)) := (Real.exp_pos _).le
    have h_prod_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg h_gW_nn h_exp_nn
    rw [Real.norm_eq_abs]
    rw [show expNumCubic φ a hφ t u * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t u))
        = expNumCubic φ a hφ t u * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) from by ring,
        abs_mul, abs_of_nonneg h_prod_nn]
    calc |expNumCubic φ a hφ t u| *
            (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))
        ≤ ((Real.sqrt t)⁻¹ / t * (‖hφ.Φ‖ / 6) * ‖u‖ ^ 3) *
            (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) := by
          apply mul_le_mul_of_nonneg_right h_cubic_le h_prod_nn
      _ = ((Real.sqrt t)⁻¹ / t * (‖hφ.Φ‖ / 6)) *
            (‖u‖ ^ 3 * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))) := by ring

/-- Integrability of `expNumLin a t u · gW(u) · exp(-(rescaledPerturbation V H t u))`. -/
private lemma integrable_expNumLin_mul_gW_mul_rescaled_weight
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV_cont : Continuous V)
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      expNumLin a t u * gaussianWeight H u
        * Real.exp (-(rescaledPerturbation V H t u))) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_dom_int : Integrable (fun u : ι → ℝ =>
      ((Real.sqrt t)⁻¹ * (∑ i, |a i|)) *
        (‖u‖ * (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))))) := by
    have := integrable_pow_norm_mul_rescaled_weight V hV_cont H hc_pos h_coer 1 ht
    simp only [pow_one] at this
    exact this.const_mul _
  apply h_dom_int.mono'
  · have h_dot_cont : Continuous (fun u : ι → ℝ => dot a u) := by
      unfold dot
      exact continuous_finset_sum _
        (fun i _ => continuous_const.mul (continuous_apply i))
    have h_lin_cont : Continuous (fun u : ι → ℝ => expNumLin a t u) := by
      unfold expNumLin
      exact continuous_const.mul h_dot_cont
    exact ((h_lin_cont.mul (continuous_gaussianWeight H)).mul
      (Real.continuous_exp.comp
        (continuous_rescaledPerturbation hV_cont H t).neg)).aestronglyMeasurable
  · filter_upwards with u
    have h_lin_le : |expNumLin a t u|
        ≤ ((Real.sqrt t)⁻¹ * (∑ i, |a i|)) * ‖u‖ := by
      unfold expNumLin
      rw [abs_mul, abs_of_pos (by positivity : 0 < (Real.sqrt t)⁻¹)]
      have h_dot_le : |dot a u| ≤ (∑ i, |a i|) * ‖u‖ := abs_dot_le_l1_mul_norm a u
      calc (Real.sqrt t)⁻¹ * |dot a u|
          ≤ (Real.sqrt t)⁻¹ * ((∑ i, |a i|) * ‖u‖) := by
            apply mul_le_mul_of_nonneg_left h_dot_le (by positivity)
        _ = ((Real.sqrt t)⁻¹ * (∑ i, |a i|)) * ‖u‖ := by ring
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    have h_exp_nn : 0 ≤ Real.exp (-(rescaledPerturbation V H t u)) :=
      (Real.exp_pos _).le
    have h_prod_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg h_gW_nn h_exp_nn
    rw [Real.norm_eq_abs]
    rw [show expNumLin a t u * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t u))
        = expNumLin a t u * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) from by ring,
        abs_mul, abs_of_nonneg h_prod_nn]
    calc |expNumLin a t u| *
            (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))
        ≤ (((Real.sqrt t)⁻¹ * (∑ i, |a i|)) * ‖u‖) *
            (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) :=
          mul_le_mul_of_nonneg_right h_lin_le h_prod_nn
      _ = ((Real.sqrt t)⁻¹ * (∑ i, |a i|)) *
            (‖u‖ * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))) := by ring

/-- Integrability of `expNumQuad φ a hφ t u · gW(u) · exp(-(rescaledPerturbation V H t u))`. -/
private lemma integrable_expNumQuad_mul_gW_mul_rescaled_weight
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV_cont : Continuous V)
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      expNumQuad φ a hφ t u * gaussianWeight H u
        * Real.exp (-(rescaledPerturbation V H t u))) := by
  have h_dom_int : Integrable (fun u : ι → ℝ =>
      ((1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖)) *
        (‖u‖ ^ 2 * (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))))) :=
    (integrable_pow_norm_mul_rescaled_weight V hV_cont H hc_pos h_coer 2 ht).const_mul _
  apply h_dom_int.mono'
  · have h_qf_cont : Continuous (fun u : ι → ℝ => quadForm hφ.A u) := by
      show Continuous (fun u : ι → ℝ => ∑ i, u i * (hφ.A u) i)
      refine continuous_finset_sum _ (fun i _ => ?_)
      exact (continuous_apply i).mul ((continuous_apply i).comp hφ.A.continuous)
    have h_quad_cont : Continuous (fun u : ι → ℝ => expNumQuad φ a hφ t u) := by
      unfold expNumQuad
      exact continuous_const.mul (continuous_const.mul h_qf_cont)
    exact ((h_quad_cont.mul (continuous_gaussianWeight H)).mul
      (Real.continuous_exp.comp
        (continuous_rescaledPerturbation hV_cont H t).neg)).aestronglyMeasurable
  · filter_upwards with u
    have h_qf_le : |quadForm hφ.A u| ≤ Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by
      unfold quadForm
      show |∑ i, u i * (hφ.A u) i| ≤ Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2
      have h_each : ∀ i, |u i * (hφ.A u) i| ≤ ‖u‖ * ‖hφ.A u‖ := fun i => by
        rw [abs_mul]
        apply mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm (hφ.A u) i)
          (abs_nonneg _) (norm_nonneg _)
      have h_sum_le : |∑ i, u i * (hφ.A u) i| ≤ ∑ i, |u i * (hφ.A u) i| :=
        Finset.abs_sum_le_sum_abs _ _
      have h_sum_le2 : ∑ i, |u i * (hφ.A u) i|
          ≤ Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := by
        calc ∑ i, |u i * (hφ.A u) i|
            ≤ ∑ _ : ι, ‖u‖ * ‖hφ.A u‖ := Finset.sum_le_sum (fun i _ => h_each i)
          _ = Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := by
                rw [Finset.sum_const, Finset.card_univ]; ring
      have h_Au : ‖hφ.A u‖ ≤ ‖hφ.A‖ * ‖u‖ := hφ.A.le_opNorm u
      calc |∑ i, u i * (hφ.A u) i|
          ≤ Fintype.card ι * (‖u‖ * ‖hφ.A u‖) := le_trans h_sum_le h_sum_le2
        _ ≤ Fintype.card ι * (‖u‖ * (‖hφ.A‖ * ‖u‖)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left h_Au (norm_nonneg _)
        _ = Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2 := by ring
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    have h_exp_nn : 0 ≤ Real.exp (-(rescaledPerturbation V H t u)) :=
      (Real.exp_pos _).le
    have h_prod_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg h_gW_nn h_exp_nn
    have h_quad_le : |expNumQuad φ a hφ t u|
        ≤ (1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖) * ‖u‖ ^ 2 := by
      unfold expNumQuad
      rw [show (1 / t : ℝ) * ((1/2 : ℝ) * quadForm hφ.A u)
            = (1 / t) * (1 / 2) * quadForm hφ.A u from by ring,
          abs_mul, abs_mul,
          abs_of_pos (by positivity : (0:ℝ) < 1/t),
          abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      calc (1 / t) * (1 / 2) * |quadForm hφ.A u|
          ≤ (1 / t) * (1 / 2) *
              (Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2) := by gcongr
        _ = (1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖) * ‖u‖ ^ 2 := by ring
    rw [Real.norm_eq_abs]
    rw [show expNumQuad φ a hφ t u * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t u))
        = expNumQuad φ a hφ t u * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) from by ring,
        abs_mul, abs_of_nonneg h_prod_nn]
    calc |expNumQuad φ a hφ t u| *
            (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))
        ≤ ((1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖) * ‖u‖ ^ 2) *
            (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) :=
          mul_le_mul_of_nonneg_right h_quad_le h_prod_nn
      _ = ((1 / t) * ((1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖)) *
            (‖u‖ ^ 2 * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))) := by ring

/-- Integrability of the J₃ integrand `L_t · gW · (exp(-s_t) - 1 + C_t)`. -/
private lemma integrable_J3_integrand
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      expNumLin a t u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1 + expPotCubic V H hV t u) *
        gaussianWeight H u) := by
  -- L_t · gW · (exp(-s_t) - 1 + C_t)
  -- = L_t · gW · exp(-s_t) - L_t · gW + L_t · C_t · gW.
  have h_coer : ∀ w : ι → ℝ, hV.coercive_const * ‖w‖ ^ 2 ≤ V w :=
    hV.coercive_bound
  have h_piece1 : Integrable (fun u : ι → ℝ =>
      expNumLin a t u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) :=
    integrable_expNumLin_mul_gW_mul_rescaled_weight V H a
      hV.V_continuous hV.coercive_const_pos h_coer ht
  have h_piece2 : Integrable (fun u : ι → ℝ =>
      expNumLin a t u * gaussianWeight H u) :=
    integrable_expNumLin_mul_gaussianWeight V H a hV.toPotentialJetApprox ht
  have h_piece3 : Integrable (fun u : ι → ℝ =>
      expNumLin a t u * expPotCubic V H hV t u * gaussianWeight H u) :=
    integrable_expNumLin_mul_expPotCubic_mul_gaussianWeight V H a hV ht
  have h_combine : Integrable (fun u : ι → ℝ =>
      expNumLin a t u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
      - expNumLin a t u * gaussianWeight H u
      + expNumLin a t u * expPotCubic V H hV t u * gaussianWeight H u) := by
    have := (h_piece1.sub h_piece2).add h_piece3
    convert this using 1
  apply h_combine.congr
  filter_upwards with u
  ring

/-- Integrability of the J₄ integrand `(Q_t - μ/t) · gW · (exp(-s_t) - 1)`. -/
private lemma integrable_J4_integrand
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1) *
        gaussianWeight H u) := by
  -- (Q_t - μ/t) · gW · (exp(-s_t) - 1)
  -- = Q_t · gW · exp(-s_t) - Q_t · gW - (μ/t) · gW · exp(-s_t) + (μ/t) · gW.
  -- Each piece is integrable.
  have h_coer : ∀ w : ι → ℝ, hV.coercive_const * ‖w‖ ^ 2 ≤ V w :=
    hV.coercive_bound
  -- Piece 1: Q_t · gW · exp(-s_t).
  have h_piece1 : Integrable (fun u : ι → ℝ =>
      expNumQuad φ a hφ t u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) :=
    integrable_expNumQuad_mul_gW_mul_rescaled_weight V φ H a
      hV.V_continuous hV.coercive_const_pos h_coer hφ ht
  -- Piece 2: Q_t · gW.
  have h_piece2 : Integrable (fun u : ι → ℝ =>
      expNumQuad φ a hφ t u * gaussianWeight H u) :=
    integrable_expNumQuad_mul_gaussianWeight V φ H a hV.toPotentialJetApprox hφ ht
  -- Piece 3: (μ/t) · gW · exp(-s_t).
  have h_piece3 : Integrable (fun u : ι → ℝ =>
      (expNumeratorCoeff V φ H Hinv a hV hφ / t) *
        (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))) := by
    have := integrable_pow_norm_mul_rescaled_weight V hV.V_continuous H
      hV.coercive_const_pos h_coer 0 ht
    simpa using this.const_mul _
  -- Piece 4: (μ/t) · gW.
  have h_piece4 : Integrable (fun u : ι → ℝ =>
      (expNumeratorCoeff V φ H Hinv a hV hφ / t) * gaussianWeight H u) := by
    have := (hV.int_norm_pow_gW 0).const_mul
      (expNumeratorCoeff V φ H Hinv a hV hφ / t)
    simpa using this
  -- Combine: integrand = piece1 - piece2 - piece3 + piece4.
  have h_combine : Integrable (fun u : ι → ℝ =>
      expNumQuad φ a hφ t u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
      - expNumQuad φ a hφ t u * gaussianWeight H u
      - (expNumeratorCoeff V φ H Hinv a hV hφ / t) *
          (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))
      + (expNumeratorCoeff V φ H Hinv a hV hφ / t) * gaussianWeight H u) := by
    have := ((h_piece1.sub h_piece2).sub h_piece3).add h_piece4
    convert this using 1
  apply h_combine.congr
  filter_upwards with u
  ring

/-- Integrability of the J₄ integrand with `-u` substituted in `s_t`:
`(Q_t(u) - μ/t) · gW(u) · (exp(-s_t(-u)) - 1)`.

This follows from `integrable_J4_integrand` via `Integrable.comp_neg`
(since the volume on `ι → ℝ` is `IsNegInvariant`), then using parity
(Q_t even, gW even) to swap `-u` for `u` in those factors. -/
private lemma integrable_J4_integrand_neg
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
        (Real.exp (-(rescaledPerturbation V H t (-u))) - 1) *
        gaussianWeight H u) := by
  have h_orig := integrable_J4_integrand V φ H Hinv a hV hφ ht
  -- f(-u) is integrable by Integrable.comp_neg.
  have h_neg := h_orig.comp_neg
  -- f(-u) = (Q_t(-u) - μ/t) · gW(-u) · (exp(-s_t(-u)) - 1).
  -- By parity: Q_t(-u) = Q_t(u), gW(-u) = gW(u).
  apply h_neg.congr
  filter_upwards with u
  rw [expNumQuad_neg, gaussianWeight_neg]

/-- Integrability of the J₃ symmetrized integrand
`L_t · gW · ((exp(-s_t(u)) - 1 + C_t(u)) - (exp(-s_t(-u)) - 1 + C_t(-u)))`.
Difference of the original and `-u`-substituted (after parity adjustment)
J_3 integrands. -/
private lemma integrable_J3_integrand_sym
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      expNumLin a t u *
        ((Real.exp (-(rescaledPerturbation V H t u)) - 1 + expPotCubic V H hV t u)
          - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
              + expPotCubic V H hV t (-u))) *
        gaussianWeight H u) := by
  have h_int_orig := integrable_J3_integrand V H a hV ht
  -- Derive integrability of the substituted version (with -u in s_t and C_t).
  have h_int_neg : Integrable (fun u : ι → ℝ =>
      expNumLin a t u *
        (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
            + expPotCubic V H hV t (-u)) *
        gaussianWeight H u) := by
    have h_int_orig_neg := h_int_orig.comp_neg
    -- J_3_integrand(-u) = -L_t(u)·(exp(-s_t(-u)) - 1 - C_t(u))·gW(u).
    have h_neg_int : Integrable (fun u : ι → ℝ =>
        -(expNumLin a t (-u) *
          (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
              + expPotCubic V H hV t (-u)) *
          gaussianWeight H (-u))) := h_int_orig_neg.neg
    apply h_neg_int.congr
    filter_upwards with u
    rw [expNumLin_neg, expPotCubic_neg, gaussianWeight_neg]
    ring
  -- Sum/difference structure: L_t · (R(u) - R(-u)) · gW = orig - neg.
  have h_combine : Integrable (fun u : ι → ℝ =>
      expNumLin a t u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1 + expPotCubic V H hV t u) *
        gaussianWeight H u -
      expNumLin a t u *
        (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
            + expPotCubic V H hV t (-u)) *
        gaussianWeight H u) := by
    have := h_int_orig.sub h_int_neg
    convert this using 1
  apply h_combine.congr
  filter_upwards with u
  ring

/-- Integrability of the J₄ symmetrized integrand
`(Q_t - μ/t) · gW · ((exp(-s_t(u)) - 1) + (exp(-s_t(-u)) - 1))`.
Sum of the original and `-u`-substituted J₄ integrands. -/
private lemma integrable_J4_integrand_sym
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
        ((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
          (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)) *
        gaussianWeight H u) := by
  have h_int_orig := integrable_J4_integrand V φ H Hinv a hV hφ ht
  have h_int_neg := integrable_J4_integrand_neg V φ H Hinv a hV hφ ht
  have h_sum : Integrable (fun u : ι → ℝ =>
      (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1) *
          gaussianWeight H u
        + (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
          (Real.exp (-(rescaledPerturbation V H t (-u))) - 1) *
          gaussianWeight H u) := by
    have := h_int_orig.add h_int_neg
    convert this using 1
  apply h_sum.congr
  filter_upwards with u
  ring

/-! ### The 4 error integrals -/

/-- `J₁ = ∫ R_{φ,t}(u) · exp(-s_t) · gW(u) du` — quartic observable remainder
against the full Gibbs factor. -/
private noncomputable def expNumErr₁
    (V φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hφ : ObservableTensorApprox φ a) (t : ℝ) : ℝ :=
  ∫ u : ι → ℝ, expNumObsRem φ a hφ t u
      * Real.exp (-(rescaledPerturbation V H t u))
      * gaussianWeight H u

/-- `J₂ = ∫ P_t(u) · (e^{-s_t} - 1) · gW(u) du` — cubic observable jet against
the perturbation residual. -/
private noncomputable def expNumErr₂
    (V φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hφ : ObservableTensorApprox φ a) (t : ℝ) : ℝ :=
  ∫ u : ι → ℝ, expNumCubic φ a hφ t u
      * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
      * gaussianWeight H u

/-- `J₃ = ∫ L_t(u) · (e^{-s_t} - 1 + C_t) · gW(u) du` — linear observable jet
against the odd remainder of the perturbation. -/
private noncomputable def expNumErr₃
    (V : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    (a : ι → ℝ) (t : ℝ) : ℝ :=
  ∫ u : ι → ℝ, expNumLin a t u
      * (Real.exp (-(rescaledPerturbation V H t u)) - 1 + expPotCubic V H hV t u)
      * gaussianWeight H u

/-- **J₃ symmetrization**: by `u ↦ -u` substitution (L_t flips sign,
gW invariant),

`2 · J₃ = ∫ L_t(u) · [(e^{-s_t(u)} + C_t(u)) - (e^{-s_t(-u)} + C_t(-u))] · gW(u) du`.

The bracket is the ODD part of `e^{-s_t(u)} - 1 + C_t(u)`. The leading
cubic-jet `C_t(u)` doubles in the difference (cubic = odd), giving
`exp(-s_t(u)) - exp(-s_t(-u)) + 2·C_t(u)`, which by Stage-1 + Stage-2 ≈
`-(s_t(u) - s_t(-u)) + 2·C_t(u) + O(s_t² · exp|s_t|)`.

The main term `s_t(u) - s_t(-u) = 2·C_t(u) + O(‖u‖⁴/t)` (from quartic `T_jet_bound`),
so the leading part of the bracket cancels modulo `O(‖u‖⁴/t)`. To get a
sharper `O(‖u‖⁵/t^(3/2))` bound (needed for the `O(t⁻²)` rate), the
QUINTIC bound from `PotentialQuinticApprox` is required. -/
private lemma expNumErr₃_symmetric
    (V : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    {t : ℝ} (ht : 0 < t) :
    2 * expNumErr₃ V H hV a t
      = ∫ u : ι → ℝ,
          expNumLin a t u *
            ((Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV t u)
              - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                  + expPotCubic V H hV t (-u))) *
            gaussianWeight H u := by
  unfold expNumErr₃
  -- Step 1: ∫ f(u) du = -∫ -f(-u) du = -∫ -L_t(u)·R(-u)·gW(u) du
  --       = ∫ L_t(u)·R(-u)·gW(u) du after rewriting with parity.
  -- Actually: ∫ f(u) du = ∫ f(-u) du by substitution. f(-u) = -L_t(u)·R(-u)·gW(u).
  have h_neg :
      (∫ u : ι → ℝ,
        expNumLin a t u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV t u) *
          gaussianWeight H u)
      = (∫ u : ι → ℝ,
          - (expNumLin a t u *
            (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                + expPotCubic V H hV t (-u)) *
            gaussianWeight H u)) := by
    have h_sub :=
      integral_pi_comp_neg
        (fun u : ι → ℝ =>
          expNumLin a t u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV t u) *
            gaussianWeight H u)
    rw [← h_sub]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [expNumLin_neg, gaussianWeight_neg]
    ring
  -- Step 2: 2·J₃ = J₃ + J₃ = ∫ f - (-∫ f) wait no...
  -- 2·J₃ = J₃ + J₃ = ∫f + ∫f = ∫f - (-∫f). And -∫f = ∫(-f(-u) under sub) = ∫(-(...))
  -- Actually: 2J₃ = J₃ + J₃ = J₃ - (-J₃). And from step 1, -J₃ = ∫(-(...))... hmm.
  -- Let me reformulate: 2·J₃ = J₃ + J₃, and using J₃ = -∫(−L_t·R(-u)·gW) (the negative
  -- of the substituted form), so J₃ = -(-J₃_neg) where J₃_neg := ∫ L_t(u)·R(-u)·gW(u).
  -- Hmm getting tangled. Let me just compute directly.
  have h_int_orig := integrable_J3_integrand V H a hV ht
  -- Integrability of J_3 with -u substituted: similar to J_4_integrand_neg.
  have h_int_neg : Integrable (fun u : ι → ℝ =>
      expNumLin a t u *
        (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
            + expPotCubic V H hV t (-u)) *
        gaussianWeight H u) := by
    have h_int_orig_neg := h_int_orig.comp_neg
    -- Note: J_3_integrand(-u) = -L_t(u)·(exp(-s_t(-u)) - 1 - C_t(u))·gW(u), so
    -- the integrand differs by a global sign from what we want. Negate.
    have h_neg_int : Integrable (fun u : ι → ℝ =>
        -(expNumLin a t (-u) *
          (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
              + expPotCubic V H hV t (-u)) *
          gaussianWeight H (-u))) := h_int_orig_neg.neg
    apply h_neg_int.congr
    filter_upwards with u
    rw [expNumLin_neg, expPotCubic_neg, gaussianWeight_neg]
    ring
  -- 2·J₃ = J₃ + J₃ = ∫ f - ∫ f_neg' where f_neg'(u) = -L_t(u)·R(-u)·gW(u) (from h_neg).
  have h_two_mul : (2 : ℝ) * (∫ u : ι → ℝ,
        expNumLin a t u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV t u) *
          gaussianWeight H u)
      = (∫ u : ι → ℝ,
          expNumLin a t u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV t u) *
            gaussianWeight H u)
        - (∫ u : ι → ℝ,
            expNumLin a t u *
              (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                  + expPotCubic V H hV t (-u)) *
              gaussianWeight H u) := by
    -- LHS = 2·J₃, RHS = J₃ - (-J₃) = J₃ + J₃ from h_neg.
    rw [show (∫ u : ι → ℝ,
            expNumLin a t u *
              (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                  + expPotCubic V H hV t (-u)) *
              gaussianWeight H u)
          = -(∫ u : ι → ℝ,
              expNumLin a t u *
                (Real.exp (-(rescaledPerturbation V H t u)) - 1
                    + expPotCubic V H hV t u) *
                gaussianWeight H u) from by
        conv_rhs => rw [h_neg]
        rw [← MeasureTheory.integral_neg]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        ring]
    ring
  rw [h_two_mul, ← MeasureTheory.integral_sub h_int_orig h_int_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  ring

/-- `J₄ = ∫ (Q_t(u) - μ/t) · (e^{-s_t} - 1) · gW(u) du` — centered quadratic
observable jet against the perturbation residual. -/
private noncomputable def expNumErr₄
    (V φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a) (t : ℝ) : ℝ :=
  ∫ u : ι → ℝ, (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t)
      * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
      * gaussianWeight H u

/-- **J₄ symmetrization**: by `u ↦ -u` substitution (preserves `Q_t`, `gW`),

`2 · J₄ = ∫ (Q_t(u) - μ/t) · [(e^{-s_t(u)} - 1) + (e^{-s_t(-u)} - 1)] · gW(u) du`.

The bracket is `2 · (even part of e^{-s_t(u)} - 1)`, with sharper local
decay (`O(‖u‖^4/t)` from `s_t(u) + s_t(-u) = O(‖u‖^4/t)`, since the cubic
piece in `s_t` cancels) — this is what makes J₄'s rate `O(t⁻²)` rather
than `O(t⁻³ᐟ²)`. -/
private lemma expNumErr₄_symmetric
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    {t : ℝ} (ht : 0 < t) :
    2 * expNumErr₄ V φ a H Hinv hV hφ t
      = ∫ u : ι → ℝ,
          (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
            ((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
              (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)) *
            gaussianWeight H u := by
  unfold expNumErr₄
  -- Step 1: ∫ f(u) du = ∫ f(-u) du (substitution), then use parity.
  have h_neg :
      (∫ u : ι → ℝ,
          (expNumQuad φ a hφ t u -
              expNumeratorCoeff V φ H Hinv a hV hφ / t) *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1) *
            gaussianWeight H u)
      = (∫ u : ι → ℝ,
            (expNumQuad φ a hφ t u -
              expNumeratorCoeff V φ H Hinv a hV hφ / t) *
            (Real.exp (-(rescaledPerturbation V H t (-u))) - 1) *
            gaussianWeight H u) := by
    have h_sub :=
      integral_pi_comp_neg
        (fun u : ι → ℝ =>
          (expNumQuad φ a hφ t u -
              expNumeratorCoeff V φ H Hinv a hV hφ / t) *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1) *
            gaussianWeight H u)
    rw [← h_sub]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [expNumQuad_neg, gaussianWeight_neg]
  -- Step 2: 2·J₄ = J₄ + J₄_neg = ∫ (f + f_neg).
  have h_int_orig := integrable_J4_integrand V φ H Hinv a hV hφ ht
  have h_int_neg := integrable_J4_integrand_neg V φ H Hinv a hV hφ ht
  have h_two_mul : (2 : ℝ) * (∫ u : ι → ℝ,
        (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t)
          * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
          * gaussianWeight H u)
      = (∫ u : ι → ℝ,
          (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t)
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u)
        + (∫ u : ι → ℝ,
          (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t)
            * (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)
            * gaussianWeight H u) := by
    rw [← h_neg]; ring
  rw [h_two_mul, ← MeasureTheory.integral_add h_int_orig h_int_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  ring

/-! ### Decomposition + 4 bounds -/

/-- **Gaussian background identity** (Wick algebra step in the decomposition):

`∫ [-L_t - Q_t - P_t + L_t·C_t + μ/t] · gW du = 0`

where `L_t, Q_t, P_t, C_t, μ` are the standard scaled jets and the explicit
coefficient. This is the algebraic identity that makes the centered-numerator
decomposition close: the Gaussian background of the linear+quadratic+cubic
jets cancels the `μ/t` correction.

Proof: oddness for L_t, P_t (linear/cubic against even gW vanish);
`gaussian_quad_expectation` for Q_t; `gaussian_linear_cubic` for L_t·C_t;
and the algebraic identity `2μ = trASig - dot(Hinv a)(T:Σ)`. -/
private lemma expNumerator_gaussian_background_eq_zero
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv)
    {t : ℝ} (ht : 0 < t) :
    (∫ u : ι → ℝ, expNumLin a t u * gaussianWeight H u)
      + (∫ u : ι → ℝ, expNumQuad φ a hφ t u * gaussianWeight H u)
      + (∫ u : ι → ℝ, expNumCubic φ a hφ t u * gaussianWeight H u)
      - expNumeratorCoeff V φ H Hinv a hV hφ / t *
          (∫ u : ι → ℝ, gaussianWeight H u)
      - (∫ u : ι → ℝ, expNumLin a t u * expPotCubic V H hV t u
          * gaussianWeight H u)
      = 0 := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  -- ∫ L_t · gW = (√t)⁻¹ · ∫ ⟨a,u⟩ · gW = 0.
  have h_L_zero : ∫ u : ι → ℝ, expNumLin a t u * gaussianWeight H u = 0 := by
    have h_eq : (fun u : ι → ℝ => expNumLin a t u * gaussianWeight H u)
        = (fun u => (Real.sqrt t)⁻¹ * (dot a u * gaussianWeight H u)) := by
      funext u; unfold expNumLin; ring
    rw [h_eq, integral_const_mul]
    rw [integral_dot_mul_gaussianWeight_eq_zero]
    ring
  -- ∫ Q_t · gW = (1/t) · gaussianZ · (1/2) · trASig.
  have h_Q_eval : ∫ u : ι → ℝ, expNumQuad φ a hφ t u * gaussianWeight H u
      = (1 / t) * (gaussianZ H * (1 / 2 : ℝ) * trASig hφ.A Hinv) := by
    have h_eq : (fun u : ι → ℝ => expNumQuad φ a hφ t u * gaussianWeight H u)
        = (fun u => (1 / t) *
            ((1 / 2 : ℝ) * quadForm hφ.A u * gaussianWeight H u)) := by
      funext u; unfold expNumQuad; ring
    rw [h_eq, integral_const_mul]
    rw [gaussian_quad_expectation hφ.A hφ.A_symm hGauss.toLaplaceCovHypotheses]
  -- ∫ P_t · gW = 0 (oddness).
  have h_P_zero : ∫ u : ι → ℝ, expNumCubic φ a hφ t u * gaussianWeight H u = 0 := by
    have h_eq : (fun u : ι → ℝ => expNumCubic φ a hφ t u * gaussianWeight H u)
        = (fun u => ((Real.sqrt t)⁻¹ / t * (1 / 6 : ℝ)) *
            (hφ.Φ (fun _ => u) * gaussianWeight H u)) := by
      funext u; unfold expNumCubic; ring
    rw [h_eq, integral_const_mul]
    rw [integral_cmm_diag_mul_gaussianWeight_eq_zero H hφ.Φ]
    ring
  -- ∫ L_t · C_t · gW = ((√t)⁻¹·(√t)⁻¹·(1/6)) · ∫ ⟨a,u⟩ · T(u,u,u) · gW
  --                  = (1/(6t)) · gaussianZ · 3 · dot(Hinv a)(T:Σ)
  --                  = (Z/(2t)) · dot(Hinv a)(T:Σ).
  have h_LC_eval : ∫ u : ι → ℝ, expNumLin a t u * expPotCubic V H hV t u
                       * gaussianWeight H u
      = (1 / (2 * t)) * (gaussianZ H *
          dot (Hinv a) (tensorContractMatrix hV.T Hinv)) := by
    have h_sqrt_inv_sq : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = 1 / t := by
      rw [show (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹
            = ((Real.sqrt t) * (Real.sqrt t))⁻¹ from by rw [mul_inv]]
      rw [Real.mul_self_sqrt ht.le]
      rw [one_div]
    have h_eq : (fun u : ι → ℝ => expNumLin a t u * expPotCubic V H hV t u
                * gaussianWeight H u)
        = (fun u => ((Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * (1 / 6 : ℝ)) *
            (dot a u * hV.T (fun _ => u) * gaussianWeight H u)) := by
      funext u; unfold expNumLin expPotCubic; ring
    rw [h_eq, integral_const_mul]
    rw [gaussian_linear_cubic a hV.T hV.T_symm hGauss]
    rw [h_sqrt_inv_sq]
    field_simp
    ring
  -- ∫ gW = gaussianZ (definitional).
  have h_gW_eval : ∫ u : ι → ℝ, gaussianWeight H u = gaussianZ H := rfl
  -- Combine: 0 + (1/(2t))·Z·trASig + 0 - (μ/t)·Z - (Z/(2t))·dot = 0.
  rw [h_L_zero, h_Q_eval, h_P_zero, h_LC_eval, h_gW_eval]
  -- Goal: 0 + (1/t)·(Z·(1/2)·trASig) + 0 - (μ/t)·Z - (1/(2t))·(Z·dot) = 0.
  -- With μ = (trASig - dot)/2.
  unfold expNumeratorCoeff
  ring

/-- **Centered numerator decomposition**: the EXP analogue of the COV
`pair_product_expansion`. Decomposes the centered numerator as a sum of
the 4 helper integrals, with the Gaussian main terms
`(-L_t - Q_t - P_t + L_t·C_t + μ/t)` integrating to zero by oddness +
`gaussian_quad_expectation` + `gaussian_linear_cubic`. -/
private lemma expNumerator_centered_decomp
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv)
    {t : ℝ} (ht : 0 < t) :
    rescaledNumerator V t φ
      - rescaledPartition V t * (expNumeratorCoeff V φ H Hinv a hV hφ / t)
      = expNumErr₁ V φ a H hφ t
        + expNumErr₂ V φ a H hφ t
        + expNumErr₃ V H hV a t
        + expNumErr₄ V φ a H Hinv hV hφ t := by
  -- Setup.
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hinv_sqrt_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hsqrt_pos
  have hc_pos : 0 < hV.coercive_const := hV.coercive_const_pos
  have h_coer : ∀ w : ι → ℝ, hV.coercive_const * ‖w‖ ^ 2 ≤ V w := hV.coercive_bound
  set μ_const : ℝ := expNumeratorCoeff V φ H Hinv a hV hφ / t with hμ_def
  -- Common integrabilities.
  have h_rw_int : Integrable (fun u : ι → ℝ =>
      gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) := by
    have := integrable_pow_norm_mul_rescaled_weight V hV.V_continuous H hc_pos h_coer 0 ht
    simpa using this
  have h_L_e : Integrable (fun u : ι → ℝ =>
      expNumLin a t u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) :=
    integrable_expNumLin_mul_gW_mul_rescaled_weight V H a
      hV.V_continuous hc_pos h_coer ht
  have h_Q_e : Integrable (fun u : ι → ℝ =>
      expNumQuad φ a hφ t u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) :=
    integrable_expNumQuad_mul_gW_mul_rescaled_weight V φ H a
      hV.V_continuous hc_pos h_coer hφ ht
  have h_P_e : Integrable (fun u : ι → ℝ =>
      expNumCubic φ a hφ t u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) :=
    integrable_expNumCubic_mul_gW_mul_rescaled_weight V φ H a
      hV.V_continuous hc_pos h_coer hφ ht
  have h_L_gW : Integrable (fun u : ι → ℝ => expNumLin a t u * gaussianWeight H u) :=
    integrable_expNumLin_mul_gaussianWeight V H a hV.toPotentialJetApprox ht
  have h_Q_gW : Integrable (fun u : ι → ℝ => expNumQuad φ a hφ t u * gaussianWeight H u) :=
    integrable_expNumQuad_mul_gaussianWeight V φ H a hV.toPotentialJetApprox hφ ht
  have h_P_gW : Integrable (fun u : ι → ℝ => expNumCubic φ a hφ t u * gaussianWeight H u) :=
    integrable_expNumCubic_mul_gaussianWeight V φ H a hV.toPotentialJetApprox hφ ht
  have h_LC_gW : Integrable (fun u : ι → ℝ =>
      expNumLin a t u * expPotCubic V H hV t u * gaussianWeight H u) :=
    integrable_expNumLin_mul_expPotCubic_mul_gaussianWeight V H a hV ht
  -- Constant times rescaled weight.
  have h_const_e : Integrable (fun u : ι → ℝ =>
      μ_const * (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))) :=
    h_rw_int.const_mul μ_const
  -- φ((√t)⁻¹·u) · gW · exp(-s_t) integrability via polynomial growth dominator.
  obtain ⟨Kφ, p, hKφ_nn, hpoly⟩ := hφ.toObservableApprox.poly_growth
  have h_phi_cont : Continuous (fun u : ι → ℝ => φ ((Real.sqrt t)⁻¹ • u)) :=
    hφ.toObservableApprox.phi_continuous.comp
      (continuous_const.smul continuous_id)
  have h_rw_cont : Continuous (fun u : ι → ℝ =>
      gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) :=
    (continuous_gaussianWeight H).mul (Real.continuous_exp.comp
      (continuous_rescaledPerturbation hV.V_continuous H t).neg)
  have h_phi_e : Integrable (fun u : ι → ℝ =>
      φ ((Real.sqrt t)⁻¹ • u) *
        (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))) := by
    -- Dominate by `Kφ · ((√t)⁻ᵖ · ‖u‖^p · exp(-c‖u‖²) + exp(-c‖u‖²))`.
    set Cinv_p : ℝ := ((Real.sqrt t)⁻¹) ^ p with hCinv_def
    have hCinv_nn : 0 ≤ Cinv_p := by rw [hCinv_def]; positivity
    have h0 := integrable_exp_neg_const_norm_sq (ι := ι) hc_pos
    have hpInt := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos p
    have h_dom : Integrable (fun u : ι → ℝ =>
        Kφ * (Real.exp (-(hV.coercive_const * ‖u‖ ^ 2)) +
          Cinv_p * (‖u‖ ^ p * Real.exp (-(hV.coercive_const * ‖u‖ ^ 2))))) :=
      (h0.add (hpInt.const_mul Cinv_p)).const_mul Kφ
    refine h_dom.mono' ?_ ?_
    · exact (h_phi_cont.mul h_rw_cont).aestronglyMeasurable
    · filter_upwards with u
      have h_phi_le : |φ ((Real.sqrt t)⁻¹ • u)|
          ≤ Kφ * (1 + ‖(Real.sqrt t)⁻¹ • u‖ ^ p) := hpoly _
      have h_norm_sm : ‖(Real.sqrt t)⁻¹ • u‖ = (Real.sqrt t)⁻¹ * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv_sqrt_pos]
      have h_norm_sm_p : ‖(Real.sqrt t)⁻¹ • u‖ ^ p = Cinv_p * ‖u‖ ^ p := by
        rw [h_norm_sm, mul_pow]
      have h_phi_le' : |φ ((Real.sqrt t)⁻¹ • u)|
          ≤ Kφ * (1 + Cinv_p * ‖u‖ ^ p) := by
        rw [← h_norm_sm_p]; exact h_phi_le
      have h_rw_nn : 0 ≤ gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)) :=
        mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
      have h_rw_le : gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
          ≤ Real.exp (-(hV.coercive_const * ‖u‖ ^ 2)) :=
        rescaled_weight_le_coercive V H hc_pos h_coer ht u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_rw_nn]
      calc |φ ((Real.sqrt t)⁻¹ • u)| * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
          ≤ Kφ * (1 + Cinv_p * ‖u‖ ^ p) * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) :=
            mul_le_mul_of_nonneg_right h_phi_le' h_rw_nn
        _ ≤ Kφ * (1 + Cinv_p * ‖u‖ ^ p) *
              Real.exp (-(hV.coercive_const * ‖u‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h_rw_le
              (mul_nonneg hKφ_nn (by positivity))
        _ = Kφ * (Real.exp (-(hV.coercive_const * ‖u‖ ^ 2)) +
            Cinv_p * (‖u‖ ^ p * Real.exp (-(hV.coercive_const * ‖u‖ ^ 2)))) := by
            ring
  -- Step A: rewrite LHS as ∫ (φ((√t)⁻¹·u) - μ_const) · gW · exp(-s_t).
  have h_LHS : rescaledNumerator V t φ - rescaledPartition V t * μ_const
      = ∫ u : ι → ℝ,
          (φ ((Real.sqrt t)⁻¹ • u) - μ_const) *
          (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) := by
    rw [rescaledNumerator_eq_gaussian_form V φ H t,
        rescaledPartition_eq_gaussian_form V H t,
        mul_comm (∫ u : ι → ℝ, gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) μ_const,
        ← integral_const_mul]
    rw [show (∫ u : ι → ℝ, φ ((Real.sqrt t)⁻¹ • u) *
            gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))
          = ∫ u : ι → ℝ, φ ((Real.sqrt t)⁻¹ • u) *
            (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) from by
        apply MeasureTheory.integral_congr_ae; filter_upwards with u; ring]
    rw [← MeasureTheory.integral_sub h_phi_e h_const_e]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    ring
  -- Step B: pointwise identity for the integrand.
  -- (φ((√t)⁻¹·u) - μ_const) · gW · e
  -- = R·e·gW + P_t·(e-1)·gW + L_t·(e-1+C_t)·gW + (Q_t-μ_const)·(e-1)·gW
  --   + (L_t + Q_t + P_t - L_t·C_t - μ_const)·gW
  -- (algebraic identity using R = φ((√t)⁻¹·u) - L_t - Q_t - P_t).
  have h_pointwise : ∀ u : ι → ℝ,
      (φ ((Real.sqrt t)⁻¹ • u) - μ_const) *
        (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))
      = (expNumObsRem φ a hφ t u
            * Real.exp (-(rescaledPerturbation V H t u))
            * gaussianWeight H u)
        + (expNumCubic φ a hφ t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u)
        + (expNumLin a t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV t u)
            * gaussianWeight H u)
        + ((expNumQuad φ a hφ t u - μ_const)
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u)
        + ((expNumLin a t u + expNumQuad φ a hφ t u + expNumCubic φ a hφ t u
              - expNumLin a t u * expPotCubic V H hV t u - μ_const)
            * gaussianWeight H u) := by
    intro u
    -- Unfold expNumObsRem to get φ((√t)⁻¹·u) - L_t - Q_t - P_t.
    unfold expNumObsRem
    ring
  -- Step C: integrate the right-hand side. Each piece is integrable.
  have h_J1_int : Integrable (fun u : ι → ℝ =>
      expNumObsRem φ a hφ t u
        * Real.exp (-(rescaledPerturbation V H t u))
        * gaussianWeight H u) := by
    -- R·e·gW = (φ - L_t - Q_t - P_t)·e·gW = φ·e·gW - L_t·e·gW - Q_t·e·gW - P_t·e·gW.
    have h_combine : Integrable (fun u : ι → ℝ =>
        φ ((Real.sqrt t)⁻¹ • u) *
          (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))
        - expNumLin a t u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
        - expNumQuad φ a hφ t u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
        - expNumCubic φ a hφ t u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) :=
      ((h_phi_e.sub h_L_e).sub h_Q_e).sub h_P_e
    apply h_combine.congr
    filter_upwards with u
    unfold expNumObsRem
    ring
  have h_J2_int : Integrable (fun u : ι → ℝ =>
      expNumCubic φ a hφ t u
        * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
        * gaussianWeight H u) := by
    -- P_t·(e-1)·gW = P_t·gW·e - P_t·gW.
    have h_combine : Integrable (fun u : ι → ℝ =>
        expNumCubic φ a hφ t u * gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
        - expNumCubic φ a hφ t u * gaussianWeight H u) := h_P_e.sub h_P_gW
    apply h_combine.congr
    filter_upwards with u
    show expNumCubic φ a hφ t u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
          - expNumCubic φ a hφ t u * gaussianWeight H u
        = expNumCubic φ a hφ t u
          * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
          * gaussianWeight H u
    ring
  have h_J3_int := integrable_J3_integrand V H a hV ht
  have h_J4_int := integrable_J4_integrand V φ H Hinv a hV hφ ht
  -- bg integrand integrability.
  have h_const_gW : Integrable (fun u : ι → ℝ =>
      μ_const * gaussianWeight H u) := by
    have := (hV.int_norm_pow_gW 0).const_mul μ_const
    simpa using this
  have h_bg_int : Integrable (fun u : ι → ℝ =>
      (expNumLin a t u + expNumQuad φ a hφ t u + expNumCubic φ a hφ t u
        - expNumLin a t u * expPotCubic V H hV t u - μ_const)
        * gaussianWeight H u) := by
    -- = L_t·gW + Q_t·gW + P_t·gW - L_t·C_t·gW - μ·gW.
    have h_combine : Integrable (fun u : ι → ℝ =>
        expNumLin a t u * gaussianWeight H u
          + expNumQuad φ a hφ t u * gaussianWeight H u
          + expNumCubic φ a hφ t u * gaussianWeight H u
        - expNumLin a t u * expPotCubic V H hV t u * gaussianWeight H u
        - μ_const * gaussianWeight H u) :=
      (((h_L_gW.add h_Q_gW).add h_P_gW).sub h_LC_gW).sub h_const_gW
    apply h_combine.congr
    filter_upwards with u
    show expNumLin a t u * gaussianWeight H u
          + expNumQuad φ a hφ t u * gaussianWeight H u
          + expNumCubic φ a hφ t u * gaussianWeight H u
        - expNumLin a t u * expPotCubic V H hV t u * gaussianWeight H u
        - μ_const * gaussianWeight H u
        = (expNumLin a t u + expNumQuad φ a hφ t u + expNumCubic φ a hφ t u
            - expNumLin a t u * expPotCubic V H hV t u - μ_const)
          * gaussianWeight H u
    ring
  -- Use h_LHS and integrate the pointwise identity.
  rw [hμ_def] at h_LHS
  rw [hμ_def]
  rw [h_LHS]
  -- Sum of integrals = integral of sum (chain).
  -- Use integral_congr_ae with the pointwise identity, then split.
  have h_int_sum : ∫ u : ι → ℝ,
      (φ ((Real.sqrt t)⁻¹ • u) - μ_const) *
        (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))
      = (∫ u : ι → ℝ, expNumObsRem φ a hφ t u
            * Real.exp (-(rescaledPerturbation V H t u))
            * gaussianWeight H u)
        + (∫ u : ι → ℝ, expNumCubic φ a hφ t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u)
        + (∫ u : ι → ℝ, expNumLin a t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV t u)
            * gaussianWeight H u)
        + (∫ u : ι → ℝ, (expNumQuad φ a hφ t u - μ_const)
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u)
        + (∫ u : ι → ℝ,
            (expNumLin a t u + expNumQuad φ a hφ t u + expNumCubic φ a hφ t u
              - expNumLin a t u * expPotCubic V H hV t u - μ_const)
            * gaussianWeight H u) := by
    rw [show
      (fun u : ι → ℝ =>
        (φ ((Real.sqrt t)⁻¹ • u) - μ_const) *
          (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))))
      = (fun u : ι → ℝ =>
        (expNumObsRem φ a hφ t u
            * Real.exp (-(rescaledPerturbation V H t u))
            * gaussianWeight H u)
          + (expNumCubic φ a hφ t u
              * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
              * gaussianWeight H u)
          + (expNumLin a t u
              * (Real.exp (-(rescaledPerturbation V H t u)) - 1
                  + expPotCubic V H hV t u)
              * gaussianWeight H u)
          + ((expNumQuad φ a hφ t u - μ_const)
              * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
              * gaussianWeight H u)
          + ((expNumLin a t u + expNumQuad φ a hφ t u + expNumCubic φ a hφ t u
                - expNumLin a t u * expPotCubic V H hV t u - μ_const)
              * gaussianWeight H u))
      from by funext u; exact h_pointwise u]
    -- Single-lambda integrability witnesses for integral_add chain.
    have h_J12 : Integrable (fun u : ι → ℝ =>
        expNumObsRem φ a hφ t u * Real.exp (-(rescaledPerturbation V H t u))
            * gaussianWeight H u
        + expNumCubic φ a hφ t u * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u) := h_J1_int.add h_J2_int
    have h_J123 : Integrable (fun u : ι → ℝ =>
        (expNumObsRem φ a hφ t u * Real.exp (-(rescaledPerturbation V H t u))
            * gaussianWeight H u
          + expNumCubic φ a hφ t u * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
              * gaussianWeight H u)
        + expNumLin a t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV t u)
            * gaussianWeight H u) := h_J12.add h_J3_int
    have h_J1234 : Integrable (fun u : ι → ℝ =>
        ((expNumObsRem φ a hφ t u * Real.exp (-(rescaledPerturbation V H t u))
            * gaussianWeight H u
          + expNumCubic φ a hφ t u * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
              * gaussianWeight H u)
          + expNumLin a t u
              * (Real.exp (-(rescaledPerturbation V H t u)) - 1
                  + expPotCubic V H hV t u)
              * gaussianWeight H u)
        + (expNumQuad φ a hφ t u - μ_const)
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u) := h_J123.add h_J4_int
    rw [MeasureTheory.integral_add h_J1234 h_bg_int]
    rw [MeasureTheory.integral_add h_J123 h_J4_int]
    rw [MeasureTheory.integral_add h_J12 h_J3_int]
    rw [MeasureTheory.integral_add h_J1_int h_J2_int]
  rw [h_int_sum]
  -- Each ∫ Jᵢ_int = expNumErrᵢ by definition.
  unfold expNumErr₁ expNumErr₂ expNumErr₃ expNumErr₄
  -- bg integral = 0 by background lemma.
  have h_bg_eq : ∫ u : ι → ℝ,
      (expNumLin a t u + expNumQuad φ a hφ t u + expNumCubic φ a hφ t u
        - expNumLin a t u * expPotCubic V H hV t u - μ_const)
        * gaussianWeight H u
      = 0 := by
    -- bg·gW = (L_t + Q_t + P_t - L_t·C_t - μ_const)·gW.
    -- = L_t·gW + Q_t·gW + P_t·gW - L_t·C_t·gW - μ_const·gW.
    -- ∫ each integrable, sum = (lemma's expression).
    have h_split : ∫ u : ι → ℝ,
        (expNumLin a t u + expNumQuad φ a hφ t u + expNumCubic φ a hφ t u
          - expNumLin a t u * expPotCubic V H hV t u - μ_const)
          * gaussianWeight H u
        = (∫ u, expNumLin a t u * gaussianWeight H u)
          + (∫ u, expNumQuad φ a hφ t u * gaussianWeight H u)
          + (∫ u, expNumCubic φ a hφ t u * gaussianWeight H u)
          - (∫ u, expNumLin a t u * expPotCubic V H hV t u * gaussianWeight H u)
          - (∫ u, μ_const * gaussianWeight H u) := by
      rw [show (fun u : ι → ℝ =>
          (expNumLin a t u + expNumQuad φ a hφ t u + expNumCubic φ a hφ t u
            - expNumLin a t u * expPotCubic V H hV t u - μ_const)
            * gaussianWeight H u)
        = (fun u : ι → ℝ =>
          ((expNumLin a t u * gaussianWeight H u
              + expNumQuad φ a hφ t u * gaussianWeight H u)
            + expNumCubic φ a hφ t u * gaussianWeight H u)
          - expNumLin a t u * expPotCubic V H hV t u * gaussianWeight H u
          - μ_const * gaussianWeight H u) from by funext u; ring]
      -- Single-lambda integrability witnesses for the integral_add/sub chain.
      have h_LQ : Integrable (fun u : ι → ℝ =>
          expNumLin a t u * gaussianWeight H u
          + expNumQuad φ a hφ t u * gaussianWeight H u) := h_L_gW.add h_Q_gW
      have h_LQP : Integrable (fun u : ι → ℝ =>
          (expNumLin a t u * gaussianWeight H u
            + expNumQuad φ a hφ t u * gaussianWeight H u)
          + expNumCubic φ a hφ t u * gaussianWeight H u) := h_LQ.add h_P_gW
      have h_LQP_LC : Integrable (fun u : ι → ℝ =>
          ((expNumLin a t u * gaussianWeight H u
            + expNumQuad φ a hφ t u * gaussianWeight H u)
          + expNumCubic φ a hφ t u * gaussianWeight H u)
          - expNumLin a t u * expPotCubic V H hV t u * gaussianWeight H u) :=
        h_LQP.sub h_LC_gW
      rw [MeasureTheory.integral_sub h_LQP_LC h_const_gW]
      rw [MeasureTheory.integral_sub h_LQP h_LC_gW]
      rw [MeasureTheory.integral_add h_LQ h_P_gW]
      rw [MeasureTheory.integral_add h_L_gW h_Q_gW]
    rw [h_split]
    -- Simplify ∫ μ_const · gW = μ_const · ∫ gW.
    rw [show ∫ u : ι → ℝ, μ_const * gaussianWeight H u
          = μ_const * ∫ u : ι → ℝ, gaussianWeight H u from
        integral_const_mul _ _]
    -- Apply background lemma.
    have h_bg_lemma := expNumerator_gaussian_background_eq_zero
      V φ H Hinv a hV hφ hGauss ht
    rw [hμ_def]
    linarith [h_bg_lemma]
  rw [h_bg_eq]
  ring

/-- **J₁ bound**: quartic observable remainder × full Gibbs factor is `O(t⁻²)`.

Proof: unified Glocal+Gtail majorant via the "absorption trick" from
`abs_integral_remainder_remainder_sharp_le` (CovarianceSharp.lean):
- Local (`‖u‖ ≤ jet_R·√t`): `|R| ≤ jet_C·‖u‖⁴/t²` (sharp).
- Tail (`‖u‖ > jet_R·√t`): use `1 ≤ ‖u‖⁴/(jet_R⁴·t²)` to absorb the
  global polynomial bound into a `1/t²` factor.

Both pieces combine into a single majorant `(const/t²) · ‖u‖⁴·(1 + ‖u‖^N) ·
exp(-c·‖u‖²)`, which is t-independent up to the `1/t²` prefactor and
integrable via `integrable_norm_pow_mul_exp_neg_const_sq`. -/
private lemma expNumErr₁_bound
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₁ V φ a H hφ t| ≤ K / t ^ 2 := by
  -- Extract constants.
  set c : ℝ := hV.coercive_const with hc_def
  have hc_pos : 0 < c := hV.coercive_const_pos
  have h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w := hV.coercive_bound
  set jet_R : ℝ := hφ.jet_radius with hjet_R_def
  have hjet_R_pos : 0 < jet_R := hφ.jet_radius_pos
  set jet_C : ℝ := hφ.jet_const with hjet_C_def
  have hjet_C_nn : 0 ≤ jet_C := hφ.jet_const_nonneg
  obtain ⟨Kφ, p, hKφ_nn, hpoly⟩ := hφ.toObservableApprox.poly_growth
  -- Polynomial degree N for the tail majorant; we need N ≥ p (so all four
  -- pieces of the polynomial bound are dominated by `1 + ‖u‖^N`).
  set N : ℕ := max p 3 with hN_def
  -- Polynomial constant: combines the four pieces of the global bound.
  -- The factor 2 in front of Kφ accounts for the (1 + ‖u‖^p) ≤ 2·(1 + ‖u‖^N)
  -- absorption.
  set C_glob : ℝ :=
    2 * Kφ + (∑ i, |a i|) + (1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖
      + ‖hφ.Φ‖ / 6 with hC_glob_def
  have hC_glob_nn : 0 ≤ C_glob := by rw [hC_glob_def]; positivity
  -- Gaussian moment for the unified majorant.
  set M : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) *
    Real.exp (-(c * ‖u‖ ^ 2)) with hM_def
  have hM_int : Integrable (fun u : ι → ℝ =>
      ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) * Real.exp (-(c * ‖u‖ ^ 2))) := by
    have h4 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos 4
    have h4N := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos (4 + N)
    have h_sum := h4.add h4N
    convert h_sum using 1
    funext u
    rw [show ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) * Real.exp (-(c * ‖u‖ ^ 2))
          = ‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2))
            + ‖u‖ ^ (4 + N) * Real.exp (-(c * ‖u‖ ^ 2)) from by
        rw [show ‖u‖ ^ (4 + N) = ‖u‖ ^ 4 * ‖u‖ ^ N from by rw [pow_add]]
        ring]
    rfl
  have hM_nn : 0 ≤ M := by
    rw [hM_def]
    apply MeasureTheory.integral_nonneg
    intro u; positivity
  -- Tail-absorption constant: when ‖u‖ > jet_R·√t, ‖u‖⁴/t² ≥ jet_R⁴.
  -- So the global bound `C_glob · (1 + ‖u‖^N)` ≤ (C_glob / jet_R⁴) · ‖u‖⁴/t² · (1+‖u‖^N).
  set C_tail_factor : ℝ := C_glob / jet_R ^ 4 with hC_tail_factor_def
  have hC_tail_factor_nn : 0 ≤ C_tail_factor := by
    rw [hC_tail_factor_def]; positivity
  -- The combined majorant constant: max(jet_C, C_tail_factor) for unified prefactor.
  -- Sum form (since both pieces are nonneg, sum dominates max).
  set K : ℝ := (jet_C + C_tail_factor) * M with hK_def
  refine ⟨K, 1, le_refl _, ?_⟩
  intro t ht1
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have ht_sq_pos : 0 < t ^ 2 := pow_pos ht_pos 2
  -- Define the unified majorant.
  set G : (ι → ℝ) → ℝ := fun u =>
    ((jet_C + C_tail_factor) / t ^ 2) * ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) *
      Real.exp (-(c * ‖u‖ ^ 2)) with hG_def
  have hG_nn : ∀ u, 0 ≤ G u := by
    intro u; rw [hG_def]; positivity
  have hG_int : Integrable G := by
    rw [hG_def]
    have := hM_int.const_mul ((jet_C + C_tail_factor) / t ^ 2)
    convert this using 1; funext u; ring
  -- Pointwise bound.
  have h_pointwise : ∀ u : ι → ℝ,
      ‖expNumObsRem φ a hφ t u
        * Real.exp (-(rescaledPerturbation V H t u))
        * gaussianWeight H u‖ ≤ G u := by
    intro u
    rw [Real.norm_eq_abs]
    have h_gibbs_le : gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
        ≤ Real.exp (-(c * ‖u‖ ^ 2)) :=
      rescaled_weight_le_coercive V H hc_pos h_coer ht_pos u
    have h_gibbs_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
    rw [show expNumObsRem φ a hφ t u
          * Real.exp (-(rescaledPerturbation V H t u))
          * gaussianWeight H u
        = expNumObsRem φ a hφ t u *
          (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) from by ring,
        abs_mul, abs_of_nonneg h_gibbs_nn]
    -- Pointwise: |R| ≤ ((jet_C + C_tail_factor) / t²) · ‖u‖⁴ · (1 + ‖u‖^N).
    have h_R_ptw : |expNumObsRem φ a hφ t u|
        ≤ ((jet_C + C_tail_factor) / t ^ 2) * ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) := by
      by_cases hu : ‖u‖ ≤ jet_R * Real.sqrt t
      · -- Local: use sharp bound; the remaining factors absorb.
        have h_loc :=
          abs_expNumObsRem_local_le (φ := φ) (a := a) hφ ht_pos u (by
            show ‖u‖ ≤ hφ.jet_radius * Real.sqrt t
            exact hu)
        have h_loc' : |expNumObsRem φ a hφ t u| ≤ jet_C * ‖u‖ ^ 4 / t ^ 2 := by
          rw [hjet_C_def]; exact h_loc
        have h_pow_N_nn : 0 ≤ ‖u‖ ^ N := pow_nonneg (norm_nonneg _) _
        have h_C_tail_nn : 0 ≤ C_tail_factor := hC_tail_factor_nn
        have h_jet_C_nn : 0 ≤ jet_C := hjet_C_nn
        have h_norm_pow_nn : 0 ≤ ‖u‖ ^ 4 := pow_nonneg (norm_nonneg _) _
        calc |expNumObsRem φ a hφ t u|
            ≤ jet_C * ‖u‖ ^ 4 / t ^ 2 := h_loc'
          _ = (jet_C / t ^ 2) * ‖u‖ ^ 4 * 1 := by ring
          _ ≤ (jet_C / t ^ 2) * ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith [h_pow_N_nn]
          _ ≤ ((jet_C + C_tail_factor) / t ^ 2) * ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) := by
              gcongr
              linarith
      · -- Tail: use global bound, absorb `1` into `‖u‖⁴/(jet_R⁴·t²)`.
        push_neg at hu
        have h_glob :=
          abs_expNumObsRem_global_le (φ := φ) (a := a) hφ hKφ_nn hpoly ht1 u
        have h_norm_sq_lb : jet_R ^ 2 * t < ‖u‖ ^ 2 := by
          have h1 : 0 ≤ jet_R * Real.sqrt t := by positivity
          have h2 := mul_self_lt_mul_self h1 hu
          rw [show (jet_R * Real.sqrt t) * (jet_R * Real.sqrt t)
                = (jet_R * Real.sqrt t) ^ 2 from by ring,
              show ‖u‖ * ‖u‖ = ‖u‖ ^ 2 from by ring] at h2
          rw [mul_pow, Real.sq_sqrt ht_pos.le] at h2
          exact h2
        have h_norm_pow_lb : jet_R ^ 4 * t ^ 2 < ‖u‖ ^ 4 := by
          calc jet_R ^ 4 * t ^ 2 = (jet_R ^ 2 * t) ^ 2 := by ring
            _ < (‖u‖ ^ 2) ^ 2 := by
                apply sq_lt_sq'
                · have h_pos : 0 ≤ jet_R ^ 2 * t := by positivity
                  linarith [sq_nonneg (‖u‖ ^ 2)]
                · exact h_norm_sq_lb
            _ = ‖u‖ ^ 4 := by ring
        have h_one_le : (1 : ℝ) ≤ ‖u‖ ^ 4 / (jet_R ^ 4 * t ^ 2) := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < jet_R^4 * t^2)]
          linarith
        -- Bound each piece of the global polynomial bound.
        -- |R| ≤ Kφ·(1 + ‖u‖^p) + (∑|aᵢ|)·‖u‖ + (|ι|/2)·‖A‖·‖u‖² + (‖Φ‖/6)·‖u‖³
        -- Each piece ≤ C_glob · (1 + ‖u‖^N).
        have h_p_le_N : ‖u‖ ^ p ≤ 1 + ‖u‖ ^ N := by
          have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
          by_cases h1u : ‖u‖ ≤ 1
          · have : ‖u‖ ^ p ≤ 1 := pow_le_one₀ h_norm_nn h1u
            have : 0 ≤ ‖u‖ ^ N := pow_nonneg h_norm_nn _
            linarith
          · push_neg at h1u
            have h_p_le : ‖u‖ ^ p ≤ ‖u‖ ^ N := by
              apply pow_le_pow_right₀ h1u.le
              rw [hN_def]; exact le_max_left _ _
            linarith [pow_nonneg h_norm_nn N]
        have h_1_le_N : (1 : ℝ) ≤ 1 + ‖u‖ ^ N := by
          linarith [pow_nonneg (norm_nonneg u) N]
        have h_norm_le_N : ‖u‖ ≤ 1 + ‖u‖ ^ N := by
          by_cases h1u : ‖u‖ ≤ 1
          · linarith [pow_nonneg (norm_nonneg u) N]
          · push_neg at h1u
            have h_le : ‖u‖ ≤ ‖u‖ ^ N := by
              calc ‖u‖ = ‖u‖ ^ 1 := by ring
                _ ≤ ‖u‖ ^ N := by
                    apply pow_le_pow_right₀ h1u.le
                    rw [hN_def]; have := le_max_right p 3; omega
            linarith [pow_nonneg (norm_nonneg u) N]
        have h_norm_sq_le_N : ‖u‖ ^ 2 ≤ 1 + ‖u‖ ^ N := by
          by_cases h1u : ‖u‖ ≤ 1
          · have : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h1u
            linarith [pow_nonneg (norm_nonneg u) N]
          · push_neg at h1u
            have h_le : ‖u‖ ^ 2 ≤ ‖u‖ ^ N := by
              apply pow_le_pow_right₀ h1u.le
              rw [hN_def]; have := le_max_right p 3; omega
            linarith [pow_nonneg (norm_nonneg u) N]
        have h_norm_cube_le_N : ‖u‖ ^ 3 ≤ 1 + ‖u‖ ^ N := by
          by_cases h1u : ‖u‖ ≤ 1
          · have : ‖u‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) h1u
            linarith [pow_nonneg (norm_nonneg u) N]
          · push_neg at h1u
            have h_le : ‖u‖ ^ 3 ≤ ‖u‖ ^ N := by
              apply pow_le_pow_right₀ h1u.le
              rw [hN_def]; exact le_max_right _ _
            linarith [pow_nonneg (norm_nonneg u) N]
        have h_glob_simp : |expNumObsRem φ a hφ t u| ≤ C_glob * (1 + ‖u‖ ^ N) := by
          rw [hC_glob_def]
          calc |expNumObsRem φ a hφ t u|
              ≤ Kφ * (1 + ‖u‖ ^ p) + (∑ i, |a i|) * ‖u‖
                + (1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2
                + ‖hφ.Φ‖ / 6 * ‖u‖ ^ 3 := h_glob
            _ ≤ 2 * Kφ * (1 + ‖u‖ ^ N) + (∑ i, |a i|) * (1 + ‖u‖ ^ N)
                + (1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖ * (1 + ‖u‖ ^ N)
                + ‖hφ.Φ‖ / 6 * (1 + ‖u‖ ^ N) := by
                  -- Kφ·(1 + ‖u‖^p) ≤ 2·Kφ·(1 + ‖u‖^N) via h_p_le_N
                  have hKφ_factor : Kφ * (1 + ‖u‖ ^ p) ≤ 2 * Kφ * (1 + ‖u‖ ^ N) := by
                    have h_pow_N_nn : 0 ≤ ‖u‖ ^ N := pow_nonneg (norm_nonneg _) _
                    have h_factor : 1 + ‖u‖ ^ p ≤ 2 * (1 + ‖u‖ ^ N) := by linarith
                    calc Kφ * (1 + ‖u‖ ^ p)
                        ≤ Kφ * (2 * (1 + ‖u‖ ^ N)) :=
                          mul_le_mul_of_nonneg_left h_factor hKφ_nn
                      _ = 2 * Kφ * (1 + ‖u‖ ^ N) := by ring
                  have ha_factor : (∑ i, |a i|) * ‖u‖ ≤ (∑ i, |a i|) * (1 + ‖u‖ ^ N) := by
                    apply mul_le_mul_of_nonneg_left h_norm_le_N
                    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
                  have hA_factor : (1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖ * ‖u‖ ^ 2
                      ≤ (1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖ * (1 + ‖u‖ ^ N) := by
                    apply mul_le_mul_of_nonneg_left h_norm_sq_le_N
                    positivity
                  have hΦ_factor : ‖hφ.Φ‖ / 6 * ‖u‖ ^ 3
                      ≤ ‖hφ.Φ‖ / 6 * (1 + ‖u‖ ^ N) := by
                    apply mul_le_mul_of_nonneg_left h_norm_cube_le_N
                    positivity
                  linarith
            _ = (2 * Kφ + (∑ i, |a i|) + (1/2 : ℝ) * Fintype.card ι * ‖hφ.A‖
                  + ‖hφ.Φ‖ / 6) * (1 + ‖u‖ ^ N) := by ring
        -- Now absorb: C_glob · (1 + ‖u‖^N) ≤ C_tail_factor · (‖u‖⁴/t²) · (1 + ‖u‖^N).
        calc |expNumObsRem φ a hφ t u|
            ≤ C_glob * (1 + ‖u‖ ^ N) := h_glob_simp
          _ = C_glob * 1 * (1 + ‖u‖ ^ N) := by ring
          _ ≤ C_glob * (‖u‖ ^ 4 / (jet_R ^ 4 * t ^ 2)) * (1 + ‖u‖ ^ N) := by
              apply mul_le_mul_of_nonneg_right _ (by linarith [pow_nonneg (norm_nonneg u) N])
              apply mul_le_mul_of_nonneg_left h_one_le hC_glob_nn
          _ = (C_glob / jet_R ^ 4) * (‖u‖ ^ 4 / t ^ 2) * (1 + ‖u‖ ^ N) := by
              field_simp
          _ = (C_tail_factor / t ^ 2) * ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) := by
              rw [hC_tail_factor_def]; field_simp
          _ ≤ ((jet_C + C_tail_factor) / t ^ 2) * ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) := by
              gcongr
              linarith
    calc |expNumObsRem φ a hφ t u| *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
        ≤ ((jet_C + C_tail_factor) / t ^ 2) * ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) *
            Real.exp (-(c * ‖u‖ ^ 2)) := by
          apply mul_le_mul h_R_ptw h_gibbs_le h_gibbs_nn (by positivity)
      _ = G u := by rw [hG_def]
  -- Conclude.
  have h_main :=
    norm_integral_le_of_norm_le hG_int (Filter.Eventually.of_forall h_pointwise)
  have h_intG : ∫ u : ι → ℝ, G u = K / t ^ 2 := by
    rw [hG_def, hK_def, hM_def]
    rw [show (fun u : ι → ℝ =>
            (jet_C + C_tail_factor) / t ^ 2 * ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) *
              Real.exp (-(c * ‖u‖ ^ 2)))
          = (fun u => ((jet_C + C_tail_factor) / t ^ 2) *
              (‖u‖ ^ 4 * (1 + ‖u‖ ^ N) * Real.exp (-(c * ‖u‖ ^ 2)))) from by
        funext u; ring]
    rw [integral_const_mul]
    ring
  calc |expNumErr₁ V φ a H hφ t|
      = ‖∫ u : ι → ℝ, expNumObsRem φ a hφ t u
          * Real.exp (-(rescaledPerturbation V H t u))
          * gaussianWeight H u‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ ∫ u : ι → ℝ, G u := h_main
    _ = K / t ^ 2 := h_intG

/-- **J₂ bound**: cubic observable jet × `(e^{-s_t} - 1)` is `O(t⁻²)`.
`P_t = O(t⁻³ᐟ²·‖u‖³)` and `e^{-s_t}-1 = O(t⁻¹ᐟ²·‖u‖³)` directly,
so the product is `O(t⁻²·‖u‖⁶)` after multiplying.

Proof: Glocal+Gtail decomposition. Pointwise local bound
(`abs_expNumCubic_mul_gW_mul_exp_sub_one_local_le`) gives
`(‖Φ‖·Cs/6/t²) · ‖u‖⁶ · exp(-(c/4)·‖u‖²)` on `‖u‖ ≤ δ·√t`.
Pointwise tail bound has an extra `exp(-(c·δ²/4)·t)` factor, and
`exp(-βt)/(t·√t) ≤ 1/t²` for `t ≥ 4/β²` via `exp_neg_const_mul_le_inv_sqrt`.
Both pieces dominated by integrable Gaussian-poly envelopes
(`integrable_norm_pow_mul_exp_neg_const_sq`). -/
private lemma expNumErr₂_bound
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₂ V φ a H hφ t| ≤ K / t ^ 2 := by
  -- Extract constants from hV (PotentialTensorApprox extends PotentialJetApprox
  -- extends PotentialApprox).
  set c : ℝ := hV.coercive_const with hc_def
  have hc_pos : 0 < c := hV.coercive_const_pos
  have h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w := hV.coercive_bound
  set R : ℝ := hV.local_radius with hR_def
  have hR_pos : 0 < R := hV.local_radius_pos
  set Cs : ℝ := hV.local_const with hCs_def
  have hCs_nn : 0 ≤ Cs := hV.local_const_nonneg
  have h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - (1/2) * quadForm H w| ≤ Cs * ‖w‖ ^ 3 := hV.local_bound
  -- Choose δ ≤ min(R, c/(4·(Cs+1))) to satisfy Cs·δ ≤ c/4.
  have hCs1_pos : (0 : ℝ) < Cs + 1 := by linarith
  set δ : ℝ := min R (c / (4 * (Cs + 1))) with hδ_def
  have hδ_pos : 0 < δ :=
    lt_min hR_pos (by positivity)
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
  set β : ℝ := c * δ ^ 2 / 4 with hβ_def
  have hβ_pos : 0 < β := by rw [hβ_def]; positivity
  -- Gaussian moments (t-independent).
  set M_loc : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 6 *
    Real.exp (-((c / 4) * ‖u‖ ^ 2)) with hM_loc_def
  set M_tail : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 3 *
    Real.exp (-((c / 4) * ‖u‖ ^ 2)) with hM_tail_def
  have h_c_quart_pos : 0 < c / 4 := by linarith
  have hM_loc_int : Integrable (fun u : ι → ℝ =>
      ‖u‖ ^ 6 * Real.exp (-((c / 4) * ‖u‖ ^ 2))) :=
    integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) h_c_quart_pos 6
  have hM_tail_int : Integrable (fun u : ι → ℝ =>
      ‖u‖ ^ 3 * Real.exp (-((c / 4) * ‖u‖ ^ 2))) :=
    integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) h_c_quart_pos 3
  have hM_loc_nn : 0 ≤ M_loc := by
    rw [hM_loc_def]
    apply MeasureTheory.integral_nonneg
    intro u; positivity
  have hM_tail_nn : 0 ≤ M_tail := by
    rw [hM_tail_def]
    apply MeasureTheory.integral_nonneg
    intro u; positivity
  -- K and T₀.
  set K : ℝ := ‖hφ.Φ‖ * Cs / 6 * M_loc + ‖hφ.Φ‖ / 3 * M_tail with hK_def
  refine ⟨K, max 1 (4 / β ^ 2), le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := le_of_max_le_left ht
  have htβ : 4 / β ^ 2 ≤ t := le_of_max_le_right ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have ht_sqrt_pos : 0 < t * Real.sqrt t := mul_pos ht_pos hsqrt_pos
  have ht_sq_pos : 0 < t ^ 2 := by positivity
  have h_tail_decay : Real.exp (-(β * t)) ≤ 1 / t :=
    exp_neg_const_mul_le_inv hβ_pos htβ
  -- Define majorants.
  set Glocal : (ι → ℝ) → ℝ := fun u =>
    (‖hφ.Φ‖ * Cs / 6 / t ^ 2) * ‖u‖ ^ 6 *
      Real.exp (-((c / 4) * ‖u‖ ^ 2)) with hGlocal_def
  set Gtail : (ι → ℝ) → ℝ := fun u =>
    (‖hφ.Φ‖ / 3 / (t * Real.sqrt t)) * ‖u‖ ^ 3 *
      Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
      Real.exp (-(β * t)) with hGtail_def
  have hGlocal_nn : ∀ u, 0 ≤ Glocal u := by
    intro u; rw [hGlocal_def]; positivity
  have hGtail_nn : ∀ u, 0 ≤ Gtail u := by
    intro u; rw [hGtail_def]; positivity
  -- Pointwise: |J₂ integrand u| ≤ Glocal u + Gtail u.
  have h_pointwise : ∀ u : ι → ℝ,
      ‖expNumCubic φ a hφ t u
        * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
        * gaussianWeight H u‖ ≤ Glocal u + Gtail u := by
    intro u
    rw [Real.norm_eq_abs]
    by_cases hu : ‖u‖ ≤ δ * Real.sqrt t
    · -- Local: bound by Glocal, Gtail nonneg.
      have h_loc :
          |expNumCubic φ a hφ t u * gaussianWeight H u
              * (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
            ≤ (‖hφ.Φ‖ * Cs / 6 / t ^ 2) * ‖u‖ ^ 6 *
                Real.exp (-((c / 4) * ‖u‖ ^ 2)) :=
        abs_expNumCubic_mul_gW_mul_exp_sub_one_local_le
          (V := V) (φ := φ) (a := a) (H := H) hφ
          hc_pos hR_pos hCs_nn h_coer h_local
          hδ_pos hδ_le_R hδ_const ht_pos u hu
      have h_eq : expNumCubic φ a hφ t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u
          = expNumCubic φ a hφ t u * gaussianWeight H u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1) := by ring
      rw [h_eq]
      calc |expNumCubic φ a hφ t u * gaussianWeight H u
              * (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
          ≤ (‖hφ.Φ‖ * Cs / 6 / t ^ 2) * ‖u‖ ^ 6 *
              Real.exp (-((c / 4) * ‖u‖ ^ 2)) := h_loc
        _ = Glocal u := by rw [hGlocal_def]
        _ ≤ Glocal u + Gtail u := by linarith [hGtail_nn u]
    · -- Tail: bound by Gtail, Glocal nonneg.
      push_neg at hu
      have h_tail :
          |expNumCubic φ a hφ t u * gaussianWeight H u
              * (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
            ≤ (‖hφ.Φ‖ / 3 / (t * Real.sqrt t)) * ‖u‖ ^ 3 *
                Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
                Real.exp (-((c * δ ^ 2 / 4) * t)) :=
        abs_expNumCubic_mul_gW_mul_exp_sub_one_tail_le
          (V := V) (φ := φ) (a := a) (H := H) hφ
          hc_pos hR_pos hCs_nn h_coer h_local
          hδ_pos ht_pos u hu
      have h_eq : expNumCubic φ a hφ t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u
          = expNumCubic φ a hφ t u * gaussianWeight H u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1) := by ring
      rw [h_eq]
      calc |expNumCubic φ a hφ t u * gaussianWeight H u
              * (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
          ≤ (‖hφ.Φ‖ / 3 / (t * Real.sqrt t)) * ‖u‖ ^ 3 *
              Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
              Real.exp (-((c * δ ^ 2 / 4) * t)) := h_tail
        _ = Gtail u := by rw [hGtail_def, hβ_def]
        _ ≤ Glocal u + Gtail u := by linarith [hGlocal_nn u]
  -- Integrability of Glocal + Gtail.
  have hGlocal_int : Integrable Glocal := by
    rw [hGlocal_def]
    have := hM_loc_int.const_mul (‖hφ.Φ‖ * Cs / 6 / t ^ 2)
    convert this using 1
    funext u; ring
  have hGtail_int : Integrable Gtail := by
    rw [hGtail_def]
    have := hM_tail_int.const_mul
      ((‖hφ.Φ‖ / 3 / (t * Real.sqrt t)) * Real.exp (-(β * t)))
    convert this using 1
    funext u; ring
  have hSum_int : Integrable (fun u => Glocal u + Gtail u) :=
    hGlocal_int.add hGtail_int
  -- Conclude.
  have h_main :=
    norm_integral_le_of_norm_le hSum_int (Filter.Eventually.of_forall h_pointwise)
  -- ∫ Glocal = ‖Φ‖·Cs/6/t² · M_loc.
  have h_intGlocal : ∫ u : ι → ℝ, Glocal u =
      ‖hφ.Φ‖ * Cs / 6 / t ^ 2 * M_loc := by
    rw [hGlocal_def, hM_loc_def]
    rw [show (fun u : ι → ℝ => ‖hφ.Φ‖ * Cs / 6 / t ^ 2 *
              ‖u‖ ^ 6 * Real.exp (-(c / 4 * ‖u‖ ^ 2)))
          = (fun u => (‖hφ.Φ‖ * Cs / 6 / t ^ 2) *
              (‖u‖ ^ 6 * Real.exp (-(c / 4 * ‖u‖ ^ 2)))) from by
        funext u; ring]
    exact integral_const_mul _ _
  have h_intGtail : ∫ u : ι → ℝ, Gtail u =
      ‖hφ.Φ‖ / 3 / (t * Real.sqrt t) * Real.exp (-(β * t)) * M_tail := by
    rw [hGtail_def, hM_tail_def]
    rw [show (fun u : ι → ℝ => ‖hφ.Φ‖ / 3 / (t * Real.sqrt t) *
              ‖u‖ ^ 3 * Real.exp (-(c / 4 * ‖u‖ ^ 2)) *
              Real.exp (-(β * t)))
          = (fun u => (‖hφ.Φ‖ / 3 / (t * Real.sqrt t) *
              Real.exp (-(β * t))) *
              (‖u‖ ^ 3 * Real.exp (-(c / 4 * ‖u‖ ^ 2)))) from by
        funext u; ring]
    rw [integral_const_mul]
  -- Bound the tail piece by 1/t².
  have h_tail_bound : ‖hφ.Φ‖ / 3 / (t * Real.sqrt t) * Real.exp (-(β * t)) * M_tail
      ≤ ‖hφ.Φ‖ / 3 * M_tail / t ^ 2 := by
    have h1 : Real.exp (-(β * t)) ≤ 1 / t := h_tail_decay
    have h2 : (1 : ℝ) ≤ Real.sqrt t := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt ht1
    have h3 : 1 / (t * Real.sqrt t) ≤ 1 / t := by
      apply one_div_le_one_div_of_le ht_pos
      calc t = t * 1 := (mul_one t).symm
        _ ≤ t * Real.sqrt t := mul_le_mul_of_nonneg_left h2 ht_pos.le
    have hΦ_nn : 0 ≤ ‖hφ.Φ‖ / 3 := by positivity
    have h4 : ‖hφ.Φ‖ / 3 / (t * Real.sqrt t) ≤ ‖hφ.Φ‖ / 3 / t := by
      rw [div_eq_mul_inv (‖hφ.Φ‖ / 3) (t * Real.sqrt t),
          div_eq_mul_inv (‖hφ.Φ‖ / 3) t]
      apply mul_le_mul_of_nonneg_left _ hΦ_nn
      rw [show (t * Real.sqrt t)⁻¹ = 1 / (t * Real.sqrt t) from by rw [one_div],
          show t⁻¹ = 1 / t from by rw [one_div]]
      exact h3
    have h_M_tail_nn : 0 ≤ M_tail := hM_tail_nn
    have hexp_nn : 0 ≤ Real.exp (-(β * t)) := (Real.exp_pos _).le
    calc ‖hφ.Φ‖ / 3 / (t * Real.sqrt t) * Real.exp (-(β * t)) * M_tail
        ≤ ‖hφ.Φ‖ / 3 / t * Real.exp (-(β * t)) * M_tail := by
          apply mul_le_mul_of_nonneg_right _ h_M_tail_nn
          exact mul_le_mul_of_nonneg_right h4 hexp_nn
      _ ≤ ‖hφ.Φ‖ / 3 / t * (1 / t) * M_tail := by
          apply mul_le_mul_of_nonneg_right _ h_M_tail_nn
          apply mul_le_mul_of_nonneg_left h1
          exact div_nonneg hΦ_nn ht_pos.le
      _ = ‖hφ.Φ‖ / 3 * M_tail / t ^ 2 := by
          field_simp
  -- Combine.
  have h_intSum :
      ∫ u : ι → ℝ, Glocal u + Gtail u
      = ‖hφ.Φ‖ * Cs / 6 / t ^ 2 * M_loc
        + ‖hφ.Φ‖ / 3 / (t * Real.sqrt t) * Real.exp (-(β * t)) * M_tail := by
    rw [integral_add hGlocal_int hGtail_int, h_intGlocal, h_intGtail]
  have h_intSum_nn : 0 ≤ ∫ u : ι → ℝ, Glocal u + Gtail u := by
    apply MeasureTheory.integral_nonneg
    intro u
    show (0 : ℝ) ≤ Glocal u + Gtail u
    linarith [hGlocal_nn u, hGtail_nn u]
  calc |expNumErr₂ V φ a H hφ t|
      = ‖∫ u : ι → ℝ, expNumCubic φ a hφ t u
          * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
          * gaussianWeight H u‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ∫ u : ι → ℝ, Glocal u + Gtail u := h_main
    _ = ‖hφ.Φ‖ * Cs / 6 / t ^ 2 * M_loc
        + ‖hφ.Φ‖ / 3 / (t * Real.sqrt t) * Real.exp (-(β * t)) * M_tail := h_intSum
    _ ≤ ‖hφ.Φ‖ * Cs / 6 / t ^ 2 * M_loc
        + ‖hφ.Φ‖ / 3 * M_tail / t ^ 2 := by linarith [h_tail_bound]
    _ = K / t ^ 2 := by rw [hK_def]; ring

set_option maxHeartbeats 3200000 in
/-- **Pointwise local bound for J₃ integrand.** -/
private lemma J3_local_pointwise_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_le_R : δ ≤ hV.local_radius)
    (hδ_le_jet_R : δ ≤ hV.jet_radius)
    (hδ_const : hV.local_const * δ ≤ hV.coercive_const / 4)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ δ * Real.sqrt t) :
    |expNumLin a t u *
        ((Real.exp (-(rescaledPerturbation V H t u)) - 1
            + expPotCubic V H hV.toPotentialTensorApprox t u)
          - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
        gaussianWeight H u|
      ≤ ((∑ i, |a i|) * (hV.Q_const + 2 * hV.jet_const * hV.local_const +
            hV.local_const ^ 3) / t ^ 2) *
          (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
          Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
  set La : ℝ := ∑ i, |a i| with hLa_def
  set D : ℝ := hV.Q_const + 2 * hV.jet_const * hV.local_const + hV.local_const ^ 3
    with hD_def
  have hLa_nn : 0 ≤ La := by rw [hLa_def]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hCs_nn : 0 ≤ hV.local_const := hV.local_const_nonneg
  have hjet_C_nn : 0 ≤ hV.jet_const := hV.jet_const_nonneg
  have hQ_nn : 0 ≤ hV.Q_const := hV.Q_const_nn
  have hc_pos : 0 < hV.coercive_const := hV.coercive_const_pos
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_sqrt_t_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
  have ht_sq_pos : 0 < t ^ 2 := pow_pos ht 2
  -- Rearrange |F| = |L_t| · gW · |bracket|.
  have h_F_eq : |expNumLin a t u *
        ((Real.exp (-(rescaledPerturbation V H t u)) - 1
            + expPotCubic V H hV.toPotentialTensorApprox t u)
          - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
        gaussianWeight H u|
      = |expNumLin a t u| * (gaussianWeight H u *
          |((Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t u)
            - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t (-u)))|) := by
    rw [show expNumLin a t u *
            ((Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t u)
              - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                  + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
            gaussianWeight H u
          = expNumLin a t u *
              (gaussianWeight H u *
                ((Real.exp (-(rescaledPerturbation V H t u)) - 1
                    + expPotCubic V H hV.toPotentialTensorApprox t u)
                  - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                      + expPotCubic V H hV.toPotentialTensorApprox t (-u)))) from by
        ring,
        abs_mul, abs_mul (gaussianWeight H u), abs_of_nonneg h_gW_nn]
  rw [h_F_eq]
  -- |L_t| ≤ La·‖u‖/√t.
  have h_L_bound : |expNumLin a t u| ≤ La * ‖u‖ / Real.sqrt t := by
    unfold expNumLin
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (Real.sqrt t)⁻¹)]
    have h_dot_le : |dot a u| ≤ La * ‖u‖ := by
      rw [hLa_def]; unfold dot
      calc |∑ i, a i * u i|
          ≤ ∑ i, |a i * u i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |a i| * ‖u‖ := by
            apply Finset.sum_le_sum; intro i _; rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) (abs_nonneg _)
        _ = (∑ i, |a i|) * ‖u‖ := by rw [Finset.sum_mul]
    have h2 : (Real.sqrt t)⁻¹ * (La * ‖u‖) = La * ‖u‖ / Real.sqrt t := by field_simp
    have h1 : (Real.sqrt t)⁻¹ * |dot a u|
        ≤ (Real.sqrt t)⁻¹ * (La * ‖u‖) :=
      mul_le_mul_of_nonneg_left h_dot_le (by positivity)
    linarith [h2.le, h2.ge]
  have h_L_nn : 0 ≤ La * ‖u‖ / Real.sqrt t := by positivity
  -- gW · |bracket| bound combining helper and gW absorption.
  have h_br := abs_J3_bracket_local_le V H hV hδ_pos hδ_le_R hδ_le_jet_R hδ_const ht u hu
  have h_gW_le := gaussianWeight_le_exp_neg_coercive V H hV.toPotentialTensorApprox u
  have h_gW_quart : gaussianWeight H u
      ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
    have h2 : Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2))
        ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
      apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg ‖u‖, hc_pos]
    linarith
  have h_gW_combine : gaussianWeight H u *
        Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2)
      ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
    have h_eq : Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2)) *
        Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2)
        = Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h_mul : gaussianWeight H u * Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2)
        ≤ Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2)) *
          Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h_gW_le (by positivity)
    linarith [h_eq.le, h_eq.ge]
  -- gW · |bracket| ≤ exp(-(c/4)) · (Q·‖u‖^5/(t·√t) + 2·jet_C·Cs·‖u‖^7/(t·√t) + Cs³·‖u‖^9/(t·√t)).
  have h_gWbr : gaussianWeight H u *
        |((Real.exp (-(rescaledPerturbation V H t u)) - 1
            + expPotCubic V H hV.toPotentialTensorApprox t u)
          - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t (-u)))|
      ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
        (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
          + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
          + hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t)) := by
    -- Step a: gW · |bracket| ≤ gW · h_br.
    have h_step_a : gaussianWeight H u *
          |((Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t u)
            - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t (-u)))|
        ≤ gaussianWeight H u * (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
              + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
              + hV.local_const ^ 3 * ‖u‖ ^ 9 *
                  Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (t * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_left h_br h_gW_nn
    -- Step b: gW · sum ≤ exp(-(c/4)) · sum-without-extra-exp.
    have h_t1 : gaussianWeight H u * (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t))
        ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
          (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_right h_gW_quart (by positivity)
    have h_t2 : gaussianWeight H u *
          (2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t))
        ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
          (2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_right h_gW_quart (by positivity)
    have h_t3 : gaussianWeight H u *
          (hV.local_const ^ 3 * ‖u‖ ^ 9 *
            Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (t * Real.sqrt t))
        ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
          (hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t)) := by
      have h_factor : gaussianWeight H u *
            (hV.local_const ^ 3 * ‖u‖ ^ 9 *
              Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (t * Real.sqrt t))
          = (gaussianWeight H u * Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
            (hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t)) := by ring
      rw [h_factor]
      exact mul_le_mul_of_nonneg_right h_gW_combine (by positivity)
    have h_dist_lhs : gaussianWeight H u *
          (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
              + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
              + hV.local_const ^ 3 * ‖u‖ ^ 9 *
                  Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / (t * Real.sqrt t))
        = gaussianWeight H u * (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t))
          + gaussianWeight H u *
              (2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t))
          + gaussianWeight H u *
              (hV.local_const ^ 3 * ‖u‖ ^ 9 *
                Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) /
                  (t * Real.sqrt t)) := by ring
    have h_dist_rhs : Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
          (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
            + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
            + hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t))
        = Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
            (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t))
          + Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
              (2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t))
          + Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
              (hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t)) := by ring
    linarith [h_step_a, h_t1, h_t2, h_t3, h_dist_lhs.le, h_dist_lhs.ge,
              h_dist_rhs.le, h_dist_rhs.ge]
  -- Multiply by |L_t| ≤ La·‖u‖/√t.
  have h_step1 : |expNumLin a t u| * (gaussianWeight H u *
          |((Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t u)
            - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t (-u)))|)
      ≤ (La * ‖u‖ / Real.sqrt t) *
        (Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
        (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
          + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
          + hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t))) := by
    apply mul_le_mul h_L_bound h_gWbr (mul_nonneg h_gW_nn (abs_nonneg _)) h_L_nn
  -- Algebraic identity: (X/√t) · (Y/(t·√t)) = X·Y/t².
  have h_simp_factor : ∀ X : ℝ, (‖u‖ / Real.sqrt t) * (X / (t * Real.sqrt t))
      = ‖u‖ * X / t ^ 2 := by
    intro X
    rw [div_mul_div_comm]
    rw [mul_comm (Real.sqrt t) (t * Real.sqrt t), mul_assoc t _ _, h_sqrt_t_sq]
    ring
  -- Distribute La·(‖u‖/√t) over the three terms.
  have h_distrib : (La * ‖u‖ / Real.sqrt t) *
        (Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
        (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
          + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
          + hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t)))
      = (La * (hV.Q_const * ‖u‖ ^ 6
            + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 8
            + hV.local_const ^ 3 * ‖u‖ ^ 10) / t ^ 2) *
        Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
    have h_t1 := h_simp_factor (hV.Q_const * ‖u‖ ^ 5)
    have h_t2 := h_simp_factor (2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7)
    have h_t3 := h_simp_factor (hV.local_const ^ 3 * ‖u‖ ^ 9)
    have h_lhs : (La * ‖u‖ / Real.sqrt t) *
          (Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
          (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t)
            + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t)
            + hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t)))
        = La * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) *
          ((‖u‖ / Real.sqrt t) * (hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t))
            + (‖u‖ / Real.sqrt t) *
              (2 * hV.jet_const * hV.local_const * ‖u‖ ^ 7 / (t * Real.sqrt t))
            + (‖u‖ / Real.sqrt t) *
              (hV.local_const ^ 3 * ‖u‖ ^ 9 / (t * Real.sqrt t))) := by ring
    rw [h_lhs, h_t1, h_t2, h_t3]
    ring
  -- Final: La·(Q·‖u‖^6 + 2·jet_C·Cs·‖u‖^8 + Cs³·‖u‖^10) ≤ La·D·(‖u‖^6+‖u‖^8+‖u‖^10).
  have h_final : (La * (hV.Q_const * ‖u‖ ^ 6
            + 2 * hV.jet_const * hV.local_const * ‖u‖ ^ 8
            + hV.local_const ^ 3 * ‖u‖ ^ 10) / t ^ 2) *
        Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))
      ≤ (La * D / t ^ 2) *
        (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
        Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
    rw [show (La * D / t ^ 2) * (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
            Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))
          = (La * D * (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) / t ^ 2) *
            Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) from by ring]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply div_le_div_of_nonneg_right _ ht_sq_pos.le
    rw [hD_def]
    have h_u6_nn : 0 ≤ ‖u‖ ^ 6 := pow_nonneg (norm_nonneg _) _
    have h_u8_nn : 0 ≤ ‖u‖ ^ 8 := pow_nonneg (norm_nonneg _) _
    have h_u10_nn : 0 ≤ ‖u‖ ^ 10 := pow_nonneg (norm_nonneg _) _
    have h_jc_nn : 0 ≤ hV.jet_const * hV.local_const := mul_nonneg hjet_C_nn hCs_nn
    have h_cs3_nn : 0 ≤ hV.local_const ^ 3 := by positivity
    -- La·D·(‖u‖^6+‖u‖^8+‖u‖^10) - La·(Q·‖u‖^6 + 2·jet·Cs·‖u‖^8 + Cs³·‖u‖^10) ≥ 0
    -- because LHS includes Q·‖u‖^8, Q·‖u‖^10, 2·jet·Cs·‖u‖^6, 2·jet·Cs·‖u‖^10,
    -- Cs³·‖u‖^6, Cs³·‖u‖^8 as extra terms.
    nlinarith [mul_nonneg hLa_nn hQ_nn, mul_nonneg hLa_nn h_jc_nn,
               mul_nonneg hLa_nn h_cs3_nn,
               mul_nonneg (mul_nonneg hLa_nn hQ_nn) h_u6_nn,
               mul_nonneg (mul_nonneg hLa_nn hQ_nn) h_u8_nn,
               mul_nonneg (mul_nonneg hLa_nn hQ_nn) h_u10_nn,
               mul_nonneg (mul_nonneg hLa_nn h_jc_nn) h_u6_nn,
               mul_nonneg (mul_nonneg hLa_nn h_jc_nn) h_u8_nn,
               mul_nonneg (mul_nonneg hLa_nn h_jc_nn) h_u10_nn,
               mul_nonneg (mul_nonneg hLa_nn h_cs3_nn) h_u6_nn,
               mul_nonneg (mul_nonneg hLa_nn h_cs3_nn) h_u8_nn,
               mul_nonneg (mul_nonneg hLa_nn h_cs3_nn) h_u10_nn]
  linarith [h_step1, h_distrib.le, h_distrib.ge, h_final]

set_option maxHeartbeats 3200000 in
/-- **Pointwise tail bound for J₃ integrand.** -/
private lemma J3_tail_pointwise_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {c : ℝ} (hc_pos : 0 < c) (hc_eq : c = hV.coercive_const)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : δ * Real.sqrt t < ‖u‖) :
    |expNumLin a t u *
        ((Real.exp (-(rescaledPerturbation V H t u)) - 1
            + expPotCubic V H hV.toPotentialTensorApprox t u)
          - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
        gaussianWeight H u|
      ≤ ((∑ i, |a i|) * (4 / δ ^ 3 + ‖hV.T‖ / (3 * δ ^ 2)) / t ^ 2) *
          (‖u‖ ^ 4 + ‖u‖ ^ 6) *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
  set La : ℝ := ∑ i, |a i| with hLa_def
  have hLa_nn : 0 ≤ La := by rw [hLa_def]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hT_nn : 0 ≤ ‖hV.T‖ := norm_nonneg _
  have hδ_sq_pos : 0 < δ ^ 2 := by positivity
  have hδ_cube_pos : 0 < δ ^ 3 := by positivity
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_sqrt_t_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
  have ht_sq_pos : 0 < t ^ 2 := pow_pos ht 2
  -- Use uniform helper.
  have h_uniform := abs_gW_J3_bracket_le_uniform V H hV.toPotentialTensorApprox
    hc_pos h_coer ht u
  -- Rearrange |F| = |L_t| · |gW · bracket|.
  have h_F_eq : |expNumLin a t u *
        ((Real.exp (-(rescaledPerturbation V H t u)) - 1
            + expPotCubic V H hV.toPotentialTensorApprox t u)
          - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
        gaussianWeight H u|
      = |expNumLin a t u| *
        |gaussianWeight H u *
          ((Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t u)
            - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t (-u)))| := by
    rw [show expNumLin a t u *
            ((Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t u)
              - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                  + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
            gaussianWeight H u
          = expNumLin a t u *
              (gaussianWeight H u *
                ((Real.exp (-(rescaledPerturbation V H t u)) - 1
                    + expPotCubic V H hV.toPotentialTensorApprox t u)
                  - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                      + expPotCubic V H hV.toPotentialTensorApprox t (-u)))) from by
        ring,
        abs_mul]
  rw [h_F_eq]
  -- |L_t| ≤ La·‖u‖/√t.
  have h_L_bound : |expNumLin a t u| ≤ La * ‖u‖ / Real.sqrt t := by
    unfold expNumLin
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (Real.sqrt t)⁻¹)]
    have h_dot_le : |dot a u| ≤ La * ‖u‖ := by
      rw [hLa_def]; unfold dot
      calc |∑ i, a i * u i|
          ≤ ∑ i, |a i * u i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |a i| * ‖u‖ := by
            apply Finset.sum_le_sum; intro i _; rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) (abs_nonneg _)
        _ = (∑ i, |a i|) * ‖u‖ := by rw [Finset.sum_mul]
    have h2 : (Real.sqrt t)⁻¹ * (La * ‖u‖) = La * ‖u‖ / Real.sqrt t := by field_simp
    have h1 : (Real.sqrt t)⁻¹ * |dot a u|
        ≤ (Real.sqrt t)⁻¹ * (La * ‖u‖) :=
      mul_le_mul_of_nonneg_left h_dot_le (by positivity)
    linarith [h2.le, h2.ge]
  have h_L_nn : 0 ≤ La * ‖u‖ / Real.sqrt t := by positivity
  -- Tail uniform bound: |gW·bracket| ≤ 2·gW + 2·exp(-c·‖u‖²) + 2·gW·‖T‖/6·‖u‖³/√t.
  -- Bound each piece by exp(-(c/4)).
  have h_gW_le : gaussianWeight H u ≤ Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
    rw [hc_eq] at *
    have h1 := gaussianWeight_le_exp_neg_coercive V H hV.toPotentialTensorApprox u
    have h2 : Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2))
        ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
      apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg ‖u‖, hV.coercive_const_pos]
    linarith
  have h_exp_c_quart : Real.exp (-(c * ‖u‖ ^ 2))
      ≤ Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
    apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg ‖u‖, hc_pos]
  -- Simpler form: |gW·bracket| ≤ 4·exp(-(c/4)) + 2·(‖T‖/6·‖u‖³/√t)·exp(-(c/4)).
  have h_unif_simpler : |gaussianWeight H u *
        ((Real.exp (-(rescaledPerturbation V H t u)) - 1
            + expPotCubic V H hV.toPotentialTensorApprox t u)
          - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t (-u)))|
      ≤ 4 * Real.exp (-((c / 4) * ‖u‖ ^ 2))
        + 2 * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) *
            Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
    have h_T_term_nn : 0 ≤ ‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t := by positivity
    have h_step_a : 2 * gaussianWeight H u ≤ 2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
      linarith [h_gW_le]
    have h_step_b : 2 * Real.exp (-(c * ‖u‖ ^ 2))
        ≤ 2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by linarith
    have h_step_c : 2 * gaussianWeight H u *
          (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t)
        ≤ 2 * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) *
            Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
      have h_factor : 2 * gaussianWeight H u *
            (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t)
          = 2 * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) * gaussianWeight H u := by ring
      rw [h_factor]
      apply mul_le_mul_of_nonneg_left h_gW_le (by positivity)
    linarith [h_uniform, h_step_a, h_step_b, h_step_c]
  -- |F| ≤ La·(‖u‖/√t) · (4·exp + 2·(‖T‖/6·‖u‖³/√t)·exp).
  have h_step1 : |expNumLin a t u| *
        |gaussianWeight H u *
          ((Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t u)
            - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t (-u)))|
      ≤ (La * ‖u‖ / Real.sqrt t) *
        (4 * Real.exp (-((c / 4) * ‖u‖ ^ 2))
          + 2 * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) *
              Real.exp (-((c / 4) * ‖u‖ ^ 2))) := by
    apply mul_le_mul h_L_bound h_unif_simpler (abs_nonneg _) h_L_nn
  -- Distribute: La·(‖u‖/√t)·4·exp = 4·La·(‖u‖/√t)·exp.
  -- La·(‖u‖/√t)·2·(‖T‖/6·‖u‖³/√t)·exp = (La·‖T‖/3)·(‖u‖^4/t)·exp.
  have h_distrib : (La * ‖u‖ / Real.sqrt t) *
        (4 * Real.exp (-((c / 4) * ‖u‖ ^ 2))
          + 2 * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) *
              Real.exp (-((c / 4) * ‖u‖ ^ 2)))
      = (4 * La * (‖u‖ / Real.sqrt t)
          + La * ‖hV.T‖ / 3 * (‖u‖ ^ 4 / t)) *
        Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
    have h_t_factor : (‖u‖ / Real.sqrt t) * (‖u‖ ^ 3 / Real.sqrt t)
        = ‖u‖ ^ 4 / t := by
      rw [div_mul_div_comm, h_sqrt_t_sq]
      ring
    have h_lhs_simp : (La * ‖u‖ / Real.sqrt t) *
          (4 * Real.exp (-((c / 4) * ‖u‖ ^ 2))
            + 2 * (‖hV.T‖ / 6 * ‖u‖ ^ 3 / Real.sqrt t) *
                Real.exp (-((c / 4) * ‖u‖ ^ 2)))
        = (4 * La * (‖u‖ / Real.sqrt t)
            + La * ‖hV.T‖ / 3 *
              ((‖u‖ / Real.sqrt t) * (‖u‖ ^ 3 / Real.sqrt t))) *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by ring
    rw [h_lhs_simp, h_t_factor]
  -- Tail absorption: ‖u‖ > δ·√t ⟹ ‖u‖/√t ≤ ‖u‖^4/(δ³·t²) and ‖u‖^4/t ≤ ‖u‖^6/(δ²·t²).
  have h_norm_sq_lb : δ ^ 2 * t < ‖u‖ ^ 2 := by
    have h1 : 0 ≤ δ * Real.sqrt t := by positivity
    have h2 := mul_self_lt_mul_self h1 hu
    rw [show (δ * Real.sqrt t) * (δ * Real.sqrt t) = (δ * Real.sqrt t) ^ 2 from by ring,
        show ‖u‖ * ‖u‖ = ‖u‖ ^ 2 from by ring] at h2
    rw [mul_pow, Real.sq_sqrt ht.le] at h2; exact h2
  have h_one_le : (1 : ℝ) ≤ ‖u‖ ^ 2 / (δ ^ 2 * t) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < δ^2 * t)]; linarith [h_norm_sq_lb]
  have h_norm_sqt_le : ‖u‖ / Real.sqrt t ≤ ‖u‖ ^ 2 / (δ * t) := by
    rw [div_le_div_iff₀ hsqrt_pos (by positivity : (0 : ℝ) < δ * t)]
    calc ‖u‖ * (δ * t) = ‖u‖ * δ * t := by ring
      _ = ‖u‖ * δ * ((Real.sqrt t) * (Real.sqrt t)) := by
          rw [Real.mul_self_sqrt ht.le]
      _ = (δ * Real.sqrt t) * (‖u‖ * Real.sqrt t) := by ring
      _ ≤ ‖u‖ * (‖u‖ * Real.sqrt t) :=
          mul_le_mul_of_nonneg_right hu.le (by positivity)
      _ = ‖u‖ ^ 2 * Real.sqrt t := by ring
  have h_norm_sqt_to_t2 : ‖u‖ / Real.sqrt t ≤ ‖u‖ ^ 4 / (δ ^ 3 * t ^ 2) := by
    calc ‖u‖ / Real.sqrt t ≤ ‖u‖ ^ 2 / (δ * t) := h_norm_sqt_le
      _ = ‖u‖ ^ 2 / (δ * t) * 1 := (mul_one _).symm
      _ ≤ ‖u‖ ^ 2 / (δ * t) * (‖u‖ ^ 2 / (δ ^ 2 * t)) :=
          mul_le_mul_of_nonneg_left h_one_le (by positivity)
      _ = ‖u‖ ^ 4 / (δ ^ 3 * t ^ 2) := by field_simp
  have h_u4_t_to_t2 : ‖u‖ ^ 4 / t ≤ ‖u‖ ^ 6 / (δ ^ 2 * t ^ 2) := by
    calc ‖u‖ ^ 4 / t = ‖u‖ ^ 4 / t * 1 := (mul_one _).symm
      _ ≤ ‖u‖ ^ 4 / t * (‖u‖ ^ 2 / (δ ^ 2 * t)) :=
          mul_le_mul_of_nonneg_left h_one_le (by positivity)
      _ = ‖u‖ ^ 6 / (δ ^ 2 * t ^ 2) := by field_simp
  -- Final: 4·La·(‖u‖/√t) + (La·‖T‖/3)·(‖u‖^4/t) ≤ La·(4/δ³ + ‖T‖/(3·δ²)) · (‖u‖^4 + ‖u‖^6)/t².
  have h_absorbed : 4 * La * (‖u‖ / Real.sqrt t)
        + La * ‖hV.T‖ / 3 * (‖u‖ ^ 4 / t)
      ≤ La * (4 / δ ^ 3 + ‖hV.T‖ / (3 * δ ^ 2)) * (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2 := by
    have h_a : 4 * La * (‖u‖ / Real.sqrt t)
        ≤ 4 * La * (‖u‖ ^ 4 / (δ ^ 3 * t ^ 2)) := by
      apply mul_le_mul_of_nonneg_left h_norm_sqt_to_t2 (by positivity)
    have h_b : La * ‖hV.T‖ / 3 * (‖u‖ ^ 4 / t)
        ≤ La * ‖hV.T‖ / 3 * (‖u‖ ^ 6 / (δ ^ 2 * t ^ 2)) := by
      apply mul_le_mul_of_nonneg_left h_u4_t_to_t2 (by positivity)
    have h_a_eq : 4 * La * (‖u‖ ^ 4 / (δ ^ 3 * t ^ 2))
        = (La * (4 / δ ^ 3)) * (‖u‖ ^ 4 / t ^ 2) := by field_simp
    have h_b_eq : La * ‖hV.T‖ / 3 * (‖u‖ ^ 6 / (δ ^ 2 * t ^ 2))
        = (La * ‖hV.T‖ / (3 * δ ^ 2)) * (‖u‖ ^ 6 / t ^ 2) := by field_simp
    rw [h_a_eq] at h_a
    rw [h_b_eq] at h_b
    have h_u4_nn : 0 ≤ ‖u‖ ^ 4 := pow_nonneg (norm_nonneg _) _
    have h_u6_nn : 0 ≤ ‖u‖ ^ 6 := pow_nonneg (norm_nonneg _) _
    have h_4_nn : 0 ≤ La * (4 / δ ^ 3) := by positivity
    have h_T_nn' : 0 ≤ La * ‖hV.T‖ / (3 * δ ^ 2) := by positivity
    -- Goal: La·(4/δ³)·‖u‖^4/t² + La·‖T‖/(3δ²)·‖u‖^6/t² ≤ La·(4/δ³+‖T‖/(3δ²))·(‖u‖^4+‖u‖^6)/t².
    have h_bound : La * (4 / δ ^ 3) * (‖u‖ ^ 4 / t ^ 2)
          + La * ‖hV.T‖ / (3 * δ ^ 2) * (‖u‖ ^ 6 / t ^ 2)
        ≤ La * (4 / δ ^ 3 + ‖hV.T‖ / (3 * δ ^ 2)) *
          (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2 := by
      have h_expand : La * (4 / δ ^ 3 + ‖hV.T‖ / (3 * δ ^ 2)) *
            (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2
          = (La * (4 / δ ^ 3) * (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2)
            + (La * ‖hV.T‖ / (3 * δ ^ 2) * (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2) := by ring
      rw [h_expand]
      have h_split_a : La * (4 / δ ^ 3) * (‖u‖ ^ 4 / t ^ 2)
          ≤ La * (4 / δ ^ 3) * (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2 := by
        rw [show La * (4 / δ ^ 3) * (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2
              = La * (4 / δ ^ 3) * ((‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2) from by ring,
            show La * (4 / δ ^ 3) * (‖u‖ ^ 4 / t ^ 2)
              = La * (4 / δ ^ 3) * (‖u‖ ^ 4 / t ^ 2) from rfl]
        apply mul_le_mul_of_nonneg_left _ h_4_nn
        apply div_le_div_of_nonneg_right _ ht_sq_pos.le
        linarith
      have h_split_b : La * ‖hV.T‖ / (3 * δ ^ 2) * (‖u‖ ^ 6 / t ^ 2)
          ≤ La * ‖hV.T‖ / (3 * δ ^ 2) * (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2 := by
        rw [show La * ‖hV.T‖ / (3 * δ ^ 2) * (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2
              = La * ‖hV.T‖ / (3 * δ ^ 2) * ((‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2) from by ring]
        apply mul_le_mul_of_nonneg_left _ h_T_nn'
        apply div_le_div_of_nonneg_right _ ht_sq_pos.le
        linarith
      linarith
    linarith [h_a, h_b, h_bound]
  -- Combine.
  have h_combine_final : (4 * La * (‖u‖ / Real.sqrt t)
          + La * ‖hV.T‖ / 3 * (‖u‖ ^ 4 / t)) *
        Real.exp (-((c / 4) * ‖u‖ ^ 2))
      ≤ La * (4 / δ ^ 3 + ‖hV.T‖ / (3 * δ ^ 2)) / t ^ 2 *
        (‖u‖ ^ 4 + ‖u‖ ^ 6) *
        Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
    rw [show La * (4 / δ ^ 3 + ‖hV.T‖ / (3 * δ ^ 2)) / t ^ 2 *
            (‖u‖ ^ 4 + ‖u‖ ^ 6) *
            Real.exp (-((c / 4) * ‖u‖ ^ 2))
          = (La * (4 / δ ^ 3 + ‖hV.T‖ / (3 * δ ^ 2)) *
              (‖u‖ ^ 4 + ‖u‖ ^ 6) / t ^ 2) *
            Real.exp (-((c / 4) * ‖u‖ ^ 2)) from by ring]
    exact mul_le_mul_of_nonneg_right h_absorbed (Real.exp_pos _).le
  linarith [h_step1, h_distrib.le, h_distrib.ge, h_combine_final]

/-- **J₃ bound**: linear observable jet × `(e^{-s_t} - 1 + C_t)` is `O(t⁻²)`.

Hypothesis: `PotentialQuinticApprox` (provides quintic remainder bound on V).
Combines `J3_local_pointwise_le` and `J3_tail_pointwise_le` by case-split,
then applies `norm_integral_le_of_norm_le` for the integral bound. -/
private lemma expNumErr₃_bound
    (V : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₃ V H hV.toPotentialTensorApprox a t| ≤ K / t ^ 2 := by
  -- Setup constants.
  have hc_pos : 0 < hV.coercive_const := hV.coercive_const_pos
  have h_coer : ∀ w : ι → ℝ, hV.coercive_const * ‖w‖ ^ 2 ≤ V w := hV.coercive_bound
  have hCs_nn : 0 ≤ hV.local_const := hV.local_const_nonneg
  have hjet_C_nn : 0 ≤ hV.jet_const := hV.jet_const_nonneg
  have hQ_nn : 0 ≤ hV.Q_const := hV.Q_const_nn
  have hT_nn : 0 ≤ ‖hV.T‖ := norm_nonneg _
  have hCs1_pos : (0 : ℝ) < hV.local_const + 1 := by linarith
  set δ : ℝ := min (min hV.local_radius hV.jet_radius)
      (hV.coercive_const / (4 * (hV.local_const + 1))) with hδ_def
  have hδ_pos : 0 < δ :=
    lt_min (lt_min hV.local_radius_pos hV.jet_radius_pos) (by positivity)
  have hδ_le_R : δ ≤ hV.local_radius :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ_le_jet_R : δ ≤ hV.jet_radius :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ_const : hV.local_const * δ ≤ hV.coercive_const / 4 := by
    have h_le : δ ≤ hV.coercive_const / (4 * (hV.local_const + 1)) := min_le_right _ _
    calc hV.local_const * δ
        ≤ hV.local_const * (hV.coercive_const / (4 * (hV.local_const + 1))) :=
          mul_le_mul_of_nonneg_left h_le hCs_nn
      _ = (hV.local_const / (hV.local_const + 1)) * (hV.coercive_const / 4) := by field_simp
      _ ≤ 1 * (hV.coercive_const / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : (0:ℝ) ≤ hV.coercive_const / 4)
          rw [div_le_one hCs1_pos]; linarith
      _ = hV.coercive_const / 4 := one_mul _
  have hδ_sq_pos : 0 < δ ^ 2 := by positivity
  have hδ_cube_pos : 0 < δ ^ 3 := by positivity
  have hc4_pos : 0 < hV.coercive_const / 4 := by linarith
  -- Polynomial-Gaussian moments (k=4,6,8,10).
  have hM4 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc4_pos 4
  have hM6 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc4_pos 6
  have hM8 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc4_pos 8
  have hM10 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc4_pos 10
  set La : ℝ := ∑ i, |a i| with hLa_def
  have hLa_nn : 0 ≤ La := by rw [hLa_def]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  -- Local moment integral.
  set M_loc : ℝ := ∫ u : ι → ℝ,
      (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
        Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) with hM_loc_def
  have hM_loc_int : Integrable (fun u : ι → ℝ =>
      (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
        Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))) := by
    have h_sum : Integrable (fun u : ι → ℝ =>
        ‖u‖ ^ 6 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))
          + ‖u‖ ^ 8 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))
          + ‖u‖ ^ 10 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))) :=
      ((hM6.add hM8).add hM10)
    apply h_sum.congr
    filter_upwards with u
    ring
  have hM_loc_nn : 0 ≤ M_loc := by
    rw [hM_loc_def]; apply MeasureTheory.integral_nonneg; intro u; positivity
  -- Tail moment integral.
  set M_tail : ℝ := ∫ u : ι → ℝ,
      (‖u‖ ^ 4 + ‖u‖ ^ 6) *
        Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) with hM_tail_def
  have hM_tail_int : Integrable (fun u : ι → ℝ =>
      (‖u‖ ^ 4 + ‖u‖ ^ 6) *
        Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))) := by
    have h_sum : Integrable (fun u : ι → ℝ =>
        ‖u‖ ^ 4 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))
          + ‖u‖ ^ 6 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))) :=
      (hM4.add hM6)
    apply h_sum.congr
    filter_upwards with u
    ring
  have hM_tail_nn : 0 ≤ M_tail := by
    rw [hM_tail_def]; apply MeasureTheory.integral_nonneg; intro u; positivity
  -- Constants.
  set C_loc : ℝ := La * (hV.Q_const + 2 * hV.jet_const * hV.local_const +
    hV.local_const ^ 3) with hC_loc_def
  have hC_loc_nn : 0 ≤ C_loc := by
    rw [hC_loc_def]
    have h_jc_nn : 0 ≤ hV.jet_const * hV.local_const := mul_nonneg hjet_C_nn hCs_nn
    have h_cs3_nn : 0 ≤ hV.local_const ^ 3 := by positivity
    have : 0 ≤ hV.Q_const + 2 * hV.jet_const * hV.local_const + hV.local_const ^ 3 := by
      linarith
    exact mul_nonneg hLa_nn this
  set C_tail : ℝ := La * (4 / δ ^ 3 + ‖hV.T‖ / (3 * δ ^ 2)) with hC_tail_def
  have hC_tail_nn : 0 ≤ C_tail := by rw [hC_tail_def]; positivity
  set K : ℝ := (C_loc * M_loc + C_tail * M_tail) / 2 with hK_def
  refine ⟨K, 1, le_refl _, ?_⟩
  intro t ht1
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have ht_sq_pos : 0 < t ^ 2 := pow_pos ht_pos 2
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have h_sym := expNumErr₃_symmetric V H a hV.toPotentialTensorApprox ht_pos
  -- Define summed majorant G_t(u) := G_loc(u) + G_tail(u).
  set G_loc : (ι → ℝ) → ℝ := fun u =>
    (C_loc / t ^ 2) * (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
      Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) with hG_loc_def
  set G_tail : (ι → ℝ) → ℝ := fun u =>
    (C_tail / t ^ 2) * (‖u‖ ^ 4 + ‖u‖ ^ 6) *
      Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) with hG_tail_def
  have hG_loc_nn : ∀ u, 0 ≤ G_loc u := by intro u; rw [hG_loc_def]; positivity
  have hG_tail_nn : ∀ u, 0 ≤ G_tail u := by intro u; rw [hG_tail_def]; positivity
  have hG_loc_int : Integrable G_loc := by
    rw [hG_loc_def]
    have := hM_loc_int.const_mul (C_loc / t ^ 2)
    convert this using 1; funext u; ring
  have hG_tail_int : Integrable G_tail := by
    rw [hG_tail_def]
    have := hM_tail_int.const_mul (C_tail / t ^ 2)
    convert this using 1; funext u; ring
  have hG_sum_int : Integrable (fun u => G_loc u + G_tail u) :=
    hG_loc_int.add hG_tail_int
  -- Pointwise: |F u| ≤ G_loc u + G_tail u via case split.
  have h_pointwise : ∀ u : ι → ℝ,
      ‖expNumLin a t u *
          ((Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t u)
            - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
          gaussianWeight H u‖ ≤ G_loc u + G_tail u := by
    intro u
    rw [Real.norm_eq_abs]
    by_cases hu : ‖u‖ ≤ δ * Real.sqrt t
    · have h_loc := J3_local_pointwise_le V H a hV hδ_pos hδ_le_R hδ_le_jet_R
        hδ_const ht_pos u hu
      have h_tail_nn : 0 ≤ G_tail u := hG_tail_nn u
      have h_loc_eq : G_loc u = (La * (hV.Q_const + 2 * hV.jet_const * hV.local_const +
            hV.local_const ^ 3) / t ^ 2) *
          (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
          Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
        rw [hG_loc_def, hC_loc_def]
      linarith [h_loc, h_tail_nn, h_loc_eq.le, h_loc_eq.ge]
    · push_neg at hu
      have h_tail := J3_tail_pointwise_le V H a hV hδ_pos hc_pos rfl h_coer ht_pos u hu
      have h_loc_nn : 0 ≤ G_loc u := hG_loc_nn u
      have h_tail_eq : G_tail u = (La * (4 / δ ^ 3 + ‖hV.T‖ / (3 * δ ^ 2)) / t ^ 2) *
          (‖u‖ ^ 4 + ‖u‖ ^ 6) *
          Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
        rw [hG_tail_def, hC_tail_def]
      linarith [h_tail, h_loc_nn, h_tail_eq.le, h_tail_eq.ge]
  -- Apply norm_integral_le_of_norm_le.
  have h_main : ‖∫ u : ι → ℝ,
        expNumLin a t u *
            ((Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t u)
              - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                  + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
            gaussianWeight H u‖
      ≤ ∫ u : ι → ℝ, G_loc u + G_tail u := by
    apply norm_integral_le_of_norm_le hG_sum_int
    filter_upwards with u
    exact h_pointwise u
  -- Compute ∫ G_loc + ∫ G_tail.
  have h_int_sum : ∫ u : ι → ℝ, G_loc u + G_tail u
      = (C_loc * M_loc + C_tail * M_tail) / t ^ 2 := by
    rw [integral_add hG_loc_int hG_tail_int]
    rw [hG_loc_def, hG_tail_def, hM_loc_def, hM_tail_def]
    rw [show (fun u : ι → ℝ =>
            C_loc / t ^ 2 * (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)))
          = (fun u => (C_loc / t ^ 2) *
              ((‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
                Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)))) from by
        funext u; ring]
    rw [show (fun u : ι → ℝ =>
            C_tail / t ^ 2 * (‖u‖ ^ 4 + ‖u‖ ^ 6) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)))
          = (fun u => (C_tail / t ^ 2) *
              ((‖u‖ ^ 4 + ‖u‖ ^ 6) *
                Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)))) from by
        funext u; ring]
    rw [integral_const_mul, integral_const_mul]
    ring
  -- Conclude.
  have h_2J3_le : |2 * expNumErr₃ V H hV.toPotentialTensorApprox a t|
      ≤ (C_loc * M_loc + C_tail * M_tail) / t ^ 2 := by
    rw [h_sym]
    calc |∫ u : ι → ℝ,
            expNumLin a t u *
              ((Real.exp (-(rescaledPerturbation V H t u)) - 1
                  + expPotCubic V H hV.toPotentialTensorApprox t u)
                - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                    + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
              gaussianWeight H u|
        = ‖∫ u : ι → ℝ,
            expNumLin a t u *
              ((Real.exp (-(rescaledPerturbation V H t u)) - 1
                  + expPotCubic V H hV.toPotentialTensorApprox t u)
                - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                    + expPotCubic V H hV.toPotentialTensorApprox t (-u))) *
              gaussianWeight H u‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ u : ι → ℝ, G_loc u + G_tail u := h_main
      _ = (C_loc * M_loc + C_tail * M_tail) / t ^ 2 := h_int_sum
  have h_abs_2 : |2 * expNumErr₃ V H hV.toPotentialTensorApprox a t|
      = 2 * |expNumErr₃ V H hV.toPotentialTensorApprox a t| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [h_abs_2] at h_2J3_le
  rw [hK_def, show (C_loc * M_loc + C_tail * M_tail) / 2 / t ^ 2
        = (C_loc * M_loc + C_tail * M_tail) / t ^ 2 / 2 from by ring]
  linarith

set_option maxHeartbeats 1600000 in
/-- **J₄ bound**: centered quadratic observable jet × `(e^{-s_t} - 1)` is `O(t⁻²)`.

Uses the `u ↦ -u` parity symmetrization:
`J₄ = (1/2) ∫ (Q_t(u)-μ/t) · [R(u) + R(-u)] · gW(u) du` where
`R(u) = e^{-s_t(u)} - 1`. The even part `R(u) + R(-u)` is `O(t⁻¹)`
because the leading `√t⁻¹·C_t` part is odd and cancels in the sum. -/
private lemma expNumErr₄_bound
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₄ V φ a H Hinv hV hφ t| ≤ K / t ^ 2 := by
  -- Setup constants from hV.
  have hc_pos : 0 < hV.coercive_const := hV.coercive_const_pos
  have h_coer : ∀ w : ι → ℝ, hV.coercive_const * ‖w‖ ^ 2 ≤ V w := hV.coercive_bound
  have hCs_nn : 0 ≤ hV.local_const := hV.local_const_nonneg
  have hR_pos : 0 < hV.local_radius := hV.local_radius_pos
  have hjet_R_pos : 0 < hV.jet_radius := hV.jet_radius_pos
  have hjet_C_nn : 0 ≤ hV.jet_const := hV.jet_const_nonneg
  -- Choose δ for the local region.
  have hCs1_pos : (0 : ℝ) < hV.local_const + 1 := by linarith
  set δ : ℝ := min (min hV.local_radius hV.jet_radius)
      (hV.coercive_const / (4 * (hV.local_const + 1))) with hδ_def
  have hδ_pos : 0 < δ :=
    lt_min (lt_min hR_pos hjet_R_pos) (by positivity)
  have hδ_le_R : δ ≤ hV.local_radius :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ_le_jet_R : δ ≤ hV.jet_radius :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ_const : hV.local_const * δ ≤ hV.coercive_const / 4 := by
    have h_le : δ ≤ hV.coercive_const / (4 * (hV.local_const + 1)) :=
      min_le_right _ _
    calc hV.local_const * δ
        ≤ hV.local_const *
            (hV.coercive_const / (4 * (hV.local_const + 1))) :=
          mul_le_mul_of_nonneg_left h_le hCs_nn
      _ = (hV.local_const / (hV.local_const + 1)) * (hV.coercive_const / 4) := by
          field_simp
      _ ≤ 1 * (hV.coercive_const / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : (0:ℝ) ≤ hV.coercive_const / 4)
          rw [div_le_one hCs1_pos]; linarith
      _ = hV.coercive_const / 4 := one_mul _
  have hδ_sq_pos : 0 < δ ^ 2 := by positivity
  -- Gaussian moment dominator: ∫ (1 + ‖u‖^8) · exp(-(c/4)‖u‖²).
  have hc4_pos : 0 < hV.coercive_const / 4 := by linarith
  set M : ℝ := ∫ u : ι → ℝ,
      (1 + ‖u‖ ^ 8) * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) with hM_def
  have hM_int : Integrable (fun u : ι → ℝ =>
      (1 + ‖u‖ ^ 8) * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))) := by
    have h0 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc4_pos 0
    have h8 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc4_pos 8
    have h_sum : Integrable (fun u : ι → ℝ =>
        ‖u‖ ^ 0 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))
          + ‖u‖ ^ 8 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))) := h0.add h8
    apply h_sum.congr
    filter_upwards with u
    rw [pow_zero]; ring
  have hM_nn : 0 ≤ M := by
    rw [hM_def]; apply MeasureTheory.integral_nonneg
    intro u; positivity
  -- Constants for B and bracket bounds.
  set Cμ : ℝ := |expNumeratorCoeff V φ H Hinv a hV hφ| with hCμ_def
  have hCμ_nn : 0 ≤ Cμ := abs_nonneg _
  -- b := bound on t·|B(u)|/(1+‖u‖²): |B| ≤ b·(1+‖u‖²)/t.
  set b : ℝ := Fintype.card ι * ‖hφ.A‖ / 2 + Cμ with hb_def
  have hb_nn : 0 ≤ b := by rw [hb_def]; positivity
  -- D := jet_C + Cs² (combined bracket constant for unified poly).
  set D : ℝ := hV.jet_const + hV.local_const ^ 2 with hD_def
  have hD_nn : 0 ≤ D := by rw [hD_def]; positivity
  -- Unified majorant constant.
  set K_unified : ℝ := 8 * b * (D + 1 / δ ^ 2) with hKun_def
  have hKun_nn : 0 ≤ K_unified := by rw [hKun_def]; positivity
  set K : ℝ := K_unified * M / 2 with hK_def
  refine ⟨K, 1, le_refl _, ?_⟩
  intro t ht1
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have ht_sq_pos : 0 < t ^ 2 := pow_pos ht_pos 2
  -- Apply symmetrization: 2·J₄ = ∫ (B · bracket · gW).
  have h_sym := expNumErr₄_symmetric V φ H Hinv a hV hφ ht_pos
  -- Define unified majorant G.
  set G : (ι → ℝ) → ℝ := fun u =>
    (K_unified / t ^ 2) * (1 + ‖u‖ ^ 8) *
      Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) with hG_def
  have hG_nn : ∀ u, 0 ≤ G u := by
    intro u; rw [hG_def]; positivity
  have hG_int : Integrable G := by
    rw [hG_def]
    have := hM_int.const_mul (K_unified / t ^ 2)
    convert this using 1; funext u; ring
  -- KEY POINTWISE BOUND: |B · bracket · gW| ≤ G(u).
  have h_pointwise : ∀ u : ι → ℝ,
      ‖(expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
          ((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
            (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)) *
          gaussianWeight H u‖ ≤ G u := by
    intro u
    rw [Real.norm_eq_abs]
    -- Rearrange product as |B| · |gW · bracket|.
    rw [show (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
            ((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
              (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)) *
            gaussianWeight H u
          = (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
            (gaussianWeight H u *
              ((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))) from by ring,
        abs_mul]
    -- |B| bound: |B| ≤ b·(1+‖u‖²)/t.
    have h_B_bound : |expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t|
        ≤ b * (1 + ‖u‖ ^ 2) / t := by
      have h := abs_expNumQuad_sub_coeff_le V φ H Hinv a hV hφ ht_pos u
      have h_card_nn : (0 : ℝ) ≤ Fintype.card ι * ‖hφ.A‖ := by positivity
      calc |expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t|
          ≤ (Fintype.card ι * ‖hφ.A‖ / (2 * t)) * ‖u‖ ^ 2 + Cμ / t := h
        _ = ((Fintype.card ι * ‖hφ.A‖ / 2) * ‖u‖ ^ 2 + Cμ) / t := by
            field_simp
        _ ≤ b * (1 + ‖u‖ ^ 2) / t := by
            apply div_le_div_of_nonneg_right _ ht_pos.le
            rw [hb_def]
            nlinarith [sq_nonneg ‖u‖, h_card_nn, hCμ_nn]
    have h_B_nn : 0 ≤ b * (1 + ‖u‖ ^ 2) / t := by
      apply div_nonneg _ ht_pos.le
      apply mul_nonneg hb_nn (by linarith [sq_nonneg ‖u‖])
    -- gW nonnegativity for `|gW · X| = gW · |X|`.
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    have h_gW_bracket_eq :
        |gaussianWeight H u *
            ((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
              (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))|
          = gaussianWeight H u *
            |(Real.exp (-(rescaledPerturbation V H t u)) - 1) +
              (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)| := by
      rw [abs_mul, abs_of_nonneg h_gW_nn]
    -- Helper: each ‖u‖^k ≤ 1 + ‖u‖^8 for k = 2, 4, 6.
    have h_pow_le_8 : ∀ k : ℕ, k ≤ 8 → ‖u‖ ^ k ≤ 1 + ‖u‖ ^ 8 := by
      intro k hk
      have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
      by_cases h1u : ‖u‖ ≤ 1
      · have : ‖u‖ ^ k ≤ 1 := pow_le_one₀ h_norm_nn h1u
        have h8 : 0 ≤ ‖u‖ ^ 8 := pow_nonneg h_norm_nn _
        linarith
      · push_neg at h1u
        have : ‖u‖ ^ k ≤ ‖u‖ ^ 8 := pow_le_pow_right₀ h1u.le hk
        linarith
    have h_u2 : ‖u‖ ^ 2 ≤ 1 + ‖u‖ ^ 8 := h_pow_le_8 2 (by omega)
    have h_u4 : ‖u‖ ^ 4 ≤ 1 + ‖u‖ ^ 8 := h_pow_le_8 4 (by omega)
    have h_u6 : ‖u‖ ^ 6 ≤ 1 + ‖u‖ ^ 8 := h_pow_le_8 6 (by omega)
    have h_u8 : ‖u‖ ^ 8 ≤ 1 + ‖u‖ ^ 8 := by linarith [pow_nonneg (norm_nonneg u) 8]
    by_cases hu : ‖u‖ ≤ δ * Real.sqrt t
    · -- LOCAL CASE: ‖u‖ ≤ δ·√t.
      have h_bracket_loc :=
        abs_J4_bracket_local_le V H hV hδ_pos hδ_le_R hδ_le_jet_R hδ_const ht_pos u hu
      have h_gW_le := gaussianWeight_le_exp_neg_coercive V H hV u
      -- Bound `gW · |bracket|` by combining h_gW_le and h_bracket_loc.
      have h_bracket_nn : 0 ≤ |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))| := abs_nonneg _
      have h_exp_c2_le_c4 : Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2))
          ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg ‖u‖, hc_pos]
      -- gW · |bracket| ≤ 2·D·(‖u‖^4 + ‖u‖^6)·exp(-(c/4)‖u‖²)/t.
      have h_gWbr_local :
          gaussianWeight H u *
              |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))|
            ≤ 2 * D * (‖u‖ ^ 4 + ‖u‖ ^ 6) *
                Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) / t := by
        calc gaussianWeight H u *
                |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                  (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))|
            ≤ Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2)) *
                (2 * hV.jet_const * ‖u‖ ^ 4 / t
                  + 2 * hV.local_const ^ 2 * ‖u‖ ^ 6 *
                      Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) / t) := by
              apply mul_le_mul h_gW_le h_bracket_loc h_bracket_nn (Real.exp_pos _).le
          _ = 2 * hV.jet_const * ‖u‖ ^ 4 *
                Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2)) / t
              + 2 * hV.local_const ^ 2 * ‖u‖ ^ 6 *
                (Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) *
                  Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2))) / t := by ring
          _ = 2 * hV.jet_const * ‖u‖ ^ 4 *
                Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2)) / t
              + 2 * hV.local_const ^ 2 * ‖u‖ ^ 6 *
                Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) / t := by
              rw [show Real.exp ((hV.coercive_const / 4) * ‖u‖ ^ 2) *
                    Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2))
                  = Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) from by
                rw [← Real.exp_add]
                congr 1; ring]
          _ ≤ 2 * hV.jet_const * ‖u‖ ^ 4 *
                Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) / t
              + 2 * hV.local_const ^ 2 * ‖u‖ ^ 6 *
                Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) / t := by
              gcongr
          _ = (2 * hV.jet_const * ‖u‖ ^ 4 +
                2 * hV.local_const ^ 2 * ‖u‖ ^ 6) *
                Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) / t := by ring
          _ ≤ 2 * D * (‖u‖ ^ 4 + ‖u‖ ^ 6) *
                Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) / t := by
              apply div_le_div_of_nonneg_right _ ht_pos.le
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              rw [hD_def]
              have h_u4_nn : 0 ≤ ‖u‖ ^ 4 := pow_nonneg (norm_nonneg _) _
              have h_u6_nn : 0 ≤ ‖u‖ ^ 6 := pow_nonneg (norm_nonneg _) _
              have h_Cs_sq_nn : 0 ≤ hV.local_const ^ 2 := sq_nonneg _
              nlinarith
      have h_gWbr_nn : 0 ≤ gaussianWeight H u *
            |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
              (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))| :=
        mul_nonneg h_gW_nn (abs_nonneg _)
      rw [h_gW_bracket_eq]
      -- Combine: |B| · (gW · |bracket|) ≤ b·(1+‖u‖²)/t · 2D·(‖u‖^4+‖u‖^6)·exp(-(c/4)‖u‖²)/t.
      calc |expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t| *
              (gaussianWeight H u *
                |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                  (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))|)
          ≤ (b * (1 + ‖u‖ ^ 2) / t) *
              (2 * D * (‖u‖ ^ 4 + ‖u‖ ^ 6) *
                Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) / t) := by
            exact mul_le_mul h_B_bound h_gWbr_local h_gWbr_nn h_B_nn
        _ = (2 * b * D / t ^ 2) *
              ((1 + ‖u‖ ^ 2) * (‖u‖ ^ 4 + ‖u‖ ^ 6)) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
            have ht_ne : t ≠ 0 := ne_of_gt ht_pos
            field_simp
        _ ≤ (2 * b * D / t ^ 2) * (4 * (1 + ‖u‖ ^ 8)) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            -- (1 + ‖u‖²)(‖u‖^4 + ‖u‖^6) = ‖u‖^4 + 2‖u‖^6 + ‖u‖^8 ≤ 4·(1+‖u‖^8).
            have h_expand : (1 + ‖u‖ ^ 2) * (‖u‖ ^ 4 + ‖u‖ ^ 6)
                = ‖u‖ ^ 4 + ‖u‖ ^ 6 + ‖u‖ ^ 6 + ‖u‖ ^ 8 := by ring
            rw [h_expand]
            linarith [h_u4, h_u6, h_u8]
        _ = (8 * b * D / t ^ 2) * (1 + ‖u‖ ^ 8) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by ring
        _ ≤ (K_unified / t ^ 2) * (1 + ‖u‖ ^ 8) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_right _ (by linarith [pow_nonneg (norm_nonneg u) 8])
            rw [hKun_def]
            apply div_le_div_of_nonneg_right _ ht_sq_pos.le
            -- 8bD ≤ 8b(D + 1/δ²).
            have h_inv_nn : 0 ≤ 1 / δ ^ 2 := by positivity
            nlinarith
        _ = G u := by rw [hG_def]
    · -- TAIL CASE: ‖u‖ > δ·√t.
      push_neg at hu
      have h_uniform := abs_gW_J4_bracket_le_uniform V H hc_pos h_coer ht_pos u
      -- Switch from `|gW · bracket| ≤ ...` (bound on |...|) to `gW · |bracket| ≤ ...`.
      -- Note h_uniform: |gW · bracket| ≤ 2·gW + 2·exp(-c·‖u‖²).
      -- And |gW · bracket| = gW · |bracket|, so gW · |bracket| ≤ 2·gW + 2·exp(-c·‖u‖²).
      have h_gWbr_uniform :
          gaussianWeight H u *
              |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))|
            ≤ 2 * gaussianWeight H u + 2 * Real.exp (-(hV.coercive_const * ‖u‖ ^ 2)) := by
        rw [← h_gW_bracket_eq]; exact h_uniform
      -- Bound by 4·exp(-(c/4)‖u‖²).
      have h_gW_le := gaussianWeight_le_exp_neg_coercive V H hV u
      have h_exp_c2_le_c4 : Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2))
          ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg ‖u‖, hc_pos]
      have h_exp_c_le_c4 : Real.exp (-(hV.coercive_const * ‖u‖ ^ 2))
          ≤ Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg ‖u‖, hc_pos]
      have h_gWbr_4 :
          gaussianWeight H u *
              |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))|
            ≤ 4 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
        calc gaussianWeight H u *
                |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                  (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))|
            ≤ 2 * gaussianWeight H u + 2 * Real.exp (-(hV.coercive_const * ‖u‖ ^ 2)) :=
              h_gWbr_uniform
          _ ≤ 2 * Real.exp (-((hV.coercive_const / 2) * ‖u‖ ^ 2))
              + 2 * Real.exp (-(hV.coercive_const * ‖u‖ ^ 2)) := by
              linarith [h_gW_le]
          _ ≤ 2 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))
              + 2 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
              linarith [h_exp_c2_le_c4, h_exp_c_le_c4]
          _ = 4 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by ring
      have h_gWbr_4_nn : 0 ≤ 4 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
        positivity
      rw [h_gW_bracket_eq]
      -- |B| · (gW · |bracket|) ≤ (b·(1+‖u‖²)/t) · 4·exp(-(c/4)‖u‖²).
      -- Then absorb 1/t by 1/t ≤ ‖u‖²/(δ²·t²).
      have h_norm_sq_lb : δ ^ 2 * t < ‖u‖ ^ 2 := by
        have h1 : 0 ≤ δ * Real.sqrt t := by positivity
        have h2 := mul_self_lt_mul_self h1 hu
        rw [show (δ * Real.sqrt t) * (δ * Real.sqrt t) = (δ * Real.sqrt t) ^ 2 from by ring,
            show ‖u‖ * ‖u‖ = ‖u‖ ^ 2 from by ring] at h2
        rw [mul_pow, Real.sq_sqrt ht_pos.le] at h2
        exact h2
      have h_t_inv : (1 : ℝ) / t ≤ ‖u‖ ^ 2 / (δ ^ 2 * t ^ 2) := by
        rw [div_le_div_iff₀ ht_pos (by positivity : (0:ℝ) < δ^2 * t^2)]
        -- 1·(δ²·t²) ≤ ‖u‖²·t.
        calc (1 : ℝ) * (δ ^ 2 * t ^ 2) = (δ ^ 2 * t) * t := by ring
          _ ≤ ‖u‖ ^ 2 * t := by
              apply mul_le_mul_of_nonneg_right h_norm_sq_lb.le ht_pos.le
      calc |expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t| *
              (gaussianWeight H u *
                |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                  (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))|)
          ≤ (b * (1 + ‖u‖ ^ 2) / t) *
              (4 * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2))) := by
            have h_gWbr_nn : 0 ≤ gaussianWeight H u *
                |((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                  (Real.exp (-(rescaledPerturbation V H t (-u))) - 1))| :=
              mul_nonneg h_gW_nn (abs_nonneg _)
            exact mul_le_mul h_B_bound h_gWbr_4 h_gWbr_nn h_B_nn
        _ = 4 * b * (1 + ‖u‖ ^ 2) * (1 / t) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by ring
        _ ≤ 4 * b * (1 + ‖u‖ ^ 2) * (‖u‖ ^ 2 / (δ ^ 2 * t ^ 2)) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_left h_t_inv
            apply mul_nonneg (mul_nonneg (by norm_num) hb_nn)
            linarith [sq_nonneg ‖u‖]
        _ = (4 * b / δ ^ 2 / t ^ 2) * ((1 + ‖u‖ ^ 2) * ‖u‖ ^ 2) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
            have ht_ne : t ≠ 0 := ne_of_gt ht_pos
            have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
            field_simp
        _ ≤ (4 * b / δ ^ 2 / t ^ 2) * (2 * (1 + ‖u‖ ^ 8)) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            -- (1 + ‖u‖²)·‖u‖² = ‖u‖² + ‖u‖^4 ≤ 2·(1+‖u‖^8).
            have h_expand : (1 + ‖u‖ ^ 2) * ‖u‖ ^ 2 = ‖u‖ ^ 2 + ‖u‖ ^ 4 := by ring
            rw [h_expand]
            linarith [h_u2, h_u4]
        _ = (8 * b / δ ^ 2 / t ^ 2) * (1 + ‖u‖ ^ 8) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by ring
        _ ≤ (K_unified / t ^ 2) * (1 + ‖u‖ ^ 8) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_right _ (by linarith [pow_nonneg (norm_nonneg u) 8])
            rw [hKun_def]
            -- 8b/δ² ≤ 8b·(D + 1/δ²). Compare 1/δ² ≤ D + 1/δ² (since D ≥ 0).
            rw [show (8 * b * (D + 1 / δ ^ 2) : ℝ) / t ^ 2
                  = (8 * b * D + 8 * b / δ ^ 2) / t ^ 2 from by ring,
                show (8 * b / δ ^ 2 / t ^ 2 : ℝ)
                  = (0 + 8 * b / δ ^ 2) / t ^ 2 from by ring]
            apply div_le_div_of_nonneg_right _ ht_sq_pos.le
            have h_8bD_nn : 0 ≤ 8 * b * D := by positivity
            linarith
        _ = G u := by rw [hG_def]
  -- Apply norm_integral_le_of_norm_le to bound |∫ ...| by ∫ G.
  have h_main : ‖∫ u : ι → ℝ,
        (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
            ((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
              (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)) *
            gaussianWeight H u‖
      ≤ ∫ u : ι → ℝ, G u :=
    norm_integral_le_of_norm_le hG_int (Filter.Eventually.of_forall h_pointwise)
  -- Compute ∫ G.
  have h_intG : ∫ u : ι → ℝ, G u = K_unified * M / t ^ 2 := by
    rw [hG_def, hM_def]
    rw [show (fun u : ι → ℝ =>
            K_unified / t ^ 2 * (1 + ‖u‖ ^ 8) *
              Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)))
          = (fun u => (K_unified / t ^ 2) *
              ((1 + ‖u‖ ^ 8) * Real.exp (-((hV.coercive_const / 4) * ‖u‖ ^ 2)))) from by
        funext u; ring]
    rw [integral_const_mul]
    ring
  -- Combine: 2·|J₄| = |2·J₄| = |∫ ...| ≤ ∫G = K_unified·M/t², so |J₄| ≤ K/t².
  have h_2J4_le : |2 * expNumErr₄ V φ a H Hinv hV hφ t| ≤ K_unified * M / t ^ 2 := by
    rw [h_sym]
    calc |∫ u : ι → ℝ,
            (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
              ((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)) *
              gaussianWeight H u|
        = ‖∫ u : ι → ℝ,
            (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
              ((Real.exp (-(rescaledPerturbation V H t u)) - 1) +
                (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)) *
              gaussianWeight H u‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ u : ι → ℝ, G u := h_main
      _ = K_unified * M / t ^ 2 := h_intG
  have h_abs_2 : |2 * expNumErr₄ V φ a H Hinv hV hφ t|
      = 2 * |expNumErr₄ V φ a H Hinv hV hφ t| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [h_abs_2] at h_2J4_le
  -- 2·|J₄| ≤ K_unified·M/t², so |J₄| ≤ K_unified·M/(2t²) = K/t².
  rw [hK_def, show K_unified * M / 2 / t ^ 2 = K_unified * M / t ^ 2 / 2 from by ring]
  linarith

/-- **Centered EXP numerator (sharp rate)**: the centered numerator
`rescaledNumerator V t φ - rescaledPartition V t · μ/t` is `O(t⁻²)`,
where `μ := (tr(AΣ) - dot(Hinv a)(T:Σ))/2` is the explicit `lem:laplace_exp`
coefficient.

Proven by combining the 4 sub-bounds via the triangle inequality. -/
private theorem rescaledNumerator_first_order_centered_explicit
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |rescaledNumerator V t φ
        - rescaledPartition V t *
            (expNumeratorCoeff V φ H Hinv a hV.toPotentialTensorApprox hφ / t)|
        ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hT₁, h₁⟩ :=
    expNumErr₁_bound (V := V) (φ := φ) (H := H) (Hinv := Hinv)
      (a := a) hV.toPotentialTensorApprox hφ hGauss
  obtain ⟨K₂, T₂, hT₂, h₂⟩ :=
    expNumErr₂_bound (V := V) (φ := φ) (H := H) (Hinv := Hinv)
      (a := a) hV.toPotentialTensorApprox hφ hGauss
  obtain ⟨K₃, T₃, hT₃, h₃⟩ :=
    expNumErr₃_bound (V := V) (H := H) (Hinv := Hinv)
      (a := a) hV hGauss
  obtain ⟨K₄, T₄, hT₄, h₄⟩ :=
    expNumErr₄_bound (V := V) (φ := φ) (H := H) (Hinv := Hinv)
      (a := a) hV.toPotentialTensorApprox hφ hGauss
  refine ⟨K₁ + K₂ + K₃ + K₄, max (max T₁ T₂) (max T₃ T₄), ?_, ?_⟩
  · exact le_trans hT₁ (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro t ht
    have ht1 : T₁ ≤ t :=
      le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht)
    have ht2 : T₂ ≤ t :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ht)
    have ht3 : T₃ ≤ t :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) ht)
    have ht4 : T₄ ≤ t :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) ht)
    have ht_pos : 0 < t :=
      lt_of_lt_of_le zero_lt_one (le_trans hT₁ ht1)
    have hdecomp :=
      expNumerator_centered_decomp (V := V) (φ := φ) (H := H) (Hinv := Hinv)
        (a := a) hV.toPotentialTensorApprox hφ hGauss ht_pos
    rw [hdecomp]
    have hK1 := h₁ t ht1
    have hK2 := h₂ t ht2
    have hK3 := h₃ t ht3
    have hK4 := h₄ t ht4
    have ht_sq_pos : 0 < t ^ 2 := by positivity
    calc |expNumErr₁ V φ a H hφ t + expNumErr₂ V φ a H hφ t
            + expNumErr₃ V H hV.toPotentialTensorApprox a t
            + expNumErr₄ V φ a H Hinv hV.toPotentialTensorApprox hφ t|
        ≤ |expNumErr₁ V φ a H hφ t| + |expNumErr₂ V φ a H hφ t|
            + |expNumErr₃ V H hV.toPotentialTensorApprox a t|
            + |expNumErr₄ V φ a H Hinv hV.toPotentialTensorApprox hφ t| := by
          calc |expNumErr₁ V φ a H hφ t + expNumErr₂ V φ a H hφ t
                  + expNumErr₃ V H hV.toPotentialTensorApprox a t
                  + expNumErr₄ V φ a H Hinv hV.toPotentialTensorApprox hφ t|
              ≤ |expNumErr₁ V φ a H hφ t + expNumErr₂ V φ a H hφ t
                  + expNumErr₃ V H hV.toPotentialTensorApprox a t|
                + |expNumErr₄ V φ a H Hinv hV.toPotentialTensorApprox hφ t| :=
                  abs_add_le _ _
            _ ≤ (|expNumErr₁ V φ a H hφ t + expNumErr₂ V φ a H hφ t|
                  + |expNumErr₃ V H hV.toPotentialTensorApprox a t|)
                + |expNumErr₄ V φ a H Hinv hV.toPotentialTensorApprox hφ t| := by
                  gcongr; exact abs_add_le _ _
            _ ≤ ((|expNumErr₁ V φ a H hφ t| + |expNumErr₂ V φ a H hφ t|)
                  + |expNumErr₃ V H hV.toPotentialTensorApprox a t|)
                + |expNumErr₄ V φ a H Hinv hV.toPotentialTensorApprox hφ t| := by
                  gcongr; exact abs_add_le _ _
            _ = _ := by ring
      _ ≤ K₁ / t ^ 2 + K₂ / t ^ 2 + K₃ / t ^ 2 + K₄ / t ^ 2 := by
          gcongr
      _ = (K₁ + K₂ + K₃ + K₄) / t ^ 2 := by ring

/-- **Sharp expectation rate (explicit coefficient, `lem:laplace_exp`)**:
for $\phi$ with $\phi(0) = 0$,
$$
  \langle\phi\rangle_t = \tfrac{1}{2t}\big[\mathrm{tr}(A\Sigma)
    - (\Sigma\,\nabla\phi(0))\!\cdot\!(T{:}\Sigma)\big] + O(t^{-2}),
$$
where $A = \nabla^2\phi(0)$, $T = \nabla^3 V(0)$, $\Sigma = H^{-1}$.

The Lean theorem packages this as: there exist constants $K, T_0$ with
$T_0 \ge 1$ such that for all $t \ge T_0$,
$$
  \big| 2t\,\langle\phi\rangle_t - \mathrm{tr}(A\Sigma)
    + (\Sigma\,\nabla\phi(0))\!\cdot\!(T{:}\Sigma) \big| \le K/t.
$$ -/
theorem gibbsExpectation_first_order_rate_explicit
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |2 * t * gibbsExpectation V t φ - trASig hφ.A Hinv
          + dot (Hinv a) (tensorContractMatrix hV.T Hinv)| ≤ K / t := by
  -- Reduce to centered-numerator helper + partition lower bound.
  set μ : ℝ := expNumeratorCoeff V φ H Hinv a hV.toPotentialTensorApprox hφ with hμ_def
  set c : ℝ := trASig hφ.A Hinv -
      dot (Hinv a) (tensorContractMatrix hV.T Hinv) with hc_def
  have hc_eq : c = 2 * μ := by
    rw [hμ_def, hc_def, expNumeratorCoeff]; ring
  obtain ⟨K₁, T₁, hT₁, hNum⟩ :=
    rescaledNumerator_first_order_centered_explicit
      (V := V) (φ := φ) (H := H) (Hinv := Hinv) (a := a) hV hφ hGauss
  obtain ⟨T₂, hT₂, hPart⟩ :=
    rescaledPartition_ge_half_gaussianZ V H Hinv
      hV.toPotentialJetApprox.toPotentialApprox hGauss.toLaplaceCovHypotheses
  have hZ_pos : 0 < gaussianZ H := hGauss.Z_pos
  set K : ℝ := 4 * K₁ / gaussianZ H with hK_def
  refine ⟨K, max T₁ T₂, le_max_of_le_left hT₁, ?_⟩
  intro t ht
  have ht_T1 : T₁ ≤ t := le_of_max_le_left ht
  have ht_T2 : T₂ ≤ t := le_of_max_le_right ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans hT₁ ht_T1)
  have hP_ge : gaussianZ H / 2 ≤ rescaledPartition V t := hPart t ht_T2
  have hP_pos : 0 < rescaledPartition V t := lt_of_lt_of_le (by linarith) hP_ge
  -- Rewrite gibbsExpectation via the rescaled bridge.
  rw [gibbsExpectation_eq_rescaledExpectation V φ ht_pos]
  unfold rescaledExpectation
  -- Goal: |2*t * (rescaledNumerator V t φ / rescaledPartition V t) - c| ≤ K/t
  -- = |((2*t) / D_t) * (N_t - D_t * μ/t)| ≤ K/t.
  -- Re-express the goal LHS in terms of `c`.
  have hgoal_eq : 2 * t * (rescaledNumerator V t φ / rescaledPartition V t)
        - trASig hφ.A Hinv + dot (Hinv a) (tensorContractMatrix hV.T Hinv)
      = 2 * t * (rescaledNumerator V t φ / rescaledPartition V t) - c := by
    rw [hc_def]; ring
  rw [hgoal_eq]
  have hAlg : 2 * t * (rescaledNumerator V t φ / rescaledPartition V t) - c
      = ((2 * t) / rescaledPartition V t) *
          (rescaledNumerator V t φ - rescaledPartition V t * (μ / t)) := by
    rw [hc_eq]
    field_simp
  rw [hAlg]
  rw [abs_mul, abs_div, abs_of_pos hP_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
  -- Bound each factor.
  have h2 : |rescaledNumerator V t φ - rescaledPartition V t * (μ / t)| ≤ K₁ / t ^ 2 :=
    hNum t ht_T1
  have h_zsim : (2 * t) / (gaussianZ H / 2) * (K₁ / t ^ 2) = K / t := by
    rw [hK_def]; field_simp; ring
  calc (2 * t) / rescaledPartition V t *
        |rescaledNumerator V t φ - rescaledPartition V t * (μ / t)|
      ≤ (2 * t) / (gaussianZ H / 2) * (K₁ / t ^ 2) := by
        gcongr
    _ = K / t := h_zsim

/-- **Corrected-bracket transformation for an even, Gaussian-centered kernel**
(parity helper P1, transformation half).

For an even kernel `F` (i.e. `F(-u) = F(u)`) with zero Gaussian mean
(`∫ F · gW = 0`) and the integrability witnesses listed below,
\[
  \int F(u)\,gW(u)\,e^{-s_t(u)}\,du =
    \int F(u)\,gW(u)\bigl(e^{-s_t(u)} - 1 + t\cdot c_V((\sqrt t)^{-1}{\cdot}u)\bigr)\,du,
\]
where `c_V` is the `cV` field of `PotentialJetApprox` (the cubic correction).

This is the generic analogue of `integral_centered_bilinear_eq_corrected_bracket`
in `CovarianceSharp.lean`. The proof is purely algebraic + parity:
- the constant-1 piece vanishes by Gaussian-centering of `F`;
- the `t · cV` piece vanishes by parity (`F` even, `cV(·)` odd, `gW` even).

The remaining `∫ F · gW · (exp(-s_t) - 1 + t·cV)` is what the Stage 5 K/t bound
actually controls via the corrected-bracket pointwise estimate
(`abs_corrected_bracket_local_le`). -/
private lemma integral_even_centered_eq_corrected_bracket
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (F : (ι → ℝ) → ℝ) (hF_even : ∀ u, F (-u) = F u)
    (h_F_centered : ∫ u : ι → ℝ, F u * gaussianWeight H u = 0)
    {t : ℝ} (ht_pos : 0 < t)
    (h_int_F_gW : Integrable (fun u : ι → ℝ => F u * gaussianWeight H u))
    (h_int_F_cV : Integrable (fun u : ι → ℝ =>
      F u * gaussianWeight H u * hV.cV ((Real.sqrt t)⁻¹ • u)))
    (h_int_F_exp : Integrable (fun u : ι → ℝ =>
      F u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) :
    ∫ u : ι → ℝ, F u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
      = ∫ u : ι → ℝ, F u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
         t * hV.cV ((Real.sqrt t)⁻¹ • u)) := by
  -- Pointwise: integrand_RHS = F·gW·exp(-s_t) - F·gW + t·F·gW·cV.
  have h_pt : ∀ u : ι → ℝ,
      F u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
         t * hV.cV ((Real.sqrt t)⁻¹ • u))
      = F u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
        - F u * gaussianWeight H u
        + t * (F u * gaussianWeight H u *
              hV.cV ((Real.sqrt t)⁻¹ • u)) := by
    intro u; ring
  rw [show (fun u : ι → ℝ => F u * gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
             t * hV.cV ((Real.sqrt t)⁻¹ • u))) =
        fun u => F u * gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))
            - F u * gaussianWeight H u
            + t * (F u * gaussianWeight H u *
                  hV.cV ((Real.sqrt t)⁻¹ • u)) from funext h_pt]
  -- Integrability of `F · gW · exp(-s_t) - F · gW` (in single-lambda form).
  have h_int_diff : Integrable (fun u : ι → ℝ =>
      F u * gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
        - F u * gaussianWeight H u) := by
    have := h_int_F_exp.sub h_int_F_gW
    apply this.congr
    filter_upwards with u
    simp only [Pi.sub_apply]
  -- Integrability of `t · (F · gW · cV)` (in single-lambda form).
  have h_int_cV : Integrable (fun u : ι → ℝ =>
      t * (F u * gaussianWeight H u *
        hV.cV ((Real.sqrt t)⁻¹ • u))) := h_int_F_cV.const_mul t
  rw [MeasureTheory.integral_add h_int_diff h_int_cV]
  rw [MeasureTheory.integral_sub h_int_F_exp h_int_F_gW]
  rw [h_F_centered]
  -- ∫ t · F · gW · cV = 0 (parity: F even, cV odd, gW even).
  have h_parity : ∫ u : ι → ℝ,
        F u * gaussianWeight H u *
          hV.cV ((Real.sqrt t)⁻¹ • u) = 0 := by
    rw [show (fun u : ι → ℝ => F u * gaussianWeight H u *
              hV.cV ((Real.sqrt t)⁻¹ • u))
            = fun u => (F u * hV.cV ((Real.sqrt t)⁻¹ • u)) *
              gaussianWeight H u from by funext u; ring]
    apply integral_odd_mul_gaussian_eq_zero H
      (fun u => F u * hV.cV ((Real.sqrt t)⁻¹ • u))
    intro u
    have h_smul : (Real.sqrt t)⁻¹ • (-u) = -((Real.sqrt t)⁻¹ • u) := by
      simp [smul_neg]
    rw [show F (-u) * hV.cV ((Real.sqrt t)⁻¹ • -u)
          = F u * hV.cV (-((Real.sqrt t)⁻¹ • u)) from by
        rw [hF_even, h_smul]]
    rw [hV.cV_odd ((Real.sqrt t)⁻¹ • u)]
    ring
  -- Pull `t` out of the cV integral.
  have h_cV_eq : ∫ u : ι → ℝ,
        t * (F u * gaussianWeight H u *
          hV.cV ((Real.sqrt t)⁻¹ • u))
      = t * ∫ u : ι → ℝ, F u * gaussianWeight H u *
          hV.cV ((Real.sqrt t)⁻¹ • u) := by
    rw [MeasureTheory.integral_const_mul]
  rw [h_cV_eq, h_parity]
  ring

/-- **The FQQ kernel** for Lemma B Step 2: doubly-centered quartic
`FQQ(u) = (Q^c_A · Q_B)(u) - c_QQ`, where `Q^c_A := (1/2)Q_A - (1/2)tr(AΣ)`
is the centered quadratic, `Q_B := (1/2) quadForm B`, and
`c_QQ := (1/2) trASig (A∘Hinv) (B∘Hinv)`.

By construction, `∫ FQQ · gW = 0` (centering kills both the quadratic mean
of `Q_A` and the resulting product mean), and `FQQ` is even in `u`. -/
private noncomputable def fqqKernel
    (A B Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) : ℝ :=
  ((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
      ((1 / 2 : ℝ) * quadForm B u)
    - (1 / 2 : ℝ) * trASig (A.comp Hinv) (B.comp Hinv)

/-- **`fqqKernel` is even**: `quadForm` is even in `u`, so the entire
quartic-minus-constant kernel is invariant under `u ↦ -u`. -/
private lemma fqqKernel_even
    (A B Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) :
    fqqKernel A B Hinv (-u) = fqqKernel A B Hinv u := by
  unfold fqqKernel
  rw [quadForm_neg, quadForm_neg]

/-- **`fqqKernel` has zero Gaussian mean**: by `gaussian_quad_centered_quad_eq`,
the quartic centered-product integrates to `Z · c_QQ`; subtracting `c_QQ`
gives `∫ FQQ · gW = Z · c_QQ - c_QQ · Z = 0`. -/
private lemma integral_fqqKernel_mul_gaussianWeight_eq_zero
    {Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (A B : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hA_symm : ∀ u v : ι → ℝ, dot u (A v) = dot v (A u))
    (hB_symm : ∀ u v : ι → ℝ, dot u (B v) = dot v (B u))
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∫ u : ι → ℝ, fqqKernel A B Hinv u * gaussianWeight H u = 0 := by
  unfold fqqKernel
  set c_QQ : ℝ := (1 / 2 : ℝ) * trASig (A.comp Hinv) (B.comp Hinv) with hc_QQ_def
  -- The integrand `((Q_A - tr_A)/2 · Q_B/2) · gW` is integrable as a sum of
  -- two `int_4`/`int_uk_uj_gW` pieces.
  have h_int_QcQ_gW : Integrable (fun u : ι → ℝ =>
      ((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
        ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u) := by
    have hQQ := (integrable_quadForm_mul_quadForm_mul_gaussianWeight A B hGauss).const_mul
      (1 / 4 : ℝ)
    have hQB := (integrable_quadForm_mul_gaussianWeight B hGauss).const_mul
      ((1 / 4 : ℝ) * trASig A Hinv)
    have h_diff := hQQ.sub hQB
    apply h_diff.congr
    filter_upwards with u
    simp only [Pi.sub_apply]; ring
  have h_int_const_gW :
      Integrable (fun u : ι → ℝ => c_QQ * gaussianWeight H u) :=
    hGauss.toLaplaceCovHypotheses.int_gW.const_mul c_QQ
  rw [show (fun u : ι → ℝ =>
        (((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
            ((1 / 2 : ℝ) * quadForm B u) - c_QQ) * gaussianWeight H u)
        = fun u =>
            (((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
                ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u)
            - c_QQ * gaussianWeight H u from by
      funext u; ring]
  rw [MeasureTheory.integral_sub h_int_QcQ_gW h_int_const_gW]
  rw [gaussian_quad_centered_quad_eq A B hA_symm hB_symm hGauss]
  rw [MeasureTheory.integral_const_mul]
  have h_int_gW_eq : ∫ u : ι → ℝ, gaussianWeight H u = gaussianZ H := rfl
  rw [h_int_gW_eq, hc_QQ_def]
  ring

/-- **Polynomial bound on `fqqKernel`**: `|FQQ(u)| ≤ C_FQQ · (1 + ‖u‖^4)`
where `C_FQQ` depends on `A`, `B`, `|trASig A Hinv|`, `|trASig (A∘Hinv) (B∘Hinv)|`,
and `Fintype.card ι`. This gives the polynomial growth needed for the
tail estimates in the K/t bound. -/
private lemma abs_fqqKernel_le
    (A B Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ |fqqKernel A B Hinv u| ≤ C * (1 + ‖u‖ ^ 4) := by
  classical
  set N : ℝ := (Fintype.card ι : ℝ) with hN_def
  have hN_nn : 0 ≤ N := by rw [hN_def]; exact_mod_cast Nat.zero_le _
  have hA_nn : 0 ≤ ‖A‖ := norm_nonneg _
  have hB_nn : 0 ≤ ‖B‖ := norm_nonneg _
  set tA : ℝ := |trASig A Hinv| with htA_def
  set tAB : ℝ := |trASig (A.comp Hinv) (B.comp Hinv)| with htAB_def
  have htA_nn : 0 ≤ tA := abs_nonneg _
  have htAB_nn : 0 ≤ tAB := abs_nonneg _
  set C : ℝ := (1 / 4 : ℝ) * (N * ‖A‖ * (N * ‖B‖))
              + (1 / 4 : ℝ) * tA * (N * ‖B‖)
              + (1 / 2 : ℝ) * tAB with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]; positivity
  refine ⟨C, hC_nn, ?_⟩
  -- Pointwise bounds on each piece.
  have h_qf_A : |quadForm A u| ≤ N * ‖A‖ * ‖u‖ ^ 2 := by
    unfold quadForm
    have h_each : ∀ i, |u i * (A u) i| ≤ ‖u‖ * ‖A u‖ := fun i => by
      rw [abs_mul]
      apply mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm (A u) i)
        (abs_nonneg _) (norm_nonneg _)
    have h_sum_le : |∑ i, u i * (A u) i| ≤ ∑ i, |u i * (A u) i| :=
      Finset.abs_sum_le_sum_abs _ _
    have h_sum_le2 : ∑ i, |u i * (A u) i|
        ≤ N * (‖u‖ * ‖A u‖) := by
      calc ∑ i, |u i * (A u) i|
          ≤ ∑ _ : ι, ‖u‖ * ‖A u‖ := Finset.sum_le_sum (fun i _ => h_each i)
        _ = N * (‖u‖ * ‖A u‖) := by
              rw [Finset.sum_const, Finset.card_univ]
              rw [hN_def]; push_cast; ring
    have h_Au : ‖A u‖ ≤ ‖A‖ * ‖u‖ := A.le_opNorm u
    calc |∑ i, u i * (A u) i|
        ≤ N * (‖u‖ * ‖A u‖) := le_trans h_sum_le h_sum_le2
      _ ≤ N * (‖u‖ * (‖A‖ * ‖u‖)) := by
          apply mul_le_mul_of_nonneg_left _ hN_nn
          apply mul_le_mul_of_nonneg_left h_Au (norm_nonneg _)
      _ = N * ‖A‖ * ‖u‖ ^ 2 := by ring
  have h_qf_B : |quadForm B u| ≤ N * ‖B‖ * ‖u‖ ^ 2 := by
    unfold quadForm
    have h_each : ∀ i, |u i * (B u) i| ≤ ‖u‖ * ‖B u‖ := fun i => by
      rw [abs_mul]
      apply mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm (B u) i)
        (abs_nonneg _) (norm_nonneg _)
    have h_sum_le : |∑ i, u i * (B u) i| ≤ ∑ i, |u i * (B u) i| :=
      Finset.abs_sum_le_sum_abs _ _
    have h_sum_le2 : ∑ i, |u i * (B u) i|
        ≤ N * (‖u‖ * ‖B u‖) := by
      calc ∑ i, |u i * (B u) i|
          ≤ ∑ _ : ι, ‖u‖ * ‖B u‖ := Finset.sum_le_sum (fun i _ => h_each i)
        _ = N * (‖u‖ * ‖B u‖) := by
              rw [Finset.sum_const, Finset.card_univ]
              rw [hN_def]; push_cast; ring
    have h_Bu : ‖B u‖ ≤ ‖B‖ * ‖u‖ := B.le_opNorm u
    calc |∑ i, u i * (B u) i|
        ≤ N * (‖u‖ * ‖B u‖) := le_trans h_sum_le h_sum_le2
      _ ≤ N * (‖u‖ * (‖B‖ * ‖u‖)) := by
          apply mul_le_mul_of_nonneg_left _ hN_nn
          apply mul_le_mul_of_nonneg_left h_Bu (norm_nonneg _)
      _ = N * ‖B‖ * ‖u‖ ^ 2 := by ring
  have h_norm_pow_nn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  have h_norm_pow4_nn : 0 ≤ ‖u‖ ^ 4 := by positivity
  -- Bound `(1/2 Q_A - 1/2 trASig A Hinv) · (1/2 Q_B)`.
  have h_h2_pos : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h_QcQ : |((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
        ((1 / 2 : ℝ) * quadForm B u)|
      ≤ (1 / 4 : ℝ) * (N * ‖A‖ * ‖u‖ ^ 2 + tA) * (N * ‖B‖ * ‖u‖ ^ 2) := by
    rw [abs_mul]
    have h1 : |(1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv|
        ≤ (1 / 2 : ℝ) * (N * ‖A‖ * ‖u‖ ^ 2 + tA) := by
      have h_split : |(1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv|
          ≤ |(1 / 2 : ℝ) * quadForm A u| + |(1 / 2 : ℝ) * trASig A Hinv| :=
        abs_sub _ _
      have h_qA_abs : |(1 / 2 : ℝ) * quadForm A u| = (1 / 2 : ℝ) * |quadForm A u| := by
        rw [abs_mul, abs_of_nonneg h_h2_pos]
      have h_tA_abs : |(1 / 2 : ℝ) * trASig A Hinv| = (1 / 2 : ℝ) * tA := by
        rw [abs_mul, abs_of_nonneg h_h2_pos, htA_def]
      have h_step : (1 / 2 : ℝ) * |quadForm A u| ≤ (1 / 2 : ℝ) * (N * ‖A‖ * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h_qf_A h_h2_pos
      linarith
    have h2 : |(1 / 2 : ℝ) * quadForm B u| ≤ (1 / 2 : ℝ) * (N * ‖B‖ * ‖u‖ ^ 2) := by
      rw [show |(1 / 2 : ℝ) * quadForm B u| = (1 / 2 : ℝ) * |quadForm B u| from by
        rw [abs_mul, abs_of_nonneg h_h2_pos]]
      exact mul_le_mul_of_nonneg_left h_qf_B h_h2_pos
    have h_step1 : |(1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv| *
          |(1 / 2 : ℝ) * quadForm B u|
        ≤ (1 / 2 : ℝ) * (N * ‖A‖ * ‖u‖ ^ 2 + tA) *
          ((1 / 2 : ℝ) * (N * ‖B‖ * ‖u‖ ^ 2)) :=
      mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    linarith [h_step1]
  -- Polynomial monotonicity facts.
  have h_one_le : (1 : ℝ) ≤ 1 + ‖u‖ ^ 4 := by linarith
  have h_u4_le : ‖u‖ ^ 4 ≤ 1 + ‖u‖ ^ 4 := by linarith
  have h_u2_le_one_plus_u4 : ‖u‖ ^ 2 ≤ 1 + ‖u‖ ^ 4 := by
    nlinarith [sq_nonneg (‖u‖ ^ 2 - 1)]
  -- Bound `1/4 (N‖A‖ ‖u‖² + tA)(N‖B‖ ‖u‖²)` by expanding.
  have h_expand_QcQ :
      (1 / 4 : ℝ) * (N * ‖A‖ * ‖u‖ ^ 2 + tA) * (N * ‖B‖ * ‖u‖ ^ 2)
        = (1 / 4 : ℝ) * (N * ‖A‖) * (N * ‖B‖) * ‖u‖ ^ 4
        + (1 / 4 : ℝ) * tA * (N * ‖B‖) * ‖u‖ ^ 2 := by
    have h_uu : ‖u‖ ^ 2 * ‖u‖ ^ 2 = ‖u‖ ^ 4 := by ring
    nlinarith [h_uu, sq_nonneg (‖u‖ ^ 2)]
  -- Three-piece bound: each scalar coefficient is nonneg, pieces are
  -- monotonic in (1 + ‖u‖^4).
  have h_NANB_nn : (0 : ℝ) ≤ (1 / 4 : ℝ) * (N * ‖A‖) * (N * ‖B‖) := by positivity
  have h_tANB_nn : (0 : ℝ) ≤ (1 / 4 : ℝ) * tA * (N * ‖B‖) := by positivity
  have h_tAB_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) * tAB := by positivity
  have h_step_NANB : (1 / 4 : ℝ) * (N * ‖A‖) * (N * ‖B‖) * ‖u‖ ^ 4
      ≤ (1 / 4 : ℝ) * (N * ‖A‖) * (N * ‖B‖) * (1 + ‖u‖ ^ 4) :=
    mul_le_mul_of_nonneg_left h_u4_le h_NANB_nn
  have h_step_tANB : (1 / 4 : ℝ) * tA * (N * ‖B‖) * ‖u‖ ^ 2
      ≤ (1 / 4 : ℝ) * tA * (N * ‖B‖) * (1 + ‖u‖ ^ 4) :=
    mul_le_mul_of_nonneg_left h_u2_le_one_plus_u4 h_tANB_nn
  have h_step_tAB : (1 / 2 : ℝ) * tAB ≤ (1 / 2 : ℝ) * tAB * (1 + ‖u‖ ^ 4) := by
    have := mul_le_mul_of_nonneg_left h_one_le h_tAB_nn
    linarith
  unfold fqqKernel
  calc |((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
          ((1 / 2 : ℝ) * quadForm B u) -
        (1 / 2 : ℝ) * trASig (A.comp Hinv) (B.comp Hinv)|
      ≤ |((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv) *
          ((1 / 2 : ℝ) * quadForm B u)| +
        |(1 / 2 : ℝ) * trASig (A.comp Hinv) (B.comp Hinv)| := abs_sub _ _
    _ ≤ (1 / 4 : ℝ) * (N * ‖A‖ * ‖u‖ ^ 2 + tA) * (N * ‖B‖ * ‖u‖ ^ 2)
        + (1 / 2 : ℝ) * tAB := by
        have h_tAB_eq : |(1 / 2 : ℝ) * trASig (A.comp Hinv) (B.comp Hinv)|
            = (1 / 2 : ℝ) * tAB := by
          rw [abs_mul, abs_of_nonneg h_h2_pos, htAB_def]
        linarith [h_QcQ, h_tAB_eq.le]
    _ = (1 / 4 : ℝ) * (N * ‖A‖) * (N * ‖B‖) * ‖u‖ ^ 4
        + (1 / 4 : ℝ) * tA * (N * ‖B‖) * ‖u‖ ^ 2
        + (1 / 2 : ℝ) * tAB := by linarith [h_expand_QcQ]
    _ ≤ (1 / 4 : ℝ) * (N * ‖A‖) * (N * ‖B‖) * (1 + ‖u‖ ^ 4)
        + (1 / 4 : ℝ) * tA * (N * ‖B‖) * (1 + ‖u‖ ^ 4)
        + (1 / 2 : ℝ) * tAB * (1 + ‖u‖ ^ 4) := by
        linarith [h_step_NANB, h_step_tANB, h_step_tAB]
    _ = C * (1 + ‖u‖ ^ 4) := by rw [hC_def]; ring

/-- **Local pointwise bound for the FQQ corrected-bracket integrand** (item 5
of GPT path response). On the local ball `‖u‖ ≤ ρ·√t`,
\[
  |F_{QQ}(u) \cdot gW(u) \cdot (e^{-s_t} - 1 + c_t)|
    \le \frac{C_{FQQ}}{t}\,(1+\|u\|^4)\,(C_s^2\|u\|^6 + j\|u\|^4)
    \,e^{-(c'/4)\,\|u\|^2}.
\]

Combines the polynomial bound `abs_fqqKernel_le` with the corrected-bracket
local bound `abs_gaussianWeight_mul_corrected_bracket_local_le`.

The polynomial RHS has degree 10 in `‖u‖`; integrating against a Gaussian
gives `O(1/t)` after multiplying by the Gaussian moment constants. -/
private lemma abs_fqqKernel_mul_gaussianWeight_mul_corrected_bracket_local_le
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (A B : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hρ_le_jet_R : ρ ≤ hV.jet_radius)
    (hρ_le_local_R : ρ ≤ hV.toPotentialApprox.local_radius)
    (hρ_decay : hV.toPotentialApprox.local_const * ρ ≤
        hV.H_coercive_const / 4)
    {t : ℝ} (ht_pos : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ ρ * Real.sqrt t) :
    ∃ C_FQQ : ℝ, 0 ≤ C_FQQ ∧
      |fqqKernel A B Hinv u| * (gaussianWeight H u *
          |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
            t * hV.cV ((Real.sqrt t)⁻¹ • u)|)
        ≤ C_FQQ * (1 + ‖u‖ ^ 4) *
          ((hV.toPotentialApprox.local_const ^ 2 * ‖u‖ ^ 6 +
            hV.jet_const * ‖u‖ ^ 4) / t) *
          Real.exp (-(hV.H_coercive_const / 4 * ‖u‖ ^ 2)) := by
  obtain ⟨C_FQQ, hC_FQQ_nn, hF_bound⟩ := abs_fqqKernel_le A B Hinv u
  refine ⟨C_FQQ, hC_FQQ_nn, ?_⟩
  -- Local bracket bound (existing helper).
  have h_bracket :=
    abs_gaussianWeight_mul_corrected_bracket_local_le V H hV
      hρ_pos hρ_le_jet_R hρ_le_local_R hρ_decay ht_pos u hu
  -- |F| · (gW · |bracket|) ≤ |F| · (poly/t · gauss-decay)
  -- ≤ C(1+‖u‖^4) · (poly/t · gauss-decay).
  have h_F_nn : 0 ≤ |fqqKernel A B Hinv u| := abs_nonneg _
  have h_one_plus_u4_nn : 0 ≤ 1 + ‖u‖ ^ 4 := by positivity
  have h_poly_decay_nn : 0 ≤ (hV.toPotentialApprox.local_const ^ 2 * ‖u‖ ^ 6 +
          hV.jet_const * ‖u‖ ^ 4) / t *
          Real.exp (-(hV.H_coercive_const / 4 * ‖u‖ ^ 2)) := by
    apply mul_nonneg
    · apply div_nonneg
      · have h1 : 0 ≤ hV.toPotentialApprox.local_const ^ 2 * ‖u‖ ^ 6 :=
          mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
        have h2 : 0 ≤ hV.jet_const * ‖u‖ ^ 4 :=
          mul_nonneg hV.jet_const_nonneg (pow_nonneg (norm_nonneg _) _)
        linarith
      · exact ht_pos.le
    · exact (Real.exp_pos _).le
  calc |fqqKernel A B Hinv u| *
        (gaussianWeight H u *
          |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
            t * hV.cV ((Real.sqrt t)⁻¹ • u)|)
      ≤ |fqqKernel A B Hinv u| *
          ((hV.toPotentialApprox.local_const ^ 2 * ‖u‖ ^ 6 +
              hV.jet_const * ‖u‖ ^ 4) / t *
            Real.exp (-(hV.H_coercive_const / 4 * ‖u‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left h_bracket h_F_nn
    _ ≤ (C_FQQ * (1 + ‖u‖ ^ 4)) *
          ((hV.toPotentialApprox.local_const ^ 2 * ‖u‖ ^ 6 +
              hV.jet_const * ‖u‖ ^ 4) / t *
            Real.exp (-(hV.H_coercive_const / 4 * ‖u‖ ^ 2))) :=
        mul_le_mul_of_nonneg_right hF_bound h_poly_decay_nn
    _ = C_FQQ * (1 + ‖u‖ ^ 4) *
          ((hV.toPotentialApprox.local_const ^ 2 * ‖u‖ ^ 6 +
            hV.jet_const * ‖u‖ ^ 4) / t) *
          Real.exp (-(hV.H_coercive_const / 4 * ‖u‖ ^ 2)) := by ring

/-- **Integrability of `‖u‖^k · gaussianWeight H · cV((√t)⁻¹•u)`** for
any `k : ℕ` and `t > 0`. Bounds `|cV(w)| ≤ Cc · ‖w‖^3` (via
`PotentialJetApprox.cV_bound`), then dominated by polynomial-times-Gaussian. -/
private lemma integrable_pow_norm_mul_gaussianWeight_mul_cV
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (k : ℕ) {t : ℝ} (ht_pos : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      ‖u‖ ^ k * gaussianWeight H u * hV.cV ((Real.sqrt t)⁻¹ • u)) := by
  classical
  set Cc := hV.cV_bound_const with hCc_def
  set c' := hV.H_coercive_const with hc'_def
  have hc'_pos : 0 < c' := hV.H_coercive_const_pos
  have hCc_nn : 0 ≤ Cc := hV.cV_bound_const_nonneg
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_inv_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hsqrt_pos
  -- Dominate: |‖u‖^k · gW · cV((√t)⁻¹•u)| ≤ Cc · ‖u‖^(k+3) · ((√t)⁻¹)^3 · exp(-c'/2 ‖u‖²).
  have h_continuous : Continuous (fun u : ι → ℝ =>
      ‖u‖ ^ k * gaussianWeight H u * hV.cV ((Real.sqrt t)⁻¹ • u)) :=
    ((continuous_norm.pow k).mul (continuous_gaussianWeight H)).mul
      (hV.cV_continuous.comp (continuous_const.smul continuous_id))
  -- Use `integrable_pow_norm_mul_gaussianWeight` to get
  -- `Integrable (‖u‖^(k+3) · gW)` and bound by const.
  have h_dom : Integrable (fun u : ι → ℝ =>
      Cc * ((Real.sqrt t)⁻¹) ^ 3 *
        (‖u‖ ^ (k + 3) * gaussianWeight H u)) :=
    (hV.int_norm_pow_gW (k + 3)).const_mul _
  refine h_dom.mono' h_continuous.aestronglyMeasurable ?_
  filter_upwards with u
  have h_norm_sm : ‖(Real.sqrt t)⁻¹ • u‖ ^ 3 =
      ((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos, mul_pow]
  have h_cV_le : |hV.cV ((Real.sqrt t)⁻¹ • u)| ≤ Cc * ‖(Real.sqrt t)⁻¹ • u‖ ^ 3 :=
    hV.cV_bound _
  have h_uk_nn : 0 ≤ ‖u‖ ^ k := pow_nonneg (norm_nonneg _) _
  have h_gW_pos : 0 < gaussianWeight H u := gaussianWeight_pos H u
  rw [Real.norm_eq_abs]
  calc |‖u‖ ^ k * gaussianWeight H u * hV.cV ((Real.sqrt t)⁻¹ • u)|
      = ‖u‖ ^ k * gaussianWeight H u * |hV.cV ((Real.sqrt t)⁻¹ • u)| := by
        rw [show ‖u‖ ^ k * gaussianWeight H u * hV.cV ((Real.sqrt t)⁻¹ • u)
              = (‖u‖ ^ k * gaussianWeight H u) *
                  hV.cV ((Real.sqrt t)⁻¹ • u) from by ring]
        rw [abs_mul, abs_of_nonneg (mul_nonneg h_uk_nn h_gW_pos.le)]
    _ ≤ ‖u‖ ^ k * gaussianWeight H u *
          (Cc * ‖(Real.sqrt t)⁻¹ • u‖ ^ 3) :=
        mul_le_mul_of_nonneg_left h_cV_le
          (mul_nonneg h_uk_nn h_gW_pos.le)
    _ = ‖u‖ ^ k * gaussianWeight H u *
          (Cc * (((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3)) := by rw [h_norm_sm]
    _ = Cc * ((Real.sqrt t)⁻¹) ^ 3 *
          (‖u‖ ^ (k + 3) * gaussianWeight H u) := by
        rw [show ‖u‖ ^ (k + 3) = ‖u‖ ^ k * ‖u‖ ^ 3 from by
              rw [pow_add]]
        ring

/-- **Connected part of `φ((√t)⁻¹u)`** when `a = 0`: subtracts off the
Stage-4 expectation coefficient `μ_φ/t = (1/(2t)) · tr(A_φ Σ)`, leaving
`φ_conn_t(u) = (1/t)·(½ A_φ u² - μ_φ) + (1/(t√t))·(1/6 Φ_φ(u,u,u)) + R_φ`.

Per `gpt_responses/strategy_stage5_decomposition.md`, the centered split
`φ_t = μ_φ/t + φ_conn_t` lets the disconnected `μ_φ μ_ψ` piece of `cov2_full`
be absorbed into the Stage-4 wrapper for `t · N_t(ψ)`, leaving only
"connected" Wick contractions in the new asymptotic lemmas. -/
private noncomputable def expCovPhiConn
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ) (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a) (t : ℝ) (u : ι → ℝ) : ℝ :=
  φ ((Real.sqrt t)⁻¹ • u) -
    expNumeratorCoeff V φ H Hinv a hV hφ / t

/-- **Linear remainder of `ψ((√t)⁻¹u)`**: subtracts the linear jet
`(√t)⁻¹ · (b·u)`, giving
`ψ_rem_t(u) = (1/t)·(½ A_ψ u²) + (1/(t√t))·(1/6 Φ_ψ(u,u,u)) + R_ψ`. -/
private noncomputable def expCovPsiRem
    (ψ : (ι → ℝ) → ℝ) (b : ι → ℝ) (t : ℝ) (u : ι → ℝ) : ℝ :=
  ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u

/-- **Pointwise pair-product expansion when `a = 0`**: with `a = 0`, the first
two pieces of `pair_product_expansion` vanish, leaving only the cross
term `(√t)⁻¹·(b·u)·φ((√t)⁻¹u)` and the rem-rem term
`φ((√t)⁻¹u)·(ψ((√t)⁻¹u) - (√t)⁻¹·b·u)`. -/
private lemma pair_product_expansion_a_zero
    (φ ψ : (ι → ℝ) → ℝ) (b : ι → ℝ) (t : ℝ) (ht : 0 < t) (u : ι → ℝ) :
    φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)
      = (Real.sqrt t)⁻¹ * dot b u * φ ((Real.sqrt t)⁻¹ • u)
        + φ ((Real.sqrt t)⁻¹ • u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) := by
  have h_pp := pair_product_expansion φ ψ (0 : ι → ℝ) b t ht u
  -- pair_product_expansion: φψ = (1/t)·dot 0 u·dot b u
  --   + (√t)⁻¹·dot 0 u·(ψ - (√t)⁻¹·dot b u)
  --   + (√t)⁻¹·dot b u·(φ - (√t)⁻¹·dot 0 u)
  --   + (φ - (√t)⁻¹·dot 0 u)(ψ - (√t)⁻¹·dot b u)
  -- with `dot 0 u = 0`, the first two pieces vanish and `φ - 0 = φ`.
  have h_dot0 : dot (0 : ι → ℝ) u = 0 := by
    unfold dot
    apply Finset.sum_eq_zero
    intros i _
    simp [Pi.zero_apply]
  rw [h_pp, h_dot0]
  ring

/-- **Integrated pair-product decomposition when `a = 0`**: integrating the
pointwise identity `pair_product_expansion_a_zero` against `gW · exp(-s_t)`
gives
\[
  t^2 \cdot N_t(\phi\psi)
    = t \sqrt{t} \cdot I_{\text{cross}} + t^2 \cdot I_{\text{rem-rem}}
\]
where
\[
  I_{\text{cross}} := \int (b\!\cdot\!u)\,\phi((\sqrt t)^{-1} u)\,gW\,e^{-s_t}\,du,
\]
\[
  I_{\text{rem-rem}} := \int \phi((\sqrt t)^{-1} u)\,
        (\psi((\sqrt t)^{-1} u) - (\sqrt t)^{-1} (b\!\cdot\!u))\,gW\,e^{-s_t}\,du.
\]

Reuses the sharp-track integrability lemmas
`integrable_dot_mul_remainder_mul_rescaled_weight` (with `a = 0`) and
`integrable_remainder_mul_remainder_mul_rescaled_weight`. -/
private lemma rescaledNumerator_pair_decompose_a_zero
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hφ : ObservableJetApprox φ (0 : ι → ℝ))
    (hψ : ObservableJetApprox ψ b)
    (hGauss : LaplaceCovHypotheses H Hinv)
    {t : ℝ} (ht1 : 1 ≤ t) :
    t ^ 2 * rescaledNumerator V t (fun w => φ w * ψ w)
      = t * Real.sqrt t *
          (∫ u : ι → ℝ, dot b u * φ ((Real.sqrt t)⁻¹ • u) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
        + t ^ 2 *
          (∫ u : ι → ℝ, φ ((Real.sqrt t)⁻¹ • u) *
              (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) := by
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have h_sqrt_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht_pos.le
  -- Pointwise identity: t² · pair = t·√t · cross + t² · rem-rem.
  have h_pt : ∀ u : ι → ℝ,
      t ^ 2 * (φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
      = t * Real.sqrt t *
          (dot b u * φ ((Real.sqrt t)⁻¹ • u) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
        + t ^ 2 *
          (φ ((Real.sqrt t)⁻¹ • u) *
              (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) := by
    intro u
    have h_pp := pair_product_expansion_a_zero φ ψ b t ht_pos u
    -- Need: t² · pair · gW · e = t·√t · (b·u·φ + ...) · gW · e + ...
    -- From h_pp: pair = (√t)⁻¹·(b·u)·φ + φ·rψ.
    -- Multiplying by t² · gW · e:
    -- LHS = t² · ((√t)⁻¹·(b·u)·φ + φ·rψ) · gW · e
    --     = t²·(√t)⁻¹·(b·u)·φ·gW·e + t²·φ·rψ·gW·e
    -- We need: t·√t · ((b·u)·φ·gW·e) = t²·(√t)⁻¹·(b·u)·φ·gW·e
    -- Since t·√t·(√t) = t·t = t² ⇒ t·√t = t²·(√t)⁻¹. ✓
    have h_t_sqrt_eq : t * Real.sqrt t = t ^ 2 * (Real.sqrt t)⁻¹ := by
      have hne : Real.sqrt t ≠ 0 := hsqrt_pos.ne'
      field_simp
      exact Real.sq_sqrt ht_pos.le
    rw [h_pp]; rw [h_t_sqrt_eq]; ring
  -- Apply h_pt as integrand congruence and split.
  rw [rescaledNumerator_eq_gaussian_form V (fun w => φ w * ψ w) H t]
  -- Goal: t² · (∫ (φψ)((√t)⁻¹u) · gW · e) = ...
  rw [show (fun u : ι → ℝ => (φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
            = fun u => φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u) *
                gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)) from rfl]
  rw [← MeasureTheory.integral_const_mul]
  -- Pointwise integrand identity.
  have h_integrand_eq :
      (fun u : ι → ℝ => t ^ 2 *
          (φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))))
      = fun u : ι → ℝ =>
          t * Real.sqrt t *
              (dot b u * φ ((Real.sqrt t)⁻¹ • u) *
                  gaussianWeight H u *
                  Real.exp (-(rescaledPerturbation V H t u)))
            + t ^ 2 *
              (φ ((Real.sqrt t)⁻¹ • u) *
                  (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
                  gaussianWeight H u *
                  Real.exp (-(rescaledPerturbation V H t u))) := by
    funext u
    have hu := h_pt u
    -- hu : t²·(φψ)·gW·e = (t·√t)·(b·u·φ·gW·e) + t²·(φ·rψ·gW·e)
    -- Goal LHS has the (φψ) inside ‹...›; just rearrange.
    linarith [hu]
  rw [h_integrand_eq]
  -- Split ∫ (a + b) = ∫ a + ∫ b.
  have h_cross_int : Integrable (fun u : ι → ℝ =>
      dot b u * φ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
    -- Reuse sharp-track helper with `dotCoef = b`, `phiGrad = 0`.
    -- It gives `dot b u · (φ((√t)⁻¹u) - (√t)⁻¹·dot 0 u) · gW · e` integrable.
    have h := integrable_dot_mul_remainder_mul_rescaled_weight V φ H Hinv b
        (0 : ι → ℝ) hV.toPotentialApprox hφ.toObservableApprox hGauss ht1
    apply h.congr
    filter_upwards with u
    have h_dot0 : dot (0 : ι → ℝ) u = 0 := by
      unfold dot; apply Finset.sum_eq_zero; intros i _; simp [Pi.zero_apply]
    rw [h_dot0]; ring
  have h_remrem_int : Integrable (fun u : ι → ℝ =>
      φ ((Real.sqrt t)⁻¹ • u) *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
    have h := integrable_remainder_mul_remainder_mul_rescaled_weight V φ ψ H Hinv
        (0 : ι → ℝ) b hV.toPotentialApprox hφ.toObservableApprox hψ.toObservableApprox
        hGauss ht1
    apply h.congr
    filter_upwards with u
    have h_dot0 : dot (0 : ι → ℝ) u = 0 := by
      unfold dot; apply Finset.sum_eq_zero; intros i _; simp [Pi.zero_apply]
    rw [h_dot0]; ring
  have h_cross_smul : Integrable (fun u : ι → ℝ =>
      t * Real.sqrt t *
        (dot b u * φ ((Real.sqrt t)⁻¹ • u) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))) := h_cross_int.const_mul _
  have h_remrem_smul : Integrable (fun u : ι → ℝ =>
      t ^ 2 *
        (φ ((Real.sqrt t)⁻¹ • u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))) := h_remrem_int.const_mul _
  rw [MeasureTheory.integral_add h_cross_smul h_remrem_smul,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **Single-dot integrability against `gW · exp(-s_t)`**: dominate
`|dot a u|` by `A · ‖u‖` where `A = ∑ |a_i|`, then use
`integrable_pow_norm_mul_rescaled_weight` at `k = 1`. -/
private lemma integrable_dot_mul_rescaled_weight
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV_cont : Continuous V)
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      dot a u * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) := by
  set A : ℝ := ∑ i, |a i| with hA_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_dot_a_cont : Continuous (fun u : ι → ℝ => dot a u) := by
    unfold dot
    exact continuous_finset_sum _
      (fun i _ => continuous_const.mul (continuous_apply i))
  have h_dom : Integrable (fun u : ι → ℝ =>
      A * (‖u‖ ^ 1 *
        (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))))) :=
    (integrable_pow_norm_mul_rescaled_weight V hV_cont H hc_pos h_coer 1 ht).const_mul A
  refine h_dom.mono' ?_ ?_
  · exact (h_dot_a_cont.mul ((continuous_gaussianWeight H).mul
      (Real.continuous_exp.comp
        (continuous_rescaledPerturbation hV_cont H t).neg))).aestronglyMeasurable
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
            Real.exp (-(rescaledPerturbation V H t u))) := by
          gcongr
      _ = A * (‖u‖ ^ 1 * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))) := by
          rw [pow_one]; ring

/-- **Observable-times-rescaled-weight integrability**: with polynomial
growth of `φ` (degree `p`), dominate `|φ((√t)⁻¹·u)| · gW · exp(-s_t)` by
a Gaussian polynomial bound. Template lifted from `expNumerator_centered_decomp`. -/
private lemma integrable_obs_mul_rescaled_weight
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV_cont : Continuous V)
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (hφ : ObservableApprox φ a)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      φ ((Real.sqrt t)⁻¹ • u) *
        (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)))) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hinv_sqrt_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hsqrt_pos
  obtain ⟨Kφ, p, hKφ_nn, hpoly⟩ := hφ.poly_growth
  have h_phi_cont : Continuous (fun u : ι → ℝ => φ ((Real.sqrt t)⁻¹ • u)) :=
    hφ.phi_continuous.comp (continuous_const.smul continuous_id)
  have h_rw_cont : Continuous (fun u : ι → ℝ =>
      gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) :=
    (continuous_gaussianWeight H).mul (Real.continuous_exp.comp
      (continuous_rescaledPerturbation hV_cont H t).neg)
  set Cinv_p : ℝ := ((Real.sqrt t)⁻¹) ^ p with hCinv_def
  have hCinv_nn : 0 ≤ Cinv_p := by rw [hCinv_def]; positivity
  have h0 := integrable_exp_neg_const_norm_sq (ι := ι) hc_pos
  have hpInt := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos p
  have h_dom : Integrable (fun u : ι → ℝ =>
      Kφ * (Real.exp (-(c * ‖u‖ ^ 2)) +
        Cinv_p * (‖u‖ ^ p * Real.exp (-(c * ‖u‖ ^ 2))))) :=
    (h0.add (hpInt.const_mul Cinv_p)).const_mul Kφ
  refine h_dom.mono' ?_ ?_
  · exact (h_phi_cont.mul h_rw_cont).aestronglyMeasurable
  · filter_upwards with u
    have h_phi_le : |φ ((Real.sqrt t)⁻¹ • u)|
        ≤ Kφ * (1 + ‖(Real.sqrt t)⁻¹ • u‖ ^ p) := hpoly _
    have h_norm_sm : ‖(Real.sqrt t)⁻¹ • u‖ = (Real.sqrt t)⁻¹ * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv_sqrt_pos]
    have h_norm_sm_p : ‖(Real.sqrt t)⁻¹ • u‖ ^ p = Cinv_p * ‖u‖ ^ p := by
      rw [h_norm_sm, mul_pow]
    have h_phi_le' : |φ ((Real.sqrt t)⁻¹ • u)|
        ≤ Kφ * (1 + Cinv_p * ‖u‖ ^ p) := by
      rw [← h_norm_sm_p]; exact h_phi_le
    have h_rw_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
    have h_rw_le : gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
        ≤ Real.exp (-(c * ‖u‖ ^ 2)) :=
      rescaled_weight_le_coercive V H hc_pos h_coer ht u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_rw_nn]
    calc |φ ((Real.sqrt t)⁻¹ • u)| * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
        ≤ Kφ * (1 + Cinv_p * ‖u‖ ^ p) * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) :=
          mul_le_mul_of_nonneg_right h_phi_le' h_rw_nn
      _ ≤ Kφ * (1 + Cinv_p * ‖u‖ ^ p) *
            Real.exp (-(c * ‖u‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h_rw_le
            (mul_nonneg hKφ_nn (by positivity))
      _ = Kφ * (Real.exp (-(c * ‖u‖ ^ 2)) +
          Cinv_p * (‖u‖ ^ p * Real.exp (-(c * ‖u‖ ^ 2)))) := by ring

/-- **Pointwise centered decomposition** when `a = 0`: the substitution
`φ((√t)⁻¹u) = μ_φ/t + φ_conn(u)` and `ψ((√t)⁻¹u) = (√t)⁻¹·(b·u) + ψ_rem(u)`
yields
\[
  \phi((\sqrt t)^{-1}u)\,\psi((\sqrt t)^{-1}u)
    = \tfrac{\mu_\phi}{t}\,\psi((\sqrt t)^{-1}u)
      + (\sqrt t)^{-1} (b\!\cdot\!u)\,\phi_{\text{conn}}(u)
      + \phi_{\text{conn}}(u)\,\psi_{\text{rem}}(u).
\]
Pure algebraic identity. -/
private lemma pair_product_centered_decomposition
    (V φ ψ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ) (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    (t : ℝ) (u : ι → ℝ) :
    φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)
      = (expNumeratorCoeff V φ H Hinv (0 : ι → ℝ) hV hφ / t) *
            ψ ((Real.sqrt t)⁻¹ • u)
        + (Real.sqrt t)⁻¹ * dot b u *
            expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u
        + expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u *
            expCovPsiRem ψ b t u := by
  -- Substitute the defs and ring.
  unfold expCovPhiConn expCovPsiRem
  ring

/-- **GPT-style decomposition of `t² · N(φψ)`** when `a = 0`: peeling
`μ_φ/t` off `φ_t` first, the centered numerator splits as
\[
  t^2 N_t(\phi\psi)
    = \mu_\phi \cdot \bigl(t \cdot N_t(\psi)\bigr)
      + t\sqrt t \cdot \texttt{cross}_t
      + t^2 \cdot \texttt{rr}_t.
\]
The disconnected `μ_φ μ_ψ` contribution is absorbed into `μ_φ · t · N_t(ψ)`
(handled by Stage-4); the two new integrals contain only connected Wick
contributions, which simplifies the asymptotic lemmas A and B.

Proof: integrate `pair_product_centered_decomposition` against
`gW · exp(-s_t)`, multiply by `t²`, and use `t² · (√t)⁻¹ = t · √t`. -/
private lemma rescaledNumerator_pair_decompose_centered_a_zero
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    (hψ : ObservableTensorApprox ψ b)
    (hGauss : LaplaceCovHypotheses H Hinv)
    {t : ℝ} (ht1 : 1 ≤ t) :
    t ^ 2 * rescaledNumerator V t (fun w => φ w * ψ w)
      = expNumeratorCoeff V φ H Hinv (0 : ι → ℝ) hV hφ
          * (t * rescaledNumerator V t ψ)
        + t * Real.sqrt t *
          (∫ u : ι → ℝ, dot b u *
              expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
        + t ^ 2 *
          (∫ u : ι → ℝ,
              expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u *
              expCovPsiRem ψ b t u *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) := by
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have h_sqrt_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht_pos.le
  have ht_ne : t ≠ 0 := ht_pos.ne'
  set μ_φ : ℝ := expNumeratorCoeff V φ H Hinv (0 : ι → ℝ) hV hφ with hμ_def
  -- Apply the raw decomposition.
  rw [rescaledNumerator_pair_decompose_a_zero V φ ψ H Hinv b
    hV.toPotentialJetApprox hφ.toObservableJetApprox hψ.toObservableJetApprox
    hGauss ht1]
  -- Integrability witnesses (use new helpers).
  have hVc := hV.toPotentialJetApprox.toPotentialApprox.V_continuous
  have hc_pos : 0 < hV.toPotentialJetApprox.toPotentialApprox.coercive_const :=
    hV.toPotentialJetApprox.toPotentialApprox.coercive_const_pos
  have h_coer := hV.toPotentialJetApprox.toPotentialApprox.coercive_bound
  have h_int_b : Integrable (fun u : ι → ℝ =>
      dot b u * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) :=
    integrable_dot_mul_rescaled_weight V H b hVc hc_pos h_coer ht_pos
  have h_int_phi : Integrable (fun u : ι → ℝ =>
      φ ((Real.sqrt t)⁻¹ • u) * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) :=
    integrable_obs_mul_rescaled_weight V φ H (0 : ι → ℝ) hVc hc_pos h_coer
      hφ.toObservableApprox ht_pos
  have h_int_psi : Integrable (fun u : ι → ℝ =>
      ψ ((Real.sqrt t)⁻¹ • u) * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) :=
    integrable_obs_mul_rescaled_weight V ψ H b hVc hc_pos h_coer
      hψ.toObservableApprox ht_pos
  have h_int_b_phi : Integrable (fun u : ι → ℝ =>
      dot b u * φ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
    have h := integrable_dot_mul_remainder_mul_rescaled_weight V φ H Hinv b
        (0 : ι → ℝ) hV.toPotentialJetApprox.toPotentialApprox hφ.toObservableApprox
        hGauss ht1
    have h_eq : (fun u : ι → ℝ =>
        dot b u * (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot (0 : ι → ℝ) u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
        = fun u : ι → ℝ =>
          dot b u * φ ((Real.sqrt t)⁻¹ • u) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)) := by
      funext u
      have h_dot0 : dot (0 : ι → ℝ) u = 0 := by
        unfold dot; apply Finset.sum_eq_zero; intros i _; simp [Pi.zero_apply]
      rw [h_dot0]; ring
    rw [← h_eq]; exact h
  have h_int_phi_psirem : Integrable (fun u : ι → ℝ =>
      φ ((Real.sqrt t)⁻¹ • u) * expCovPsiRem ψ b t u *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
    have h := integrable_remainder_mul_remainder_mul_rescaled_weight V φ ψ H Hinv
        (0 : ι → ℝ) b hV.toPotentialJetApprox.toPotentialApprox
        hφ.toObservableApprox hψ.toObservableApprox hGauss ht1
    have h_eq : (fun u : ι → ℝ =>
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot (0 : ι → ℝ) u) *
          (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
        = fun u : ι → ℝ =>
          φ ((Real.sqrt t)⁻¹ • u) * expCovPsiRem ψ b t u *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)) := by
      funext u
      have h_dot0 : dot (0 : ι → ℝ) u = 0 := by
        unfold dot; apply Finset.sum_eq_zero; intros i _; simp [Pi.zero_apply]
      rw [h_dot0, expCovPsiRem]; ring
    rw [← h_eq]; exact h
  -- Set abbreviations.
  set J_b : ℝ := ∫ u : ι → ℝ, dot b u *
      (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) with hJ_b_def
  set J_rem : ℝ := ∫ u : ι → ℝ, expCovPsiRem ψ b t u *
      (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) with hJ_rem_def
  set I_conn_cross : ℝ := ∫ u : ι → ℝ, dot b u *
      expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u *
      gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u)) with hI_cc_def
  set I_conn_rr : ℝ := ∫ u : ι → ℝ,
      expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u *
      expCovPsiRem ψ b t u *
      gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u)) with hI_rr_def
  -- Show: I_raw_cross = (μ_φ/t)·J_b + I_conn_cross.
  have h_int_b_conn : Integrable (fun u : ι → ℝ =>
      dot b u * expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
    have h_eq : (fun u : ι → ℝ =>
        dot b u * expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
        = fun u : ι → ℝ =>
          dot b u * φ ((Real.sqrt t)⁻¹ • u) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
          - (μ_φ / t) * (dot b u *
              (gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))) := by
      funext u; rw [expCovPhiConn, hμ_def]; ring
    rw [h_eq]; exact h_int_b_phi.sub (h_int_b.const_mul _)
  have h_int_phi_conn_psirem : Integrable (fun u : ι → ℝ =>
      expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u *
        expCovPsiRem ψ b t u *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
    -- need J_rem' integrable.
    have h_int_psirem : Integrable (fun u : ι → ℝ =>
        expCovPsiRem ψ b t u * (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))) := by
      have h_eq : (fun u : ι → ℝ =>
          expCovPsiRem ψ b t u * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))))
          = fun u : ι → ℝ =>
            ψ ((Real.sqrt t)⁻¹ • u) * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
            - (Real.sqrt t)⁻¹ * (dot b u * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))) := by
        funext u; rw [expCovPsiRem]; ring
      rw [h_eq]; exact h_int_psi.sub (h_int_b.const_mul _)
    have h_eq : (fun u : ι → ℝ =>
        expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u *
          expCovPsiRem ψ b t u *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
        = fun u : ι → ℝ =>
          φ ((Real.sqrt t)⁻¹ • u) * expCovPsiRem ψ b t u *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
          - (μ_φ / t) * (expCovPsiRem ψ b t u *
              (gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))) := by
      funext u; rw [expCovPhiConn, hμ_def]; ring
    rw [h_eq]; exact h_int_phi_psirem.sub (h_int_psirem.const_mul _)
  -- Identity 1: I_raw_cross = (μ_φ/t)·J_b + I_conn_cross.
  have h_id_cross :
      (∫ u : ι → ℝ, dot b u * φ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))
      = (μ_φ / t) * J_b + I_conn_cross := by
    rw [hJ_b_def, hI_cc_def, ← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_add (h_int_b.const_mul _) h_int_b_conn]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [expCovPhiConn, hμ_def]; ring
  -- Identity 2: I_raw_rr = (μ_φ/t)·J_rem + I_conn_rr.
  have h_id_rr :
      (∫ u : ι → ℝ, φ ((Real.sqrt t)⁻¹ • u) *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))
      = (μ_φ / t) * J_rem + I_conn_rr := by
    have h_int_psirem : Integrable (fun u : ι → ℝ =>
        expCovPsiRem ψ b t u * (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))) := by
      have h_eq : (fun u : ι → ℝ =>
          expCovPsiRem ψ b t u * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))))
          = fun u : ι → ℝ =>
            ψ ((Real.sqrt t)⁻¹ • u) * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
            - (Real.sqrt t)⁻¹ * (dot b u * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))) := by
        funext u; rw [expCovPsiRem]; ring
      rw [h_eq]; exact h_int_psi.sub (h_int_b.const_mul _)
    rw [hJ_rem_def, hI_rr_def, ← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_add (h_int_psirem.const_mul _) h_int_phi_conn_psirem]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [expCovPhiConn, expCovPsiRem, hμ_def]; ring
  -- Identity 3: t·N(ψ) = √t·J_b + t·J_rem.
  have h_tN_psi : t * rescaledNumerator V t ψ
      = Real.sqrt t * J_b + t * J_rem := by
    rw [rescaledNumerator_eq_gaussian_form V ψ H t]
    have h_eq_lambda : (fun u : ι → ℝ => ψ ((Real.sqrt t)⁻¹ • u) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
          = fun u : ι → ℝ => ψ ((Real.sqrt t)⁻¹ • u) *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) := by
      funext u; ring
    rw [h_eq_lambda]
    have h_int_psirem : Integrable (fun u : ι → ℝ =>
        expCovPsiRem ψ b t u * (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))) := by
      have h_eq : (fun u : ι → ℝ =>
          expCovPsiRem ψ b t u * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))))
          = fun u : ι → ℝ =>
            ψ ((Real.sqrt t)⁻¹ • u) * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
            - (Real.sqrt t)⁻¹ * (dot b u * (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))) := by
        funext u; rw [expCovPsiRem]; ring
      rw [h_eq]; exact h_int_psi.sub (h_int_b.const_mul _)
    -- Pointwise: ψ_t · h = (√t)⁻¹·(b·u)·h + ψ_rem·h.
    have h_split_eq :
        (fun u : ι → ℝ => ψ ((Real.sqrt t)⁻¹ • u) *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))))
          = fun u : ι → ℝ =>
              (Real.sqrt t)⁻¹ * (dot b u * (gaussianWeight H u *
                  Real.exp (-(rescaledPerturbation V H t u))))
              + expCovPsiRem ψ b t u * (gaussianWeight H u *
                  Real.exp (-(rescaledPerturbation V H t u))) := by
      funext u; rw [expCovPsiRem]; ring
    rw [h_split_eq, MeasureTheory.integral_add (h_int_b.const_mul _) h_int_psirem]
    rw [MeasureTheory.integral_const_mul]
    rw [← hJ_b_def, ← hJ_rem_def]
    have h_t_inv_sqrt : t * (Real.sqrt t)⁻¹ = Real.sqrt t := by
      field_simp; exact (Real.sq_sqrt ht_pos.le).symm
    linear_combination J_b * h_t_inv_sqrt
  -- Final algebra.
  rw [h_id_cross, h_id_rr]
  -- Use h_tN_psi to expand t · N(ψ) = √t·J_b + t·J_rem.
  rw [h_tN_psi]
  -- Distribute and cancel.
  have h1 : t * Real.sqrt t * (μ_φ / t) = μ_φ * Real.sqrt t := by
    field_simp
  have h2 : t ^ 2 * (μ_φ / t) = μ_φ * t := by
    rw [show (t : ℝ)^2 = t * t from sq t]; field_simp
  linear_combination J_b * h1 + J_rem * h2

/-- **Stage-5 cross asymptotic** (lemma A in `gpt_responses/strategy_stage5_decomposition.md`).
With `a = 0` and `φ_conn_t = φ((√t)⁻¹u) - μ_φ/t`, the cross integral
\[
  \texttt{cross}_t \;:=\;
    \int (b\!\cdot\!u)\,\phi_{\text{conn},t}\,gW\,e^{-s_t}\,du
\]
satisfies the asymptotic
\[
  \bigl|\,t^{3/2} \cdot \texttt{cross}_t - c_{\text{cross}} \cdot D_t\,\bigr|
    \le K/t,
\]
where `c_cross = (1/2)<Σb, Φ_φ:Σ> - (1/2)<b, A_φΣ T:Σ> - (1/2)<Σb, T:(ΣA_φΣ)>`
is the connected (non-QQ) piece of `cov2Coefficient`.

The 3 connected terms come from:
- `Lψ · Cφ · 1` → `(1/2)<Σb, Φ_φ:Σ>` (Wick `gaussian_cubic_linear`).
- `Lψ · Q_φ^c · (-V_3/√t)` → the two `T`-contractions
  (Wick `gaussian_quad_linear_cubic` — explicit form, requires strengthening).
The Q^c centering removes the `μ_φ μ_ψ` disconnected contribution.

Currently a sorry; proof recipe in `strategy_stage5_decomposition.md`. -/
private theorem rescaledIntegral_cross_linear_connected_asymptotic
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * Real.sqrt t *
          (∫ u : ι → ℝ, dot b u *
              expCovPhiConn V φ H Hinv (0 : ι → ℝ)
                hV.toPotentialTensorApprox hφ t u *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
        - ((1 / 2 : ℝ) * dot (Hinv b) (tensorContractMatrix hφ.Φ Hinv)
          - (1 / 2 : ℝ) * dot b
              (Hinv (hφ.A (Hinv (tensorContractMatrix hV.T Hinv))))
          - (1 / 2 : ℝ) * dot (Hinv b)
              (tensorContractMatrix hV.T (Hinv.comp (hφ.A.comp Hinv))))
          * rescaledPartition V t|
        ≤ K / t := by
  -- 4-step plan per `gpt_responses/strategy_stage5_lemmas_attack.md`:
  --
  -- Pointwise: t·√t · (b·u) · φ_conn expands to 3 terms (with Q^c_φ = Q_φ - μ_φ):
  --   √t · (b·u) · Q^c_φ   (parity-vanishing odd; pairs with -V_3/√t correction)
  --   (b·u) · C_φ          (even, leading)
  --   t·√t · (b·u) · R_φ   (quartic remainder)
  --
  -- Steps:
  -- 1. **Strengthen `gaussian_quad_linear_cubic`** from existential to explicit.
  --    GPT recommends: ONE IBP on `(b·u)`, NOT full 15-pairing 6-moment Wick.
  --    Differentiate `(1/2 Q_A) · (1/6 T(u,u,u))`:
  --     - derivative on `Q_A` yields `linear · cubic` integral → use
  --       `gaussian_linear_cubic` (already proved, 4-moment).
  --     - derivative on `T` yields `quad · quad` integral → use
  --       `gaussian_quad_quad` (already proved, 4-moment).
  --    Net: explicit closed form bypasses sextic moment formula entirely.
  -- 2. **Apply parity helper P2** to `Fodd := (b·u) · Q^c_φ`:
  --    `Fodd` is odd (linear · even). The (-V_3/√t) Taylor correction makes
  --    `(b·u) · Q^c_φ · V_3` even, integrating to the two T-contractions
  --    (after centering subtracts the disconnected trace via Step 1).
  --    Note: centering MATTERS here despite parity zeroing the leading —
  --    `μ_φ · (b·u) · V_3 · gW` is NOT zero by parity (linear·cubic = even).
  -- 3. **Apply parity helper P1** (or direct gaussian_cubic_linear) to
  --    `Feven := (b·u) · C_φ`:
  --    `(b·u) · (1/6 Φ_φ(u,u,u))` integrates to `Z · (1/2)⟨Σb, Φ_φ:Σ⟩`
  --    via `gaussian_cubic_linear`.
  -- 4. **Bound** `t·√t · (b·u) · R_φ` using local quartic + tail:
  --    `|R_φ| ≤ jet_const · ‖u‖^4 / t^2`, so `t·√t · |b·u| · |R_φ|
  --    ≤ const · ‖u‖^5 / √t`. Multiplied by gW · exp(-s_t), gives K/√t.
  --    For tighter K/t, need parity-aware bound on the odd part of R_φ.
  --
  -- Prerequisites (shared with Lemma B): parity helpers P1, P2 + the
  -- explicit `gaussian_quad_linear_cubic` (Step 1 above, ~150-200 LOC).
  --
  -- 2026-04-29 update: After Lemma B is closed (next session), Lemma A reuses
  -- its FQQ-style scaffolding with adaptations:
  --   - `(b·u) · C_φ`: linear·cubic = even kernel — analogous to FQQ but
  --     polynomial degree 4 (not centered around constant); main term via
  --     `gaussian_cubic_linear`.
  --   - `(b·u) · Q^c_φ · V_3`: odd kernel; needs P2 (odd analogue of FQQ
  --     transformation). Main term from explicit `gaussian_quad_linear_cubic`.
  --   - Strengthened `gaussian_quad_linear_cubic`: per GPT recommendation, ONE
  --     IBP on `(b·u)` (NOT full sextic Wick), reducing to existing 4-moment
  --     `gaussian_linear_cubic` + `gaussian_quad_quad`. ~150-200 LOC.
  -- Total after Lemma B + strengthened Wick: ~400-600 LOC.
  sorry

/-- **Stage-5 rem-rem asymptotic** (lemma B in `gpt_responses/strategy_stage5_decomposition.md`).
With `a = 0` and `ψ_rem_t = ψ((√t)⁻¹u) - (√t)⁻¹·(b·u)`, the rem-rem integral
\[
  \texttt{rr}_t \;:=\;
    \int \phi_{\text{conn},t}\,\psi_{\text{rem},t}\,gW\,e^{-s_t}\,du
\]
satisfies the asymptotic
\[
  \bigl|\,t^2 \cdot \texttt{rr}_t
    - \tfrac12\,\mathrm{tr}(A_\phi \Sigma A_\psi \Sigma) \cdot D_t\,\bigr|
    \le K/t.
\]

Main term comes from `Q^c_φ · Q_ψ · 1` via `gaussian_quad_quad` (already
proved). Centering of `Q_φ` automatically subtracts the disconnected
trace product `(1/2)tr(A_φ Σ) · (1/2)tr(A_ψ Σ) = μ_φ μ_ψ`.

Currently a sorry. -/
private theorem rescaledIntegral_rr_connected_asymptotic
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    (hψ : ObservableTensorApprox ψ b)
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 *
          (∫ u : ι → ℝ,
              expCovPhiConn V φ H Hinv (0 : ι → ℝ)
                hV.toPotentialTensorApprox hφ t u *
              expCovPsiRem ψ b t u *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
        - (1 / 2 : ℝ) * trASig (hφ.A.comp ((Hinv).comp (hψ.A.comp Hinv)))
              (1 : (ι → ℝ) →L[ℝ] (ι → ℝ))
            * rescaledPartition V t|
        ≤ K / t := by
  -- 10-step plan per `gpt_responses/strategy_stage5_lemmas_attack.md`:
  --
  -- Pointwise: t² · φ_conn · ψ_rem expands to 9 terms (with Q^c_φ = Q_φ - μ_φ):
  --   QQ := Q^c_φ · Q_ψ          (leading)
  --   QC := (1/√t) · Q^c_φ · C_ψ  (parity-vanishing odd)
  --   t · Q^c_φ · R_ψ
  --   CQ := (1/√t) · C_φ · Q_ψ   (parity-vanishing odd)
  --   (1/t) · C_φ · C_ψ
  --   √t · C_φ · R_ψ
  --   t · R_φ · Q_ψ
  --   √t · R_φ · C_ψ
  --   t² · R_φ · R_ψ
  --
  -- Steps (each producing an `O(K/t)` bound on its piece):
  -- 1. **Main coefficient** `gaussian_QcQ_mean`:
  --    `∫ Q^c_φ · Q_ψ · gW = Z · (1/2) trASig (A_φ.comp(Hinv.comp(A_ψ.comp Hinv))) 1`
  --    via `gaussian_quad_quad` + `gaussian_quad_expectation`; the (1/4)tr·tr
  --    disconnected piece cancels against the μ_φ subtraction.
  -- 2. **Apply parity helper P1** to FQQ = QQ - c_QQ:
  --    `|∫ FQQ · gW · exp(-s_t)| ≤ K/t`. The (-V_3/√t) term in the Taylor
  --    expansion of `exp(-s_t)-1` vanishes by parity (FQQ even, V_3 odd).
  -- 3. **Coarse odd-kernel bound** for QC = Q^c_φ · C_ψ:
  --    `|∫ odd · gW · exp(-s_t)| ≤ K/√t` (parity zero + Stage-1 Taylor for the
  --    perturbation correction). Multiplied by 1/√t in the decomposition gives K/t.
  -- 4. **Same** for CQ.
  -- 5-6. **Quad·remainder bounds** for `t · Q^c_φ · R_ψ` and `t · R_φ · Q_ψ`.
  --    Direct domination by polynomial × Gaussian using
  --    `integrable_pow_norm_mul_rescaled_weight`.
  -- 7. **Cubic·cubic** `(1/t) · C_φ · C_ψ`: direct moment bound
  --    `|C_φ C_ψ| ≤ const · ‖u‖^6`, integral O(1), times 1/t gives K/t.
  -- 8. **Cubic·remainder** `√t · C_φ · R_ψ` (and symmetric):
  --    `|C·R| ≤ const · ‖u‖^7 / t^2`, multiplied by √t gives O(1/t^(3/2)) ≤ O(1/t).
  -- 9. **Remainder·remainder** via existing `abs_integral_remainder_remainder_sharp_le`.
  -- 10. **Final assembly**: triangle inequality over the 9 pieces.
  --
  -- Prerequisites (shared with Lemma A): parity helpers P1, P2 — see
  -- `gpt_responses/strategy_stage5_lemmas_attack.md` § "Shared infrastructure".
  --
  -- 2026-04-29 update: GPT consult #2 locked in Path 2 (specialize, not generic
  -- P1) — see `gpt_responses/strategy_stage5_lemmaB_path.md`. Items 1-6 of the
  -- 10-item plan are now in this file as named helpers (compiles, 0 sorry):
  --   1. `fqqKernel A B Hinv u`: doubly-centered quartic FQQ.
  --   2. `fqqKernel_even`: parity (via `quadForm_neg`).
  --   3. `integral_fqqKernel_mul_gaussianWeight_eq_zero`: zero Gaussian mean
  --      (via `gaussian_quad_centered_quad_eq` − constant·Z cancellation).
  --   4. `abs_fqqKernel_le`: `|FQQ(u)| ≤ C · (1 + ‖u‖^4)` polynomial bound.
  --   5. `integral_even_centered_eq_corrected_bracket`: generic transformation
  --      `∫ F · gW · exp(-s_t) = ∫ F · gW · (exp(-s_t) - 1 + t·cV)` for any
  --      centered even kernel.
  --   6. `abs_fqqKernel_mul_gaussianWeight_mul_corrected_bracket_local_le`:
  --      local pointwise bound on `‖u‖ ≤ ρ√t`.
  --   7. `integrable_pow_norm_mul_gaussianWeight_mul_cV`: `‖u‖^k · gW · cV(...)`
  --      integrability for arbitrary `k : ℕ`.
  -- Remaining (~600 LOC): clone-and-adapt of `abs_integral_corrected_bracket_centered_bilinear_le`
  -- in `Multi/CovarianceSharp.lean` (lines 2020-2760) for the FQQ kernel:
  --   • Adapt polynomial bound from `A·B·‖u‖²+|m|` → `C_FQQ·(1+‖u‖^4)`.
  --   • Bump Gaussian moment exponents: Glocal needs degrees 4,6,8,10; Gtail
  --     needs degrees 4,6,7,9.
  --   • Combine local + tail via case analysis at pointwise level.
  -- After that, item 9 (corrected-bracket K/t bound) closes via this clone +
  -- the transformation lemma; item 10 (transport corollary) closes Step 2 of
  -- the 10-step Lemma B plan above.
  sorry

/-- **Centered pair-numerator asymptote (explicit, `lem:laplace_cov2` core)**:
when $\nabla\phi(0) = 0$, the rescaled pair numerator $N_t(\phi\psi)$ has
$t^{-2}$ coefficient `cov2Coefficient_full · D_t / t² + O(D_t / t^3)`, i.e.
\[
  | t^2 \cdot N_t(\phi\psi) - \texttt{cov2\_full} \cdot D_t | \le K/t.
\]
Here `cov2_full = cov2Coefficient + μ_φ · μ_ψ` includes both the connected
4-term coefficient (the theorem's `cov2Coefficient`) and the disconnected
piece $\mathbb{E}_t[\phi]\mathbb{E}_t[\psi]$-product part; the wrapper
`gibbsCov_first_order_rate_explicit` cancels the disconnected piece against
the explicit expectation theorem, leaving the 4-term `cov2Coefficient`.

Proof recipe (per `gpt_responses/strategy_stage5_cov2.md`): decompose via
`pair_product_expansion` and identify the surviving $t^{-2}$ Gaussian terms
using a 6-moment quad·linear·cubic Wick contraction; reuse the sharp-track
remainder/integrability bounds. Currently a sorry. -/
private theorem rescaledNumerator_centered_pair_explicit
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hψ : ObservableTensorApprox ψ b)
    (h_phi_grad_zero : a = 0)
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * rescaledNumerator V t (fun w => φ w * ψ w)
          - cov2Coefficient_full V φ ψ H Hinv a b
              hV.toPotentialTensorApprox hφ hψ
            * rescaledPartition V t|
        ≤ K / t := by
  -- Per `gpt_responses/strategy_stage5_decomposition.md`, decompose:
  --   t² · N(φψ) = μ_φ · (t · N(ψ)) + t·√t · I_cross + t² · I_rr
  -- and bound each piece:
  --   - μ_φ · (t · N(ψ) - μ_ψ · D)  via Stage 4 numerator helper.
  --   - t·√t · I_cross - c_cross · D  via lemma A (cross asymptotic).
  --   - t² · I_rr - c_QQ · D  via lemma B (rr asymptotic).
  -- The disconnected μ_φ μ_ψ piece in cov2_full cancels against the
  -- μ_φ μ_ψ · D contribution of `μ_φ · μ_ψ · D` once Stage 4 is applied.
  set μ_φ : ℝ := expNumeratorCoeff V φ H Hinv a hV.toPotentialTensorApprox hφ
    with hμφ_def
  set μ_ψ : ℝ := expNumeratorCoeff V ψ H Hinv b hV.toPotentialTensorApprox hψ
    with hμψ_def
  set c_QQ : ℝ := (1 / 2 : ℝ) *
      trASig (hφ.A.comp ((Hinv).comp (hψ.A.comp Hinv)))
        (1 : (ι → ℝ) →L[ℝ] (ι → ℝ)) with hc_QQ_def
  set c_cross : ℝ :=
      (1 / 2 : ℝ) * dot (Hinv b) (tensorContractMatrix hφ.Φ Hinv)
      - (1 / 2 : ℝ) * dot b
          (Hinv (hφ.A (Hinv (tensorContractMatrix hV.T Hinv))))
      - (1 / 2 : ℝ) * dot (Hinv b)
          (tensorContractMatrix hV.T (Hinv.comp (hφ.A.comp Hinv)))
    with hc_cross_def
  -- cov2Coefficient_full = c_QQ + c_cross + μ_φ μ_ψ.
  have h_full_eq : cov2Coefficient_full V φ ψ H Hinv a b
        hV.toPotentialTensorApprox hφ hψ
      = c_QQ + c_cross + μ_φ * μ_ψ := by
    simp [cov2Coefficient_full, cov2Coefficient,
          hc_QQ_def, hc_cross_def, hμφ_def, hμψ_def]
    ring
  -- Specialize hypothesis a = 0.
  subst h_phi_grad_zero
  -- Pull the three asymptotic constants.
  obtain ⟨K_dec_unused, T_dec, hT_dec, _⟩ : ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ True := ⟨0, 1, le_refl _, trivial⟩
  obtain ⟨K_ψN, T_ψN, hT_ψN, h_ψN⟩ :=
    rescaledNumerator_first_order_centered_explicit V ψ H Hinv b hV hψ
      hGauss.toLaplaceCov4MomentHypotheses
  obtain ⟨K_A, T_A, hT_A, h_A⟩ :=
    rescaledIntegral_cross_linear_connected_asymptotic V φ H Hinv b hV hφ hGauss
  obtain ⟨K_B, T_B, hT_B, h_B⟩ :=
    rescaledIntegral_rr_connected_asymptotic V φ ψ H Hinv b hV hφ hψ hGauss
  -- Final K and T₀.
  set K : ℝ := |μ_φ| * K_ψN + K_A + K_B with hK_def
  refine ⟨K,
    max T_ψN (max T_A T_B),
    le_max_of_le_left hT_ψN, ?_⟩
  intro t ht
  have ht_ψN : T_ψN ≤ t := le_of_max_le_left ht
  have ht_pp : max T_A T_B ≤ t := le_of_max_le_right ht
  have ht_A : T_A ≤ t := le_of_max_le_left ht_pp
  have ht_B : T_B ≤ t := le_of_max_le_right ht_pp
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans hT_ψN ht_ψN)
  have ht1 : 1 ≤ t := le_trans hT_ψN ht_ψN
  -- Apply the decomposition.
  have h_decomp := rescaledNumerator_pair_decompose_centered_a_zero V φ ψ H Hinv b
    hV.toPotentialTensorApprox hφ hψ hGauss.toLaplaceCovHypotheses ht1
  -- Substitute and rewrite the goal.
  rw [h_decomp, h_full_eq]
  set I_A : ℝ := t * Real.sqrt t *
        (∫ u : ι → ℝ, dot b u *
            expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV.toPotentialTensorApprox hφ t u *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) with hI_A_def
  set I_B : ℝ := t ^ 2 *
        (∫ u : ι → ℝ,
            expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV.toPotentialTensorApprox hφ t u *
            expCovPsiRem ψ b t u *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) with hI_B_def
  -- Goal: |μ_φ · t · N(ψ) + I_A + I_B - (c_QQ + c_cross + μ_φ μ_ψ) · D| ≤ K/t.
  -- Reorganize: μ_φ·t·N(ψ) - μ_φ μ_ψ · D = μ_φ · (t · N(ψ) - μ_ψ · D).
  have h_reorg :
      μ_φ * (t * rescaledNumerator V t ψ) + I_A + I_B
        - (c_QQ + c_cross + μ_φ * μ_ψ) * rescaledPartition V t
      = μ_φ * (t * rescaledNumerator V t ψ - μ_ψ * rescaledPartition V t)
        + (I_A - c_cross * rescaledPartition V t)
        + (I_B - c_QQ * rescaledPartition V t) := by ring
  rw [h_reorg]
  -- Bound piece 1: |μ_φ · (t · N(ψ) - μ_ψ · D)| ≤ |μ_φ| · K_ψN / t.
  have h_ψN_t : |rescaledNumerator V t ψ
      - rescaledPartition V t * (μ_ψ / t)| ≤ K_ψN / t ^ 2 := h_ψN t ht_ψN
  have hpiece1 : |μ_φ * (t * rescaledNumerator V t ψ
        - μ_ψ * rescaledPartition V t)| ≤ |μ_φ| * K_ψN / t := by
    rw [abs_mul]
    have h_alg : t * rescaledNumerator V t ψ - μ_ψ * rescaledPartition V t
        = t * (rescaledNumerator V t ψ - rescaledPartition V t * (μ_ψ / t)) := by
      have ht_ne : t ≠ 0 := ht_pos.ne'
      field_simp
    rw [h_alg, abs_mul, abs_of_pos ht_pos]
    have : t * (K_ψN / t ^ 2) = K_ψN / t := by
      have : t ^ 2 = t * t := sq t
      field_simp
    calc |μ_φ| * (t * |rescaledNumerator V t ψ
            - rescaledPartition V t * (μ_ψ / t)|)
        ≤ |μ_φ| * (t * (K_ψN / t ^ 2)) := by
          gcongr
      _ = |μ_φ| * K_ψN / t := by rw [this]; ring
  have hpiece2 : |I_A - c_cross * rescaledPartition V t| ≤ K_A / t := by
    rw [hI_A_def, hc_cross_def]; exact h_A t ht_A
  have hpiece3 : |I_B - c_QQ * rescaledPartition V t| ≤ K_B / t := by
    rw [hI_B_def, hc_QQ_def]; exact h_B t ht_B
  -- Combine via triangle inequality.
  calc |μ_φ * (t * rescaledNumerator V t ψ - μ_ψ * rescaledPartition V t)
          + (I_A - c_cross * rescaledPartition V t)
          + (I_B - c_QQ * rescaledPartition V t)|
      ≤ |μ_φ * (t * rescaledNumerator V t ψ - μ_ψ * rescaledPartition V t)|
        + |I_A - c_cross * rescaledPartition V t|
        + |I_B - c_QQ * rescaledPartition V t| := by
        have h1 := abs_add_le
            (μ_φ * (t * rescaledNumerator V t ψ - μ_ψ * rescaledPartition V t)
              + (I_A - c_cross * rescaledPartition V t))
            (I_B - c_QQ * rescaledPartition V t)
        have h2 := abs_add_le
            (μ_φ * (t * rescaledNumerator V t ψ - μ_ψ * rescaledPartition V t))
            (I_A - c_cross * rescaledPartition V t)
        linarith
    _ ≤ |μ_φ| * K_ψN / t + K_A / t + K_B / t :=
        add_le_add (add_le_add hpiece1 hpiece2) hpiece3
    _ = K / t := by rw [hK_def]; ring

/-- **Sharp covariance rate (explicit coefficient, `lem:laplace_cov2`)**:
for $\phi$ vanishing to second order ($\phi(0) = 0$, $\nabla\phi(0) = 0$)
and $\psi$ with $\psi(0) = 0$ and $\nabla\psi(0) = b$,
$$
  \mathrm{Cov}_t[\phi,\psi] = \tfrac{1}{t^2}\Big[\tfrac{1}{2}\mathrm{tr}(A\Sigma B\Sigma)
    + \tfrac{1}{2}(\Sigma b)\!\cdot\!(\Phi{:}\Sigma)
    - \tfrac{1}{2}b^\top\Sigma A\Sigma(T{:}\Sigma)
    - \tfrac{1}{2}(\Sigma b)\!\cdot\!(T{:}(\Sigma A\Sigma))\Big] + o(t^{-2}),
$$
where $A = \nabla^2\phi(0)$, $\Phi = \nabla^3\phi(0)$, $b = \nabla\psi(0)$,
$B = \nabla^2\psi(0)$, $T = \nabla^3 V(0)$, $\Sigma = H^{-1}$.

The conclusion uses the named coefficient `cov2Coefficient`:
`|t² · gibbsCov V t φ ψ - cov2Coefficient ...| ≤ K/t`.

The proof composes:
1. `rescaledNumerator_centered_pair_explicit`:
   `|t² · N(φψ) - cov2_full · D| ≤ K_N/t`.
2. The existing weak denominator lower bound `D ≥ Z/2`.
3. `gibbsExpectation_first_order_rate_explicit` (Stage 4):
   `|2t · E_t[φ] - 2 μ_φ| ≤ K_φ/t`, similarly for `ψ`.
The disconnected piece `μ_φ · μ_ψ` from `cov2_full` cancels against
`(t · E_t[φ])(t · E_t[ψ]) → μ_φ · μ_ψ`, leaving `cov2Coefficient`. -/
theorem gibbsCov_first_order_rate_explicit
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hψ : ObservableTensorApprox ψ b)
    (h_phi_grad_zero : a = 0)
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * gibbsCov V t φ ψ -
          cov2Coefficient V φ ψ H Hinv a b
            hV.toPotentialTensorApprox hφ hψ|
        ≤ K / t := by
  -- Bookkeeping abbreviations.
  set μ_φ : ℝ := expNumeratorCoeff V φ H Hinv a hV.toPotentialTensorApprox hφ
    with hμφ_def
  set μ_ψ : ℝ := expNumeratorCoeff V ψ H Hinv b hV.toPotentialTensorApprox hψ
    with hμψ_def
  set ν   : ℝ := cov2Coefficient V φ ψ H Hinv a b
      hV.toPotentialTensorApprox hφ hψ with hν_def
  set ν_full : ℝ := cov2Coefficient_full V φ ψ H Hinv a b
      hV.toPotentialTensorApprox hφ hψ with hνfull_def
  have hν_full_eq : ν_full = ν + μ_φ * μ_ψ := by
    simp [hνfull_def, hν_def, hμφ_def, hμψ_def, cov2Coefficient_full]
  -- Pull the centered-pair numerator bound (sorry'd helper).
  obtain ⟨K_N, T_N, hT_N, h_N⟩ :=
    rescaledNumerator_centered_pair_explicit V φ ψ H Hinv a b
      hV hφ hψ h_phi_grad_zero hGauss
  -- Pull the existing denominator lower bound.
  obtain ⟨T_D, hT_D, h_D⟩ :=
    rescaledPartition_ge_half_gaussianZ V H Hinv
      hV.toPotentialJetApprox.toPotentialApprox
      hGauss.toLaplaceCovHypotheses
  -- Pull Stage 4 explicit expectation bounds for φ and ψ.
  obtain ⟨K_φ, T_φ, hT_φ, h_φ⟩ :=
    gibbsExpectation_first_order_rate_explicit V φ H Hinv a hV hφ
      hGauss.toLaplaceCov4MomentHypotheses
  obtain ⟨K_ψ, T_ψ, hT_ψ, h_ψ⟩ :=
    gibbsExpectation_first_order_rate_explicit V ψ H Hinv b hV hψ
      hGauss.toLaplaceCov4MomentHypotheses
  have hZ_pos : 0 < gaussianZ H := hGauss.Z_pos
  -- Final K and T₀.
  set K : ℝ := 2 * K_N / gaussianZ H
      + (K_φ * |μ_ψ| + |μ_φ| * K_ψ) / 2
      + K_φ * K_ψ / 4 with hK_def
  refine ⟨K,
    max T_N (max T_D (max T_φ T_ψ)),
    le_max_of_le_left hT_N, ?_⟩
  intro t ht
  have ht_N : T_N ≤ t := le_of_max_le_left ht
  have ht_rest : max T_D (max T_φ T_ψ) ≤ t := le_of_max_le_right ht
  have ht_D : T_D ≤ t := le_of_max_le_left ht_rest
  have ht_pp : max T_φ T_ψ ≤ t := le_of_max_le_right ht_rest
  have ht_φ : T_φ ≤ t := le_of_max_le_left ht_pp
  have ht_ψ : T_ψ ≤ t := le_of_max_le_right ht_pp
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans hT_N ht_N)
  have hP_ge : gaussianZ H / 2 ≤ rescaledPartition V t := h_D t ht_D
  have hP_pos : 0 < rescaledPartition V t :=
    lt_of_lt_of_le (by linarith) hP_ge
  -- Specific bounds at t.
  have h_N_t := h_N t ht_N
  have h_φ_t := h_φ t ht_φ
  have h_ψ_t := h_ψ t ht_ψ
  -- Goal-side: rewrite gibbsCov via rescaledCov.
  rw [gibbsCov_eq_rescaledCov V φ ψ ht_pos]
  unfold rescaledCov
  -- Rewrite ν using the def-set.
  show |t ^ 2 * (rescaledExpectation V t (fun w => φ w * ψ w)
        - rescaledExpectation V t φ * rescaledExpectation V t ψ) - ν| ≤ K / t
  -- Decomposition (cleaner with `t² · E_t[φψ] - ν_full` on one side
  -- and `(t · E_φ)(t · E_ψ) - μ_φ · μ_ψ` on the other; their
  -- difference equals `t² · gibbsCov - ν` since `ν_full = ν + μ_φ μ_ψ`).
  have h_decompose :
      t ^ 2 * (rescaledExpectation V t (fun w => φ w * ψ w)
            - rescaledExpectation V t φ * rescaledExpectation V t ψ) - ν
        = (t ^ 2 * rescaledExpectation V t (fun w => φ w * ψ w) - ν_full)
          - ((t * rescaledExpectation V t φ) *
              (t * rescaledExpectation V t ψ) - μ_φ * μ_ψ) := by
    rw [hν_full_eq]; ring
  rw [h_decompose]
  -- Bound piece 1: |t² · E_t[φψ] - ν_full| ≤ 2·K_N / (Z·t).
  have hpart1 :
      |t ^ 2 * rescaledExpectation V t (fun w => φ w * ψ w) - ν_full|
        ≤ 2 * K_N / gaussianZ H / t := by
    -- t² · E_t[φψ] - ν_full = (t² · N(φψ) - ν_full · D) / D.
    have h_centered_eq :
        t ^ 2 * rescaledExpectation V t (fun w => φ w * ψ w) - ν_full
          = (t ^ 2 * rescaledNumerator V t (fun w => φ w * ψ w)
              - ν_full * rescaledPartition V t) / rescaledPartition V t := by
      unfold rescaledExpectation
      field_simp
    rw [h_centered_eq, abs_div, abs_of_pos hP_pos]
    calc |t ^ 2 * rescaledNumerator V t (fun w => φ w * ψ w)
              - ν_full * rescaledPartition V t| / rescaledPartition V t
        ≤ (K_N / t) / rescaledPartition V t :=
          div_le_div_of_nonneg_right h_N_t hP_pos.le
      _ ≤ (K_N / t) / (gaussianZ H / 2) := by
          apply div_le_div_of_nonneg_left _ (by linarith) hP_ge
          exact le_trans (abs_nonneg _) h_N_t
      _ = 2 * K_N / gaussianZ H / t := by field_simp
  -- For piece 2, convert Stage 4 bounds to the `|t · E_t[φ] - μ_φ|` form.
  -- Stage 4 gives: |2t · E - 2 μ_•| ≤ K_•/t, i.e. |t · E - μ_•| ≤ K_•/(2t).
  have h_φ_centered : |t * rescaledExpectation V t φ - μ_φ|
        ≤ K_φ / (2 * t) := by
    have h_eq : 2 * t * gibbsExpectation V t φ - trASig hφ.A Hinv
          + dot (Hinv a) (tensorContractMatrix hV.T Hinv)
          = 2 * (t * rescaledExpectation V t φ - μ_φ) := by
      rw [gibbsExpectation_eq_rescaledExpectation V φ ht_pos, hμφ_def,
          expNumeratorCoeff]; ring
    have h_φ_t' := h_φ_t
    rw [h_eq] at h_φ_t'
    rw [show (K_φ / (2 * t) : ℝ) = K_φ / t / 2 by field_simp]
    rw [show |2 * (t * rescaledExpectation V t φ - μ_φ)|
          = 2 * |t * rescaledExpectation V t φ - μ_φ| from by
        rw [abs_mul]; simp] at h_φ_t'
    linarith
  have h_ψ_centered : |t * rescaledExpectation V t ψ - μ_ψ|
        ≤ K_ψ / (2 * t) := by
    have h_eq : 2 * t * gibbsExpectation V t ψ - trASig hψ.A Hinv
          + dot (Hinv b) (tensorContractMatrix hV.T Hinv)
          = 2 * (t * rescaledExpectation V t ψ - μ_ψ) := by
      rw [gibbsExpectation_eq_rescaledExpectation V ψ ht_pos, hμψ_def,
          expNumeratorCoeff]; ring
    have h_ψ_t' := h_ψ_t
    rw [h_eq] at h_ψ_t'
    rw [show (K_ψ / (2 * t) : ℝ) = K_ψ / t / 2 by field_simp]
    rw [show |2 * (t * rescaledExpectation V t ψ - μ_ψ)|
          = 2 * |t * rescaledExpectation V t ψ - μ_ψ| from by
        rw [abs_mul]; simp] at h_ψ_t'
    linarith
  -- Bound piece 2: |(t · E_φ)(t · E_ψ) - μ_φ · μ_ψ| ≤ (K_φ |μ_ψ| + |μ_φ| K_ψ)/(2t)
  --                                                  + K_φ K_ψ / (4t²).
  -- Use the identity: AB - ab = (A - a) B + a (B - b).
  have hpart2 :
      |(t * rescaledExpectation V t φ) * (t * rescaledExpectation V t ψ)
          - μ_φ * μ_ψ|
        ≤ (K_φ * |μ_ψ| + |μ_φ| * K_ψ) / (2 * t) + K_φ * K_ψ / (4 * t ^ 2) := by
    set A : ℝ := t * rescaledExpectation V t φ with hA_def
    set B : ℝ := t * rescaledExpectation V t ψ with hB_def
    have h_id : A * B - μ_φ * μ_ψ
        = (A - μ_φ) * (B - μ_ψ) + (A - μ_φ) * μ_ψ + μ_φ * (B - μ_ψ) := by ring
    rw [h_id]
    have hA_diff : |A - μ_φ| ≤ K_φ / (2 * t) := h_φ_centered
    have hB_diff : |B - μ_ψ| ≤ K_ψ / (2 * t) := h_ψ_centered
    have h_t2_pos : 0 < 2 * t := by linarith
    have hK_φ_nn : 0 ≤ K_φ := by
      have h0 : 0 ≤ K_φ / (2 * t) := le_trans (abs_nonneg _) h_φ_centered
      have := mul_nonneg h0 h_t2_pos.le
      have hsimp : K_φ / (2 * t) * (2 * t) = K_φ := by field_simp
      linarith [hsimp ▸ this]
    have hK_ψ_nn : 0 ≤ K_ψ := by
      have h0 : 0 ≤ K_ψ / (2 * t) := le_trans (abs_nonneg _) h_ψ_centered
      have := mul_nonneg h0 h_t2_pos.le
      have hsimp : K_ψ / (2 * t) * (2 * t) = K_ψ := by field_simp
      linarith [hsimp ▸ this]
    calc |(A - μ_φ) * (B - μ_ψ) + (A - μ_φ) * μ_ψ + μ_φ * (B - μ_ψ)|
        ≤ |(A - μ_φ) * (B - μ_ψ)| + |(A - μ_φ) * μ_ψ| + |μ_φ * (B - μ_ψ)| := by
          have := abs_add_le ((A - μ_φ) * (B - μ_ψ) + (A - μ_φ) * μ_ψ)
              (μ_φ * (B - μ_ψ))
          have h2 := abs_add_le ((A - μ_φ) * (B - μ_ψ)) ((A - μ_φ) * μ_ψ)
          linarith
      _ = |A - μ_φ| * |B - μ_ψ| + |A - μ_φ| * |μ_ψ| + |μ_φ| * |B - μ_ψ| := by
          rw [abs_mul, abs_mul, abs_mul]
      _ ≤ (K_φ / (2 * t)) * (K_ψ / (2 * t))
          + (K_φ / (2 * t)) * |μ_ψ| + |μ_φ| * (K_ψ / (2 * t)) := by
          gcongr
      _ = (K_φ * |μ_ψ| + |μ_φ| * K_ψ) / (2 * t) + K_φ * K_ψ / (4 * t ^ 2) := by
          field_simp; ring
  -- Combine with triangle inequality.
  calc |(t ^ 2 * rescaledExpectation V t (fun w => φ w * ψ w) - ν_full)
          - ((t * rescaledExpectation V t φ) *
              (t * rescaledExpectation V t ψ) - μ_φ * μ_ψ)|
      ≤ |t ^ 2 * rescaledExpectation V t (fun w => φ w * ψ w) - ν_full|
        + |(t * rescaledExpectation V t φ) *
              (t * rescaledExpectation V t ψ) - μ_φ * μ_ψ| := abs_sub _ _
    _ ≤ 2 * K_N / gaussianZ H / t
        + ((K_φ * |μ_ψ| + |μ_φ| * K_ψ) / (2 * t) + K_φ * K_ψ / (4 * t ^ 2)) :=
        add_le_add hpart1 hpart2
    _ ≤ K / t := by
        rw [hK_def]
        have ht_ge_1 : 1 ≤ t := le_trans hT_N ht_N
        have h_inv_t_ge : (1 : ℝ) / t ^ 2 ≤ 1 / t := by
          have : t ≤ t ^ 2 := by nlinarith [ht_ge_1]
          have ht_pos2 : 0 < t ^ 2 := by positivity
          rw [div_le_div_iff₀ ht_pos2 ht_pos]
          linarith
        have h_t2_pos : 0 < 2 * t := by linarith
        have hK_φ_nn : 0 ≤ K_φ := by
          have h0 : 0 ≤ K_φ / (2 * t) := le_trans (abs_nonneg _) h_φ_centered
          have := mul_nonneg h0 h_t2_pos.le
          have hsimp : K_φ / (2 * t) * (2 * t) = K_φ := by field_simp
          linarith [hsimp ▸ this]
        have hK_ψ_nn : 0 ≤ K_ψ := by
          have h0 : 0 ≤ K_ψ / (2 * t) := le_trans (abs_nonneg _) h_ψ_centered
          have := mul_nonneg h0 h_t2_pos.le
          have hsimp : K_ψ / (2 * t) * (2 * t) = K_ψ := by field_simp
          linarith [hsimp ▸ this]
        have h_K_φψ_nn : 0 ≤ K_φ * K_ψ := mul_nonneg hK_φ_nn hK_ψ_nn
        have h_t2_le : K_φ * K_ψ / (4 * t ^ 2) ≤ K_φ * K_ψ / (4 * t) := by
          apply div_le_div_of_nonneg_left h_K_φψ_nn (by linarith)
          have : t ≤ t ^ 2 := by nlinarith [ht_ge_1]
          linarith
        have h_terms_eq : 2 * K_N / gaussianZ H / t
            + (K_φ * |μ_ψ| + |μ_φ| * K_ψ) / (2 * t)
            + K_φ * K_ψ / (4 * t)
          = (2 * K_N / gaussianZ H + (K_φ * |μ_ψ| + |μ_φ| * K_ψ) / 2
              + K_φ * K_ψ / 4) / t := by
          field_simp
        linarith [h_t2_le]

end MainTheorems

end Laplace.Multi
