/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Multi.CovarianceSharp

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
  -- h_pair1', h_pair2 (sorry'd): the two tr(AΣBΣ) identifications.
  -- Final calc to assemble: deferred.
  sorry

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
specialised Gaussian contraction lemma — used in `lem:laplace_cov2` term 3. -/
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
  sorry

end GaussianContractions

section MainTheorems

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
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |2 * t * gibbsExpectation V t φ - trASig hφ.A Hinv
          + dot (Hinv a) (tensorContractMatrix hV.T Hinv)| ≤ K / t := by
  sorry

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

The Lean theorem packages the explicit coefficient as a single `ℝ`-valued
function `cov2_coefficient` of `(hV, hφ, hψ)` so the conclusion has the form
`|t² · gibbsCov V t φ ψ - cov2_coefficient| ≤ K/t`, i.e. a sharp $o(t^{-2})$
remainder. The decomposition into the four named terms (and the `tr(A\Sigma)`
cancellation between connected and disconnected pieces) is exposed via the
helper lemma `cov2_coefficient_eq`. -/
theorem gibbsCov_first_order_rate_explicit
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hψ : ObservableTensorApprox ψ b)
    (h_phi_grad_zero : a = 0)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * gibbsCov V t φ ψ -
        ((1 / 2 : ℝ) * trASig (hφ.A.comp ((Hinv).comp (hψ.A.comp Hinv))) (1 : (ι → ℝ) →L[ℝ] (ι → ℝ))
        + (1 / 2 : ℝ) * dot (Hinv b) (tensorContractMatrix hφ.Φ Hinv)
        - (1 / 2 : ℝ) * dot b (Hinv (hφ.A (Hinv (tensorContractMatrix hV.T Hinv))))
        - (1 / 2 : ℝ) * dot (Hinv b)
            (tensorContractMatrix hV.T (Hinv.comp (hφ.A.comp Hinv))))|
      ≤ K / t := by
  sorry

end MainTheorems

end Laplace.Multi
