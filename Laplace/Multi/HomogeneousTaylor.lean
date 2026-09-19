/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AllOrders
import Laplace.Multi.SufficientFamilies

/-!
# Taylor terms of homogeneous functions

For a smooth function `Q` homogeneous of degree `k` (`Q (s • x) = s^k Q x`),
the iterated derivatives at the origin vanish in every order `j ≠ k`
(`iteratedFDeriv_zero_of_isHomogeneous`: scaling gives
`s^j D^jQ(0) = s^k D^jQ(0)`, so `D^jQ(0) = 0` at `s = 2`), and the degree-`k`
Taylor term is `Q` itself (`taylorHomogeneousTerm_of_isHomogeneous`: the
`k`-th derivative along the line `s ↦ s • x` of `s ↦ s^k Q x` is `k! Q x`).
The quadratic form `qform H` is smooth and homogeneous of degree `2`, and
every degree-`k` homogeneous polynomial in `homogPolySpan d k` is smooth;
these feed the kernel-direction instance for the sufficient-family
obstruction.
-/

open Asymptotics Filter
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-- **Scaling of iterated derivatives of a homogeneous function**:
`s^j D^jQ(s x) = s^k D^jQ(x)`. -/
theorem iteratedFDeriv_smul_eq_of_isHomogeneous {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q)
    {k : ℕ} (hhom : IsHomogeneousOfDegree k Q) (j : ℕ) (s : ℝ) (x : EuclidD d) :
    s ^ j • iteratedFDeriv ℝ j Q (s • x) = s ^ k • iteratedFDeriv ℝ j Q x := by
  set g : EuclidD d →L[ℝ] EuclidD d := s • ContinuousLinearMap.id ℝ (EuclidD d) with hg_def
  have hg : ∀ y, g y = s • y := fun y ↦ by simp [hg_def]
  have hcomp : Q ∘ g = s ^ k • Q := by
    funext y
    simp only [Function.comp_apply, hg, hhom s y, Pi.smul_apply, smul_eq_mul]
  have h1 := g.iteratedFDeriv_comp_right hQ x (natCast_le_infty j)
  rw [hcomp, hg] at h1
  have h2 : iteratedFDeriv ℝ j (s ^ k • Q) x = s ^ k • iteratedFDeriv ℝ j Q x :=
    iteratedFDeriv_const_smul_apply (hQ.contDiffAt.of_le (natCast_le_infty j))
  rw [h2] at h1
  ext v
  have h3 := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclidD d) ℝ ↦ T v) h1
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hg] at h3
  rw [ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ j Q (s • x)) (fun _ ↦ s) v,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h3
  rw [smul_apply, smul_apply]
  exact h3.symm

/-- The iterated derivatives of a degree-`k` homogeneous smooth function vanish
at the origin in every order `j ≠ k`. -/
theorem iteratedFDeriv_zero_of_isHomogeneous {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q)
    {k : ℕ} (hhom : IsHomogeneousOfDegree k Q) {j : ℕ} (hj : j ≠ k) :
    iteratedFDeriv ℝ j Q 0 = 0 := by
  have h := iteratedFDeriv_smul_eq_of_isHomogeneous hQ hhom j 2 0
  rw [smul_zero] at h
  have h' : ((2 : ℝ) ^ j - 2 ^ k) • iteratedFDeriv ℝ j Q 0 = 0 := by
    rw [sub_smul, h, sub_self]
  have hne : (2 : ℝ) ^ j - 2 ^ k ≠ 0 := by
    refine sub_ne_zero.mpr fun heq ↦ hj ?_
    have : (2 : ℕ) ^ j = 2 ^ k := by exact_mod_cast heq
    exact Nat.pow_right_injective le_rfl this
  exact (smul_eq_zero.mp h').resolve_left hne

/-- The degree-`k` derivative of a degree-`k` homogeneous smooth function on the
diagonal is `k! Q x`. -/
theorem iteratedFDeriv_diag_of_isHomogeneous {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q)
    {k : ℕ} (hhom : IsHomogeneousOfDegree k Q) (x : EuclidD d) :
    iteratedFDeriv ℝ k Q 0 (fun _ ↦ x) = (k.factorial : ℝ) * Q x := by
  set g : ℝ →L[ℝ] EuclidD d := (ContinuousLinearMap.id ℝ ℝ).smulRight x with hg_def
  have hg : ∀ s : ℝ, g s = s • x := fun s ↦ by simp [hg_def]
  have hcomp : Q ∘ g = fun s ↦ Q x * s ^ k := by
    funext s
    simp only [Function.comp_apply, hg, hhom s x, mul_comm]
  have h1 := g.iteratedFDeriv_comp_right hQ 0 (natCast_le_infty k)
  have h3 := congrArg
    (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ ℝ) ℝ ↦ T (fun _ ↦ (1 : ℝ))) h1
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hg, zero_smul,
    one_smul] at h3
  rw [← iteratedDeriv_eq_iteratedFDeriv, hcomp] at h3
  have hcd : ContDiffAt ℝ k (fun s : ℝ ↦ s ^ k) 0 := (contDiff_id.pow k).contDiffAt
  rw [← h3, iteratedDeriv_const_mul (f := fun s : ℝ ↦ s ^ k) (Q x) hcd,
    iteratedDeriv_pow, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one]
  ring

/-- **Taylor terms of a homogeneous function**: `T_j Q = Q` if `j = k`, else `0`. -/
theorem taylorHomogeneousTerm_of_isHomogeneous {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q)
    {k : ℕ} (hhom : IsHomogeneousOfDegree k Q) (j : ℕ) :
    taylorHomogeneousTerm j Q = if j = k then Q else 0 := by
  funext x
  unfold taylorHomogeneousTerm
  split_ifs with h
  · subst h
    rw [iteratedFDeriv_diag_of_isHomogeneous hQ hhom]
    have : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    field_simp
  · rw [iteratedFDeriv_zero_of_isHomogeneous hQ hhom h]
    simp

/-! ### Smoothness and homogeneity of the building blocks -/

/-- The quadratic form is smooth. -/
theorem contDiff_qform (H : Matrix (Fin d) (Fin d) ℝ) : ContDiff ℝ ∞ (qform H) :=
  ContDiff.inner ℝ contDiff_id (Matrix.toEuclideanCLM (𝕜 := ℝ) H).contDiff

/-- The quadratic form is homogeneous of degree `2`. -/
theorem isHomogeneousOfDegree_qform (H : Matrix (Fin d) (Fin d) ℝ) :
    IsHomogeneousOfDegree 2 (qform H) := by
  intro a x
  unfold qform
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp only [RCLike.conj_to_real]
  ring

/-- Members of the degree-`k` homogeneous polynomial span are smooth. -/
theorem contDiff_of_mem_homogPolySpan {k : ℕ} {Q : EuclidD d → ℝ} (hQ : Q ∈ homogPolySpan d k) :
    ContDiff ℝ ∞ Q := by
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact contDiff_monomialTest m
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

end Laplace.Multi
