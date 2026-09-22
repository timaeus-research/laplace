/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RotatedDerivatives

/-!
# The rotated tensors as Fréchet derivatives

`Laplace.Multi.RotatedDerivatives` identified the note's `H`, `T`, `Q₄` for E2's rotated oscillator
`L∘A = rotatedAnharmonic Q c lam alpha gamma` through iterated one-dimensional derivatives along
coordinate lines, `partialD i f w = d/ds f(w + s eᵢ)|₀`. This file bridges to Mathlib's derivative:

* `partialD_eq_fderiv`: `partialD i f w = fderiv ℝ f w eᵢ` for `f` differentiable at `w`;
* `partialD_iteratedFDeriv`: one rung, `partialD i (fun y => Dⁿf(y)[m]) x = Dⁿ⁺¹f(x)[eᵢ, m]`,
  from `fderiv_continuousMultilinear_apply_const_apply` and `iteratedFDeriv_succ_apply_left`;
* `partialD1_eq_iteratedFDeriv` … `partialD4_eq_iteratedFDeriv`: the tower, for `ContDiff ℝ n f`;
* `contDiff_rotatedAnharmonic`: `L∘A` is `Cⁿ` for every `n`;
* `fderiv_rotatedAnharmonic_center`: `fderiv ℝ (L∘A) c = 0` (the centre is a critical point);
* `iteratedFDeriv2_rotatedAnharmonic_center`, `iteratedFDeriv3_…`, `iteratedFDeriv4_…`:
  `D²(L∘A)(c)[eⱼ, eₖ] = (Q diag λ Qᵀ)ⱼₖ`, `D³(L∘A)(c)[eᵢ, eⱼ, eₖ] = rotT Q α i j k`,
  `D⁴(L∘A)(c)[eᵢ, eⱼ, eₖ, eₗ] = rotQ Q γ i j k l`.

So the tensors that enter `oneLoopCov_rot`, `meanShift_rot`, `covKFormula_rot` and
`twoLoopEnergy_rot` are the second, third and fourth Fréchet derivatives of the potential at its
minimum, in Mathlib's `iteratedFDeriv`, as the note's `T = D³L(w*)`, `Q = D⁴L(w*)` intend.
-/

open Matrix

namespace Laplace.Multi

variable {d : ℕ}

/-- The directional derivative along `eᵢ` is the Fréchet derivative on `eᵢ`. -/
theorem partialD_eq_fderiv {f : (Fin d → ℝ) → ℝ} {w : Fin d → ℝ} (hf : DifferentiableAt ℝ f w)
    (i : Fin d) : partialD i f w = fderiv ℝ f w (Pi.single i 1) := by
  have hline : HasDerivAt (fun s : ℝ => w + s • (Pi.single i 1 : Fin d → ℝ)) (Pi.single i 1) 0 := by
    have h := ((hasDerivAt_id' (x := (0 : ℝ))).smul_const (Pi.single i 1 : Fin d → ℝ)).const_add w
    simpa using h
  have hw : w + (0 : ℝ) • (Pi.single i 1 : Fin d → ℝ) = w := by simp
  have hcomp := HasFDerivAt.comp_hasDerivAt (l := f)
    (f := fun s : ℝ => w + s • (Pi.single i 1 : Fin d → ℝ)) (x := (0 : ℝ))
    (by rw [hw]; exact hf.hasFDerivAt) hline
  unfold partialD
  exact hcomp.deriv

/-- One rung: a directional derivative of `y ↦ Dⁿf(y)[m]` is `Dⁿ⁺¹f(x)[eᵢ, m]`. -/
theorem partialD_iteratedFDeriv {n : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ (n + 1) f)
    (m : Fin n → (Fin d → ℝ)) (i : Fin d) (x : Fin d → ℝ) :
    partialD i (fun y => iteratedFDeriv ℝ n f y m) x =
      iteratedFDeriv ℝ (n + 1) f x (Fin.cons (Pi.single i 1) m) := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  rw [partialD_eq_fderiv ((hdiff x).continuousMultilinear_apply_const m) i,
    fderiv_continuousMultilinear_apply_const_apply (hdiff x) m, iteratedFDeriv_succ_apply_left,
    Fin.cons_zero, Fin.tail_cons]

theorem partialD1_eq_iteratedFDeriv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (k : Fin d)
    (x : Fin d → ℝ) : partialD k f x = iteratedFDeriv ℝ 1 f x ![Pi.single k 1] := by
  have h0 : f = fun y => iteratedFDeriv ℝ 0 f y ![] := by
    funext y; rw [iteratedFDeriv_zero_apply]
  conv_lhs => rw [h0]
  exact partialD_iteratedFDeriv hf ![] k x

theorem partialD2_eq_iteratedFDeriv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (j k : Fin d)
    (x : Fin d → ℝ) :
    partialD j (partialD k f) x = iteratedFDeriv ℝ 2 f x ![Pi.single j 1, Pi.single k 1] := by
  have h1 : partialD k f = fun y => iteratedFDeriv ℝ 1 f y ![Pi.single k 1] :=
    funext fun y => partialD1_eq_iteratedFDeriv (hf.of_le (by norm_num)) k y
  rw [h1]
  exact partialD_iteratedFDeriv hf _ j x

theorem partialD3_eq_iteratedFDeriv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ 3 f) (i j k : Fin d)
    (x : Fin d → ℝ) :
    partialD i (partialD j (partialD k f)) x =
      iteratedFDeriv ℝ 3 f x ![Pi.single i 1, Pi.single j 1, Pi.single k 1] := by
  have h2 : partialD j (partialD k f) =
      fun y => iteratedFDeriv ℝ 2 f y ![Pi.single j 1, Pi.single k 1] :=
    funext fun y => partialD2_eq_iteratedFDeriv (hf.of_le (by norm_num)) j k y
  rw [h2]
  exact partialD_iteratedFDeriv hf _ i x

theorem partialD4_eq_iteratedFDeriv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ 4 f) (i j k l : Fin d)
    (x : Fin d → ℝ) :
    partialD i (partialD j (partialD k (partialD l f))) x =
      iteratedFDeriv ℝ 4 f x ![Pi.single i 1, Pi.single j 1, Pi.single k 1, Pi.single l 1] := by
  have h3 : partialD j (partialD k (partialD l f)) =
      fun y => iteratedFDeriv ℝ 3 f y ![Pi.single j 1, Pi.single k 1, Pi.single l 1] :=
    funext fun y => partialD3_eq_iteratedFDeriv (hf.of_le (by norm_num)) j k l y
  rw [h3]
  exact partialD_iteratedFDeriv hf _ i x

theorem contDiff_anharmonicPotential (lam alpha gamma : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (OneD.anharmonicPotential lam alpha gamma) := by
  unfold OneD.anharmonicPotential
  fun_prop

theorem contDiff_affineFrame (Q : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (affineFrame Q c) := by
  have h : affineFrame Q c = fun w i => ∑ j, Qᵀ i j * (w j - c j) := by
    funext w i
    simp [affineFrame, Matrix.mulVec, dotProduct]
  rw [h]
  exact contDiff_pi.2 fun i => ContDiff.sum fun j _ =>
    contDiff_const.mul ((contDiff_apply ℝ ℝ j).sub contDiff_const)

theorem contDiff_rotatedAnharmonic (Q : Matrix (Fin d) (Fin d) ℝ) (c lam alpha gamma : Fin d → ℝ)
    (n : WithTop ℕ∞) : ContDiff ℝ n (rotatedAnharmonic Q c lam alpha gamma) := by
  change ContDiff ℝ n fun w =>
    ∑ i, OneD.anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)
  exact ContDiff.sum fun i _ => (contDiff_anharmonicPotential _ _ _ n).comp
    ((contDiff_apply ℝ ℝ i).comp (contDiff_affineFrame Q c n))

/-- `c` is a critical point of `L∘A` in Mathlib's sense: `fderiv ℝ (L∘A) c = 0`. -/
theorem fderiv_rotatedAnharmonic_center (Q : Matrix (Fin d) (Fin d) ℝ)
    (c lam alpha gamma : Fin d → ℝ) :
    fderiv ℝ (rotatedAnharmonic Q c lam alpha gamma) c = 0 := by
  ext v
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin d → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul, _root_.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← partialD_eq_fderiv ((contDiff_rotatedAnharmonic Q c lam alpha gamma 1).differentiable
    one_ne_zero c) k, partialD_rotatedAnharmonic_center]
  simp

theorem iteratedFDeriv2_rotatedAnharmonic_center (Q : Matrix (Fin d) (Fin d) ℝ)
    (c lam alpha gamma : Fin d → ℝ) (j k : Fin d) :
    iteratedFDeriv ℝ 2 (rotatedAnharmonic Q c lam alpha gamma) c ![Pi.single j 1, Pi.single k 1] =
      (Q * diagonal lam * Qᵀ) j k := by
  rw [← partialD2_eq_iteratedFDeriv (contDiff_rotatedAnharmonic Q c lam alpha gamma 2),
    partialD2_rotatedAnharmonic_center]

theorem iteratedFDeriv3_rotatedAnharmonic_center (Q : Matrix (Fin d) (Fin d) ℝ)
    (c lam alpha gamma : Fin d → ℝ) (i j k : Fin d) :
    iteratedFDeriv ℝ 3 (rotatedAnharmonic Q c lam alpha gamma) c
        ![Pi.single i 1, Pi.single j 1, Pi.single k 1] = rotT Q alpha i j k := by
  rw [← partialD3_eq_iteratedFDeriv (contDiff_rotatedAnharmonic Q c lam alpha gamma 3),
    partialD3_rotatedAnharmonic_center]

theorem iteratedFDeriv4_rotatedAnharmonic_center (Q : Matrix (Fin d) (Fin d) ℝ)
    (c lam alpha gamma : Fin d → ℝ) (i j k l : Fin d) :
    iteratedFDeriv ℝ 4 (rotatedAnharmonic Q c lam alpha gamma) c
        ![Pi.single i 1, Pi.single j 1, Pi.single k 1, Pi.single l 1] = rotQ Q gamma i j k l := by
  rw [← partialD4_eq_iteratedFDeriv (contDiff_rotatedAnharmonic Q c lam alpha gamma 4),
    partialD4_rotatedAnharmonic_center]

end Laplace.Multi
