/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RotatedTaylor

/-!
# The rotated tensors are the coordinate derivatives of the rotated oscillator

`RotatedTaylor` certifies `H = Q diag(λ) Qᵀ`, `rotT`, `rotQ` as Taylor coefficients. Here they are
identified with derivatives in Lean's sense: with `∂ᵢ f (w) = d/ds f(w + s eᵢ)|₀` (`partialD`),

* `partialD_rotatedAnharmonic_center`: `∂ₖ(L∘A)(c) = 0`;
* `partialD2_rotatedAnharmonic_center`: `∂ⱼ∂ₖ(L∘A)(c) = (Q diag(λ) Qᵀ)ⱼₖ`;
* `partialD3_rotatedAnharmonic_center`: `∂ᵢ∂ⱼ∂ₖ(L∘A)(c) = rotT Q α i j k`;
* `partialD4_rotatedAnharmonic_center`: `∂ᵢ∂ⱼ∂ₖ∂ₘ(L∘A)(c) = rotQ Q γ i j k m`.

The route is the one-variable chain rule along a coordinate line (`hasDerivAt_sum_affine`,
`partialD_sum_affineFrame`) applied to the explicit derivative tower of the anharmonic polynomial
(`anhD1`, `anhD2`, `anhD3`, `anhD4`); every partial derivative is computed for all `w` first
(`partialD_rotatedAnharmonic`, `partialD2_…`, `partialD3_…`, `partialD4_…`) and evaluated at `c`
where the eigen-coordinates vanish.
-/

open Matrix

namespace Laplace.Multi

variable {d : ℕ}

/-- The partial derivative along the `i`-th coordinate line:
`∂ᵢ f (w) = d/ds f(w + s eᵢ)|_{s = 0}`. -/
noncomputable def partialD (i : Fin d) (f : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) : ℝ :=
  deriv (fun s : ℝ => f (w + s • Pi.single i 1)) 0

/-! ### The derivative tower of the anharmonic polynomial -/

/-- `ℓ'(x) = λx + αx²/2 + γx³/6`. -/
noncomputable def anhD1 (lam alpha gamma : ℝ) (x : ℝ) : ℝ :=
  lam * x + alpha / 2 * x ^ 2 + gamma / 6 * x ^ 3

/-- `ℓ''(x) = λ + αx + γx²/2`. -/
noncomputable def anhD2 (lam alpha gamma : ℝ) (x : ℝ) : ℝ := lam + alpha * x + gamma / 2 * x ^ 2

/-- `ℓ'''(x) = α + γx`. -/
noncomputable def anhD3 (_lam alpha gamma : ℝ) (x : ℝ) : ℝ := alpha + gamma * x

/-- `ℓ''''(x) = γ`. -/
noncomputable def anhD4 (_lam _alpha gamma : ℝ) (_x : ℝ) : ℝ := gamma

theorem hasDerivAt_anharmonic (lam alpha gamma x : ℝ) :
    HasDerivAt (OneD.anharmonicPotential lam alpha gamma) (anhD1 lam alpha gamma x) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul (lam / 2)).add
    ((hasDerivAt_pow 3 x).const_mul (alpha / 6))).add ((hasDerivAt_pow 4 x).const_mul (gamma / 24))
  have e : anhD1 lam alpha gamma x = lam / 2 * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) +
      alpha / 6 * (((3 : ℕ) : ℝ) * x ^ (3 - 1)) + gamma / 24 * (((4 : ℕ) : ℝ) * x ^ (4 - 1)) := by
    simp only [anhD1]
    norm_num
    ring
  rw [e]
  exact h

theorem hasDerivAt_anhD1 (lam alpha gamma x : ℝ) :
    HasDerivAt (anhD1 lam alpha gamma) (anhD2 lam alpha gamma x) x := by
  have h := (((hasDerivAt_id' (x := x)).const_mul lam).add
    ((hasDerivAt_pow 2 x).const_mul (alpha / 2))).add ((hasDerivAt_pow 3 x).const_mul (gamma / 6))
  have e : anhD2 lam alpha gamma x = lam * 1 + alpha / 2 * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) +
      gamma / 6 * (((3 : ℕ) : ℝ) * x ^ (3 - 1)) := by
    simp only [anhD2]
    norm_num
    ring
  rw [e]
  exact h

theorem hasDerivAt_anhD2 (lam alpha gamma x : ℝ) :
    HasDerivAt (anhD2 lam alpha gamma) (anhD3 lam alpha gamma x) x := by
  have h := ((hasDerivAt_const x lam).add ((hasDerivAt_id' (x := x)).const_mul alpha)).add
    ((hasDerivAt_pow 2 x).const_mul (gamma / 2))
  have e : anhD3 lam alpha gamma x = 0 + alpha * 1 + gamma / 2 * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) := by
    simp only [anhD3]
    norm_num
    ring
  rw [e]
  exact h

theorem hasDerivAt_anhD3 (lam alpha gamma x : ℝ) :
    HasDerivAt (anhD3 lam alpha gamma) (anhD4 lam alpha gamma x) x := by
  have h := (hasDerivAt_const x alpha).add ((hasDerivAt_id' (x := x)).const_mul gamma)
  have e : anhD4 lam alpha gamma x = 0 + gamma * 1 := by
    simp only [anhD4]
    ring
  rw [e]
  exact h

@[simp] theorem anhD1_zero (lam alpha gamma : ℝ) : anhD1 lam alpha gamma 0 = 0 := by
  simp [anhD1]

@[simp] theorem anhD2_zero (lam alpha gamma : ℝ) : anhD2 lam alpha gamma 0 = lam := by
  simp [anhD2]

@[simp] theorem anhD3_zero (lam alpha gamma : ℝ) : anhD3 lam alpha gamma 0 = alpha := by
  simp [anhD3]

/-! ### The chain rule along a coordinate line -/

/-- `d/ds ∑ₗ gₗ(aₗ + s bₗ)|₀ = ∑ₗ gₗ'(aₗ) bₗ`. -/
theorem hasDerivAt_sum_affine {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ) (gp a b : ι → ℝ)
    (hg : ∀ l, HasDerivAt (g l) (gp l) (a l)) :
    HasDerivAt (fun s : ℝ => ∑ l, g l (a l + s * b l)) (∑ l, gp l * b l) 0 := by
  have h : ∀ l ∈ (Finset.univ : Finset ι),
      HasDerivAt (fun s : ℝ => g l (a l + s * b l)) (gp l * b l) 0 := by
    intro l _
    have hlin : HasDerivAt (fun s : ℝ => a l + s * b l) (b l) 0 := by
      have h1 := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (b l)).const_add (a l)
      simpa using h1
    have hg' : HasDerivAt (g l) (gp l) (a l + 0 * b l) := by
      rw [zero_mul, add_zero]
      exact hg l
    exact hg'.comp (0 : ℝ) hlin
  refine (HasDerivAt.sum h).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s => by simp [Finset.sum_apply]

/-- The eigen-coordinates along a coordinate line: `(A(w + s eₖ))ₗ = (A w)ₗ + s Qₖₗ`. -/
theorem affineFrame_line (Q : Matrix (Fin d) (Fin d) ℝ) (c w : Fin d → ℝ) (k : Fin d) (s : ℝ) :
    affineFrame Q c (w + s • Pi.single k 1) = fun l => affineFrame Q c w l + s * Q k l := by
  funext l
  simp only [affineFrame]
  rw [add_sub_right_comm, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- **One coordinate derivative of a weighted separable function of the eigen-coordinates**:
`∂ₖ (∑ₗ Aₗ gₗ(uₗ(w))) = ∑ₗ Aₗ gₗ'(uₗ(w)) Qₖₗ`, `u = A(w)`. -/
theorem partialD_sum_affineFrame (Q : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) (A : Fin d → ℝ)
    (g gp : Fin d → ℝ → ℝ) (hg : ∀ l x, HasDerivAt (g l) (gp l x) x) (k : Fin d) (w : Fin d → ℝ) :
    partialD k (fun w => ∑ l, A l * g l (affineFrame Q c w l)) w =
      ∑ l, A l * gp l (affineFrame Q c w l) * Q k l := by
  unfold partialD
  have hf : (fun s : ℝ => ∑ l, A l * g l (affineFrame Q c (w + s • Pi.single k 1) l)) =
      fun s => ∑ l, A l * g l (affineFrame Q c w l + s * Q k l) := by
    funext s
    simp only [affineFrame_line]
  rw [hf]
  have hg' : ∀ l, HasDerivAt (fun x => A l * g l x) (A l * gp l (affineFrame Q c w l))
      (affineFrame Q c w l) := fun l => (hg l _).const_mul (A l)
  exact (hasDerivAt_sum_affine (fun l x => A l * g l x)
    (fun l => A l * gp l (affineFrame Q c w l)) (fun l => affineFrame Q c w l) (fun l => Q k l)
    hg').deriv

/-! ### The four coordinate derivatives of the rotated oscillator -/

theorem partialD_rotatedAnharmonic (Q : Matrix (Fin d) (Fin d) ℝ) (c lam alpha gamma : Fin d → ℝ)
    (k : Fin d) (w : Fin d → ℝ) :
    partialD k (rotatedAnharmonic Q c lam alpha gamma) w =
      ∑ l, anhD1 (lam l) (alpha l) (gamma l) (affineFrame Q c w l) * Q k l := by
  have e : rotatedAnharmonic Q c lam alpha gamma = fun w => ∑ l, (1 : ℝ) *
      OneD.anharmonicPotential (lam l) (alpha l) (gamma l) (affineFrame Q c w l) := by
    funext w
    simp [rotatedAnharmonic, rotated, separableAnharmonic, separablePotential]
  rw [e, partialD_sum_affineFrame Q c (fun _ => (1 : ℝ)) _
    (fun l => anhD1 (lam l) (alpha l) (gamma l))
    (fun l x => hasDerivAt_anharmonic (lam l) (alpha l) (gamma l) x) k w]
  simp only [one_mul]

theorem partialD2_rotatedAnharmonic (Q : Matrix (Fin d) (Fin d) ℝ) (c lam alpha gamma : Fin d → ℝ)
    (j k : Fin d) (w : Fin d → ℝ) :
    partialD j (partialD k (rotatedAnharmonic Q c lam alpha gamma)) w =
      ∑ l, anhD2 (lam l) (alpha l) (gamma l) (affineFrame Q c w l) * Q j l * Q k l := by
  have e : partialD k (rotatedAnharmonic Q c lam alpha gamma) =
      fun w => ∑ l, Q k l * anhD1 (lam l) (alpha l) (gamma l) (affineFrame Q c w l) := by
    funext w
    rw [partialD_rotatedAnharmonic]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e, partialD_sum_affineFrame Q c (fun l => Q k l) _
    (fun l => anhD2 (lam l) (alpha l) (gamma l))
    (fun l x => hasDerivAt_anhD1 (lam l) (alpha l) (gamma l) x) j w]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem partialD3_rotatedAnharmonic (Q : Matrix (Fin d) (Fin d) ℝ) (c lam alpha gamma : Fin d → ℝ)
    (i j k : Fin d) (w : Fin d → ℝ) :
    partialD i (partialD j (partialD k (rotatedAnharmonic Q c lam alpha gamma))) w =
      ∑ l, anhD3 (lam l) (alpha l) (gamma l) (affineFrame Q c w l) * Q i l * Q j l * Q k l := by
  have e : partialD j (partialD k (rotatedAnharmonic Q c lam alpha gamma)) =
      fun w => ∑ l, (Q j l * Q k l) * anhD2 (lam l) (alpha l) (gamma l) (affineFrame Q c w l) := by
    funext w
    rw [partialD2_rotatedAnharmonic]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e, partialD_sum_affineFrame Q c (fun l => Q j l * Q k l) _
    (fun l => anhD3 (lam l) (alpha l) (gamma l))
    (fun l x => hasDerivAt_anhD2 (lam l) (alpha l) (gamma l) x) i w]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem partialD4_rotatedAnharmonic (Q : Matrix (Fin d) (Fin d) ℝ) (c lam alpha gamma : Fin d → ℝ)
    (i j k m : Fin d) (w : Fin d → ℝ) :
    partialD i (partialD j (partialD k (partialD m (rotatedAnharmonic Q c lam alpha gamma)))) w =
      ∑ l, gamma l * Q i l * Q j l * Q k l * Q m l := by
  have e : partialD j (partialD k (partialD m (rotatedAnharmonic Q c lam alpha gamma))) =
      fun w => ∑ l, (Q j l * Q k l * Q m l) *
        anhD3 (lam l) (alpha l) (gamma l) (affineFrame Q c w l) := by
    funext w
    rw [partialD3_rotatedAnharmonic]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e, partialD_sum_affineFrame Q c (fun l => Q j l * Q k l * Q m l) _
    (fun l => anhD4 (lam l) (alpha l) (gamma l))
    (fun l x => hasDerivAt_anhD3 (lam l) (alpha l) (gamma l) x) i w]
  exact Finset.sum_congr rfl fun l _ => by simp only [anhD4]; ring

/-! ### At the centre -/

theorem affineFrame_center (Q : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) :
    affineFrame Q c c = 0 := by
  simp [affineFrame]

/-- `∇(L∘A)(c) = 0`. -/
theorem partialD_rotatedAnharmonic_center (Q : Matrix (Fin d) (Fin d) ℝ)
    (c lam alpha gamma : Fin d → ℝ) (k : Fin d) :
    partialD k (rotatedAnharmonic Q c lam alpha gamma) c = 0 := by
  rw [partialD_rotatedAnharmonic, affineFrame_center]
  simp

/-- **The Hessian at the centre is `Q diag(λ) Qᵀ`.** -/
theorem partialD2_rotatedAnharmonic_center (Q : Matrix (Fin d) (Fin d) ℝ)
    (c lam alpha gamma : Fin d → ℝ) (j k : Fin d) :
    partialD j (partialD k (rotatedAnharmonic Q c lam alpha gamma)) c =
      (Q * diagonal lam * Qᵀ) j k := by
  rw [partialD2_rotatedAnharmonic, affineFrame_center, conj_diagonal_apply]
  simp

/-- **The third derivative tensor at the centre is `rotT`.** -/
theorem partialD3_rotatedAnharmonic_center (Q : Matrix (Fin d) (Fin d) ℝ)
    (c lam alpha gamma : Fin d → ℝ) (i j k : Fin d) :
    partialD i (partialD j (partialD k (rotatedAnharmonic Q c lam alpha gamma))) c =
      rotT Q alpha i j k := by
  rw [partialD3_rotatedAnharmonic, affineFrame_center]
  simp [rotT]

/-- **The fourth derivative tensor is `rotQ`** (everywhere, the potential being quartic). -/
theorem partialD4_rotatedAnharmonic_center (Q : Matrix (Fin d) (Fin d) ℝ)
    (c lam alpha gamma : Fin d → ℝ) (i j k m : Fin d) :
    partialD i (partialD j (partialD k (partialD m (rotatedAnharmonic Q c lam alpha gamma)))) c =
      rotQ Q gamma i j k m := by
  rw [partialD4_rotatedAnharmonic]
  rfl

end Laplace.Multi
