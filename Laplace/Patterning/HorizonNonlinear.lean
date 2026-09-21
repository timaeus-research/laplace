/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.Horizon

/-!
# The nonlinear gradient-descent recursion is tangent to the linearised one

The first-order content of Proposition 3.1 of the working note *Patterning flow* that
`Horizon.lean` leaves out. Gradient descent on the reweighted loss is the recursion
`w_{k+1} = w_k - η (G(w_k) + ε b(w_k))`, `w_0 = w*`, with `G = ∇L_n` (so `G(w*) = 0`) and
`b = Bω` the gradient-response force. We show that the map `ε ↦ w_T(ε)` is differentiable at
`ε = 0` with derivative the `T`-th iterate of the linearised recursion of `Horizon.lean`, hence

  `w_T(ε) - w* = -ε F_T(H) b(w*) + o(ε)`   (`gdIter_isLittleO`).

The hypotheses are that `G` is differentiable at `w*` with derivative `H` and that `b` is
differentiable at `w*`. The note's `O(ε²)` would need a second derivative in `ε` (a `C²` loss)
and is not claimed here; the `o(ε)` statement is the exact content of "to first order".
-/

namespace Laplace.Patterning

open Matrix Filter Topology Asymptotics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One gradient-descent step on the reweighted loss: `w ↦ w - η (G w + ε b w)`. -/
def gdStep (G b : (ι → ℝ) → (ι → ℝ)) (η ε : ℝ) (w : ι → ℝ) : ι → ℝ :=
  w - η • (G w + ε • b w)

/-- `T` gradient-descent steps from `w₀`. -/
def gdIter (G b : (ι → ℝ) → (ι → ℝ)) (η ε : ℝ) (w₀ : ι → ℝ) (T : ℕ) : ι → ℝ :=
  (gdStep G b η ε)^[T] w₀

/-- At `ε = 0` the minimiser is fixed: `w_T(0) = w*`. -/
theorem gdIter_zero {G b : (ι → ℝ) → (ι → ℝ)} {η : ℝ} {w₀ : ι → ℝ} (hG0 : G w₀ = 0) (T : ℕ) :
    gdIter G b η 0 w₀ T = w₀ := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [gdIter, Function.iterate_succ_apply', ← gdIter, ih, gdStep, hG0]
    simp

/-- **The ε-derivative of the nonlinear iterate satisfies the linearised recursion.**
`d/dε w_T(ε)|₀ = (horizonIter H η η b(w*))^[T] 0`, i.e. `δ_{k+1} = (1 - ηH) δ_k - η b(w*)`. -/
theorem hasDerivAt_gdIter {G b : (ι → ℝ) → (ι → ℝ)} {η : ℝ} {w₀ : ι → ℝ}
    {H' : (ι → ℝ) →L[ℝ] (ι → ℝ)} {H : Matrix ι ι ℝ}
    (hG0 : G w₀ = 0) (hG : HasFDerivAt G H' w₀) (hH' : ∀ v, H' v = H *ᵥ v)
    (hb : DifferentiableAt ℝ b w₀) (T : ℕ) :
    HasDerivAt (fun ε => gdIter G b η ε w₀ T) ((horizonIter H η η (b w₀))^[T] 0) 0 := by
  induction T with
  | zero =>
    simp only [gdIter, Function.iterate_zero, id_eq]
    exact hasDerivAt_const 0 w₀
  | succ T ih =>
    have hG' : HasFDerivAt G H' (gdIter G b η 0 w₀ T) := by
      rw [gdIter_zero hG0 T]
      exact hG
    have hb' : DifferentiableAt ℝ b (gdIter G b η 0 w₀ T) := by
      rw [gdIter_zero hG0 T]
      exact hb
    have hGc := hG'.comp_hasDerivAt (0 : ℝ) ih
    have hbc := hb'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ih
    have hsm := (hasDerivAt_id (0 : ℝ)).smul hbc
    have h := ih.sub ((hGc.add hsm).const_smul η)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => ?_)).congr_deriv ?_
    · simp only [gdIter, Function.iterate_succ_apply', gdStep, Function.comp_apply, id_eq]
      rfl
    · rw [Function.iterate_succ_apply']
      simp only [id_eq, zero_smul, one_smul, zero_add, Function.comp_apply, gdIter_zero hG0, hH',
        horizonIter, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, smul_add]
      abel

/-- **Tangency to the horizon filter.** `d/dε w_T(ε)|₀ = -F_T(H) b(w*)`. -/
theorem hasDerivAt_gdIter_filter {G b : (ι → ℝ) → (ι → ℝ)} {η : ℝ} {w₀ : ι → ℝ}
    {H' : (ι → ℝ) →L[ℝ] (ι → ℝ)} {H : Matrix ι ι ℝ}
    (hG0 : G w₀ = 0) (hG : HasFDerivAt G H' w₀) (hH' : ∀ v, H' v = H *ᵥ v)
    (hb : DifferentiableAt ℝ b w₀) (T : ℕ) :
    HasDerivAt (fun ε => gdIter G b η ε w₀ T) (-((horizonFilter H η T) *ᵥ b w₀)) 0 := by
  refine (hasDerivAt_gdIter hG0 hG hH' hb T).congr_deriv ?_
  have h := horizon_iterate_zero_filter H η 1 (b w₀) T
  simpa using h

/-- **Proposition 3.1 to first order.** `w_T(ε) - w* + ε F_T(H) b(w*) = o(ε)` as `ε → 0`. -/
theorem gdIter_isLittleO {G b : (ι → ℝ) → (ι → ℝ)} {η : ℝ} {w₀ : ι → ℝ}
    {H' : (ι → ℝ) →L[ℝ] (ι → ℝ)} {H : Matrix ι ι ℝ}
    (hG0 : G w₀ = 0) (hG : HasFDerivAt G H' w₀) (hH' : ∀ v, H' v = H *ᵥ v)
    (hb : DifferentiableAt ℝ b w₀) (T : ℕ) :
    (fun ε => gdIter G b η ε w₀ T - w₀ + ε • ((horizonFilter H η T) *ᵥ b w₀))
      =o[𝓝 0] fun ε : ℝ => ε := by
  have h := hasDerivAt_gdIter_filter (η := η) hG0 hG hH' hb T
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h
  refine h.congr' (Filter.Eventually.of_forall fun ε => ?_) Filter.EventuallyEq.rfl
  simp only [zero_add, gdIter_zero hG0, smul_neg, sub_neg_eq_add]

end Laplace.Patterning
