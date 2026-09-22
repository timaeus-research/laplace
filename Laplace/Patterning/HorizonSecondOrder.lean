/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.HorizonNonlinear

/-!
# The nonlinear gradient-descent recursion to second order

`HorizonNonlinear.lean` proves Proposition 3.1 of the working note *Patterning flow* to first
order: `w_T(ε) − w* + ε F_T(H) b(w*) = o(ε)`. The note claims `O(ε²)`, which needs a `C²` loss.
Here the second-order data are packaged as two local bounds at the minimiser `w*`:

* a **quadratic Taylor bound** for the gradient field, `‖G(w) − H(w − w*)‖ ≤ L ‖w − w*‖²` for
  `‖w − w*‖ ≤ r` (true for a `C²` loss with Lipschitz Hessian, or any `C³` loss);
* a **local Lipschitz bound** for the force, `‖b(w) − b(w*)‖ ≤ K ‖w − w*‖`.

With these, the error `e_k(ε) = w_k(ε) − w* − ε δ_k` against the linearised iterate `δ_k` satisfies
`e_{k+1} = (1 − ηH) e_k − η [G(w_k) − H(w_k − w*)] − ηε [b(w_k) − b(w*)]`, and both brackets are
`O(ε²)` once `w_k − w* = O(ε)`; induction on the horizon gives

  `w_T(ε) − w* + ε F_T(H) b(w*) = O(ε²)`   (`gdIter_isBigO_sq`).

This is the remainder the note's "pipeline = split Euler step of the flow" statement relies on:
the data-side step of the pipeline is exact and the parameter-side step is the linear response
up to `O(ε²)`.
-/

namespace Laplace.Patterning

open Matrix Filter Topology Asymptotics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix as a continuous linear map on `ι → ℝ`. -/
noncomputable def horizonCLM (M : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

@[simp] lemma horizonCLM_apply (M : Matrix ι ι ℝ) (v : ι → ℝ) : horizonCLM M v = M *ᵥ v := by
  simp [horizonCLM]

/-- `ε² = O(ε)` at `0`. -/
theorem isBigO_sq_id : (fun ε : ℝ => ε ^ 2) =O[𝓝 (0 : ℝ)] fun ε => ε := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with ε hε
  rw [mem_closedBall_zero_iff] at hε
  rw [norm_pow, one_mul]
  calc ‖ε‖ ^ 2 = ‖ε‖ * ‖ε‖ := by ring
    _ ≤ 1 * ‖ε‖ := by gcongr
    _ = ‖ε‖ := one_mul _

/-- **Proposition 3.1 to second order.** With a quadratic Taylor bound for the gradient field and
a local Lipschitz bound for the force at the minimiser,
`w_T(ε) − w* + ε F_T(H) b(w*) = O(ε²)` as `ε → 0`. -/
theorem gdIter_isBigO_sq {G b : (ι → ℝ) → (ι → ℝ)} {η : ℝ} {w₀ : ι → ℝ} {H : Matrix ι ι ℝ}
    {L K r : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hr : 0 < r)
    (hG : ∀ w, ‖w - w₀‖ ≤ r → ‖G w - H *ᵥ (w - w₀)‖ ≤ L * ‖w - w₀‖ ^ 2)
    (hb : ∀ w, ‖w - w₀‖ ≤ r → ‖b w - b w₀‖ ≤ K * ‖w - w₀‖) (T : ℕ) :
    (fun ε => gdIter G b η ε w₀ T - w₀ + ε • ((horizonFilter H η T) *ᵥ b w₀))
      =O[𝓝 (0 : ℝ)] fun ε => ε ^ 2 := by
  have hlinF : ∀ T, (horizonIter H η η (b w₀))^[T] 0 = -((horizonFilter H η T) *ᵥ b w₀) := by
    intro T
    have h := horizon_iterate_zero_filter H η 1 (b w₀) T
    simpa using h
  have key : ∀ T, ((fun ε => gdIter G b η ε w₀ T - w₀) =O[𝓝 (0 : ℝ)] fun ε => ε) ∧
      ((fun ε => gdIter G b η ε w₀ T - w₀ - ε • (horizonIter H η η (b w₀))^[T] 0)
        =O[𝓝 (0 : ℝ)] fun ε => ε ^ 2) := by
    intro T
    induction T with
    | zero =>
      simp only [gdIter, Function.iterate_zero, id_eq, sub_self, smul_zero, sub_zero]
      exact ⟨isBigO_zero _ _, isBigO_zero _ _⟩
    | succ T ih =>
      obtain ⟨hδ, he⟩ := ih
      obtain ⟨A, hA⟩ := hδ.bound
      have hδ0 : Tendsto (fun ε => gdIter G b η ε w₀ T - w₀) (𝓝 0) (𝓝 0) :=
        hδ.trans_tendsto tendsto_id
      have hsmall : ∀ᶠ ε in 𝓝 (0 : ℝ), ‖gdIter G b η ε w₀ T - w₀‖ ≤ r := by
        filter_upwards [hδ0.eventually (Metric.closedBall_mem_nhds (0 : ι → ℝ) hr)] with ε hε
        rwa [dist_zero_right] at hε
      have hR1 : (fun ε => G (gdIter G b η ε w₀ T) - H *ᵥ (gdIter G b η ε w₀ T - w₀))
          =O[𝓝 (0 : ℝ)] fun ε => ε ^ 2 := by
        refine IsBigO.of_bound (L * A ^ 2) ?_
        filter_upwards [hA, hsmall] with ε hAε hsε
        calc ‖G (gdIter G b η ε w₀ T) - H *ᵥ (gdIter G b η ε w₀ T - w₀)‖
            ≤ L * ‖gdIter G b η ε w₀ T - w₀‖ ^ 2 := hG _ hsε
          _ ≤ L * (A * ‖ε‖) ^ 2 := by gcongr
          _ = L * A ^ 2 * ‖ε ^ 2‖ := by rw [norm_pow]; ring
      have hR2 : (fun ε => ε • (b (gdIter G b η ε w₀ T) - b w₀)) =O[𝓝 (0 : ℝ)] fun ε => ε ^ 2 := by
        refine IsBigO.of_bound (K * A) ?_
        filter_upwards [hA, hsmall] with ε hAε hsε
        rw [norm_smul, norm_pow]
        calc ‖ε‖ * ‖b (gdIter G b η ε w₀ T) - b w₀‖
            ≤ ‖ε‖ * (K * ‖gdIter G b η ε w₀ T - w₀‖) := by gcongr; exact hb _ hsε
          _ ≤ ‖ε‖ * (K * (A * ‖ε‖)) := by gcongr
          _ = K * A * ‖ε‖ ^ 2 := by ring
      have hrec : ∀ ε, gdIter G b η ε w₀ (T + 1) - w₀ - ε • (horizonIter H η η (b w₀))^[T + 1] 0
          = (1 - η • H) *ᵥ (gdIter G b η ε w₀ T - w₀ - ε • (horizonIter H η η (b w₀))^[T] 0)
            - η • (G (gdIter G b η ε w₀ T) - H *ᵥ (gdIter G b η ε w₀ T - w₀))
            - η • (ε • (b (gdIter G b η ε w₀ T) - b w₀)) := by
        intro ε
        rw [gdIter, Function.iterate_succ_apply', Function.iterate_succ_apply', ← gdIter]
        simp only [gdStep, horizonIter, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
          Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub, smul_add, smul_smul]
        module
      have he' : (fun ε => gdIter G b η ε w₀ (T + 1) - w₀ - ε • (horizonIter H η η (b w₀))^[T + 1] 0)
          =O[𝓝 (0 : ℝ)] fun ε => ε ^ 2 := by
        have h1 := (((horizonCLM (1 - η • H)).isBigO_comp _ (𝓝 (0 : ℝ))).trans he)
        simp only [horizonCLM_apply] at h1
        refine ((h1.sub (hR1.const_smul_left η)).sub (hR2.const_smul_left η)).congr_left ?_
        intro ε
        rw [hrec ε]
        rfl
      refine ⟨?_, he'⟩
      have hlinO : (fun ε => ε • (horizonIter H η η (b w₀))^[T + 1] 0) =O[𝓝 (0 : ℝ)] fun ε => ε := by
        refine IsBigO.of_bound ‖(horizonIter H η η (b w₀))^[T + 1] 0‖
          (Filter.Eventually.of_forall fun ε => ?_)
        rw [norm_smul, mul_comm]
      refine ((he'.trans isBigO_sq_id).add hlinO).congr_left fun ε => ?_
      abel
  refine ((key T).2).congr_left fun ε => ?_
  rw [hlinF T, smul_neg, sub_neg_eq_add]

end Laplace.Patterning
