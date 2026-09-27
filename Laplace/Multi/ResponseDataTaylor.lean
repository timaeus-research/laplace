/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDataSmooth
import Mathlib.Analysis.Calculus.Taylor

/-!
# The second-order Taylor expansion of the response map

Along a data journey `g + t k` the response expands as

  `Φ(g + t k) = Φ(g) + t DΦ_g[k] + (t²/2) H_g(k,k) + o(t²)`   (`responseOf_add_taylor_two`),

with `DΦ_g[k]` the response velocity and `H_g(k,k)` the response Hessian. The journey is a
one-dimensional data slice, hence `C^∞` (`contDiff_responseOf_add`), and Mathlib's Taylor theorem
with Peano remainder identifies the first two derivatives with the velocity and the Hessian
(`deriv_responseOf_add`, `deriv_deriv_responseOf_add_zero`). This is the user-facing form of the
second-order response calculus: the two-jet of the response map at a data law is the pair
(inverse-covariance transport of the forcing, cumulant-corrected Hessian).
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ContDiff

namespace Laplace.Multi

section Taylor

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k)
include hS hg hk

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk in
/-- The straight journey is the one-dimensional slice. -/
theorem sliceFun_unit (t : ℝ) :
    sliceFun g (fun _ : Unit ↦ k) (fun _ ↦ t) = fun x ↦ g x + t * k x := by
  funext x
  simp [sliceFun]

/-- **The response along a data journey is `C^∞`.** -/
theorem contDiff_responseOf_add :
    ContDiff ℝ ∞ (fun t : ℝ ↦ responseOf hS ν (fun x ↦ g x + t * k x)) := by
  have h := (contDiff_responseOf_slice hS ν hg (fun _ : Unit ↦ hk)).comp
    (contDiff_pi.2 fun _ : Unit ↦ contDiff_id (E := ℝ))
  have e : (fun t : ℝ ↦ responseOf hS ν (fun x ↦ g x + t * k x)) =
      (fun z : Unit → ℝ ↦ responseOf hS ν (sliceFun g (fun _ ↦ k) z)) ∘ (fun t ↦ fun _ ↦ t) :=
    funext fun t ↦ by
      simp only [Function.comp_def]
      rw [sliceFun_unit]
  rw [e]
  exact h

theorem deriv_responseOf_add :
    deriv (fun t : ℝ ↦ responseOf hS ν (fun x ↦ g x + t * k x)) =
      fun t ↦ responseVel hS ν (hg.add (Bdd.const_mul t hk)) hk :=
  funext fun t ↦ (hasDerivAt_responseOf_add hS ν hg hk t).deriv

theorem deriv_deriv_responseOf_add_zero :
    deriv (deriv (fun t : ℝ ↦ responseOf hS ν (fun x ↦ g x + t * k x))) 0 =
      responseHess hS ν hg hk hk := by
  rw [deriv_responseOf_add hS ν hg hk, (hasDerivAt_responseVel_add_self hS ν hg hk 0).deriv]
  exact responseHess_congr hS ν _ hg hk hk (by funext x; simp)

/-- **The second-order Taylor expansion of the response map**:
`Φ(g + t k) = Φ(g) + t DΦ_g[k] + (t²/2) H_g(k,k) + o(t²)`. -/
theorem responseOf_add_taylor_two :
    (fun t : ℝ ↦ responseOf hS ν (fun x ↦ g x + t * k x) - responseOf hS ν g -
        t • responseVel hS ν hg hk - (t ^ 2 / 2) • responseHess hS ν hg hk hk)
      =o[𝓝 (0 : ℝ)] fun t ↦ t ^ 2 := by
  have h2 : ContDiff ℝ 2 (fun t : ℝ ↦ responseOf hS ν (fun x ↦ g x + t * k x)) :=
    (contDiff_responseOf_add hS ν hg hk).of_le (by exact_mod_cast natCast_le_infty 2)
  have h := taylor_isLittleO_univ (x₀ := 0) h2
  simp only [sub_zero] at h
  refine h.congr_left fun t ↦ ?_
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval,
    iteratedDerivWithin_univ, iteratedDerivWithin_univ, iteratedDeriv_one, iteratedDeriv_succ,
    iteratedDeriv_one,
    deriv_deriv_responseOf_add_zero hS ν hg hk, deriv_responseOf_add hS ν hg hk]
  have e0 : responseVel hS ν (hg.add (Bdd.const_mul 0 hk)) hk = responseVel hS ν hg hk :=
    responseVel_congr hS ν _ _ hg hk (by funext x; simp) rfl
  have e1 : responseOf hS ν (fun x ↦ g x + 0 * k x) = responseOf hS ν g := by
    congr 1
    funext x
    simp
  beta_reduce
  rw [e0, e1]
  simp only [Nat.factorial, Nat.cast_one, sub_zero]
  norm_num [sub_sub]
  module

end Taylor

end Laplace.Multi
