/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LowSpectrumTail

/-!
# The polynomial Taylor tree as an asymptotic expansion (Stage 3i)

Unit 239 (Taylor-tree programme; Astra #27). The quantitative cutoff bound of unit 238 is packaged
in the asymptotic notation of `thm:TaylorTree` / `cor:standardintegralexp` for **polynomial**
phase `ξ` and amplitude `η` on the unit box:

* **Headline XXVI** (`taylorTree_isBigO`): for every cutoff `L > 0`,
  `Z(N) - ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} A_{μ,j} (log N)^j = O(N^{-L} (1+log N)^n)` as `N → ∞`;
* the paper's form with `(log N)^{d-1}` (`taylorTree_isBigO_log`);
* the **asymptotic-expansion** statement (`taylorTree_isLittleO`): for `L' < L` the same
  difference is `o(N^{-L'})`, so `∑_μ N^{-μ} P_μ(log N)` is an asymptotic expansion of `Z` in the
  scale `N^{-μ}(log N)^j`, `μ ∈ (2∏kᵢ)⁻¹ℕ`, `j ≤ d-1`.

Here `Λ_L = latticeBelow (2∏kᵢ) L` is the lattice `Q⁻¹ℕ` below the cutoff (coarser than the paper's
`Λ(h,k)`: the coefficients `A_{μ,j}` vanish at exponents not carried by any state density), and
the `A_{μ,j}` (`spectralCoeff`) are the cutoff-free absolutely convergent series of unit 237, with
`n + 1 = d`. Scope: `b = 1`, `β > 0`, positive `k`, polynomial `ξ, η`. No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Laplace.Grammar

open MonoRep

/-- The spectral sum below the cutoff `L`: `∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} A_{μ,j} (log N)^j`. -/
noncomputable def spectralSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β L : ℝ) (ξ η : MonoRep (n + 1))
    (N : ℝ) : ℝ :=
  ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
    ∑ j ∈ Finset.range (n + 1), spectralCoeff n h k β ξ η μ j * (Real.log N) ^ j

/-- **Headline XXVI — the polynomial Taylor tree, `IsBigO` form.** -/
theorem taylorTree_isBigO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) (ξ η : MonoRep (n + 1)) :
    (fun N : ℝ => polyPhaseIntegral n h k β N ξ η - spectralSum n h k β L ξ η N) =O[atTop]
      fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n := by
  refine IsBigO.of_bound (taylorCutoffConst n k β L ξ η) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (by linarith) _) (pow_nonneg (by linarith [Real.log_nonneg hN]) _))]
  exact taylorTree_cutoff_bound n h k hk β hβ hL hN ξ η

/-- `(1 + log N)^n ≤ 2^n (log N)^n` for `N ≥ e`, so the `(1+log N)^n` scale is `O((log N)^n)`. -/
theorem one_add_log_pow_isBigO (n : ℕ) :
    (fun N : ℝ => (1 + Real.log N) ^ n) =O[atTop] fun N : ℝ => (Real.log N) ^ n := by
  refine IsBigO.of_bound (2 ^ n) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have h1 : 1 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) hN
    rwa [Real.log_exp] at this
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith) _),
    abs_of_nonneg (pow_nonneg (by linarith) _), ← mul_pow]
  exact pow_le_pow_left₀ (by linarith) (by linarith) n

/-- **The paper's form**: the remainder is `O(N^{-L} (log N)^{d-1})`. -/
theorem taylorTree_isBigO_log (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) (ξ η : MonoRep (n + 1)) :
    (fun N : ℝ => polyPhaseIntegral n h k β N ξ η - spectralSum n h k β L ξ η N) =O[atTop]
      fun N : ℝ => N ^ (-L) * (Real.log N) ^ n :=
  (taylorTree_isBigO n h k hk β hβ hL ξ η).trans
    ((isBigO_refl (fun N : ℝ => N ^ (-L)) atTop).mul (one_add_log_pow_isBigO n))

/-- `(1 + log N)^n = o(N^s)` for every `s > 0`. -/
theorem one_add_log_pow_isLittleO (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (fun N : ℝ => (1 + Real.log N) ^ n) =o[atTop] fun N : ℝ => N ^ s := by
  refine (one_add_log_pow_isBigO n).trans_isLittleO ?_
  have := isLittleO_log_rpow_rpow_atTop (n : ℝ) hs
  refine this.congr' ?_ (Eventually.of_forall fun _ => rfl)
  exact Eventually.of_forall fun N => by simp [Real.rpow_natCast]

/-- **Asymptotic expansion**: for `L' < L` the remainder is `o(N^{-L'})`. Since `L` is arbitrary,
`∑_μ N^{-μ} P_μ(log N)` is an asymptotic expansion of `Z(N)` in the scale `N^{-μ} (log N)^j`. -/
theorem taylorTree_isLittleO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L L' : ℝ} (hL : 0 < L) (hL' : L' < L) (ξ η : MonoRep (n + 1)) :
    (fun N : ℝ => polyPhaseIntegral n h k β N ξ η - spectralSum n h k β L ξ η N) =o[atTop]
      fun N : ℝ => N ^ (-L') := by
  refine (taylorTree_isBigO n h k hk β hβ hL ξ η).trans_isLittleO ?_
  have hs : 0 < L - L' := by linarith
  -- `N^{-L}(1+log N)^n = N^{-L'} · ((1+log N)^n · N^{-(L-L')})`, and the bracket is `o(1)`
  have h1 : (fun N : ℝ => (1 + Real.log N) ^ n * N ^ (-(L - L'))) =o[atTop]
      fun N : ℝ => N ^ (L - L') * N ^ (-(L - L')) :=
    (one_add_log_pow_isLittleO n hs).mul_isBigO (isBigO_refl _ _)
  have h2 := (isBigO_refl (fun N : ℝ => N ^ (-L')) atTop).mul_isLittleO h1
  refine h2.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    have : N ^ (-L') * N ^ (-(L - L')) = N ^ (-L) := by
      rw [← Real.rpow_add hN]; congr 1; ring
    calc N ^ (-L') * ((1 + Real.log N) ^ n * N ^ (-(L - L')))
        = (N ^ (-L') * N ^ (-(L - L'))) * (1 + Real.log N) ^ n := by ring
      _ = _ := by rw [this]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    rw [← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring

end Laplace.Grammar
