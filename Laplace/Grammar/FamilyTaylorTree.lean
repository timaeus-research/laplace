/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FamilyPhaseIntegral
import Laplace.Grammar.FamilySpectralCoeff
import Laplace.Grammar.UniformCutoffConst

/-!
# The Taylor tree for absolutely summable coefficient families (Stage 4g)

Unit 247 (Taylor-tree programme, Stage 4 assembly; Astra #28 §2.4). For phase and amplitude given
on the unit box by **absolutely summable power series** `ξ(u) = ∑_γ cξ_γ u^γ`, `η(u) = ∑_γ cη_γ u^γ`
(the hypothesis implied by the paper's holomorphy on a polydisc `D_R`, `R > 1`, via Cauchy
estimates), `β > 0`, `kᵢ > 0`:

**Headline XXVII** (`familyTaylorTree_cutoff_bound`): for every cutoff `L > 0` and every `N ≥ 1`,
```
|Z(N) − ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ d-1} A_{μ,j} (log N)^j|
  ≤ cutoffBound(ξ(0), mass η, mass ξ) · N^{-L} (1+log N)^{d-1},
```
with the cutoff-free coefficients `A_{μ,j}(cξ, cη)` of unit 245 (limits of the polynomial
coefficients, vanishing off `Λ(h,k)`) and a constant depending on the data only through `ξ(0)` and
the two masses. Proof: fix `N`, apply the polynomial theorem with the uniform constant (unit 246) to
every box truncation, and pass to the limit `m → ∞` on both sides (units 244–245). Corollaries:
`O(N^{-L}(1+log N)^{d-1})`, `O(N^{-L}(log N)^{d-1})` and `o(N^{-L'})` for `L' < L`, and the
expansion over the paper's candidate set `Λ(h,k) ∩ [0,L)`. This is `thm:TaylorTree` /
`cor:standardintegralexp` at `b = 1` under the coefficient-summability form of the analytic
hypothesis. No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Laplace.Grammar

open MonoRep CoeffFamily

/-- **Headline XXVII — the Taylor tree for coefficient-family data, quantitative form.** -/
theorem familyTaylorTree_cutoff_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    |familyPhaseIntegral n h k β N cξ cη - familySpectralSum n h k β L cξ cη N| ≤
      cutoffBound n k β L (cξ 0) (mass cη) (mass cξ) * (N ^ (-L) * (1 + Real.log N) ^ n) := by
  have hlim : Tendsto (fun m => |polyPhaseIntegral n h k β N (truncList cξ m) (truncList cη m) -
      spectralSum n h k β L (truncList cξ m) (truncList cη m) N|) atTop
      (𝓝 |familyPhaseIntegral n h k β N cξ cη - familySpectralSum n h k β L cξ cη N|) :=
    ((tendsto_polyPhaseIntegral_truncList n h k β hβ.le (by linarith) hξ hη).sub
      (tendsto_spectralSum_truncList n h k hk β hβ L hξ hη N)).abs
  refine le_of_tendsto' hlim fun m => ?_
  exact taylorTree_cutoff_bound_uniform n h k hk β hβ hL hN _ _ (eval_truncList_zero cξ m)
    (l1_truncList_le_mass hη m) ((l1_fluct_le _).trans (l1_truncList_le_mass hξ m))

/-- **Headline XXVII, `IsBigO` form.** -/
theorem familyTaylorTree_isBigO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) :
    (fun N : ℝ => familyPhaseIntegral n h k β N cξ cη - familySpectralSum n h k β L cξ cη N)
      =O[atTop] fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n := by
  refine IsBigO.of_bound (cutoffBound n k β L (cξ 0) (mass cη) (mass cξ)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (by linarith) _) (pow_nonneg (by linarith [Real.log_nonneg hN]) _))]
  exact familyTaylorTree_cutoff_bound n h k hk β hβ hL hN hξ hη

/-- The paper's form `O(N^{-L} (log N)^{d-1})`. -/
theorem familyTaylorTree_isBigO_log (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) :
    (fun N : ℝ => familyPhaseIntegral n h k β N cξ cη - familySpectralSum n h k β L cξ cη N)
      =O[atTop] fun N : ℝ => N ^ (-L) * (Real.log N) ^ n :=
  (familyTaylorTree_isBigO n h k hk β hβ hL hξ hη).trans
    ((isBigO_refl (fun N : ℝ => N ^ (-L)) atTop).mul (one_add_log_pow_isBigO n))

/-- `N^{-L}(1+log N)^n = o(N^{-L'})` for `L' < L`. -/
theorem rpow_neg_mul_log_pow_isLittleO (n : ℕ) {L L' : ℝ} (hL' : L' < L) :
    (fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n) =o[atTop] fun N : ℝ => N ^ (-L') := by
  have hs : 0 < L - L' := by linarith
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

/-- **Asymptotic expansion**: the remainder below the cutoff `L` is `o(N^{-L'})` for every
`L' < L`. -/
theorem familyTaylorTree_isLittleO (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L L' : ℝ} (hL : 0 < L) (hL' : L' < L) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    (fun N : ℝ => familyPhaseIntegral n h k β N cξ cη - familySpectralSum n h k β L cξ cη N)
      =o[atTop] fun N : ℝ => N ^ (-L') :=
  (familyTaylorTree_isBigO n h k hk β hβ hL hξ hη).trans_isLittleO
    (rpow_neg_mul_log_pow_isLittleO n hL')

open Classical in
/-- The family spectral sum restricted to the paper's candidate set `Λ(h,k) ∩ [0,L)`. -/
theorem familySpectralSum_eq_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (L : ℝ) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    (N : ℝ) :
    familySpectralSum n h k β L cξ cη N =
      ∑ μ ∈ (latticeBelow (latticeQ k) L).filter (candidateExp h k), N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), familySpectralCoeff n h k β cξ cη μ j * (Real.log N) ^ j := by
  unfold familySpectralSum
  symm
  refine Finset.sum_filter_of_ne fun μ _ hne => ?_
  by_contra hμ
  refine hne ?_
  rw [Finset.sum_eq_zero fun j _ => by
    rw [familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ hξ hη hμ j, zero_mul], mul_zero]

open Classical in
/-- **Headline XXVII over the paper's candidate set.** -/
theorem familyTaylorTree_isBigO_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) :
    (fun N : ℝ => familyPhaseIntegral n h k β N cξ cη -
      ∑ μ ∈ (latticeBelow (latticeQ k) L).filter (candidateExp h k), N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), familySpectralCoeff n h k β cξ cη μ j * (Real.log N) ^ j)
      =O[atTop] fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n := by
  refine (familyTaylorTree_isBigO n h k hk β hβ hL hξ hη).congr_left fun N => ?_
  rw [familySpectralSum_eq_candidate n h k hk β hβ L hξ hη]

end Laplace.Grammar
