/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ProjectiveClosure

/-!
# Local total variation: from smooth tests to bounded tests

`ProjectiveClosure` ends with exact agreement of two Laplace families
beyond all orders, `∫ φ e^{-tL₂} - ∫ φ e^{-tL₁} = o(t^{-∞})`, for every
observable `φ` in the tested class `C_c^∞`. This file upgrades the
observable class. Writing `a = e^{-tL₁}`, `b = e^{-tL₂}`, `D = L₂ - L₁`,
the pointwise inequalities

* `D (a - b) ≥ 0` and `|a - b| ≤ t |D|`, hence `|a - b|² ≤ t D (a - b)`,

turn the smooth observable `η² D` into control of the local total
variation: `E(t) = ∫ η² D (a - b) = I₁(η² D) - I₂(η² D)` is beyond all
orders and nonnegative, and for every `N` the pointwise bound
`|a - b| ≤ t^{-N}/2 + t^{N+1} D (a - b)/2` gives
`∫ η² |a - b| ≤ (∫ η²) t^{-N}/2 + t^{N+1} E(t)/2 = O(t^{-N})`.
So `∫ η² |e^{-tL₂} - e^{-tL₁}| = o(t^{-∞})` for every smooth compactly
supported `η` (`superPoly_integral_sq_mul_abs_exp_sub`), the total
variation over any compact set is beyond all orders
(`superPoly_setIntegral_abs_exp_sub`), and every bounded measurable
compactly supported observable, in particular every continuous
compactly supported one, sees the two families agree beyond all orders
(`superPoly_difference_of_bounded`, `superPoly_difference_of_continuous`).
The corollaries wire this into the closure package: projective agreement
on `C_c^∞` together with local agreement at one `C²` zero gives exact
agreement on bounded tests (`superPoly_difference_of_projective_bounded`),
and normalized expectations of bounded tests agree beyond all orders once
the partition values carry the anchor
(`superPoly_normalized_difference_of_bounded`).

Smoothness of both losses is what puts `η² D` in the tested class; the
argument needs nothing else. No square roots and no Hölder inequality
appear: the AM–GM step with the free parameter `t^{-N}` does the work of
Cauchy–Schwarz at the level of "beyond all orders".
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-! ### Pointwise inequalities for the Boltzmann weights -/

/-- `exp` is `1`-Lipschitz on the nonpositive half-line:
`|e^{-x} - e^{-y}| ≤ |x - y|` for `x, y ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have key : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v →
      Real.exp (-u) - Real.exp (-v) ≤ v - u := by
    intro u v hu huv
    have h1 : Real.exp (-u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have h2 : 1 - (v - u) ≤ Real.exp (-(v - u)) := by
      have := Real.add_one_le_exp (-(v - u))
      linarith
    have h3 : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h3]
    have h4 : Real.exp (-u) * (1 - (v - u)) ≤ Real.exp (-u) * Real.exp (-(v - u)) :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    nlinarith [Real.exp_pos (-u)]
  rcases le_total x y with hxy | hxy
  · have h := key hx hxy
    have hnn : 0 ≤ Real.exp (-x) - Real.exp (-y) := by
      have : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
      linarith
    rw [abs_of_nonneg hnn, abs_of_nonpos (by linarith)]
    linarith
  · have h := key hy hxy
    have hnp : Real.exp (-x) - Real.exp (-y) ≤ 0 := by
      have : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
      linarith
    rw [abs_of_nonpos hnp, abs_of_nonneg (by linarith)]
    linarith

/-- `(y - x)(e^{-x} - e^{-y}) ≥ 0`: the Boltzmann weight is antitone. -/
theorem mul_exp_neg_sub_exp_neg_nonneg (x y : ℝ) :
    0 ≤ (y - x) * (Real.exp (-x) - Real.exp (-y)) := by
  rcases le_total x y with hxy | hxy
  · have : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    exact mul_nonneg (by linarith) (by linarith)
  · have : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

omit [Fintype ι] in
/-- The tested quantity `D (a - b)` is nonnegative for `t ≥ 0`. -/
theorem weightDiff_mul_nonneg (L₁ L₂ : (ι → ℝ) → ℝ) {t : ℝ} (ht : 0 ≤ t) (w : ι → ℝ) :
    0 ≤ (L₂ w - L₁ w) * (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := by
  rcases le_total (L₁ w) (L₂ w) with h | h
  · have : Real.exp (-(t * L₂ w)) ≤ Real.exp (-(t * L₁ w)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact mul_nonneg (by linarith) (by linarith)
  · have : Real.exp (-(t * L₁ w)) ≤ Real.exp (-(t * L₂ w)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

omit [Fintype ι] in
/-- The square of the weight difference is controlled by the tested
quantity: `|a - b|² ≤ t D (a - b)` for `t ≥ 0` and nonnegative losses. -/
theorem sq_exp_sub_le_mul {L₁ L₂ : (ι → ℝ) → ℝ}
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w) {t : ℝ} (ht : 0 ≤ t) (w : ι → ℝ) :
    (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) ^ 2 ≤
      t * ((L₂ w - L₁ w) *
        (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)))) := by
  have hx : 0 ≤ t * L₁ w := mul_nonneg ht (hL1 w)
  have hy : 0 ≤ t * L₂ w := mul_nonneg ht (hL2 w)
  have hlip := abs_exp_neg_sub_exp_neg_le hx hy
  have hsign := mul_exp_neg_sub_exp_neg_nonneg (t * L₁ w) (t * L₂ w)
  set a := Real.exp (-(t * L₁ w)) with ha
  set b := Real.exp (-(t * L₂ w)) with hb
  have habs : |a - b| * |a - b| ≤ |a - b| * |t * L₂ w - t * L₁ w| :=
    mul_le_mul_of_nonneg_left (by rwa [abs_sub_comm (t * L₂ w) (t * L₁ w)]) (abs_nonneg _)
  have hprod : |a - b| * |t * L₂ w - t * L₁ w| =
      (t * L₂ w - t * L₁ w) * (a - b) := by
    rw [← abs_mul, mul_comm, abs_of_nonneg hsign]
  calc (a - b) ^ 2 = |a - b| * |a - b| := by rw [← sq_abs, sq]
    _ ≤ (t * L₂ w - t * L₁ w) * (a - b) := habs.trans_eq hprod
    _ = t * ((L₂ w - L₁ w) * (a - b)) := by ring

/-! ### SuperPoly helpers -/

/-- A function bounded by `C_N t^{-N}` eventually, for every `N`, is
beyond all orders. -/
theorem superPoly_of_forall_eventually_le {f : ℝ → ℝ}
    (h : ∀ N : ℕ, ∃ C : ℝ, ∀ᶠ t in atTop, |f t| ≤ C * t ^ (-(N : ℝ))) :
    SuperPoly f := by
  intro N
  obtain ⟨C, hC⟩ := h (N + 1)
  have hbig : f =O[atTop] fun t : ℝ ↦ t ^ (-((N + 1 : ℕ) : ℝ)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with t ht htpos
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
    exact ht
  have hsmall : (fun t : ℝ ↦ t ^ (-((N + 1 : ℕ) : ℝ))) =o[atTop]
      fun t : ℝ ↦ t ^ (-(N : ℝ)) := by
    have hinv : (fun t : ℝ ↦ t⁻¹) =o[atTop] fun _ : ℝ ↦ (1 : ℝ) :=
      (isLittleO_one_iff ℝ).mpr tendsto_inv_atTop_zero
    have := hinv.mul_isBigO (isBigO_refl (fun t : ℝ ↦ t ^ (-(N : ℝ))) atTop)
    refine this.congr' ?_ (Eventually.of_forall fun t ↦ one_mul _)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t htpos
    rw [show (-((N + 1 : ℕ) : ℝ)) = (-1 : ℝ) + -(N : ℝ) by push_cast; ring,
      Real.rpow_add htpos, Real.rpow_neg_one]
  exact hbig.trans_isLittleO hsmall

/-- Domination by a constant multiple of a beyond-all-orders function. -/
theorem SuperPoly.of_abs_le {f g : ℝ → ℝ} (hg : SuperPoly g) {M : ℝ}
    (h : ∀ᶠ t in atTop, |f t| ≤ M * |g t|) : SuperPoly f := by
  intro N
  refine IsBigO.trans_isLittleO (IsBigO.of_bound M ?_) (hg N)
  filter_upwards [h] with t ht
  simpa [Real.norm_eq_abs] using ht

/-- A beyond-all-orders function times a polynomially bounded one is
beyond all orders. -/
theorem SuperPoly.polyBounded_mul {f B : ℝ → ℝ} (hf : SuperPoly f)
    {A : ℝ} {n : ℕ} (hB : ∀ᶠ t in atTop, |B t| ≤ A * t ^ n) :
    SuperPoly fun t ↦ B t * f t := by
  refine superPoly_of_forall_eventually_le fun N ↦ ⟨A, ?_⟩
  have hfN := isLittleO_iff.mp (hf (N + n)) one_pos
  filter_upwards [hB, hfN, eventually_gt_atTop (0 : ℝ)] with t hBt hft htpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _),
    one_mul] at hft
  have hAt : 0 ≤ A * t ^ n := le_trans (abs_nonneg _) hBt
  have hsplit : t ^ n * t ^ (-((N + n : ℕ) : ℝ)) = t ^ (-(N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
    congr 1
    push_cast
    ring
  calc |B t * f t| = |B t| * |f t| := abs_mul _ _
    _ ≤ (A * t ^ n) * t ^ (-((N + n : ℕ) : ℝ)) := mul_le_mul hBt hft (abs_nonneg _) hAt
    _ = A * (t ^ n * t ^ (-((N + n : ℕ) : ℝ))) := by ring
    _ = A * t ^ (-(N : ℝ)) := by rw [hsplit]

/-! ### Integrability of bounded compactly supported functions -/

/-- A bounded, a.e.-strongly measurable, compactly supported function is
integrable. -/
theorem integrable_of_bounded_of_hasCompactSupport {f : (ι → ℝ) → ℝ}
    (hfm : AEStronglyMeasurable f (volume : Measure (ι → ℝ)))
    (hfs : HasCompactSupport f) {M : ℝ} (hM : ∀ w, |f w| ≤ M) :
    Integrable f := by
  have hK : IsCompact (tsupport f) := hfs
  have hKm : MeasurableSet (tsupport f) := hK.isClosed.measurableSet
  have hg : Integrable ((tsupport f).indicator fun _ ↦ M) :=
    (integrable_indicator_iff hKm).mpr (integrableOn_const hK.measure_lt_top.ne)
  refine hg.mono' hfm (Eventually.of_forall fun w ↦ ?_)
  rw [Real.norm_eq_abs]
  by_cases hw : w ∈ tsupport f
  · rw [Set.indicator_of_mem hw]
    exact hM w
  · rw [Set.indicator_of_notMem hw, image_eq_zero_of_notMem_tsupport hw, abs_zero]

/-! ### Local total variation beyond all orders -/

/-- **Local total variation is beyond all orders.** For smooth
nonnegative losses whose Laplace families agree exactly beyond all orders
on `C_c^∞`, and any smooth compactly supported `η`,
`∫ η² |e^{-tL₂} - e^{-tL₁}| = o(t^{-∞})`. -/
theorem superPoly_integral_sq_mul_abs_exp_sub {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    {η : (ι → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) :
    SuperPoly fun t ↦ ∫ w, η w ^ 2 *
      |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| := by
  have hL1c := h1.continuous
  have hL2c := h2.continuous
  have hηc := hη.continuous
  have hη2s : HasCompactSupport (fun w ↦ η w ^ 2) :=
    hηs.comp_left (g := fun x : ℝ ↦ x ^ 2) (by simp)
  -- the tested observable `η² D` and its beyond-all-orders energy
  set ψ : (ι → ℝ) → ℝ := fun w ↦ η w ^ 2 * (L₂ w - L₁ w) with hψ_def
  have hψ : ContDiff ℝ ∞ ψ := (hη.pow 2).mul (h2.sub h1)
  have hψs : HasCompactSupport ψ := hη2s.mul_right
  have hE := hexact ψ hψ hψs
  have hint₁ : ∀ t : ℝ, Integrable fun w ↦ ψ w * Real.exp (-(t * L₁ w)) :=
    fun t ↦ integrable_mul_exp_neg_of_compactSupport hψ.continuous hψs hL1c t
  have hint₂ : ∀ t : ℝ, Integrable fun w ↦ ψ w * Real.exp (-(t * L₂ w)) :=
    fun t ↦ integrable_mul_exp_neg_of_compactSupport hψ.continuous hψs hL2c t
  have hEeq : ∀ t : ℝ, (∫ w, η w ^ 2 * ((L₂ w - L₁ w) *
      (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))))) =
      (∫ w, ψ w * Real.exp (-(t * L₁ w))) - ∫ w, ψ w * Real.exp (-(t * L₂ w)) := by
    intro t
    rw [← integral_sub (hint₁ t) (hint₂ t)]
    congr 1
    funext w
    simp only [hψ_def]
    ring
  have hEsp : SuperPoly fun t ↦ ∫ w, η w ^ 2 * ((L₂ w - L₁ w) *
      (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)))) := by
    have hneg : SuperPoly fun t ↦ -((∫ w, ψ w * Real.exp (-(t * L₂ w)))
        - ∫ w, ψ w * Real.exp (-(t * L₁ w))) := fun N ↦ (hE N).neg_left
    refine hneg.congr (Eventually.of_forall fun t ↦ ?_)
    beta_reduce
    rw [hEeq t]
    ring
  -- continuity and integrability of the pointwise pieces
  have hcont_ab : ∀ t : ℝ, Continuous fun w ↦
      Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)) := fun t ↦
    (Real.continuous_exp.comp ((continuous_const.mul hL1c).neg)).sub
      (Real.continuous_exp.comp ((continuous_const.mul hL2c).neg))
  have hint_abs : ∀ t : ℝ, Integrable fun w ↦ η w ^ 2 *
      |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| := by
    intro t
    have hc : Continuous fun w ↦ η w ^ 2 *
        |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| :=
      (hηc.pow 2).mul ((Real.continuous_exp.comp ((continuous_const.mul hL2c).neg)).sub
        (Real.continuous_exp.comp ((continuous_const.mul hL1c).neg))).abs
    exact hc.integrable_of_hasCompactSupport hη2s.mul_right
  have hint_η2 : Integrable fun w ↦ η w ^ 2 :=
    (hηc.pow 2).integrable_of_hasCompactSupport hη2s
  have hint_E : ∀ t : ℝ, Integrable fun w ↦ η w ^ 2 * ((L₂ w - L₁ w) *
      (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)))) := by
    intro t
    have hc : Continuous fun w ↦ η w ^ 2 * ((L₂ w - L₁ w) *
        (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)))) :=
      (hηc.pow 2).mul ((hL2c.sub hL1c).mul (hcont_ab t))
    exact hc.integrable_of_hasCompactSupport hη2s.mul_right
  have hAη : 0 ≤ ∫ w, η w ^ 2 := integral_nonneg fun w ↦ sq_nonneg _
  -- the estimate at every order
  refine superPoly_of_forall_eventually_le fun N ↦ ⟨(∫ w, η w ^ 2) / 2 + 1 / 2, ?_⟩
  have hE' := isLittleO_iff.mp (hEsp (2 * N + 1)) one_pos
  filter_upwards [hE', eventually_gt_atTop (0 : ℝ)] with t hEt htpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _),
    one_mul] at hEt
  have hεpos : 0 < t ^ (-(N : ℝ)) := Real.rpow_pos_of_pos htpos _
  have hunit : t ^ (-(N : ℝ)) * t ^ N = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
    simp
  -- pointwise AM–GM with the free parameter `t^{-N}`
  have hpt : ∀ w, η w ^ 2 * |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| ≤
      t ^ (-(N : ℝ)) / 2 * η w ^ 2 +
        t ^ (N + 1) / 2 * (η w ^ 2 * ((L₂ w - L₁ w) *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))))) := by
    intro w
    set h := Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)) with hh
    have hsq := sq_exp_sub_le_mul hL1 hL2 htpos.le w
    have habs : |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| = |h| := by
      rw [hh, abs_sub_comm]
    rw [habs]
    -- `|h| ≤ ε/2 + h²/(2ε)` with `ε = t^{-N}`, i.e. `|h| ≤ ε/2 + t^N h²/2`
    have hamgm : |h| ≤ t ^ (-(N : ℝ)) / 2 + t ^ N * h ^ 2 / 2 := by
      have h0 : 0 ≤ (t ^ (-(N : ℝ)) - |h|) ^ 2 := sq_nonneg _
      have hsqabs : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
      have htN : 0 < t ^ N := pow_pos htpos N
      -- multiply the target by `ε > 0`
      have key : t ^ (-(N : ℝ)) * |h| ≤ t ^ (-(N : ℝ)) * (t ^ (-(N : ℝ)) / 2) +
          t ^ (-(N : ℝ)) * (t ^ N * h ^ 2 / 2) := by
        have : t ^ (-(N : ℝ)) * (t ^ N * h ^ 2 / 2) = h ^ 2 / 2 := by
          calc t ^ (-(N : ℝ)) * (t ^ N * h ^ 2 / 2)
              = (t ^ (-(N : ℝ)) * t ^ N) * h ^ 2 / 2 := by ring
            _ = h ^ 2 / 2 := by rw [hunit, one_mul]
        rw [this, hsqabs]
        nlinarith [h0]
      have key' : t ^ (-(N : ℝ)) * |h| ≤
          t ^ (-(N : ℝ)) * (t ^ (-(N : ℝ)) / 2 + t ^ N * h ^ 2 / 2) := by
        rw [mul_add]
        exact key
      exact le_of_mul_le_mul_left key' hεpos
    have hη2 : 0 ≤ η w ^ 2 := sq_nonneg _
    calc η w ^ 2 * |h| ≤ η w ^ 2 * (t ^ (-(N : ℝ)) / 2 + t ^ N * h ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hamgm hη2
      _ ≤ η w ^ 2 * (t ^ (-(N : ℝ)) / 2 + t ^ N * (t * ((L₂ w - L₁ w) * h)) / 2) := by
          gcongr
      _ = t ^ (-(N : ℝ)) / 2 * η w ^ 2 +
          t ^ (N + 1) / 2 * (η w ^ 2 * ((L₂ w - L₁ w) * h)) := by ring
  -- integrate the pointwise bound
  have hintRHS : Integrable fun w ↦ t ^ (-(N : ℝ)) / 2 * η w ^ 2 +
      t ^ (N + 1) / 2 * (η w ^ 2 * ((L₂ w - L₁ w) *
        (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))))) :=
    (hint_η2.const_mul _).add ((hint_E t).const_mul _)
  have hmono := integral_mono (hint_abs t) hintRHS hpt
  rw [integral_add (hint_η2.const_mul _) ((hint_E t).const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have hEle : (∫ w, η w ^ 2 * ((L₂ w - L₁ w) *
      (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))))) ≤
      t ^ (-((2 * N + 1 : ℕ) : ℝ)) := le_trans (le_abs_self _) hEt
  have hpow : t ^ (N + 1) / 2 * t ^ (-((2 * N + 1 : ℕ) : ℝ)) = t ^ (-(N : ℝ)) / 2 := by
    rw [div_mul_eq_mul_div, ← Real.rpow_natCast, ← Real.rpow_add htpos]
    congr 2
    push_cast
    ring
  have hnn : 0 ≤ ∫ w, η w ^ 2 * |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| :=
    integral_nonneg fun w ↦ mul_nonneg (sq_nonneg _) (abs_nonneg _)
  rw [abs_of_nonneg hnn]
  calc ∫ w, η w ^ 2 * |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))|
      ≤ t ^ (-(N : ℝ)) / 2 * (∫ w, η w ^ 2) + t ^ (N + 1) / 2 *
          ∫ w, η w ^ 2 * ((L₂ w - L₁ w) *
            (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)))) := hmono
    _ ≤ t ^ (-(N : ℝ)) / 2 * (∫ w, η w ^ 2) +
        t ^ (N + 1) / 2 * t ^ (-((2 * N + 1 : ℕ) : ℝ)) := by
        gcongr
    _ = ((∫ w, η w ^ 2) / 2 + 1 / 2) * t ^ (-(N : ℝ)) := by
        rw [hpow]
        ring

/-! ### From local total variation to bounded tests -/

/-- A smooth bump equal to `1` on a prescribed compact set. -/
theorem exists_smooth_bump_one_on_compact {K : Set (ι → ℝ)} (hK : IsCompact K) :
    ∃ η : (ι → ℝ) → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      (∀ w, 0 ≤ η w) ∧ ∀ w ∈ K, η w = 1 := by
  obtain ⟨R, hRpos, hKR⟩ : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.closedBall (0 : ι → ℝ) R := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ι → ℝ)).mp hK.isBounded
    exact ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have h4R : 0 < 4 * R := by positivity
  let f : ContDiffBump (0 : ι → ℝ) := gapBump (0 : ι → ℝ) h4R
  have hrIn : f.rIn = 4 * R / 4 := rfl
  refine ⟨⇑f, f.contDiff, f.hasCompactSupport, f.nonneg', fun w hw ↦ ?_⟩
  apply f.one_of_mem_closedBall
  rw [Metric.mem_closedBall, hrIn]
  have hwr := hKR hw
  rw [Metric.mem_closedBall] at hwr
  linarith

/-- **Bounded compactly supported tests agree beyond all orders.** -/
theorem superPoly_difference_of_bounded {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    {φ : (ι → ℝ) → ℝ} (hφm : AEStronglyMeasurable φ (volume : Measure (ι → ℝ)))
    (hφs : HasCompactSupport φ) {M : ℝ} (hφM : ∀ w, |φ w| ≤ M) :
    SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
      - ∫ w, φ w * Real.exp (-(t * L₁ w)) := by
  have hL1c := h1.continuous
  have hL2c := h2.continuous
  obtain ⟨η, hη, hηs, hη0, hη1⟩ := exists_smooth_bump_one_on_compact (hφs : IsCompact (tsupport φ))
  have hTV := superPoly_integral_sq_mul_abs_exp_sub h1 h2 hL1 hL2 hexact hη hηs
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hφM 0)
  refine hTV.of_abs_le (M := M) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  -- integrability of the two moments
  have hexp_le : ∀ (L : (ι → ℝ) → ℝ), (∀ w, 0 ≤ L w) → ∀ w,
      |Real.exp (-(t * L w))| ≤ 1 := by
    intro L hL w
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg ht (hL w))
  have hint : ∀ (L : (ι → ℝ) → ℝ), Continuous L → (∀ w, 0 ≤ L w) →
      Integrable fun w ↦ φ w * Real.exp (-(t * L w)) := by
    intro L hLc hL
    refine integrable_of_bounded_of_hasCompactSupport
      (hφm.mul (Real.continuous_exp.comp ((continuous_const.mul hLc).neg)).aestronglyMeasurable)
      hφs.mul_right (M := M) fun w ↦ ?_
    rw [abs_mul]
    calc |φ w| * |Real.exp (-(t * L w))| ≤ M * 1 :=
          mul_le_mul (hφM w) (hexp_le L hL w) (abs_nonneg _) hM0
      _ = M := mul_one _
  have hTVnn : 0 ≤ ∫ w, η w ^ 2 * |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| :=
    integral_nonneg fun w ↦ mul_nonneg (sq_nonneg _) (abs_nonneg _)
  rw [abs_of_nonneg hTVnn, ← integral_sub (hint L₂ hL2c hL2) (hint L₁ hL1c hL1)]
  -- pointwise domination by `M η² |b - a|`
  have hint_dom : Integrable fun w ↦ M * (η w ^ 2 *
      |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))|) := by
    have hc : Continuous fun w ↦ η w ^ 2 *
        |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| :=
      (hη.continuous.pow 2).mul ((Real.continuous_exp.comp ((continuous_const.mul hL2c).neg)).sub
        (Real.continuous_exp.comp ((continuous_const.mul hL1c).neg))).abs
    exact (hc.integrable_of_hasCompactSupport
      ((hηs.comp_left (g := fun x : ℝ ↦ x ^ 2) (by simp)).mul_right)).const_mul _
  have hint_diff : Integrable fun w ↦ φ w * Real.exp (-(t * L₂ w)) -
      φ w * Real.exp (-(t * L₁ w)) := (hint L₂ hL2c hL2).sub (hint L₁ hL1c hL1)
  calc |∫ w, φ w * Real.exp (-(t * L₂ w)) - φ w * Real.exp (-(t * L₁ w))|
      ≤ ∫ w, |φ w * Real.exp (-(t * L₂ w)) - φ w * Real.exp (-(t * L₁ w))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, M * (η w ^ 2 * |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))|) := by
        refine integral_mono hint_diff.abs hint_dom fun w ↦ ?_
        rw [← mul_sub, abs_mul]
        by_cases hw : w ∈ tsupport φ
        · rw [hη1 w hw, one_pow, one_mul]
          exact mul_le_mul_of_nonneg_right (hφM w) (abs_nonneg _)
        · rw [image_eq_zero_of_notMem_tsupport hw, abs_zero, zero_mul]
          exact mul_nonneg hM0 (mul_nonneg (sq_nonneg _) (abs_nonneg _))
    _ = M * ∫ w, η w ^ 2 * |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| :=
        integral_const_mul _ _

/-- **Continuous compactly supported tests agree beyond all orders.** -/
theorem superPoly_difference_of_continuous {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    {φ : (ι → ℝ) → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
      - ∫ w, φ w * Real.exp (-(t * L₁ w)) := by
  obtain ⟨M, hM⟩ := hφs.exists_bound_of_continuous hφc
  exact superPoly_difference_of_bounded h1 h2 hL1 hL2 hexact hφc.aestronglyMeasurable hφs
    (M := M) fun w ↦ by simpa [Real.norm_eq_abs] using hM w

/-- **Total variation over a compact set is beyond all orders.** -/
theorem superPoly_setIntegral_abs_exp_sub {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    {K : Set (ι → ℝ)} (hK : IsCompact K) :
    SuperPoly fun t ↦ ∫ w in K, |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| := by
  have hL1c := h1.continuous
  have hL2c := h2.continuous
  obtain ⟨η, hη, hηs, hη0, hη1⟩ := exists_smooth_bump_one_on_compact hK
  have hTV := superPoly_integral_sq_mul_abs_exp_sub h1 h2 hL1 hL2 hexact hη hηs
  refine hTV.of_abs_le (M := 1) ?_
  filter_upwards with t
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hc : Continuous fun w ↦ |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| :=
    ((Real.continuous_exp.comp ((continuous_const.mul hL2c).neg)).sub
      (Real.continuous_exp.comp ((continuous_const.mul hL1c).neg))).abs
  have hη2s : HasCompactSupport (fun w ↦ η w ^ 2) :=
    hηs.comp_left (g := fun x : ℝ ↦ x ^ 2) (by simp)
  have hsupp : HasCompactSupport fun w ↦ η w ^ 2 *
      |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| := hη2s.mul_right
  have hint_dom : Integrable fun w ↦ η w ^ 2 *
      |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| :=
    ((hη.continuous.pow 2).mul hc).integrable_of_hasCompactSupport hsupp
  have hKnn : 0 ≤ ∫ w in K, |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| :=
    setIntegral_nonneg hKm fun w _ ↦ abs_nonneg _
  have hTVnn : 0 ≤ ∫ w, η w ^ 2 * |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| :=
    integral_nonneg fun w ↦ mul_nonneg (sq_nonneg _) (abs_nonneg _)
  rw [abs_of_nonneg hKnn, abs_of_nonneg hTVnn, one_mul]
  have hEqOn : Set.EqOn (fun w ↦ |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))|)
      (fun w ↦ η w ^ 2 * |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))|) K := by
    intro w hw
    simp only [hη1 w hw, one_pow, one_mul]
  rw [setIntegral_congr_fun hKm hEqOn]
  exact setIntegral_le_integral hint_dom
    (Eventually.of_forall fun w ↦ mul_nonneg (sq_nonneg _) (abs_nonneg _))

/-! ### Corollaries in the closure package -/

/-- **Projective agreement on smooth tests, local agreement at one `C²`
zero, smooth losses: exact agreement on bounded compactly supported
tests.** -/
theorem superPoly_difference_of_projective_bounded {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {p : ι → ℝ} (hp : L₁ p = 0) (hC1 : ContDiffAt ℝ 2 L₁ p)
    (hEq : ∀ᶠ w in 𝓝 p, L₁ w = L₂ w)
    {C : ℝ → ℝ} (hfam : ProjectiveAgreement L₁ L₂ C)
    {φ : (ι → ℝ) → ℝ} (hφm : AEStronglyMeasurable φ (volume : Measure (ι → ℝ)))
    (hφs : HasCompactSupport φ) {M : ℝ} (hφM : ∀ w, |φ w| ≤ M) :
    SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
      - ∫ w, φ w * Real.exp (-(t * L₁ w)) :=
  superPoly_difference_of_bounded h1 h2 hL1 hL2
    (superPoly_difference_of_projective h1.continuous hL1 hp hC1 hEq hfam) hφm hφs hφM

/-- **Normalized expectations of bounded tests agree beyond all orders**,
given exact smooth-test agreement, the anchor lower bounds on both
partition values, and `Z₂/Z₁ = 1 + o(t^{-∞})`. The identity used is
`I₂/Z₂ - I₁/Z₁ = (I₂ - I₁)/Z₁ + (I₂/Z₂)(1 - Z₂/Z₁)`. -/
theorem superPoly_normalized_difference_of_bounded {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    {Z₁ Z₂ : ℝ → ℝ} (hZ1 : ∀ t, 0 < Z₁ t) (hZ2 : ∀ t, 0 < Z₂ t)
    {κ₁ κ₂ : ℝ} {n : ℕ} (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂)
    (hZ1low : ∀ᶠ t in atTop, κ₁ * t ^ (-(n : ℝ)) ≤ Z₁ t)
    (hZ2low : ∀ᶠ t in atTop, κ₂ * t ^ (-(n : ℝ)) ≤ Z₂ t)
    (hratio : SuperPoly fun t ↦ Z₂ t / Z₁ t - 1)
    {φ : (ι → ℝ) → ℝ} (hφm : AEStronglyMeasurable φ (volume : Measure (ι → ℝ)))
    (hφs : HasCompactSupport φ) {M : ℝ} (hφM : ∀ w, |φ w| ≤ M) :
    SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w))) / Z₂ t
      - (∫ w, φ w * Real.exp (-(t * L₁ w))) / Z₁ t := by
  have hL2c := h2.continuous
  have hdiff := superPoly_difference_of_bounded h1 h2 hL1 hL2 hexact hφm hφs hφM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hφM 0)
  -- `1/Z_i ≤ t^n/κ_i` eventually
  have hinv : ∀ {Z : ℝ → ℝ} {κ : ℝ}, 0 < κ → (∀ t, 0 < Z t) →
      (∀ᶠ t in atTop, κ * t ^ (-(n : ℝ)) ≤ Z t) →
      ∀ᶠ t in atTop, |(Z t)⁻¹| ≤ κ⁻¹ * t ^ n := by
    intro Z κ hκ hZ hlow
    filter_upwards [hlow, eventually_gt_atTop (0 : ℝ)] with t hlt htpos
    rw [abs_of_pos (inv_pos.mpr (hZ t))]
    have hunit : t ^ (-(n : ℝ)) * t ^ n = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
      simp
    have hpos : 0 < κ * t ^ (-(n : ℝ)) := by positivity
    calc (Z t)⁻¹ ≤ (κ * t ^ (-(n : ℝ)))⁻¹ := by gcongr
      _ = κ⁻¹ * t ^ n := by
          rw [mul_inv, Real.rpow_neg htpos.le, inv_inv, Real.rpow_natCast]
  -- `I₂` is bounded for `t ≥ 0`
  have hI2bdd : ∀ᶠ t in atTop, |∫ w, φ w * Real.exp (-(t * L₂ w))| ≤
      M * volume.real (tsupport φ) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hK : IsCompact (tsupport φ) := hφs
    have hKm : MeasurableSet (tsupport φ) := hK.isClosed.measurableSet
    have hint : Integrable fun w ↦ φ w * Real.exp (-(t * L₂ w)) := by
      refine integrable_of_bounded_of_hasCompactSupport
        (hφm.mul (Real.continuous_exp.comp ((continuous_const.mul hL2c).neg)).aestronglyMeasurable)
        hφs.mul_right (M := M) fun w ↦ ?_
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-(t * L₂ w)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg ht (hL2 w))
      calc |φ w| * Real.exp (-(t * L₂ w)) ≤ M * 1 :=
            mul_le_mul (hφM w) this (Real.exp_pos _).le hM0
        _ = M := mul_one _
    have hind : Integrable ((tsupport φ).indicator fun _ ↦ M) :=
      (integrable_indicator_iff hKm).mpr (integrableOn_const hK.measure_lt_top.ne)
    calc |∫ w, φ w * Real.exp (-(t * L₂ w))|
        ≤ ∫ w, |φ w * Real.exp (-(t * L₂ w))| := abs_integral_le_integral_abs
      _ ≤ ∫ w, (tsupport φ).indicator (fun _ ↦ M) w := by
          refine integral_mono hint.abs hind fun w ↦ ?_
          by_cases hw : w ∈ tsupport φ
          · rw [Set.indicator_of_mem hw, abs_mul, abs_of_pos (Real.exp_pos _)]
            have : Real.exp (-(t * L₂ w)) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              exact neg_nonpos.mpr (mul_nonneg ht (hL2 w))
            calc |φ w| * Real.exp (-(t * L₂ w)) ≤ M * 1 :=
                  mul_le_mul (hφM w) this (Real.exp_pos _).le hM0
              _ = M := mul_one _
          · rw [Set.indicator_of_notMem hw, image_eq_zero_of_notMem_tsupport hw, zero_mul,
              abs_zero]
      _ = M * volume.real (tsupport φ) := by
          rw [integral_indicator hKm, setIntegral_const, smul_eq_mul, mul_comm]
  -- assemble the identity
  have hterm1 : SuperPoly fun t ↦ (Z₁ t)⁻¹ *
      ((∫ w, φ w * Real.exp (-(t * L₂ w))) - ∫ w, φ w * Real.exp (-(t * L₁ w))) :=
    hdiff.polyBounded_mul (hinv hκ₁ hZ1 hZ1low)
  have hterm2 : SuperPoly fun t ↦
      ((∫ w, φ w * Real.exp (-(t * L₂ w))) * (Z₂ t)⁻¹) * (Z₂ t / Z₁ t - 1) := by
    refine hratio.polyBounded_mul (A := M * volume.real (tsupport φ) * κ₂⁻¹) (n := n) ?_
    filter_upwards [hI2bdd, hinv hκ₂ hZ2 hZ2low] with t hI ht
    rw [abs_mul]
    calc |∫ w, φ w * Real.exp (-(t * L₂ w))| * |(Z₂ t)⁻¹|
        ≤ M * volume.real (tsupport φ) * (κ₂⁻¹ * t ^ n) :=
          mul_le_mul hI ht (abs_nonneg _) (by positivity)
      _ = M * volume.real (tsupport φ) * κ₂⁻¹ * t ^ n := by ring
  refine (hterm1.sub hterm2).congr (Eventually.of_forall fun t ↦ ?_)
  have h1t : Z₁ t ≠ 0 := (hZ1 t).ne'
  have h2t : Z₂ t ≠ 0 := (hZ2 t).ne'
  field_simp
  ring

end Laplace
