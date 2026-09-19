/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NormalizedSingular
import Laplace.OnePointAnchoring

/-!
# Closing the projective (normalized) identifiability story

`NormalizedSingular` shows that projective agreement of two Laplace
families beyond all orders,
`∫ φ e^{-tL₂} - C(t) ∫ φ e^{-tL₁} = o(t^{-∞})` for all `φ ∈ C_c^∞`,
forces `L₁ = L₂` near every common analytic zero, whatever the scalar
`C`. This file supplies the two facts that finish the picture and make
the normalized (`1/Z`) and unnormalized theories coincide.

* **The anchor** (`exists_lower_bound_integral_exp_near_zero`,
  `anchor_lower_bound_eventually`): near a zero `p` of a nonnegative `C²`
  weight `K`, a bump `ψ` equal to `1` near `p` has
  `∫ ψ e^{-tK} ≥ κ t^{-d/2}` for large `t`. This is the `a ≡ 1` case of
  the sector lower bound, and it discharges the polynomial lower bound
  `hanchor_low` that the seabed's scalar-gauge lemmas (`Anchoring`,
  `OnePointAnchoring`) had left as a hypothesis.
* **The gap** (`abs_integral_mul_exp_le_of_gap`,
  `superPoly_polyBounded_mul_integral_of_gap`): away from the zero set
  the Laplace integral is exponentially small, and stays beyond all
  orders after multiplication by any polynomially bounded scalar.
* **Scalar tameness** (`exists_scalar_upper_bound`,
  `eventually_scalar_lower_bound`): whenever both losses have zeros,
  `c t^{-d} ≤ C(t) ≤ A t^{d}` eventually; in particular `C` is
  eventually positive. Nothing is assumed of `C`.
* **Equal zero loci** (`zero_iff_zero_of_projective`): continuous
  nonnegative losses, `C²` near their zeros, both with zeros, that agree
  projectively have the same zero set. No analyticity.
* **Scalar rigidity and transfer**
  (`superPoly_scalar_sub_one_of_eventuallyEq`,
  `superPoly_difference_of_projective`): once the losses agree near one
  zero, `C(t) = 1 + o(t^{-∞})` and the two families agree *exactly*
  beyond all orders at every tested observable. With the merged germ
  theorem supplying the local agreement
  (`projective_forces_exact_at`): at a common analytic zero, projective
  agreement fixes its own scalar gauge.
* **The `1/Z` headline** (`normalized_expectations_closure`): equality
  of the normalized expansions `Φ_{L₁} = Φ_{L₂}` for smooth nonnegative
  losses analytic at their zeros, both with zeros, gives equal zero
  sets, `L₁ = L₂` on an open neighbourhood of the zero set,
  `Z₂/Z₁ = 1 + o(t^{-∞})`, and exact agreement of every moment.

Conclusions are for the tested class `C_c^∞`. Upgrading exact agreement
to continuous observables (local total variation
`∫_K |e^{-tL₂} - e^{-tL₁}| = o(t^{-∞})`) is a separate argument, left as
a follow-up.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff Pointwise

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-! ### The anchor: a Gaussian-type lower bound near a zero -/

/-- **Anchor lower bound from a local quadratic upper bound.** If
`K ≤ C₀ ‖w - p‖²` on the ball of radius `R` about `p` and the nonnegative
compactly supported `ψ` equals `1` there, then
`∫ ψ e^{-tK} ≥ κ t^{-d/2}` for `t ≥ 4/R²`. The `a ≡ 1` case of
`sector_lower_bound_multi`. -/
theorem exists_lower_bound_integral_exp_of_quadratic
    {K ψ : (ι → ℝ) → ℝ} {p : ι → ℝ} (hKc : Continuous K)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hquad : ∀ w : ι → ℝ, ‖w - p‖ ≤ R → K w ≤ C0 * ‖w - p‖ ^ 2)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ w, 0 ≤ ψ w)
    (hψ1 : ∀ w : ι → ℝ, ‖w - p‖ ≤ R → ψ w = 1) :
    ∃ κ T₀ : ℝ, 0 < κ ∧ ∀ t : ℝ, T₀ ≤ t →
      κ * t ^ (-(Fintype.card ι : ℝ) / 2) ≤
        ∫ w, ψ w * Real.exp (-(t * K w)) := by
  set S : Set (ι → ℝ) := Metric.closedBall (0 : ι → ℝ) 1 with hS_def
  have hS : MeasurableSet S := measurableSet_closedBall
  have hSfin : volume S ≠ ⊤ := measure_closedBall_lt_top.ne
  have hSvol0 : volume S ≠ 0 :=
    (Metric.measure_closedBall_pos volume (0 : ι → ℝ) one_pos).ne'
  have hvolpos : 0 < (volume S).toReal := ENNReal.toReal_pos hSvol0 hSfin
  have hSnorm : ∀ x ∈ S, ‖x‖ ≤ 2 := fun x hx ↦ by
    have := mem_closedBall_zero_iff.mp hx
    linarith
  refine ⟨(volume S).toReal * Real.exp (-(4 * C0)), 4 / R ^ 2, by positivity, ?_⟩
  intro t ht
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have ht4 : 4 ≤ R ^ 2 * t := (div_le_iff₀' hR2).mp ht
  -- the shifted weight satisfies the quadratic bound at the origin
  have hK' : ∀ w : ι → ℝ, ‖w‖ ≤ R → K (p + w) ≤ C0 * ‖w‖ ^ 2 := by
    intro w hw
    have h := hquad (p + w) (by rw [add_sub_cancel_left]; exact hw)
    rwa [add_sub_cancel_left] at h
  have hgrow : ∀ x ∈ S, (1 : ℝ) * ((Real.sqrt t)⁻¹) ^ 0 ≤
      |(fun _ : ι → ℝ ↦ (1 : ℝ)) ((Real.sqrt t)⁻¹ • x)| := by
    intro x _
    simp
  -- on the scaled set the bump is `1`
  have hinvR : (Real.sqrt t)⁻¹ ≤ R := by
    rw [inv_le_comm₀ hst hR]
    have h3 : 2 / R ≤ Real.sqrt t := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, div_le_iff₀ hR2]
      linarith
    refine le_trans ?_ h3
    rw [inv_eq_one_div]
    gcongr
    norm_num
  have hscaled_norm : ∀ w ∈ ((Real.sqrt t)⁻¹) • S, ‖w‖ ≤ R := by
    rintro w ⟨x, hxS, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hst)]
    calc (Real.sqrt t)⁻¹ * ‖x‖ ≤ (Real.sqrt t)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hxS)
            (inv_pos.mpr hst).le
      _ = (Real.sqrt t)⁻¹ := mul_one _
      _ ≤ R := hinvR
  -- integrability of the shifted integrand
  have hshiftc : Continuous (fun w : ι → ℝ ↦ p + w) :=
    continuous_const.add continuous_id
  have hintf : Integrable fun w ↦ ψ (p + w) * Real.exp (-(t * K (p + w))) := by
    have hcont : Continuous fun w ↦ ψ (p + w) * Real.exp (-(t * K (p + w))) :=
      (hψc.comp hshiftc).mul
        (Real.continuous_exp.comp ((continuous_const.mul (hKc.comp hshiftc)).neg))
    refine hcont.integrable_of_hasCompactSupport ?_
    exact (hψs.comp_homeomorph (Homeomorph.addLeft p)).mul_right
  have hSm : MeasurableSet (((Real.sqrt t)⁻¹) • S) :=
    hS.const_smul_of_ne_zero (inv_pos.mpr hst).ne'
  have hcongr : Set.EqOn
      (fun w ↦ ((fun _ : ι → ℝ ↦ (1 : ℝ)) w) ^ 2 * Real.exp (-(t * K (p + w))))
      (fun w ↦ ψ (p + w) * Real.exp (-(t * K (p + w)))) (((Real.sqrt t)⁻¹) • S) := by
    intro w hw
    have h1 : ψ (p + w) = 1 :=
      hψ1 (p + w) (by rw [add_sub_cancel_left]; exact hscaled_norm w hw)
    simp [h1]
  have hintS : IntegrableOn
      (fun w ↦ ((fun _ : ι → ℝ ↦ (1 : ℝ)) w) ^ 2 * Real.exp (-(t * K (p + w))))
      (((Real.sqrt t)⁻¹) • S) volume :=
    (hintf.integrableOn).congr_fun hcongr.symm hSm
  have hsec := sector_lower_bound_multi (fun w ↦ K (p + w)) (fun _ ↦ (1 : ℝ)) 0
    hS hSfin zero_le_one hC0 hR ht4 hSnorm hgrow hK' hintS
  have hnonneg : ∀ w, 0 ≤ ψ (p + w) * Real.exp (-(t * K (p + w))) :=
    fun w ↦ mul_nonneg (hψ0 _) (Real.exp_nonneg _)
  have hle : ∫ w in ((Real.sqrt t)⁻¹) • S,
      ((fun _ : ι → ℝ ↦ (1 : ℝ)) w) ^ 2 * Real.exp (-(t * K (p + w)))
      ≤ ∫ w, ψ (p + w) * Real.exp (-(t * K (p + w))) := by
    rw [setIntegral_congr_fun hSm hcongr]
    exact setIntegral_le_integral hintf (Eventually.of_forall hnonneg)
  have htrans : (∫ w, ψ (p + w) * Real.exp (-(t * K (p + w)))) =
      ∫ w, ψ w * Real.exp (-(t * K w)) :=
    integral_add_left_eq_self (fun w ↦ ψ w * Real.exp (-(t * K w))) p
  have hexp : (-((0 : ℕ) : ℝ) - (Fintype.card ι : ℝ) / 2) =
      -(Fintype.card ι : ℝ) / 2 := by
    push_cast
    ring
  rw [hexp] at hsec
  calc (volume S).toReal * Real.exp (-(4 * C0)) * t ^ (-(Fintype.card ι : ℝ) / 2)
      = (volume S).toReal *
          (1 ^ 2 * Real.exp (-(4 * C0)) * t ^ (-(Fintype.card ι : ℝ) / 2)) := by ring
    _ ≤ ∫ w in ((Real.sqrt t)⁻¹) • S,
          ((fun _ : ι → ℝ ↦ (1 : ℝ)) w) ^ 2 * Real.exp (-(t * K (p + w))) := hsec
    _ ≤ ∫ w, ψ (p + w) * Real.exp (-(t * K (p + w))) := hle
    _ = ∫ w, ψ w * Real.exp (-(t * K w)) := htrans

/-- **Anchor lower bound near a `C²` zero.** For a continuous nonnegative
`K` with `K p = 0`, `C²` at `p`, and a nonnegative compactly supported
`ψ` equal to `1` near `p`: `∫ ψ e^{-tK} ≥ κ t^{-d/2}` for large `t`. -/
theorem exists_lower_bound_integral_exp_near_zero
    {K ψ : (ι → ℝ) → ℝ} {p : ι → ℝ} (hKc : Continuous K)
    (hK0 : ∀ w, 0 ≤ K w) (hKp : K p = 0) (hK2 : ContDiffAt ℝ 2 K p)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ w, 0 ≤ ψ w)
    (hψ1 : ∀ᶠ w in 𝓝 p, ψ w = 1) :
    ∃ κ T₀ : ℝ, 0 < κ ∧ ∀ t : ℝ, T₀ ≤ t →
      κ * t ^ (-(Fintype.card ι : ℝ) / 2) ≤
        ∫ w, ψ w * Real.exp (-(t * K w)) := by
  have hK2' : ContDiffAt ℝ 2 (fun w ↦ K (p + w)) 0 := by
    have hg : ContDiffAt ℝ 2 K ((fun w : ι → ℝ ↦ p + w) 0) := by simpa using hK2
    exact hg.comp 0 (contDiffAt_const.add contDiffAt_id)
  have hK0' : (fun w ↦ K (p + w)) 0 = 0 := by simp [hKp]
  have hKnn : ∀ᶠ w in 𝓝 (0 : ι → ℝ), 0 ≤ K (p + w) :=
    Eventually.of_forall fun w ↦ hK0 _
  obtain ⟨C0, R, hC0, hR, hsum⟩ := Multi.quadratic_upper_bound_of_nonneg hK2' hK0' hKnn
  obtain ⟨ε, hε, hψε⟩ := Metric.eventually_nhds_iff.mp hψ1
  have hR' : 0 < min R (ε / 2) := lt_min hR (by positivity)
  refine exists_lower_bound_integral_exp_of_quadratic (p := p) hKc hC0 hR' ?_ hψc hψs hψ0 ?_
  · intro w hw
    have h := hsum (w - p) (le_trans hw (min_le_left _ _))
    rwa [add_sub_cancel] at h
  · intro w hw
    apply hψε
    rw [dist_eq_norm]
    calc ‖w - p‖ ≤ min R (ε / 2) := hw
      _ ≤ ε / 2 := min_le_right _ _
      _ < ε := by linarith

/-- The anchor in the integer-power form consumed by the scalar-gauge
lemmas (`superPoly_of_mul_anchor`, `anchored_proportionality_remove_scalar`):
`κ t^{-d} ≤ ∫ ψ e^{-tK}` eventually. -/
theorem anchor_lower_bound_eventually
    {K ψ : (ι → ℝ) → ℝ} {p : ι → ℝ} (hKc : Continuous K)
    (hK0 : ∀ w, 0 ≤ K w) (hKp : K p = 0) (hK2 : ContDiffAt ℝ 2 K p)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ w, 0 ≤ ψ w)
    (hψ1 : ∀ᶠ w in 𝓝 p, ψ w = 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ t in atTop,
      κ * t ^ (-(Fintype.card ι : ℝ)) ≤ ∫ w, ψ w * Real.exp (-(t * K w)) := by
  obtain ⟨κ, T₀, hκ, hbound⟩ :=
    exists_lower_bound_integral_exp_near_zero hKc hK0 hKp hK2 hψc hψs hψ0 hψ1
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (1 : ℝ)] with t hT h1
  refine le_trans ?_ (hbound t hT)
  apply mul_le_mul_of_nonneg_left _ hκ.le
  apply Real.rpow_le_rpow_of_exponent_le h1
  have : (0 : ℝ) ≤ Fintype.card ι := by positivity
  linarith

/-- A Laplace integral anchored at a `C²` zero is never beyond all orders. -/
theorem not_superPoly_integral_exp_near_zero
    {K ψ : (ι → ℝ) → ℝ} {p : ι → ℝ} (hKc : Continuous K)
    (hK0 : ∀ w, 0 ≤ K w) (hKp : K p = 0) (hK2 : ContDiffAt ℝ 2 K p)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ w, 0 ≤ ψ w)
    (hψ1 : ∀ᶠ w in 𝓝 p, ψ w = 1) :
    ¬ SuperPoly fun t ↦ ∫ w, ψ w * Real.exp (-(t * K w)) := by
  intro hsp
  obtain ⟨κ, T₀, hκ, hbound⟩ :=
    exists_lower_bound_integral_exp_near_zero hKc hK0 hKp hK2 hψc hψs hψ0 hψ1
  exact lower_bound_not_superpolynomial hκ hbound hsp

/-! ### The gap: exponential smallness away from the zero set -/

/-- If `L ≥ δ` on the support of `ψ`, the Laplace integral is bounded by
`‖ψ‖₁ e^{-tδ}` for `t ≥ 0`. -/
theorem abs_integral_mul_exp_le_of_gap {L ψ : (ι → ℝ) → ℝ}
    (hLc : Continuous L) (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    {δ : ℝ} (hgap : ∀ w ∈ tsupport ψ, δ ≤ L w) {t : ℝ} (ht : 0 ≤ t) :
    |∫ w, ψ w * Real.exp (-(t * L w))| ≤
      (∫ w, |ψ w|) * Real.exp (-(t * δ)) := by
  have hint1 : Integrable fun w ↦ |ψ w| * Real.exp (-(t * L w)) :=
    integrable_mul_exp_neg_of_compactSupport hψc.abs hψs.abs hLc t
  have hint2 : Integrable fun w ↦ |ψ w| * Real.exp (-(t * δ)) :=
    (hψc.abs.integrable_of_hasCompactSupport hψs.abs).mul_const _
  calc |∫ w, ψ w * Real.exp (-(t * L w))|
      ≤ ∫ w, |ψ w * Real.exp (-(t * L w))| := abs_integral_le_integral_abs
    _ = ∫ w, |ψ w| * Real.exp (-(t * L w)) := by
        congr 1
        funext w
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ ∫ w, |ψ w| * Real.exp (-(t * δ)) := by
        refine integral_mono hint1 hint2 fun w ↦ ?_
        by_cases hw : w ∈ tsupport ψ
        · exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (hgap w hw) ht)))
            (abs_nonneg _)
        · rw [image_eq_zero_of_notMem_tsupport hw]
          simp
    _ = (∫ w, |ψ w|) * Real.exp (-(t * δ)) := integral_mul_const _ _

/-- **Gap times a polynomially bounded scalar is beyond all orders.** -/
theorem superPoly_polyBounded_mul_integral_of_gap {L ψ : (ι → ℝ) → ℝ} {B : ℝ → ℝ}
    (hLc : Continuous L) (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ w ∈ tsupport ψ, δ ≤ L w)
    {A : ℝ} {n : ℕ} (hB : ∀ᶠ t in atTop, |B t| ≤ A * t ^ n) :
    SuperPoly fun t ↦ B t * ∫ w, ψ w * Real.exp (-(t * L w)) := by
  -- `t^n ≤ e^{(δ/2) t}` eventually
  have hpow : ∀ᶠ t in atTop, |(t : ℝ) ^ n| ≤ 1 * ‖Real.exp (δ / 2 * t)‖ := by
    have := isLittleO_iff.mp (isLittleO_pow_exp_pos_mul_atTop n (half_pos hδ)) one_pos
    filter_upwards [this] with t ht
    simpa using ht
  have hM : 0 ≤ ∫ w, |ψ w| := integral_nonneg fun w ↦ abs_nonneg _
  refine superPoly_of_eventually_abs_le_exp (K := A * ∫ w, |ψ w|) (half_pos hδ) ?_
  filter_upwards [hB, hpow, eventually_gt_atTop (0 : ℝ)] with t hBt hpt ht
  have hI := abs_integral_mul_exp_le_of_gap hLc hψc hψs hgap ht.le
  have hAt : 0 ≤ A * t ^ n := le_trans (abs_nonneg _) hBt
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] at hpt
  have htn : t ^ n ≤ Real.exp (δ / 2 * t) := le_trans (le_abs_self _) hpt
  have hA : 0 ≤ A := by
    have htnpos : 0 < t ^ n := pow_pos ht n
    exact nonneg_of_mul_nonneg_left hAt htnpos
  -- `e^{(δ/2) t} e^{-tδ} = e^{-(δ/2) t}`
  have hexp : Real.exp (δ / 2 * t) * Real.exp (-(t * δ)) = Real.exp (-(δ / 2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc |B t * ∫ w, ψ w * Real.exp (-(t * L w))|
      = |B t| * |∫ w, ψ w * Real.exp (-(t * L w))| := abs_mul _ _
    _ ≤ (A * t ^ n) * ((∫ w, |ψ w|) * Real.exp (-(t * δ))) :=
        mul_le_mul hBt hI (abs_nonneg _) hAt
    _ ≤ (A * Real.exp (δ / 2 * t)) * ((∫ w, |ψ w|) * Real.exp (-(t * δ))) := by
        gcongr
    _ = (A * ∫ w, |ψ w|) * (Real.exp (δ / 2 * t) * Real.exp (-(t * δ))) := by ring
    _ = (A * ∫ w, |ψ w|) * Real.exp (-(δ / 2 * t)) := by rw [hexp]

/-- The Laplace integral of a bump supported in the gap is beyond all orders. -/
theorem superPoly_integral_mul_exp_of_gap {L ψ : (ι → ℝ) → ℝ}
    (hLc : Continuous L) (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ w ∈ tsupport ψ, δ ≤ L w) :
    SuperPoly fun t ↦ ∫ w, ψ w * Real.exp (-(t * L w)) := by
  have h := superPoly_polyBounded_mul_integral_of_gap (B := fun _ ↦ (1 : ℝ)) hLc hψc hψs hδ
    hgap (A := 1) (n := 0) (Eventually.of_forall fun t ↦ by simp)
  exact h.congr (Eventually.of_forall fun t ↦ by simp)

/-! ### The projective hypothesis and smooth bumps -/

/-- Projective agreement of the two Laplace families over `C_c^∞`, with
scalar `C`. -/
def ProjectiveAgreement (L₁ L₂ : (ι → ℝ) → ℝ) (C : ℝ → ℝ) : Prop :=
  ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
      - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))

/-- A smooth bump at `p` with inner radius `r/4` and outer radius `r/2`. -/
noncomputable def gapBump (p : ι → ℝ) {r : ℝ} (hr : 0 < r) : ContDiffBump p where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem gapBump_tsupport_subset (p : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    tsupport (gapBump p hr) ⊆ Metric.ball p r := by
  rw [ContDiffBump.tsupport_eq]
  exact Metric.closedBall_subset_ball (by simp [gapBump]; linarith)

/-- A continuous `L` with `L p > 0` is bounded below by `L p / 2` on the
support of a small bump at `p`. -/
theorem exists_gapBump_of_pos {L : (ι → ℝ) → ℝ} (hLc : Continuous L) {p : ι → ℝ}
    (hp : 0 < L p) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∀ w ∈ tsupport (gapBump p hr), L p / 2 ≤ L w := by
  have hev : ∀ᶠ w in 𝓝 p, L p / 2 < L w :=
    hLc.continuousAt.eventually (lt_mem_nhds (half_lt_self hp))
  obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr, fun w hw ↦ ?_⟩
  have hw' := gapBump_tsupport_subset p hr hw
  exact (hrball (Metric.mem_ball.mp hw')).le

/-! ### Scalar tameness -/

/-- **Polynomial upper bound on the scalar** from a zero of `L₁`:
`|C(t)| ≤ A t^d` eventually. -/
theorem exists_scalar_upper_bound {L₁ L₂ : (ι → ℝ) → ℝ}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {p : ι → ℝ} (hp : L₁ p = 0) (hC1 : ContDiffAt ℝ 2 L₁ p)
    {C : ℝ → ℝ} (hfam : ProjectiveAgreement L₁ L₂ C) :
    ∃ A : ℝ, ∀ᶠ t in atTop, |C t| ≤ A * t ^ (Fintype.card ι) := by
  set f : ContDiffBump p := gapBump p one_pos
  obtain ⟨κ, hκ, hlow⟩ := anchor_lower_bound_eventually hL1c hL1 hp hC1
    f.continuous f.hasCompactSupport f.nonneg' f.eventuallyEq_one
  have hR := hfam f f.contDiff f.hasCompactSupport
  obtain ⟨M, hM⟩ := isBigO_iff.mp
    (laplace_moment_bounded f.continuous f.hasCompactSupport hL2c hL2)
  have hR1 : ∀ᶠ t in atTop, |(∫ w, f w * Real.exp (-(t * L₂ w))) -
      C t * ∫ w, f w * Real.exp (-(t * L₁ w))| ≤ 1 := by
    have := isLittleO_iff.mp (hR 0) one_pos
    filter_upwards [this] with t ht
    simpa using ht
  refine ⟨(M + 1) / κ, ?_⟩
  filter_upwards [hlow, hM, hR1, eventually_gt_atTop (0 : ℝ)] with t hlow_t hM_t hR_t htpos
  set I₁ := ∫ w, f w * Real.exp (-(t * L₁ w)) with hI₁
  set I₂ := ∫ w, f w * Real.exp (-(t * L₂ w)) with hI₂
  have htd : 0 < t ^ (-(Fintype.card ι : ℝ)) := Real.rpow_pos_of_pos htpos _
  have hI₁pos : 0 < I₁ := lt_of_lt_of_le (by positivity) hlow_t
  have hM_t' : |I₂| ≤ M := by simpa using hM_t
  have hCI : |C t| * I₁ ≤ M + 1 := by
    calc |C t| * I₁ = |C t * I₁| := by rw [abs_mul, abs_of_pos hI₁pos]
      _ = |I₂ - (I₂ - C t * I₁)| := by ring_nf
      _ ≤ |I₂| + |I₂ - C t * I₁| := abs_sub _ _
      _ ≤ M + 1 := add_le_add hM_t' hR_t
  have key : |C t| * (κ * t ^ (-(Fintype.card ι : ℝ))) ≤ M + 1 :=
    le_trans (mul_le_mul_of_nonneg_left hlow_t (abs_nonneg _)) hCI
  have hrpow : t ^ (-(Fintype.card ι : ℝ)) * t ^ (Fintype.card ι) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
    simp
  have hunit : κ * t ^ (-(Fintype.card ι : ℝ)) * (t ^ (Fintype.card ι) / κ) = 1 := by
    calc κ * t ^ (-(Fintype.card ι : ℝ)) * (t ^ (Fintype.card ι) / κ)
        = (t ^ (-(Fintype.card ι : ℝ)) * t ^ (Fintype.card ι)) * (κ / κ) := by ring
      _ = 1 := by rw [hrpow, div_self hκ.ne', mul_one]
  have hfrac : 0 ≤ t ^ (Fintype.card ι) / κ := by positivity
  calc |C t| = |C t| * (κ * t ^ (-(Fintype.card ι : ℝ)) * (t ^ (Fintype.card ι) / κ)) := by
        rw [hunit, mul_one]
    _ = |C t| * (κ * t ^ (-(Fintype.card ι : ℝ))) * (t ^ (Fintype.card ι) / κ) := by ring
    _ ≤ (M + 1) * (t ^ (Fintype.card ι) / κ) := mul_le_mul_of_nonneg_right key hfrac
    _ = (M + 1) / κ * t ^ (Fintype.card ι) := by ring

/-- **Polynomial lower bound and eventual positivity of the scalar** from
a zero of `L₂`: `c t^{-d} ≤ C(t)` eventually. -/
theorem eventually_scalar_lower_bound {L₁ L₂ : (ι → ℝ) → ℝ}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {q : ι → ℝ} (hq : L₂ q = 0) (hC2 : ContDiffAt ℝ 2 L₂ q)
    {C : ℝ → ℝ} (hfam : ProjectiveAgreement L₁ L₂ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t in atTop, c * t ^ (-(Fintype.card ι : ℝ)) ≤ C t := by
  set f : ContDiffBump q := gapBump q one_pos
  obtain ⟨κ, hκ, hlow⟩ := anchor_lower_bound_eventually hL2c hL2 hq hC2
    f.continuous f.hasCompactSupport f.nonneg' f.eventuallyEq_one
  have hR := hfam f f.contDiff f.hasCompactSupport
  obtain ⟨M, hM⟩ := isBigO_iff.mp
    (laplace_moment_bounded f.continuous f.hasCompactSupport hL1c hL1)
  set M' : ℝ := max M 1 with hM'_def
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRsmall : ∀ᶠ t in atTop, |(∫ w, f w * Real.exp (-(t * L₂ w))) -
      C t * ∫ w, f w * Real.exp (-(t * L₁ w))| ≤
        κ / 2 * t ^ (-(Fintype.card ι : ℝ)) := by
    have := isLittleO_iff.mp (hR (Fintype.card ι)) (half_pos hκ)
    filter_upwards [this, eventually_gt_atTop (0 : ℝ)] with t ht htpos
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos htpos _)] at ht
    exact ht
  refine ⟨κ / 2 / M', by positivity, ?_⟩
  filter_upwards [hlow, hM, hRsmall, eventually_gt_atTop (0 : ℝ)]
    with t hlow_t hM_t hR_t htpos
  set I₁ := ∫ w, f w * Real.exp (-(t * L₁ w)) with hI₁
  set I₂ := ∫ w, f w * Real.exp (-(t * L₂ w)) with hI₂
  have htd : 0 < t ^ (-(Fintype.card ι : ℝ)) := Real.rpow_pos_of_pos htpos _
  have hI₁le : I₁ ≤ M' := by
    have : |I₁| ≤ M := by simpa using hM_t
    exact le_trans (le_abs_self _) (le_trans this (le_max_left _ _))
  have hI₁nonneg : 0 ≤ I₁ :=
    integral_nonneg fun w ↦ mul_nonneg (f.nonneg' w) (Real.exp_nonneg _)
  have hCI : κ / 2 * t ^ (-(Fintype.card ι : ℝ)) ≤ C t * I₁ := by
    have h1 := (abs_le.mp hR_t).2
    linarith
  have hpos : 0 < C t * I₁ := lt_of_lt_of_le (by positivity) hCI
  have hI₁pos : 0 < I₁ := by
    rcases hI₁nonneg.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
  have hCpos : 0 < C t := (mul_pos_iff_of_pos_right hI₁pos).mp hpos
  calc κ / 2 / M' * t ^ (-(Fintype.card ι : ℝ))
      = (κ / 2 * t ^ (-(Fintype.card ι : ℝ))) / M' := by ring
    _ ≤ C t * I₁ / M' := by gcongr
    _ ≤ C t * M' / M' := by gcongr
    _ = C t := by field_simp

/-! ### Equal zero loci -/

/-- **A zero of `L₁` that is not a zero of `L₂` kills the scalar**:
`C` itself is beyond all orders. -/
theorem superPoly_scalar_of_zero_gap {L₁ L₂ : (ι → ℝ) → ℝ}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {p : ι → ℝ} (hp : L₁ p = 0) (hC1 : ContDiffAt ℝ 2 L₁ p) (hne : L₂ p ≠ 0)
    {C : ℝ → ℝ} (hfam : ProjectiveAgreement L₁ L₂ C) :
    SuperPoly C := by
  have hL2p : 0 < L₂ p := lt_of_le_of_ne (hL2 p) (Ne.symm hne)
  obtain ⟨r, hr, hgap⟩ := exists_gapBump_of_pos hL2c hL2p
  set f : ContDiffBump p := gapBump p hr
  have hI2 : SuperPoly fun t ↦ ∫ w, f w * Real.exp (-(t * L₂ w)) :=
    superPoly_integral_mul_exp_of_gap hL2c f.continuous f.hasCompactSupport
      (half_pos hL2p) hgap
  have hR := hfam f f.contDiff f.hasCompactSupport
  have hCI : SuperPoly fun t ↦ C t * ∫ w, f w * Real.exp (-(t * L₁ w)) :=
    (hI2.sub hR).congr (Eventually.of_forall fun t ↦ by ring)
  obtain ⟨κ, hκ, hlow⟩ := anchor_lower_bound_eventually hL1c hL1 hp hC1
    f.continuous f.hasCompactSupport f.nonneg' f.eventuallyEq_one
  have h := superPoly_of_mul_anchor (C := fun t ↦ C t + 1) hκ hlow
    (hCI.congr (Eventually.of_forall fun t ↦ by ring))
  exact h.congr (Eventually.of_forall fun t ↦ by ring)

/-- **Equal zero loci** (projective form, no analyticity): continuous
nonnegative losses, `C²` near their zeros, both with zeros, that agree
projectively have the same zero set. -/
theorem zero_iff_zero_of_projective {L₁ L₂ : (ι → ℝ) → ℝ}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hC1 : ∀ p, L₁ p = 0 → ContDiffAt ℝ 2 L₁ p)
    (hC2 : ∀ q, L₂ q = 0 → ContDiffAt ℝ 2 L₂ q)
    {C : ℝ → ℝ} (hfam : ProjectiveAgreement L₁ L₂ C)
    (hne1 : ∃ p, L₁ p = 0) (hne2 : ∃ q, L₂ q = 0) :
    ∀ w, L₁ w = 0 ↔ L₂ w = 0 := by
  obtain ⟨p₀, hp₀⟩ := hne1
  obtain ⟨q₀, hq₀⟩ := hne2
  intro w
  constructor
  · intro hw
    by_contra hne
    have hC := superPoly_scalar_of_zero_gap hL1c hL2c hL1 hL2 hw (hC1 w hw) hne hfam
    set f : ContDiffBump q₀ := gapBump q₀ one_pos
    have hR := hfam f f.contDiff f.hasCompactSupport
    have hI1 := laplace_moment_bounded f.continuous f.hasCompactSupport hL1c hL1
    have hI2 : SuperPoly fun t ↦ ∫ w, f w * Real.exp (-(t * L₂ w)) :=
      (hR.add (hC.bounded_mul hI1)).congr (Eventually.of_forall fun t ↦ by ring)
    exact not_superPoly_integral_exp_near_zero hL2c hL2 hq₀ (hC2 q₀ hq₀)
      f.continuous f.hasCompactSupport f.nonneg' f.eventuallyEq_one hI2
  · intro hw
    by_contra hne
    obtain ⟨A, hA⟩ := exists_scalar_upper_bound hL1c hL2c hL1 hL2 hp₀ (hC1 p₀ hp₀) hfam
    have hL1w : 0 < L₁ w := lt_of_le_of_ne (hL1 w) (Ne.symm hne)
    obtain ⟨r, hr, hgap⟩ := exists_gapBump_of_pos hL1c hL1w
    set f : ContDiffBump w := gapBump w hr
    have hCI1 : SuperPoly fun t ↦ C t * ∫ w, f w * Real.exp (-(t * L₁ w)) :=
      superPoly_polyBounded_mul_integral_of_gap hL1c f.continuous f.hasCompactSupport
        (half_pos hL1w) hgap hA
    have hR := hfam f f.contDiff f.hasCompactSupport
    have hI2 : SuperPoly fun t ↦ ∫ w, f w * Real.exp (-(t * L₂ w)) :=
      (hR.add hCI1).congr (Eventually.of_forall fun t ↦ by ring)
    exact not_superPoly_integral_exp_near_zero hL2c hL2 hw (hC2 w hw)
      f.continuous f.hasCompactSupport f.nonneg' f.eventuallyEq_one hI2

/-! ### Scalar rigidity and the transfer projective ⇒ exact -/

/-- **Scalar rigidity**: if the losses agree near a `C²` zero `p` of
`L₁`, projective agreement forces `C(t) = 1 + o(t^{-∞})`. -/
theorem superPoly_scalar_sub_one_of_eventuallyEq {L₁ L₂ : (ι → ℝ) → ℝ}
    (hL1c : Continuous L₁) (hL1 : ∀ w, 0 ≤ L₁ w)
    {p : ι → ℝ} (hp : L₁ p = 0) (hC1 : ContDiffAt ℝ 2 L₁ p)
    (hEq : ∀ᶠ w in 𝓝 p, L₁ w = L₂ w)
    {C : ℝ → ℝ} (hfam : ProjectiveAgreement L₁ L₂ C) :
    SuperPoly fun t ↦ C t - 1 := by
  obtain ⟨ε, hε, hεEq⟩ := Metric.eventually_nhds_iff.mp hEq
  set f : ContDiffBump p := gapBump p hε
  have hsupp : tsupport f ⊆ Metric.ball p ε := gapBump_tsupport_subset p hε
  have hEqOn : Set.EqOn L₁ L₂ (Metric.ball p ε) :=
    fun y hy ↦ hεEq (Metric.mem_ball.mp hy)
  have hanchor : ∀ t : ℝ, (∫ w, f w * Real.exp (-(t * L₂ w))) =
      ∫ w, f w * Real.exp (-(t * L₁ w)) :=
    fun t ↦ anchor_moment_eq hEqOn hsupp t
  obtain ⟨κ, hκ, hlow⟩ := anchor_lower_bound_eventually hL1c hL1 hp hC1
    f.continuous f.hasCompactSupport f.nonneg' f.eventuallyEq_one
  have hR := hfam f f.contDiff f.hasCompactSupport
  have hflat : SuperPoly fun t ↦ (C t - 1) * ∫ w, f w * Real.exp (-(t * L₁ w)) := by
    have hneg : SuperPoly fun t ↦ -((∫ w, f w * Real.exp (-(t * L₂ w))) -
        C t * ∫ w, f w * Real.exp (-(t * L₁ w))) :=
      fun N ↦ (hR N).neg_left
    refine hneg.congr (Eventually.of_forall fun t ↦ ?_)
    beta_reduce
    rw [hanchor t]
    ring
  exact superPoly_of_mul_anchor hκ hlow hflat

/-- **Transfer, projective ⇒ exact**: under the hypotheses of scalar
rigidity, the two families agree beyond all orders at every tested
observable, with no scalar. -/
theorem superPoly_difference_of_projective {L₁ L₂ : (ι → ℝ) → ℝ}
    (hL1c : Continuous L₁) (hL1 : ∀ w, 0 ≤ L₁ w)
    {p : ι → ℝ} (hp : L₁ p = 0) (hC1 : ContDiffAt ℝ 2 L₁ p)
    (hEq : ∀ᶠ w in 𝓝 p, L₁ w = L₂ w)
    {C : ℝ → ℝ} (hfam : ProjectiveAgreement L₁ L₂ C) :
    ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)) := by
  intro φ hφ hφs
  have hC := superPoly_scalar_sub_one_of_eventuallyEq hL1c hL1 hp hC1 hEq hfam
  exact superPoly_sub_of_scalar_gauge hC
    (laplace_moment_bounded hφ.continuous hφs hL1c hL1) (hfam φ hφ hφs)

/-- **At a common analytic zero, projective agreement fixes its own
gauge**: for smooth nonnegative losses analytic at a common zero `p`,
projective agreement gives `C(t) = 1 + o(t^{-∞})` and exact agreement
of every tested moment beyond all orders. -/
theorem projective_forces_exact_at {L₁ L₂ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p)
    (hp1 : L₁ p = 0) (hp2 : L₂ p = 0)
    {C : ℝ → ℝ} (hfam : ProjectiveAgreement L₁ L₂ C) :
    (SuperPoly fun t ↦ C t - 1) ∧
    ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)) := by
  have hEq : ∀ᶠ w in 𝓝 p, L₁ w = L₂ w :=
    normalized_families_force_germ_eq_at h1 h2 hL1 hL2 hA1 hA2 hp1 hp2 hfam
  exact ⟨superPoly_scalar_sub_one_of_eventuallyEq h1.continuous hL1 hp1
      hA1.contDiffAt hEq hfam,
    superPoly_difference_of_projective h1.continuous hL1 hp1
      hA1.contDiffAt hEq hfam⟩

/-! ### The `1/Z` headline -/

/-- Normalized agreement (common window `χ`, both partition values
positive) implies projective agreement with `C = Z₂/Z₁`. -/
theorem projectiveAgreement_of_normalized {L₁ L₂ χ : (ι → ℝ) → ℝ}
    (hL2 : ∀ w, 0 ≤ L₂ w)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₂ w)))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦
        (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
        - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w)))) :
    ProjectiveAgreement L₁ L₂ fun t ↦
      (∫ w, χ w * Real.exp (-(t * L₂ w))) / ∫ w, χ w * Real.exp (-(t * L₁ w)) := by
  set Z₁ : ℝ → ℝ := fun t ↦ ∫ w, χ w * Real.exp (-(t * L₁ w)) with hZ₁_def
  set Z₂ : ℝ → ℝ := fun t ↦ ∫ w, χ w * Real.exp (-(t * L₂ w)) with hZ₂_def
  have hχint : Integrable χ := hχc.integrable_of_hasCompactSupport hχs
  have hZ₂le : ∀ t : ℝ, 0 ≤ t → Z₂ t ≤ ∫ w, χ w := by
    intro t ht
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun w ↦ mul_nonneg (hχ0 w) (Real.exp_nonneg _)
    · exact hχint
    · refine Eventually.of_forall fun w ↦ ?_
      have : Real.exp (-(t * L₂ w)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg ht (hL2 w))
      calc χ w * Real.exp (-(t * L₂ w)) ≤ χ w * 1 :=
            mul_le_mul_of_nonneg_left this (hχ0 w)
        _ = χ w := mul_one _
  have hZ₂O : Z₂ =O[atTop] fun _ : ℝ ↦ (1 : ℝ) := by
    refine IsBigO.of_bound (∫ w, χ w) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (hZ2 t), norm_one, mul_one]
    exact hZ₂le t ht
  intro φ hφ hφs
  have hφ' := (hfam φ hφ hφs).bounded_mul hZ₂O
  refine hφ'.congr (Eventually.of_forall fun t ↦ ?_)
  have h1t : Z₁ t ≠ 0 := (hZ1 t).ne'
  have h2t : Z₂ t ≠ 0 := (hZ2 t).ne'
  simp only [hZ₁_def, hZ₂_def] at h1t h2t ⊢
  field_simp

/-- **The `1/Z` closure.** For smooth nonnegative losses analytic at their
zeros, both with zeros, equality of the normalized expansions
`Φ_{L₁} = Φ_{L₂}` (common window, both partition values positive) gives:
equal zero sets; `L₁ = L₂` on an open neighbourhood of the zero set;
`Z₂/Z₁ = 1 + o(t^{-∞})`; and exact agreement of every tested moment
beyond all orders. -/
theorem normalized_expectations_closure {L₁ L₂ χ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p, L₁ p = 0 → AnalyticAt ℝ L₁ p) (hA2 : ∀ p, L₂ p = 0 → AnalyticAt ℝ L₂ p)
    (hne1 : ∃ p, L₁ p = 0) (hne2 : ∃ q, L₂ q = 0)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₂ w)))
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦
        (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
        - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w)))) :
    (∀ w, L₁ w = 0 ↔ L₂ w = 0) ∧
    (∃ U : Set (ι → ℝ), IsOpen U ∧ {w | L₁ w = 0} ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w) ∧
    (SuperPoly fun t ↦
      (∫ w, χ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))) - 1) ∧
    ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)) := by
  have hproj := projectiveAgreement_of_normalized hL2 hχc hχs hχ0 hZ1 hZ2 hfam
  have hzero := zero_iff_zero_of_projective h1.continuous h2.continuous hL1 hL2
    (fun p hp ↦ (hA1 p hp).contDiffAt) (fun q hq ↦ (hA2 q hq).contDiffAt)
    hproj hne1 hne2
  obtain ⟨U, hUo, hUsub, hUeq⟩ := normalized_families_force_eq_near h1 h2 hL1 hL2
    (W₀ := {w | L₁ w = 0}) (fun p hp ↦ hA1 p hp) (fun p hp ↦ hA2 p ((hzero p).mp hp))
    (fun p hp ↦ hp) (fun p hp ↦ (hzero p).mp hp) hproj
  obtain ⟨p₀, hp₀⟩ := hne1
  have hEq : ∀ᶠ w in 𝓝 p₀, L₁ w = L₂ w :=
    (hUo.eventually_mem (hUsub hp₀)).mono fun w hw ↦ hUeq w hw
  refine ⟨hzero, ⟨U, hUo, hUsub, hUeq⟩, ?_, ?_⟩
  · exact superPoly_scalar_sub_one_of_eventuallyEq h1.continuous hL1 hp₀
      (hA1 p₀ hp₀).contDiffAt hEq hproj
  · exact superPoly_difference_of_projective h1.continuous hL1 hp₀
      (hA1 p₀ hp₀).contDiffAt hEq hproj

end Laplace
