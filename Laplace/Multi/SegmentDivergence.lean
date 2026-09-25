/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NaturalCoordinates

/-!
# Divergences along a data segment: the two anchor identities, Jeffreys, and Pythagoras

For the affine family `L_a = L₀ + ∑ aᵢRᵢ` at temperature `t`, along the segment `a + s(b − a)` with
`V(s) = Var_{a+s(b−a)}(R_{b−a})`:

* **the two segment identities** `KL(P_b ‖ P_a) = t² ∫₀¹ s V(s) ds` and
  `KL(P_a ‖ P_b) = t² ∫₀¹ (1 − s) V(s) ds` (`mixKL_eq_integral_mul_var`,
  `mixKL_eq_integral_one_sub_mul_var`): both divergences are weighted integrals of the response form
  along the segment (Taylor's formula with integral remainder for the free energy);
* **the Jeffreys bound** `Length² ≤ KL(P_a ‖ P_b) + KL(P_b ‖ P_a)` for the response length
  `t ∫₀¹ √V` of the segment (`sq_segmentLength_le_jeffreys`; the one-sided bound `L² ≤ 2 KL` is
  false);
* **the three-point identity** `KL(a‖b) − KL(a‖c) − KL(c‖b) = t ⟨b − c, m(a) − m(c)⟩`
  (`mixKL_three_point`) and the **generalised Pythagoras theorem** under orthogonality
  (`mixKL_pythagoras`), with orthogonality supplied by the first-order condition of an information
  projection onto an affine subfamily (`orthogonal_of_isMinOn_line`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- `(∫₀¹ √f)² ≤ ∫₀¹ f` for a continuous nonnegative `f` (Cauchy–Schwarz on `[0,1]`). -/
theorem sq_integral_sqrt_le_integral {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ s, 0 ≤ f s) :
    (∫ s in (0 : ℝ)..1, Real.sqrt (f s)) ^ 2 ≤ ∫ s in (0 : ℝ)..1, f s := by
  have hI : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable 0 1
  have hIs : IntervalIntegrable (fun s ↦ Real.sqrt (f s)) volume 0 1 :=
    (Real.continuous_sqrt.comp hf).intervalIntegrable 0 1
  have hV0 : 0 ≤ ∫ s in (0 : ℝ)..1, f s :=
    intervalIntegral.integral_nonneg zero_le_one fun s _ ↦ hf0 s
  have hS0 : 0 ≤ ∫ s in (0 : ℝ)..1, Real.sqrt (f s) :=
    intervalIntegral.integral_nonneg zero_le_one fun s _ ↦ Real.sqrt_nonneg _
  -- AM–GM with a free weight: `√f ≤ (λ + f/λ)/2`
  have key : ∀ lam : ℝ, 0 < lam →
      ∫ s in (0 : ℝ)..1, Real.sqrt (f s) ≤ (lam + (∫ s in (0 : ℝ)..1, f s) / lam) / 2 := by
    intro lam hlam
    have hpt : ∀ s, Real.sqrt (f s) ≤ (lam + f s / lam) / 2 := fun s ↦ by
      have hsq : Real.sqrt (f s) ^ 2 = f s := Real.sq_sqrt (hf0 s)
      have key : 2 * lam * Real.sqrt (f s) ≤ lam ^ 2 + f s := by
        nlinarith [sq_nonneg (Real.sqrt (f s) - lam)]
      have e : (lam + f s / lam) / 2 - Real.sqrt (f s) =
          (lam ^ 2 + f s - 2 * lam * Real.sqrt (f s)) / (2 * lam) := by
        field_simp
      have : 0 ≤ (lam + f s / lam) / 2 - Real.sqrt (f s) := by
        rw [e]; exact div_nonneg (by linarith) (by positivity)
      linarith
    calc ∫ s in (0 : ℝ)..1, Real.sqrt (f s) ≤ ∫ s in (0 : ℝ)..1, (lam + f s / lam) / 2 :=
          intervalIntegral.integral_mono_on zero_le_one hIs
            ((intervalIntegrable_const.add (hI.div_const lam)).div_const 2) fun s _ ↦ hpt s
      _ = (lam + (∫ s in (0 : ℝ)..1, f s) / lam) / 2 := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_add
            intervalIntegrable_const (hI.div_const lam), intervalIntegral.integral_div]
          simp
  -- choose `λ = √(∫ f + ε)` and let `ε → 0`
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hlam : 0 < Real.sqrt ((∫ s in (0 : ℝ)..1, f s) + ε) := Real.sqrt_pos.2 (by linarith)
  have h := key _ hlam
  have hsq : Real.sqrt ((∫ s in (0 : ℝ)..1, f s) + ε) ^ 2 = (∫ s in (0 : ℝ)..1, f s) + ε :=
    Real.sq_sqrt (by linarith)
  have hle : ∫ s in (0 : ℝ)..1, Real.sqrt (f s) ≤ Real.sqrt ((∫ s in (0 : ℝ)..1, f s) + ε) := by
    refine h.trans ?_
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), add_div' _ _ _ hlam.ne', div_le_iff₀ hlam]
    nlinarith
  calc (∫ s in (0 : ℝ)..1, Real.sqrt (f s)) ^ 2
      ≤ Real.sqrt ((∫ s in (0 : ℝ)..1, f s) + ε) ^ 2 := pow_le_pow_left₀ hS0 hle 2
    _ = (∫ s in (0 : ℝ)..1, f s) + ε := hsq

section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]
variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- The response variance along a segment, `V(s) = Var_{a+sv}(R_v)`. -/
noncomputable def segVar (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a v : ι → ℝ)
    (s : ℝ) : ℝ :=
  priorCov μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) (dirLoss R v) t

/-- The line derivative of the mean contrast: `d/ds ⟨R_v⟩_{a+sv} = −t V(s)`. -/
theorem hasDerivAt_segMean (a v : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) t)
      (-t * segVar μ π L₀ R t a v s) s := by
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  have h := (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht
    (a + s • v)).comp_hasDerivAt s (hasDerivAt_affineLine a v s)
  refine h.congr_deriv ?_
  exact obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht (a + s • v) v

theorem continuous_segVar (a v : ι → ℝ) : Continuous (segVar μ π L₀ R t a v) := by
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  have hlc : Continuous (fun s : ℝ ↦ a + s • v) :=
    continuous_const.add ((continuous_id : Continuous fun s : ℝ ↦ s).smul
      (continuous_const : Continuous fun _ : ℝ ↦ v))
  have hcont : Continuous (fun s ↦ obsMapDeriv μ π L₀ (dirLoss R v) R t (a + s • v) v) :=
    ((continuous_obsMapDeriv hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht).comp hlc).clm_apply
      continuous_const
  have e : segVar μ π L₀ R t a v = fun s ↦
      -(1 / t) * obsMapDeriv μ π L₀ (dirLoss R v) R t (a + s • v) v := by
    funext s
    rw [obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht (a + s • v) v]
    unfold segVar
    field_simp
  rw [e]
  exact hcont.const_mul _

omit ht in
theorem segVar_nonneg (a v : ι → ℝ) (s : ℝ) : 0 ≤ segVar μ π L₀ R t a v s :=
  priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (a + s • v) (bdd_dirLoss hR v)

/-- **Forward segment identity**: `KL(P_b ‖ P_a) = t² ∫₀¹ s V(s) ds`. -/
theorem mixKL_eq_integral_mul_var (a b : ι → ℝ) :
    mixKL μ π (affLoss L₀ R b) (dirLoss R (a - b)) t 0 1 =
      t ^ 2 * ∫ s in (0 : ℝ)..1, s * segVar μ π L₀ R t a (b - a) s := by
  set v := b - a with hv
  have hD := hasDerivAt_segMean hπm hπi hπ hπpos hL₀m hL₀ hR ht a v
  have hψ := hasDerivAt_affLogZ_line hπm hπi hπ hπpos hL₀m hL₀ hR t a v
  -- primitive `g(s) = A(a) − A(a+sv) − t s D(s)`
  have hg : ∀ s, HasDerivAt (fun s ↦ affLogZ μ π L₀ R t a - affLogZ μ π L₀ R t (a + s • v) -
      t * (s * priorExp μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) t))
      (t ^ 2 * (s * segVar μ π L₀ R t a v s)) s := fun s ↦ by
    have h := ((hasDerivAt_const s (affLogZ μ π L₀ R t a)).sub (hψ s)).sub
      (((hasDerivAt_id s).mul (hD s)).const_mul t)
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hcont : Continuous (fun s ↦ t ^ 2 * (s * segVar μ π L₀ R t a v s)) :=
    (continuous_id.mul (continuous_segVar hπm hπi hπ hπpos hL₀m hL₀ hR ht a v)).const_mul _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hg s)
    (hcont.intervalIntegrable (μ := volume) 0 1)
  rw [intervalIntegral.integral_const_mul] at hftc
  rw [hftc, mixKL_aff_eq hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR t b a,
    priorExp_dirLoss_eq_dot hπm hπi hπ hπpos hL₀m hL₀ hR t (a + 1 • v) v]
  simp only [one_smul, zero_smul, add_zero, zero_mul, mul_zero, sub_zero, hv, add_sub_cancel]
  simp only [mul_sub, Finset.sum_sub_distrib, Pi.sub_apply, sub_mul, Finset.mul_sum]
  ring

/-- **Reverse segment identity**: `KL(P_a ‖ P_b) = t² ∫₀¹ (1 − s) V(s) ds`. -/
theorem mixKL_eq_integral_one_sub_mul_var (a b : ι → ℝ) :
    mixKL μ π (affLoss L₀ R a) (dirLoss R (b - a)) t 0 1 =
      t ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * segVar μ π L₀ R t a (b - a) s := by
  set v := b - a with hv
  have hD := hasDerivAt_segMean hπm hπi hπ hπpos hL₀m hL₀ hR ht a v
  have hψ := hasDerivAt_affLogZ_line hπm hπi hπ hπpos hL₀m hL₀ hR t a v
  -- primitive `g(s) = A(a+sv) − A(a) − t (1 − s) D(s) + t D(0)`
  have hg : ∀ s, HasDerivAt (fun s ↦ affLogZ μ π L₀ R t (a + s • v) - affLogZ μ π L₀ R t a -
      t * ((1 - s) * priorExp μ π (affLoss L₀ R (a + s • v)) (dirLoss R v) t) +
      t * priorExp μ π (affLoss L₀ R (a + 0 • v)) (dirLoss R v) t)
      (t ^ 2 * ((1 - s) * segVar μ π L₀ R t a v s)) s := fun s ↦ by
    have h := (((hψ s).sub (hasDerivAt_const s (affLogZ μ π L₀ R t a))).sub
      ((((hasDerivAt_id s).const_sub 1).mul (hD s)).const_mul t)).add
      (hasDerivAt_const s (t * priorExp μ π (affLoss L₀ R (a + 0 • v)) (dirLoss R v) t))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hcont : Continuous (fun s ↦ t ^ 2 * ((1 - s) * segVar μ π L₀ R t a v s)) :=
    ((continuous_const.sub continuous_id).mul
      (continuous_segVar hπm hπi hπ hπpos hL₀m hL₀ hR ht a v)).const_mul _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hg s)
    (hcont.intervalIntegrable (μ := volume) 0 1)
  rw [intervalIntegral.integral_const_mul] at hftc
  rw [hftc, mixKL_aff_eq hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR t a b]
  simp only [one_smul, zero_smul, add_zero, sub_self, zero_mul, mul_zero, sub_zero, hv,
    add_sub_cancel]
  rw [priorExp_dirLoss_eq_dot hπm hπi hπ hπpos hL₀m hL₀ hR t a (b - a)]
  simp only [Finset.mul_sum, Pi.sub_apply]
  ring

/-- The response length of a data segment, `t ∫₀¹ √V(s) ds`. -/
noncomputable def segmentLength (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a b : ι → ℝ) : ℝ :=
  t * ∫ s in (0 : ℝ)..1, Real.sqrt (segVar μ π L₀ R t a (b - a) s)

/-- **The Jeffreys bound**: `Length(a,b)² ≤ KL(P_a ‖ P_b) + KL(P_b ‖ P_a)`. -/
theorem sq_segmentLength_le_jeffreys (a b : ι → ℝ) :
    segmentLength μ π L₀ R t a b ^ 2 ≤
      mixKL μ π (affLoss L₀ R a) (dirLoss R (b - a)) t 0 1 +
        mixKL μ π (affLoss L₀ R b) (dirLoss R (a - b)) t 0 1 := by
  rw [mixKL_eq_integral_one_sub_mul_var hπm hπi hπ hπpos hL₀m hL₀ hR ht a b,
    mixKL_eq_integral_mul_var hπm hπi hπ hπpos hL₀m hL₀ hR ht a b]
  have hc := continuous_segVar hπm hπi hπ hπpos hL₀m hL₀ hR ht a (b - a)
  have hI : IntervalIntegrable (segVar μ π L₀ R t a (b - a)) volume 0 1 :=
    hc.intervalIntegrable 0 1
  have hsum : (∫ s in (0 : ℝ)..1, (1 - s) * segVar μ π L₀ R t a (b - a) s) +
      ∫ s in (0 : ℝ)..1, s * segVar μ π L₀ R t a (b - a) s =
      ∫ s in (0 : ℝ)..1, segVar μ π L₀ R t a (b - a) s := by
    have h1 : IntervalIntegrable (fun s ↦ (1 - s) * segVar μ π L₀ R t a (b - a) s) volume 0 1 :=
      ((continuous_const.sub continuous_id).mul hc).intervalIntegrable 0 1
    have h2 : IntervalIntegrable (fun s ↦ s * segVar μ π L₀ R t a (b - a) s) volume 0 1 :=
      (continuous_id.mul hc).intervalIntegrable 0 1
    rw [← intervalIntegral.integral_add h1 h2]
    exact intervalIntegral.integral_congr fun s _ ↦ by ring
  have hcs := sq_integral_sqrt_le_integral hc
    (segVar_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR a (b - a))
  unfold segmentLength
  rw [mul_pow, ← mul_add, hsum]
  exact mul_le_mul_of_nonneg_left hcs (by positivity)

omit ht in
/-- **The three-point identity**:
`KL(a‖b) − KL(a‖c) − KL(c‖b) = t ⟨b − c, m(a) − m(c)⟩`. -/
theorem mixKL_three_point (a b c : ι → ℝ) :
    mixKL μ π (affLoss L₀ R a) (dirLoss R (b - a)) t 0 1 -
      mixKL μ π (affLoss L₀ R a) (dirLoss R (c - a)) t 0 1 -
      mixKL μ π (affLoss L₀ R c) (dirLoss R (b - c)) t 0 1 =
      t * ∑ i, (b i - c i) * (meanMap μ π L₀ R t a i - meanMap μ π L₀ R t c i) := by
  have hπ' : ∀ x, 0 ≤ π x := fun x ↦ (hπ x).le
  rw [mixKL_aff_eq hπm hπi hπ' hπpos hL₀m hL₀ hR t a b, mixKL_aff_eq hπm hπi hπ' hπpos hL₀m hL₀ hR
    t a c, mixKL_aff_eq hπm hπi hπ' hπpos hL₀m hL₀ hR t c b]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

omit ht in
/-- **Generalised Pythagoras**: if `m(a) − m(c) ⊥ b − c` then
`KL(a‖b) = KL(a‖c) + KL(c‖b)`. -/
theorem mixKL_pythagoras (a b c : ι → ℝ)
    (horth : ∑ i, (b i - c i) * (meanMap μ π L₀ R t a i - meanMap μ π L₀ R t c i) = 0) :
    mixKL μ π (affLoss L₀ R a) (dirLoss R (b - a)) t 0 1 =
      mixKL μ π (affLoss L₀ R a) (dirLoss R (c - a)) t 0 1 +
        mixKL μ π (affLoss L₀ R c) (dirLoss R (b - c)) t 0 1 := by
  have h := mixKL_three_point hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a b c
  rw [horth, mul_zero] at h
  linarith

omit ht in
/-- The line derivative of `ζ ↦ KL(P_a ‖ P_ζ)` along `c + s v` is `t ⟨v, m(c + sv) − m(a)⟩`. -/
theorem hasDerivAt_mixKL_line (a c v : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ mixKL μ π (affLoss L₀ R a) (dirLoss R (c + s • v - a)) t 0 1)
      (t * ∑ i, v i * (meanMap μ π L₀ R t a i - meanMap μ π L₀ R t (c + s • v) i)) s := by
  have hπ' : ∀ x, 0 ≤ π x := fun x ↦ (hπ x).le
  have e : (fun s : ℝ ↦ mixKL μ π (affLoss L₀ R a) (dirLoss R (c + s • v - a)) t 0 1) =
      fun s ↦ affLogZ μ π L₀ R t (c + s • v) - affLogZ μ π L₀ R t a +
        t * ∑ i, (c i + s * v i - a i) * meanMap μ π L₀ R t a i := by
    funext s
    rw [mixKL_aff_eq hπm hπi hπ' hπpos hL₀m hL₀ hR t a (c + s • v)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  have hψ := hasDerivAt_affLogZ_line hπm hπi hπ hπpos hL₀m hL₀ hR t c v s
  have hlin : HasDerivAt (fun s ↦ t * ∑ i, (c i + s * v i - a i) * meanMap μ π L₀ R t a i)
      (t * ∑ i, v i * meanMap μ π L₀ R t a i) s := by
    have e2 : (fun s ↦ t * ∑ i, (c i + s * v i - a i) * meanMap μ π L₀ R t a i) = fun s ↦
        t * ∑ i, (c i - a i) * meanMap μ π L₀ R t a i +
          s * (t * ∑ i, v i * meanMap μ π L₀ R t a i) := by
      funext s
      simp only [Finset.mul_sum, mul_add, mul_sub, sub_mul, add_mul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      ring
    rw [e2]
    simpa using ((hasDerivAt_id s).mul_const (t * ∑ i, v i * meanMap μ π L₀ R t a i)).const_add
      (t * ∑ i, (c i - a i) * meanMap μ π L₀ R t a i)
  have h := ((hψ).sub (hasDerivAt_const s (affLogZ μ π L₀ R t a))).add hlin
  refine h.congr_deriv ?_
  rw [priorExp_dirLoss_eq_dot hπm hπi hπ hπpos hL₀m hL₀ hR t (c + s • v) v]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **Orthogonality at an information projection**: if `c` minimises `KL(P_a ‖ P_·)` along the line
`c + s v`, then `⟨v, m(a) − m(c)⟩ = 0`. -/
theorem orthogonal_of_isMinOn_line (a c v : ι → ℝ)
    (hmin : ∀ s : ℝ, mixKL μ π (affLoss L₀ R a) (dirLoss R (c - a)) t 0 1 ≤
      mixKL μ π (affLoss L₀ R a) (dirLoss R (c + s • v - a)) t 0 1) :
    ∑ i, v i * (meanMap μ π L₀ R t a i - meanMap μ π L₀ R t c i) = 0 := by
  have hd := hasDerivAt_mixKL_line hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a c v 0
  have hloc : IsLocalMin
      (fun s : ℝ ↦ mixKL μ π (affLoss L₀ R a) (dirLoss R (c + s • v - a)) t 0 1) 0 := by
    refine Filter.Eventually.of_forall fun s ↦ ?_
    simp only [zero_smul, add_zero]
    exact hmin s
  have h0 := hloc.hasDerivAt_eq_zero hd
  simp only [zero_smul, add_zero] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h ht.ne'
  · exact h

end

end Laplace.Multi
