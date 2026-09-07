/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CircleOpParam

/-!
# Cauchy coefficients on a polydisc: bound and reconstruction (Stage 7d — the gate)

Unit 263 (Astra #31 route R2, units 3/6/7 of the tranche). The **several-variable Cauchy
coefficients** `c_γ = A_r^{[d]}(w ↦ F w ∏ᵢ wᵢ^{-γᵢ})` (`polyCoeff`) satisfy the **Cauchy estimate**
`‖c_γ‖ ≤ M r^{-|γ|}` with `M` a bound of `‖F‖` on the **torus** only (`norm_polyCoeff_le`, no
holomorphy needed there — Lean's totalised contour integrals), and the
**reconstruction** `∑_γ c_γ z^γ = F z` as a `HasSum` on the open polydisc (`hasSum_polyCoeff`), for
`F ∈ SliceHolo d r` bounded on the **closed polydisc** (a stronger hypothesis than the torus bound,
supplied in unit 264 by compactness inside a larger open polydisc). The induction extracts the
first coordinate with the one-variable `HasSum` (unit 260), expands the tail by the induction
hypothesis on the circle, interchanges the circle operator with the tail series under the
product-geometric majorant (unit 262), and regroups the double series along `Fin.cons`.
Consequences: `∑_γ ‖c_γ‖ b^{|γ|} < ∞` for
every `b < r` (`summable_norm_polyCoeff_mul_pow`) — the weighted-mass hypothesis of the
coefficient-family Taylor tree. This is the quantitative reconstruction gate of Astra #31.
No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

/-- The several-variable Cauchy coefficients `c_γ = A_r^{[d]}(w ↦ F w ∏ᵢ wᵢ^{-γᵢ})`. -/
noncomputable def polyCoeff (d : ℕ) (r : ℝ) (F : (Fin d → ℂ) → ℂ) (γ : Fin d → ℕ) : ℂ :=
  iterOp d r fun w => F w * ∏ i, (w i)⁻¹ ^ γ i

/-- **Cauchy estimate**: `‖c_γ‖ ≤ M r^{-|γ|}` if `‖F‖ ≤ M` on the torus. -/
theorem norm_polyCoeff_le {d : ℕ} {r M : ℝ} (hr : 0 < r) {F : (Fin d → ℂ) → ℂ}
    (hF : ∀ w ∈ torusSet d r, ‖F w‖ ≤ M) (γ : Fin d → ℕ) :
    ‖polyCoeff d r F γ‖ ≤ M * r⁻¹ ^ (∑ i, γ i) := by
  unfold polyCoeff
  refine norm_iterOp_le d hr fun w hw => ?_
  have hw' := mem_torusSet.1 hw
  rw [norm_mul, norm_prod]
  have : ∏ i, ‖(w i)⁻¹ ^ γ i‖ = r⁻¹ ^ (∑ i, γ i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => by rw [norm_pow, norm_inv, hw' i]
  rw [this]
  exact mul_le_mul_of_nonneg_right (hF w hw) (by positivity)

/-- The coefficient of `(n :: γ')` is the first-coordinate extraction of the tail coefficients. -/
theorem polyCoeff_cons {d : ℕ} (r : ℝ) (F : (Fin (d + 1) → ℂ) → ℂ) (n : ℕ) (γ' : Fin d → ℕ) :
    polyCoeff (d + 1) r F (Fin.cons n γ') =
      circleOp r fun w => w⁻¹ ^ n * polyCoeff d r (fun w' => F (Fin.cons w w')) γ' := by
  unfold polyCoeff
  simp only [iterOp]
  congr 1
  funext w
  rw [← iterOp_const_mul]
  congr 1
  funext w'
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem norm_polyCoeff_mul_pow_le {d : ℕ} {r M : ℝ} (hr : 0 < r) {F : (Fin d → ℂ) → ℂ}
    (hF : ∀ w ∈ torusSet d r, ‖F w‖ ≤ M) (γ : Fin d → ℕ) (z : Fin d → ℂ) :
    ‖polyCoeff d r F γ * ∏ i, z i ^ γ i‖ ≤ M * ∏ i, (‖z i‖ / r) ^ γ i := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF (fun _ => (r : ℂ)) (by
    rw [mem_torusSet]; intro i; simp [abs_of_pos hr]))
  rw [norm_mul, norm_prod]
  simp only [norm_pow]
  calc ‖polyCoeff d r F γ‖ * ∏ i, ‖z i‖ ^ γ i ≤ M * r⁻¹ ^ (∑ i, γ i) * ∏ i, ‖z i‖ ^ γ i :=
        mul_le_mul_of_nonneg_right (norm_polyCoeff_le hr hF γ) (by positivity)
    _ = M * ∏ i, (‖z i‖ / r) ^ γ i := by
        rw [← Finset.prod_pow_eq_pow_sum, mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        exact Finset.prod_congr rfl fun i _ => by rw [div_eq_mul_inv, mul_pow, mul_comm]

/-- Absolute summability of `c_γ z^γ` on the open polydisc. -/
theorem summable_norm_polyCoeff_mul_pow {d : ℕ} {r M : ℝ} (hr : 0 < r) {F : (Fin d → ℂ) → ℂ}
    (hF : ∀ w ∈ torusSet d r, ‖F w‖ ≤ M) {z : Fin d → ℂ} (hz : z ∈ openPolydisc d r) :
    Summable fun γ : Fin d → ℕ => ‖polyCoeff d r F γ * ∏ i, z i ^ γ i‖ := by
  have hz' := mem_openPolydisc.1 hz
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_polyCoeff_mul_pow_le hr hF · z)
    ((summable_prodGeom d (q := fun i => ‖z i‖ / r) (fun i => by positivity)
      (fun i => (div_lt_one hr).2 (hz' i))).mul_left M)

/-- **Reconstruction**: `∑_γ c_γ z^γ = F z` on the open polydisc, as a `HasSum`. -/
theorem hasSum_polyCoeff : ∀ (d : ℕ) {r M : ℝ}, 0 < r → ∀ {F : (Fin d → ℂ) → ℂ}, SliceHolo d r F →
    (∀ w ∈ closedPolydisc d r, ‖F w‖ ≤ M) → ∀ {z : Fin d → ℂ}, z ∈ openPolydisc d r →
      HasSum (fun γ : Fin d → ℕ => polyCoeff d r F γ * ∏ i, z i ^ γ i) (F z)
  | 0, r, M, _, F, _, _, z, _ => by
    have hval : ∀ γ : Fin 0 → ℕ, polyCoeff 0 r F γ * ∏ i, z i ^ γ i = F z := by
      intro γ
      simp only [polyCoeff, iterOp, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      congr 1
      exact Subsingleton.elim _ _
    have h := hasSum_fintype fun γ : Fin 0 → ℕ => polyCoeff 0 r F γ * ∏ i, z i ^ γ i
    rwa [Fintype.sum_unique, hval] at h
  | d + 1, r, M, hr, F, hF, hM, z, hz => by
    obtain ⟨hcont, hslice, htail⟩ := hF
    set z0 := z 0
    set z' := Fin.tail z with hz'def
    have hz0 : ‖z0‖ < r := (mem_openPolydisc.1 hz) 0
    have hz' : z' ∈ openPolydisc d r := tail_mem_openPolydisc hz
    have hz'c : z' ∈ closedPolydisc d r := openPolydisc_subset_closedPolydisc d le_rfl hz'
    have hzq : ∀ j, ‖z' j‖ / r < 1 := fun j => (div_lt_one hr).2 ((mem_openPolydisc.1 hz') j)
    -- the tail functions, their bounds and their coefficients
    have hMtail : ∀ w : ℂ, ‖w‖ ≤ r → ∀ w' ∈ closedPolydisc d r, ‖F (Fin.cons w w')‖ ≤ M :=
      fun w hw w' hw' => hM _ (cons_mem_closedPolydisc hw hw')
    have hMtorus : ∀ w : ℂ, ‖w‖ ≤ r → ∀ w' ∈ torusSet d r, ‖F (Fin.cons w w')‖ ≤ M :=
      fun w hw w' hw' => hMtail w hw w' (torusSet_subset_closedPolydisc d r hw')
    set c : ℂ → (Fin d → ℕ) → ℂ := fun w γ' => polyCoeff d r (fun w' => F (Fin.cons w w')) γ'
        with hc
    -- Step A: first-coordinate extraction
    have hA : HasSum (fun n => z0 ^ n * circleOp r fun w => w⁻¹ ^ n * F (Fin.cons w z')) (F z) := by
      have := hasSum_circleOp_coeff_eq hr (hslice z' hz'c) hz0
      rwa [Fin.cons_self_tail] at this
    -- Step B: tail expansion on the circle (induction hypothesis)
    have hB : ∀ w ∈ Metric.sphere (0 : ℂ) r,
        HasSum (fun γ' => c w γ' * ∏ j, z' j ^ γ' j) (F (Fin.cons w z')) := by
      intro w hw
      have hw' : ‖w‖ ≤ r := by simp at hw; linarith [hw]
      exact hasSum_polyCoeff d hr (htail w hw') (hMtail w hw') hz'
    -- Step C: interchange the circle operator with the tail series
    have hC : ∀ n : ℕ, HasSum (fun γ' => z0 ^ n * (∏ j, z' j ^ γ' j) * polyCoeff (d + 1) r F
        (Fin.cons n γ'))
        (z0 ^ n * circleOp r fun w => w⁻¹ ^ n * F (Fin.cons w z')) := by
      intro n
      -- the inner function on the circle is the tail series
      have hEq : EqOn (fun w => w⁻¹ ^ n * F (Fin.cons w z'))
          (fun w => ∑' γ' : Fin d → ℕ, w⁻¹ ^ n * c w γ' * ∏ j, z' j ^ γ' j) (Metric.sphere 0 r)
              := by
        intro w hw
        simp only
        rw [← (hB w hw).tsum_eq, ← tsum_mul_left]
        exact tsum_congr fun γ' => by ring
      -- majorant and continuity of the terms
      have hbound : ∀ γ' : Fin d → ℕ, ∀ w ∈ Metric.sphere (0 : ℂ) r,
          ‖w⁻¹ ^ n * c w γ' * ∏ j, z' j ^ γ' j‖ ≤ r⁻¹ ^ n * (M * ∏ j, (‖z' j‖ / r) ^ γ' j) := by
        intro γ' w hw
        have hwn : ‖w‖ = r := by simpa using hw
        rw [mul_assoc, norm_mul, norm_pow, norm_inv, hwn]
        exact mul_le_mul_of_nonneg_left (norm_polyCoeff_mul_pow_le hr (hMtorus w hwn.le) γ' z')
          (by positivity)
      have hsumb : Summable fun γ' : Fin d → ℕ => r⁻¹ ^ n * (M * ∏ j, (‖z' j‖ / r) ^ γ' j) :=
        ((summable_prodGeom d (q := fun j => ‖z' j‖ / r) (fun j => by positivity) hzq).mul_left
            M).mul_left _
      have hcontc : ∀ γ' : Fin d → ℕ, ContinuousOn (fun w => c w γ') (Metric.sphere (0 : ℂ) r) := by
        intro γ'
        simp only [hc, polyCoeff]
        refine continuousOn_iterOp_param d hr (X := ℂ) (S := Metric.sphere 0 r)
          (G := fun w w' => F (Fin.cons w w') * ∏ j, (w' j)⁻¹ ^ γ' j) ?_
        have hmap : Continuous fun p : ℂ × (Fin d → ℂ) => (Fin.cons p.1 p.2 : Fin (d + 1) → ℂ) :=
          continuous_fin_cons_pair
        have h1 : ContinuousOn (fun p : ℂ × (Fin d → ℂ) => F (Fin.cons p.1 p.2))
            (Metric.sphere (0 : ℂ) r ×ˢ torusSet d r) := by
          refine hcont.comp hmap.continuousOn fun p hp => ?_
          have hp1 : ‖p.1‖ ≤ r := by have := hp.1; simp at this; linarith
          exact cons_mem_closedPolydisc hp1 (torusSet_subset_closedPolydisc d r hp.2)
        have h2 : ContinuousOn (fun p : ℂ × (Fin d → ℂ) => ∏ j, (p.2 j)⁻¹ ^ γ' j)
            (Metric.sphere (0 : ℂ) r ×ˢ torusSet d r) := by
          refine continuousOn_finsetProd _ fun j _ => ?_
          refine ContinuousOn.pow ?_ _
          refine ContinuousOn.inv₀ ((continuous_apply j).comp continuous_snd).continuousOn ?_
          intro p hp h0
          have := (mem_torusSet.1 hp.2) j
          rw [h0, norm_zero] at this
          linarith
        exact h1.mul h2
      have hcontG : ∀ γ' : Fin d → ℕ, ContinuousOn (fun w => w⁻¹ ^ n * c w γ' * ∏ j, z' j ^ γ' j)
          (Metric.sphere (0 : ℂ) r) := by
        intro γ'
        refine ContinuousOn.mul (ContinuousOn.mul ?_ (hcontc γ')) continuousOn_const
        refine (ContinuousOn.inv₀ continuousOn_id fun w hw h0 => ?_).pow _
        have : ‖w‖ = r := by simpa using hw
        have h0' : w = 0 := h0
        rw [h0', norm_zero] at this; linarith
      have hint := hasSum_circleOp_tsum hr hsumb hbound hcontG
      rw [← circleOp_congr hr.le hEq] at hint
      -- pull the constants out of each circle operator
      have hterm : ∀ γ' : Fin d → ℕ, circleOp r (fun w => w⁻¹ ^ n * c w γ' * ∏ j, z' j ^ γ' j) =
          (∏ j, z' j ^ γ' j) * polyCoeff (d + 1) r F (Fin.cons n γ') := by
        intro γ'
        rw [polyCoeff_cons, ← circleOp_const_mul]
        congr 1; funext w; simp only [hc]; ring
      simp_rw [hterm] at hint
      exact (hint.mul_left (z0 ^ n)).congr_fun fun γ' => by ring
    -- Step D: regroup the double series along `Fin.cons`
    have hsumm : Summable fun γ : Fin (d + 1) → ℕ => polyCoeff (d + 1) r F γ * ∏ i, z i ^ γ i :=
      Summable.of_norm (summable_norm_polyCoeff_mul_pow hr
        (fun w hw => hM w (torusSet_subset_closedPolydisc _ _ hw)) hz)
    have hprod : ∀ p : ℕ × (Fin d → ℕ), polyCoeff (d + 1) r F (Fin.cons p.1 p.2) *
        ∏ i, z i ^ (Fin.cons p.1 p.2 : Fin (d + 1) → ℕ) i =
        z0 ^ p.1 * (∏ j, z' j ^ p.2 j) * polyCoeff (d + 1) r F (Fin.cons p.1 p.2) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hz'def, Fin.tail]
      ring
    rw [← (Fin.consEquiv fun _ => ℕ).hasSum_iff]
    have hsumm' : Summable ((fun γ : Fin (d + 1) → ℕ => polyCoeff (d + 1) r F γ * ∏ i, z i ^ γ i) ∘
        (Fin.consEquiv fun _ => ℕ)) := (Equiv.summable_iff _).2 hsumm
    rw [← (Equiv.sigmaEquivProd ℕ (Fin d → ℕ)).hasSum_iff]
    refine HasSum.sigma_of_hasSum hA (fun n => ?_) ((Equiv.summable_iff _).2 hsumm')
    show HasSum (fun γ' : Fin d → ℕ => polyCoeff (d + 1) r F (Fin.cons n γ') *
      ∏ i, z i ^ (Fin.cons n γ' : Fin (d + 1) → ℕ) i) _
    exact (hC n).congr_fun fun γ' => hprod (n, γ')

end Laplace.Grammar
