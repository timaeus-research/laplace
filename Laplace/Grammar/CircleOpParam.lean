/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PolydiscCauchy

/-!
# Parametric continuity and series interchange for the circle operators (Stage 7c)

Unit 262 (Astra #31 route R2, unit 2/4 deliverables). Three tools for the coefficient extraction
on a
polydisc: (i) `x ↦ A_r(G x)` is continuous on a set `S` when `G` is jointly continuous on
`S × {|w| = r}` (`continuousOn_circleOp_param`; via restriction to the subtype and the
interval-integral
parametric-continuity lemma), and likewise for the iterated operator on `S × torus`
(`continuousOn_iterOp_param`); (ii) **series interchange**: `A_r(∑_γ G γ ·) = ∑_γ A_r(G γ ·)` as a
`HasSum`, for families with a uniform summable majorant on the circle and continuous terms
(`hasSum_circleOp_tsum`, dominated convergence on the interval integral); (iii) the product
geometric series `∑_{γ : Fin d → ℕ} ∏ᵢ qᵢ^{γᵢ} < ∞` for `0 ≤ qᵢ < 1` (`summable_prodGeom`), the
majorant of the several-variable Cauchy coefficients. No `sorry` and no additional `axiom`
declarations.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

/-! ### Parametric continuity on sets -/

theorem continuous_circleMap_param {X : Type*} [TopologicalSpace X] (r : ℝ) :
    Continuous fun p : X × ℝ => circleMap 0 r p.2 :=
  (continuous_circleMap 0 r).comp continuous_snd

/-- `x ↦ A_r(G x)` is continuous on `S` if `(x, w) ↦ G x w` is continuous on `S × {|w| = r}`. -/
theorem continuousOn_circleOp_param {X : Type*} [TopologicalSpace X] {r : ℝ} (hr : 0 < r)
    {G : X → ℂ → ℂ} {S : Set X}
    (hG : ContinuousOn (fun p : X × ℂ => G p.1 p.2) (S ×ˢ Metric.sphere (0 : ℂ) r)) :
    ContinuousOn (fun x => circleOp r (G x)) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  show Continuous fun x : S => circleOp r (G x.1)
  unfold circleOp
  refine continuous_const.mul ?_
  simp only [circleIntegral]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  have hmap : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hne : ∀ θ : ℝ, circleMap 0 r θ ≠ 0 := fun _ => circleMap_ne_center hr.ne'
  have hinv : Continuous fun θ : ℝ => (circleMap 0 r θ)⁻¹ := hmap.inv₀ hne
  have hderiv : Continuous fun θ : ℝ => deriv (circleMap 0 r) θ := by
    simp only [deriv_circleMap]; exact hmap.mul continuous_const
  have hGc : Continuous fun p : S × ℝ => G p.1.1 (circleMap 0 r p.2) := by
    refine hG.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (hmap.comp continuous_snd)) fun p => ?_
    exact ⟨p.1.2, circleMap_mem_sphere 0 hr.le _⟩
  exact (hderiv.comp continuous_snd).smul ((hinv.comp continuous_snd).mul hGc)

theorem continuous_fin_cons_pair {d : ℕ} :
    Continuous fun q : ℂ × (Fin d → ℂ) => (Fin.cons q.1 q.2 : Fin (d + 1) → ℂ) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd

/-- `x ↦ A_r^{[d]}(G x)` is continuous on `S` if `(x, w) ↦ G x w` is continuous on `S × torus`. -/
theorem continuousOn_iterOp_param : ∀ (d : ℕ) {X : Type*} [TopologicalSpace X] {r : ℝ}, 0 < r →
    ∀ {G : X → (Fin d → ℂ) → ℂ} {S : Set X},
      ContinuousOn (fun p : X × (Fin d → ℂ) => G p.1 p.2) (S ×ˢ torusSet d r) →
        ContinuousOn (fun x => iterOp d r (G x)) S
  | 0, X, _, r, _, G, S, hG => by
    simp only [iterOp]
    have : ContinuousOn (fun x : X => (x, (Fin.elim0 : Fin 0 → ℂ))) S :=
      continuousOn_id.prodMk continuousOn_const
    exact hG.comp this fun x hx => ⟨hx, by simp [torusSet]⟩
  | d + 1, X, _, r, hr, G, S, hG => by
    simp only [iterOp]
    refine continuousOn_circleOp_param hr ?_
    refine continuousOn_iterOp_param d hr (X := X × ℂ) (S := S ×ˢ Metric.sphere (0 : ℂ) r)
      (G := fun p w' => G p.1 (Fin.cons p.2 w')) ?_
    have hmap : Continuous fun q : (X × ℂ) × (Fin d → ℂ) =>
        (q.1.1, (Fin.cons q.1.2 q.2 : Fin (d + 1) → ℂ)) :=
      (continuous_fst.comp continuous_fst).prodMk
        (continuous_fin_cons_pair.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    refine hG.comp hmap.continuousOn fun q hq => ?_
    exact ⟨hq.1.1, cons_mem_torusSet (by simpa using hq.1.2) hq.2⟩

/-! ### Series interchange -/

/-- **Interchange of `A_r` with an absolutely dominated series**: if `‖G n w‖ ≤ bound n` on the
circle with `bound` summable and each `G n` continuous on the circle, then
`∑_n A_r(G n) = A_r(∑_n G n)` as a `HasSum`. -/
theorem hasSum_circleOp_tsum {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r) {G : ι → ℂ → ℂ}
    {bound : ι → ℝ} (hb : Summable bound) (hG : ∀ n, ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖G n w‖ ≤
        bound n)
    (hc : ∀ n, ContinuousOn (G n) (Metric.sphere (0 : ℂ) r)) :
    HasSum (fun n => circleOp r (G n)) (circleOp r fun w => ∑' n, G n w) := by
  have hmap : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hne : ∀ θ : ℝ, circleMap 0 r θ ≠ 0 := fun _ => circleMap_ne_center hr.ne'
  have hsph : ∀ θ : ℝ, circleMap 0 r θ ∈ Metric.sphere (0 : ℂ) r := fun θ =>
    circleMap_mem_sphere 0 hr.le θ
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr]
  -- pointwise summability on the circle
  have hsumm : ∀ θ : ℝ, Summable fun n => G n (circleMap 0 r θ) := fun θ =>
    Summable.of_norm_bounded hb fun n => hG n _ (hsph θ)
  set F : ι → ℝ → ℂ := fun n θ => deriv (circleMap 0 r) θ • ((circleMap 0 r θ)⁻¹ * G n (circleMap
      0 r θ))
    with hF
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    intro n
    refine Continuous.aestronglyMeasurable ?_
    have hGc : Continuous fun θ : ℝ => G n (circleMap 0 r θ) :=
      (hc n).comp_continuous hmap hsph
    have hderiv : Continuous fun θ : ℝ => deriv (circleMap 0 r) θ := by
      simp only [deriv_circleMap]; exact hmap.mul continuous_const
    exact hderiv.smul ((hmap.inv₀ hne).mul hGc)
  have hbound : ∀ n, ∀ᵐ θ ∂volume, θ ∈ Set.uIoc 0 (2 * Real.pi) → ‖F n θ‖ ≤ bound n := by
    intro n
    refine Eventually.of_forall fun θ _ => ?_
    simp only [hF, smul_eq_mul, norm_mul, deriv_circleMap, Complex.norm_I, mul_one, hnorm, norm_inv]
    have := hG n _ (hsph θ)
    calc r * (r⁻¹ * ‖G n (circleMap 0 r θ)‖) = ‖G n (circleMap 0 r θ)‖ := by field_simp
      _ ≤ bound n := this
  have hFsumm : ∀ θ : ℝ, Summable fun n => F n θ := fun θ =>
    (((hsumm θ).mul_left ((circleMap 0 r θ)⁻¹)).mul_left (deriv (circleMap 0 r) θ)).congr
      fun n => by simp [hF, smul_eq_mul]
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 2 * Real.pi) (F := F) (f := fun θ => ∑' n, F n θ) (fun n _ => bound n) hmeas
        hbound
    (Eventually.of_forall fun _ _ => hb) intervalIntegrable_const
    (Eventually.of_forall fun θ _ => (hFsumm θ).hasSum)
  have hlim : ∀ θ : ℝ, ∑' n, F n θ =
      deriv (circleMap 0 r) θ • ((circleMap 0 r θ)⁻¹ * ∑' n, G n (circleMap 0 r θ)) := by
    intro θ
    simp only [hF, smul_eq_mul]
    rw [← tsum_mul_left, ← tsum_mul_left]
  have hsum' := hsum.mul_left ((2 * Real.pi * I)⁻¹ : ℂ)
  rw [intervalIntegral.integral_congr (fun θ _ => hlim θ)] at hsum'
  unfold circleOp
  simp only [circleIntegral]
  exact hsum'

/-! ### The product geometric series -/

theorem summable_prodGeom : ∀ (d : ℕ) {q : Fin d → ℝ}, (∀ i, 0 ≤ q i) → (∀ i, q i < 1) →
    Summable fun γ : Fin d → ℕ => ∏ i, q i ^ γ i
  | 0, _, _, _ => Summable.of_finite
  | d + 1, q, hq0, hq1 => by
    have hgeo : Summable fun n : ℕ => q 0 ^ n := summable_geometric_of_lt_one (hq0 0) (hq1 0)
    have hih := summable_prodGeom d (q := fun j => q j.succ) (fun j => hq0 _) (fun j => hq1 _)
    have hprod : Summable fun p : ℕ × (Fin d → ℕ) => q 0 ^ p.1 * ∏ j, q j.succ ^ p.2 j := by
      refine summable_mul_of_summable_norm (f := fun n : ℕ => q 0 ^ n)
        (g := fun γ' : Fin d → ℕ => ∏ j, q j.succ ^ γ' j) ?_ ?_
      · simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hq0 0) _)] using hgeo
      · refine hih.congr fun γ' => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun j _ => pow_nonneg (hq0 _) _)]
    rw [← (Fin.consEquiv fun _ => ℕ).summable_iff]
    refine hprod.congr fun p => ?_
    simp only [Function.comp, Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ]

end Laplace.Grammar
