/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.JointChartMetric

/-!
# The arcsine length bound

For an observable with values in `[lo, hi]` the **Bhatia–Davis inequality**
`Var φ ≤ (⟨φ⟩ − lo)(hi − ⟨φ⟩)` (`priorCov_self_le_mul_of_bounds`) sharpens Popoviciu's bound, and
it turns the Cauchy–Schwarz speed bound `|d⟨φ⟩/ds| ≤ √Var φ · √G(η', η')` into a bound on the speed
of the **arcsine chart** `F = 2 arcsin √((⟨φ⟩ − lo)/(hi − lo))`: `|dF/ds| ≤ √G(η', η')`
(`arcsin_speed_bound`). Integrating along any `C¹` path in natural coordinates whose observable
expectation stays strictly inside `(lo, hi)`,

`2 |arcsin √z(1) − arcsin √z(0)| ≤ Length(η)`,  `z(s) = (⟨φ⟩_{η s} − lo)/(hi − lo)`

(`natLength_ge_arcsin`): the Fisher length of a journey is at least the Fisher distance between the
Bernoulli laws that a bounded observable is seen through. This dominates the Popoviciu bound
`2|Δ⟨φ⟩|/(hi − lo)`, since `2 arcsin` has slope at least `2` on `[0, 1]` in the `√z` variable.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- **The speed of the arcsine chart is bounded by the Fisher speed**, given the Cauchy–Schwarz
bound on the observable speed and the Bhatia–Davis bound on its variance. -/
theorem arcsin_speed_bound {p q d m' V G : ℝ} (hp : 0 < p) (hq : 0 < q) (hd : p + q = d)
    (hVle : V ≤ p * q) (hm' : |m'| ≤ Real.sqrt V * Real.sqrt G) :
    |2 * (1 / Real.sqrt (1 - Real.sqrt (p / d) ^ 2) *
      (m' / d / (2 * Real.sqrt (p / d))))| ≤ Real.sqrt G := by
  have hd0 : 0 < d := by rw [← hd]; positivity
  have hz : Real.sqrt (p / d) ^ 2 = p / d := Real.sq_sqrt (by positivity)
  have h1z : 1 - p / d = q / d := by field_simp; linarith
  rw [hz, h1z, Real.sqrt_div' _ hd0.le, Real.sqrt_div' _ hd0.le]
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have e : 2 * (1 / (Real.sqrt q / Real.sqrt d) * (m' / d / (2 * (Real.sqrt p / Real.sqrt d)))) =
      m' / (Real.sqrt p * Real.sqrt q) := by
    set st := Real.sqrt d with hst
    have hd' : d = st * st := (Real.mul_self_sqrt hd0.le).symm
    have hst0 : st ≠ 0 := hsd.ne'
    rw [hd']
    field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hsp hsq), div_le_iff₀ (mul_pos hsp hsq)]
  calc |m'| ≤ Real.sqrt V * Real.sqrt G := hm'
    _ ≤ Real.sqrt (p * q) * Real.sqrt G :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hVle) (Real.sqrt_nonneg _)
    _ = Real.sqrt G * (Real.sqrt p * Real.sqrt q) := by
        rw [Real.sqrt_mul hp.le]; ring

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- **The Bhatia–Davis inequality**: `Var φ ≤ (⟨φ⟩ − lo)(hi − ⟨φ⟩)` for `lo ≤ φ ≤ hi`. -/
theorem priorCov_self_le_mul_of_bounds {t : ℝ} (a : ι → ℝ) {φ : X → ℝ} (hφ : Bdd φ) {lo hi : ℝ}
    (hlo : ∀ x, lo ≤ φ x) (hhi : ∀ x, φ x ≤ hi) :
    priorCov μ π (affLoss L₀ R a) φ φ t ≤
      (priorExp μ π (affLoss L₀ R a) φ t - lo) * (hi - priorExp μ π (affLoss L₀ R a) φ t) := by
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  have hexp : priorExp μ π (affLoss L₀ R a) (fun x ↦ (φ x - lo) * (hi - φ x)) t =
      -1 * priorExp μ π (affLoss L₀ R a) (fun x ↦ φ x * φ x) t +
        ((lo + hi) * priorExp μ π (affLoss L₀ R a) φ t + -(lo * hi)) := by
    have e : (fun x ↦ (φ x - lo) * (hi - φ x)) =
        fun x ↦ -1 * (φ x * φ x) + ((lo + hi) * φ x + -(lo * hi)) := funext fun x ↦ by ring
    rw [e, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (Bdd.const_mul _ (hφ.mul hφ))
      ((hφ.const_mul _).add (Bdd.const _)),
      priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hφ.const_mul _) (Bdd.const _),
      priorExp_const_mul_bdd, priorExp_const_mul_bdd, priorExp_const_fun hZ]
  have hnn : priorExp μ π (affLoss L₀ R a) (fun _ ↦ (0 : ℝ)) t ≤
      priorExp μ π (affLoss L₀ R a) (fun x ↦ (φ x - lo) * (hi - φ x)) t :=
    priorExp_mono_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (Bdd.const _)
      ((hφ.sub (Bdd.const _)).mul ((Bdd.const _).sub hφ)) fun x ↦
        mul_nonneg (sub_nonneg.2 (hlo x)) (sub_nonneg.2 (hhi x))
  rw [priorExp_const_fun hZ, hexp] at hnn
  unfold priorCov
  nlinarith

end

section Path

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- **The arcsine length bound**: along any `C¹` path in natural coordinates whose observable
expectation stays strictly inside `(lo, hi)`,
`2 |arcsin √z(1) − arcsin √z(0)| ≤ Length(η)` with `z(s) = (⟨φ⟩_{η s} − lo)/(hi − lo)`. -/
theorem natLength_ge_arcsin {η η' : ℝ → Option ι → ℝ} (hη : ∀ s, HasDerivAt η (η' s) s)
    (hη' : Continuous η') {φ : X → ℝ} (hφ : Bdd φ) {lo hi : ℝ} (hlo : ∀ x, lo ≤ φ x)
    (hhi : ∀ x, φ x ≤ hi)
    (hint : ∀ s, lo < priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ 1 ∧
      priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ 1 < hi) :
    2 * |Real.arcsin (Real.sqrt
        ((priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η 1)) φ 1 - lo) / (hi - lo))) -
      Real.arcsin (Real.sqrt
        ((priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η 0)) φ 1 - lo) / (hi - lo)))|
      ≤ natLength μ π L₀ R η η' := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hηc : Continuous η := continuous_iff_continuousAt.2 fun s ↦ (hη s).continuousAt
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  have hd : 0 < hi - lo := by linarith [(hint 0).1, (hint 0).2]
  -- the observable expectation along the path and its velocity
  set m : ℝ → ℝ := fun s ↦ priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ 1
    with hmdef
  set m' : ℝ → ℝ := fun s ↦ -priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ
    (dirLoss (jointStat L₀ R) (η' s)) 1 with hm'def
  have hD : ∀ s, HasDerivAt m (m' s) s := fun s ↦
    hasDerivAt_priorExp_natPath hπm hπi hπ hπpos hL₀m hL₀ hR (hη s) ⟨hφm, Mφ, hφb⟩
  have hmc : Continuous m := continuous_iff_continuousAt.2 fun s ↦ (hD s).continuousAt
  have hm'c : Continuous m' := by
    have hc := (continuous_obsMapDeriv hπm hπi hπ hπpos measurable_const h0 hS' hφm hφb
      one_pos).comp hηc |>.clm_apply hη'
    refine hc.congr fun s ↦ ?_
    simp only [Function.comp, hm'def]
    rw [obsMapDeriv_apply hπm hπi hπ hπpos measurable_const h0 hS' hφm hφb one_pos]
    ring
  -- the arcsine chart and its derivative
  set z : ℝ → ℝ := fun s ↦ (m s - lo) / (hi - lo) with hzdef
  have hzpos : ∀ s, 0 < z s := fun s ↦ div_pos (by linarith [(hint s).1]) hd
  have hzlt : ∀ s, z s < 1 := fun s ↦ by
    rw [hzdef]; dsimp only
    rw [div_lt_one hd]; linarith [(hint s).2]
  have hsq1 : ∀ s, Real.sqrt (z s) ≠ 1 := fun s ↦ by
    rw [Ne, Real.sqrt_eq_one]; exact (hzlt s).ne
  have hsqm1 : ∀ s, Real.sqrt (z s) ≠ -1 := fun s ↦ by
    have := Real.sqrt_nonneg (z s); linarith
  have hF : ∀ s, HasDerivAt (fun s ↦ 2 * Real.arcsin (Real.sqrt (z s)))
      (2 * (1 / Real.sqrt (1 - Real.sqrt (z s) ^ 2) * (m' s / (hi - lo) / (2 * Real.sqrt (z s)))))
      s := by
    intro s
    have hz : HasDerivAt z (m' s / (hi - lo)) s := ((hD s).sub_const lo).div_const (hi - lo)
    have hsq : HasDerivAt (fun s ↦ Real.sqrt (z s)) (m' s / (hi - lo) / (2 * Real.sqrt (z s))) s :=
      hz.sqrt (hzpos s).ne'
    have harc := (Real.hasDerivAt_arcsin (hsqm1 s) (hsq1 s)).comp s hsq
    exact harc.const_mul 2
  -- continuity of the derivative of the chart
  have hs1ne : ∀ s, Real.sqrt (1 - Real.sqrt (z s) ^ 2) ≠ 0 := fun s ↦ by
    rw [Real.sq_sqrt (hzpos s).le]
    exact (Real.sqrt_pos.2 (by linarith [hzlt s])).ne'
  have hs2ne : ∀ s, 2 * Real.sqrt (z s) ≠ 0 := fun s ↦ by
    have := Real.sqrt_pos.2 (hzpos s); positivity
  have hzc : Continuous z := (hmc.sub continuous_const).div_const _
  have hF'c : Continuous (fun s ↦ 2 * (1 / Real.sqrt (1 - Real.sqrt (z s) ^ 2) *
      (m' s / (hi - lo) / (2 * Real.sqrt (z s))))) :=
    continuous_const.mul ((continuous_const.div ((continuous_const.sub (hzc.sqrt.pow 2)).sqrt)
      hs1ne).mul ((hm'c.div_const _).div (continuous_const.mul hzc.sqrt) hs2ne))
  have hGc : Continuous (fun s ↦ natForm μ π L₀ R (η s) (η' s) (η' s)) :=
    continuous_natCov_path hπm hπi hπ hπpos hL₀m hL₀ hR hηc hη' hη'
  -- the pointwise speed bound
  have hbound : ∀ s, |2 * (1 / Real.sqrt (1 - Real.sqrt (z s) ^ 2) *
      (m' s / (hi - lo) / (2 * Real.sqrt (z s))))| ≤
      Real.sqrt (natForm μ π L₀ R (η s) (η' s) (η' s)) := by
    intro s
    have hBD := priorCov_self_le_mul_of_bounds hπm hπi hπ hπpos measurable_const h0 hS' (t := 1)
      (η s) ⟨hφm, Mφ, hφb⟩ hlo hhi
    have hCS := abs_priorCov_le_sqrt_natForm hπm hπi hπ hπpos hL₀m hL₀ hR (η s) (η' s)
      ⟨hφm, Mφ, hφb⟩
    have hm'abs : |m' s| ≤ Real.sqrt
        (priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ φ 1) *
        Real.sqrt (natForm μ π L₀ R (η s) (η' s) (η' s)) := by
      rw [hm'def]; dsimp only
      rw [abs_neg]; exact hCS
    exact arcsin_speed_bound (p := m s - lo) (q := hi - m s) (d := hi - lo)
      (by linarith [(hint s).1]) (by linarith [(hint s).2]) (by ring) hBD hm'abs
  -- integrate
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hF s)
    (hF'c.intervalIntegrable 0 1)
  have e : 2 * |Real.arcsin (Real.sqrt (z 1)) - Real.arcsin (Real.sqrt (z 0))| =
      |2 * Real.arcsin (Real.sqrt (z 1)) - 2 * Real.arcsin (Real.sqrt (z 0))| := by
    rw [← mul_sub, abs_mul, abs_two]
  change 2 * |Real.arcsin (Real.sqrt (z 1)) - Real.arcsin (Real.sqrt (z 0))| ≤ _
  rw [e, ← hftc, natLength]
  calc |∫ s in (0 : ℝ)..1, 2 * (1 / Real.sqrt (1 - Real.sqrt (z s) ^ 2) *
          (m' s / (hi - lo) / (2 * Real.sqrt (z s))))|
      ≤ ∫ s in (0 : ℝ)..1, |2 * (1 / Real.sqrt (1 - Real.sqrt (z s) ^ 2) *
          (m' s / (hi - lo) / (2 * Real.sqrt (z s))))| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ _ := intervalIntegral.integral_mono_on zero_le_one (hF'c.abs.intervalIntegrable 0 1)
        (hGc.sqrt.intervalIntegrable 0 1) fun s _ ↦ hbound s

end Path

end Laplace.Multi
