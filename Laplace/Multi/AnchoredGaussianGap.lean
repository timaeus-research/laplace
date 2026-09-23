/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.GammaLaw
import Laplace.Multi.LocalisedLaplaceGaussianGap

/-!
# The anchored Gaussian prediction and its purely anharmonic gap (E3/E2)

E3's localised target is a *tilted* Gaussian: precision `tH + gI` and tilt `v = g w₀` (the
localiser is
centred at the anchor `w₀`, not at the minimiser). Its scaled-energy Laplace transform is again a
ratio
of partition functions, now with the tilt's completed square
(`tiltedExpectation_exp_quadForm_tilted`):
`⟨e^{−c·½uᵀHu}⟩_{Q,v} = exp(½ m_c·v − ½ m·v)·√det Q/√det(Q + cH)`, `m = Q⁻¹v`, `m_c = (Q + cH)⁻¹v`;
in the
eigenbasis of `H` with `Q = tH + gI`, `c = st` and `aᵢ = (Uᵀv)ᵢ`
(`laplace_localisedGibbs_anchored`):
`Λ^{anch}_t(s) = exp(∑ᵢ(aᵢ²/2)(1/((1+s)tλᵢ + g) − 1/(tλᵢ + g)))·∏ᵢ√((tλᵢ + g)/((1+s)tλᵢ + g))`.

On the E2 side (`aᵢ = g·u₀ᵢ`, `u₀ = affineFrame Q c w₀`) the anchored prediction expands as
`Λ^{anch} = (1+s)^{−d/2}(1 + s(g∑ᵢ1/(2λᵢ) − ∑ᵢaᵢ²/(2λᵢ))/((1+s)t)) + O(t⁻²)`
(`anchoredGaussianTransform_rate2`), and with `LocalisedLaplaceCorrection`'s expansion of the exact
anharmonic transform (`localisedLaplace_anchoredGap`):
**`⟨e^{−st·L∘A}⟩_loc − Λ^{anch} = −(1+s)^{−d/2}·sC₁′/(1+s)/t + O(t⁻²)`**,
**`C₁′ = ∑ᵢ(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ)) = ∑ᵢ(e₀ᵢ − aᵢαᵢ/(2λᵢ²))`**, `e₀ = 5α²/(24λ³) − γ/(8λ²)`
(`energyLocCoeff1_anchored`): the anchored Gaussian prediction reproduces every localiser effect at
order
`1/t` — the `g` and `a²` terms of `LocalisedLaplaceGaussianGap`'s `C₁` cancel exactly — and the
residual
is purely anharmonic: the unlocalised first correction `e₀` and the cubic–anchor cross term
`−aα/(2λ²)`. Pointwise in `s > −1`; fixed `g, w₀` and quartic parameters.
-/

open Matrix Filter Topology Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The anchored (tilted) transform is a completed-square partition-function ratio**:
`⟨exp(−c·½uᵀHu)⟩_{Q,v} = exp(½ m_c·v − ½ m·v)·√det Q/√det(Q + cH)` with `m = Q⁻¹v`, `m_c = (Q +
cH)⁻¹v`. -/
theorem tiltedExpectation_exp_quadForm_tilted {Q H : Matrix ι ι ℝ} (hQ : Q.PosDef) {c : ℝ}
    (hQc : (Q + c • H).PosDef) (v : ι → ℝ) :
    tiltedExpectation Q v (fun u => Real.exp (-(c * ((1 / 2) * (u ⬝ᵥ H *ᵥ u))))) =
      Real.exp ((1 / 2) * (tiltMean (Q + c • H) v ⬝ᵥ v) - (1 / 2) * (tiltMean Q v ⬝ᵥ v)) *
        (Real.sqrt Q.det / Real.sqrt (Q + c • H).det) := by
  have e : ∀ u : ι → ℝ, Real.exp (-(c * ((1 / 2) * (u ⬝ᵥ H *ᵥ u)))) * tiltedWeight Q v u =
      tiltedWeight (Q + c • H) v u := by
    intro u
    unfold tiltedWeight
    rw [← Real.exp_add, dotProduct_add_smul_mulVec]
    congr 1
    ring
  have hnum : (∫ u : ι → ℝ, Real.exp (-(c * ((1 / 2) * (u ⬝ᵥ H *ᵥ u)))) * tiltedWeight Q v u) =
      tiltedZ (Q + c • H) v :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall e)
  unfold tiltedExpectation
  rw [hnum, tiltedZ_eq hQc v, tiltedZ_eq hQ v, gaussianZ_matCLM hQc, gaussianZ_matCLM hQ,
    mulVec_tiltMean hQc v, mulVec_tiltMean hQ v, Real.exp_sub]
  have h1 : Real.sqrt Q.det ≠ 0 := (Real.sqrt_pos.mpr hQ.det_pos).ne'
  have h2 : Real.sqrt (Q + c • H).det ≠ 0 := (Real.sqrt_pos.mpr hQc.det_pos).ne'
  have h3 : Real.sqrt (2 * Real.pi) ^ Fintype.card ι ≠ 0 := by positivity
  have h4 : Real.exp ((1 / 2) * (tiltMean Q v ⬝ᵥ v)) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- `(tH + gI)⁻¹ = U diag(1/(tλᵢ + g)) Uᵀ`. -/
theorem inv_localisedPrecision_eq_conj {H : Matrix ι ι ℝ} (hH : H.PosDef) {t g : ℝ} (ht : 0 < t)
    (hg : 0 ≤ g) :
    (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ =
      orthoOf hH.1 * diagonal (fun i => 1 / (t * hH.1.eigenvalues i + g)) * (orthoOf hH.1)ᵀ := by
  have hU' := orthoOf_mul_transpose hH.1
  rw [← orthoOf_transpose_localised_inv_mul hH ht hg]
  calc (t • H + g • (1 : Matrix ι ι ℝ))⁻¹
      = (orthoOf hH.1 * (orthoOf hH.1)ᵀ) * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ *
        (orthoOf hH.1 * (orthoOf hH.1)ᵀ) := by rw [hU', Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The tilt's completed square in the eigenbasis: `m·v = ∑ᵢ (Uᵀv)ᵢ²/(tλᵢ + g)` for `m = (tH +
gI)⁻¹v`. -/
theorem tiltMean_dot_localised {H : Matrix ι ι ℝ} (hH : H.PosDef) {t g : ℝ} (ht : 0 < t) (hg : 0 ≤
    g)
    (v : ι → ℝ) :
    tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v ⬝ᵥ v =
      ∑ i, ((orthoOf hH.1)ᵀ *ᵥ v) i ^ 2 / (t * hH.1.eigenvalues i + g) := by
  unfold tiltMean
  rw [inv_localisedPrecision_eq_conj hH ht hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **E3's anchored Gaussian prediction**: for `Q = tH + gI` and tilt `v`, with `aᵢ = (Uᵀv)ᵢ`,
`⟨e^{−st·½uᵀHu}⟩_{Q,v} = exp(∑ᵢ(aᵢ²/2)(1/((1+s)tλᵢ + g) − 1/(tλᵢ + g)))·√(∏ᵢ(tλᵢ + g)/((1+s)tλᵢ +
g))`. -/
theorem laplace_localisedGibbs_anchored {H : Matrix ι ι ℝ} (hH : H.PosDef) {t g s : ℝ} (ht : 0 < t)
    (hg : 0 ≤ g) (hs : -1 < s) (v : ι → ℝ) :
    tiltedExpectation (t • H + g • (1 : Matrix ι ι ℝ)) v
        (fun u => Real.exp (-(s * t * ((1 / 2) * (u ⬝ᵥ H *ᵥ u))))) =
      Real.exp (∑ i, (((orthoOf hH.1)ᵀ *ᵥ v) i ^ 2 / 2) *
          (1 / ((1 + s) * t * hH.1.eigenvalues i + g) - 1 / (t * hH.1.eigenvalues i + g))) *
        Real.sqrt (∏ i, (t * hH.1.eigenvalues i + g) / ((1 + s) * t * hH.1.eigenvalues i + g)) := by
  have hQ := effectivePrecision_posDef hH ht hg
  have ha : 0 < 1 + s := by linarith
  have e : t • H + g • (1 : Matrix ι ι ℝ) + (s * t) • H =
      ((1 + s) * t) • H + g • (1 : Matrix ι ι ℝ) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hQs : (t • H + g • (1 : Matrix ι ι ℝ) + (s * t) • H).PosDef := by
    rw [e]
    exact effectivePrecision_posDef hH (mul_pos ha ht) hg
  have hB : ∀ i, 0 ≤ (1 + s) * t * hH.1.eigenvalues i + g := fun i => by
    have := hH.eigenvalues_pos i
    positivity
  rw [tiltedExpectation_exp_quadForm_tilted hQ hQs v, e, det_localisedPrecision hH.1,
    det_localisedPrecision hH.1, Finset.prod_div_distrib,
    Real.sqrt_div' _ (Finset.prod_nonneg fun i _ => hB i), tiltMean_dot_localised hH ht hg v,
    tiltMean_dot_localised hH (mul_pos ha ht) hg v]
  congr 2
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Laplace.Sampler

namespace Laplace.Multi

/-! ### The anchored prediction's finite-temperature correction (E2 frame data) -/

/-- `|1/(u + g) − 1/u| ≤ g/u²` for `u > 0`, `g ≥ 0`. -/
theorem inv_shift_rate {u g : ℝ} (hu : 0 < u) (hg : 0 ≤ g) : |1 / (u + g) - 1 / u| ≤ g / u ^ 2 := by
  have e : 1 / (u + g) - 1 / u = -(g / (u * (u + g))) := by
    field_simp
    ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left hg (by positivity) (by nlinarith)

/-- The anchored exponent: `∑ᵢ(aᵢ²/2)(1/((1+s)tλᵢ + g) − 1/(tλᵢ + g)) = −(∑ᵢ s aᵢ²/(2λᵢ(1+s)))/t +
O(t⁻²)`. -/
theorem anchoredExponent_rate {d : ℕ} {lam : Fin d → ℝ} {g s : ℝ} (hlam : ∀ i, 0 < lam i) (hg : 0 ≤
    g)
    (hs : -1 < s) (a : Fin d → ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |(∑ i, (a i ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g))) -
      (-(∑ i, s * a i ^ 2 / (2 * lam i * (1 + s)))) / t| ≤ (∑ i, a i ^ 2 / 2 * (g / ((1 + s) ^ 2 *
        lam i ^ 2) + g / lam i ^ 2)) / t ^ 2 := by
  have ha : 0 < 1 + s := by linarith
  have ht0 : 0 < t := by linarith
  have key : ∀ i, (a i ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g)) -
      (-(s * a i ^ 2 / (2 * lam i * (1 + s)))) / t =
      (a i ^ 2 / 2) * ((1 / ((1 + s) * t * lam i + g) - 1 / ((1 + s) * t * lam i)) -
        (1 / (t * lam i + g) - 1 / (t * lam i))) := fun i => by
    have := (hlam i).ne'
    have := ha.ne'
    have := ht0.ne'
    field_simp
    ring
  have hb : ∀ i, |(a i ^ 2 / 2) * ((1 / ((1 + s) * t * lam i + g) - 1 / ((1 + s) * t * lam i)) -
      (1 / (t * lam i + g) - 1 / (t * lam i)))| ≤
      a i ^ 2 / 2 * (g / ((1 + s) ^ 2 * lam i ^ 2) + g / lam i ^ 2) / t ^ 2 := fun i => by
    have hl := hlam i
    have h1 := inv_shift_rate (mul_pos (mul_pos ha ht0) hl) hg
    have h2 := inv_shift_rate (mul_pos ht0 hl) hg
    have e1 : g / ((1 + s) * t * lam i) ^ 2 = g / ((1 + s) ^ 2 * lam i ^ 2) / t ^ 2 := by
      field_simp
    have e2 : g / (t * lam i) ^ 2 = g / lam i ^ 2 / t ^ 2 := by
      field_simp
    rw [e1] at h1
    rw [e2] at h2
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a i ^ 2 / 2)]
    calc a i ^ 2 / 2 * |(1 / ((1 + s) * t * lam i + g) - 1 / ((1 + s) * t * lam i)) -
          (1 / (t * lam i + g) - 1 / (t * lam i))|
        ≤ a i ^ 2 / 2 * (g / ((1 + s) ^ 2 * lam i ^ 2) / t ^ 2 + g / lam i ^ 2 / t ^ 2) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (by positivity)
      _ = _ := by ring
  calc |(∑ i, (a i ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g))) -
        (-(∑ i, s * a i ^ 2 / (2 * lam i * (1 + s)))) / t|
      = |∑ i, ((a i ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g)) -
        (-(s * a i ^ 2 / (2 * lam i * (1 + s)))) / t)| := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_neg_distrib]
    _ ≤ ∑ i, |(a i ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g)) -
        (-(s * a i ^ 2 / (2 * lam i * (1 + s)))) / t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, a i ^ 2 / 2 * (g / ((1 + s) ^ 2 * lam i ^ 2) + g / lam i ^ 2) / t ^ 2 :=
        Finset.sum_le_sum fun i _ => by rw [key i]; exact hb i
    _ = _ := by rw [Finset.sum_div]

/-- `exp(X/t + R) = 1 + X/t + O(t⁻²)` from `|exp x − 1 − x| ≤ x²` (`|x| ≤ 1`). -/
theorem exp_rate2 {x X KR t : ℝ} (ht : 1 ≤ t) (hKR : 0 ≤ KR) (hx : |x - X / t| ≤ KR / t ^ 2)
    (hT : |X| + KR ≤ t) :
    |Real.exp x - 1 - X / t| ≤ (KR + (|X| + KR) ^ 2) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hxb : |x| ≤ (|X| + KR) / t := by
    calc |x| = |(x - X / t) + X / t| := by ring_nf
      _ ≤ |x - X / t| + |X / t| := abs_add_le _ _
      _ ≤ KR / t ^ 2 + |X| / t := by
          rw [abs_div, abs_of_pos ht0]
          exact add_le_add hx le_rfl
      _ ≤ KR / t + |X| / t :=
          add_le_add (div_le_div_of_nonneg_left hKR ht0 (by nlinarith)) le_rfl
      _ = (|X| + KR) / t := by ring
  have hx1 : |x| ≤ 1 := hxb.trans (by rw [div_le_one ht0]; exact hT)
  have h1 := Real.abs_exp_sub_one_sub_id_le hx1
  have hx2 : x ^ 2 ≤ ((|X| + KR) / t) ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hxb 2
  have e : Real.exp x - 1 - X / t = (Real.exp x - 1 - x) + (x - X / t) := by ring
  rw [e]
  calc _ ≤ |Real.exp x - 1 - x| + |x - X / t| := abs_add_le _ _
    _ ≤ ((|X| + KR) / t) ^ 2 + KR / t ^ 2 := add_le_add (h1.trans hx2) hx
    _ = _ := by ring

/-- **The anchored Gaussian prediction's correction**:
`Λ^{anch} = (1+s)^{−d/2}(1 + s(g∑ᵢ1/(2λᵢ) − ∑ᵢaᵢ²/(2λᵢ))/((1+s)t)) + O(t⁻²)`. -/
theorem anchoredGaussianTransform_rate2 {d : ℕ} {lam : Fin d → ℝ} {g s : ℝ} (hlam : ∀ i, 0 < lam i)
    (hg : 0 ≤ g) (hs : -1 < s) (a : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |Real.exp (∑ i, (a i ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g))) * (∏ i,
        Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) - (1 / Real.sqrt (1 + s)) ^ d * (1
        + ((∑ i, g * s / (2 * lam i * (1 + s))) - ∑ i, s * a i ^ 2 / (2 * lam i * (1 + s))) / t)| ≤
        K / t ^ 2 := by
  obtain ⟨KG, TG, hKG, hTG, hG⟩ := gaussianTransform_rate2 hlam hg hs (s := s)
  have ha : 0 < 1 + s := by linarith
  have hsa : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr ha
  set KR : ℝ := ∑ i, a i ^ 2 / 2 * (g / ((1 + s) ^ 2 * lam i ^ 2) + g / lam i ^ 2) with hKR
  set X : ℝ := -(∑ i, s * a i ^ 2 / (2 * lam i * (1 + s))) with hX
  have hKR0 : 0 ≤ KR := Finset.sum_nonneg fun i _ => by have := hlam i; positivity
  set P : ℝ := (1 / Real.sqrt (1 + s)) ^ d with hP
  have hP0 : 0 < P := by positivity
  refine ⟨P * ((KR + (|X| + KR) ^ 2) * (1 + |∑ i, g * s / (2 * lam i * (1 + s))| + KG / P) +
    (1 + |X|) * (KG / P) + |X * (∑ i, g * s / (2 * lam i * (1 + s)))|), TG + (|X| + KR) + 1, by
        positivity,
    by linarith [abs_nonneg X], fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith [abs_nonneg X]
  have ht0 : 0 < t := by linarith
  have hexp := exp_rate2 ht1 hKR0 (anchoredExponent_rate hlam hg hs a ht1) (by linarith)
  have hG' : |(∏ i, Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) / P - 1 - (∑ i, g * s /
      (2 * lam i * (1 + s))) / t| ≤ KG / P / t ^ 2 := by
    have h := hG (t := t) (by linarith [abs_nonneg X])
    have e : (∏ i, Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) / P - 1 - (∑ i, g * s /
      (2 * lam i * (1 + s))) / t = ((∏ i, Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) -
      P * (1 + (∑ i, g * s / (2 * lam i * (1 + s))) / t)) / P := by
      rw [sub_div, mul_div_cancel_left₀ _ hP0.ne']
      ring
    rw [e, abs_div, abs_of_pos hP0, div_div, mul_comm P (t ^ 2), ← div_div]
    exact div_le_div_of_nonneg_right h hP0.le
  have hprod := prod_rate_order2 ht1 (by positivity) (by positivity) hexp hG'
  have e2 : Real.exp (∑ i, (a i ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g))) *
      (∏ i, Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) - P * (1 + ((∑ i, g * s / (2 *
      lam i * (1 + s))) - ∑ i, s * a i ^ 2 / (2 * lam i * (1 + s))) / t) = P * (Real.exp (∑ i, (a i
      ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g))) * ((∏ i, Real.sqrt ((t * lam
      i + g) / ((1 + s) * t * lam i + g))) / P) - 1 - (X + (∑ i, g * s / (2 * lam i * (1 + s)))) /
      t) := by
    rw [hX]
    field_simp
    ring
  rw [e2, abs_mul, abs_of_pos hP0]
  calc _ ≤ P * (((KR + (|X| + KR) ^ 2) * (1 + |∑ i, g * s / (2 * lam i * (1 + s))| + KG / P) +
        (1 + |X|) * (KG / P) + |X * (∑ i, g * s / (2 * lam i * (1 + s)))|) / t ^ 2) :=
        mul_le_mul_of_nonneg_left hprod hP0.le
    _ = _ := by ring

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

omit hgamma hdisc in
/-- **The anchored gap coefficient is purely anharmonic**:
`e₁ + g/(2λ) − (gx₀)²/(2λ) = (5α²/(24λ³) − γ/(8λ²)) − gx₀α/(2λ²)`. -/
theorem energyLocCoeff1_anchored (i : Fin d) (alpha gamma : ℝ) (x₀ : ℝ) :
    energyLocCoeff1 (lam i) alpha gamma g x₀ + g / (2 * lam i) - (g * x₀) ^ 2 / (2 * lam i) =
      (5 * alpha ^ 2 / (24 * lam i ^ 3) - gamma / (8 * lam i ^ 2)) - g * x₀ * alpha / (2 * lam i ^
          2) := by
  have hl : lam i ≠ 0 := (hlam i).ne'
  unfold energyLocCoeff1 locSecondCoeff2 locN2 locThirdCoeff locD1 locP₃
  field_simp
  ring

/-- **The gap to the anchored prediction is purely anharmonic**: for each fixed `s > −1`,
`⟨e^{−st·L∘A}⟩_loc − Λ^{anch} = −(1+s)^{−d/2}·sC₁′/(1+s)/t + O(t⁻²)` with
`C₁′ = ∑ᵢ(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ))`, `aᵢ = g·u₀ᵢ` — by `energyLocCoeff1_anchored` equal to
`∑ᵢ(e₀ᵢ − aᵢαᵢ/(2λᵢ²))`: the anchored Gaussian captures all localiser effects at order `1/t`. -/
theorem localisedLaplace_anchoredGap (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {s : ℝ}
    (hs : -1 < s) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => Real.exp
        (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) - Real.exp (∑ i, ((g * affineFrame Q c
        w₀ i) ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g))) * (∏ i, Real.sqrt
        ((t * lam i + g) / ((1 + s) * t * lam i + g))) + (1 / Real.sqrt (1 + s)) ^ d * (s * (∑ i,
        (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g
        * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / (1 + s) / t)| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := localisedLaplace_rate2 hlam hgamma hdisc hQ c w₀ hg hs
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := anchoredGaussianTransform_rate2 hlam hg hs
    (fun i => g * affineFrame Q c w₀ i) (s := s)
  have ha : 0 < 1 + s := by linarith
  refine ⟨K₁ + K₂, T₁ + T₂, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e₁ := h₁ (t := t) (by linarith)
  have e₂ := h₂ (t := t) (by linarith)
  have hX : (∑ i, -(energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) * s / (1 +
      s))) - ((∑ i, g * s / (2 * lam i * (1 + s))) - ∑ i, s * (g * affineFrame Q c w₀ i) ^ 2 / (2 *
      lam i * (1 + s))) = -(s * (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q
      c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / (1 + s)) := by
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hlam i).ne'
    have := ha.ne'
    field_simp
    ring
  have e : gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w =>
      Real.exp (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) - Real.exp (∑ i, ((g *
      affineFrame Q c w₀ i) ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t * lam i + g))) * (∏
      i, Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) + (1 / Real.sqrt (1 + s)) ^ d * (s
      * (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam
      i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / (1 + s) / t) = (gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => Real.exp (-(s * t *
      rotatedAnharmonic Q c lam alpha gamma w))) - (1 / Real.sqrt (1 + s)) ^ d * (1 + (∑ i,
      -(energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) * s / (1 + s))) / t)) -
      (Real.exp (∑ i, ((g * affineFrame Q c w₀ i) ^ 2 / 2) * (1 / ((1 + s) * t * lam i + g) - 1 / (t
      * lam i + g))) * (∏ i, Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) - (1 /
      Real.sqrt (1 + s)) ^ d * (1 + ((∑ i, g * s / (2 * lam i * (1 + s))) - ∑ i, s * (g *
      affineFrame Q c w₀ i) ^ 2 / (2 * lam i * (1 + s))) / t)) := by
    linear_combination ((1 / Real.sqrt (1 + s)) ^ d / t) * hX
  rw [e]
  calc _ ≤ |_| + |_| := abs_sub _ _
    _ ≤ K₁ / t ^ 2 + K₂ / t ^ 2 := add_le_add e₁ e₂
    _ = _ := by ring

end Multi

end Laplace.Multi
