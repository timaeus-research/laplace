/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.CovKRate
import Laplace.Multi.SeparableExact

/-!
# The localised anharmonic measure: eq:mean's localisation term at leading order

eq:mean reads `⟨w⟩ − w* = −½ S (tT:S) + γ S (w₀ − w*) + O(S²)` with `S = (tH + γI)⁻¹`; the seabed
certifies the localisation term only for Gaussian targets. Here, in one dimension, for the exact
localised anharmonic measure `e^{−tℓ(x) − (g/2)(x − x₀)²}` (`ℓ` the anharmonic quartic, `g ≥ 0` the
localisation strength, `x₀` the anchor), the mean is `⟨x⟩_loc = ⟨xφ⟩_t/⟨φ⟩_t` under the anharmonic
Gibbs measure with the bounded weight `φ(x) = e^{g x₀ x − (g/2)x²}` (`localisedMean_eq_ratio`).
The weight expands as `|φ(x) − 1 − g x₀ x| ≤ C₁x² + C₂x⁴` (`locWeight_expansion`), odd absolute
moments are controlled by even ones through a `t`-dependent Young inequality
(`absMoment_three_bound`, `absMoment_five_bound`), and the main theorem
`localisedMean_anharmonic_rate` gives

  `|t ⟨x⟩_loc − (−α/(2λ²) + g x₀/λ)| ≤ K/√t`  for `t ≥ T`:

eq:mean's `−½ S (tT:S) + g S (x₀ − x*)` at leading order (`S ≈ 1/(λt)`) for the exact anharmonic
localised measure, and `localisedMean_sub_locLeading_rate` compares with the displayed formula
itself, `P_t = −αt/(2(tλ + g)²) + g x₀/(tλ + g)` (`locLeading`): `|⟨x⟩_loc − P_t| ≤ K/(t√t)`.
This is leading-order certification only; the note's `O(S²)` remainder is not addressed
(numerically it holds).
-/

open Real MeasureTheory Filter Topology
open scoped Nat

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

/-! ### The localised weight -/

section Weight

variable {g x₀ : ℝ}

/-- The localised weight `φ(x) = exp(g x₀ x − (g/2) x²)`. -/
noncomputable def locWeight (g x₀ x : ℝ) : ℝ := Real.exp (g * x₀ * x - g / 2 * x ^ 2)

theorem locWeight_pos (x : ℝ) : 0 < locWeight g x₀ x := Real.exp_pos _

theorem continuous_locWeight (g x₀ : ℝ) : Continuous (locWeight g x₀) := by
  unfold locWeight
  fun_prop

/-- `φ ≤ e^{g x₀²/2}` (completing the square). -/
theorem locWeight_le (hg : 0 ≤ g) (x : ℝ) : locWeight g x₀ x ≤ Real.exp (g * x₀ ^ 2 / 2) := by
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hg (sq_nonneg (x - x₀))]

/-- `|e^y − 1 − y| ≤ (e^M + 2) y²` for `y ≤ M`, `M ≥ 0`. -/
theorem abs_exp_sub_one_sub_le {y M : ℝ} (hy : y ≤ M) :
    |Real.exp y - 1 - y| ≤ (Real.exp M + 2) * y ^ 2 := by
  rcases le_or_gt |y| 1 with h1 | h1
  · calc |Real.exp y - 1 - y| ≤ y ^ 2 := Real.abs_exp_sub_one_sub_id_le h1
      _ ≤ (Real.exp M + 2) * y ^ 2 := by nlinarith [Real.exp_pos M, sq_nonneg y]
  · have hy2 : |y| ≤ y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
    have h1sq : 1 ≤ y ^ 2 := le_trans h1.le hy2
    have hexp : Real.exp y ≤ Real.exp M := Real.exp_le_exp.mpr hy
    calc |Real.exp y - 1 - y| = |Real.exp y - (1 + y)| := by ring_nf
      _ ≤ |Real.exp y| + |1 + y| := abs_sub _ _
      _ ≤ Real.exp M + (1 + |y|) := by
          gcongr
          · rw [abs_of_pos (Real.exp_pos _)]; exact hexp
          · exact (abs_add_le 1 y).trans (by rw [abs_one])
      _ ≤ (Real.exp M + 2) * y ^ 2 := by nlinarith [Real.exp_pos M]

/-- **The weight's expansion**: `|φ(x) − 1 − g x₀ x| ≤ C₁ x² + C₂ x⁴` with
`C₁ = (e^{g x₀²/2} + 2)·2g²x₀² + g/2`, `C₂ = (e^{g x₀²/2} + 2)·g²/2`. -/
theorem locWeight_expansion (hg : 0 ≤ g) (x : ℝ) :
    |locWeight g x₀ x - 1 - g * x₀ * x| ≤
      ((Real.exp (g * x₀ ^ 2 / 2) + 2) * (2 * g ^ 2 * x₀ ^ 2) + g / 2) * x ^ 2 +
        (Real.exp (g * x₀ ^ 2 / 2) + 2) * (g ^ 2 / 2) * x ^ 4 := by
  set y := g * x₀ * x - g / 2 * x ^ 2 with hy
  have hyM : y ≤ g * x₀ ^ 2 / 2 := by
    rw [hy]; nlinarith [mul_nonneg hg (sq_nonneg (x - x₀))]
  have h1 := abs_exp_sub_one_sub_le hyM
  have hy2 : y ^ 2 ≤ 2 * g ^ 2 * x₀ ^ 2 * x ^ 2 + g ^ 2 / 2 * x ^ 4 := by
    rw [hy]; nlinarith [sq_nonneg (g * x₀ * x + g / 2 * x ^ 2)]
  have e : locWeight g x₀ x - 1 - g * x₀ * x = (Real.exp y - 1 - y) + (y - g * x₀ * x) := by
    rw [locWeight, ← hy]; ring
  have e2 : |y - g * x₀ * x| = g / 2 * x ^ 2 := by
    rw [show y - g * x₀ * x = -(g / 2 * x ^ 2) by rw [hy]; ring, abs_neg,
      abs_of_nonneg (by positivity)]
  have hE : 0 ≤ Real.exp (g * x₀ ^ 2 / 2) + 2 := by positivity
  calc |locWeight g x₀ x - 1 - g * x₀ * x|
      ≤ |Real.exp y - 1 - y| + |y - g * x₀ * x| := by rw [e]; exact abs_add_le _ _
    _ ≤ (Real.exp (g * x₀ ^ 2 / 2) + 2) * y ^ 2 + g / 2 * x ^ 2 := by rw [e2]; linarith
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hy2 hE]

/-- The two constants of `locWeight_expansion`. -/
noncomputable def locC₁ (g x₀ : ℝ) : ℝ :=
  (Real.exp (g * x₀ ^ 2 / 2) + 2) * (2 * g ^ 2 * x₀ ^ 2) + g / 2

noncomputable def locC₂ (g x₀ : ℝ) : ℝ := (Real.exp (g * x₀ ^ 2 / 2) + 2) * (g ^ 2 / 2)

theorem locC₁_nonneg (hg : 0 ≤ g) : 0 ≤ locC₁ g x₀ := by unfold locC₁; positivity

theorem locC₂_nonneg (g x₀ : ℝ) : 0 ≤ locC₂ g x₀ := by unfold locC₂; positivity

theorem locWeight_expansion' (hg : 0 ≤ g) (x : ℝ) :
    |locWeight g x₀ x - 1 - g * x₀ * x| ≤ locC₁ g x₀ * x ^ 2 + locC₂ g x₀ * x ^ 4 :=
  locWeight_expansion hg x

end Weight

/-! ### Gibbs expectations: order and absolute values -/

section GibbsOrder

variable {L : ℝ → ℝ} {t : ℝ}

theorem gibbsExpectation_mono' (hZ : 0 < _root_.Laplace.partitionFunction L t) {f h : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * L x))))
    (hh : Integrable (fun x => h x * Real.exp (-(t * L x)))) (hfh : ∀ x, f x ≤ h x) :
    _root_.Laplace.gibbsExpectation L t f ≤ _root_.Laplace.gibbsExpectation L t h := by
  unfold _root_.Laplace.gibbsExpectation
  refine div_le_div_of_nonneg_right ?_ hZ.le
  exact integral_mono hf hh fun x => mul_le_mul_of_nonneg_right (hfh x) (Real.exp_pos _).le

theorem abs_gibbsExpectation_le' (hZ : 0 < _root_.Laplace.partitionFunction L t) (f : ℝ → ℝ) :
    |_root_.Laplace.gibbsExpectation L t f| ≤
      _root_.Laplace.gibbsExpectation L t (fun x => |f x|) := by
  unfold _root_.Laplace.gibbsExpectation
  rw [abs_div, abs_of_pos hZ]
  refine div_le_div_of_nonneg_right ?_ hZ.le
  calc |∫ x, f x * Real.exp (-(t * L x))| ≤ ∫ x, |f x * Real.exp (-(t * L x))| :=
        abs_integral_le_integral_abs
    _ = ∫ x, |f x| * Real.exp (-(t * L x)) := by
        congr 1; funext x; rw [abs_mul, abs_of_pos (Real.exp_pos _)]

theorem gibbsExpectation_nonneg' (hZ : 0 < _root_.Laplace.partitionFunction L t) {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ _root_.Laplace.gibbsExpectation L t f :=
  div_nonneg (integral_nonneg fun x => mul_nonneg (hf x) (Real.exp_pos _).le) hZ.le

theorem gibbsExpectation_one' (hZ : 0 < _root_.Laplace.partitionFunction L t) :
    _root_.Laplace.gibbsExpectation L t (fun _ => 1) = 1 := by
  unfold _root_.Laplace.gibbsExpectation _root_.Laplace.partitionFunction at *
  simp only [one_mul]
  exact div_self hZ.ne'

theorem integrable_abs_weighted {f : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * L x)))) :
    Integrable (fun x => |f x| * Real.exp (-(t * L x))) := by
  refine hf.norm.congr (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp]

/-- `⟨a f + b h⟩ = a ⟨f⟩ + b ⟨h⟩`. -/
theorem gibbsExpectation_lin {a b : ℝ} {f h : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * L x))))
    (hh : Integrable (fun x => h x * Real.exp (-(t * L x)))) :
    _root_.Laplace.gibbsExpectation L t (fun x => a * f x + b * h x) =
      a * _root_.Laplace.gibbsExpectation L t f + b * _root_.Laplace.gibbsExpectation L t h := by
  unfold _root_.Laplace.gibbsExpectation
  have e : ∀ x, (a * f x + b * h x) * Real.exp (-(t * L x)) =
      a * (f x * Real.exp (-(t * L x))) + b * (h x * Real.exp (-(t * L x))) := fun x => by ring
  simp only [e]
  rw [integral_add (hf.const_mul a) (hh.const_mul b), integral_const_mul, integral_const_mul]
  ring

end GibbsOrder

/-! ### The anharmonic measure -/

section Anharmonic

variable {lam alpha gamma : ℝ}

/-- Young with a free weight: `|x|³ ≤ (ε x² + x⁴/ε)/2`. -/
theorem abs_cube_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : |x| ^ 3 ≤ (ε * x ^ 2 + 1 / ε * x ^ 4) / 2 := by
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hx4 : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, hx2]
  have key : 2 * ε * |x| ^ 3 ≤ ε ^ 2 * x ^ 2 + x ^ 4 := by
    have h := sq_nonneg (ε * |x| - x ^ 2)
    have e : (ε * |x| - x ^ 2) ^ 2 = ε ^ 2 * x ^ 2 - 2 * ε * |x| ^ 3 + x ^ 4 := by
      rw [← hx2, ← hx4]; ring
    linarith [h, e]
  have hx4 : ε * (1 / ε * x ^ 4) = x ^ 4 := by field_simp
  rw [le_div_iff₀ two_pos]
  have : ε * (|x| ^ 3 * 2) ≤ ε * (ε * x ^ 2 + 1 / ε * x ^ 4) := by
    rw [mul_add, hx4]; nlinarith [key]
  exact le_of_mul_le_mul_left this hε

/-- `|x|⁵ ≤ (ε x⁴ + x⁶/ε)/2`. -/
theorem abs_fifth_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : |x| ^ 5 ≤ (ε * x ^ 4 + 1 / ε * x ^ 6) / 2 := by
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hx6 : (|x| ^ 3) ^ 2 = x ^ 6 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, hx2]; ring
  have hx4 : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, hx2]
  have hx6'' : |x| ^ 6 = x ^ 6 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_mul, hx2]
  have key : 2 * ε * |x| ^ 5 ≤ ε ^ 2 * x ^ 4 + x ^ 6 := by
    have h := sq_nonneg (ε * x ^ 2 - |x| ^ 3)
    have e : (ε * x ^ 2 - |x| ^ 3) ^ 2 = ε ^ 2 * x ^ 4 - 2 * ε * |x| ^ 5 + x ^ 6 := by
      rw [← hx2, ← hx4, ← hx6'']; ring
    linarith [h, e]
  have hx6' : ε * (1 / ε * x ^ 6) = x ^ 6 := by field_simp
  rw [le_div_iff₀ two_pos]
  have : ε * (|x| ^ 5 * 2) ≤ ε * (ε * x ^ 4 + 1 / ε * x ^ 6) := by
    rw [mul_add, hx6']; nlinarith [key]
  exact le_of_mul_le_mul_left this hε

variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

theorem integrable_pow_exp' {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
  integrable_pow_mul_exp_neg_t_anharmonic m hlam hgamma hdisc ht

theorem integrable_abs_pow_exp' {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Integrable (fun x : ℝ => |x| ^ m * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
  Laplace.OneD.integrable_abs_pow_mul_exp_neg_t_anharmonic m hlam hgamma hdisc ht

theorem partition_pos' {t : ℝ} (ht : 0 < t) :
    0 < _root_.Laplace.partitionFunction (anharmonicPotential lam alpha gamma) t :=
  partitionFunction_anharmonic_pos hlam hgamma hdisc ht

/-- Even moments are eventually bounded by `C/tᵏ`. -/
theorem evenMoment_bound (k : ℕ) :
    ∃ C T : ℝ, 0 ≤ C ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (2 * k)) ≤ C / t ^ k := by
  obtain ⟨K, T, hK, hT, h⟩ := Laplace.OneD.evenMoment_anharmonic_rate hlam hgamma hdisc k
  refine ⟨((2 * k - 1)‼ : ℝ) / lam ^ k + K, T,
    add_nonneg (div_nonneg (by positivity) (pow_nonneg hlam.le k)) hK, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have htk : 0 < t ^ k := by positivity
  have hM0 : 0 ≤ _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ (2 * k)) :=
    gibbsExpectation_nonneg' (partition_pos' hlam hgamma hdisc ht0) fun x => by
      rw [pow_mul]; positivity
  have hb := Laplace.OneD.rate_bounded ht1 hK (h ht)
  rw [abs_of_nonneg (mul_nonneg htk.le hM0),
    abs_of_nonneg (div_nonneg (by positivity) (pow_nonneg hlam.le k))] at hb
  rw [le_div_iff₀ htk, mul_comm]
  exact hb

omit hlam hgamma hdisc in
/-- Linearity for the three-term combinations used below. -/
theorem gibbs_sub_sub {t c : ℝ} {f h k : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
    (hh : Integrable (fun x => h x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
    (hk : Integrable (fun x => k x * Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) :
    _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => f x - h x - c * k x) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t f -
        _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t h -
        c * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t k := by
  unfold _root_.Laplace.gibbsExpectation
  have e : ∀ x, (f x - h x - c * k x) * Real.exp (-(t * anharmonicPotential lam alpha gamma x)) =
      (f x * Real.exp (-(t * anharmonicPotential lam alpha gamma x)) -
        h x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) -
        c * (k x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := fun x => by ring
  simp only [e]
  have h1 : Integrable (fun x => f x * Real.exp (-(t * anharmonicPotential lam alpha gamma x)) -
      h x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := hf.sub hh
  rw [integral_sub h1 (hk.const_mul c), integral_sub hf hh, integral_const_mul]
  ring

omit hlam hgamma hdisc in
/-- `⟨(a f + b h)/2⟩ = (a ⟨f⟩ + b ⟨h⟩)/2`. -/
theorem gibbs_half_comb {t a b : ℝ} {f h : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
    (hh : Integrable (fun x => h x * Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) :
    _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => (a * f x + b * h x) / 2) =
      (a * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t f +
        b * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t h) / 2 := by
  unfold _root_.Laplace.gibbsExpectation
  have e : ∀ x, (a * f x + b * h x) / 2 * Real.exp (-(t * anharmonicPotential lam alpha gamma x)) =
      (a * (f x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) +
        b * (h x * Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) / 2 := fun x => by ring
  simp only [e]
  rw [integral_div, integral_add (hf.const_mul a) (hh.const_mul b), integral_const_mul,
    integral_const_mul]
  ring

/-- **Odd absolute moments from even ones**: `⟨|x|³⟩ ≤ K/(t√t)` eventually. -/
theorem absMoment_three_bound :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => |x| ^ 3) ≤
        K / (t * Real.sqrt t) := by
  obtain ⟨C₂, T₂, hC₂, hT₂, h₂⟩ := evenMoment_bound hlam hgamma hdisc 1
  obtain ⟨C₄, T₄, hC₄, hT₄, h₄⟩ := evenMoment_bound hlam hgamma hdisc 2
  refine ⟨(C₂ + C₄) / 2, max T₂ T₄, by positivity, le_max_of_le_left hT₂, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith [le_max_left T₂ T₄]
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  set ε := 1 / Real.sqrt t with hε
  have hε0 : 0 < ε := by positivity
  have hZ := partition_pos' hlam hgamma hdisc ht0
  have hcomb : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => (ε * x ^ 2 + (1 / ε) * x ^ 4) / 2) =
      (ε * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2)
        + (1 / ε) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4)) / 2 :=
    gibbs_half_comb (integrable_pow_exp' hlam hgamma hdisc ht0 2)
      (integrable_pow_exp' hlam hgamma hdisc ht0 4)
  have hint : Integrable (fun x : ℝ => (ε * x ^ 2 + 1 / ε * x ^ 4) / 2 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have h1 := ((integrable_pow_exp' hlam hgamma hdisc ht0 2).const_mul ε).add
      ((integrable_pow_exp' hlam hgamma hdisc ht0 4).const_mul (1 / ε))
    refine (h1.div_const 2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hmono := gibbsExpectation_mono' hZ (integrable_abs_pow_exp' hlam hgamma hdisc ht0 3) hint
    (fun x => abs_cube_le hε0 x)
  have hM2 := h₂ (le_trans (le_max_left _ _) ht)
  have hM4 := h₄ (le_trans (le_max_right _ _) ht)
  simp only [pow_one, show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl] at hM2 hM4
  calc _ ≤ _ := hmono
    _ = _ := hcomb
    _ ≤ (ε * (C₂ / t) + (1 / ε) * (C₄ / t ^ 2)) / 2 := by
        gcongr
    _ = (C₂ + C₄) / 2 / (t * Real.sqrt t) := by
        have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
        have h1 : ε * (C₂ / t) = C₂ / (t * Real.sqrt t) := by rw [hε]; field_simp
        have h2 : 1 / ε * (C₄ / t ^ 2) = C₄ / (t * Real.sqrt t) := by
          rw [hε, one_div_one_div, mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
          linear_combination (C₄ * t) * hsq
        rw [h1, h2]
        ring

/-- `⟨|x|⁵⟩ ≤ K/(t²√t)` eventually. -/
theorem absMoment_five_bound :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => |x| ^ 5) ≤
        K / (t ^ 2 * Real.sqrt t) := by
  obtain ⟨C₄, T₄, hC₄, hT₄, h₄⟩ := evenMoment_bound hlam hgamma hdisc 2
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  refine ⟨(C₄ + C₆) / 2, max T₄ T₆, by positivity, le_max_of_le_left hT₄, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith [le_max_left T₄ T₆]
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  set ε := 1 / Real.sqrt t with hε
  have hε0 : 0 < ε := by positivity
  have hZ := partition_pos' hlam hgamma hdisc ht0
  have hcomb : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => (ε * x ^ 4 + (1 / ε) * x ^ 6) / 2) =
      (ε * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4)
        + (1 / ε) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6)) / 2 :=
    gibbs_half_comb (integrable_pow_exp' hlam hgamma hdisc ht0 4)
      (integrable_pow_exp' hlam hgamma hdisc ht0 6)
  have hint : Integrable (fun x : ℝ => (ε * x ^ 4 + 1 / ε * x ^ 6) / 2 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have h1 := ((integrable_pow_exp' hlam hgamma hdisc ht0 4).const_mul ε).add
      ((integrable_pow_exp' hlam hgamma hdisc ht0 6).const_mul (1 / ε))
    refine (h1.div_const 2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hmono := gibbsExpectation_mono' hZ (integrable_abs_pow_exp' hlam hgamma hdisc ht0 5) hint
    (fun x => abs_fifth_le hε0 x)
  have hM4 := h₄ (le_trans (le_max_left _ _) ht)
  have hM6 := h₆ (le_trans (le_max_right _ _) ht)
  simp only [show 2 * 2 = 4 from rfl, show 2 * 3 = 6 from rfl] at hM4 hM6
  calc _ ≤ _ := hmono
    _ = _ := hcomb
    _ ≤ (ε * (C₄ / t ^ 2) + (1 / ε) * (C₆ / t ^ 3)) / 2 := by
        gcongr
    _ = (C₄ + C₆) / 2 / (t ^ 2 * Real.sqrt t) := by
        have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
        have h1 : ε * (C₄ / t ^ 2) = C₄ / (t ^ 2 * Real.sqrt t) := by rw [hε]; field_simp
        have h2 : 1 / ε * (C₆ / t ^ 3) = C₆ / (t ^ 2 * Real.sqrt t) := by
          rw [hε, one_div_one_div, mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
          linear_combination (C₆ * t ^ 2) * hsq
        rw [h1, h2]
        ring

/-! ### The localised mean -/

variable {g x₀ : ℝ}

theorem integrable_pow_locWeight (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m * locWeight g x₀ x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  have h := (integrable_pow_exp' hlam hgamma hdisc ht m).bdd_mul (c := Real.exp (g * x₀ ^ 2 / 2))
    (continuous_locWeight g x₀).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (locWeight_pos x)]; exact locWeight_le hg x)
  refine h.congr (Eventually.of_forall fun x => ?_)
  change locWeight g x₀ x * (x ^ m * _) = _
  ring

theorem integrable_locWeight (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ =>
      locWeight g x₀ x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  simpa using integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 0

theorem integrable_mul_locWeight (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ =>
      x * locWeight g x₀ x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  simpa using integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 1

omit hlam hgamma hdisc in
/-- The mean of the localised anharmonic measure `e^{−tℓ(x) − (g/2)(x − x₀)²}`. -/
noncomputable def localisedMean (lam alpha gamma g x₀ t : ℝ) : ℝ :=
  (∫ x : ℝ, x * Real.exp (-(t * anharmonicPotential lam alpha gamma x) - g / 2 * (x - x₀) ^ 2)) /
    ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x) - g / 2 * (x - x₀) ^ 2)

/-- `⟨x⟩_loc = ⟨x φ⟩_t / ⟨φ⟩_t` under the anharmonic Gibbs measure, `φ` the localised weight. -/
theorem localisedMean_eq_ratio {t : ℝ} (ht : 0 < t) (g x₀ : ℝ) :
    localisedMean lam alpha gamma g x₀ t =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x * locWeight g x₀ x) /
        _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (locWeight g x₀) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hc : 0 < Real.exp (-(g * x₀ ^ 2 / 2)) := Real.exp_pos _
  have e : ∀ x, Real.exp (-(t * anharmonicPotential lam alpha gamma x) - g / 2 * (x - x₀) ^ 2) =
      Real.exp (-(g * x₀ ^ 2 / 2)) *
        (locWeight g x₀ x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    intro x
    unfold locWeight
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have e2 : ∀ x : ℝ, x * (Real.exp (-(g * x₀ ^ 2 / 2)) *
      (locWeight g x₀ x * Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) =
      Real.exp (-(g * x₀ ^ 2 / 2)) *
        (x * locWeight g x₀ x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    fun x => by ring
  unfold localisedMean _root_.Laplace.gibbsExpectation
  simp only [e, e2]
  rw [integral_const_mul, integral_const_mul, mul_div_mul_left _ _ hc.ne',
    div_div_div_cancel_right₀ hZ.ne']

/-- Numerator expansion: `|⟨xφ⟩ − ⟨x⟩ − g x₀ ⟨x²⟩| ≤ C₁ ⟨|x|³⟩ + C₂ ⟨|x|⁵⟩`. -/
theorem locNumerator_expansion (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x * locWeight g x₀ x) -
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) -
      g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2)| ≤
      locC₁ g x₀ *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => |x| ^ 3) +
        locC₂ g x₀ *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => |x| ^ 5) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_mul_locWeight hlam hgamma hdisc hg ht (x₀ := x₀)
  have h1 := integrable_pow_exp' hlam hgamma hdisc ht 1
  simp only [pow_one] at h1
  have h2 := integrable_pow_exp' hlam hgamma hdisc ht 2
  have hF : Integrable (fun x => (x * locWeight g x₀ x - x - g * x₀ * x ^ 2) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (hf.sub h1).sub (h2.const_mul (g * x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hpt : ∀ x : ℝ, |x * locWeight g x₀ x - x - g * x₀ * x ^ 2| ≤
      locC₁ g x₀ * |x| ^ 3 + locC₂ g x₀ * |x| ^ 5 := by
    intro x
    have e : x * locWeight g x₀ x - x - g * x₀ * x ^ 2 =
        x * (locWeight g x₀ x - 1 - g * x₀ * x) := by ring
    rw [e, abs_mul]
    calc |x| * |locWeight g x₀ x - 1 - g * x₀ * x|
        ≤ |x| * (locC₁ g x₀ * x ^ 2 + locC₂ g x₀ * x ^ 4) :=
          mul_le_mul_of_nonneg_left (locWeight_expansion' hg x) (abs_nonneg x)
      _ = locC₁ g x₀ * |x| ^ 3 + locC₂ g x₀ * |x| ^ 5 := by
          have h4 : x ^ 4 = |x| ^ 4 := by
            rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
          rw [← sq_abs x, h4]
          ring
  have hG : Integrable (fun x => (locC₁ g x₀ * |x| ^ 3 + locC₂ g x₀ * |x| ^ 5) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((integrable_abs_pow_exp' hlam hgamma hdisc ht 3).const_mul (locC₁ g x₀)).add
      ((integrable_abs_pow_exp' hlam hgamma hdisc ht 5).const_mul (locC₂ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← gibbs_sub_sub hf h1 h2,
    ← gibbsExpectation_lin (integrable_abs_pow_exp' hlam hgamma hdisc ht 3)
      (integrable_abs_pow_exp' hlam hgamma hdisc ht 5)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG hpt)

/-- Denominator expansion: `|⟨φ⟩ − 1 − g x₀ ⟨x⟩| ≤ C₁ ⟨x²⟩ + C₂ ⟨x⁴⟩`. -/
theorem locDenominator_expansion (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (locWeight g x₀) -
      1 - g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x)| ≤
      locC₁ g x₀ *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ 2) +
        locC₂ g x₀ *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ 4) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_locWeight hlam hgamma hdisc hg ht (x₀ := x₀)
  have h0 := integrable_pow_exp' hlam hgamma hdisc ht 0
  simp only [pow_zero] at h0
  have h1 := integrable_pow_exp' hlam hgamma hdisc ht 1
  simp only [pow_one] at h1
  have hF : Integrable (fun x => (locWeight g x₀ x - 1 - g * x₀ * x) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (hf.sub h0).sub (h1.const_mul (g * x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locC₁ g x₀ * x ^ 2 + locC₂ g x₀ * x ^ 4) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((integrable_pow_exp' hlam hgamma hdisc ht 2).const_mul (locC₁ g x₀)).add
      ((integrable_pow_exp' hlam hgamma hdisc ht 4).const_mul (locC₂ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← gibbsExpectation_one' hZ, ← gibbs_sub_sub hf h0 h1,
    ← gibbsExpectation_lin (integrable_pow_exp' hlam hgamma hdisc ht 2)
      (integrable_pow_exp' hlam hgamma hdisc ht 4)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x => locWeight_expansion' hg x)

omit hlam hgamma hdisc in
theorem sqrt_le_self_of_one_le {t : ℝ} (ht : 1 ≤ t) : Real.sqrt t ≤ t := by
  have ht0 : 0 < t := by linarith
  calc Real.sqrt t ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = t := Real.sqrt_sq ht0.le

/-- `|t ⟨xφ⟩ − (−α/(2λ²) + g x₀/λ)| ≤ K/√t` eventually. -/
theorem locNumerator_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x * locWeight g x₀ x) - (-alpha / (2 * lam ^ 2) + g * x₀ / lam)| ≤
        K / Real.sqrt t := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := Laplace.OneD.mean_anharmonic_O2_rate hlam hgamma hdisc
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := Laplace.OneD.evenMoment_anharmonic_rate hlam hgamma hdisc 1
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := absMoment_three_bound hlam hgamma hdisc
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := absMoment_five_bound hlam hgamma hdisc
  have hC₁ := locC₁_nonneg (x₀ := x₀) hg
  have hC₂ := locC₂_nonneg g x₀
  refine ⟨K₁ + |g * x₀| * K₂ + locC₁ g x₀ * K₃ + locC₂ g x₀ * K₅, max (max T₁ T₂) (max T₃ T₅),
    by positivity, le_max_of_le_left (le_max_of_le_left hT₁), fun {t} ht => ?_⟩
  have hT₁t : T₁ ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht)
  have hT₂t : T₂ ≤ t := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ht)
  have hT₃t : T₃ ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) ht)
  have hT₅t : T₅ ≤ t := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) ht)
  have ht1 : 1 ≤ t := hT₁.trans hT₁t
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst : Real.sqrt t ≤ t := sqrt_le_self_of_one_le ht1
  have e₁ := h₁ hT₁t
  have e₂ : |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 2) - 1 / lam| ≤ K₂ / t := by
    simpa [Nat.doubleFactorial] using h₂ hT₂t
  have hR := (locNumerator_expansion hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (mul_le_mul_of_nonneg_left (h₃ hT₃t) hC₁)
      (mul_le_mul_of_nonneg_left (h₅ hT₅t) hC₂))
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x * locWeight g x₀ x) with hN
  set M₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x) with hM₁
  set M₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2) with hM₂
  have key : t * N - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) =
      (t * M₁ - -alpha / (2 * lam ^ 2)) + g * x₀ * (t * M₂ - 1 / lam) +
        t * (N - M₁ - g * x₀ * M₂) := by ring
  have hA : K₁ / t ≤ K₁ / Real.sqrt t := div_le_div_of_nonneg_left hK₁ hs0 hst
  have hB : K₂ / t ≤ K₂ / Real.sqrt t := div_le_div_of_nonneg_left hK₂ hs0 hst
  have hC : t * (locC₁ g x₀ * (K₃ / (t * Real.sqrt t)) +
      locC₂ g x₀ * (K₅ / (t ^ 2 * Real.sqrt t))) =
      locC₁ g x₀ * K₃ / Real.sqrt t + locC₂ g x₀ * K₅ / (t * Real.sqrt t) := by
    field_simp
  have hD : locC₂ g x₀ * K₅ / (t * Real.sqrt t) ≤ locC₂ g x₀ * K₅ / Real.sqrt t :=
    div_le_div_of_nonneg_left (mul_nonneg hC₂ hK₅) hs0 (le_mul_of_one_le_left hs0.le ht1)
  rw [key]
  calc |t * M₁ - -alpha / (2 * lam ^ 2) + g * x₀ * (t * M₂ - 1 / lam) +
        t * (N - M₁ - g * x₀ * M₂)|
      ≤ |t * M₁ - -alpha / (2 * lam ^ 2)| + |g * x₀ * (t * M₂ - 1 / lam)| +
          |t * (N - M₁ - g * x₀ * M₂)| := abs_add_three _ _ _
    _ = |t * M₁ - -alpha / (2 * lam ^ 2)| + |g * x₀| * |t * M₂ - 1 / lam| +
          t * |N - M₁ - g * x₀ * M₂| := by rw [abs_mul (g * x₀), abs_mul t, abs_of_pos ht0]
    _ ≤ K₁ / t + |g * x₀| * (K₂ / t) + t * (locC₁ g x₀ * (K₃ / (t * Real.sqrt t)) +
          locC₂ g x₀ * (K₅ / (t ^ 2 * Real.sqrt t))) := by gcongr
    _ = K₁ / t + |g * x₀| * (K₂ / t) +
          (locC₁ g x₀ * K₃ / Real.sqrt t + locC₂ g x₀ * K₅ / (t * Real.sqrt t)) := by rw [hC]
    _ ≤ K₁ / Real.sqrt t + |g * x₀| * (K₂ / Real.sqrt t) +
          (locC₁ g x₀ * K₃ / Real.sqrt t + locC₂ g x₀ * K₅ / Real.sqrt t) := by gcongr
    _ = (K₁ + |g * x₀| * K₂ + locC₁ g x₀ * K₃ + locC₂ g x₀ * K₅) / Real.sqrt t := by ring

/-- `|⟨φ⟩ − 1| ≤ K/t` eventually. -/
theorem locDenominator_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (locWeight g x₀) -
        1| ≤ K / t := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := Laplace.OneD.mean_anharmonic_O2_rate hlam hgamma hdisc
  obtain ⟨C₂, T₂, hC₂, hT₂, h₂⟩ := evenMoment_bound hlam hgamma hdisc 1
  obtain ⟨C₄, T₄, hC₄, hT₄, h₄⟩ := evenMoment_bound hlam hgamma hdisc 2
  have hC₁ := locC₁_nonneg (x₀ := x₀) hg
  have hC₂' := locC₂_nonneg g x₀
  refine ⟨|g * x₀| * (|-alpha / (2 * lam ^ 2)| + K₁) + locC₁ g x₀ * C₂ + locC₂ g x₀ * C₄,
    max T₁ (max T₂ T₄), by positivity, le_max_of_le_left hT₁, fun {t} ht => ?_⟩
  have hT₁t : T₁ ≤ t := le_trans (le_max_left _ _) ht
  have hT₂t : T₂ ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) ht)
  have hT₄t : T₄ ≤ t := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) ht)
  have ht1 : 1 ≤ t := hT₁.trans hT₁t
  have ht0 : 0 < t := by linarith
  have htt : t ≤ t ^ 2 := by nlinarith
  have hM2 := h₂ hT₂t
  have hM4 := h₄ hT₄t
  simp only [pow_one, show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl] at hM2 hM4
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hD
  set M₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x) with hM₁
  have hM1 : |M₁| ≤ (|-alpha / (2 * lam ^ 2)| + K₁) / t := by
    have hb := Laplace.OneD.rate_bounded ht1 hK₁ (h₁ hT₁t)
    rw [abs_mul, abs_of_pos ht0] at hb
    rw [le_div_iff₀ ht0, mul_comm]
    exact hb
  have hR := (locDenominator_expansion hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hM2 hC₁) (mul_le_mul_of_nonneg_left hM4 hC₂'))
  have key : D - 1 = g * x₀ * M₁ + (D - 1 - g * x₀ * M₁) := by ring
  rw [key]
  calc |g * x₀ * M₁ + (D - 1 - g * x₀ * M₁)|
      ≤ |g * x₀ * M₁| + |D - 1 - g * x₀ * M₁| := abs_add_le _ _
    _ = |g * x₀| * |M₁| + |D - 1 - g * x₀ * M₁| := by rw [abs_mul]
    _ ≤ |g * x₀| * ((|-alpha / (2 * lam ^ 2)| + K₁) / t) +
          (locC₁ g x₀ * (C₂ / t) + locC₂ g x₀ * (C₄ / t ^ 2)) := by gcongr
    _ ≤ |g * x₀| * ((|-alpha / (2 * lam ^ 2)| + K₁) / t) +
          (locC₁ g x₀ * (C₂ / t) + locC₂ g x₀ * (C₄ / t)) := by gcongr
    _ = (|g * x₀| * (|-alpha / (2 * lam ^ 2)| + K₁) + locC₁ g x₀ * C₂ + locC₂ g x₀ * C₄) / t := by
          ring

/-- **The localised mean at leading order** (eq:mean's `−½ S (tT:S) + g S (x₀ − x*)` with
`S ≈ 1/(λt)`, for the exact anharmonic localised measure):
`|t ⟨x⟩_loc − (−α/(2λ²) + g x₀/λ)| ≤ K/√t` for `t ≥ T`. -/
theorem localisedMean_anharmonic_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * localisedMean lam alpha gamma g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam)| ≤
        K / Real.sqrt t := by
  obtain ⟨KN, TN, hKN, hTN, hN⟩ := locNumerator_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate hlam hgamma hdisc hg (x₀ := x₀)
  set c := -alpha / (2 * lam ^ 2) + g * x₀ / lam with hc
  refine ⟨2 * KN + 2 * |c| * KD, max (max TN TD) (2 * KD), by positivity,
    le_max_of_le_left (le_max_of_le_left hTN), fun {t} ht => ?_⟩
  have hTNt : TN ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht)
  have hTDt : TD ≤ t := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ht)
  have h2K : 2 * KD ≤ t := le_trans (le_max_right _ _) ht
  have ht1 : 1 ≤ t := hTN.trans hTNt
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst : Real.sqrt t ≤ t := sqrt_le_self_of_one_le ht1
  rw [localisedMean_eq_ratio hlam hgamma hdisc ht0]
  have eN := hN hTNt
  have eD := hD hTDt
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x * locWeight g x₀ x) with hNdef
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
  have hDhalf : 1 / 2 ≤ D := by
    have h1 : KD / t ≤ 1 / 2 := by rw [div_le_iff₀ ht0]; linarith
    have h2 := (abs_le.mp (eD.trans h1)).1
    linarith
  have hD0 : 0 < D := by linarith
  have hDne : D ≠ 0 := hD0.ne'
  have key : t * (N / D) - c = ((t * N - c) + c * (1 - D)) / D := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  have hKD' : KD / t ≤ KD / Real.sqrt t := div_le_div_of_nonneg_left hKD hs0 hst
  calc |(t * N - c) + c * (1 - D)| ≤ |t * N - c| + |c| * |1 - D| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ KN / Real.sqrt t + |c| * (KD / t) := by rw [abs_sub_comm 1 D]; gcongr
    _ ≤ KN / Real.sqrt t + |c| * (KD / Real.sqrt t) := by gcongr
    _ = (2 * KN + 2 * |c| * KD) / Real.sqrt t * (1 / 2) := by ring
    _ ≤ (2 * KN + 2 * |c| * KD) / Real.sqrt t * D := by gcongr

/-! ### Against the note's displayed formula -/

omit hlam hgamma hdisc in
/-- eq:mean's right-hand side in one dimension: `−½ S (tT:S) + g S (x₀ − x*)` with
`S = 1/(tλ + g)`, `T = α`, `x* = 0`. -/
noncomputable def locLeading (lam alpha g x₀ t : ℝ) : ℝ :=
  -alpha * t / (2 * (t * lam + g) ^ 2) + g * x₀ / (t * lam + g)

omit hgamma hdisc in
/-- The displayed formula differs from its leading term `c/t` by `O(1/t²)`. -/
theorem locLeading_sub_le (hg : 0 ≤ g) {t : ℝ} (ht : 1 ≤ t) :
    |locLeading lam alpha g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) / t| ≤
      (|alpha| / 2 * (2 * lam * g + g ^ 2) / lam ^ 4 + g ^ 2 * |x₀| / lam ^ 2) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < t * lam + g := by positivity
  have e : locLeading lam alpha g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) / t =
      alpha / 2 * ((2 * t * lam * g + g ^ 2) / ((t * lam + g) ^ 2 * lam ^ 2 * t)) -
        g ^ 2 * x₀ / ((t * lam + g) * lam * t) := by
    unfold locLeading
    field_simp
    ring
  have hsq : t ^ 2 * lam ^ 2 ≤ (t * lam + g) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ht0.le hlam.le) hg, sq_nonneg g]
  have hA : (2 * t * lam * g + g ^ 2) / ((t * lam + g) ^ 2 * lam ^ 2 * t) ≤
      (2 * lam * g + g ^ 2) / lam ^ 4 / t ^ 2 := by
    have hnum : 2 * t * lam * g + g ^ 2 ≤ t * (2 * lam * g + g ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg g) (sub_nonneg.2 ht)]
    have hden : lam ^ 4 * t ^ 3 ≤ (t * lam + g) ^ 2 * lam ^ 2 * t := by
      calc lam ^ 4 * t ^ 3 = t ^ 2 * lam ^ 2 * (lam ^ 2 * t) := by ring
        _ ≤ (t * lam + g) ^ 2 * (lam ^ 2 * t) := mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = (t * lam + g) ^ 2 * lam ^ 2 * t := by ring
    calc (2 * t * lam * g + g ^ 2) / ((t * lam + g) ^ 2 * lam ^ 2 * t)
        ≤ t * (2 * lam * g + g ^ 2) / (lam ^ 4 * t ^ 3) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = (2 * lam * g + g ^ 2) / lam ^ 4 / t ^ 2 := by
          field_simp
  have hB : g ^ 2 * |x₀| / ((t * lam + g) * lam * t) ≤ g ^ 2 * |x₀| / lam ^ 2 / t ^ 2 := by
    have hden : lam ^ 2 * t ^ 2 ≤ (t * lam + g) * lam * t := by
      nlinarith [mul_nonneg (mul_nonneg hg hlam.le) ht0.le]
    calc g ^ 2 * |x₀| / ((t * lam + g) * lam * t) ≤ g ^ 2 * |x₀| / (lam ^ 2 * t ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = g ^ 2 * |x₀| / lam ^ 2 / t ^ 2 := by rw [div_div]
  rw [e]
  calc |alpha / 2 * ((2 * t * lam * g + g ^ 2) / ((t * lam + g) ^ 2 * lam ^ 2 * t)) -
        g ^ 2 * x₀ / ((t * lam + g) * lam * t)|
      ≤ |alpha / 2 * ((2 * t * lam * g + g ^ 2) / ((t * lam + g) ^ 2 * lam ^ 2 * t))| +
          |g ^ 2 * x₀ / ((t * lam + g) * lam * t)| := abs_sub _ _
    _ = |alpha| / 2 * ((2 * t * lam * g + g ^ 2) / ((t * lam + g) ^ 2 * lam ^ 2 * t)) +
          g ^ 2 * |x₀| / ((t * lam + g) * lam * t) := by
        rw [abs_mul, abs_div, abs_two, abs_of_nonneg (by positivity : (0:ℝ) ≤ _ / _),
          abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ g ^ 2),
          abs_of_pos (by positivity : (0:ℝ) < (t * lam + g) * lam * t)]
    _ ≤ |alpha| / 2 * ((2 * lam * g + g ^ 2) / lam ^ 4 / t ^ 2) +
          g ^ 2 * |x₀| / lam ^ 2 / t ^ 2 := by gcongr
    _ = (|alpha| / 2 * (2 * lam * g + g ^ 2) / lam ^ 4 + g ^ 2 * |x₀| / lam ^ 2) / t ^ 2 := by
        ring

/-- **The localised mean against eq:mean's displayed formula**: `|⟨x⟩_loc − P_t| ≤ K/(t√t)`
with `P_t = −αt/(2(tλ + g)²) + g x₀/(tλ + g)`. -/
theorem localisedMean_sub_locLeading_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |localisedMean lam alpha gamma g x₀ t - locLeading lam alpha g x₀ t| ≤
        K / (t * Real.sqrt t) := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedMean_anharmonic_rate hlam hgamma hdisc hg (x₀ := x₀)
  set c := -alpha / (2 * lam ^ 2) + g * x₀ / lam with hc
  set K' := |alpha| / 2 * (2 * lam * g + g ^ 2) / lam ^ 4 + g ^ 2 * |x₀| / lam ^ 2 with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨K + K', T, by positivity, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst : Real.sqrt t ≤ t := sqrt_le_self_of_one_le ht1
  set m := localisedMean lam alpha gamma g x₀ t with hm
  have h1 : |m - c / t| ≤ K / (t * Real.sqrt t) := by
    have e : m - c / t = (t * m - c) / t := by field_simp
    rw [e, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    calc |t * m - c| ≤ K / Real.sqrt t := h ht
      _ = K / (t * Real.sqrt t) * t := by field_simp
  have h2 := locLeading_sub_le hlam hg ht1 (alpha := alpha) (x₀ := x₀)
  have h3 : K' / t ^ 2 ≤ K' / (t * Real.sqrt t) :=
    div_le_div_of_nonneg_left hK'0 (by positivity)
      (by calc t * Real.sqrt t ≤ t * t := mul_le_mul_of_nonneg_left hst ht0.le
        _ = t ^ 2 := by ring)
  calc |m - locLeading lam alpha g x₀ t|
      = |(m - c / t) - (locLeading lam alpha g x₀ t - c / t)| := by rw [sub_sub_sub_cancel_right]
    _ ≤ |m - c / t| + |locLeading lam alpha g x₀ t - c / t| := abs_sub _ _
    _ ≤ K / (t * Real.sqrt t) + K' / (t * Real.sqrt t) := add_le_add h1 (h2.trans h3)
    _ = (K + K') / (t * Real.sqrt t) := by ring

end Anharmonic

end Laplace.Multi
