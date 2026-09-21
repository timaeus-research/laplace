/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.MorseBottNormalForm

/-!
# The singular power normal form `L = a(y) x^{2k}`: what expectation values know about λ

A non-isolated zero set with a *singular* transverse normal form: `L(x, y) = a(y) x^{2k}` on
`ℝ × ℝⁿ`, `k ≥ 1`, with a continuous weight `a ≥ a₀ > 0` and a tangential cutoff `χ(y)`. The
transverse integrals are generalised Gaussians, exactly in `t`
(`integral_pow_mul_exp_neg_mul_pow`): `∫ x^m e^{-b x^{2k}} dx = b^{-(m+1)/2k} c_m`, where
`c_m = ∫ u^m e^{-u^{2k}} du = Γ((m+1)/2k)/k` for even `m` (`gmom_even_eq_Gamma`). Hence
(`spExp_tangential`, `spExp_transverse`, `mul_spExp_spLoss`, `neg_log_integral_spWeight`), with
`p = 1/2k` and `dμ_k = χ a^{-p} dy / ∫ χ a^{-p}`:

* `E_t[yᵛ] = ∫ yᵛ dμ_k` — the tangential monomials see the singular density `a^{-1/2k}`;
* `t^{q/k} E_t[x^{2q} yᵛ] = (c_{2q}/c_0) ∫ yᵛ a^{-q/k} dμ_k`;
* `t E_t[L] = 1/2k = λ` — the energy observable is the RLCT;
* `-log Z_t = (1/2k) log t - log (c_0 ∫ χ a^{-p})` — `λ = 1/2k`, multiplicity one.

**Identification** (`sp_exponent_identification`, `sp_identification`): the decay exponent of
`E_t[x²]` identifies `k`; the tangential moments identify `μ_k`; the moments of `x² yᵛ` at one
temperature then identify `a` on `{χ ≠ 0}` (moment determinacy and
`a^{-3/2k}/a^{-1/2k} = a^{-1/k}`).
Astra (`research_germbij_next_arc_v1`, arc C): a singular transverse normal-form theorem, not yet
a general theorem about singular non-isolated zero sets.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {n : ℕ}

/-! ### Generalised Gaussian moments -/

/-- `c_m = ∫ u^m e^{-u^{2k}} du`. -/
noncomputable def gmom (k m : ℕ) : ℝ := ∫ u : ℝ, u ^ m * Real.exp (-u ^ (2 * k))

/-- `x^{2k} ≥ x² - 1` for `k ≥ 1`. -/
theorem sq_sub_one_le_pow (k : ℕ) (hk : 1 ≤ k) (x : ℝ) : x ^ 2 - 1 ≤ x ^ (2 * k) := by
  rw [pow_mul]
  by_cases h : x ^ 2 ≤ 1
  · have : 0 ≤ (x ^ 2) ^ k := by positivity
    linarith
  · push Not at h
    have := le_self_pow₀ h.le (by omega : k ≠ 0)
    linarith

/-- `e^{-b x^{2k}} ≤ e^{b} e^{-b x²}` for `b ≥ 0`. -/
theorem exp_neg_mul_pow_le {b : ℝ} (hb : 0 ≤ b) (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    Real.exp (-(b * x ^ (2 * k))) ≤ Real.exp b * Real.exp (-(b * x ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := sq_sub_one_le_pow k hk x
  nlinarith

theorem continuous_pow_mul_exp_neg_mul_pow (b : ℝ) (k m : ℕ) :
    Continuous fun x : ℝ ↦ x ^ m * Real.exp (-(b * x ^ (2 * k))) := by fun_prop

/-- `x^m e^{-b x^{2k}}` is integrable on `ℝ` for `b > 0`. -/
theorem integrable_pow_mul_exp_neg_mul_pow {b : ℝ} (hb : 0 < b) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    Integrable fun x : ℝ ↦ x ^ m * Real.exp (-(b * x ^ (2 * k))) := by
  have hg : Integrable fun x : ℝ ↦ x ^ m * Real.exp (-b * x ^ 2) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (s := (m : ℝ)) (by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
    simpa [Real.rpow_natCast] using this
  refine (hg.norm.const_mul (Real.exp b)).mono'
    (continuous_pow_mul_exp_neg_mul_pow b k m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp, Real.abs_exp,
    neg_mul]
  have := exp_neg_mul_pow_le hb.le k hk x
  calc |x ^ m| * Real.exp (-(b * x ^ (2 * k)))
      ≤ |x ^ m| * (Real.exp b * Real.exp (-(b * x ^ 2))) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = Real.exp b * (|x ^ m| * Real.exp (-(b * x ^ 2))) := by ring

theorem integrable_gmom (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    Integrable fun u : ℝ ↦ u ^ m * Real.exp (-u ^ (2 * k)) := by
  have := integrable_pow_mul_exp_neg_mul_pow one_pos k hk m
  simpa using this

/-- **The even generalised Gaussian moments**: `c_{2q} = Γ((2q+1)/2k) / k`. -/
theorem gmom_even_eq_Gamma (k : ℕ) (hk : 1 ≤ k) (q : ℕ) :
    gmom k (2 * q) = Real.Gamma ((2 * q + 1) / (2 * k)) / k := by
  unfold gmom
  have heven : (fun u : ℝ ↦ u ^ (2 * q) * Real.exp (-u ^ (2 * k))) =
      fun u ↦ (fun s : ℝ ↦ s ^ (2 * q) * Real.exp (-s ^ (2 * k))) |u| := by
    funext u
    simp only [pow_mul, sq_abs]
  rw [heven, integral_comp_abs (f := fun s : ℝ ↦ s ^ (2 * q) * Real.exp (-s ^ (2 * k)))]
  have hk' : (0 : ℝ) < 2 * k := by positivity
  have hq' : (-1 : ℝ) < 2 * q := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have h := integral_rpow_mul_exp_neg_rpow hk' hq'
  have hconv : (∫ x in Ioi (0 : ℝ), x ^ (2 * q : ℝ) * Real.exp (-x ^ (2 * k : ℝ))) =
      ∫ x in Ioi (0 : ℝ), x ^ (2 * q) * Real.exp (-x ^ (2 * k)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    rw [show (2 * q : ℝ) = ((2 * q : ℕ) : ℝ) by push_cast; ring,
      show (2 * k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      Real.rpow_natCast]
  rw [hconv] at h
  rw [h]
  field_simp

theorem gmom_even_pos (k : ℕ) (hk : 1 ≤ k) (q : ℕ) : 0 < gmom k (2 * q) := by
  rw [gmom_even_eq_Gamma k hk q]
  have : 0 < Real.Gamma ((2 * q + 1) / (2 * k)) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-- `c_{2k} / c_0 = 1/(2k)`: the energy ratio. -/
theorem gmom_two_k_div_zero (k : ℕ) (hk : 1 ≤ k) :
    gmom k (2 * k) / gmom k 0 = 1 / (2 * k) := by
  have h0 := gmom_even_eq_Gamma k hk 0
  have hk2 := gmom_even_eq_Gamma k hk k
  simp only [mul_zero, Nat.cast_zero, zero_add] at h0
  rw [hk2, h0]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have harg : ((2 * k + 1 : ℝ)) / (2 * k) = 1 / (2 * k) + 1 := by
    field_simp
    ring
  rw [harg, Real.Gamma_add_one (by positivity)]
  have hG : 0 < Real.Gamma (1 / (2 * k)) := Real.Gamma_pos_of_pos (by positivity)
  field_simp

/-! ### Exact scaling -/

/-- **Generalised Gaussian scaling**: `∫ x^m e^{-b x^{2k}} dx = b^{-(m+1)/2k} c_m` for `b > 0`. -/
theorem integral_pow_mul_exp_neg_mul_pow {b : ℝ} (hb : 0 < b) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∫ x : ℝ, x ^ m * Real.exp (-(b * x ^ (2 * k))) =
      b ^ (-((m : ℝ) + 1) / (2 * k)) * gmom k m := by
  set s : ℝ := b ^ (1 / (2 * k : ℝ)) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos hb _
  have hk' : (2 * k : ℝ) ≠ 0 := by positivity
  have hs2k : s ^ (2 * k) = b := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    push_cast
    rw [one_div_mul_cancel hk', Real.rpow_one]
  have hcomp := Measure.integral_comp_mul_left (fun u : ℝ ↦ u ^ m * Real.exp (-u ^ (2 * k))) s
  -- `∫ g(s x) dx = s⁻¹ ∫ g`, and `g(s x) = s^m x^m e^{-b x^{2k}}`
  have hpt : (fun x : ℝ ↦ (s * x) ^ m * Real.exp (-(s * x) ^ (2 * k))) =
      fun x ↦ s ^ m * (x ^ m * Real.exp (-(b * x ^ (2 * k)))) := by
    funext x
    rw [mul_pow, mul_pow, hs2k]
    ring
  rw [hpt, integral_const_mul, abs_inv, abs_of_pos hspos, smul_eq_mul] at hcomp
  -- solve for the integral
  have hsm : s ^ m ≠ 0 := pow_ne_zero _ hspos.ne'
  have hI : (∫ x : ℝ, x ^ m * Real.exp (-(b * x ^ (2 * k)))) =
      (s ^ m)⁻¹ * s⁻¹ * gmom k m := by
    unfold gmom
    calc (∫ x : ℝ, x ^ m * Real.exp (-(b * x ^ (2 * k))))
        = (s ^ m)⁻¹ * (s ^ m * ∫ x : ℝ, x ^ m * Real.exp (-(b * x ^ (2 * k)))) := by
          field_simp
      _ = (s ^ m)⁻¹ * (s⁻¹ * ∫ u : ℝ, u ^ m * Real.exp (-u ^ (2 * k))) := by rw [hcomp]
      _ = (s ^ m)⁻¹ * s⁻¹ * ∫ u : ℝ, u ^ m * Real.exp (-u ^ (2 * k)) := by ring
  rw [hI]
  congr 1
  rw [← mul_inv, ← pow_succ, hs, ← Real.rpow_natCast, ← Real.rpow_mul hb.le,
    ← Real.rpow_neg hb.le]
  congr 1
  push_cast
  ring

/-! ### The model -/

/-- `L(x, y) = a(y) x^{2k}`. -/
noncomputable def spLoss (a : EuclidD n → ℝ) (k : ℕ) (z : ℝ × EuclidD n) : ℝ :=
  a z.2 * z.1 ^ (2 * k)

/-- The weight `χ(y) e^{-tL}`. -/
noncomputable def spWeight (a χ : EuclidD n → ℝ) (k : ℕ) (t : ℝ) (z : ℝ × EuclidD n) : ℝ :=
  χ z.2 * Real.exp (-(t * spLoss a k z))

/-- The normalised expectation. -/
noncomputable def spExp (a χ : EuclidD n → ℝ) (k : ℕ) (t : ℝ) (F : ℝ × EuclidD n → ℝ) : ℝ :=
  (∫ z, F z * spWeight a χ k t z) / ∫ z, spWeight a χ k t z

/-- Hypotheses: `k ≥ 1`, a continuous weight `a ≥ a₀ > 0`, a continuous nonnegative compactly
supported tangential cutoff. -/
structure SPData (a χ : EuclidD n → ℝ) (k : ℕ) (a₀ : ℝ) : Prop where
  k_pos : 1 ≤ k
  a_cont : Continuous a
  a₀_pos : 0 < a₀
  a_lower : ∀ y, a₀ ≤ a y
  χ_cont : Continuous χ
  χ_supp : HasCompactSupport χ
  χ_nonneg : ∀ y, 0 ≤ χ y

theorem SPData.a_pos {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀) (y : EuclidD n) :
    0 < a y := h.a₀_pos.trans_le (h.a_lower y)

/-- The singular tangential density `a^{-e}`, continuous for every real exponent. -/
theorem SPData.continuous_rpow {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀)
    (e : ℝ) : Continuous fun y ↦ a y ^ e :=
  h.a_cont.rpow_const fun y ↦ Or.inl (h.a_pos y).ne'

/-! ### Joint integrability and Fubini -/

theorem integrable_spWeight_mul {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀)
    {t : ℝ} (ht : 0 < t) (m : ℕ) {ψ : EuclidD n → ℝ} (hψ : Continuous ψ) :
    Integrable fun z : ℝ × EuclidD n ↦ z.1 ^ m * ψ z.2 * spWeight a χ k t z := by
  have hb : 0 < t * a₀ := mul_pos ht h.a₀_pos
  have hprod : Integrable (fun z : ℝ × EuclidD n ↦
      |z.1 ^ m * Real.exp (-(t * a₀ * z.1 ^ (2 * k)))| * |ψ z.2 * χ z.2|) := by
    rw [Measure.volume_eq_prod]
    exact (integrable_pow_mul_exp_neg_mul_pow hb k h.k_pos m).norm.mul_prod
      ((hψ.mul h.χ_cont).integrable_of_hasCompactSupport h.χ_supp.mul_left).norm
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
  · unfold spWeight spLoss
    exact (((continuous_fst.pow m).mul (hψ.comp continuous_snd)).mul
      ((h.χ_cont.comp continuous_snd).mul (Real.continuous_exp.comp
        ((continuous_const.mul ((h.a_cont.comp continuous_snd).mul
          (continuous_fst.pow (2 * k)))).neg)))).aestronglyMeasurable
  · unfold spWeight spLoss
    rw [Real.norm_eq_abs]
    have hx : 0 ≤ z.1 ^ (2 * k) := by
      rw [pow_mul]
      positivity
    have hexp : Real.exp (-(t * (a z.2 * z.1 ^ (2 * k)))) ≤
        Real.exp (-(t * a₀ * z.1 ^ (2 * k))) := by
      apply Real.exp_le_exp.mpr
      have := h.a_lower z.2
      nlinarith [mul_nonneg ht.le hx]
    calc |z.1 ^ m * ψ z.2 * (χ z.2 * Real.exp (-(t * (a z.2 * z.1 ^ (2 * k)))))|
        = |z.1 ^ m| * Real.exp (-(t * (a z.2 * z.1 ^ (2 * k)))) * |ψ z.2 * χ z.2| := by
          simp only [abs_mul, Real.abs_exp]
          ring
      _ ≤ |z.1 ^ m| * Real.exp (-(t * a₀ * z.1 ^ (2 * k))) * |ψ z.2 * χ z.2| := by
          gcongr
      _ = |z.1 ^ m * Real.exp (-(t * a₀ * z.1 ^ (2 * k)))| * |ψ z.2 * χ z.2| := by
          simp only [abs_mul, Real.abs_exp]

/-- Fubini and the exact transverse integral:
`∫ x^m ψ χ e^{-tL} = t^{-(m+1)/2k} c_m ∫ ψ χ a^{-(m+1)/2k}`. -/
theorem integral_pow_mul_spWeight {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀)
    {t : ℝ} (ht : 0 < t) (m : ℕ) {ψ : EuclidD n → ℝ} (hψ : Continuous ψ) :
    ∫ z : ℝ × EuclidD n, z.1 ^ m * ψ z.2 * spWeight a χ k t z =
      t ^ (-((m : ℝ) + 1) / (2 * k)) * gmom k m *
        ∫ y, ψ y * χ y * a y ^ (-((m : ℝ) + 1) / (2 * k)) := by
  have hi := integrable_spWeight_mul h ht m hψ
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [spWeight, spLoss]
  have hinner : (∫ x : ℝ, x ^ m * ψ y * (χ y * Real.exp (-(t * (a y * x ^ (2 * k)))))) =
      ψ y * χ y * ∫ x : ℝ, x ^ m * Real.exp (-((t * a y) * x ^ (2 * k))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    ring_nf
  rw [hinner, integral_pow_mul_exp_neg_mul_pow (mul_pos ht (h.a_pos y)) k h.k_pos m,
    Real.mul_rpow ht.le (h.a_pos y).le]
  ring

/-! ### The exact formulas -/

/-- The partition function: `Z_t = t^{-1/2k} c_0 ∫ χ a^{-1/2k}`. -/
theorem integral_spWeight {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀) {t : ℝ}
    (ht : 0 < t) :
    ∫ z, spWeight a χ k t z =
      t ^ (-(1 : ℝ) / (2 * k)) * gmom k 0 * ∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k)) := by
  have := integral_pow_mul_spWeight h ht 0 (ψ := fun _ ↦ (1 : ℝ)) continuous_const
  simp only [pow_zero, one_mul, mul_one, Nat.cast_zero, zero_add] at this
  exact this

theorem integral_cutoff_mul_rpow_pos {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀)
    {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0) (e : ℝ) : 0 < ∫ y, χ y * a y ^ e := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := y₀)
    (h.χ_cont.mul (h.continuous_rpow e)) h.χ_supp.mul_right
    (fun y ↦ mul_nonneg (h.χ_nonneg y) (Real.rpow_pos_of_pos (h.a_pos y) e).le) ?_
  exact mul_ne_zero hy₀ (Real.rpow_pos_of_pos (h.a_pos y₀) e).ne'

/-- **Tangential monomials see the singular density `a^{-1/2k}`**, independently of `t`. -/
theorem spExp_tangential {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀) {t : ℝ}
    (ht : 0 < t) {q : ℕ} (w : Fin q → Fin n) :
    spExp a χ k t (fun z ↦ monomialTest w z.2) =
      (∫ y, monomialTest w y * χ y * a y ^ (-(1 : ℝ) / (2 * k))) /
        ∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k)) := by
  unfold spExp
  have hnum := integral_pow_mul_spWeight h ht 0 (monomialTest_continuous w)
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at hnum
  rw [hnum, integral_spWeight h ht]
  have hc : t ^ (-(1 : ℝ) / (2 * k)) * gmom k 0 ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos ht _).ne' (by
      have := gmom_even_pos k h.k_pos 0
      simp only [mul_zero] at this
      exact this.ne')
  rw [mul_div_mul_left _ _ hc]

/-- **Transverse even moments**:
`t^{q/k} E_t[x^{2q} yᵛ] = (c_{2q}/c_0) ∫ yᵛ χ a^{-(2q+1)/2k} / ∫ χ a^{-1/2k}`. -/
theorem spExp_transverse {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀) {t : ℝ}
    (ht : 0 < t) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0) (q : ℕ) {m : ℕ} (w : Fin m → Fin n) :
    t ^ ((q : ℝ) / k) * spExp a χ k t (fun z ↦ z.1 ^ (2 * q) * monomialTest w z.2) =
      gmom k (2 * q) / gmom k 0 *
        ((∫ y, monomialTest w y * χ y * a y ^ (-((2 * q : ℕ) + 1 : ℝ) / (2 * k))) /
          ∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k))) := by
  unfold spExp
  rw [integral_pow_mul_spWeight h ht (2 * q) (monomialTest_continuous w), integral_spWeight h ht]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast h.k_pos
  have hA : (∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k))) ≠ 0 :=
    (integral_cutoff_mul_rpow_pos h hy₀ _).ne'
  have hg0 : gmom k 0 ≠ 0 := by
    have := gmom_even_pos k h.k_pos 0
    simp only [mul_zero] at this
    exact this.ne'
  have ht1 : t ^ (-(1 : ℝ) / (2 * k)) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hpow : t ^ ((q : ℝ) / k) * t ^ (-((2 * q : ℕ) + 1 : ℝ) / (2 * k)) =
      t ^ (-(1 : ℝ) / (2 * k)) := by
    rw [← Real.rpow_add ht]
    congr 1
    push_cast
    field_simp
    ring
  rw [← mul_div_assoc, show t ^ ((q : ℝ) / k) * (t ^ (-((2 * q : ℕ) + 1 : ℝ) / (2 * k)) *
      gmom k (2 * q) * ∫ y, monomialTest w y * χ y * a y ^ (-((2 * q : ℕ) + 1 : ℝ) / (2 * k))) =
      (t ^ ((q : ℝ) / k) * t ^ (-((2 * q : ℕ) + 1 : ℝ) / (2 * k))) * gmom k (2 * q) *
        ∫ y, monomialTest w y * χ y * a y ^ (-((2 * q : ℕ) + 1 : ℝ) / (2 * k)) by ring, hpow,
    mul_assoc, mul_assoc, mul_div_mul_left _ _ ht1, div_mul_div_comm]

/-- **The energy observable is the RLCT**: `t E_t[L] = 1/(2k)` exactly. -/
theorem mul_spExp_spLoss {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀) {t : ℝ}
    (ht : 0 < t) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0) :
    t * spExp a χ k t (spLoss a k) = 1 / (2 * k) := by
  unfold spExp
  have hnum : (∫ z : ℝ × EuclidD n, spLoss a k z * spWeight a χ k t z) =
      ∫ z : ℝ × EuclidD n, z.1 ^ (2 * k) * a z.2 * spWeight a χ k t z := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only [spLoss]
    ring
  rw [hnum, integral_pow_mul_spWeight h ht (2 * k) h.a_cont, integral_spWeight h ht]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast h.k_pos
  have hA : (∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k))) ≠ 0 :=
    (integral_cutoff_mul_rpow_pos h hy₀ _).ne'
  have hg0 : gmom k 0 ≠ 0 := by
    have := gmom_even_pos k h.k_pos 0
    simp only [mul_zero] at this
    exact this.ne'
  -- `a · a^{-(2k+1)/2k} = a^{-1/2k}`
  have hdens : (∫ y, a y * χ y * a y ^ (-((2 * k : ℕ) + 1 : ℝ) / (2 * k))) =
      ∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    have hay := h.a_pos y
    have : a y * a y ^ (-((2 * k : ℕ) + 1 : ℝ) / (2 * k)) = a y ^ (-(1 : ℝ) / (2 * k)) := by
      have hadd := Real.rpow_add hay 1 (-((2 * k : ℕ) + 1 : ℝ) / (2 * k))
      rw [Real.rpow_one] at hadd
      rw [← hadd]
      congr 1
      push_cast
      field_simp
      ring
    calc a y * χ y * a y ^ (-((2 * k : ℕ) + 1 : ℝ) / (2 * k))
        = χ y * (a y * a y ^ (-((2 * k : ℕ) + 1 : ℝ) / (2 * k))) := by ring
      _ = χ y * a y ^ (-(1 : ℝ) / (2 * k)) := by rw [this]
  rw [hdens]
  have hpow : t * t ^ (-((2 * k : ℕ) + 1 : ℝ) / (2 * k)) = t ^ (-(1 : ℝ) / (2 * k)) := by
    have hadd := Real.rpow_add ht 1 (-((2 * k : ℕ) + 1 : ℝ) / (2 * k))
    rw [Real.rpow_one] at hadd
    rw [← hadd]
    congr 1
    push_cast
    field_simp
    ring
  have ht1 : t ^ (-(1 : ℝ) / (2 * k)) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  rw [← gmom_two_k_div_zero k h.k_pos, ← mul_div_assoc,
    show t * (t ^ (-((2 * k : ℕ) + 1 : ℝ) / (2 * k)) * gmom k (2 * k) *
      ∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k))) =
      (t * t ^ (-((2 * k : ℕ) + 1 : ℝ) / (2 * k))) * gmom k (2 * k) *
        ∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k)) by ring, hpow, mul_div_mul_right _ _ hA,
    mul_div_mul_left _ _ ht1]

/-- **Free energy**: `-log Z_t = (1/2k) log t - log (c_0 ∫ χ a^{-1/2k})`, so `λ = 1/2k`. -/
theorem neg_log_integral_spWeight {a χ : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀)
    {t : ℝ} (ht : 0 < t) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0) :
    -Real.log (∫ z, spWeight a χ k t z) =
      1 / (2 * k) * Real.log t - Real.log (gmom k 0 * ∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k))) := by
  rw [integral_spWeight h ht, mul_assoc]
  have hg0 : 0 < gmom k 0 := by
    have := gmom_even_pos k h.k_pos 0
    simpa using this
  have hA : 0 < ∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k)) := integral_cutoff_mul_rpow_pos h hy₀ _
  rw [Real.log_mul (Real.rpow_pos_of_pos ht _).ne' (mul_pos hg0 hA).ne', Real.log_rpow ht]
  ring

/-! ### Identification -/

/-- **The decay exponent of `E_t[x²]` identifies `k`**: if two singular models have the same
`E_t[x²]` for all `t > 0`, their transverse orders agree. -/
theorem sp_exponent_identification {a₁ a₂ χ : EuclidD n → ℝ} {k₁ k₂ : ℕ} {a₀₁ a₀₂ : ℝ}
    (h₁ : SPData a₁ χ k₁ a₀₁) (h₂ : SPData a₂ χ k₂ a₀₂) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0)
    (hE : ∀ t : ℝ, 0 < t → spExp a₁ χ k₁ t (fun z ↦ z.1 ^ 2) = spExp a₂ χ k₂ t (fun z ↦ z.1 ^ 2)) :
    k₁ = k₂ := by
  -- `E_t[x²] = C t^{-1/k}` with `C > 0`
  have key : ∀ {a : EuclidD n → ℝ} {k : ℕ} {a₀ : ℝ} (h : SPData a χ k a₀), ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 < t → spExp a χ k t (fun z ↦ z.1 ^ 2) = C * t ^ (-(1 : ℝ) / k) := by
    intro a k a₀ h
    have hkpos : (0 : ℝ) < k := by exact_mod_cast h.k_pos
    refine ⟨gmom k 2 / gmom k 0 * ((∫ y, χ y * a y ^ (-((2 * 1 : ℕ) + 1 : ℝ) / (2 * k))) /
      ∫ y, χ y * a y ^ (-(1 : ℝ) / (2 * k))), ?_, fun t ht ↦ ?_⟩
    · have h2 := gmom_even_pos k h.k_pos 1
      have h0 := gmom_even_pos k h.k_pos 0
      simp only [mul_one, mul_zero] at h2 h0
      have := integral_cutoff_mul_rpow_pos h hy₀ (-((2 * 1 : ℕ) + 1 : ℝ) / (2 * k))
      have := integral_cutoff_mul_rpow_pos h hy₀ (-(1 : ℝ) / (2 * k))
      positivity
    · have := spExp_transverse h ht hy₀ 1 (w := (Fin.elim0 : Fin 0 → Fin n))
      have hmono : (fun z : ℝ × EuclidD n ↦
          z.1 ^ (2 * 1) * monomialTest (Fin.elim0 : Fin 0 → Fin n) z.2) = fun z ↦ z.1 ^ 2 := by
        funext z
        simp [monomialTest]
      have hmono' : (fun y : EuclidD n ↦ monomialTest (Fin.elim0 : Fin 0 → Fin n) y * χ y *
          a y ^ (-((2 * 1 : ℕ) + 1 : ℝ) / (2 * k))) =
          fun y ↦ χ y * a y ^ (-((2 * 1 : ℕ) + 1 : ℝ) / (2 * k)) := by
        funext y
        simp [monomialTest]
      rw [hmono, hmono'] at this
      have hne : t ^ ((1 : ℕ) / (k : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
      have hinv : t ^ (-(1 : ℝ) / k) = (t ^ ((1 : ℕ) / (k : ℝ)))⁻¹ := by
        rw [← Real.rpow_neg ht.le]
        congr 1
        push_cast
        ring
      rw [hinv, ← this]
      field_simp
  obtain ⟨C₁, hC₁, hf₁⟩ := key h₁
  obtain ⟨C₂, hC₂, hf₂⟩ := key h₂
  have h1 := hE 1 one_pos
  rw [hf₁ 1 one_pos, hf₂ 1 one_pos, Real.one_rpow, Real.one_rpow] at h1
  simp only [mul_one] at h1
  have h2 := hE 2 two_pos
  rw [hf₁ 2 two_pos, hf₂ 2 two_pos, ← h1] at h2
  have h2' := mul_left_cancel₀ hC₁.ne' h2
  -- `2^{-1/k₁} = 2^{-1/k₂}` forces `k₁ = k₂`
  have hk₁ : (0 : ℝ) < k₁ := by exact_mod_cast h₁.k_pos
  have hk₂ : (0 : ℝ) < k₂ := by exact_mod_cast h₂.k_pos
  have hexp : -(1 : ℝ) / k₁ = -(1 : ℝ) / k₂ :=
    le_antisymm ((Real.rpow_le_rpow_left_iff one_lt_two).mp h2'.le)
      ((Real.rpow_le_rpow_left_iff one_lt_two).mp h2'.ge)
  have : (k₁ : ℝ) = k₂ := by
    field_simp at hexp
    linarith
  exact_mod_cast this

/-- **Identification of the weight**: two singular models of the same order `k` with the same
cutoff and the same expectations of all tangential monomials `yᵛ` and of all `x² yᵛ` at one
temperature have `a₁ = a₂` on `{χ ≠ 0}`. -/
theorem sp_identification {a₁ a₂ χ : EuclidD n → ℝ} {k : ℕ} {a₀₁ a₀₂ : ℝ}
    (h₁ : SPData a₁ χ k a₀₁) (h₂ : SPData a₂ χ k a₀₂) {t : ℝ} (ht : 0 < t) {y₀ : EuclidD n}
    (hy₀ : χ y₀ ≠ 0)
    (hT : ∀ (q : ℕ) (w : Fin q → Fin n),
      spExp a₁ χ k t (fun z ↦ monomialTest w z.2) = spExp a₂ χ k t (fun z ↦ monomialTest w z.2))
    (hN : ∀ (q : ℕ) (w : Fin q → Fin n),
      spExp a₁ χ k t (fun z ↦ z.1 ^ (2 * 1) * monomialTest w z.2) =
        spExp a₂ χ k t (fun z ↦ z.1 ^ (2 * 1) * monomialTest w z.2)) :
    ∀ y, χ y ≠ 0 → a₁ y = a₂ y := by
  set e₀ : ℝ := -(1 : ℝ) / (2 * k) with he₀
  set e₁ : ℝ := -((2 * 1 : ℕ) + 1 : ℝ) / (2 * k) with he₁
  set A₁ := ∫ y, χ y * a₁ y ^ e₀ with hA₁
  set A₂ := ∫ y, χ y * a₂ y ^ e₀ with hA₂
  have hA₁p : 0 < A₁ := integral_cutoff_mul_rpow_pos h₁ hy₀ e₀
  have hA₂p : 0 < A₂ := integral_cutoff_mul_rpow_pos h₂ hy₀ e₀
  have hkpos : (0 : ℝ) < k := by exact_mod_cast h₁.k_pos
  -- generic step: equal normalised moments of `χ a_j^e / A_j` force equal densities
  have step : ∀ e : ℝ, (∀ (q : ℕ) (w : Fin q → Fin n),
      (∫ y, monomialTest w y * χ y * a₁ y ^ e) / A₁ =
        (∫ y, monomialTest w y * χ y * a₂ y ^ e) / A₂) →
      (fun y ↦ χ y * (a₁ y ^ e / A₁ - a₂ y ^ e / A₂)) = 0 := by
    intro e he
    apply eq_zero_of_integral_monomialTest_mul_eq_zero
    · exact h₁.χ_cont.mul (((h₁.continuous_rpow e).div_const _).sub
        ((h₂.continuous_rpow e).div_const _))
    · exact h₁.χ_supp.mul_right
    · intro q w
      have hi₁ : Integrable fun y ↦ monomialTest w y * χ y * a₁ y ^ e :=
        (((monomialTest_continuous w).mul h₁.χ_cont).mul (h₁.continuous_rpow e))
          |>.integrable_of_hasCompactSupport (h₁.χ_supp.mul_left.mul_right)
      have hi₂ : Integrable fun y ↦ monomialTest w y * χ y * a₂ y ^ e :=
        (((monomialTest_continuous w).mul h₂.χ_cont).mul (h₂.continuous_rpow e))
          |>.integrable_of_hasCompactSupport (h₂.χ_supp.mul_left.mul_right)
      have hfun : (fun y ↦ monomialTest w y * (χ y * (a₁ y ^ e / A₁ - a₂ y ^ e / A₂))) =
          fun y ↦ monomialTest w y * χ y * a₁ y ^ e / A₁ -
            monomialTest w y * χ y * a₂ y ^ e / A₂ := by
        funext y
        ring
      rw [hfun, integral_sub (hi₁.div_const _) (hi₂.div_const _), integral_div, integral_div,
        he q w, sub_self]
  have hρ := step e₀ fun q w ↦ by
    have e₁' := spExp_tangential h₁ ht w
    have e₂' := spExp_tangential h₂ ht w
    rw [← hA₁] at e₁'
    rw [← hA₂] at e₂'
    rw [← e₁', ← e₂']
    exact hT q w
  have hσ := step e₁ fun q w ↦ by
    have f₁ := spExp_transverse h₁ ht hy₀ 1 w
    have f₂ := spExp_transverse h₂ ht hy₀ 1 w
    rw [← hA₁] at f₁
    rw [← hA₂] at f₂
    have hc : gmom k (2 * 1) / gmom k 0 ≠ 0 := by
      have h2 : 0 < gmom k (2 * 1) := gmom_even_pos k h₁.k_pos 1
      have h0 : 0 < gmom k 0 := by simpa using gmom_even_pos k h₁.k_pos 0
      positivity
    have ht' : t ^ ((1 : ℕ) / (k : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    have := hN q w
    have := congrArg (fun x ↦ t ^ ((1 : ℕ) / (k : ℝ)) * x) this
    rw [f₁, f₂] at this
    exact mul_left_cancel₀ hc this
  intro y hy
  have h₁y := h₁.a_pos y
  have h₂y := h₂.a_pos y
  have hρy : a₁ y ^ e₀ / A₁ = a₂ y ^ e₀ / A₂ := by
    have := congrFun hρ y
    simp only [Pi.zero_apply, mul_eq_zero, hy, false_or] at this
    linarith
  have hσy : a₁ y ^ e₁ / A₁ = a₂ y ^ e₁ / A₂ := by
    have := congrFun hσ y
    simp only [Pi.zero_apply, mul_eq_zero, hy, false_or] at this
    linarith
  -- `a^{e₁}/a^{e₀} = a^{-1/k}` agree
  have hr₁ : 0 < a₁ y ^ e₀ := Real.rpow_pos_of_pos h₁y _
  have hr₂ : 0 < a₂ y ^ e₀ := Real.rpow_pos_of_pos h₂y _
  have key : a₁ y ^ e₁ / a₁ y ^ e₀ = a₂ y ^ e₁ / a₂ y ^ e₀ := by
    rw [div_eq_div_iff hr₁.ne' hr₂.ne']
    rw [div_eq_div_iff hA₁p.ne' hA₂p.ne'] at hρy hσy
    have e : a₁ y ^ e₁ * a₂ y ^ e₀ * A₁ = a₂ y ^ e₁ * a₁ y ^ e₀ * A₁ := by
      linear_combination a₁ y ^ e₀ * hσy - a₁ y ^ e₁ * hρy
    exact mul_right_cancel₀ hA₁p.ne' e
  rw [← Real.rpow_sub h₁y, ← Real.rpow_sub h₂y] at key
  have hne : e₁ - e₀ ≠ 0 := by
    have : e₁ - e₀ = -(1 : ℝ) / k := by
      rw [he₁, he₀]
      push_cast
      field_simp
      ring
    rw [this]
    exact div_ne_zero (by norm_num) hkpos.ne'
  exact Real.rpow_left_injOn hne h₁y.le h₂y.le key

end Laplace.Multi
