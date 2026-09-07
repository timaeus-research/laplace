/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StateDensity
import Laplace.Grammar.MonomialAmplitudeAsymptotic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The state density: integrability, real form, Mellin transform

Unit 225 (Taylor-tree programme, Stage 1c). Downstream stages should never reopen the box
Fubini: this file exports the state density of unit 224 in the forms they need.

* `stateDensity_integrableOn`: the density is integrable on `(0,1]` (from the box identity with
  `g = 1`: no analysis of the individual power–log terms is needed).
* `integral_unitBox_eq_stateDensity`: the **real-valued identity**
  `∫_{(0,1]^{n+1}} ∏ aᵢ^{wᵢ} f(∏ aᵢ) da = ∫₀¹ v(z) f(z) dz` for measurable `f ≥ 0` on `(0,1]`.
* `weightedBoxIntegral_rpow` / `mellin_stateDensity`: the Mellin transform
  `∫₀¹ z^s v(z) dz = ∏ᵢ 1/(wᵢ + s + 1)` for `wᵢ + s > -1` — the paper's product zeta function
  `∏ 1/(2kᵢz + hᵢ + 1)` in the weight normalisation.
* `integral_Ioc_rpow_mul_neg_log_pow`: the Mellin transform of a basis term,
  `∫₀¹ τ^{c-1} (-log τ)^j dτ = j!/c^{j+1}` (substitution `τ = e^{-x}` into Euler's integral), and
  `mellin_eval`: termwise, `∫₀¹ z^s eval c z dz = ∑ cₜ jₜ!/(s+μₜ)^{jₜ+1}` — the factorial that
  converts density coefficients into Laurent coefficients.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real

namespace Laplace.Grammar

/-! ### One-dimensional Mellin factors -/

theorem lintegral_Ioc_rpow (a : ℝ) (ha : -1 < a) :
    ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ a) = ENNReal.ofReal (1 / (a + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioc_rpow_factor a ha)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => Real.rpow_nonneg hx.1.le a),
    integral_Ioc_rpow_factor a ha]

/-- **Mellin transform of the weighted box**: `∫_{(0,1]^d} ∏ aᵢ^{wᵢ} (∏ aᵢ)^s = ∏ 1/(wᵢ+s+1)`. -/
theorem weightedBoxIntegral_rpow : ∀ (d : ℕ) (w : Fin d → ℝ) (s : ℝ), (∀ i, -1 < w i + s) →
    weightedBoxIntegral d w (fun z => ENNReal.ofReal (z ^ s)) =
      ∏ i, ENNReal.ofReal (1 / (w i + s + 1)) := by
  intro d
  induction d with
  | zero =>
    intro w s _
    rw [weightedBoxIntegral_zero]
    simp
  | succ d ih =>
    intro w s hw
    have hg : Measurable fun z : ℝ => ENNReal.ofReal (z ^ s) :=
      ENNReal.measurable_ofReal.comp (measurable_id.pow_const s)
    rw [weightedBoxIntegral_succ d w (fun z => ENNReal.ofReal (z ^ s)) hg]
    have hin : ∀ a ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal (a ^ w 0) *
          weightedBoxIntegral d (Fin.tail w) (fun z => ENNReal.ofReal ((a * z) ^ s)) =
        ENNReal.ofReal (a ^ (w 0 + s)) * ∏ i, ENNReal.ofReal (1 / (Fin.tail w i + s + 1)) := by
      intro a ha
      rw [← ih (Fin.tail w) s (fun i => hw i.succ)]
      unfold weightedBoxIntegral
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun (measurableSet_unitBox d) fun t ht => ?_
      have ht0 : 0 ≤ ∏ i, t i := Finset.prod_nonneg fun i _ => (ht i (mem_univ i)).1.le
      beta_reduce
      rw [Real.mul_rpow ha.1.le ht0, ENNReal.ofReal_mul (Real.rpow_nonneg ha.1.le _),
        Real.rpow_add ha.1, ENNReal.ofReal_mul (Real.rpow_nonneg ha.1.le _)]
      ring
    have hm : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (w 0 + s)) :=
      ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
    rw [setLIntegral_congr_fun measurableSet_Ioc hin, Fin.prod_univ_succ, lintegral_mul_const _ hm,
      lintegral_Ioc_rpow _ (hw 0)]
    rfl

/-! ### Integrability and the real identity -/

/-- The state density is integrable on `(0,1]`. -/
theorem stateDensity_integrableOn (n : ℕ) (w : Fin (n + 1) → ℝ) (hw : ∀ i, -1 < w i) :
    IntegrableOn (PowLogRep.eval (stateDensityRep n w)) (Ioc 0 1) := by
  have hfin :
      ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (PowLogRep.eval (stateDensityRep n w) z) < ⊤ := by
    have h := weightedBoxIntegral_eq_stateDensity n w (fun _ => 1) measurable_const
    simp only [mul_one] at h
    rw [← h]
    have h0 := weightedBoxIntegral_rpow (n + 1) w 0 (fun i => by simpa using hw i)
    simp only [Real.rpow_zero, ENNReal.ofReal_one] at h0
    rw [h0]
    exact ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top
  refine ⟨(PowLogRep.measurable_eval _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_eq_of_lt (setLIntegral_congr_fun measurableSet_Ioc fun z hz => ?_) hfin
  rw [Real.enorm_eq_ofReal (stateDensityRep_nonneg n w z hz)]

theorem prod_mem_Ioc {d : ℕ} {a : Fin d → ℝ} (ha : a ∈ unitBox d) : ∏ i, a i ∈ Ioc (0 : ℝ) 1 :=
  ⟨Finset.prod_pos fun i _ => (ha i (mem_univ i)).1,
    Finset.prod_le_one (fun i _ => (ha i (mem_univ i)).1.le) fun i _ => (ha i (mem_univ i)).2⟩

/-- **Real-valued state-density identity** for measurable `f ≥ 0` on `(0,1]`. -/
theorem integral_unitBox_eq_stateDensity (n : ℕ) (w : Fin (n + 1) → ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (hf0 : ∀ z ∈ Ioc (0 : ℝ) 1, 0 ≤ f z) :
    ∫ a in unitBox (n + 1), (∏ i, a i ^ w i) * f (∏ i, a i) =
      ∫ z in Ioc (0 : ℝ) 1, PowLogRep.eval (stateDensityRep n w) z * f z := by
  have hmeasL : Measurable fun a : Fin (n + 1) → ℝ => (∏ i, a i ^ w i) * f (∏ i, a i) :=
    (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _).mul
      (hf.comp (Finset.measurable_prod _ fun i _ => measurable_pi_apply i))
  rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem (measurableSet_unitBox _)
      fun a ha => mul_nonneg
        (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ha i (mem_univ i)).1.le _)
        (hf0 _ (prod_mem_Ioc ha))) hmeasL.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioc
      fun z hz => mul_nonneg (stateDensityRep_nonneg n w z hz) (hf0 z hz))
      ((PowLogRep.measurable_eval _).mul hf).aestronglyMeasurable]
  congr 1
  have h := weightedBoxIntegral_eq_stateDensity n w (fun z => ENNReal.ofReal (f z))
    (ENNReal.measurable_ofReal.comp hf)
  unfold weightedBoxIntegral at h
  have hR : ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (PowLogRep.eval (stateDensityRep n w) z * f z) =
      ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (PowLogRep.eval (stateDensityRep n w) z) *
        ENNReal.ofReal (f z) :=
    setLIntegral_congr_fun measurableSet_Ioc fun z hz =>
      ENNReal.ofReal_mul (stateDensityRep_nonneg n w z hz)
  rw [hR, ← h]
  refine setLIntegral_congr_fun (measurableSet_unitBox _) fun a ha => ?_
  rw [ENNReal.ofReal_mul
      (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ha i (mem_univ i)).1.le _),
    ENNReal.ofReal_prod_of_nonneg fun i _ => Real.rpow_nonneg (ha i (mem_univ i)).1.le _]

/-- **Mellin transform of the state density**: `∫₀¹ z^s v(z) dz = ∏ 1/(wᵢ+s+1)`. -/
theorem mellin_stateDensity (n : ℕ) (w : Fin (n + 1) → ℝ) (s : ℝ) (hw : ∀ i, -1 < w i + s) :
    ∫ z in Ioc (0 : ℝ) 1, z ^ s * PowLogRep.eval (stateDensityRep n w) z =
      ∏ i, 1 / (w i + s + 1) := by
  have h := integral_unitBox_eq_stateDensity n w (fun z => z ^ s) (measurable_id.pow_const s)
    fun z hz => Real.rpow_nonneg hz.1.le s
  have hbox : ∫ a in unitBox (n + 1), (∏ i, a i ^ w i) * (∏ i, a i) ^ s =
      ∏ i, 1 / (w i + s + 1) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem (measurableSet_unitBox _)
      fun a ha => mul_nonneg
        (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ha i (mem_univ i)).1.le _)
        (Real.rpow_nonneg (prod_mem_Ioc ha).1.le _))
      ((Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _).mul
        ((Finset.measurable_prod _ fun i _ =>
          measurable_pi_apply i).pow_const _)).aestronglyMeasurable]
    have hW := weightedBoxIntegral_rpow (n + 1) w s hw
    unfold weightedBoxIntegral at hW
    rw [setLIntegral_congr_fun (measurableSet_unitBox _) (fun a ha => by
      rw [ENNReal.ofReal_mul
          (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ha i (mem_univ i)).1.le _),
        ENNReal.ofReal_prod_of_nonneg fun i _ => Real.rpow_nonneg (ha i (mem_univ i)).1.le _]), hW,
      ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal ?_
    have : 0 < w i + s + 1 := by linarith [hw i]
    positivity
  rw [← hbox, h]
  refine setIntegral_congr_fun measurableSet_Ioc fun z _ => ?_
  ring

/-! ### Mellin transform of a basis term -/

theorem image_neg_log_Ioc : (fun x : ℝ => -Real.log x) '' Ioc (0 : ℝ) 1 = Ici 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact neg_nonneg.2 (Real.log_nonpos hx.1.le hx.2)
  · intro hy
    refine ⟨Real.exp (-y),
      ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (neg_nonpos.2 (mem_Ici.mp hy))⟩, ?_⟩
    simp only [Real.log_exp, neg_neg]

theorem hasDerivWithinAt_neg_log {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    HasDerivWithinAt (fun x : ℝ => -Real.log x) (-(x⁻¹)) (Ioc 0 1) x :=
  ((Real.hasDerivAt_log hx.1.ne').neg).hasDerivWithinAt

theorem injOn_neg_log : InjOn (fun x : ℝ => -Real.log x) (Ioc (0 : ℝ) 1) :=
  fun _ hx _ hy h => Real.log_injOn_pos hx.1 hy.1 (neg_injective h)

/-- Pointwise: `|−x⁻¹| · (−log x)^j e^{−c(−log x)} = x^{c−1} (−log x)^j` on `(0,1]`. -/
theorem neg_log_kernel_eq (c : ℝ) (j : ℕ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    |-(x⁻¹)| * ((-Real.log x) ^ j * Real.exp (-(c * -Real.log x))) =
      x ^ (c - 1) * (-Real.log x) ^ j := by
  have hx0 : 0 < x := hx.1
  rw [abs_neg, abs_of_pos (inv_pos.2 hx0), show -(c * -Real.log x) = Real.log x * c by ring,
    ← Real.rpow_def_of_pos hx0, Real.rpow_sub_one hx0.ne']
  ring

theorem integrableOn_Ioi_pow_mul_exp (c : ℝ) (hc : 0 < c) (j : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ j * Real.exp (-(c * y))) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (j : ℝ) + 1) (by positivity)
  have h2 : IntegrableOn (fun y : ℝ => Real.exp (-(c * y)) * (c * y) ^ ((j : ℝ) + 1 - 1))
      (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x) * x ^ ((j : ℝ) + 1 - 1))
      0 hc).2 (by simpa using h)
    simpa using this
  have h3 : IntegrableOn (fun y : ℝ => c ^ (-(j : ℝ)) *
      (Real.exp (-(c * y)) * (c * y) ^ ((j : ℝ) + 1 - 1))) (Ioi 0) := h2.const_mul _
  refine h3.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : 0 < y := hy
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  rw [mul_pow, Real.rpow_neg hc.le, Real.rpow_natCast]
  field_simp

/-- **Mellin transform of a basis term**: `∫₀¹ τ^{c-1} (-log τ)^j dτ = j!/c^{j+1}`. -/
theorem integral_Ioc_rpow_mul_neg_log_pow (c : ℝ) (hc : 0 < c) (j : ℕ) :
    ∫ τ in Ioc (0 : ℝ) 1, τ ^ (c - 1) * (-Real.log τ) ^ j = (j.factorial : ℝ) / c ^ (j + 1) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun x hx => hasDerivWithinAt_neg_log hx) injOn_neg_log
    (fun y => y ^ j * Real.exp (-(c * y)))
  rw [image_neg_log_Ioc, integral_Ici_eq_integral_Ioi] at h
  have hG : ∫ y in Ioi (0 : ℝ), y ^ j * Real.exp (-(c * y)) = (j.factorial : ℝ) / c ^ (j + 1) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ) + 1) (r := c) (by positivity) hc
    simp only [add_sub_cancel_right, Real.rpow_natCast] at this
    rw [this, Real.Gamma_nat_eq_factorial, show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, one_div, inv_pow]
    ring
  rw [← hG, h]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [smul_eq_mul, neg_log_kernel_eq c j hx]

theorem integrableOn_powLogBasis (c : ℝ) (hc : 0 < c) (j : ℕ) :
    IntegrableOn (powLogBasis c j) (Ioc 0 1) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc
    (fun x hx => hasDerivWithinAt_neg_log hx) injOn_neg_log
    (fun y => y ^ j * Real.exp (-(c * y)))).1 (by
      rw [image_neg_log_Ioc, integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_Ioi_pow_mul_exp c hc j)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioc
  beta_reduce
  rw [smul_eq_mul, neg_log_kernel_eq c j hx]
  rfl

theorem integrableOn_rpow_mul_powLogBasis (μ s : ℝ) (j : ℕ) (hμ : 0 < μ + s) (a : ℝ) :
    IntegrableOn (fun z => z ^ s * (a * powLogBasis μ j z)) (Ioc 0 1) := by
  have h : IntegrableOn (fun z => a * powLogBasis (μ + s) j z) (Ioc 0 1) :=
    (integrableOn_powLogBasis (μ + s) hμ j).const_mul a
  refine h.congr_fun (fun z hz => ?_) measurableSet_Ioc
  unfold powLogBasis
  beta_reduce
  rw [show μ + s - 1 = s + (μ - 1) by ring, Real.rpow_add hz.1]
  ring

theorem integrableOn_rpow_mul_eval (c : PowLogRep) (s : ℝ) (hc : ∀ t ∈ c, 0 < t.1 + s) :
    IntegrableOn (fun z => z ^ s * PowLogRep.eval c z) (Ioc 0 1) := by
  induction c with
  | nil => simp only [PowLogRep.eval_nil, mul_zero]; exact integrableOn_zero
  | cons t c ih =>
    have h1 := integrableOn_rpow_mul_powLogBasis t.1 s t.2.1 (hc t (List.mem_cons_self ..)) t.2.2
    have h2 := ih fun u hu => hc u (List.mem_cons_of_mem t hu)
    refine (h1.add h2).congr_fun (fun z _ => ?_) measurableSet_Ioc
    simp only [PowLogRep.eval_cons, Pi.add_apply]
    ring

/-- Termwise Mellin transform of a representation whose exponents satisfy `μ + s > 0`. -/
theorem mellin_eval (c : PowLogRep) (s : ℝ) (hc : ∀ t ∈ c, 0 < t.1 + s) :
    ∫ z in Ioc (0 : ℝ) 1, z ^ s * PowLogRep.eval c z =
      (c.map fun t => t.2.2 * ((t.2.1.factorial : ℝ) / (s + t.1) ^ (t.2.1 + 1))).sum := by
  induction c with
  | nil => simp
  | cons t c ih =>
    have ht := hc t (List.mem_cons_self ..)
    have hrest : ∀ u ∈ c, 0 < u.1 + s := fun u hu => hc u (List.mem_cons_of_mem t hu)
    rw [List.map_cons, List.sum_cons, ← ih hrest]
    have hsplit : ∫ z in Ioc (0 : ℝ) 1, z ^ s * PowLogRep.eval (t :: c) z =
        ∫ z in Ioc (0 : ℝ) 1, (z ^ s * (t.2.2 * powLogBasis t.1 t.2.1 z) +
          z ^ s * PowLogRep.eval c z) :=
      setIntegral_congr_fun measurableSet_Ioc fun z _ => by simp only [PowLogRep.eval_cons]; ring
    rw [hsplit, integral_add (integrableOn_rpow_mul_powLogBasis t.1 s t.2.1 ht t.2.2)
      (integrableOn_rpow_mul_eval c s hrest)]
    congr 1
    have hb : ∫ z in Ioc (0 : ℝ) 1, z ^ s * (t.2.2 * powLogBasis t.1 t.2.1 z) =
        t.2.2 * ∫ z in Ioc (0 : ℝ) 1, powLogBasis (t.1 + s) t.2.1 z := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun z hz => ?_
      unfold powLogBasis
      rw [show t.1 + s - 1 = s + (t.1 - 1) by ring, Real.rpow_add hz.1]
      ring
    rw [hb]
    unfold powLogBasis
    rw [integral_Ioc_rpow_mul_neg_log_pow (t.1 + s) ht, add_comm t.1 s]

end Laplace.Grammar
