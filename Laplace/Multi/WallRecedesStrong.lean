/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WallRecedes

/-!
# The receding wall, strong form: quantitative Gamma tail

The Gamma-tail limit `I_k(c) → Γ(k + 1/q)` of `ProfileGammaTail` is made quantitative here:
since `0 ≤ 1 − e^{-x} ≤ x`,

  `0 ≤ Γ(k + 1/q) − I_k(c) ≤ c^{-p/q} Γ(k + 1/q + p/q)`   (`tailIntegral_sub_le`),

so the profile moments approach their Gamma limits at rate `c^{-p/q}`. With the exact ratio
identities `c ⟨y^q⟩_c = I₁/I₀` and `c² ⟨y^q y^q⟩_c = I₂/I₀` (`mul_profileMean_eq`,
`sq_mul_profileSecond_eq`) this gives `c² Var_c(y^q) = 1/q + O(c^{-p/q})`, hence the *integrable
defect* `h(c) − √(1/q)/c = O(c^{-1-p/q})` of the profile speed, which is what the renormalised
receding-wall limit needs (Astra, rounds 23–24).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- `1 − e^{-x} ≤ x`. -/
theorem one_sub_exp_neg_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  have := Real.add_one_le_exp (-x)
  linarith

/-- The tail integrand is dominated by the Gamma integrand. -/
theorem tailIntegrand_le {s r c z : ℝ} (hc : 0 < c) (hz : 0 < z) :
    z ^ s * Real.exp (-z) * Real.exp (-((z / c) ^ r)) ≤ z ^ s * Real.exp (-z) := by
  refine mul_le_of_le_one_right (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le) ?_
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact Real.rpow_nonneg (by positivity) _

/-- Integrability of the tail integrand. -/
theorem integrableOn_tailIntegrand {s r c : ℝ} (hs : -1 < s) (hc : 0 < c) :
    IntegrableOn (fun z : ℝ ↦ z ^ s * Real.exp (-z) * Real.exp (-((z / c) ^ r))) (Ioi 0) := by
  have hint : IntegrableOn (fun z : ℝ ↦ z ^ s * Real.exp (-z)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := s) hs one_pos
    simpa only [Real.rpow_one] using this
  refine hint.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun z hz ↦ ?_)
  have hz0 : (0 : ℝ) < z := hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hz0.le _)
    (Real.exp_pos _).le) (Real.exp_pos _).le)]
  exact tailIntegrand_le hc hz0

/-- **Quantitative Gamma tail**: `0 ≤ Γ(k + 1/q) − I_k(c) ≤ c^{-p/q} Γ(k + 1/q + p/q)`. -/
theorem tailIntegral_sub_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {k : ℝ} (hk : 0 ≤ k) {c : ℝ}
    (hc : 0 < c) :
    0 ≤ Real.Gamma (k + 1 / q) - tailIntegral p q k c ∧
      Real.Gamma (k + 1 / q) - tailIntegral p q k c ≤
        c ^ (-(p / q)) * Real.Gamma (k + 1 / q + p / q) := by
  have hq' : 0 < 1 / q := one_div_pos.mpr hq
  have hs : -1 < k + 1 / q - 1 := by linarith
  have hr : 0 < p / q := div_pos hp hq
  have hs' : -1 < k + 1 / q - 1 + p / q := by linarith
  have hG : Real.Gamma (k + 1 / q) = ∫ z in Ioi (0 : ℝ), z ^ (k + 1 / q - 1) * Real.exp (-z) := by
    rw [integral_rpow_mul_exp_neg_eq_Gamma hs, sub_add_cancel]
  have hG' : Real.Gamma (k + 1 / q + p / q) =
      ∫ z in Ioi (0 : ℝ), z ^ (k + 1 / q - 1 + p / q) * Real.exp (-z) := by
    rw [integral_rpow_mul_exp_neg_eq_Gamma hs']
    congr 1
    ring
  have hint : IntegrableOn (fun z : ℝ ↦ z ^ (k + 1 / q - 1) * Real.exp (-z)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := k + 1 / q - 1) hs one_pos
    simpa only [Real.rpow_one] using this
  have hint' : IntegrableOn (fun z : ℝ ↦ z ^ (k + 1 / q - 1 + p / q) * Real.exp (-z)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := k + 1 / q - 1 + p / q) hs' one_pos
    simpa only [Real.rpow_one] using this
  have htail := integrableOn_tailIntegrand (r := p / q) hs hc
  unfold tailIntegral
  rw [hG, ← integral_sub hint htail]
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi fun z hz ↦ ?_
    have hz0 : (0 : ℝ) < z := hz
    linarith [tailIntegrand_le (s := k + 1 / q - 1) (r := p / q) hc hz0]
  · rw [hG', ← MeasureTheory.integral_const_mul]
    refine setIntegral_mono_on (hint.sub htail) (hint'.const_mul _) measurableSet_Ioi
      fun z hz ↦ ?_
    have hz0 : (0 : ℝ) < z := hz
    have e : z ^ (k + 1 / q - 1) * Real.exp (-z) -
        z ^ (k + 1 / q - 1) * Real.exp (-z) * Real.exp (-((z / c) ^ (p / q))) =
        z ^ (k + 1 / q - 1) * Real.exp (-z) * (1 - Real.exp (-((z / c) ^ (p / q)))) := by ring
    rw [e]
    calc z ^ (k + 1 / q - 1) * Real.exp (-z) * (1 - Real.exp (-((z / c) ^ (p / q))))
        ≤ z ^ (k + 1 / q - 1) * Real.exp (-z) * (z / c) ^ (p / q) :=
          mul_le_mul_of_nonneg_left (one_sub_exp_neg_le _) (by positivity)
      _ = c ^ (-(p / q)) * (z ^ (k + 1 / q - 1 + p / q) * Real.exp (-z)) := by
          rw [Real.div_rpow hz0.le hc.le, Real.rpow_add hz0, Real.rpow_neg hc.le]
          ring

/-- The exact ratio identity `c ⟨y^q⟩_c = I₁(c)/I₀(c)`. -/
theorem mul_profileMean_eq {p q : ℝ} (hq : 0 < q) {c : ℝ} (hc : 0 < c) :
    c * profilePosterior p q (fun y ↦ y ^ q) c = tailIntegral p q 1 c / tailIntegral p q 0 c := by
  unfold profilePosterior
  rw [profileNum_score_eq_moment, profileNum_one_eq_moment, profileMoment_eq_tail hq 1 hc,
    profileMoment_eq_tail hq 0 hc]
  have hq' : (1 / q : ℝ) ≠ 0 := (one_div_pos.mpr hq).ne'
  have hc0 : c ^ (-(0 + 1 / q)) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have hc1 : c ^ (-(1 + 1 / q)) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have e : c * c ^ (-(1 + 1 / q)) = c ^ (-(0 + 1 / q)) := by
    rw [Real.rpow_neg hc.le, Real.rpow_neg hc.le, Real.rpow_add hc, Real.rpow_one, zero_add,
      mul_inv, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [← mul_div_assoc, show c * (1 / q * (c ^ (-(1 + 1 / q)) * tailIntegral p q 1 c)) =
      1 / q * (c ^ (-(0 + 1 / q)) * tailIntegral p q 1 c) by rw [← e]; ring,
    mul_div_mul_left _ _ hq', mul_div_mul_left _ _ hc0]

/-- The exact ratio identity `c² ⟨y^q y^q⟩_c = I₂(c)/I₀(c)`. -/
theorem sq_mul_profileSecond_eq {p q : ℝ} (hq : 0 < q) {c : ℝ} (hc : 0 < c) :
    c ^ 2 * profilePosterior p q (fun y ↦ y ^ q * y ^ q) c =
      tailIntegral p q 2 c / tailIntegral p q 0 c := by
  unfold profilePosterior
  rw [profileNum_score_sq_eq_moment, profileNum_one_eq_moment, profileMoment_eq_tail hq 2 hc,
    profileMoment_eq_tail hq 0 hc]
  have hq' : (1 / q : ℝ) ≠ 0 := (one_div_pos.mpr hq).ne'
  have hc0 : c ^ (-(0 + 1 / q)) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have hc2 : c ^ (-(2 + 1 / q)) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have e : c ^ 2 * c ^ (-(2 + 1 / q)) = c ^ (-(0 + 1 / q)) := by
    rw [Real.rpow_neg hc.le, Real.rpow_neg hc.le, Real.rpow_add hc, zero_add, Real.rpow_two,
      mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hc.ne'), one_mul]
  rw [← mul_div_assoc, show c ^ 2 * (1 / q * (c ^ (-(2 + 1 / q)) * tailIntegral p q 2 c)) =
      1 / q * (c ^ (-(0 + 1 / q)) * tailIntegral p q 2 c) by rw [← e]; ring,
    mul_div_mul_left _ _ hq', mul_div_mul_left _ _ hc0]

/-- `|√x − √κ| ≤ |x − κ| / √κ` for `x ≥ 0`, `κ > 0`. -/
theorem abs_sqrt_sub_sqrt_le {x κ : ℝ} (hx : 0 ≤ x) (hκ : 0 < κ) :
    |Real.sqrt x - Real.sqrt κ| ≤ |x - κ| / Real.sqrt κ := by
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hprod : (Real.sqrt x - Real.sqrt κ) * (Real.sqrt x + Real.sqrt κ) = x - κ := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hκ.le
    nlinarith
  have hsum : 0 < Real.sqrt x + Real.sqrt κ := by linarith
  rw [le_div_iff₀ hsκ, ← hprod, abs_mul, abs_of_pos hsum]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

/-- Perturbing numerator and denominator of a ratio by at most `ε D`, with the denominator kept
above half its limit, moves the ratio by at most `ε · 2(D_a Γ₀ + Γ_a D₀)/Γ₀²`. -/
theorem ratio_perturb_bound {a b Γa Γ₀ Da D₀ ε : ℝ} (hΓ₀ : 0 < Γ₀) (hΓa : 0 ≤ Γa) (hDa : 0 ≤ Da)
    (hD₀ : 0 ≤ D₀) (hε : 0 ≤ ε) (hb : Γ₀ / 2 ≤ b) (ha : |Γa - a| ≤ ε * Da)
    (hb' : |Γ₀ - b| ≤ ε * D₀) :
    |a / b - Γa / Γ₀| ≤ ε * (2 * (Da * Γ₀ + Γa * D₀) / Γ₀ ^ 2) := by
  have hb0 : 0 < b := by linarith
  rw [div_sub_div _ _ hb0.ne' hΓ₀.ne', abs_div, abs_of_pos (mul_pos hb0 hΓ₀), div_le_iff₀
    (mul_pos hb0 hΓ₀)]
  have hnum : |a * Γ₀ - b * Γa| ≤ ε * (Da * Γ₀ + Γa * D₀) := by
    calc |a * Γ₀ - b * Γa| = |(a - Γa) * Γ₀ + Γa * (Γ₀ - b)| := by ring_nf
      _ ≤ |(a - Γa) * Γ₀| + |Γa * (Γ₀ - b)| := abs_add_le _ _
      _ = |Γa - a| * Γ₀ + Γa * |Γ₀ - b| := by
          rw [abs_mul, abs_mul, abs_of_pos hΓ₀, abs_of_nonneg hΓa, abs_sub_comm a Γa]
      _ ≤ ε * Da * Γ₀ + Γa * (ε * D₀) :=
          add_le_add (mul_le_mul_of_nonneg_right ha hΓ₀.le) (mul_le_mul_of_nonneg_left hb' hΓa)
      _ = ε * (Da * Γ₀ + Γa * D₀) := by ring
  refine le_trans hnum ?_
  have hb2 : Γ₀ ^ 2 / 2 ≤ b * Γ₀ := by nlinarith
  rw [show ε * (2 * (Da * Γ₀ + Γa * D₀) / Γ₀ ^ 2) * (b * Γ₀) =
    ε * (Da * Γ₀ + Γa * D₀) * (b * Γ₀ / (Γ₀ ^ 2 / 2)) by field_simp]
  refine le_mul_of_one_le_right (by positivity) ?_
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The threshold beyond which the Gamma-tail deficit of `I₀` is at most half of `Γ(1/q)`. -/
noncomputable def tailThreshold (p q : ℝ) : ℝ :=
  max 1 ((2 * Real.Gamma (1 / q + p / q) / Real.Gamma (1 / q)) ^ (q / p))

theorem tailThreshold_pos (p q : ℝ) : 0 < tailThreshold p q :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Beyond the threshold the tail deficit of `I₀` is at most `Γ(1/q)/2`. -/
theorem tail_deficit_half {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hc : tailThreshold p q ≤ c) :
    c ^ (-(p / q)) * Real.Gamma (1 / q + p / q) ≤ Real.Gamma (1 / q) / 2 := by
  have hcpos : 0 < c := lt_of_lt_of_le (tailThreshold_pos p q) hc
  have hΓ := Gamma_one_div_pos hq
  have hD : 0 < Real.Gamma (1 / q + p / q) := Real.Gamma_pos_of_pos (by positivity)
  have hr : 0 < p / q := div_pos hp hq
  set B : ℝ := 2 * Real.Gamma (1 / q + p / q) / Real.Gamma (1 / q) with hB
  have hBpos : 0 < B := by positivity
  have hcB : B ^ (q / p) ≤ c := le_trans (le_max_right _ _) hc
  -- `c^{p/q} ≥ B`
  have hcr : B ≤ c ^ (p / q) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hBpos.le _) hcB hr.le
    rwa [← Real.rpow_mul hBpos.le, show q / p * (p / q) = 1 by field_simp, Real.rpow_one] at this
  rw [Real.rpow_neg hcpos.le, inv_mul_eq_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hcpos _)
    two_pos]
  calc Real.Gamma (1 / q + p / q) * 2 = B * Real.Gamma (1 / q) := by rw [hB]; field_simp
    _ ≤ c ^ (p / q) * Real.Gamma (1 / q) := mul_le_mul_of_nonneg_right hcr hΓ.le
    _ = Real.Gamma (1 / q) * c ^ (p / q) := mul_comm _ _

/-- **Rate of the Gamma tail for the profile moments**: beyond the threshold,
`|I_k/I₀ − Γ_k/Γ₀| ≤ C_k c^{-p/q}`. -/
theorem tailRatio_sub_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {k : ℝ} (hk : 0 ≤ k) {c : ℝ}
    (hc : tailThreshold p q ≤ c) :
    |tailIntegral p q k c / tailIntegral p q 0 c - Real.Gamma (k + 1 / q) / Real.Gamma (0 + 1 / q)|
      ≤ c ^ (-(p / q)) * (2 * (Real.Gamma (k + 1 / q + p / q) * Real.Gamma (0 + 1 / q) +
        Real.Gamma (k + 1 / q) * Real.Gamma (0 + 1 / q + p / q)) / Real.Gamma (0 + 1 / q) ^ 2) := by
  have hcpos : 0 < c := lt_of_lt_of_le (tailThreshold_pos p q) hc
  obtain ⟨hk1, hk2⟩ := tailIntegral_sub_le hp hq hk hcpos
  obtain ⟨h01, h02⟩ := tailIntegral_sub_le hp hq (k := 0) le_rfl hcpos
  have hΓ₀ : 0 < Real.Gamma (0 + 1 / q) := by rw [zero_add]; exact Gamma_one_div_pos hq
  have hhalf := tail_deficit_half hp hq hc
  simp only [zero_add] at h01 h02 hhalf hΓ₀ ⊢
  refine ratio_perturb_bound (Γ₀ := Real.Gamma (1 / q)) hΓ₀ (Real.Gamma_pos_of_pos
    (by positivity)).le (Real.Gamma_pos_of_pos (by positivity)).le
    (Real.Gamma_pos_of_pos (by positivity)).le (Real.rpow_nonneg hcpos.le _) ?_ ?_ ?_
  · linarith
  · rw [abs_of_nonneg hk1]; exact hk2
  · rw [abs_of_nonneg h01]; exact h02


/-- The rate constant `C_k = 2(Γ(k+1/q+p/q)Γ(1/q) + Γ(k+1/q)Γ(1/q+p/q))/Γ(1/q)²`. -/
noncomputable def tailRateConst (p q k : ℝ) : ℝ :=
  2 * (Real.Gamma (k + 1 / q + p / q) * Real.Gamma (1 / q) +
    Real.Gamma (k + 1 / q) * Real.Gamma (1 / q + p / q)) / Real.Gamma (1 / q) ^ 2

theorem tailRateConst_nonneg {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ tailRateConst p q k := by
  unfold tailRateConst
  have := Gamma_one_div_pos hq
  have h1 : 0 < Real.Gamma (k + 1 / q + p / q) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Real.Gamma (k + 1 / q) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : 0 < Real.Gamma (1 / q + p / q) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-- The Gamma ratios of the profile limits. -/
theorem gamma_ratio_one {q : ℝ} (hq : 0 < q) :
    Real.Gamma (1 + 1 / q) / Real.Gamma (1 / q) = 1 / q := by
  rw [add_comm, Real.Gamma_add_one (one_div_pos.mpr hq).ne', mul_div_assoc,
    div_self (Gamma_one_div_pos hq).ne', mul_one]

theorem gamma_ratio_two {q : ℝ} (hq : 0 < q) :
    Real.Gamma (2 + 1 / q) / Real.Gamma (1 / q) = 1 / q * (1 / q + 1) := by
  have hq0 : (1 / q : ℝ) ≠ 0 := (one_div_pos.mpr hq).ne'
  rw [show (2 : ℝ) + 1 / q = (1 / q + 1) + 1 by ring, Real.Gamma_add_one (by positivity),
    Real.Gamma_add_one hq0, div_eq_iff (Gamma_one_div_pos hq).ne']
  ring

/-- The variance-rate constant `C_V = C₂ + C₁(2/q + C₁)`. -/
noncomputable def varRateConst (p q : ℝ) : ℝ :=
  tailRateConst p q 2 + tailRateConst p q 1 * (2 / q + tailRateConst p q 1)

/-- **Rate of the profile variance**: `|c² Var_c(y^q) − 1/q| ≤ C_V c^{-p/q}` beyond the
threshold. -/
theorem sq_mul_profileVar_sub_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hc : max (tailThreshold p q) 1 ≤ c) :
    |c ^ 2 * (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2) - 1 / q| ≤
      varRateConst p q * c ^ (-(p / q)) := by
  have hcT : tailThreshold p q ≤ c := le_trans (le_max_left _ _) hc
  have hc1 : (1 : ℝ) ≤ c := le_trans (le_max_right _ _) hc
  have hcpos : 0 < c := by linarith
  have hr : 0 < p / q := div_pos hp hq
  set ε : ℝ := c ^ (-(p / q)) with hε
  have hε0 : 0 ≤ ε := Real.rpow_nonneg hcpos.le _
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by linarith)
  have h1 := tailRatio_sub_le hp hq (k := 1) zero_le_one hcT
  have h2 := tailRatio_sub_le hp hq (k := 2) zero_le_two hcT
  simp only [zero_add] at h1 h2
  rw [gamma_ratio_one hq] at h1
  rw [gamma_ratio_two hq] at h2
  have hC1 : tailRateConst p q 1 = 2 * (Real.Gamma (1 + 1 / q + p / q) * Real.Gamma (1 / q) +
      Real.Gamma (1 + 1 / q) * Real.Gamma (1 / q + p / q)) / Real.Gamma (1 / q) ^ 2 := rfl
  have hC2 : tailRateConst p q 2 = 2 * (Real.Gamma (2 + 1 / q + p / q) * Real.Gamma (1 / q) +
      Real.Gamma (2 + 1 / q) * Real.Gamma (1 / q + p / q)) / Real.Gamma (1 / q) ^ 2 := rfl
  rw [← hC1] at h1
  rw [← hC2] at h2
  have hC1nn := tailRateConst_nonneg hp hq (k := 1) zero_le_one
  have hC2nn := tailRateConst_nonneg hp hq (k := 2) zero_le_two
  -- the exact ratio identities
  have e2 := sq_mul_profileSecond_eq (p := p) hq hcpos
  have e1 := mul_profileMean_eq (p := p) hq hcpos
  set R₁ := tailIntegral p q 1 c / tailIntegral p q 0 c with hR₁
  set R₂ := tailIntegral p q 2 c / tailIntegral p q 0 c with hR₂
  have eV : c ^ 2 * (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2) = R₂ - R₁ ^ 2 := by
    rw [← e2, ← e1]
    ring
  rw [eV]
  have hq' : 0 < 1 / q := one_div_pos.mpr hq
  -- `|R₁ + 1/q| ≤ C₁ + 2/q`
  have hsum : |R₁ + 1 / q| ≤ tailRateConst p q 1 + 2 / q := by
    calc |R₁ + 1 / q| = |(R₁ - 1 / q) + 2 * (1 / q)| := by ring_nf
      _ ≤ |R₁ - 1 / q| + |2 * (1 / q)| := abs_add_le _ _
      _ ≤ ε * tailRateConst p q 1 + 2 / q := by
          rw [abs_of_pos (by positivity : 0 < 2 * (1 / q))]
          have : 2 * (1 / q) = 2 / q := by ring
          linarith
      _ ≤ tailRateConst p q 1 + 2 / q := by nlinarith
  calc |R₂ - R₁ ^ 2 - 1 / q|
      = |(R₂ - 1 / q * (1 / q + 1)) - (R₁ - 1 / q) * (R₁ + 1 / q)| := by ring_nf
    _ ≤ |R₂ - 1 / q * (1 / q + 1)| + |(R₁ - 1 / q) * (R₁ + 1 / q)| := abs_sub _ _
    _ = |R₂ - 1 / q * (1 / q + 1)| + |R₁ - 1 / q| * |R₁ + 1 / q| := by rw [abs_mul]
    _ ≤ ε * tailRateConst p q 2 + ε * tailRateConst p q 1 * (tailRateConst p q 1 + 2 / q) :=
        add_le_add h2 (mul_le_mul h1 hsum (abs_nonneg _) (by positivity))
    _ = varRateConst p q * ε := by unfold varRateConst; ring

/-- **The speed defect is integrable**: `|√Var_c(y^q) − √(1/q)/c| ≤ (C_V/√(1/q)) c^{-(1 + p/q)}`. -/
theorem profileSpeed_defect_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hc : max (tailThreshold p q) 1 ≤ c) :
    |Real.sqrt (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2) - Real.sqrt (1 / q) / c| ≤
      varRateConst p q / Real.sqrt (1 / q) * c ^ (-(1 + p / q)) := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hc)
  have hq' : 0 < 1 / q := one_div_pos.mpr hq
  have hV := profileVar_nonneg hp hq.le hcpos.le
  set V := profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
    profilePosterior p q (fun y ↦ y ^ q) c ^ 2 with hVdef
  have hsq : Real.sqrt V = Real.sqrt (c ^ 2 * V) / c := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hcpos.le, mul_div_cancel_left₀ _ hcpos.ne']
  rw [hsq, ← sub_div, abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
  have h1 := abs_sqrt_sub_sqrt_le (mul_nonneg (sq_nonneg c) hV) hq'
  have h2 := sq_mul_profileVar_sub_le hp hq hc
  have hsκ : 0 < Real.sqrt (1 / q) := Real.sqrt_pos.mpr hq'
  calc |Real.sqrt (c ^ 2 * V) - Real.sqrt (1 / q)| ≤ |c ^ 2 * V - 1 / q| / Real.sqrt (1 / q) := h1
    _ ≤ varRateConst p q * c ^ (-(p / q)) / Real.sqrt (1 / q) :=
        div_le_div_of_nonneg_right h2 hsκ.le
    _ = varRateConst p q / Real.sqrt (1 / q) * c ^ (-(1 + p / q)) * c := by
        rw [Real.rpow_neg hcpos.le, Real.rpow_neg hcpos.le, Real.rpow_add hcpos, Real.rpow_one]
        field_simp

/-- The profile speed `h(c) = √Var_c(y^q)`. -/
noncomputable def profileSpeed (p q c : ℝ) : ℝ :=
  Real.sqrt (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
    profilePosterior p q (fun y ↦ y ^ q) c ^ 2)

theorem continuousOn_profileSpeed {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ContinuousOn (profileSpeed p q) (Ici 0) :=
  Real.continuous_sqrt.comp_continuousOn (continuousOn_profileVar hp hq)

/-- The tail threshold `c₂ = max(tailThreshold, 1)`. -/
noncomputable def speedThreshold (p q : ℝ) : ℝ := max (tailThreshold p q) 1

theorem speedThreshold_pos (p q : ℝ) : 0 < speedThreshold p q :=
  lt_of_lt_of_le zero_lt_one (le_max_right _ _)

/-- **The defect of the profile speed is integrable on the tail.** -/
theorem integrableOn_profileSpeed_defect {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun c ↦ profileSpeed p q c - Real.sqrt (1 / q) / c)
      (Ioi (speedThreshold p q)) := by
  have hr : 0 < p / q := div_pos hp hq
  have hc₂ := speedThreshold_pos p q
  have hbound : IntegrableOn (fun c : ℝ ↦ varRateConst p q / Real.sqrt (1 / q) *
      c ^ (-(1 + p / q))) (Ioi (speedThreshold p q)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hc₂).const_mul _
  refine hbound.mono' ?_ ?_
  · have hcont : ContinuousOn (fun c ↦ profileSpeed p q c - Real.sqrt (1 / q) / c)
        (Ioi (speedThreshold p q)) := by
      refine ((continuousOn_profileSpeed hp hq.le).mono fun c hc ↦ ?_).sub
        (continuousOn_const.div continuousOn_id fun c hc ↦ ?_)
      · exact le_of_lt (lt_trans hc₂ hc)
      · exact (lt_trans hc₂ hc).ne'
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun c hc ↦ ?_)
    rw [Real.norm_eq_abs]
    exact profileSpeed_defect_le hp hq (le_of_lt hc)

/-- **The renormalised profile length converges**: `∫_{c₀}^T h − √(1/q) log T → K(c₀)`. -/
theorem profileLength_renormalised {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    Tendsto (fun T ↦ (∫ c in c₀..T, profileSpeed p q c) - Real.sqrt (1 / q) * Real.log T) atTop
      (𝓝 ((∫ c in c₀..speedThreshold p q, profileSpeed p q c) +
        (∫ c in Ioi (speedThreshold p q), (profileSpeed p q c - Real.sqrt (1 / q) / c)) -
        Real.sqrt (1 / q) * Real.log (speedThreshold p q))) := by
  set c₂ := speedThreshold p q with hc₂def
  have hc₂ : 0 < c₂ := speedThreshold_pos p q
  have hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable (profileSpeed p q) volume a b :=
    fun a b ha hb ↦ by
      have hsub : uIcc a b ⊆ Ici 0 := fun x hx ↦ le_trans (le_min ha hb) hx.1
      exact ((continuousOn_profileSpeed hp hq.le).mono hsub).intervalIntegrable
  have hdef := integrableOn_profileSpeed_defect hp hq
  have hI := intervalIntegral_tendsto_integral_Ioi c₂ hdef (tendsto_id (x := atTop))
  have key := ((tendsto_const_nhds (x := ∫ c in c₀..c₂, profileSpeed p q c)).add hI).sub
    (tendsto_const_nhds (x := Real.sqrt (1 / q) * Real.log c₂))
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop c₂] with T hT
  have hTpos : 0 < T := lt_of_lt_of_le hc₂ hT
  have hinv : IntervalIntegrable (fun c : ℝ ↦ c⁻¹) volume c₂ T := by
    refine intervalIntegral.intervalIntegrable_inv (f := fun x ↦ x) (fun x hx ↦ ?_) continuousOn_id
    rw [Set.uIcc_of_le hT] at hx
    exact (lt_of_lt_of_le hc₂ hx.1).ne'
  have hdiv : IntervalIntegrable (fun c : ℝ ↦ Real.sqrt (1 / q) / c) volume c₂ T := by
    simpa [div_eq_mul_inv] using hinv.const_mul (Real.sqrt (1 / q))
  have hsplit : ∫ c in c₀..T, profileSpeed p q c =
      (∫ c in c₀..c₂, profileSpeed p q c) + ∫ c in c₂..T, profileSpeed p q c :=
    (intervalIntegral.integral_add_adjacent_intervals (hint c₀ c₂ hc₀ hc₂.le)
      (hint c₂ T hc₂.le hTpos.le)).symm
  have hsub : ∫ c in c₂..T, (profileSpeed p q c - Real.sqrt (1 / q) / c) =
      (∫ c in c₂..T, profileSpeed p q c) - Real.sqrt (1 / q) * Real.log (T / c₂) := by
    rw [intervalIntegral.integral_sub (hint c₂ T hc₂.le hTpos.le) hdiv,
      ← integral_inv_of_pos hc₂ hTpos, ← intervalIntegral.integral_const_mul]
    congr 1
  simp only [id_eq]
  rw [hsub, hsplit, Real.log_div hTpos.ne' hc₂.ne']
  ring

/-- **The wall recedes, strong form**: for the two-monomial family the length from the wall
window to a fixed data point, renormalised by `σ* √(1/q) log t`, converges. -/
theorem wall_recedes_strong {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hqp : q < p) {a₁ : ℝ}
    (ha₁ : 0 < a₁) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    ∃ K : ℝ, Tendsto (fun t ↦ (∫ a in (c₀ * t ^ (-(1 - q / p)))..a₁, Real.sqrt (fisherSpeed
      (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q) (twoMonoVel q) t a)) -
      (1 - q / p) * Real.sqrt (1 / q) * Real.log t) atTop (𝓝 K) := by
  have hσ : 0 < 1 - q / p := by
    rw [sub_pos, div_lt_one hp]
    exact hqp
  have hT : Tendsto (fun t : ℝ ↦ a₁ * t ^ (1 - q / p)) atTop atTop :=
    (tendsto_rpow_atTop hσ).const_mul_atTop ha₁
  have hren := (profileLength_renormalised hp hq hc₀).comp hT
  refine ⟨_, (hren.add (tendsto_const_nhds (x := Real.sqrt (1 / q) * Real.log a₁))).congr' ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hw := wall_window_length (q := q) hp ht c₀ (a₁ * t ^ (1 - q / p))
  have e : a₁ * t ^ (1 - q / p) * t ^ (-(1 - q / p)) = a₁ := by
    rw [mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  rw [e] at hw
  simp only [Function.comp_apply]
  rw [hw, Real.log_mul ha₁.ne' (Real.rpow_pos_of_pos ht _).ne', Real.log_rpow ht]
  unfold profileSpeed
  ring


end Laplace.Multi
