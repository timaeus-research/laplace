/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RayVarianceSandwich

/-!
# The shell-mass classification of Fisher accessibility

Along a natural ray `p_t ∝ e^{−tg} w ν` with slack `0 ≤ g ≤ R`, the Fisher speed is comparable to
`√C₂(t)`, `C₂(t) = ∫_{g>0} g² w e^{−tg} dν` (`RayVarianceSandwich`).  Decompose the off-face mass
into dyadic shells `a_k = ∫_{R/2^{k+1} < g ≤ R/2^k} w dν`.  Then

  `∫₀^∞ √C₂(t) dt ≤ 4 Σ_k √a_k`          (`lintegral_sqrt_secondMomentE_le`)
  `Σ_k √a_k ≤ 2e ∫_{1/R}^∞ √C₂(t) dt`   (`tsum_sqrt_shellMass_le`)

so the ray has finite Fisher length **iff** `Σ_k √a_k < ∞`
(`lintegral_sqrt_secondMomentE_lt_top_iff`).
Both bounds are elementary: shell `k` contributes at most `(R/2^k)² e^{−tR/2^{k+1}} a_k` to `C₂(t)`
and at least `(R/2^{k+1})² e^{−2} a_k` for `t ∈ [2^k/R, 2^{k+1}/R]`; the upper bound uses the
countable subadditivity of the square root (`ENNReal.rpow_tsum_le_tsum_rpow`).  Everything is
stated with Lebesgue integrals in `ℝ≥0∞`, so no integrability or summability hypotheses appear.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Subadditive

theorem ENNReal.rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) : (∑ i ∈ s, f i) ^ p ≤ ∑ i ∈ s, f i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hp0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1).trans (add_le_add le_rfl ih)

/-- **Countable subadditivity of `x ↦ x^p` on `ℝ≥0∞` for `0 < p ≤ 1`.** -/
theorem ENNReal.rpow_tsum_le_tsum_rpow {ι : Type*} (f : ι → ℝ≥0∞) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) : (∑' i, f i) ^ p ≤ ∑' i, f i ^ p := by
  rw [ENNReal.tsum_eq_iSup_sum, Monotone.map_iSup_of_continuousAt
    ENNReal.continuous_rpow_const.continuousAt (ENNReal.monotone_rpow_of_nonneg hp0.le)
    (by simp [ENNReal.zero_rpow_of_pos hp0])]
  exact iSup_le fun s ↦ (ENNReal.rpow_sum_le_sum_rpow s f hp0 hp1).trans (ENNReal.sum_le_tsum s)

end Subadditive

section Shells

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) (w g : X → ℝ) (R : ℝ)

/-- The dyadic shell `R/2^{k+1} < g ≤ R/2^k`. -/
def dyadicShell (k : ℕ) : Set X := g ⁻¹' Ioc (R / 2 ^ (k + 1)) (R / 2 ^ k)

/-- The shell mass `a_k = ∫_{shell k} w dν`. -/
noncomputable def shellMass (k : ℕ) : ℝ≥0∞ := ∫⁻ x in dyadicShell g R k, ENNReal.ofReal (w x) ∂ν

/-- The second slack moment `C₂(t) = ∫_{g>0} g² w e^{−tg} dν`. -/
noncomputable def secondMomentE (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | 0 < g x}, ENNReal.ofReal (g x ^ 2 * (w x * Real.exp (-(t * g x)))) ∂ν

variable {w g R}

theorem measurableSet_dyadicShell (hg : Measurable g) (k : ℕ) : MeasurableSet (dyadicShell g R k) :=
  hg measurableSet_Ioc

omit [MeasurableSpace X] in
theorem dyadicShell_subset_pos (hR : 0 < R) (k : ℕ) : dyadicShell g R k ⊆ {x | 0 < g x} :=
  fun x hx ↦ lt_trans (by positivity) hx.1

omit [MeasurableSpace X] in
/-- Every point with `0 < g ≤ R` lies in some shell. -/
theorem pos_subset_iUnion_dyadicShell (hgR : ∀ x, g x ≤ R) :
    {x | 0 < g x} ⊆ ⋃ k, dyadicShell g R k := by
  intro x hx
  have hx' : 0 < g x := hx
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := R / g x) (y := (2 : ℝ))
    ((one_le_div hx').2 (hgR x)) one_lt_two
  refine mem_iUnion.2 ⟨n, ?_, ?_⟩
  · rw [div_lt_iff₀ hx'] at hn2
    rw [div_lt_iff₀ (by positivity)]
    linarith
  · rw [le_div_iff₀ hx'] at hn1
    rw [le_div_iff₀ (by positivity)]
    linarith

/-- The upper shell amplitude `d_k(t) = (R/2^k) e^{−tR/2^{k+2}}`. -/
noncomputable def dAmp (R : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  R / 2 ^ k * Real.exp (-(t * (R / 2 ^ (k + 2))))

/-- The lower shell amplitude `e_k = (R/2^{k+1}) e^{−1}`. -/
noncomputable def eAmp (R : ℝ) (k : ℕ) : ℝ := R / 2 ^ (k + 1) * Real.exp (-1)

omit [MeasurableSpace X] in
theorem dAmp_sq (k : ℕ) (t : ℝ) :
    dAmp R k t ^ 2 = (R / 2 ^ k) ^ 2 * Real.exp (-(t * (R / 2 ^ (k + 1)))) := by
  rw [dAmp, mul_pow, sq (Real.exp _), ← Real.exp_add]
  congr 2
  rw [pow_succ, pow_succ]
  field_simp
  ring

omit [MeasurableSpace X] in
theorem eAmp_sq (k : ℕ) : eAmp R k ^ 2 = (R / 2 ^ (k + 1)) ^ 2 * Real.exp (-2) := by
  rw [eAmp, mul_pow, sq (Real.exp _), ← Real.exp_add]
  norm_num

omit [MeasurableSpace X] in
theorem dAmp_nonneg (hR : 0 < R) (k : ℕ) (t : ℝ) : 0 ≤ dAmp R k t :=
  mul_nonneg (div_nonneg hR.le (by positivity)) (Real.exp_pos _).le

omit [MeasurableSpace X] in
theorem eAmp_nonneg (hR : 0 < R) (k : ℕ) : 0 ≤ eAmp R k :=
  mul_nonneg (div_nonneg hR.le (by positivity)) (Real.exp_pos _).le

omit [MeasurableSpace X] in
/-- On shell `k`, for `t ≥ 0`, the integrand is at most `d_k(t)² w`. -/
theorem integrand_le_on_shell (hw0 : ∀ x, 0 ≤ w x) (hR : 0 < R) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    {x : X} (hx : x ∈ dyadicShell g R k) :
    g x ^ 2 * (w x * Real.exp (-(t * g x))) ≤ dAmp R k t ^ 2 * w x := by
  rw [dAmp_sq]
  obtain ⟨hx1, hx2⟩ := hx
  have hg0 : 0 < g x := lt_trans (by positivity) hx1
  have h1 : g x ^ 2 ≤ (R / 2 ^ k) ^ 2 := pow_le_pow_left₀ hg0.le hx2 2
  have h2 : Real.exp (-(t * g x)) ≤ Real.exp (-(t * (R / 2 ^ (k + 1)))) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hx1.le ht))
  calc g x ^ 2 * (w x * Real.exp (-(t * g x)))
      ≤ (R / 2 ^ k) ^ 2 * (w x * Real.exp (-(t * (R / 2 ^ (k + 1))))) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (hw0 x))
          (mul_nonneg (hw0 x) (Real.exp_pos _).le) (by positivity)
    _ = _ := by ring

/-- **Shellwise upper bound on the second moment**: `C₂(t) ≤ Σ_k d_k(t)² a_k`. -/
theorem secondMomentE_le_tsum (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hR : 0 < R)
    (hgR : ∀ x, g x ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    secondMomentE ν w g t ≤ ∑' k, ENNReal.ofReal (dAmp R k t ^ 2) * shellMass ν w g R k := by
  unfold secondMomentE
  calc ∫⁻ x in {x | 0 < g x}, ENNReal.ofReal (g x ^ 2 * (w x * Real.exp (-(t * g x)))) ∂ν
      ≤ ∫⁻ x in ⋃ k, dyadicShell g R k,
          ENNReal.ofReal (g x ^ 2 * (w x * Real.exp (-(t * g x)))) ∂ν :=
        lintegral_mono_set (pos_subset_iUnion_dyadicShell hgR)
    _ ≤ ∑' k, ∫⁻ x in dyadicShell g R k,
          ENNReal.ofReal (g x ^ 2 * (w x * Real.exp (-(t * g x)))) ∂ν :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' k, ∫⁻ x in dyadicShell g R k, ENNReal.ofReal (dAmp R k t ^ 2 * w x) ∂ν := by
        refine ENNReal.tsum_le_tsum fun k ↦ ?_
        refine setLIntegral_mono (hw.const_mul _).ennreal_ofReal fun x hx ↦ ?_
        exact ENNReal.ofReal_le_ofReal (integrand_le_on_shell hw0 hR ht k hx)
    _ = ∑' k, ENNReal.ofReal (dAmp R k t ^ 2) * shellMass ν w g R k := by
        refine tsum_congr fun k ↦ ?_
        unfold shellMass
        rw [← lintegral_const_mul _ hw.ennreal_ofReal]
        refine lintegral_congr fun x ↦ ?_
        rw [ENNReal.ofReal_mul (sq_nonneg _)]

/-- The square root of the second moment is bounded by `Σ_k d_k(t) √a_k`. -/
theorem sqrt_secondMomentE_le_tsum (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hR : 0 < R)
    (hgR : ∀ x, g x ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    secondMomentE ν w g t ^ (1 / 2 : ℝ) ≤
      ∑' k, ENNReal.ofReal (dAmp R k t) * shellMass ν w g R k ^ (1 / 2 : ℝ) := by
  calc secondMomentE ν w g t ^ (1 / 2 : ℝ)
      ≤ (∑' k, ENNReal.ofReal (dAmp R k t ^ 2) * shellMass ν w g R k) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (secondMomentE_le_tsum ν hw hw0 hR hgR ht) (by norm_num)
    _ ≤ ∑' k, (ENNReal.ofReal (dAmp R k t ^ 2) * shellMass ν w g R k) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_tsum_le_tsum_rpow _ (by norm_num) (by norm_num)
    _ = ∑' k, ENNReal.ofReal (dAmp R k t) * shellMass ν w g R k ^ (1 / 2 : ℝ) := by
        refine tsum_congr fun k ↦ ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (dAmp_nonneg hR k t)]

omit [MeasurableSpace X] in
/-- The time integral of the shell amplitude is `4`. -/
theorem lintegral_dAmp (hR : 0 < R) (k : ℕ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (dAmp R k t) = 4 := by
  have hc : 0 < R / 2 ^ (k + 2) := by positivity
  have hint : IntegrableOn (fun t : ℝ ↦ dAmp R k t) (Ioi 0) := by
    have this : IntegrableOn (fun t : ℝ ↦ R / 2 ^ k * Real.exp (-(R / 2 ^ (k + 2) * t))) (Ioi 0) :=
      (integrableOn_Ioi_exp_neg_mul hc 0).const_mul (R / 2 ^ k)
    refine this.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    simp only [dAmp, mul_comm t]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun t ↦ dAmp_nonneg hR k t)]
  have h := integral_Ioi_mul_exp_neg_mul hc 0
  rw [integral_const_mul, mul_zero, neg_zero, Real.exp_zero] at h
  have h' : ∫ t in Ioi (0 : ℝ), Real.exp (-(R / 2 ^ (k + 2) * t)) = 1 / (R / 2 ^ (k + 2)) := by
    rw [eq_div_iff hc.ne', mul_comm]
    exact h
  have e : (fun t : ℝ ↦ dAmp R k t) = fun t ↦ R / 2 ^ k * Real.exp (-(R / 2 ^ (k + 2) * t)) := by
    funext t
    simp only [dAmp, mul_comm t]
  rw [e, integral_const_mul, h', show R / 2 ^ k * (1 / (R / 2 ^ (k + 2))) = 4 by
    rw [pow_succ, pow_succ]
    field_simp
    ring]
  exact ENNReal.ofReal_ofNat 4

/-- **The upper shell bound**: `∫₀^∞ √C₂(t) dt ≤ 4 Σ_k √a_k`. -/
theorem lintegral_sqrt_secondMomentE_le (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hR : 0 < R)
    (hgR : ∀ x, g x ≤ R) :
    ∫⁻ t in Ioi (0 : ℝ), secondMomentE ν w g t ^ (1 / 2 : ℝ) ≤
      4 * ∑' k, shellMass ν w g R k ^ (1 / 2 : ℝ) := by
  have hmeas : ∀ k, Measurable fun t : ℝ ↦ ENNReal.ofReal (dAmp R k t) := fun k ↦ by
    refine Measurable.ennreal_ofReal ?_
    unfold dAmp
    fun_prop
  calc ∫⁻ t in Ioi (0 : ℝ), secondMomentE ν w g t ^ (1 / 2 : ℝ)
      ≤ ∫⁻ t in Ioi (0 : ℝ),
          ∑' k, ENNReal.ofReal (dAmp R k t) * shellMass ν w g R k ^ (1 / 2 : ℝ) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun t ht ↦ ?_))
        exact sqrt_secondMomentE_le_tsum ν hw hw0 hR hgR (le_of_lt ht)
    _ = ∑' k, ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (dAmp R k t) * shellMass ν w g R k ^ (1 / 2 : ℝ) :=
        lintegral_tsum fun k ↦ ((hmeas k).mul_const _).aemeasurable
    _ = ∑' k, 4 * shellMass ν w g R k ^ (1 / 2 : ℝ) := by
        refine tsum_congr fun k ↦ ?_
        rw [lintegral_mul_const _ (hmeas k), lintegral_dAmp hR k]
    _ = 4 * ∑' k, shellMass ν w g R k ^ (1 / 2 : ℝ) := ENNReal.tsum_mul_left

omit [MeasurableSpace X] in
/-- On shell `k`, for `t ∈ [2^k/R, 2^{k+1}/R]`, the integrand is at least `e_k² w`. -/
theorem le_integrand_on_shell (hw0 : ∀ x, 0 ≤ w x) (hR : 0 < R) {t : ℝ} (k : ℕ)
    (ht : t ∈ Ico ((2 : ℝ) ^ k / R) (2 ^ (k + 1) / R)) {x : X} (hx : x ∈ dyadicShell g R k) :
    eAmp R k ^ 2 * w x ≤ g x ^ 2 * (w x * Real.exp (-(t * g x))) := by
  rw [eAmp_sq]
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : (R / 2 ^ (k + 1)) ^ 2 ≤ g x ^ 2 := pow_le_pow_left₀ (by positivity) hx1.le 2
  have htg : t * g x ≤ 2 := by
    calc t * g x ≤ 2 ^ (k + 1) / R * (R / 2 ^ k) :=
          mul_le_mul ht.2.le hx2 (lt_trans (by positivity) hx1).le (by positivity)
      _ = 2 := by
          rw [pow_succ]
          field_simp
  have h2 : Real.exp (-2) ≤ Real.exp (-(t * g x)) := Real.exp_le_exp.2 (neg_le_neg htg)
  calc (R / 2 ^ (k + 1)) ^ 2 * Real.exp (-2) * w x
      ≤ g x ^ 2 * Real.exp (-(t * g x)) * w x :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)) (hw0 x)
    _ = _ := by ring

/-- **Shellwise lower bound on the second moment**: `e_k² a_k ≤ C₂(t)` for
`t ∈ [2^k/R, 2^{k+1}/R]`. -/
theorem le_secondMomentE (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hg : Measurable g) (hR : 0 < R)
    {t : ℝ} (k : ℕ) (ht : t ∈ Ico ((2 : ℝ) ^ k / R) (2 ^ (k + 1) / R)) :
    ENNReal.ofReal (eAmp R k ^ 2) * shellMass ν w g R k ≤ secondMomentE ν w g t := by
  unfold shellMass secondMomentE
  rw [← lintegral_const_mul _ hw.ennreal_ofReal]
  calc ∫⁻ x in dyadicShell g R k, ENNReal.ofReal (eAmp R k ^ 2) * ENNReal.ofReal (w x) ∂ν
      ≤ ∫⁻ x in dyadicShell g R k, ENNReal.ofReal (g x ^ 2 * (w x * Real.exp (-(t * g x)))) ∂ν := by
        refine lintegral_mono_ae ((ae_restrict_iff' (measurableSet_dyadicShell hg k)).2
          (Eventually.of_forall fun x hx ↦ ?_))
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (le_integrand_on_shell hw0 hR k ht hx)
    _ ≤ _ := lintegral_mono_set (dyadicShell_subset_pos hR k)

omit [MeasurableSpace X] in
/-- The dyadic time intervals are pairwise disjoint. -/
theorem pairwise_disjoint_dyadicIco (hR : 0 < R) :
    Pairwise (Function.onFun Disjoint fun k : ℕ ↦ Ico ((2 : ℝ) ^ k / R) (2 ^ (k + 1) / R)) := by
  have key : ∀ i j : ℕ, i < j →
      Disjoint (Ico ((2 : ℝ) ^ i / R) (2 ^ (i + 1) / R))
        (Ico ((2 : ℝ) ^ j / R) (2 ^ (j + 1) / R)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t hti htj
    have h1 : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j := pow_le_pow_right₀ one_le_two hij
    have h2 : (2 : ℝ) ^ (i + 1) / R ≤ 2 ^ j / R := div_le_div_of_nonneg_right h1 hR.le
    linarith [hti.2, htj.1]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- **The lower shell bound**: `Σ_k √a_k ≤ 2e ∫_{1/R}^∞ √C₂(t) dt`. -/
theorem tsum_sqrt_shellMass_le (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hg : Measurable g)
    (hR : 0 < R) :
    ∑' k, shellMass ν w g R k ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * Real.exp 1) *
        ∫⁻ t in Ici (1 / R), secondMomentE ν w g t ^ (1 / 2 : ℝ) := by
  have hterm : ∀ k, ENNReal.ofReal (Real.exp (-1) / 2) * shellMass ν w g R k ^ (1 / 2 : ℝ) ≤
      ∫⁻ t in Ico ((2 : ℝ) ^ k / R) (2 ^ (k + 1) / R), secondMomentE ν w g t ^ (1 / 2 : ℝ) := by
    intro k
    have hpt : ∀ t ∈ Ico ((2 : ℝ) ^ k / R) (2 ^ (k + 1) / R),
        ENNReal.ofReal (eAmp R k) * shellMass ν w g R k ^ (1 / 2 : ℝ) ≤
          secondMomentE ν w g t ^ (1 / 2 : ℝ) := fun t ht ↦ by
      have h := ENNReal.rpow_le_rpow (le_secondMomentE ν hw hw0 hg hR k ht)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq (eAmp_nonneg hR k)] at h
    calc ENNReal.ofReal (Real.exp (-1) / 2) * shellMass ν w g R k ^ (1 / 2 : ℝ)
        = ∫⁻ t in Ico ((2 : ℝ) ^ k / R) (2 ^ (k + 1) / R),
            ENNReal.ofReal (eAmp R k) * shellMass ν w g R k ^ (1 / 2 : ℝ) := by
          rw [setLIntegral_const, Real.volume_Ico, mul_right_comm,
            ← ENNReal.ofReal_mul (eAmp_nonneg hR k)]
          congr 2
          rw [eAmp, pow_succ]
          field_simp
          ring
      _ ≤ _ := lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).2
          (Eventually.of_forall hpt))
  have hsum : ENNReal.ofReal (Real.exp (-1) / 2) * ∑' k, shellMass ν w g R k ^ (1 / 2 : ℝ) ≤
      ∫⁻ t in Ici (1 / R), secondMomentE ν w g t ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' k, ENNReal.ofReal (Real.exp (-1) / 2) * shellMass ν w g R k ^ (1 / 2 : ℝ)
        ≤ ∑' k, ∫⁻ t in Ico ((2 : ℝ) ^ k / R) (2 ^ (k + 1) / R),
            secondMomentE ν w g t ^ (1 / 2 : ℝ) := ENNReal.tsum_le_tsum hterm
      _ = ∫⁻ t in ⋃ k, Ico ((2 : ℝ) ^ k / R) (2 ^ (k + 1) / R),
            secondMomentE ν w g t ^ (1 / 2 : ℝ) :=
          (lintegral_iUnion (fun _ ↦ measurableSet_Ico) (pairwise_disjoint_dyadicIco hR) _).symm
      _ ≤ _ := by
          refine lintegral_mono_set (iUnion_subset fun k t ht ↦ ?_)
          have : (1 : ℝ) / R ≤ 2 ^ k / R :=
            div_le_div_of_nonneg_right (one_le_pow₀ one_le_two) hR.le
          exact le_trans this ht.1
  calc ∑' k, shellMass ν w g R k ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (2 * Real.exp 1) *
          (ENNReal.ofReal (Real.exp (-1) / 2) * ∑' k, shellMass ν w g R k ^ (1 / 2 : ℝ)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show 2 * Real.exp 1 * (Real.exp (-1) / 2) = 1 by
            rw [Real.exp_neg]
            field_simp, ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr

/-- **The shell-mass classification**: the ray has finite Fisher length (`∫ √C₂ < ∞` on any tail)
iff the dyadic shell masses have summable square roots. -/
theorem lintegral_sqrt_secondMomentE_lt_top_iff (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hg : Measurable g) (hR : 0 < R) (hgR : ∀ x, g x ≤ R) :
    (∫⁻ t in Ioi (0 : ℝ), secondMomentE ν w g t ^ (1 / 2 : ℝ)) < ⊤ ↔
      (∑' k, shellMass ν w g R k ^ (1 / 2 : ℝ)) < ⊤ := by
  constructor
  · intro h
    refine lt_of_le_of_lt (tsum_sqrt_shellMass_le ν hw hw0 hg hR) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (lintegral_mono_set ?_) h)
    intro t ht
    exact lt_of_lt_of_le (one_div_pos.2 hR) ht
  · intro h
    exact lt_of_le_of_lt (lintegral_sqrt_secondMomentE_le ν hw hw0 hR hgR)
      (ENNReal.mul_lt_top ENNReal.ofNat_lt_top h)

end Shells

end Laplace.Multi
