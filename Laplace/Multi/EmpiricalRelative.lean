/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.EmpiricalStability

/-!
# The empirical correspondence: relative stability and finite-order detection

The empirical loss `K` is within `δ` of the population loss `L` on the supports of the test `φ`
and the window `χ`. Writing `w = e^{-t(K − L)} ∈ [e^{-tδ}, e^{tδ}]`, the normalized expectation
of `K` is a reweighting of that of `L`, and

  `|⟨φ⟩_K − ⟨φ⟩_L| ≤ (e^{2tδ} − 1) · ⟨|φ|⟩_L`

(`abs_normalized_sub_le_relative`): a RELATIVE error of order `tδ`, with no amplification by
`1/Z` and no dependence on the dimension or on the singularity exponent. This supersedes the
`1/Z`-amplified bound of `EmpiricalStability`.

Consequences. (1) Finite-order detection: if two population losses differ at order `t^{-r}`
for the test `φ` while `⟨|φ|⟩ ≤ M t^{-s}`, the empirical difference is at least
`a t^{-r} − 2M t^{-s}(e^{2tδ} − 1)`, and a same-germ pair stays below
`B(t) + 2M t^{-s}(e^{2tδ} − 1)`;
a threshold separates the two cases as soon as
`a t^{-r} > B(t) + 4M t^{-s}(e^{2tδ} − 1)`.
(2) The empirical leading coefficient is the population one along any temperature schedule
with `δ_n t_n^{r+1−s} → 0`; for `δ_n ≤ C n^{-1/2}` and `t_n = n^β` this is `β (r + 1 − s) < 1/2`,
i.e. `β k < 1` for a rescaled monomial whose first jet difference is at degree `k`
(`r = (k−2)/2`, `s = 0`). (3) The probabilistic layer is a transfer along a good event.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- `e^{2a} − 1 ≤ 2 e² a` for `0 ≤ a ≤ 1`. -/
theorem exp_two_mul_sub_one_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (2 * a) - 1 ≤ 2 * Real.exp 2 * a := by
  have h := Real.add_one_le_exp (-(2 * a))
  have hE := Real.exp_pos (2 * a)
  have h1 : Real.exp (-(2 * a)) * Real.exp (2 * a) = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : (-(2 * a) + 1) * Real.exp (2 * a) ≤ 1 := by
    calc (-(2 * a) + 1) * Real.exp (2 * a) ≤ Real.exp (-(2 * a)) * Real.exp (2 * a) :=
          mul_le_mul_of_nonneg_right h hE.le
      _ = 1 := h1
  have h3 : Real.exp (2 * a) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * a)]

/-- **Relative stability of normalized expectations under uniform closeness.** -/
theorem abs_normalized_sub_le_relative {K L φ χ : (ι → ℝ) → ℝ}
    (hKc : Continuous K) (hLc : Continuous L)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {δ : ℝ} (hδ : 0 ≤ δ) (hcloseφ : ∀ w ∈ tsupport φ, |K w - L w| ≤ δ)
    (hcloseχ : ∀ w ∈ tsupport χ, |K w - L w| ≤ δ) {t : ℝ} (ht : 0 ≤ t)
    (hZL : 0 < ∫ w, χ w * Real.exp (-(t * L w))) :
    |(∫ w, φ w * Real.exp (-(t * K w))) / (∫ w, χ w * Real.exp (-(t * K w))) -
      (∫ w, φ w * Real.exp (-(t * L w))) / (∫ w, χ w * Real.exp (-(t * L w)))| ≤
      (Real.exp (2 * (t * δ)) - 1) *
        ((∫ w, |φ w| * Real.exp (-(t * L w))) / ∫ w, χ w * Real.exp (-(t * L w))) := by
  -- the reweighting
  set a : ℝ := t * δ with ha_def
  have hw : ∀ x, Real.exp (-(t * K x)) = Real.exp (-(t * (K x - L x))) * Real.exp (-(t * L x)) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    ring
  have hwb : ∀ x, |K x - L x| ≤ δ →
      Real.exp (-a) ≤ Real.exp (-(t * (K x - L x))) ∧
        Real.exp (-(t * (K x - L x))) ≤ Real.exp a := by
    intro x hx
    obtain ⟨h1, h2⟩ := abs_le.mp hx
    constructor
    · rw [Real.exp_le_exp]
      nlinarith
    · rw [Real.exp_le_exp]
      nlinarith
  set ZL := ∫ w, χ w * Real.exp (-(t * L w)) with hZL_def
  set ZK := ∫ w, χ w * Real.exp (-(t * K w)) with hZK_def
  set NL := ∫ w, φ w * Real.exp (-(t * L w)) with hNL_def
  set NK := ∫ w, φ w * Real.exp (-(t * K w)) with hNK_def
  set IA := ∫ w, |φ w| * Real.exp (-(t * L w)) with hIA_def
  have hZLint := integrable_mul_exp_neg_of_compactSupport hχc hχs hLc t
  have hZKint := integrable_mul_exp_neg_of_compactSupport hχc hχs hKc t
  have hNLint := integrable_mul_exp_neg_of_compactSupport hφc hφs hLc t
  have hNKint := integrable_mul_exp_neg_of_compactSupport hφc hφs hKc t
  have hIAint : Integrable fun w ↦ |φ w| * Real.exp (-(t * L w)) :=
    integrable_mul_exp_neg_of_compactSupport hφc.abs hφs.abs hLc t
  -- the partition value of `K` is sandwiched
  have hZK_lower : Real.exp (-a) * ZL ≤ ZK := by
    rw [hZK_def, hZL_def, ← integral_const_mul]
    refine integral_mono (hZLint.const_mul _) hZKint fun x ↦ ?_
    by_cases hx : x ∈ tsupport χ
    · rw [hw x]
      have := (hwb x (hcloseχ x hx)).1
      have hχx := hχ0 x
      have he := (Real.exp_pos (-(t * L x))).le
      nlinarith [mul_nonneg hχx he]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hZK_upper : ZK ≤ Real.exp a * ZL := by
    rw [hZK_def, hZL_def, ← integral_const_mul]
    refine integral_mono hZKint (hZLint.const_mul _) fun x ↦ ?_
    by_cases hx : x ∈ tsupport χ
    · rw [hw x]
      have := (hwb x (hcloseχ x hx)).2
      have hχx := hχ0 x
      have he := (Real.exp_pos (-(t * L x))).le
      nlinarith [mul_nonneg hχx he]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hZKpos : 0 < ZK := lt_of_lt_of_le (by positivity) hZK_lower
  set b : ℝ := ZK / ZL with hb_def
  have hb1 : Real.exp (-a) ≤ b := by
    rw [hb_def, le_div_iff₀ hZL]
    exact hZK_lower
  have hb2 : b ≤ Real.exp a := by
    rw [hb_def, div_le_iff₀ hZL]
    exact hZK_upper
  -- the difference as one integral
  have hdiff : NK / ZK - NL / ZL = (∫ w, φ w * (Real.exp (-(t * (K w - L w))) - b) *
      Real.exp (-(t * L w))) / ZK := by
    have hNK' : NK = ∫ w, φ w * Real.exp (-(t * (K w - L w))) * Real.exp (-(t * L w)) := by
      rw [hNK_def]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      beta_reduce
      rw [hw x, mul_assoc]
    have hbNL : b * NL = ∫ w, b * (φ w * Real.exp (-(t * L w))) := by
      rw [hNL_def, integral_const_mul]
    have hint1 : Integrable
        fun w ↦ φ w * Real.exp (-(t * (K w - L w))) * Real.exp (-(t * L w)) := by
      refine hNKint.congr (Filter.Eventually.of_forall fun x ↦ ?_)
      beta_reduce
      rw [hw x, mul_assoc]
    have hsplit : (∫ w, φ w * (Real.exp (-(t * (K w - L w))) - b) * Real.exp (-(t * L w))) =
        NK - b * NL := by
      rw [hNK', hbNL, ← integral_sub hint1 (hNLint.const_mul b)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      beta_reduce
      ring
    rw [hsplit, hb_def]
    field_simp
  -- the integrand is controlled by `(e^a − e^{-a}) |φ| e^{-tL}`
  have hpt : ∀ x, ‖φ x * (Real.exp (-(t * (K x - L x))) - b) * Real.exp (-(t * L x))‖ ≤
      (Real.exp a - Real.exp (-a)) * (|φ x| * Real.exp (-(t * L x))) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    by_cases hx : x ∈ tsupport φ
    · obtain ⟨h1, h2⟩ := hwb x (hcloseφ x hx)
      have hab : |Real.exp (-(t * (K x - L x))) - b| ≤ Real.exp a - Real.exp (-a) := by
        rw [abs_le]
        constructor <;> linarith
      have he := (Real.exp_pos (-(t * L x))).le
      have hφx := abs_nonneg (φ x)
      calc |φ x| * |Real.exp (-(t * (K x - L x))) - b| * Real.exp (-(t * L x))
          ≤ |φ x| * (Real.exp a - Real.exp (-a)) * Real.exp (-(t * L x)) := by
            gcongr
        _ = (Real.exp a - Real.exp (-a)) * (|φ x| * Real.exp (-(t * L x))) := by ring
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hnum : |∫ w, φ w * (Real.exp (-(t * (K w - L w))) - b) * Real.exp (-(t * L w))| ≤
      (Real.exp a - Real.exp (-a)) * IA := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ w, φ w * (Real.exp (-(t * (K w - L w))) - b) * Real.exp (-(t * L w))‖
        ≤ ∫ w, (Real.exp a - Real.exp (-a)) * (|φ w| * Real.exp (-(t * L w))) :=
          norm_integral_le_of_norm_le (hIAint.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = (Real.exp a - Real.exp (-a)) * IA := by
          rw [integral_const_mul]
  have hIA0 : 0 ≤ IA := integral_nonneg fun w ↦ mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have ha0 : 0 ≤ a := mul_nonneg ht hδ
  have hea : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
  rw [hdiff, abs_div, abs_of_pos hZKpos]
  calc |∫ w, φ w * (Real.exp (-(t * (K w - L w))) - b) * Real.exp (-(t * L w))| / ZK
      ≤ (Real.exp a - Real.exp (-a)) * IA / ZK := div_le_div_of_nonneg_right hnum hZKpos.le
    _ ≤ (Real.exp a - Real.exp (-a)) * IA / (Real.exp (-a) * ZL) :=
        div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hea) hIA0) (by positivity)
          hZK_lower
    _ = (Real.exp (2 * a) - 1) * (IA / ZL) := by
        have h2a : Real.exp (2 * a) = Real.exp a * Real.exp a := by
          rw [← Real.exp_add]
          ring_nf
        rw [h2a, Real.exp_neg]
        field_simp

/-- The linear form of the relative bound: for `tδ ≤ 1`,
`|⟨φ⟩_K − ⟨φ⟩_L| ≤ 2e² tδ ⟨|φ|⟩_L`. -/
theorem abs_normalized_sub_le_relative_linear {K L φ χ : (ι → ℝ) → ℝ}
    (hKc : Continuous K) (hLc : Continuous L)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {δ : ℝ} (hδ : 0 ≤ δ) (hcloseφ : ∀ w ∈ tsupport φ, |K w - L w| ≤ δ)
    (hcloseχ : ∀ w ∈ tsupport χ, |K w - L w| ≤ δ) {t : ℝ} (ht : 0 ≤ t) (htδ : t * δ ≤ 1)
    (hZL : 0 < ∫ w, χ w * Real.exp (-(t * L w))) :
    |(∫ w, φ w * Real.exp (-(t * K w))) / (∫ w, χ w * Real.exp (-(t * K w))) -
      (∫ w, φ w * Real.exp (-(t * L w))) / (∫ w, χ w * Real.exp (-(t * L w)))| ≤
      2 * Real.exp 2 * (t * δ) *
        ((∫ w, |φ w| * Real.exp (-(t * L w))) / ∫ w, χ w * Real.exp (-(t * L w))) := by
  exact (abs_normalized_sub_le_relative hKc hLc hφc hφs hχc hχs hχ0 hδ hcloseφ hcloseχ ht
    hZL).trans (mul_le_mul_of_nonneg_right (exp_two_mul_sub_one_le (mul_nonneg ht hδ) htδ)
    (div_nonneg (integral_nonneg fun w ↦ mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hZL.le))

/-! ### Finite-order detection -/

/-- The normalized expectation of `|φ|` against `L` with window `χ`. -/
noncomputable def absMoment (L φ χ : (ι → ℝ) → ℝ) (t : ℝ) : ℝ :=
  (∫ w, |φ w| * Real.exp (-(t * L w))) / ∫ w, χ w * Real.exp (-(t * L w))

theorem absMoment_nonneg {L φ χ : (ι → ℝ) → ℝ} {t : ℝ}
    (hZ : 0 < ∫ w, χ w * Real.exp (-(t * L w))) : 0 ≤ absMoment L φ χ t :=
  div_nonneg (integral_nonneg fun _ ↦ mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hZ.le

/-- The normalized expectation of `φ` against `L` with window `χ`. -/
noncomputable def nmoment (L φ χ : (ι → ℝ) → ℝ) (t : ℝ) : ℝ :=
  (∫ w, φ w * Real.exp (-(t * L w))) / ∫ w, χ w * Real.exp (-(t * L w))

/-- **Empirical versus population differences.** For two population losses `L₁, L₂` with
empirical versions `K₁, K₂` within `δ`, the difference of empirical normalized expectations is
within `(e^{2tδ} − 1)(⟨|φ|⟩_{L₁} + ⟨|φ|⟩_{L₂})` of the population difference. -/
theorem abs_empirical_diff_sub_population_diff_le {K₁ K₂ L₁ L₂ φ χ : (ι → ℝ) → ℝ}
    (hK1c : Continuous K₁) (hK2c : Continuous K₂) (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose1φ : ∀ w ∈ tsupport φ, |K₁ w - L₁ w| ≤ δ)
    (hclose1χ : ∀ w ∈ tsupport χ, |K₁ w - L₁ w| ≤ δ)
    (hclose2φ : ∀ w ∈ tsupport φ, |K₂ w - L₂ w| ≤ δ)
    (hclose2χ : ∀ w ∈ tsupport χ, |K₂ w - L₂ w| ≤ δ)
    {t : ℝ} (ht : 0 ≤ t)
    (hZ1 : 0 < ∫ w, χ w * Real.exp (-(t * L₁ w))) (hZ2 : 0 < ∫ w, χ w * Real.exp (-(t * L₂ w))) :
    |(nmoment K₂ φ χ t - nmoment K₁ φ χ t) - (nmoment L₂ φ χ t - nmoment L₁ φ χ t)| ≤
      (Real.exp (2 * (t * δ)) - 1) * (absMoment L₁ φ χ t + absMoment L₂ φ χ t) := by
  have h1 := abs_normalized_sub_le_relative hK1c hL1c hφc hφs hχc hχs hχ0 hδ hclose1φ hclose1χ
    ht hZ1
  have h2 := abs_normalized_sub_le_relative hK2c hL2c hφc hφs hχc hχs hχ0 hδ hclose2φ hclose2χ
    ht hZ2
  unfold nmoment absMoment
  calc |((∫ w, φ w * Real.exp (-(t * K₂ w))) / (∫ w, χ w * Real.exp (-(t * K₂ w))) -
          (∫ w, φ w * Real.exp (-(t * K₁ w))) / (∫ w, χ w * Real.exp (-(t * K₁ w)))) -
        ((∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w))) -
          (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))))|
      = |((∫ w, φ w * Real.exp (-(t * K₂ w))) / (∫ w, χ w * Real.exp (-(t * K₂ w))) -
          (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))) -
        ((∫ w, φ w * Real.exp (-(t * K₁ w))) / (∫ w, χ w * Real.exp (-(t * K₁ w))) -
          (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))))| := by
        ring_nf
    _ ≤ |(∫ w, φ w * Real.exp (-(t * K₂ w))) / (∫ w, χ w * Real.exp (-(t * K₂ w))) -
          (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))| +
        |(∫ w, φ w * Real.exp (-(t * K₁ w))) / (∫ w, χ w * Real.exp (-(t * K₁ w))) -
          (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w)))| :=
        abs_sub _ _
    _ ≤ _ := by
        have := add_le_add h2 h1
        linarith [this]

/-- **Detection certificate.** If the population difference for `φ` is at least `a t^{-r}`
while the same-germ alternative is at most `B`, and the empirical perturbation is at most `E`,
then `|D_K| ≥ a t^{-r} − E` in the first case and `|D_K| ≤ B + E` in the second; when
`a t^{-r} > B + 2E` the threshold `B + E` separates the two. Pure arithmetic on the bounds. -/
theorem threshold_separation {DK DL a B E : ℝ} (hE : |DK - DL| ≤ E) :
    (a ≤ |DL| → a - E ≤ |DK|) ∧ (|DL| ≤ B → |DK| ≤ B + E) ∧
    (B + 2 * E < a → ((a ≤ |DL| → B + E < |DK|) ∧ (|DL| ≤ B → |DK| ≤ B + E))) := by
  have h1 : |DL| - E ≤ |DK| := by
    have := abs_sub_abs_le_abs_sub DL DK
    rw [abs_sub_comm] at this
    linarith
  have h2 : |DK| ≤ |DL| + E := by
    have := abs_sub_abs_le_abs_sub DK DL
    linarith
  refine ⟨fun ha ↦ by linarith, fun hB ↦ by linarith, fun hsep ↦ ⟨fun ha ↦ by linarith,
    fun hB ↦ by linarith⟩⟩

/-! ### Schedules: the empirical leading coefficient is the population one -/

/-- **The empirical leading coefficient along a schedule.** If the population rescaled
difference `t_n^r (⟨φ⟩_{L₂} − ⟨φ⟩_{L₁})` tends to `a`, the absolute moments are bounded by
`M t_n^{-s}`, and `δ_n t_n^{r+1−s} → 0`, then the empirical rescaled difference tends to the same
`a`. -/
theorem tendsto_rpow_mul_empirical_diff_of_schedule {K₁ K₂ : ℕ → (ι → ℝ) → ℝ}
    {L₁ L₂ φ χ : (ι → ℝ) → ℝ}
    (hK1c : ∀ n, Continuous (K₁ n)) (hK2c : ∀ n, Continuous (K₂ n))
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {δ t : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) (ht : ∀ᶠ n in atTop, 1 ≤ t n)
    (hclose1φ : ∀ n, ∀ w ∈ tsupport φ, |K₁ n w - L₁ w| ≤ δ n)
    (hclose1χ : ∀ n, ∀ w ∈ tsupport χ, |K₁ n w - L₁ w| ≤ δ n)
    (hclose2φ : ∀ n, ∀ w ∈ tsupport φ, |K₂ n w - L₂ w| ≤ δ n)
    (hclose2χ : ∀ n, ∀ w ∈ tsupport χ, |K₂ n w - L₂ w| ≤ δ n)
    (hZ1 : ∀ n, 0 < ∫ w, χ w * Real.exp (-(t n * L₁ w)))
    (hZ2 : ∀ n, 0 < ∫ w, χ w * Real.exp (-(t n * L₂ w)))
    {r s M a : ℝ} (hrs : s ≤ r)
    (hA1 : ∀ᶠ n in atTop, absMoment L₁ φ χ (t n) ≤ M * t n ^ (-s))
    (hA2 : ∀ᶠ n in atTop, absMoment L₂ φ χ (t n) ≤ M * t n ^ (-s))
    (hpop : Tendsto (fun n ↦ t n ^ r * (nmoment L₂ φ χ (t n) - nmoment L₁ φ χ (t n))) atTop (𝓝 a))
    (hsched : Tendsto (fun n ↦ δ n * t n ^ (r + 1 - s)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ t n ^ r * (nmoment (K₂ n) φ χ (t n) - nmoment (K₁ n) φ χ (t n))) atTop
      (𝓝 a) := by
  -- the perturbation `t^r (D_K − D_L)` tends to zero
  have hM0 : 0 ≤ M := by
    obtain ⟨n, hn, htn⟩ := (hA1.and ht).exists
    have : 0 ≤ absMoment L₁ φ χ (t n) := absMoment_nonneg (hZ1 n)
    have hpow : 0 < t n ^ (-s) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  have htδ : ∀ᶠ n in atTop, t n * δ n ≤ 1 := by
    have h := hsched.eventually (eventually_lt_nhds (one_pos : (0 : ℝ) < 1))
    filter_upwards [h, ht] with n hn htn
    have ht0 : 0 < t n := by linarith
    calc t n * δ n = δ n * t n ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
      _ ≤ δ n * t n ^ (r + 1 - s) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le htn (by linarith)) (hδ n)
      _ ≤ 1 := hn.le
  have hpert : Tendsto (fun n ↦ t n ^ r * (nmoment (K₂ n) φ χ (t n) - nmoment (K₁ n) φ χ (t n)) -
      t n ^ r * (nmoment L₂ φ χ (t n) - nmoment L₁ φ χ (t n))) atTop (𝓝 0) := by
    have hbound : ∀ᶠ n in atTop, ‖t n ^ r * (nmoment (K₂ n) φ χ (t n) - nmoment (K₁ n) φ χ (t n)) -
        t n ^ r * (nmoment L₂ φ χ (t n) - nmoment L₁ φ χ (t n))‖ ≤
        (4 * Real.exp 2 * M) * (δ n * t n ^ (r + 1 - s)) := by
      filter_upwards [ht, hA1, hA2, htδ] with n htn hA1n hA2n htδn
      have ht0 : 0 < t n := by linarith
      have h := abs_empirical_diff_sub_population_diff_le (hK1c n) (hK2c n) hL1c hL2c hφc hφs hχc
        hχs hχ0 (hδ n) (hclose1φ n) (hclose1χ n) (hclose2φ n) (hclose2χ n) ht0.le (hZ1 n) (hZ2 n)
      have hlin := exp_two_mul_sub_one_le (mul_nonneg ht0.le (hδ n)) htδn
      have hA : absMoment L₁ φ χ (t n) + absMoment L₂ φ χ (t n) ≤ 2 * M * t n ^ (-s) := by
        linarith
      have hpow : 0 < t n ^ (-s) := Real.rpow_pos_of_pos ht0 _
      have hr : 0 < t n ^ r := Real.rpow_pos_of_pos ht0 _
      have hδn := hδ n
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos hr]
      calc t n ^ r * |(nmoment (K₂ n) φ χ (t n) - nmoment (K₁ n) φ χ (t n)) -
              (nmoment L₂ φ χ (t n) - nmoment L₁ φ χ (t n))|
          ≤ t n ^ r * ((2 * Real.exp 2 * (t n * δ n)) * (2 * M * t n ^ (-s))) := by
            refine mul_le_mul_of_nonneg_left (h.trans ?_) hr.le
            refine mul_le_mul hlin hA ?_ (by positivity)
            exact add_nonneg (absMoment_nonneg (hZ1 n)) (absMoment_nonneg (hZ2 n))
        _ = (4 * Real.exp 2 * M) * (δ n * (t n ^ r * t n ^ (1 : ℝ) * t n ^ (-s))) := by
            rw [Real.rpow_one]
            ring
        _ = (4 * Real.exp 2 * M) * (δ n * t n ^ (r + 1 - s)) := by
            rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
            ring_nf
    refine squeeze_zero_norm' hbound ?_
    simpa using hsched.const_mul (4 * Real.exp 2 * M)
  have := hpop.add hpert
  simpa using this

/-- **As a function of the sample size.** With `δ_n ≤ C n^{-1/2}` and the schedule
`t_n = n^β`, the condition of the previous theorem holds as soon as `β (r + 1 − s) < 1/2`.
For a rescaled monomial whose first jet difference is at degree `k` (`r = (k−2)/2`, `s = 0`)
this is `β k < 1`. -/
theorem tendsto_delta_mul_rpow_of_sample_size {δ : ℕ → ℝ} {C β e : ℝ} (hδ : ∀ n, 0 ≤ δ n)
    (hδn : ∀ n : ℕ, 1 ≤ n → δ n ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)))
    (hβe : β * e < 1 / 2) :
    Tendsto (fun n : ℕ ↦ δ n * ((n : ℝ) ^ β) ^ e) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ C * (n : ℝ) ^ (-(1 / 2 : ℝ) + β * e)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 / 2 - β * e by linarith)).comp
      tendsto_natCast_atTop_atTop
    have h' := h.const_mul C
    rw [mul_zero] at h'
    refine h'.congr fun n ↦ ?_
    simp only [Function.comp]
    congr 1
    ring_nf
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hδ n) (by positivity)),
    ← Real.rpow_mul hn0.le, Real.rpow_add hn0, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hδn n hn) (by positivity)

/-! ### The probabilistic layer: transfer along a good event -/

/-- Any conclusion implied by a good event of probability at least `1 − ε` holds with
probability at least `1 − ε`: `P Gᶜ ≤ P Eᶜ ≤ ε`. -/
theorem measure_compl_le_of_subset {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {E G : Set Ω} (hEG : E ⊆ G) {ε : ENNReal} (hE : P Eᶜ ≤ ε) : P Gᶜ ≤ ε :=
  le_trans (measure_mono (Set.compl_subset_compl.mpr hEG)) hE

/-- **The empirical correspondence with high probability.** If, for each `n`, the empirical
losses are within `δ_n` of the population losses on the supports outside an event of
probability at most `ε_n`, then outside an event of probability at most `ε_n` the empirical
rescaled difference is within `4e²M δ_n t_n^{r+1−s}` of the population one. -/
theorem prob_abs_rpow_mul_empirical_diff_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {K₁ K₂ : Ω → (ι → ℝ) → ℝ} {L₁ L₂ φ χ : (ι → ℝ) → ℝ}
    (hK1c : ∀ ω, Continuous (K₁ ω)) (hK2c : ∀ ω, Continuous (K₂ ω))
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 1 ≤ t) (htδ : t * δ ≤ 1)
    (hZ1 : 0 < ∫ w, χ w * Real.exp (-(t * L₁ w))) (hZ2 : 0 < ∫ w, χ w * Real.exp (-(t * L₂ w)))
    {r s M : ℝ}
    (hA1 : absMoment L₁ φ χ t ≤ M * t ^ (-s)) (hA2 : absMoment L₂ φ χ t ≤ M * t ^ (-s))
    {ε : ENNReal}
    (hgood : P {ω | ¬ ((∀ w ∈ tsupport φ, |K₁ ω w - L₁ w| ≤ δ) ∧
      (∀ w ∈ tsupport χ, |K₁ ω w - L₁ w| ≤ δ) ∧ (∀ w ∈ tsupport φ, |K₂ ω w - L₂ w| ≤ δ) ∧
      (∀ w ∈ tsupport χ, |K₂ ω w - L₂ w| ≤ δ))} ≤ ε) :
    P {ω | ¬ |t ^ r * (nmoment (K₂ ω) φ χ t - nmoment (K₁ ω) φ χ t) -
        t ^ r * (nmoment L₂ φ χ t - nmoment L₁ φ χ t)| ≤
        (4 * Real.exp 2 * M) * (δ * t ^ (r + 1 - s))} ≤ ε := by
  have hsub : {ω | (∀ w ∈ tsupport φ, |K₁ ω w - L₁ w| ≤ δ) ∧
      (∀ w ∈ tsupport χ, |K₁ ω w - L₁ w| ≤ δ) ∧ (∀ w ∈ tsupport φ, |K₂ ω w - L₂ w| ≤ δ) ∧
      (∀ w ∈ tsupport χ, |K₂ ω w - L₂ w| ≤ δ)} ⊆
      {ω | |t ^ r * (nmoment (K₂ ω) φ χ t - nmoment (K₁ ω) φ χ t) -
        t ^ r * (nmoment L₂ φ χ t - nmoment L₁ φ χ t)| ≤
        (4 * Real.exp 2 * M) * (δ * t ^ (r + 1 - s))} := by
    intro ω hω
    obtain ⟨h1φ, h1χ, h2φ, h2χ⟩ := hω
    have ht0 : 0 < t := by linarith
    have h := abs_empirical_diff_sub_population_diff_le (hK1c ω) (hK2c ω) hL1c hL2c hφc hφs hχc
      hχs hχ0 hδ h1φ h1χ h2φ h2χ ht0.le hZ1 hZ2
    have hlin := exp_two_mul_sub_one_le (mul_nonneg ht0.le hδ) htδ
    have hA : absMoment L₁ φ χ t + absMoment L₂ φ χ t ≤ 2 * M * t ^ (-s) := by linarith
    have hpow : 0 < t ^ (-s) := Real.rpow_pos_of_pos ht0 _
    have hr : 0 < t ^ r := Real.rpow_pos_of_pos ht0 _
    change |t ^ r * (nmoment (K₂ ω) φ χ t - nmoment (K₁ ω) φ χ t) -
        t ^ r * (nmoment L₂ φ χ t - nmoment L₁ φ χ t)| ≤
        (4 * Real.exp 2 * M) * (δ * t ^ (r + 1 - s))
    rw [← mul_sub, abs_mul, abs_of_pos hr]
    calc t ^ r * |(nmoment (K₂ ω) φ χ t - nmoment (K₁ ω) φ χ t) -
            (nmoment L₂ φ χ t - nmoment L₁ φ χ t)|
        ≤ t ^ r * ((2 * Real.exp 2 * (t * δ)) * (2 * M * t ^ (-s))) := by
          refine mul_le_mul_of_nonneg_left (h.trans ?_) hr.le
          refine mul_le_mul hlin hA ?_ (by positivity)
          exact add_nonneg (absMoment_nonneg hZ1) (absMoment_nonneg hZ2)
      _ = (4 * Real.exp 2 * M) * (δ * (t ^ r * t ^ (1 : ℝ) * t ^ (-s))) := by
          rw [Real.rpow_one]
          ring
      _ = (4 * Real.exp 2 * M) * (δ * t ^ (r + 1 - s)) := by
          rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
          ring_nf
  exact measure_compl_le_of_subset P hsub hgood

end Laplace.Multi
