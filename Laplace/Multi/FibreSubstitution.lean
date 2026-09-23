/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The two-branch substitution `s = c v^q`

Step (2) of the fibre-identity plan (laplace `docs/hironaka_wall_atlas_spec.md`): on the solved
coordinate `v` of a wall chart the truth reads `s = c v^q` with `c = S ∏_{j≠k} w_j^{q_j} ≠ 0` off a
null set and `q = q_k ≥ 1`. On each half-line `v > 0`, `v < 0` the map is injective with
`|ds/dv| = q |s| / |v|`, so an integral in `v` over a half-line is an integral in `s` over the image
against the solved coordinate `V(s) = (|s|/|c|)^{1/q}` and the density `V(s)/(q |s|)`
(`integral_branch_pos`, `integral_branch_neg`, from Mathlib's one-dimensional change of variables
`integral_image_eq_integral_abs_deriv_smul`; no integrability hypotheses). The image half-lines are
identified in `image_pow_Ioi`, `image_pow_Iio`.
-/

open Real MeasureTheory Set

namespace Laplace.Multi

/-- The (positive) solved coordinate `V(s) = (|s|/|c|)^{1/q}`. -/
noncomputable def solvedCoord (c : ℝ) (q : ℕ) (s : ℝ) : ℝ := (|s| / |c|) ^ (1 / (q : ℝ))

theorem solvedCoord_nonneg (c : ℝ) (q : ℕ) (s : ℝ) : 0 ≤ solvedCoord c q s :=
  Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _

/-- `V(c v^q) = |v|`. -/
theorem solvedCoord_mul_pow {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) (v : ℝ) :
    solvedCoord c q (c * v ^ q) = |v| := by
  unfold solvedCoord
  rw [abs_mul, mul_div_cancel_left₀ _ (abs_ne_zero.mpr hc), abs_pow, one_div,
    Real.pow_rpow_inv_natCast (abs_nonneg v) hq.ne']

theorem hasDerivWithinAt_mul_pow (c : ℝ) (q : ℕ) (s : Set ℝ) (v : ℝ) :
    HasDerivWithinAt (fun v ↦ c * v ^ q) (c * (q * v ^ (q - 1))) s v :=
  ((hasDerivAt_pow q v).const_mul c).hasDerivWithinAt

theorem injOn_mul_pow_Ioi {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) :
    InjOn (fun v : ℝ ↦ c * v ^ q) (Ioi 0) := by
  intro v₁ hv₁ v₂ hv₂ h
  have h' : v₁ ^ q = v₂ ^ q := mul_left_cancel₀ hc h
  exact (pow_left_inj₀ (le_of_lt hv₁) (le_of_lt hv₂) hq.ne').mp h'

theorem injOn_mul_pow_Iio {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) :
    InjOn (fun v : ℝ ↦ c * v ^ q) (Iio 0) := by
  intro v₁ hv₁ v₂ hv₂ h
  have h' : v₁ ^ q = v₂ ^ q := mul_left_cancel₀ hc h
  have h1 : (-v₁) ^ q = (-v₂) ^ q := by
    rcases Nat.even_or_odd q with he | ho
    · rw [he.neg_pow, he.neg_pow, h']
    · rw [ho.neg_pow, ho.neg_pow, h']
  have := (pow_left_inj₀ (by linarith [mem_Iio.mp hv₁]) (by linarith [mem_Iio.mp hv₂]) hq.ne').mp h1
  linarith

/-- The density identity: `|c q v^{q−1}| · V/(q |s|) = 1` at `s = c v^q`, `v ≠ 0`. -/
theorem density_branch {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) {v : ℝ} (hv : v ≠ 0) :
    |c * (q * v ^ (q - 1))| * (solvedCoord c q (c * v ^ q) / (q * |c * v ^ q|)) = 1 := by
  rw [solvedCoord_mul_pow hc hq]
  simp only [abs_mul, abs_pow, Nat.abs_cast]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hc' : |c| ≠ 0 := abs_ne_zero.mpr hc
  have hv' : |v| ≠ 0 := abs_ne_zero.mpr hv
  have hvq : |v| ^ (q - 1) * |v| = |v| ^ q := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  field_simp
  rw [← hvq]

/-- **Positive branch.** `∫_{v>0} Φ(v) dv = ∫_{s ∈ c·(0,∞)^q} Φ(V(s)) V(s)/(q|s|) ds`. -/
theorem integral_branch_pos {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) (Φ : ℝ → ℝ) :
    ∫ s in (fun v : ℝ ↦ c * v ^ q) '' Ioi 0,
      Φ (solvedCoord c q s) * (solvedCoord c q s / (q * |s|)) = ∫ v in Ioi 0, Φ v := by
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun v _ ↦ hasDerivWithinAt_mul_pow c q (Ioi 0) v) (injOn_mul_pow_Ioi hc hq)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv ↦ ?_
  have hv : 0 < v := hv
  simp only [smul_eq_mul]
  have := density_branch hc hq hv.ne'
  rw [solvedCoord_mul_pow hc hq, abs_of_pos hv] at this ⊢
  calc |c * (q * v ^ (q - 1))| * (Φ v * (v / (q * |c * v ^ q|)))
      = Φ v * (|c * (q * v ^ (q - 1))| * (v / (q * |c * v ^ q|))) := by ring
    _ = Φ v := by rw [this, mul_one]

/-- **Negative branch.** `∫_{v<0} Φ(v) dv = ∫_{s ∈ c·(−∞,0)^q} Φ(−V(s)) V(s)/(q|s|) ds`. -/
theorem integral_branch_neg {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) (Φ : ℝ → ℝ) :
    ∫ s in (fun v : ℝ ↦ c * v ^ q) '' Iio 0,
      Φ (-solvedCoord c q s) * (solvedCoord c q s / (q * |s|)) = ∫ v in Iio 0, Φ v := by
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Iio
    (fun v _ ↦ hasDerivWithinAt_mul_pow c q (Iio 0) v) (injOn_mul_pow_Iio hc hq)]
  refine setIntegral_congr_fun measurableSet_Iio fun v hv ↦ ?_
  have hv : v < 0 := hv
  simp only [smul_eq_mul]
  have := density_branch hc hq hv.ne
  rw [solvedCoord_mul_pow hc hq, abs_of_neg hv] at this ⊢
  rw [neg_neg]
  calc |c * (q * v ^ (q - 1))| * (Φ v * (-v / (q * |c * v ^ q|)))
      = Φ v * (|c * (q * v ^ (q - 1))| * (-v / (q * |c * v ^ q|))) := by ring
    _ = Φ v := by rw [this, mul_one]

/-- The image of the positive half-line: `(0,∞)` for `c > 0`, `(−∞,0)` for `c < 0`. -/
theorem image_pow_Ioi {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) :
    (fun v : ℝ ↦ c * v ^ q) '' Ioi 0 = if 0 < c then Ioi 0 else Iio 0 := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  ext s
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv : 0 < v := hv
    split_ifs with hc'
    · exact mul_pos hc' (pow_pos hv _)
    · exact mul_neg_of_neg_of_pos (lt_of_le_of_ne (not_lt.mp hc') hc) (pow_pos hv _)
  · intro hs
    have key : ∀ s : ℝ, s ≠ 0 → (fun v : ℝ ↦ c * v ^ q) (solvedCoord c q s) = c * (|s| / |c|) := by
      intro s _
      dsimp only
      unfold solvedCoord
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg (abs_nonneg _) (abs_nonneg _)),
        one_div_mul_cancel hq', Real.rpow_one]
    rcases lt_or_gt_of_ne hc with hcn | hcp
    · have hs' : s < 0 := by simpa [not_lt.mpr hcn.le] using hs
      refine ⟨solvedCoord c q s, ?_, ?_⟩
      · exact Real.rpow_pos_of_pos (div_pos (abs_pos.mpr hs'.ne) (abs_pos.mpr hc)) _
      · rw [key s hs'.ne, abs_of_neg hcn, abs_of_neg hs', neg_div_neg_eq]
        field_simp
    · have hs' : 0 < s := by simpa [hcp] using hs
      refine ⟨solvedCoord c q s, ?_, ?_⟩
      · exact Real.rpow_pos_of_pos (div_pos (abs_pos.mpr hs'.ne') (abs_pos.mpr hc)) _
      · rw [key s hs'.ne', abs_of_pos hcp, abs_of_pos hs']
        field_simp

/-- The negative half-line is the positive half-line of `(−1)^q c` (via `v ↦ −v`). -/
theorem image_pow_Iio_eq (c : ℝ) (q : ℕ) :
    (fun v : ℝ ↦ c * v ^ q) '' Iio 0 = (fun v : ℝ ↦ (c * (-1) ^ q) * v ^ q) '' Ioi 0 := by
  ext s
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨-v, neg_pos.mpr (mem_Iio.mp hv), ?_⟩
    dsimp only
    rw [mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨-v, neg_lt_zero.mpr (mem_Ioi.mp hv), ?_⟩
    dsimp only
    rw [mul_assoc, ← mul_pow, neg_one_mul]

/-- **Both branches.** For integrable `Φ`, the full line integral is the sum of the two half-line
integrals, each written in the truth variable `s`. -/
theorem integral_two_branch {c : ℝ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) {Φ : ℝ → ℝ}
    (hΦ : Integrable Φ) :
    ∫ v, Φ v = (∫ s in (fun v : ℝ ↦ c * v ^ q) '' Iio 0,
        Φ (-solvedCoord c q s) * (solvedCoord c q s / (q * |s|))) +
      ∫ s in (fun v : ℝ ↦ c * v ^ q) '' Ioi 0,
        Φ (solvedCoord c q s) * (solvedCoord c q s / (q * |s|)) := by
  rw [integral_branch_neg hc hq, integral_branch_pos hc hq,
    ← setIntegral_union (Ioi_disjoint_Iio_of_le le_rfl).symm measurableSet_Ioi hΦ.integrableOn
      hΦ.integrableOn, Iio_union_Ioi, restrict_compl_singleton]

end Laplace.Multi
