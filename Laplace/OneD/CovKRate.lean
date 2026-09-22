/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.CovKAnharmonic
import Laplace.OneD.MomentsSharp

/-!
# eq:covK with a rate, in one dimension

E2 of the note measures a relative error `∝ 1/t` for eq:covK. The seabed's `covK_anharmonic` is a
limit; with the sharp moment rates of `MomentsSharp` it becomes a rate. Writing
`Z₁ = t⟨x⟩, Z₂ = t⟨x²⟩, Z₃ = t²⟨x³⟩, Z₄ = t²⟨x⁴⟩, Z₅ = t³⟨x⁵⟩, Z₆ = t³⟨x⁶⟩` (each `a_j + O(1/t)`,
`Z_rates`), the six pair covariances are
`t²Cov[x²,x²] = Z₄ − Z₂², t²Cov[x³,x²] = (Z₅ − Z₃Z₂)/t, t²Cov[x⁴,x²] = (Z₆ − Z₄Z₂)/t,
 t²Cov[x²,x] = Z₃ − Z₂Z₁, t²Cov[x³,x] = Z₄ − Z₃Z₁/t, t²Cov[x⁴,x] = (Z₅ − Z₄Z₁)/t`
(`cov_*_rate`), so that

* `covK_sq_rate`: `|t² Cov[ℓ, x²] − 1/λ| ≤ K/t`, `covK_lin_rate`: `|t² Cov[ℓ, x] + α/(2λ²)| ≤ K/t`;
* `covK_anharmonic_rate`: `|t² Cov[ℓ, (B/2)x² + bx] − (B/(2λ) − bα/(2λ²))| ≤ K/t`;
* `covK_anharmonic_agree_rate`: `|Cov[ℓ, ψ] − covKOneDim(t)| ≤ K/t³`, and the relative form
  `covK_anharmonic_ratio_rate` when the constant is nonzero.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

/-! ## Pointwise algebra of rated quantities -/

theorem rate_mul {X Y a b K K' t : ℝ} (ht : 1 ≤ t) (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hX : |X - a| ≤ K / t) (hY : |Y - b| ≤ K' / t) :
    |X * Y - a * b| ≤ (K * |b| + K' * |a| + K * K') / t := by
  have ht0 : 0 < t := by linarith
  have e : X * Y - a * b = (X - a) * b + a * (Y - b) + (X - a) * (Y - b) := by ring
  rw [e]
  calc |(X - a) * b + a * (Y - b) + (X - a) * (Y - b)|
      ≤ |(X - a) * b| + |a * (Y - b)| + |(X - a) * (Y - b)| := abs_add_three _ _ _
    _ = |X - a| * |b| + |a| * |Y - b| + |X - a| * |Y - b| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ K / t * |b| + |a| * (K' / t) + K / t * (K' / t) := by gcongr
    _ ≤ K / t * |b| + |a| * (K' / t) + K / t * K' := by
        gcongr
        exact div_le_self hK' ht
    _ = (K * |b| + K' * |a| + K * K') / t := by ring

theorem rate_bounded {X a K t : ℝ} (ht : 1 ≤ t) (hK : 0 ≤ K) (hX : |X - a| ≤ K / t) :
    |X| ≤ |a| + K := by
  have : K / t ≤ K := div_le_self hK ht
  calc |X| = |a + (X - a)| := by ring_nf
    _ ≤ |a| + |X - a| := abs_add_le _ _
    _ ≤ |a| + K := by linarith

theorem bounded_div {X D t : ℝ} (ht : 0 < t) (hX : |X| ≤ D) : |X / t| ≤ D / t := by
  rw [abs_div, abs_of_pos ht]
  exact div_le_div_of_nonneg_right hX ht.le

/-! ## The six normalised moments -/

variable {lam alpha gamma : ℝ}

/-- The normalised moments `Z₁ … Z₆` with a common threshold and `1/t` rates. -/
theorem Z_rates (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ K₁ K₂ K₃ K₄ K₅ K₆ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ 0 ≤ K₃ ∧ 0 ≤ K₄ ∧ 0 ≤ K₅ ∧
      0 ≤ K₆ ∧ ∀ {t : ℝ}, T ≤ t →
      |t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) -
          (-alpha / (2 * lam ^ 2))| ≤ K₁ / t ∧
      |t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2) -
          1 / lam| ≤ K₂ / t ∧
      |t ^ 2 * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3) +
          5 * alpha / (2 * lam ^ 3)| ≤ K₃ / t ∧
      |t ^ 2 * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4) -
          3 / lam ^ 2| ≤ K₄ / t ∧
      |t ^ 3 * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5) +
          alpha * 105 / (6 * lam ^ 4)| ≤ K₅ / t ∧
      |t ^ 3 * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 6) -
          15 / lam ^ 3| ≤ K₆ / t := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := mean_anharmonic_O2_rate hlam hgamma hdisc
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := evenMoment_anharmonic_rate hlam hgamma hdisc 1
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := thirdMoment_anharmonic_rate_sharp hlam hgamma hdisc
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := evenMoment_anharmonic_rate hlam hgamma hdisc 2
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := oddMoment_anharmonic_rate hlam hgamma hdisc 2
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := evenMoment_anharmonic_rate hlam hgamma hdisc 3
  refine ⟨T₁ + T₂ + T₃ + T₄ + T₅ + T₆, by linarith, K₁, K₂, K₃, K₄, K₅, K₆, hK₁, hK₂, hK₃, hK₄,
    hK₅, hK₆, fun {t} ht => ?_⟩
  have e1 := h₁ (show T₁ ≤ t by linarith)
  have e2 := h₂ (show T₂ ≤ t by linarith)
  have e3 := h₃ (show T₃ ≤ t by linarith)
  have e4 := h₄ (show T₄ ≤ t by linarith)
  have e5 := h₅ (show T₅ ≤ t by linarith)
  have e6 := h₆ (show T₆ ≤ t by linarith)
  refine ⟨e1, ?_, e3, ?_, ?_, ?_⟩
  · simpa [Nat.doubleFactorial] using e2
  · simpa [Nat.doubleFactorial] using e4
  · simpa [Nat.doubleFactorial] using e5
  · simpa [Nat.doubleFactorial] using e6

/-! ## The six pair covariances with rates -/

/-- A common package: for `t ≥ T` all six pair covariances are rated. -/
theorem pair_cov_rates (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ K₂₂ K₃₂ K₄₂ K₂₁ K₃₁ K₄₁ : ℝ, 0 ≤ K₂₂ ∧ 0 ≤ K₃₂ ∧ 0 ≤ K₄₂ ∧ 0 ≤ K₂₁ ∧
      0 ≤ K₃₁ ∧ 0 ≤ K₄₁ ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2)
          (fun x => x ^ 2) - 2 / lam ^ 2| ≤ K₂₂ / t ∧
      |t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3)
          (fun x => x ^ 2)| ≤ K₃₂ / t ∧
      |t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4)
          (fun x => x ^ 2)| ≤ K₄₂ / t ∧
      |t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2)
          (fun x => x) + 2 * alpha / lam ^ 3| ≤ K₂₁ / t ∧
      |t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3)
          (fun x => x) - 3 / lam ^ 2| ≤ K₃₁ / t ∧
      |t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4)
          (fun x => x)| ≤ K₄₁ / t := by
  obtain ⟨T, hT, K₁, K₂, K₃, K₄, K₅, K₆, hK₁, hK₂, hK₃, hK₄, hK₅, hK₆, h⟩ :=
    Z_rates hlam hgamma hdisc
  set a₁ : ℝ := -alpha / (2 * lam ^ 2) with ha₁
  set a₂ : ℝ := 1 / lam with ha₂
  set a₃ : ℝ := -(5 * alpha / (2 * lam ^ 3)) with ha₃
  set a₄ : ℝ := 3 / lam ^ 2 with ha₄
  set a₅ : ℝ := -(alpha * 105 / (6 * lam ^ 4)) with ha₅
  set a₆ : ℝ := 15 / lam ^ 3 with ha₆
  -- product constants
  set P₂₂ : ℝ := K₂ * |a₂| + K₂ * |a₂| + K₂ * K₂ with hP₂₂
  set P₃₂ : ℝ := K₃ * |a₂| + K₂ * |a₃| + K₃ * K₂ with hP₃₂
  set P₄₂ : ℝ := K₄ * |a₂| + K₂ * |a₄| + K₄ * K₂ with hP₄₂
  set P₂₁ : ℝ := K₂ * |a₁| + K₁ * |a₂| + K₂ * K₁ with hP₂₁
  set P₃₁ : ℝ := K₃ * |a₁| + K₁ * |a₃| + K₃ * K₁ with hP₃₁
  set P₄₁ : ℝ := K₄ * |a₁| + K₁ * |a₄| + K₄ * K₁ with hP₄₁
  refine ⟨T, hT, K₄ + P₂₂, (|a₅| + K₅) + (|a₃ * a₂| + P₃₂), (|a₆| + K₆) + (|a₄ * a₂| + P₄₂),
    K₃ + P₂₁, K₄ + (|a₃ * a₁| + P₃₁), (|a₅| + K₅) + (|a₄ * a₁| + P₄₁),
    by positivity, by positivity, by positivity, by positivity, by positivity, by positivity,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have htne : t ≠ 0 := ht0.ne'
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h ht
  set L := anharmonicPotential lam alpha gamma with hL
  set M1 := Laplace.gibbsExpectation L t (fun x => x) with hM1
  set M2 := Laplace.gibbsExpectation L t (fun x => x ^ 2) with hM2
  set M3 := Laplace.gibbsExpectation L t (fun x => x ^ 3) with hM3
  set M4 := Laplace.gibbsExpectation L t (fun x => x ^ 4) with hM4
  set M5 := Laplace.gibbsExpectation L t (fun x => x ^ 5) with hM5
  set M6 := Laplace.gibbsExpectation L t (fun x => x ^ 6) with hM6
  have e3' : |t ^ 2 * M3 - a₃| ≤ K₃ / t := by rw [ha₃, sub_neg_eq_add]; exact e3
  have e5' : |t ^ 3 * M5 - a₅| ≤ K₅ / t := by rw [ha₅, sub_neg_eq_add]; exact e5
  -- the products
  have p22 := rate_mul ht1 hK₂ hK₂ e2 e2
  have p32 := rate_mul ht1 hK₃ hK₂ e3' e2
  have p42 := rate_mul ht1 hK₄ hK₂ e4 e2
  have p21 := rate_mul ht1 hK₂ hK₁ e2 e1
  have p31 := rate_mul ht1 hK₃ hK₁ e3' e1
  have p41 := rate_mul ht1 hK₄ hK₁ e4 e1
  -- the bounded numerators
  have b5 := rate_bounded ht1 hK₅ e5'
  have b6 := rate_bounded ht1 hK₆ e6
  have b32 := rate_bounded ht1 (by positivity : (0 : ℝ) ≤ P₃₂) p32
  have b42 := rate_bounded ht1 (by positivity : (0 : ℝ) ≤ P₄₂) p42
  have b31 := rate_bounded ht1 (by positivity : (0 : ℝ) ≤ P₃₁) p31
  have b41 := rate_bounded ht1 (by positivity : (0 : ℝ) ≤ P₄₁) p41
  have hM := fun (m n : ℕ) => gibbsCov_pow_pow L t m n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (2,2): Z₄ − Z₂²
    have key : t ^ 2 * Laplace.gibbsCov L t (fun x => x ^ 2) (fun x => x ^ 2) - 2 / lam ^ 2 =
        (t ^ 2 * M4 - a₄) - (t * M2 * (t * M2) - a₂ * a₂) := by
      rw [hM 2 2]
      simp only [show (2 + 2 : ℕ) = 4 from rfl, ← hM4, ← hM2, ha₄, ha₂]
      have := hlam.ne'
      field_simp
      ring
    rw [key]
    calc |(t ^ 2 * M4 - a₄) - (t * M2 * (t * M2) - a₂ * a₂)|
        ≤ |t ^ 2 * M4 - a₄| + |t * M2 * (t * M2) - a₂ * a₂| := abs_sub _ _
      _ ≤ K₄ / t + P₂₂ / t := add_le_add e4 p22
      _ = (K₄ + P₂₂) / t := by ring
  · -- (3,2): (Z₅ − Z₃Z₂)/t
    have key : t ^ 2 * Laplace.gibbsCov L t (fun x => x ^ 3) (fun x => x ^ 2) =
        (t ^ 3 * M5 - t ^ 2 * M3 * (t * M2)) / t := by
      rw [hM 3 2, eq_div_iff htne]
      simp only [show (3 + 2 : ℕ) = 5 from rfl, ← hM5, ← hM3, ← hM2]
      ring
    rw [key]
    refine (bounded_div ht0 ?_).trans (le_of_eq rfl)
    calc |t ^ 3 * M5 - t ^ 2 * M3 * (t * M2)|
        ≤ |t ^ 3 * M5| + |t ^ 2 * M3 * (t * M2)| := abs_sub _ _
      _ ≤ (|a₅| + K₅) + (|a₃ * a₂| + P₃₂) := add_le_add b5 b32
  · -- (4,2): (Z₆ − Z₄Z₂)/t
    have key : t ^ 2 * Laplace.gibbsCov L t (fun x => x ^ 4) (fun x => x ^ 2) =
        (t ^ 3 * M6 - t ^ 2 * M4 * (t * M2)) / t := by
      rw [hM 4 2, eq_div_iff htne]
      simp only [show (4 + 2 : ℕ) = 6 from rfl, ← hM6, ← hM4, ← hM2]
      ring
    rw [key]
    refine (bounded_div ht0 ?_).trans (le_of_eq rfl)
    calc |t ^ 3 * M6 - t ^ 2 * M4 * (t * M2)|
        ≤ |t ^ 3 * M6| + |t ^ 2 * M4 * (t * M2)| := abs_sub _ _
      _ ≤ (|a₆| + K₆) + (|a₄ * a₂| + P₄₂) := add_le_add b6 b42
  · -- (2,1): Z₃ − Z₂Z₁
    have key : t ^ 2 * Laplace.gibbsCov L t (fun x => x ^ 2) (fun x => x) + 2 * alpha / lam ^ 3 =
        (t ^ 2 * M3 - a₃) - (t * M2 * (t * M1) - a₂ * a₁) := by
      have h := hM 2 1
      simp only [pow_one, show (2 + 1 : ℕ) = 3 from rfl] at h
      rw [h, ← hM3, ← hM2, ← hM1, ha₃, ha₂, ha₁]
      have := hlam.ne'
      field_simp
      ring
    rw [key]
    calc |(t ^ 2 * M3 - a₃) - (t * M2 * (t * M1) - a₂ * a₁)|
        ≤ |t ^ 2 * M3 - a₃| + |t * M2 * (t * M1) - a₂ * a₁| := abs_sub _ _
      _ ≤ K₃ / t + P₂₁ / t := add_le_add e3' p21
      _ = (K₃ + P₂₁) / t := by ring
  · -- (3,1): Z₄ − Z₃Z₁/t
    have key : t ^ 2 * Laplace.gibbsCov L t (fun x => x ^ 3) (fun x => x) - 3 / lam ^ 2 =
        (t ^ 2 * M4 - a₄) - (t ^ 2 * M3 * (t * M1)) / t := by
      have h := hM 3 1
      simp only [pow_one, show (3 + 1 : ℕ) = 4 from rfl] at h
      rw [h, ← hM4, ← hM3, ← hM1, ha₄]
      field_simp
      ring
    rw [key]
    calc |(t ^ 2 * M4 - a₄) - (t ^ 2 * M3 * (t * M1)) / t|
        ≤ |t ^ 2 * M4 - a₄| + |(t ^ 2 * M3 * (t * M1)) / t| := abs_sub _ _
      _ ≤ K₄ / t + (|a₃ * a₁| + P₃₁) / t := add_le_add e4 (bounded_div ht0 b31)
      _ = (K₄ + (|a₃ * a₁| + P₃₁)) / t := by ring
  · -- (4,1): (Z₅ − Z₄Z₁)/t
    have key : t ^ 2 * Laplace.gibbsCov L t (fun x => x ^ 4) (fun x => x) =
        (t ^ 3 * M5 - t ^ 2 * M4 * (t * M1)) / t := by
      have h := hM 4 1
      simp only [pow_one, show (4 + 1 : ℕ) = 5 from rfl] at h
      rw [h, eq_div_iff htne, ← hM5, ← hM4, ← hM1]
      ring
    rw [key]
    refine (bounded_div ht0 ?_).trans (le_of_eq rfl)
    calc |t ^ 3 * M5 - t ^ 2 * M4 * (t * M1)|
        ≤ |t ^ 3 * M5| + |t ^ 2 * M4 * (t * M1)| := abs_sub _ _
      _ ≤ (|a₅| + K₅) + (|a₄ * a₁| + P₄₁) := add_le_add b5 b41

/-! ## covK with a rate -/

/-- **`|t² Cov[ℓ, x²] − 1/λ| ≤ K/t`.** -/
theorem covK_sq_rate (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) - 1 / lam| ≤ K / t := by
  obtain ⟨T, hT, K₂₂, K₃₂, K₄₂, K₂₁, K₃₁, K₄₁, hK₂₂, hK₃₂, hK₄₂, _, _, _, h⟩ :=
    pair_cov_rates hlam hgamma hdisc
  refine ⟨lam / 2 * K₂₂ + |alpha| / 6 * K₃₂ + gamma / 24 * K₄₂, T, by positivity, hT,
    fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨e22, e32, e42, -, -, -⟩ := h ht
  have hk : ∀ k : ℕ, Integrable (fun x => x ^ k * x ^ 2 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := fun k =>
    (Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic (k + 2) hlam hgamma hdisc ht0).congr
      (Eventually.of_forall fun x => by simp only [pow_add])
  rw [gibbsCov_anharmonic_left hlam hgamma hdisc ht0 _ (hk 2) (hk 3) (hk 4)]
  set L := anharmonicPotential lam alpha gamma with hL
  set C22 := Laplace.gibbsCov L t (fun x => x ^ 2) (fun x => x ^ 2) with hC22
  set C32 := Laplace.gibbsCov L t (fun x => x ^ 3) (fun x => x ^ 2) with hC32
  set C42 := Laplace.gibbsCov L t (fun x => x ^ 4) (fun x => x ^ 2) with hC42
  have hne := hlam.ne'
  have key : t ^ 2 * (lam / 2 * C22 + alpha / 6 * C32 + gamma / 24 * C42) - 1 / lam =
      lam / 2 * (t ^ 2 * C22 - 2 / lam ^ 2) + alpha / 6 * (t ^ 2 * C32) +
        gamma / 24 * (t ^ 2 * C42) := by
    field_simp
    ring
  rw [key]
  calc |lam / 2 * (t ^ 2 * C22 - 2 / lam ^ 2) + alpha / 6 * (t ^ 2 * C32) +
        gamma / 24 * (t ^ 2 * C42)|
      ≤ |lam / 2 * (t ^ 2 * C22 - 2 / lam ^ 2)| + |alpha / 6 * (t ^ 2 * C32)| +
        |gamma / 24 * (t ^ 2 * C42)| := abs_add_three _ _ _
    _ = lam / 2 * |t ^ 2 * C22 - 2 / lam ^ 2| + |alpha| / 6 * |t ^ 2 * C32| +
        gamma / 24 * |t ^ 2 * C42| := by
        rw [abs_mul (lam / 2), abs_mul (alpha / 6), abs_mul (gamma / 24),
          abs_of_pos (by positivity : (0 : ℝ) < lam / 2),
          abs_of_pos (by positivity : (0 : ℝ) < gamma / 24), abs_div,
          abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    _ ≤ lam / 2 * (K₂₂ / t) + |alpha| / 6 * (K₃₂ / t) + gamma / 24 * (K₄₂ / t) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left e22 (by positivity))
          (mul_le_mul_of_nonneg_left e32 (by positivity)))
          (mul_le_mul_of_nonneg_left e42 (by positivity))
    _ = (lam / 2 * K₂₂ + |alpha| / 6 * K₃₂ + gamma / 24 * K₄₂) / t := by ring

/-- **`|t² Cov[ℓ, x] + α/(2λ²)| ≤ K/t`.** -/
theorem covK_lin_rate (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => x) + alpha / (2 * lam ^ 2)| ≤ K / t := by
  obtain ⟨T, hT, K₂₂, K₃₂, K₄₂, K₂₁, K₃₁, K₄₁, _, _, _, hK₂₁, hK₃₁, hK₄₁, h⟩ :=
    pair_cov_rates hlam hgamma hdisc
  refine ⟨lam / 2 * K₂₁ + |alpha| / 6 * K₃₁ + gamma / 24 * K₄₁, T, by positivity, hT,
    fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨-, -, -, e21, e31, e41⟩ := h ht
  have hk : ∀ k : ℕ, Integrable (fun x => x ^ k * x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := fun k =>
    (Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic (k + 1) hlam hgamma hdisc ht0).congr
      (Eventually.of_forall fun x => by simp only [pow_succ])
  rw [gibbsCov_anharmonic_left hlam hgamma hdisc ht0 _ (hk 2) (hk 3) (hk 4)]
  set L := anharmonicPotential lam alpha gamma with hL
  set C21 := Laplace.gibbsCov L t (fun x => x ^ 2) (fun x => x) with hC21
  set C31 := Laplace.gibbsCov L t (fun x => x ^ 3) (fun x => x) with hC31
  set C41 := Laplace.gibbsCov L t (fun x => x ^ 4) (fun x => x) with hC41
  have hne := hlam.ne'
  have key : t ^ 2 * (lam / 2 * C21 + alpha / 6 * C31 + gamma / 24 * C41) + alpha / (2 * lam ^ 2) =
      lam / 2 * (t ^ 2 * C21 + 2 * alpha / lam ^ 3) + alpha / 6 * (t ^ 2 * C31 - 3 / lam ^ 2) +
        gamma / 24 * (t ^ 2 * C41) := by
    field_simp
    ring
  rw [key]
  calc |lam / 2 * (t ^ 2 * C21 + 2 * alpha / lam ^ 3) + alpha / 6 * (t ^ 2 * C31 - 3 / lam ^ 2) +
        gamma / 24 * (t ^ 2 * C41)|
      ≤ |lam / 2 * (t ^ 2 * C21 + 2 * alpha / lam ^ 3)| + |alpha / 6 * (t ^ 2 * C31 - 3 / lam ^ 2)|
        + |gamma / 24 * (t ^ 2 * C41)| := abs_add_three _ _ _
    _ = lam / 2 * |t ^ 2 * C21 + 2 * alpha / lam ^ 3| + |alpha| / 6 * |t ^ 2 * C31 - 3 / lam ^ 2| +
        gamma / 24 * |t ^ 2 * C41| := by
        rw [abs_mul (lam / 2), abs_mul (alpha / 6), abs_mul (gamma / 24),
          abs_of_pos (by positivity : (0 : ℝ) < lam / 2),
          abs_of_pos (by positivity : (0 : ℝ) < gamma / 24), abs_div,
          abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    _ ≤ lam / 2 * (K₂₁ / t) + |alpha| / 6 * (K₃₁ / t) + gamma / 24 * (K₄₁ / t) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left e21 (by positivity))
          (mul_le_mul_of_nonneg_left e31 (by positivity)))
          (mul_le_mul_of_nonneg_left e41 (by positivity))
    _ = (lam / 2 * K₂₁ + |alpha| / 6 * K₃₁ + gamma / 24 * K₄₁) / t := by ring

/-- **eq:covK with a rate, one dimension**: for the probe `ψ = (B/2)x² + bx`,
`|t² Cov[ℓ, ψ] − (B/(2λ) − bα/(2λ²))| ≤ K/t` eventually. -/
theorem covK_anharmonic_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (B b : ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) -
        (B / (2 * lam) - b * alpha / (2 * lam ^ 2))| ≤ K / t := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := covK_sq_rate hlam hgamma hdisc
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := covK_lin_rate hlam hgamma hdisc
  refine ⟨|B| / 2 * K₂ + |b| * K₁, max T₁ T₂, by positivity, le_max_of_le_left hT₁,
    fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith [le_max_left T₁ T₂, hT₁]
  have e2 := h₂ ((le_max_right _ _).trans ht)
  have e1 := h₁ ((le_max_left _ _).trans ht)
  set L := anharmonicPotential lam alpha gamma with hL
  have hm : ∀ k : ℕ, Integrable (fun x => x ^ k * Real.exp (-(t * L x))) := fun k =>
    Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic k hlam hgamma hdisc ht0
  have hLm : ∀ k : ℕ, Integrable (fun x => L x * x ^ k * Real.exp (-(t * L x))) := fun k =>
    (((hm (k + 2)).const_mul (lam / 2)).add (((hm (k + 3)).const_mul (alpha / 6)).add
      ((hm (k + 4)).const_mul (gamma / 24)))).congr (Eventually.of_forall fun x => by
        simp only [Pi.add_apply, hL, anharmonicPotential, pow_add]
        ring)
  have i1 : Integrable (fun x => B / 2 * x ^ 2 * Real.exp (-(t * L x))) :=
    ((hm 2).const_mul (B / 2)).congr (Eventually.of_forall fun x => by ring)
  have i2 : Integrable (fun x => b * x * Real.exp (-(t * L x))) :=
    ((hm 1).const_mul b).congr (Eventually.of_forall fun x => by simp only [pow_one]; ring)
  have i1L : Integrable (fun x => L x * (B / 2 * x ^ 2) * Real.exp (-(t * L x))) :=
    ((hLm 2).const_mul (B / 2)).congr (Eventually.of_forall fun x => by ring)
  have i2L : Integrable (fun x => L x * (b * x) * Real.exp (-(t * L x))) :=
    ((hLm 1).const_mul b).congr (Eventually.of_forall fun x => by simp only [pow_one]; ring)
  rw [Laplace.gibbsCov_add_right L t L _ _ i1 i2 i1L i2L, Laplace.gibbsCov_smul_right,
    Laplace.gibbsCov_smul_right]
  set X := Laplace.gibbsCov L t L (fun x => x ^ 2) with hX
  set Y := Laplace.gibbsCov L t L (fun x => x) with hY
  have hne := hlam.ne'
  have key : t ^ 2 * (B / 2 * X + b * Y) - (B / (2 * lam) - b * alpha / (2 * lam ^ 2)) =
      B / 2 * (t ^ 2 * X - 1 / lam) + b * (t ^ 2 * Y + alpha / (2 * lam ^ 2)) := by
    field_simp
    ring
  rw [key]
  calc |B / 2 * (t ^ 2 * X - 1 / lam) + b * (t ^ 2 * Y + alpha / (2 * lam ^ 2))|
      ≤ |B / 2 * (t ^ 2 * X - 1 / lam)| + |b * (t ^ 2 * Y + alpha / (2 * lam ^ 2))| :=
        abs_add_le _ _
    _ = |B| / 2 * |t ^ 2 * X - 1 / lam| + |b| * |t ^ 2 * Y + alpha / (2 * lam ^ 2)| := by
        rw [abs_mul, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ |B| / 2 * (K₂ / t) + |b| * (K₁ / t) :=
        add_le_add (mul_le_mul_of_nonneg_left e2 (by positivity))
          (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
    _ = (|B| / 2 * K₂ + |b| * K₁) / t := by ring

/-- **eq:covK is exact to `O(t⁻³)`**: `|Cov[ℓ, ψ] − covKOneDim(t)| ≤ K/t³` eventually. -/
theorem covK_anharmonic_agree_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (B b : ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) -
        covKOneDim lam alpha t B b| ≤ K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ := covK_anharmonic_rate hlam hgamma hdisc B b
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have htne := ht0.ne'
  rw [covKOneDim_eq hlam.ne' htne]
  set V := Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
    (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) with hV
  have key : V - (B / (2 * lam) - b * alpha / (2 * lam ^ 2)) / t ^ 2 =
      (t ^ 2 * V - (B / (2 * lam) - b * alpha / (2 * lam ^ 2))) / t ^ 2 := by
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  calc |t ^ 2 * V - (B / (2 * lam) - b * alpha / (2 * lam ^ 2))| / t ^ 2
      ≤ (K / t) / t ^ 2 := div_le_div_of_nonneg_right (h ht) (by positivity)
    _ = K / t ^ 3 := by ring

/-- **The relative form**: when the constant is nonzero, `|Cov[ℓ, ψ]/covKOneDim(t) − 1| ≤ K/t`. -/
theorem covK_anharmonic_ratio_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (B b : ℝ)
    (hc : B / (2 * lam) - b * alpha / (2 * lam ^ 2) ≠ 0) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) /
        covKOneDim lam alpha t B b - 1| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := covK_anharmonic_rate hlam hgamma hdisc B b
  set C := B / (2 * lam) - b * alpha / (2 * lam ^ 2) with hC
  refine ⟨K / |C|, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have htne := ht0.ne'
  rw [covKOneDim_eq hlam.ne' htne]
  set V := Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
    (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) with hV
  have key : V / (C / t ^ 2) - 1 = (t ^ 2 * V - C) / C := by
    field_simp
  rw [key, abs_div]
  calc |t ^ 2 * V - C| / |C| ≤ (K / t) / |C| :=
        div_le_div_of_nonneg_right (h ht) (abs_nonneg _)
    _ = K / |C| / t := by ring

end Laplace.OneD
