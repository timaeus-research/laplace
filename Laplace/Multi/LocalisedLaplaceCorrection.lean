/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedLaplaceTransform

/-!
# The first correction to the Laplace transform of the localised energy

On E2's exact localised measure, per frame coordinate, the Laplace transform
`Λ_t(s) = ⟨e^{−stℓ}⟩_loc(t)` has the two-term expansion
`Λ_t(s) = (1+s)^{−1/2} − s·e₁/((1+s)^{3/2} t) + O(t⁻²)` for each fixed `s > −1`, where
`e₁ = energyLocCoeff1` is the first correction of the localised energy (`t⟨ℓ⟩_loc = ½ + e₁/t + …`,
`LocalisedLLCCoeff`). The coefficient comes out of the exact factorisation
`√(1+s)·Λ_t(s) = [J₀((1+s)t)/J₀(t)]·[D((1+s)t)/D(t)]` and the second-order expansions of `J₀`
(`J0_delta_order3`, coefficient `j₁ = 15A²/2 − 3B`) and of the localiser denominator `D`
(`locDenominator_rate2`, coefficient `d₁ = locD1`), through the identity **`e₁ = j₁ + d₁`**
(`energyLocCoeff1_eq_J1_add_D1`): one coefficient governs the mean energy's first correction, the
variance's (`LocalisedEnergyVarOrder2`, `2e₁`) and the transform's.

On E2 the transform is the product over frame coordinates, and
`⟨e^{−st·L∘A}⟩_loc = (1+s)^{−d/2}·(1 − s(∑ᵢe₁ᵢ)/((1+s)t)) + O(t⁻²)`: the first finite-temperature
correction to the `Gamma(d/2, 1)` transform of `t·(L∘A)` is governed by tide 73's E2 coefficient
`∑ᵢe₁ᵢ`. Pointwise in `s`; fixed parameters; the exact localised Gibbs measure.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

/-- Second-order product rule for two factors `1 + x/t + O(t⁻²)`. -/
theorem prod_rate_order2 {X Y x y KX KY t : ℝ} (ht1 : 1 ≤ t) (hKX : 0 ≤ KX) (hKY : 0 ≤ KY)
    (hX : |X - 1 - x / t| ≤ KX / t ^ 2) (hY : |Y - 1 - y / t| ≤ KY / t ^ 2) :
    |X * Y - 1 - (x + y) / t| ≤
      (KX * (1 + |y| + KY) + (1 + |x|) * KY + |x * y|) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have e : X * Y - 1 - (x + y) / t =
      (X - 1 - x / t) * Y + (1 + x / t) * (Y - 1 - y / t) + x * y / t ^ 2 := by ring
  have h1y : |1 + y / t| ≤ 1 + |y| := by
    calc |1 + y / t| ≤ |(1 : ℝ)| + |y / t| := abs_add_le _ _
      _ = 1 + |y| / t := by rw [abs_one, abs_div, abs_of_pos ht0]
      _ ≤ 1 + |y| := by linarith [div_le_self (abs_nonneg y) ht1]
  have h1x : |1 + x / t| ≤ 1 + |x| := by
    calc |1 + x / t| ≤ |(1 : ℝ)| + |x / t| := abs_add_le _ _
      _ = 1 + |x| / t := by rw [abs_one, abs_div, abs_of_pos ht0]
      _ ≤ 1 + |x| := by linarith [div_le_self (abs_nonneg x) ht1]
  have hKYt : KY / t ^ 2 ≤ KY := div_le_self hKY (one_le_pow₀ ht1)
  have hYb : |Y| ≤ 1 + |y| + KY := by
    calc |Y| = |(Y - 1 - y / t) + (1 + y / t)| := by congr 1; ring
      _ ≤ |Y - 1 - y / t| + |1 + y / t| := abs_add_le _ _
      _ ≤ KY / t ^ 2 + (1 + |y|) := add_le_add hY h1y
      _ ≤ 1 + |y| + KY := by linarith
  rw [e]
  calc |(X - 1 - x / t) * Y + (1 + x / t) * (Y - 1 - y / t) + x * y / t ^ 2|
      ≤ |(X - 1 - x / t) * Y| + |(1 + x / t) * (Y - 1 - y / t)| + |x * y / t ^ 2| := by
        have a1 := abs_add_le ((X - 1 - x / t) * Y) ((1 + x / t) * (Y - 1 - y / t))
        have a2 := abs_add_le ((X - 1 - x / t) * Y + (1 + x / t) * (Y - 1 - y / t))
          (x * y / t ^ 2)
        linarith
    _ = |X - 1 - x / t| * |Y| + |1 + x / t| * |Y - 1 - y / t| + |x * y| / t ^ 2 := by
        rw [abs_mul, abs_mul, abs_div, abs_of_pos ht2]
    _ ≤ KX / t ^ 2 * (1 + |y| + KY) + (1 + |x|) * (KY / t ^ 2) + |x * y| / t ^ 2 := by
        gcongr
    _ = _ := by ring

/-- A quotient `F((1+s)t)/F(t)` of a function with the two-term expansion `L(1 + f₁/u) + O(u⁻²)`
is `1 − f₁s/((1+s)t) + O(t⁻²)`. -/
theorem scaled_ratio_rate2 {F : ℝ → ℝ} {L f₁ K T₀ s : ℝ} (hL : 0 < L) (hK : 0 ≤ K)
    (hT₀ : 1 ≤ T₀) (hs : -1 < s)
    (hF : ∀ {u : ℝ}, T₀ ≤ u → |F u - (L + L * f₁ / u)| ≤ K / u ^ 2) :
    ∃ K' T : ℝ, 0 ≤ K' ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |F ((1 + s) * t) / F t - 1 - (-(f₁ * s / (1 + s))) / t| ≤ K' / t ^ 2 := by
  have ha : 0 < 1 + s := by linarith
  have hTa : 0 ≤ T₀ / (1 + s) := by positivity
  have hKL : 0 ≤ 2 * (L * |f₁| + K) / L := by positivity
  refine ⟨2 / L * (K / (1 + s) ^ 2 + (|(1 : ℝ)| + |-(f₁ * s / (1 + s))|) * K +
    |-(f₁ * s / (1 + s)) * (L * f₁)|), T₀ + T₀ / (1 + s) + 2 * (L * |f₁| + K) / L,
    by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have htT : T₀ ≤ t := by linarith
  have hatT : T₀ ≤ (1 + s) * t := by
    have h1 : T₀ / (1 + s) ≤ t := by linarith
    rw [div_le_iff₀ ha] at h1
    linarith [mul_comm t (1 + s)]
  have hY := hF htT
  have hX : |F ((1 + s) * t) - (L + L * f₁ / (1 + s) / t)| ≤ K / (1 + s) ^ 2 / t ^ 2 := by
    have h := hF hatT
    rwa [div_mul_eq_div_div, mul_pow, div_mul_eq_div_div] at h
  have hYlow : L / 2 ≤ F t := by
    have h1 := (abs_le.mp hY).1
    have h2 : |L * f₁ / t| ≤ L * |f₁| / t := by
      rw [abs_div, abs_of_pos ht0, abs_mul, abs_of_pos hL]
    have h3 : K / t ^ 2 ≤ K / t := div_le_div_of_nonneg_left hK ht0 (by nlinarith)
    have h4 : (L * |f₁| + K) / t ≤ L / 2 := by
      rw [div_le_iff₀ ht0]
      have h5 : 2 * (L * |f₁| + K) / L ≤ t := by linarith
      rw [div_le_iff₀ hL] at h5
      linarith
    have h5 := neg_abs_le (L * f₁ / t)
    linarith [add_div (L * |f₁|) K t]
  have h := ratio_rate_order2 (X := F ((1 + s) * t)) (Y := F t) (a := L) (b := L * f₁ / (1 + s))
    (c := L) (d := L * f₁) (KX := K / (1 + s) ^ 2) (KY := K) ht1 hL hYlow hX hY
  have hcoef : (L * f₁ / (1 + s) * L - L * (L * f₁)) / L ^ 2 = -(f₁ * s / (1 + s)) := by
    field_simp
    ring
  rw [hcoef, div_self hL.ne'] at h
  exact h

/-- Second-order finite-product rule: `∏ᵢ(1 + xᵢ/t + O(t⁻²)) = 1 + (∑ᵢxᵢ)/t + O(t⁻²)`. -/
theorem prod_one_rate2 {ι : Type*} (s : Finset ι) (R : ι → ℝ → ℝ) (x K T : ι → ℝ)
    (hK : ∀ i, 0 ≤ K i) (hT : ∀ i, 1 ≤ T i)
    (h : ∀ i, ∀ {t : ℝ}, T i ≤ t → |R i t - 1 - x i / t| ≤ K i / t ^ 2) :
    ∃ C T' : ℝ, 0 ≤ C ∧ 1 ≤ T' ∧ ∀ {t : ℝ}, T' ≤ t →
      |∏ i ∈ s, R i t - 1 - (∑ i ∈ s, x i) / t| ≤ C / t ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, le_rfl, le_rfl, fun {t} _ => by simp⟩
  | insert j s hj ih =>
    obtain ⟨C, T', hC, hT', hih⟩ := ih
    have hxj := abs_nonneg (x j)
    have hKj := hK j
    have hTj := hT j
    refine ⟨2 * C + K j + (|x j| + K j) * |∑ i ∈ s, x i|, T' + T j + (|x j| + K j),
      by positivity, by linarith, fun {t} ht => ?_⟩
    have ht1 : 1 ≤ t := by linarith
    have ht0 : 0 < t := by linarith
    have hP := hih (t := t) (by linarith)
    have hRj := h j (t := t) (by linarith)
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    set P := ∏ i ∈ s, R i t with hPdef
    set X := ∑ i ∈ s, x i with hXdef
    have e : R j t * P - 1 - (x j + X) / t =
        R j t * (P - 1 - X / t) + (R j t - 1 - x j / t) + (R j t - 1) * (X / t) := by ring
    have hR1 : |R j t - 1| ≤ (|x j| + K j) / t := by
      calc |R j t - 1| = |(R j t - 1 - x j / t) + x j / t| := by congr 1; ring
        _ ≤ |R j t - 1 - x j / t| + |x j / t| := abs_add_le _ _
        _ ≤ K j / t ^ 2 + |x j| / t := by
            rw [abs_div, abs_of_pos ht0]
            gcongr
        _ ≤ K j / t + |x j| / t :=
            add_le_add (div_le_div_of_nonneg_left (hK j) ht0 (by nlinarith)) le_rfl
        _ = (|x j| + K j) / t := by ring
    have hRb : |R j t| ≤ 2 := by
      have h1 := abs_sub_abs_le_abs_sub (R j t) 1
      rw [abs_one] at h1
      have h2 : (|x j| + K j) / t ≤ 1 := by
        rw [div_le_one ht0]
        linarith
      linarith
    rw [e]
    calc |R j t * (P - 1 - X / t) + (R j t - 1 - x j / t) + (R j t - 1) * (X / t)|
        ≤ |R j t * (P - 1 - X / t)| + |R j t - 1 - x j / t| + |(R j t - 1) * (X / t)| := by
          have a1 := abs_add_le (R j t * (P - 1 - X / t)) (R j t - 1 - x j / t)
          have a2 := abs_add_le (R j t * (P - 1 - X / t) + (R j t - 1 - x j / t))
            ((R j t - 1) * (X / t))
          linarith
      _ = |R j t| * |P - 1 - X / t| + |R j t - 1 - x j / t| + |R j t - 1| * (|X| / t) := by
          rw [abs_mul, abs_mul, abs_div, abs_of_pos ht0]
      _ ≤ 2 * (C / t ^ 2) + K j / t ^ 2 + (|x j| + K j) / t * (|X| / t) := by gcongr
      _ = (2 * C + K j + (|x j| + K j) * |X|) / t ^ 2 := by ring

section OneD

variable {lam alpha gamma g x₀ : ℝ} (hlam : 0 < lam) (hgamma : 0 < gamma)
  (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

omit hgamma hdisc in
/-- `(α/(6λ√λ))² = α²/(36λ³)`. -/
theorem cubicScale_sq : cubicScale lam alpha ^ 2 = alpha ^ 2 / (36 * lam ^ 3) := by
  unfold cubicScale
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hlam.le]
  ring

omit hgamma hdisc in
/-- **`e₁ = j₁ + d₁`**: the energy's first correction is the sum of the partition-function
coefficient `j₁ = 15A²/2 − 3B = 5α²/(24λ³) − γ/(8λ²)` and the localiser-denominator coefficient
`d₁ = locD1`. -/
theorem energyLocCoeff1_eq_J1_add_D1 :
    energyLocCoeff1 lam alpha gamma g x₀ = (15 * cubicScale lam alpha ^ 2 / 2 - 3 * quarticScale lam
      gamma) + locD1 lam alpha g x₀ := by
  have hl : lam ≠ 0 := hlam.ne'
  rw [cubicScale_sq hlam]
  unfold energyLocCoeff1 locSecondCoeff2 locN2 locThirdCoeff quarticScale locD1 locP₃
  field_simp
  ring

/-- **The two-term expansion of the normalised Laplace transform**:
`√(1+s)·Λ_t(s) = 1 − e₁s/((1+s)t) + O(t⁻²)`. -/
theorem locLaplace_scaled_rate2 (hg : 0 ≤ g) {s : ℝ} (hs : -1 < s) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |Real.sqrt (1 + s) * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => Real.exp (-(s * t * anharmonicPotential lam alpha gamma x))) - 1 -
        (-(energyLocCoeff1 lam alpha gamma g x₀ * s / (1 + s))) / t| ≤ K / t ^ 2 := by
  obtain ⟨KJ, hKJ, hJ⟩ := J0_delta_order3 hlam hgamma hdisc
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  have h2π : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := scaled_ratio_rate2 (F := J_n lam alpha gamma 0)
    (f₁ := (15 * cubicScale lam alpha ^ 2 / 2 - 3 * quarticScale lam gamma)) h2π hKJ le_rfl hs (fun
      {u} hu => hJ hu)
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := scaled_ratio_rate2
    (F := fun u => _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) u
      (locWeight g x₀)) (f₁ := locD1 lam alpha g x₀) one_pos hKD hTD hs (fun {u} hu => by
      have e : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) u
          (locWeight g x₀) - (1 + 1 * locD1 lam alpha g x₀ / u) =
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) u (locWeight g x₀) -
            1 - locD1 lam alpha g x₀ / u := by ring
      rw [e]
      exact hD hu)
  refine ⟨K₁ * (1 + |-(locD1 lam alpha g x₀ * s / (1 + s))| + K₂) +
    (1 + |-((15 * cubicScale lam alpha ^ 2 / 2 - 3 * quarticScale lam gamma) * s / (1 + s))|) * K₂ +
      |-((15 * cubicScale lam alpha ^ 2 / 2 - 3 * quarticScale lam gamma) * s / (1 + s)) * -(locD1
      lam alpha g x₀ * s / (1 + s))|, T₁ + T₂, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [locLaplace_scaled_eq hlam hgamma hdisc hg hs ht0, energyLocCoeff1_eq_J1_add_D1 hlam]
  have e1 := h₁ (t := t) (by linarith)
  have e2 := h₂ (t := t) (by linarith)
  have h := prod_rate_order2 ht1 hK₁ hK₂ e1 e2
  have e : -(((15 * cubicScale lam alpha ^ 2 / 2 - 3 * quarticScale lam gamma) + locD1 lam alpha g
      x₀) * s / (1 + s)) = -((15 * cubicScale lam alpha ^ 2 / 2 - 3 * quarticScale lam gamma) * s /
      (1 + s)) + -(locD1 lam alpha g x₀ * s / (1 + s)) := by ring
  rw [e]
  exact h

/-- **The two-term expansion of the Laplace transform**:
`Λ_t(s) = (1+s)^{−1/2} − e₁s/((1+s)^{3/2} t) + O(t⁻²)`. -/
theorem locLaplace_rate2 (hg : 0 ≤ g) {s : ℝ} (hs : -1 < s) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => Real.exp
        (-(s * t * anharmonicPotential lam alpha gamma x))) - 1 / Real.sqrt (1 + s) +
        energyLocCoeff1 lam alpha gamma g x₀ * s / (Real.sqrt (1 + s) * (1 + s) * t)| ≤ K / t ^ 2 :=
        by
  obtain ⟨K, T, hK, hT, h⟩ := locLaplace_scaled_rate2 hlam hgamma hdisc hg hs (x₀ := x₀)
  have ha : 0 < 1 + s := by linarith
  have hsa : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr ha
  refine ⟨1 / Real.sqrt (1 + s) * K, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hc : 1 / Real.sqrt (1 + s) * (Real.sqrt (1 + s) * _root_.Laplace.gibbsExpectation
      (locPotential1 lam alpha gamma g x₀ t) t (fun x => Real.exp (-(s * t * anharmonicPotential lam
      alpha gamma x)))) = _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
      (fun x => Real.exp (-(s * t * anharmonicPotential lam alpha gamma x))) := by
    rw [← mul_assoc, one_div_mul_cancel hsa.ne', one_mul]
  have e : _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
      Real.exp (-(s * t * anharmonicPotential lam alpha gamma x))) - 1 / Real.sqrt (1 + s) +
      energyLocCoeff1 lam alpha gamma g x₀ * s / (Real.sqrt (1 + s) * (1 + s) * t) = 1 / Real.sqrt
      (1 + s) * (Real.sqrt (1 + s) * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma
      g x₀ t) t (fun x => Real.exp (-(s * t * anharmonicPotential lam alpha gamma x))) - 1 -
      (-(energyLocCoeff1 lam alpha gamma g x₀ * s / (1 + s))) / t) := by
    rw [mul_sub, mul_sub, hc]
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt (1 + s))]
  calc _ ≤ 1 / Real.sqrt (1 + s) * (K / t ^ 2) :=
        mul_le_mul_of_nonneg_left (h ht) (by positivity)
    _ = _ := by ring

end OneD

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The two-term expansion of the E2 Laplace transform**:
`⟨e^{−st·L∘A}⟩_loc = (1+s)^{−d/2}(1 − s(∑ᵢe₁ᵢ)/((1+s)t)) + O(t⁻²)` — the first finite-temperature
correction to the `Gamma(d/2, 1)` transform is governed by the energy coefficient `∑ᵢe₁ᵢ`. -/
theorem localisedLaplace_rate2 (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {s : ℝ}
    (hs : -1 < s) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => Real.exp
        (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) - (1 / Real.sqrt (1 + s)) ^ d * (1 +
        (∑ i, -(energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) * s / (1 + s)))
        / t)| ≤ K / t ^ 2 := by
  choose K T hK hT h using fun i =>
    locLaplace_scaled_rate2 (hlam i) (hgamma i) (hdisc i) hg hs (x₀ := affineFrame Q c w₀ i)
  obtain ⟨C, T', hC, hT', hprod⟩ := prod_one_rate2 Finset.univ
    (fun i t => Real.sqrt (1 + s) * _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i)
      (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => Real.exp (-(s * t * anharmonicPotential (lam
      i) (alpha i) (gamma i) x)))) (fun i => -(energyLocCoeff1 (lam i) (alpha i) (gamma i) g
      (affineFrame Q c w₀ i) * s / (1 + s))) K T hK hT (fun i {t} ht => h i ht)
  have ha : 0 < 1 + s := by linarith
  have hsa : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr ha
  refine ⟨(1 / Real.sqrt (1 + s)) ^ d * C, T', by positivity, hT', fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedLaplace_eq_prod hQ c w₀ hs ht0]
  have e : (1 / Real.sqrt (1 + s)) ^ d * ∏ i, (Real.sqrt (1 + s) * _root_.Laplace.gibbsExpectation
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => Real.exp
      (-(s * t * anharmonicPotential (lam i) (alpha i) (gamma i) x)))) = ∏ i,
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (fun x => Real.exp (-(s * t * anharmonicPotential (lam i) (alpha i) (gamma i) x)))
      := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_assoc,
      ← mul_pow, one_div_mul_cancel hsa.ne', one_pow, one_mul]
  rw [← e, ← mul_sub, sub_add_eq_sub_sub, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (1 / Real.sqrt (1 + s)) ^ d)]
  calc _ ≤ (1 / Real.sqrt (1 + s)) ^ d * (C / t ^ 2) :=
        mul_le_mul_of_nonneg_left (hprod ht) (by positivity)
    _ = _ := by ring

end Multi

end Laplace.Multi
