/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovKOrder2Multi
import Laplace.Multi.LocalisedLLCCoeff

/-!
# eq:covK on the exact localised measure

E3 localises the Gibbs measure by `e^{−(g/2)|w − w₀|²}`; its eq:covK is `−∂ₜ` of the displayed
localised eq:cov/eq:mean (`CovKDerivativeLoc`). Here the covariance of the *unlocalised* energy with
a probe, taken on the exact localised anharmonic measure, is computed at leading order:

`t²Cov_loc[ℓ, x] = c + O(1/t)`, `c = −α/(2λ²) + a/λ` (`a = g x₀`),
`t²Cov_loc[ℓ, x²] = 1/λ + O(1/t)`,

so at leading order the localiser enters only through the anchor (`a/λ`, the `−∂ₜ` of the
anchor term `a/(tλ + g)` of the localised eq:mean), and `g` alone does not. Then E2's rotated
oscillator, through a generic two-family separable covariance decomposition.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

/-! ### Generic: the energy–probe covariance on a separable measure, two families -/

section Generic

variable {ι : Type*} [Fintype ι] {t : ℝ}

/-- `Cov[∑ₖ φₖ(uₖ), f(uᵢ)] = Cov_i[φᵢ, f]` on the separable measure of the family `ℓ`. -/
theorem gibbsCov_energy_coord_separable (ℓ φ : ι → ℝ → ℝ)
    (hZ : ∀ m, _root_.Laplace.partitionFunction (ℓ m) t ≠ 0) (i : ι) (f : ℝ → ℝ)
    (hE : ∀ k, Integrable (fun u : ι → ℝ => φ k (u k) * Real.exp (-(t * separablePotential ℓ u))))
    (hEP : ∀ k, Integrable (fun u : ι → ℝ =>
      φ k (u k) * f (u i) * Real.exp (-(t * separablePotential ℓ u)))) :
    gibbsCov (separablePotential ℓ) t (fun u => ∑ k, φ k (u k)) (fun u => f (u i)) =
      _root_.Laplace.gibbsCov (ℓ i) t (φ i) f := by
  classical
  calc gibbsCov (separablePotential ℓ) t (fun u => ∑ k, φ k (u k)) (fun u => f (u i))
      = ∑ k, gibbsCov (separablePotential ℓ) t (fun u => φ k (u k)) (fun u => f (u i)) :=
        gibbsCov_finsetSum_left _ t Finset.univ _ _ (fun k _ => hE k) (fun k _ => hEP k)
    _ = ∑ k, if k = i then _root_.Laplace.gibbsCov (ℓ k) t (φ k) f else 0 :=
        Finset.sum_congr rfl fun k _ => gibbsCov_coord_fun_separable ℓ t hZ k i (φ k) f
    _ = _ := by
        rw [Finset.sum_eq_single i (fun k _ hk => if_neg hk)
          (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]

/-- `Cov[∑ₖ φₖ(uₖ), uᵢuⱼ] = ⟨x⟩_j Cov_i[φᵢ, x] + ⟨x⟩_i Cov_j[φⱼ, x]` for `i ≠ j`, on the separable
measure of the family `ℓ` (the observable family `φ` may differ from `ℓ`). -/
theorem gibbsCov_energy_pair_separable (ℓ φ : ι → ℝ → ℝ)
    (hZ : ∀ m, _root_.Laplace.partitionFunction (ℓ m) t ≠ 0) {i j : ι} (hij : i ≠ j)
    (hE : ∀ k, Integrable (fun u : ι → ℝ => φ k (u k) * Real.exp (-(t * separablePotential ℓ u))))
    (hEP : ∀ k, Integrable (fun u : ι → ℝ =>
      φ k (u k) * (u i * u j) * Real.exp (-(t * separablePotential ℓ u)))) :
    gibbsCov (separablePotential ℓ) t (fun u => ∑ k, φ k (u k)) (fun u => u i * u j) =
      _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) *
        _root_.Laplace.gibbsCov (ℓ i) t (φ i) (fun x => x) +
      _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
        _root_.Laplace.gibbsCov (ℓ j) t (φ j) (fun x => x) := by
  classical
  have hji : j ≠ i := Ne.symm hij
  have hterm : ∀ k, gibbsCov (separablePotential ℓ) t (fun u => φ k (u k)) (fun u => u i * u j) =
      if k = i then _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) *
        _root_.Laplace.gibbsCov (ℓ i) t (φ i) (fun x => x)
      else if k = j then _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
        _root_.Laplace.gibbsCov (ℓ j) t (φ j) (fun x => x)
      else 0 := by
    intro k
    unfold gibbsCov _root_.Laplace.gibbsCov
    have hpair : gibbsExpectation (separablePotential ℓ) t (fun u => u i * u j) =
        _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
          _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) :=
      gibbsExpectation_two_coord_separable ℓ t hZ hij (fun x => x) (fun x => x)
    have hEk : gibbsExpectation (separablePotential ℓ) t (fun u => φ k (u k)) =
        _root_.Laplace.gibbsExpectation (ℓ k) t (φ k) :=
      gibbsExpectation_coord_separable ℓ t hZ k (φ k)
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl, hpair, hEk]
      have : gibbsExpectation (separablePotential ℓ) t (fun u => φ k (u k) * (u k * u j)) =
          _root_.Laplace.gibbsExpectation (ℓ k) t (fun x => φ k x * x) *
            _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) := by
        have h := gibbsExpectation_two_coord_separable ℓ t hZ hij (fun x => φ k x * x) (fun x => x)
        convert h using 2
        funext u
        ring
      rw [this]
      ring
    · by_cases hkj : k = j
      · subst hkj
        rw [if_neg hki, if_pos rfl, hpair, hEk]
        have : gibbsExpectation (separablePotential ℓ) t (fun u => φ k (u k) * (u i * u k)) =
            _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
              _root_.Laplace.gibbsExpectation (ℓ k) t (fun x => φ k x * x) := by
          have h := gibbsExpectation_two_coord_separable ℓ t hZ hij (fun x => x)
            (fun x => φ k x * x)
          convert h using 2
          funext u
          ring
        rw [this]
        ring
      · rw [if_neg hki, if_neg hkj, hpair, hEk]
        have : gibbsExpectation (separablePotential ℓ) t (fun u => φ k (u k) * (u i * u j)) =
            _root_.Laplace.gibbsExpectation (ℓ k) t (φ k) *
              _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
              _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) := by
          have h := gibbsExpectation_three_coord_separable ℓ t hZ hki hkj hij (φ k) (fun x => x)
            (fun x => x)
          convert h using 2
          funext u
          ring
        rw [this]
        ring
  calc gibbsCov (separablePotential ℓ) t (fun u => ∑ k, φ k (u k)) (fun u => u i * u j)
      = ∑ k, gibbsCov (separablePotential ℓ) t (fun u => φ k (u k)) (fun u => u i * u j) :=
        gibbsCov_finsetSum_left _ t Finset.univ _ _ (fun k _ => hE k) (fun k _ => hEP k)
    _ = _ := by
        simp_rw [hterm]
        rw [Finset.sum_eq_add i j hij (fun k _ hk => by rw [if_neg hk.1, if_neg hk.2])
          (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h),
          if_pos rfl, if_neg hji, if_pos rfl]

end Generic

/-! ### One dimension: the fifth and sixth localised moments are `O(t⁻³)` -/

section Fifth

variable {g x₀ : ℝ}

/-- The even envelope of the `x⁵φ` remainder (the shared expansion times `x³`). -/
noncomputable def locN₆ (g x₀ : ℝ) : ℝ := |locP₃ g x₀| / 2
noncomputable def locN₈ (g x₀ : ℝ) : ℝ := |locP₃ g x₀| / 2 + |locP₄ g x₀| + locH₆ g x₀ / 2
noncomputable def locN₁₀ (g x₀ : ℝ) : ℝ := locH₆ g x₀ / 2 + locH₈ g x₀ / 2
noncomputable def locN₁₂ (g x₀ : ℝ) : ℝ := locH₈ g x₀ / 2 + locH₁₀ g x₀ / 2
noncomputable def locN₁₄ (g x₀ : ℝ) : ℝ := locH₁₀ g x₀ / 2

theorem locN₆_nonneg (g x₀ : ℝ) : 0 ≤ locN₆ g x₀ := by unfold locN₆; positivity
theorem locN₈_nonneg (g x₀ : ℝ) : 0 ≤ locN₈ g x₀ := by
  unfold locN₈; have := locH₆_nonneg g x₀; positivity
theorem locN₁₀_nonneg (g x₀ : ℝ) : 0 ≤ locN₁₀ g x₀ := by
  unfold locN₁₀; have := locH₆_nonneg g x₀; have := locH₈_nonneg g x₀; positivity
theorem locN₁₂_nonneg (g x₀ : ℝ) : 0 ≤ locN₁₂ g x₀ := by
  unfold locN₁₂; have := locH₈_nonneg g x₀; have := locH₁₀_nonneg g x₀; positivity
theorem locN₁₄_nonneg (g x₀ : ℝ) : 0 ≤ locN₁₄ g x₀ := by
  unfold locN₁₄; have := locH₁₀_nonneg g x₀; positivity

/-- `|x⁵φ − (x⁵ + ax⁶)| ≤ N₆x⁶ + N₈x⁸ + N₁₀x¹⁰ + N₁₂x¹² + N₁₄x¹⁴` (the signed `x⁵` kept exact). -/
theorem locFifth_pointwise (hg : 0 ≤ g) (x : ℝ) :
    |x ^ 5 * locWeight g x₀ x - (x ^ 5 + g * x₀ * x ^ 6)| ≤
      locN₆ g x₀ * x ^ 6 + locN₈ g x₀ * x ^ 8 + locN₁₀ g x₀ * x ^ 10 + locN₁₂ g x₀ * x ^ 12 +
        locN₁₄ g x₀ * x ^ 14 := by
  have hS := locSquare_pointwise (x₀ := x₀) hg x
  have e : x ^ 5 * locWeight g x₀ x - (x ^ 5 + g * x₀ * x ^ 6) =
      x ^ 3 * (x ^ 2 * locWeight g x₀ x -
        (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)) +
        (locP₃ g x₀ * x ^ 7 + locP₄ g x₀ * x ^ 8) := by ring
  have hx6 : x ^ 6 = |x| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : x ^ 8 = |x| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx10 : x ^ 10 = |x| ^ 10 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx12 : x ^ 12 = |x| ^ 12 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx14 : x ^ 14 = |x| ^ 14 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h7 : |x| ^ 7 ≤ (|x| ^ 6 + |x| ^ 8) / 2 := by nlinarith [sq_nonneg (|x| ^ 3 - |x| ^ 4)]
  have h9 : |x| ^ 9 ≤ (|x| ^ 8 + |x| ^ 10) / 2 := by nlinarith [sq_nonneg (|x| ^ 4 - |x| ^ 5)]
  have h11 : |x| ^ 11 ≤ (|x| ^ 10 + |x| ^ 12) / 2 := by nlinarith [sq_nonneg (|x| ^ 5 - |x| ^ 6)]
  have h13 : |x| ^ 13 ≤ (|x| ^ 12 + |x| ^ 14) / 2 := by nlinarith [sq_nonneg (|x| ^ 6 - |x| ^ 7)]
  have hH₆ := locH₆_nonneg g x₀
  have hH₈ := locH₈_nonneg g x₀
  have hH₁₀ := locH₁₀_nonneg g x₀
  rw [e]
  calc |x ^ 3 * (x ^ 2 * locWeight g x₀ x -
          (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)) +
          (locP₃ g x₀ * x ^ 7 + locP₄ g x₀ * x ^ 8)|
      ≤ |x| ^ 3 * (locH₆ g x₀ * x ^ 6 + locH₈ g x₀ * x ^ 8 + locH₁₀ g x₀ * x ^ 10) +
          (|locP₃ g x₀| * |x| ^ 7 + |locP₄ g x₀| * |x| ^ 8) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_pow]
        gcongr
        calc |locP₃ g x₀ * x ^ 7 + locP₄ g x₀ * x ^ 8|
            ≤ |locP₃ g x₀ * x ^ 7| + |locP₄ g x₀ * x ^ 8| := abs_add_le _ _
          _ = |locP₃ g x₀| * |x| ^ 7 + |locP₄ g x₀| * |x| ^ 8 := by simp only [abs_mul, abs_pow]
    _ = locH₆ g x₀ * |x| ^ 9 + locH₈ g x₀ * |x| ^ 11 + locH₁₀ g x₀ * |x| ^ 13 +
          (|locP₃ g x₀| * |x| ^ 7 + |locP₄ g x₀| * |x| ^ 8) := by rw [hx6, hx8, hx10]; ring
    _ ≤ locH₆ g x₀ * ((|x| ^ 8 + |x| ^ 10) / 2) + locH₈ g x₀ * ((|x| ^ 10 + |x| ^ 12) / 2) +
          locH₁₀ g x₀ * ((|x| ^ 12 + |x| ^ 14) / 2) +
          (|locP₃ g x₀| * ((|x| ^ 6 + |x| ^ 8) / 2) + |locP₄ g x₀| * |x| ^ 8) := by gcongr
    _ = locN₆ g x₀ * x ^ 6 + locN₈ g x₀ * x ^ 8 + locN₁₀ g x₀ * x ^ 10 + locN₁₂ g x₀ * x ^ 12 +
          locN₁₄ g x₀ * x ^ 14 := by
        rw [hx6, hx8, hx10, hx12, hx14]
        unfold locN₆ locN₈ locN₁₀ locN₁₂ locN₁₄
        ring

end Fifth

section FifthRates

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `|⟨x⁵φ⟩ − (⟨x⁵⟩ + a⟨x⁶⟩)| ≤ N₆⟨x⁶⟩ + … + N₁₄⟨x¹⁴⟩`. -/
theorem locFifth_expansion (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 5 * locWeight g x₀ x) -
      (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6))| ≤
      locN₆ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locN₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) +
        locN₁₀ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 10) +
        locN₁₂ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 12) +
        locN₁₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 14) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 5
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht
  have h6 : Integrable (fun x => (g * x₀ * x ^ 6) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    ((hp 6).const_mul (g * x₀)).congr (Eventually.of_forall fun x => by dsimp only; ring)
  have hP : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 5 + g * x₀ * x ^ 6) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) := by
    rw [gibbs_add' (hp 5) h6, gibbsExpectation_const_mul₁]
  have hPint : Integrable (fun x => (x ^ 5 + g * x₀ * x ^ 6) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine ((hp 5).add h6).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hF : Integrable (fun x => (x ^ 5 * locWeight g x₀ x - (x ^ 5 + g * x₀ * x ^ 6)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hf.sub hPint).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locN₆ g x₀ * x ^ 6 + locN₈ g x₀ * x ^ 8 +
      locN₁₀ g x₀ * x ^ 10 + locN₁₂ g x₀ * x ^ 12 + locN₁₄ g x₀ * x ^ 14) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (((((hp 6).const_mul (locN₆ g x₀)).add ((hp 8).const_mul (locN₈ g x₀))).add
      ((hp 10).const_mul (locN₁₀ g x₀))).add ((hp 12).const_mul (locN₁₂ g x₀))).add
      ((hp 14).const_mul (locN₁₄ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← hP, ← gibbs_sub' hf hPint, ← gibbs_lin5 (hp 6) (hp 8) (hp 10) (hp 12) (hp 14)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x =>
      locFifth_pointwise hg x)

/-- **The weighted fifth moment is `O(t⁻³)`**: `|t³⟨x⁵φ⟩| ≤ K`. -/
theorem locFifth_bound (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 5 * locWeight g x₀ x)| ≤ K := by
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  obtain ⟨C₁₀, T₁₀, hC₁₀, hT₁₀, h₁₀⟩ := evenMoment_bound hlam hgamma hdisc 5
  obtain ⟨C₁₂, T₁₂, hC₁₂, hT₁₂, h₁₂⟩ := evenMoment_bound hlam hgamma hdisc 6
  obtain ⟨C₁₄, T₁₄, hC₁₄, hT₁₄, h₁₄⟩ := evenMoment_bound hlam hgamma hdisc 7
  simp only [show (2 * 3 : ℕ) = 6 from rfl, show (2 * 4 : ℕ) = 8 from rfl,
    show (2 * 5 : ℕ) = 10 from rfl, show (2 * 6 : ℕ) = 12 from rfl,
    show (2 * 7 : ℕ) = 14 from rfl] at h₆ h₈ h₁₀ h₁₂ h₁₄
  have hN₆ := locN₆_nonneg g x₀
  have hN₈ := locN₈_nonneg g x₀
  have hN₁₀ := locN₁₀_nonneg g x₀
  have hN₁₂ := locN₁₂_nonneg g x₀
  have hN₁₄ := locN₁₄_nonneg g x₀
  have h1T : (1 : ℝ) ≤ T₅ + T₆ + T₈ + T₁₀ + T₁₂ + T₁₄ := by linarith
  refine ⟨(|-(35 * alpha / (2 * lam ^ 4))| + K₅) + |g * x₀| * C₆ +
      (locN₆ g x₀ * C₆ + locN₈ g x₀ * C₈ + locN₁₀ g x₀ * C₁₀ + locN₁₂ g x₀ * C₁₂ +
        locN₁₄ g x₀ * C₁₄),
    T₅ + T₆ + T₈ + T₁₀ + T₁₂ + T₁₄, by positivity, h1T, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hZ := partition_pos' hlam hgamma hdisc ht0
  set M₅ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 5) with hM₅
  set M₆ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 6) with hM₆
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 5 * locWeight g x₀ x) with hN
  have e₅ : |t ^ 3 * M₅| ≤ |-(35 * alpha / (2 * lam ^ 4))| + K₅ :=
    Laplace.OneD.rate_bounded ht1 hK₅ (h₅ (t := t) (by linarith))
  have hM₆0 : 0 ≤ M₆ := by
    have := abs_gibbsExpectation_le' hZ (fun x : ℝ => x ^ 6)
    have e : (fun x : ℝ => |x ^ 6|) = fun x => x ^ 6 := by
      funext x
      exact abs_of_nonneg (by positivity)
    rw [e] at this
    exact (abs_nonneg _).trans this
  have e₆ : |t ^ 3 * M₆| ≤ C₆ := by
    rw [abs_of_nonneg (by positivity)]
    have := h₆ (t := t) (by linarith)
    calc t ^ 3 * M₆ ≤ t ^ 3 * (C₆ / t ^ 3) := by gcongr
      _ = C₆ := by field_simp
  have hR := (locFifth_expansion hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (h₆ (t := t) (by linarith)) hN₆)
      (mul_le_mul_of_nonneg_left (h₈ (t := t) (by linarith)) hN₈))
      (mul_le_mul_of_nonneg_left (h₁₀ (t := t) (by linarith)) hN₁₀))
      (mul_le_mul_of_nonneg_left (h₁₂ (t := t) (by linarith)) hN₁₂))
      (mul_le_mul_of_nonneg_left (h₁₄ (t := t) (by linarith)) hN₁₄))
  have hRt : locN₆ g x₀ * (C₆ / t ^ 3) + locN₈ g x₀ * (C₈ / t ^ 4) +
      locN₁₀ g x₀ * (C₁₀ / t ^ 5) + locN₁₂ g x₀ * (C₁₂ / t ^ 6) + locN₁₄ g x₀ * (C₁₄ / t ^ 7) ≤
      (locN₆ g x₀ * C₆ + locN₈ g x₀ * C₈ + locN₁₀ g x₀ * C₁₀ + locN₁₂ g x₀ * C₁₂ +
        locN₁₄ g x₀ * C₁₄) / t ^ 3 := by
    have h8 : locN₈ g x₀ * (C₈ / t ^ 4) ≤ locN₈ g x₀ * (C₈ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₈ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hN₈
    have h10 : locN₁₀ g x₀ * (C₁₀ / t ^ 5) ≤ locN₁₀ g x₀ * (C₁₀ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₀ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hN₁₀
    have h12 : locN₁₂ g x₀ * (C₁₂ / t ^ 6) ≤ locN₁₂ g x₀ * (C₁₂ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₂ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hN₁₂
    have h14 : locN₁₄ g x₀ * (C₁₄ / t ^ 7) ≤ locN₁₄ g x₀ * (C₁₄ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₄ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hN₁₄
    have e : (locN₆ g x₀ * C₆ + locN₈ g x₀ * C₈ + locN₁₀ g x₀ * C₁₀ + locN₁₂ g x₀ * C₁₂ +
        locN₁₄ g x₀ * C₁₄) / t ^ 3 =
        locN₆ g x₀ * (C₆ / t ^ 3) + locN₈ g x₀ * (C₈ / t ^ 3) + locN₁₀ g x₀ * (C₁₀ / t ^ 3) +
          locN₁₂ g x₀ * (C₁₂ / t ^ 3) + locN₁₄ g x₀ * (C₁₄ / t ^ 3) := by ring
    rw [e]
    linarith
  have hRt3 : |t ^ 3 * (N - (M₅ + g * x₀ * M₆))| ≤
      locN₆ g x₀ * C₆ + locN₈ g x₀ * C₈ + locN₁₀ g x₀ * C₁₀ + locN₁₂ g x₀ * C₁₂ +
        locN₁₄ g x₀ * C₁₄ := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 3)]
    calc t ^ 3 * |N - (M₅ + g * x₀ * M₆)| ≤ t ^ 3 * ((locN₆ g x₀ * C₆ + locN₈ g x₀ * C₈ +
          locN₁₀ g x₀ * C₁₀ + locN₁₂ g x₀ * C₁₂ + locN₁₄ g x₀ * C₁₄) / t ^ 3) :=
          mul_le_mul_of_nonneg_left (hR.trans hRt) (by positivity)
      _ = _ := by field_simp
  have key : t ^ 3 * N = t ^ 3 * M₅ + g * x₀ * (t ^ 3 * M₆) + t ^ 3 * (N - (M₅ + g * x₀ * M₆)) := by
    ring
  rw [key]
  calc _ ≤ |t ^ 3 * M₅| + |g * x₀ * (t ^ 3 * M₆)| + |t ^ 3 * (N - (M₅ + g * x₀ * M₆))| :=
        abs_add_three _ _ _
    _ ≤ (|-(35 * alpha / (2 * lam ^ 4))| + K₅) + |g * x₀| * C₆ +
        (locN₆ g x₀ * C₆ + locN₈ g x₀ * C₈ + locN₁₀ g x₀ * C₁₀ + locN₁₂ g x₀ * C₁₂ +
          locN₁₄ g x₀ * C₁₄) := by
        rw [abs_mul (g * x₀)]
        gcongr

/-- **The weighted sixth moment is `O(t⁻³)`**: `|t³⟨x⁶φ⟩| ≤ K` (`φ ≤ e^{gx₀²/2}`). -/
theorem locSixth_bound (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 6 * locWeight g x₀ x)| ≤ K := by
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  simp only [show (2 * 3 : ℕ) = 6 from rfl] at h₆
  refine ⟨Real.exp (g * x₀ ^ 2 / 2) * C₆, T₆, by positivity, hT₆, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hZ := partition_pos' hlam hgamma hdisc ht0
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht0
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht0 (x₀ := x₀) 6
  have hG : Integrable (fun x => (Real.exp (g * x₀ ^ 2 / 2) * x ^ 6) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    ((hp 6).const_mul _).congr (Eventually.of_forall fun x => by dsimp only; ring)
  have hmono : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => |x ^ 6 * locWeight g x₀ x|) ≤
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => Real.exp (g * x₀ ^ 2 / 2) * x ^ 6) := by
    refine gibbsExpectation_mono' hZ (integrable_abs_weighted hf) hG fun x => ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 6),
      abs_of_pos (locWeight_pos x), mul_comm]
    exact mul_le_mul_of_nonneg_right (locWeight_le hg x) (by positivity)
  rw [gibbsExpectation_const_mul₁] at hmono
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 3)]
  calc t ^ 3 * |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 6 * locWeight g x₀ x)|
      ≤ t ^ 3 * (Real.exp (g * x₀ ^ 2 / 2) *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ 6)) :=
        mul_le_mul_of_nonneg_left ((abs_gibbsExpectation_le' hZ _).trans hmono) (by positivity)
    _ ≤ t ^ 3 * (Real.exp (g * x₀ ^ 2 / 2) * (C₆ / t ^ 3)) := by
        gcongr
        exact h₆ (t := t) (by linarith)
    _ = Real.exp (g * x₀ ^ 2 / 2) * C₆ := by field_simp

/-- Dividing a bounded `t³`-weighted quantity by the denominator (`|D − 1| ≤ KD/t`, `D ≥ ½`). -/
theorem loc_ratio_bounded (f : ℝ → ℝ) (hg : 0 ≤ g)
    (hN : ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => f x * locWeight g x₀ x)| ≤ K) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t f| ≤ K := by
  obtain ⟨KN, TN, hKN, hTN, hN⟩ := hN
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨2 * KN, TN + TD + 2 * KD, by positivity, by linarith, fun {t} ht => ?_⟩
  have hTNt : TN ≤ t := by linarith
  have hTDt : TD ≤ t := by linarith
  have h2K : 2 * KD ≤ t := by linarith
  have ht1 : 1 ≤ t := hTN.trans hTNt
  have ht0 : 0 < t := by linarith
  rw [gibbsExpectation_locPotential1 hlam hgamma hdisc ht0]
  have eN := hN hTNt
  have eD := hD hTDt
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => f x * locWeight g x₀ x) with hNdef
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
  have hDhalf : 1 / 2 ≤ D := by
    have h1 : KD / t ≤ 1 / 2 := by rw [div_le_iff₀ ht0]; linarith
    have h2 := (abs_le.mp (eD.trans h1)).1
    linarith
  have hD0 : 0 < D := by linarith
  rw [show t ^ 3 * (N / D) = (t ^ 3 * N) / D by ring, abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  calc |t ^ 3 * N| ≤ KN := eN
    _ = 2 * KN * (1 / 2) := by ring
    _ ≤ 2 * KN * D := by gcongr

theorem locFifth_loc_bound (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 5)| ≤ K :=
  loc_ratio_bounded hlam hgamma hdisc (fun x => x ^ 5) hg (locFifth_bound hlam hgamma hdisc hg)

theorem locSixth_loc_bound (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 6)| ≤ K :=
  loc_ratio_bounded hlam hgamma hdisc (fun x => x ^ 6) hg (locSixth_bound hlam hgamma hdisc hg)

end FifthRates

/-! ### One dimension: eq:covK on the localised measure at leading order -/

section CovK

/-- A second-order rate weakened to first order:
`|X − c − c'/t| ≤ K/t² → |X − c| ≤ (|c'| + K)/t`. -/
theorem order2_to_order1 {X c c' K t : ℝ} (ht1 : 1 ≤ t) (hK : 0 ≤ K)
    (h : |X - c - c' / t| ≤ K / t ^ 2) : |X - c| ≤ (|c'| + K) / t := by
  have ht0 : 0 < t := by linarith
  calc |X - c| = |(X - c - c' / t) + c' / t| := by ring_nf
    _ ≤ |X - c - c' / t| + |c' / t| := abs_add_le _ _
    _ ≤ K / t ^ 2 + |c'| / t := by
        gcongr
        rw [abs_div, abs_of_pos ht0]
    _ ≤ K / t + |c'| / t := by
        gcongr
        nlinarith
    _ = (|c'| + K) / t := by ring

/-- The assembly of `t²Cov[ℓ, x]` on abstract reals: with `E = (λ/2)M₃ + (α/6)M₄ + (γ/24)M₅`,
`|t²(E − F·M₁) − c| ≤ K/t` from the moment rates and the product `(tF)(tM₁) → ½c`. -/
theorem covK_loc_lin_assembly (lam alpha gamma t E F M₁ M₃ M₄ M₅ c c₃' K₃ K₄ K₅ K_F K_M : ℝ)
    (hlam : 0 < lam) (hgamma : 0 < gamma) (ht1 : 1 ≤ t) (hK_F : 0 ≤ K_F) (hK_M : 0 ≤ K_M)
    (hE : E = lam / 2 * M₃ + alpha / 6 * M₄ + gamma / 24 * M₅)
    (hc : lam / 2 * c₃' + alpha / 6 * (3 / lam ^ 2) - 1 / 2 * c = c)
    (e₃ : |t ^ 2 * M₃ - c₃'| ≤ K₃ / t) (e₄ : |t ^ 2 * M₄ - 3 / lam ^ 2| ≤ K₄ / t)
    (e₅ : |t ^ 3 * M₅| ≤ K₅) (eF : |t * F - 1 / 2| ≤ K_F / t) (eM : |t * M₁ - c| ≤ K_M / t) :
    |t ^ 2 * (E - F * M₁) - c| ≤
      (lam / 2 * K₃ + |alpha| / 6 * K₄ + gamma / 24 * K₅ +
        (K_F * (|c| + K_M) + |1 / 2| * K_M)) / t := by
  have ht0 : 0 < t := by linarith
  have hprod := prod_rate t (t * F) (t * M₁) (1 / 2) c K_F K_M ht1 hK_F hK_M eF eM
  have key : t ^ 2 * (E - F * M₁) - c =
      lam / 2 * (t ^ 2 * M₃ - c₃') + alpha / 6 * (t ^ 2 * M₄ - 3 / lam ^ 2) +
        gamma / 24 * (t ^ 2 * M₅) - ((t * F) * (t * M₁) - 1 / 2 * c) := by
    rw [hE]
    linear_combination hc
  rw [key]
  have b₃ : |lam / 2 * (t ^ 2 * M₃ - c₃')| ≤ lam / 2 * (K₃ / t) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam / 2)]
    exact mul_le_mul_of_nonneg_left e₃ (by positivity)
  have b₄ : |alpha / 6 * (t ^ 2 * M₄ - 3 / lam ^ 2)| ≤ |alpha| / 6 * (K₄ / t) := by
    rw [abs_mul, abs_div alpha, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact mul_le_mul_of_nonneg_left e₄ (by positivity)
  have b₅ : |gamma / 24 * (t ^ 2 * M₅)| ≤ gamma / 24 * (K₅ / t) := by
    have e : t ^ 2 * M₅ = t ^ 3 * M₅ / t := by
      rw [eq_div_iff ht0.ne']
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 24), abs_div, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₅ ht0.le) (by positivity)
  calc _ ≤ |lam / 2 * (t ^ 2 * M₃ - c₃') + alpha / 6 * (t ^ 2 * M₄ - 3 / lam ^ 2) +
        gamma / 24 * (t ^ 2 * M₅)| + |(t * F) * (t * M₁) - 1 / 2 * c| := abs_sub _ _
    _ ≤ (lam / 2 * (K₃ / t) + |alpha| / 6 * (K₄ / t) + gamma / 24 * (K₅ / t)) +
        (K_F * (|c| + K_M) + |1 / 2| * K_M) / t :=
        add_le_add ((abs_add_three _ _ _).trans (add_le_add (add_le_add b₃ b₄) b₅)) hprod
    _ = _ := by ring

/-- The assembly of `t²Cov[ℓ, x²]` on abstract reals: with `E = (λ/2)M₄ + (α/6)M₅ + (γ/24)M₆`,
`|t²(E − F·M₂) − 1/λ| ≤ K/t`. -/
theorem covK_loc_sq_assembly (lam alpha gamma t E F M₂ M₄ M₅ M₆ K₄ K₅ K₆ K_F K_M : ℝ)
    (hlam : 0 < lam) (hgamma : 0 < gamma) (ht1 : 1 ≤ t) (hK_F : 0 ≤ K_F) (hK_M : 0 ≤ K_M)
    (hE : E = lam / 2 * M₄ + alpha / 6 * M₅ + gamma / 24 * M₆)
    (e₄ : |t ^ 2 * M₄ - 3 / lam ^ 2| ≤ K₄ / t) (e₅ : |t ^ 3 * M₅| ≤ K₅) (e₆ : |t ^ 3 * M₆| ≤ K₆)
    (eF : |t * F - 1 / 2| ≤ K_F / t) (eM : |t * M₂ - 1 / lam| ≤ K_M / t) :
    |t ^ 2 * (E - F * M₂) - 1 / lam| ≤
      (lam / 2 * K₄ + |alpha| / 6 * K₅ + gamma / 24 * K₆ +
        (K_F * (|1 / lam| + K_M) + |1 / 2| * K_M)) / t := by
  have ht0 : 0 < t := by linarith
  have hprod := prod_rate t (t * F) (t * M₂) (1 / 2) (1 / lam) K_F K_M ht1 hK_F hK_M eF eM
  have key : t ^ 2 * (E - F * M₂) - 1 / lam =
      lam / 2 * (t ^ 2 * M₄ - 3 / lam ^ 2) + alpha / 6 * (t ^ 3 * M₅ / t) +
        gamma / 24 * (t ^ 3 * M₆ / t) - ((t * F) * (t * M₂) - 1 / 2 * (1 / lam)) := by
    rw [hE]
    field_simp
    ring
  rw [key]
  have b₄ : |lam / 2 * (t ^ 2 * M₄ - 3 / lam ^ 2)| ≤ lam / 2 * (K₄ / t) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam / 2)]
    exact mul_le_mul_of_nonneg_left e₄ (by positivity)
  have b₅ : |alpha / 6 * (t ^ 3 * M₅ / t)| ≤ |alpha| / 6 * (K₅ / t) := by
    rw [abs_mul, abs_div alpha, abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_div (t ^ 3 * M₅),
      abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₅ ht0.le) (by positivity)
  have b₆ : |gamma / 24 * (t ^ 3 * M₆ / t)| ≤ gamma / 24 * (K₆ / t) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 24), abs_div, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₆ ht0.le) (by positivity)
  calc _ ≤ |lam / 2 * (t ^ 2 * M₄ - 3 / lam ^ 2) + alpha / 6 * (t ^ 3 * M₅ / t) +
        gamma / 24 * (t ^ 3 * M₆ / t)| + |(t * F) * (t * M₂) - 1 / 2 * (1 / lam)| := abs_sub _ _
    _ ≤ (lam / 2 * (K₄ / t) + |alpha| / 6 * (K₅ / t) + gamma / 24 * (K₆ / t)) +
        (K_F * (|1 / lam| + K_M) + |1 / 2| * K_M) / t :=
        add_le_add ((abs_add_three _ _ _).trans (add_le_add (add_le_add b₄ b₅) b₆)) hprod
    _ = _ := by ring

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `⟨ℓ·x⟩_loc = (λ/2)⟨x³⟩_loc + (α/6)⟨x⁴⟩_loc + (γ/24)⟨x⁵⟩_loc`. -/
theorem locEnergyMul_eq (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => anharmonicPotential lam alpha gamma x * x) =
      lam / 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 3) +
        alpha / 6 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 4) +
        gamma / 24 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 5) := by
  have e : (fun x => anharmonicPotential lam alpha gamma x * x) =
      fun x => lam / 2 * x ^ 3 + alpha / 6 * x ^ 4 + gamma / 24 * x ^ 5 := by
    funext x
    rw [anharmonicPotential_eq_lin]
    ring
  rw [e]
  exact gibbs_lin3 (integrable_pow_locPotential1 hlam hgamma hdisc hg ht 3)
    (integrable_pow_locPotential1 hlam hgamma hdisc hg ht 4)
    (integrable_pow_locPotential1 hlam hgamma hdisc hg ht 5)

/-- `⟨ℓ·x²⟩_loc = (λ/2)⟨x⁴⟩_loc + (α/6)⟨x⁵⟩_loc + (γ/24)⟨x⁶⟩_loc`. -/
theorem locEnergyMulSq_eq (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => anharmonicPotential lam alpha gamma x * x ^ 2) =
      lam / 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 4) +
        alpha / 6 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 5) +
        gamma / 24 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 6) := by
  have e : (fun x => anharmonicPotential lam alpha gamma x * x ^ 2) =
      fun x => lam / 2 * x ^ 4 + alpha / 6 * x ^ 5 + gamma / 24 * x ^ 6 := by
    funext x
    rw [anharmonicPotential_eq_lin]
    ring
  rw [e]
  exact gibbs_lin3 (integrable_pow_locPotential1 hlam hgamma hdisc hg ht 4)
    (integrable_pow_locPotential1 hlam hgamma hdisc hg ht 5)
    (integrable_pow_locPotential1 hlam hgamma hdisc hg ht 6)

/-- `|t⟨ℓ⟩_loc − ½| ≤ K/t`. -/
theorem localisedEnergy_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) - 1 / 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedEnergy_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  exact ⟨|energyLocCoeff1 lam alpha gamma g x₀| + K, T, by positivity, hT,
    fun {t} ht => order2_to_order1 (hT.trans ht) hK (h ht)⟩

/-- `|t⟨x²⟩_loc − 1/λ| ≤ K/t`. -/
theorem locSecondMoment_loc_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 2) - 1 / lam| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := locSecondMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  exact ⟨|locSecondCoeff2 lam alpha gamma g x₀| + K, T, by positivity, hT,
    fun {t} ht => order2_to_order1 (hT.trans ht) hK (h ht)⟩

/-- `|t⟨x⟩_loc − c| ≤ K/t` in the `gibbsExpectation (locPotential1 …)` form. -/
theorem locMean_loc_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x) - (-alpha / (2 * lam ^ 2) + g * x₀ / lam)| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedMean_anharmonic_rate_sharp hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [gibbsExpectation_locPotential1_id ht0]
  exact h ht

/-- **eq:covK on the localised measure, linear probe**: `|t²Cov_loc[ℓ, x] − c| ≤ K/t`,
`c = −α/(2λ²) + g x₀/λ` — the localiser enters at leading order only through the anchor. -/
theorem localisedCovK_lin_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x) -
        (-alpha / (2 * lam ^ 2) + g * x₀ / lam)| ≤ K / t := by
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locThirdMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := locFifth_loc_bound hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K_F, T_F, hK_F, hT_F, hF⟩ := localisedEnergy_leading hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K_M, T_M, hK_M, hT_M, hM⟩ := locMean_loc_leading hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨lam / 2 * K₃ + |alpha| / 6 * K₄ + gamma / 24 * K₅ +
      (K_F * (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| + K_M) + |(1 : ℝ) / 2| * K_M),
    T₃ + T₄ + T₅ + T_F + T_M, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hc : lam / 2 * locThirdCoeff lam alpha g x₀ + alpha / 6 * (3 / lam ^ 2) -
      1 / 2 * (-alpha / (2 * lam ^ 2) + g * x₀ / lam) = -alpha / (2 * lam ^ 2) + g * x₀ / lam := by
    unfold locThirdCoeff
    field_simp
    ring
  unfold _root_.Laplace.gibbsCov
  exact covK_loc_lin_assembly lam alpha gamma t _ _ _ _ _ _ _ _ K₃ K₄ K₅ K_F K_M hlam hgamma ht1
    hK_F hK_M (locEnergyMul_eq hlam hgamma hdisc hg ht0) hc (h₃ (t := t) (by linarith))
    (h₄ (t := t) (by linarith)) (h₅ (t := t) (by linarith)) (hF (t := t) (by linarith))
    (hM (t := t) (by linarith))

/-- **eq:covK on the localised measure, quadratic probe**: `|t²Cov_loc[ℓ, x²] − 1/λ| ≤ K/t` — the
unlocalised constant; the localiser does not enter at leading order. -/
theorem localisedCovK_sq_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) - 1 / lam| ≤ K / t := by
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := locFifth_loc_bound hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := locSixth_loc_bound hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K_F, T_F, hK_F, hT_F, hF⟩ := localisedEnergy_leading hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K_M, T_M, hK_M, hT_M, hM⟩ := locSecondMoment_loc_leading hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨lam / 2 * K₄ + |alpha| / 6 * K₅ + gamma / 24 * K₆ +
      (K_F * (|1 / lam| + K_M) + |(1 : ℝ) / 2| * K_M),
    T₄ + T₅ + T₆ + T_F + T_M, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  unfold _root_.Laplace.gibbsCov
  exact covK_loc_sq_assembly lam alpha gamma t _ _ _ _ _ _ K₄ K₅ K₆ K_F K_M hlam hgamma ht1
    hK_F hK_M (locEnergyMulSq_eq hlam hgamma hdisc hg ht0) (h₄ (t := t) (by linarith))
    (h₅ (t := t) (by linarith)) (h₆ (t := t) (by linarith)) (hF (t := t) (by linarith))
    (hM (t := t) (by linarith))

/-- The covariance is linear in the probe (1D, on the localised measure). -/
theorem localisedCov_probe_eq (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (B b : ℝ) :
    _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) =
      B / 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) +
        b * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x) := by
  have hp := integrable_pow_locPotential1 hlam hgamma hdisc hg ht (x₀ := x₀)
  have hℓ2 : Integrable (fun x => (anharmonicPotential lam alpha gamma x * x ^ 2) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := by
    have := (((hp 4).const_mul (lam / 2)).add ((hp 5).const_mul (alpha / 6))).add
      ((hp 6).const_mul (gamma / 24))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, anharmonicPotential_eq_lin]
    ring
  have hℓ1 : Integrable (fun x => (anharmonicPotential lam alpha gamma x * x) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := by
    have := (((hp 3).const_mul (lam / 2)).add ((hp 4).const_mul (alpha / 6))).add
      ((hp 5).const_mul (gamma / 24))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, anharmonicPotential_eq_lin]
    ring
  have h1 : Integrable (fun x => x * Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := by
    simpa using hp 1
  unfold _root_.Laplace.gibbsCov
  have e1 : (fun x => anharmonicPotential lam alpha gamma x * (B / 2 * x ^ 2 + b * x)) =
      fun x => B / 2 * (anharmonicPotential lam alpha gamma x * x ^ 2) +
        b * (anharmonicPotential lam alpha gamma x * x) := by
    funext x
    ring
  rw [e1, gibbsExpectation_lin hℓ2 hℓ1, gibbsExpectation_lin (hp 2) h1]
  ring

/-- **eq:covK on the localised measure for the probe `(B/2)x² + bx`**:
`|t²Cov_loc[ℓ, ψ] − (B/(2λ) + bc)| ≤ K/t`. Compared with the unlocalised `B/(2λ) − bα/(2λ²)`
the localiser contributes exactly `b·g x₀/λ`, the `−∂ₜ` of the anchor term `g x₀/(tλ + g)` of
the localised eq:mean at leading order; `g` alone (anchor at the minimiser) does not enter. -/
theorem localisedCovK_rate (hg : 0 ≤ g) (B b : ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) -
        (B / (2 * lam) + b * (-alpha / (2 * lam ^ 2) + g * x₀ / lam))| ≤ K / t := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := localisedCovK_sq_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := localisedCovK_lin_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨|B| / 2 * K₂ + |b| * K₁, T₁ + T₂, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e2 := h₂ (t := t) (by linarith)
  have e1 := h₁ (t := t) (by linarith)
  rw [localisedCov_probe_eq hlam hgamma hdisc hg ht0]
  have key : t ^ 2 * (B / 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) +
        b * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x)) -
      (B / (2 * lam) + b * (-alpha / (2 * lam ^ 2) + g * x₀ / lam)) =
      B / 2 * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) - 1 / lam) +
      b * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x) -
        (-alpha / (2 * lam ^ 2) + g * x₀ / lam)) := by
    field_simp
    ring
  rw [key]
  calc _ ≤ _ + _ := abs_add_le _ _
    _ ≤ |B| / 2 * (K₂ / t) + |b| * (K₁ / t) := by
        rw [abs_mul, abs_mul, abs_div B, abs_two]
        gcongr
    _ = _ := by ring

end CovK

/-! ### E2: the rotated oscillator with the isotropic localiser -/

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- The frame family of the localised measure: the `i`-th oscillator localised at `u₀ᵢ`. -/
noncomputable def locFamily (lam alpha gamma : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ) (t : ℝ) :
    Fin d → ℝ → ℝ :=
  fun i => locPotential1 (lam i) (alpha i) (gamma i) g (u₀ i) t

theorem separablePotential_locFamily (u₀ : Fin d → ℝ) (t : ℝ) :
    separablePotential (locFamily lam alpha gamma g u₀ t) =
      localisedPotential (separableAnharmonic lam alpha gamma) g u₀ t := by
  rw [separableAnharmonic, localisedPotential_separable]
  rfl

theorem localisedRotatedAnharmonic_eq_rotated_locFamily (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (t : ℝ) :
    localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t =
      rotated Q c (separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)) :=
  localisedRotatedAnharmonic_eq_rotated hQ c w₀ t

theorem continuous_separablePotential_locFamily (u₀ : Fin d → ℝ) (t : ℝ) :
    Continuous (separablePotential (locFamily lam alpha gamma g u₀ t)) := by
  rw [separablePotential_locFamily]
  exact continuous_localisedPotential (continuous_separableAnharmonic lam alpha gamma) g u₀ t

/-- Integrability on the frame localised measure is inherited from the unlocalised one. -/
theorem integrable_locFamily_of_integrable (hg : 0 ≤ g) (u₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    {ψ : (Fin d → ℝ) → ℝ} (hψc : Continuous ψ)
    (hψ : Integrable (fun u : Fin d → ℝ => ψ u *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u)))) :
    Integrable (fun u : Fin d → ℝ => ψ u *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) := by
  rw [separablePotential_locFamily]
  have hcont := continuous_localisedPotential (continuous_separableAnharmonic lam alpha gamma) g
    u₀ t
  exact integrable_localised_of_integrable (L := separableAnharmonic lam alpha gamma) (φ := ψ) hg
    u₀ ht (Continuous.aestronglyMeasurable (by fun_prop)) hψ

/-- The rotation step: the covariance on the localised rotated measure of the unlocalised energy
with a frame probe equals the covariance on the frame localised measure. -/
theorem localisedRotated_gibbsCov_eq (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (t : ℝ)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (rotated Q c ψ) =
      gibbsCov (separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)) t
        (separableAnharmonic lam alpha gamma) ψ := by
  rw [localisedRotatedAnharmonic_eq_rotated_locFamily hQ c w₀ t, rotatedAnharmonic]
  exact gibbsCov_rotated_of_continuous hQ c (continuous_separablePotential_locFamily _ t)
    (continuous_separableAnharmonic lam alpha gamma) hψ t

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

theorem partitionFunction_locFamily_ne (hg : 0 ≤ g) (u₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (m : Fin d) :
    _root_.Laplace.partitionFunction (locFamily lam alpha gamma g u₀ t m) t ≠ 0 :=
  (partitionFunction_localisedAnharmonic_pos (hlam m) (hgamma m) (hdisc m) hg ht).ne'

theorem integrable_energy_locFamily (hg : 0 ≤ g) (u₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (k : Fin d) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
  integrable_locFamily_of_integrable hg u₀ ht (by unfold anharmonicPotential; fun_prop)
    (integrable_coord_energy_separableAnharmonic hlam hgamma hdisc ht k)

theorem integrable_energy_pow_locFamily (hg : 0 ≤ g) (u₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (k i : Fin d) (m : ℕ) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      u i ^ m * Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
  integrable_locFamily_of_integrable hg u₀ ht (by unfold anharmonicPotential; fun_prop)
    (integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k i m)

theorem integrable_energy_mul_locFamily (hg : 0 ≤ g) (u₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (k i j : Fin d) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      (u i * u j) * Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) :=
  integrable_locFamily_of_integrable hg u₀ ht (by unfold anharmonicPotential; fun_prop)
    (integrable_energy_coord_mul_separableAnharmonic hlam hgamma hdisc ht k i j)

omit hlam hgamma hdisc in
theorem separableAnharmonic_eq_sum :
    separableAnharmonic lam alpha gamma =
      fun u => ∑ k, anharmonicPotential (lam k) (alpha k) (gamma k) (u k) := rfl

/-- `Cov_loc[L∘A, uᵢ^m] = Cov_loc,i[ℓᵢ, x^m]` on the localised rotated measure. -/
theorem localisedCovK_frame_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (i : Fin d) (m : ℕ) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ m) =
      _root_.Laplace.gibbsCov
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) (fun x => x ^ m) := by
  have e : (fun w => affineFrame Q c w i ^ m) = rotated Q c (fun u : Fin d → ℝ => u i ^ m) := rfl
  rw [e, localisedRotated_gibbsCov_eq hQ c w₀ t (by fun_prop), separableAnharmonic_eq_sum]
  exact gibbsCov_energy_coord_separable (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
    (fun k => anharmonicPotential (lam k) (alpha k) (gamma k))
    (partitionFunction_locFamily_ne hlam hgamma hdisc hg _ ht) i (fun x => x ^ m)
    (integrable_energy_locFamily hlam hgamma hdisc hg _ ht)
    (fun k => integrable_energy_pow_locFamily hlam hgamma hdisc hg _ ht k i m)

/-- `Cov_loc[L∘A, uᵢuⱼ] = ⟨x⟩_j Cov_loc,i[ℓᵢ, x] + ⟨x⟩_i Cov_loc,j[ℓⱼ, x]` for `i ≠ j`. -/
theorem localisedCovK_frame_pair (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) {i j : Fin d} (hij : i ≠ j) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => affineFrame Q c w i * affineFrame Q c w j) =
      _root_.Laplace.gibbsExpectation
          (locPotential1 (lam j) (alpha j) (gamma j) g (affineFrame Q c w₀ j) t) t (fun x => x) *
        _root_.Laplace.gibbsCov
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) (fun x => x) +
      _root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => x) *
        _root_.Laplace.gibbsCov
          (locPotential1 (lam j) (alpha j) (gamma j) g (affineFrame Q c w₀ j) t) t
          (anharmonicPotential (lam j) (alpha j) (gamma j)) (fun x => x) := by
  have e : (fun w => affineFrame Q c w i * affineFrame Q c w j) =
      rotated Q c (fun u : Fin d → ℝ => u i * u j) := rfl
  rw [e, localisedRotated_gibbsCov_eq hQ c w₀ t (by fun_prop), separableAnharmonic_eq_sum]
  exact gibbsCov_energy_pair_separable (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
    (fun k => anharmonicPotential (lam k) (alpha k) (gamma k))
    (partitionFunction_locFamily_ne hlam hgamma hdisc hg _ ht) hij
    (integrable_energy_locFamily hlam hgamma hdisc hg _ ht)
    (fun k => integrable_energy_mul_locFamily hlam hgamma hdisc hg _ ht k i j)

/-- `|t²Cov_loc[L∘A, uᵢ²] − 1/λᵢ| ≤ K/t`. -/
theorem localisedCovK_frame_sq_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (i : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
        1 / lam i| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedCovK_sq_rate (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedCovK_frame_coord hlam hgamma hdisc hQ c w₀ hg ht0 i 2]
  exact h ht

/-- `|t²Cov_loc[L∘A, uᵢ] − cᵢ| ≤ K/t`, `cᵢ = −αᵢ/(2λᵢ²) + g u₀ᵢ/λᵢ`. -/
theorem localisedCovK_frame_lin_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (i : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) -
        (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i)| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedCovK_lin_rate (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e := localisedCovK_frame_coord hlam hgamma hdisc hQ c w₀ hg ht0 i 1
  simp only [pow_one] at e
  rw [e]
  exact h ht

/-- `|t²Cov_loc[L∘A, uᵢuⱼ]| ≤ K/t` for `i ≠ j`: the off-diagonal pairs vanish at leading order on
the localised measure too. -/
theorem localisedCovK_frame_offdiag_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {i j : Fin d} (hij : i ≠ j) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w i * affineFrame Q c w j)| ≤ K / t := by
  obtain ⟨Ki, Ti, hKi, hTi, hi⟩ := locMean_loc_leading (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  obtain ⟨Kj, Tj, hKj, hTj, hj⟩ := locMean_loc_leading (hlam j) (hgamma j) (hdisc j) hg
    (x₀ := affineFrame Q c w₀ j)
  obtain ⟨Li, Si, hLi, hSi, gi⟩ := localisedCovK_lin_rate (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  obtain ⟨Lj, Sj, hLj, hSj, gj⟩ := localisedCovK_lin_rate (hlam j) (hgamma j) (hdisc j) hg
    (x₀ := affineFrame Q c w₀ j)
  set ci := -alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i with hci
  set cj := -alpha j / (2 * lam j ^ 2) + g * affineFrame Q c w₀ j / lam j with hcj
  refine ⟨(|cj| + Kj) * (|ci| + Li) + (|ci| + Ki) * (|cj| + Lj), Ti + Tj + Si + Sj,
    by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [localisedCovK_frame_pair hlam hgamma hdisc hQ c w₀ hg ht0 hij]
  set Mj := _root_.Laplace.gibbsExpectation
    (locPotential1 (lam j) (alpha j) (gamma j) g (affineFrame Q c w₀ j) t) t (fun x => x) with hMj
  set Mi := _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => x) with hMi
  set Ci := _root_.Laplace.gibbsCov
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
    (anharmonicPotential (lam i) (alpha i) (gamma i)) (fun x => x) with hCi
  set Cj := _root_.Laplace.gibbsCov
    (locPotential1 (lam j) (alpha j) (gamma j) g (affineFrame Q c w₀ j) t) t
    (anharmonicPotential (lam j) (alpha j) (gamma j)) (fun x => x) with hCj
  have bMj : |t * Mj| ≤ |cj| + Kj := Laplace.OneD.rate_bounded ht1 hKj (hj (t := t) (by linarith))
  have bMi : |t * Mi| ≤ |ci| + Ki := Laplace.OneD.rate_bounded ht1 hKi (hi (t := t) (by linarith))
  have bCi : |t ^ 2 * Ci| ≤ |ci| + Li :=
    Laplace.OneD.rate_bounded ht1 hLi (gi (t := t) (by linarith))
  have bCj : |t ^ 2 * Cj| ≤ |cj| + Lj :=
    Laplace.OneD.rate_bounded ht1 hLj (gj (t := t) (by linarith))
  have key : t ^ 2 * (Mj * Ci + Mi * Cj) =
      ((t * Mj) * (t ^ 2 * Ci) + (t * Mi) * (t ^ 2 * Cj)) / t := by
    field_simp
  rw [key, abs_div, abs_of_pos ht0, div_le_div_iff_of_pos_right ht0]
  calc |(t * Mj) * (t ^ 2 * Ci) + (t * Mi) * (t ^ 2 * Cj)|
      ≤ |t * Mj| * |t ^ 2 * Ci| + |t * Mi| * |t ^ 2 * Cj| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul (t * Mj), abs_mul (t * Mi)]
    _ ≤ (|cj| + Kj) * (|ci| + Li) + (|ci| + Ki) * (|cj| + Lj) := by gcongr

/-- The pair covariances at leading order, unified:
`|t²Cov_loc[L∘A, uᵢuⱼ] − (if i = j then 1/λᵢ else 0)| ≤ K/t`. -/
theorem localisedCovK_frame_pair_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (i j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w i * affineFrame Q c w j) -
        (if i = j then 1 / lam i else 0)| ≤ K / t := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨K, T, hK, hT, h⟩ := localisedCovK_frame_sq_rate hlam hgamma hdisc hQ c w₀ hg i
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    rw [if_pos rfl]
    have := h ht
    simpa only [sq] using this
  · obtain ⟨K, T, hK, hT, h⟩ := localisedCovK_frame_offdiag_rate hlam hgamma hdisc hQ c w₀ hg hij
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    rw [if_neg hij, sub_zero]
    exact h ht

/-- The quadratic frame probe splits into pairs and coordinates on the localised rotated measure. -/
theorem localisedCovK_quadratic_split (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
          ∑ i, b i * affineFrame Q c w i) =
      ∑ p : Fin d × Fin d, B p.1 p.2 / 2 *
        gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) +
      ∑ i, b i * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) := by
  set u₀ := affineFrame Q c w₀ with hu₀
  set L := separablePotential (locFamily lam alpha gamma g u₀ t) with hL
  set E := separableAnharmonic lam alpha gamma with hE
  have hψ : Continuous fun u : Fin d → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i :=
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop).add
      (continuous_finsetSum _ fun i _ => by fun_prop)
  have e : (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
      ∑ i, b i * affineFrame Q c w i) =
      rotated Q c (fun u : Fin d → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) := rfl
  have hp' : ∀ p : Fin d × Fin d,
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) =
      gibbsCov L t E (fun u => u p.1 * u p.2) := fun p =>
    localisedRotated_gibbsCov_eq hQ c w₀ t (ψ := fun u => u p.1 * u p.2) (by fun_prop)
  have hc' : ∀ i, gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) =
      gibbsCov L t E (fun u => u i) := fun i =>
    localisedRotated_gibbsCov_eq hQ c w₀ t (ψ := fun u => u i) (by fun_prop)
  rw [e, localisedRotated_gibbsCov_eq hQ c w₀ t hψ]
  simp only [hp', hc']
  -- integrability on the frame localised measure
  have hcm : ∀ i j, Integrable (fun u : Fin d → ℝ => u i * u j * Real.exp (-(t * L u))) :=
    fun i j => integrable_locFamily_of_integrable hg u₀ ht (by fun_prop)
      (integrable_coord_mul_separableAnharmonic hlam hgamma hdisc ht i j)
  have hc : ∀ i, Integrable (fun u : Fin d → ℝ => u i * Real.exp (-(t * L u))) :=
    fun i => integrable_locFamily_of_integrable hg u₀ ht (by fun_prop)
      (integrable_coord_separableAnharmonic hlam hgamma hdisc ht i)
  have hEsum : ∀ (ψ : (Fin d → ℝ) → ℝ), (∀ k, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * ψ u * Real.exp (-(t * L u)))) →
      Integrable (fun u : Fin d → ℝ => E u * ψ u * Real.exp (-(t * L u))) := fun ψ hψk => by
    refine (integrable_finsetSum Finset.univ fun k _ => hψk k).congr
      (Eventually.of_forall fun u => ?_)
    simp only [hE, separableAnharmonic, separablePotential, Finset.sum_mul]
  have hLcm : ∀ i j, Integrable (fun u : Fin d → ℝ =>
      E u * (u i * u j) * Real.exp (-(t * L u))) := fun i j =>
    hEsum _ fun k => integrable_energy_mul_locFamily hlam hgamma hdisc hg u₀ ht k i j
  have hLc : ∀ i, Integrable (fun u : Fin d → ℝ => E u * u i * Real.exp (-(t * L u))) := fun i =>
    hEsum (fun u => u i) fun k =>
      (integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 1).congr
        (Eventually.of_forall fun u => by simp only [pow_one, hL])
  have hφP : ∀ p : Fin d × Fin d, Integrable (fun u : Fin d → ℝ =>
      B p.1 p.2 / 2 * (u p.1 * u p.2) * Real.exp (-(t * L u))) := fun p =>
    ((hcm p.1 p.2).const_mul (B p.1 p.2 / 2)).congr (Eventually.of_forall fun u => by ring)
  have hφPL : ∀ p : Fin d × Fin d, Integrable (fun u : Fin d → ℝ =>
      B p.1 p.2 / 2 * (u p.1 * u p.2) * E u * Real.exp (-(t * L u))) := fun p =>
    ((hLcm p.1 p.2).const_mul (B p.1 p.2 / 2)).congr (Eventually.of_forall fun u => by ring)
  have hφQ : ∀ i, Integrable (fun u : Fin d → ℝ => b i * u i * Real.exp (-(t * L u))) := fun i =>
    ((hc i).const_mul (b i)).congr (Eventually.of_forall fun u => by ring)
  have hφQL : ∀ i, Integrable (fun u : Fin d → ℝ => b i * u i * E u * Real.exp (-(t * L u))) :=
    fun i => ((hLc i).const_mul (b i)).congr (Eventually.of_forall fun u => by ring)
  have hP : Integrable (fun u : Fin d → ℝ =>
      (∑ p : Fin d × Fin d, B p.1 p.2 / 2 * (u p.1 * u p.2)) * Real.exp (-(t * L u))) :=
    (integrable_finsetSum (Finset.univ : Finset (Fin d × Fin d)) fun p _ => hφP p).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hQ' : Integrable (fun u : Fin d → ℝ => (∑ i, b i * u i) * Real.exp (-(t * L u))) :=
    (integrable_finsetSum Finset.univ fun i _ => hφQ i).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hPL : Integrable (fun u : Fin d → ℝ =>
      (∑ p : Fin d × Fin d, B p.1 p.2 / 2 * (u p.1 * u p.2)) * E u * Real.exp (-(t * L u))) :=
    (integrable_finsetSum (Finset.univ : Finset (Fin d × Fin d)) fun p _ => hφPL p).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hQL : Integrable (fun u : Fin d → ℝ => (∑ i, b i * u i) * E u * Real.exp (-(t * L u))) :=
    (integrable_finsetSum Finset.univ fun i _ => hφQL i).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hprobe : (fun u : Fin d → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) =
      fun u => (∑ p : Fin d × Fin d, B p.1 p.2 / 2 * (u p.1 * u p.2)) + ∑ i, b i * u i := by
    funext u
    congr 1
    exact (Fintype.sum_prod_type' fun a c => B a c / 2 * (u a * u c)).symm
  rw [hprobe, gibbsCov_comm, gibbsCov_add_left_of_integrable L t _ _ _ hP hQ' hPL hQL,
    gibbsCov_finsetSum_left L t Finset.univ _ _ (fun p _ => hφP p) (fun p _ => hφPL p),
    gibbsCov_finsetSum_left L t Finset.univ _ _ (fun i _ => hφQ i) (fun i _ => hφQL i)]
  congr 1
  · exact Finset.sum_congr rfl fun p _ => by rw [gibbsCov_const_mul_left, gibbsCov_comm]
  · exact Finset.sum_congr rfl fun i _ => by rw [gibbsCov_const_mul_left, gibbsCov_comm]

/-- **eq:covK on E2's exact localised measure, frame probe**:
`|t²Cov_loc[L∘A, ∑ᵢⱼ (B̃ᵢⱼ/2)uᵢuⱼ + ∑ᵢ b̃ᵢuᵢ] − ∑ᵢ (B̃ᵢᵢ/(2λᵢ) + b̃ᵢcᵢ)| ≤ K/t`,
`cᵢ = −αᵢ/(2λᵢ²) + g u₀ᵢ/λᵢ`. -/
theorem localisedCovK_frame_quadratic_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
            ∑ i, b i * affineFrame Q c w i) -
        ∑ i, (B i i / (2 * lam i) +
          b i * (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i))| ≤ K / t := by
  obtain ⟨Kp, Tp, hKp, hTp, hp⟩ := sum_rate_div (fun p : Fin d × Fin d => B p.1 p.2 / 2)
    (fun p t => t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma)
      (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) -
      (if p.1 = p.2 then 1 / lam p.1 else 0))
    (fun p => localisedCovK_frame_pair_rate hlam hgamma hdisc hQ c w₀ hg p.1 p.2)
  obtain ⟨Kl, Tl, hKl, hTl, hl⟩ := sum_rate_div (fun i => b i)
    (fun i t => t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) -
      (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i))
    (fun i => localisedCovK_frame_lin_rate hlam hgamma hdisc hQ c w₀ hg i)
  refine ⟨Kp + Kl, Tp + Tl, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hdiag : ∑ p : Fin d × Fin d, B p.1 p.2 / 2 * (if p.1 = p.2 then 1 / lam p.1 else 0) =
      ∑ i, B i i / (2 * lam i) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
          ∑ i, b i * affineFrame Q c w i) -
      ∑ i, (B i i / (2 * lam i) +
        b i * (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i)) =
      (∑ p : Fin d × Fin d, B p.1 p.2 / 2 *
        (t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) -
          (if p.1 = p.2 then 1 / lam p.1 else 0))) +
      ∑ i, b i * (t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) -
        (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i)) := by
    rw [localisedCovK_quadratic_split hlam hgamma hdisc hQ c w₀ hg ht0 B b]
    simp only [mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hdiag]
    have e1 : ∀ p : Fin d × Fin d, B p.1 p.2 / 2 *
        (t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2)) =
        t ^ 2 * (B p.1 p.2 / 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2)) := fun p => by ring
    have e2 : ∀ i, b i * (t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t)
        t (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)) =
        t ^ 2 * (b i * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)) :=
      fun i => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    ring
  rw [key]
  calc _ ≤ _ + _ := abs_add_le _ _
    _ ≤ Kp / t + Kl / t := add_le_add (hp (t := t) (by linarith)) (hl (t := t) (by linarith))
    _ = _ := by ring

/-- **eq:covK on E2's exact localised measure, ambient probe**: for
`ψ(w) = ½(w − c)ᵀB(w − c) + bᵀ(w − c)`,
`|t²Cov_loc[L∘A, ψ] − ∑ᵢ ((QᵀBQ)ᵢᵢ/(2λᵢ) + (Qᵀb)ᵢ cᵢ)| ≤ K/t`,
`cᵢ = −αᵢ/(2λᵢ²) + g (Qᵀ(w₀ − c))ᵢ/λᵢ`:
the unlocalised leading constant plus the anchor term `bᵀ g H⁻¹(w₀ − c)`, the `−∂ₜ` of the anchor
displacement of the localised eq:mean; for centred localisation (`w₀ = c`) the localiser does not
enter at leading order. -/
theorem localisedRotatedAnharmonic_covK_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) -
        ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) +
          (Qᵀ *ᵥ b) i * (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i))| ≤
        K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedCovK_frame_quadratic_rate hlam hgamma hdisc hQ c w₀ hg
    (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have hprobe : (fun w : Fin d → ℝ => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      fun w => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
        ∑ i, (Qᵀ *ᵥ b) i * affineFrame Q c w i :=
    funext (probe_affineFrame hQ c B b)
  rw [hprobe]
  exact h ht

end Multi

end Laplace.Multi
