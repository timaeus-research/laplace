/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.MomentsAllOrders
import Laplace.OneD.AnharmonicKappa3
import Laplace.Multi.SeparableExact

/-!
# E2's fourth prediction: `Cov[K, ψ]` for the exact anharmonic measure

The note's eq:covK,
`Cov[K, ψ] = ½ tr(HSBS) + ½ (Sb)ᵀ(T:S) − (t/2) bᵀSHS(T:S) − (t/2)(Sb)ᵀ(T:(SHS))` for a quadratic
probe `ψ = ½ wᵀBw + bᵀw`, is "the primer's canonical experiment". For the one-dimensional anharmonic
oscillator `ℓ = λx²/2 + αx³/6 + γx⁴/24` we compute the exact `Cov_t[ℓ, ψ]` to leading order from the
all-orders moment asymptotics and identify it with the four terms of the formula:

* `cov_sq_sq_asymptotic`, `cov_cube_sq_asymptotic`, `cov_fourth_sq_asymptotic`,
  `cov_cube_id_asymptotic`, `cov_fourth_id_asymptotic` (with the seabed's
  `cov_anharmonic_asymptotic`):
  the six pair covariances `t² Cov[xᵐ, xⁿ]`;
* `gibbsCov_anharmonic_left`: `Cov[ℓ, ψ] = (λ/2)Cov[x², ψ] + (α/6)Cov[x³, ψ] + (γ/24)Cov[x⁴, ψ]`;
* `covK_anharmonic_sq` (`t² Cov[ℓ, x²] → 1/λ`), `covK_anharmonic_lin`
  (`t² Cov[ℓ, x] → −α/(2λ²)`), `covK_anharmonic` (`t² Cov[ℓ, (B/2)x² + bx] → B/(2λ) − bα/(2λ²)`);
* `covKOneDim`, `covKOneDim_eq`: the four terms of eq:covK in one dimension sum to
  `(B/(2λ) − bα/(2λ²))/t²`; `covK_anharmonic_agree` (`t²(Cov − covK(t)) → 0`) and
  `covK_anharmonic_ratio` (`Cov/covK(t) → 1` when the constant is nonzero).

The formula is the exact leading term; the remainder is `o(t⁻²)` (a rate would need the moment
rates, not just the limits).
-/

open MeasureTheory Filter Topology

namespace Laplace.OneD

variable {lam alpha gamma : ℝ}

/-! ### Limits of moments and their products -/

section Limits

/-- If `tⁿ f(t)` converges (`n ≥ 1`) then `f(t) → 0`. -/
theorem tendsto_zero_of_tendsto_pow_mul {f : ℝ → ℝ} {c : ℝ} {n : ℕ} (hn : n ≠ 0)
    (h : Tendsto (fun t : ℝ => t ^ n * f t) atTop (𝓝 c)) : Tendsto f atTop (𝓝 0) := by
  have hinv : Tendsto (fun t : ℝ => (t ^ n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop hn)
  have := hinv.mul h
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have := (pow_pos ht n).ne'
  field_simp

theorem gibbsCov_pow_pow (L : ℝ → ℝ) (t : ℝ) (m n : ℕ) :
    Laplace.gibbsCov L t (fun x => x ^ m) (fun x => x ^ n) =
      Laplace.gibbsExpectation L t (fun x => x ^ (m + n)) -
        Laplace.gibbsExpectation L t (fun x => x ^ m) *
          Laplace.gibbsExpectation L t (fun x => x ^ n) := by
  have : (fun x : ℝ => x ^ m * x ^ n) = fun x => x ^ (m + n) := by
    funext x
    rw [pow_add]
  unfold Laplace.gibbsCov
  rw [this]

theorem gibbsCov_pow_id (L : ℝ → ℝ) (t : ℝ) (m : ℕ) :
    Laplace.gibbsCov L t (fun x => x ^ m) (fun x => x) =
      Laplace.gibbsExpectation L t (fun x => x ^ (m + 1)) -
        Laplace.gibbsExpectation L t (fun x => x ^ m) *
          Laplace.gibbsExpectation L t (fun x => x) := by
  have : (fun x : ℝ => x ^ m * x) = fun x => x ^ (m + 1) := by
    funext x
    rw [pow_succ]
  unfold Laplace.gibbsCov
  rw [this]

variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

theorem firstMoment_tendsto_zero :
    Tendsto (fun t : ℝ => Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x)) atTop (𝓝 0) :=
  tendsto_zero_of_tendsto_pow_mul one_ne_zero (by
    simpa only [pow_one] using mean_anharmonic_asymptotic hlam hgamma hdisc)

theorem secondMoment_tendsto_zero :
    Tendsto (fun t : ℝ => Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 2)) atTop (𝓝 0) :=
  tendsto_zero_of_tendsto_pow_mul one_ne_zero (by
    simpa only [pow_one] using secondMoment_anharmonic_asymptotic hlam hgamma hdisc)

/-- `t² Cov[x², x²] → 2/λ²`. -/
theorem cov_sq_sq_asymptotic :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 2) (fun x => x ^ 2)) atTop (𝓝 (2 / lam ^ 2)) := by
  have h := (Laplace.Multi.fourthMoment_anharmonic_asymptotic hlam hgamma hdisc).sub
    ((secondMoment_anharmonic_asymptotic hlam hgamma hdisc).pow 2)
  have hne := hlam.ne'
  have hlim : 3 / lam ^ 2 - (1 / lam) ^ 2 = 2 / lam ^ 2 := by
    field_simp
    ring
  rw [hlim] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [gibbsCov_pow_pow, show (2 + 2 : ℕ) = 4 from rfl]
  ring

/-- `t² Cov[x³, x²] → 0`. -/
theorem cov_cube_sq_asymptotic :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 3) (fun x => x ^ 2)) atTop (𝓝 0) := by
  have h := (fifthMoment_t_sq_tendsto_zero hlam hgamma hdisc).sub
    ((thirdMoment_anharmonic_asymptotic hlam hgamma hdisc).mul
      (secondMoment_tendsto_zero hlam hgamma hdisc))
  rw [mul_zero, sub_zero] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [gibbsCov_pow_pow, show (3 + 2 : ℕ) = 5 from rfl]
  ring

/-- `t² Cov[x⁴, x²] → 0`. -/
theorem cov_fourth_sq_asymptotic :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 4) (fun x => x ^ 2)) atTop (𝓝 0) := by
  have h := (sixthMoment_t_sq_tendsto_zero hlam hgamma hdisc).sub
    ((Laplace.Multi.fourthMoment_anharmonic_asymptotic hlam hgamma hdisc).mul
      (secondMoment_tendsto_zero hlam hgamma hdisc))
  rw [mul_zero, sub_zero] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [gibbsCov_pow_pow, show (4 + 2 : ℕ) = 6 from rfl]
  ring

/-- `t² Cov[x³, x] → 3/λ²`. -/
theorem cov_cube_id_asymptotic :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 3) (fun x => x)) atTop (𝓝 (3 / lam ^ 2)) := by
  have h := (Laplace.Multi.fourthMoment_anharmonic_asymptotic hlam hgamma hdisc).sub
    ((thirdMoment_anharmonic_asymptotic hlam hgamma hdisc).mul
      (firstMoment_tendsto_zero hlam hgamma hdisc))
  rw [mul_zero, sub_zero] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [gibbsCov_pow_id, show (3 + 1 : ℕ) = 4 from rfl]
  ring

/-- `t² Cov[x⁴, x] → 0`. -/
theorem cov_fourth_id_asymptotic :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 4) (fun x => x)) atTop (𝓝 0) := by
  have h := (fifthMoment_t_sq_tendsto_zero hlam hgamma hdisc).sub
    ((Laplace.Multi.fourthMoment_anharmonic_asymptotic hlam hgamma hdisc).mul
      (firstMoment_tendsto_zero hlam hgamma hdisc))
  rw [mul_zero, sub_zero] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [gibbsCov_pow_id, show (4 + 1 : ℕ) = 5 from rfl]
  ring

end Limits

/-! ### Bilinearity in the energy slot -/

section Bilinear

variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `Cov[ℓ, ψ] = (λ/2)Cov[x², ψ] + (α/6)Cov[x³, ψ] + (γ/24)Cov[x⁴, ψ]`, given integrability of
`x^k ψ e^{−tℓ}` for `k = 2, 3, 4`. -/
theorem gibbsCov_anharmonic_left {t : ℝ} (ht : 0 < t) (ψ : ℝ → ℝ)
    (hψ2 : Integrable (fun x => x ^ 2 * ψ x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
    (hψ3 : Integrable (fun x => x ^ 3 * ψ x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
    (hψ4 : Integrable (fun x => x ^ 4 * ψ x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) :
    Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) ψ =
      lam / 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2) ψ +
        alpha / 6 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3) ψ +
        gamma / 24 *
          Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4) ψ := by
  set L := anharmonicPotential lam alpha gamma with hL
  have h2 := Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic 2 hlam hgamma hdisc ht
  have h3 := Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic 3 hlam hgamma hdisc ht
  have h4 := Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic 4 hlam hgamma hdisc ht
  have e1 : (fun x => L x) =
      fun x => (lam / 2 * x ^ 2 + alpha / 6 * x ^ 3) + gamma / 24 * x ^ 4 := by
    funext x
    simp only [hL, anharmonicPotential]
  have i1 : Integrable (fun x => (lam / 2 * x ^ 2 + alpha / 6 * x ^ 3) * Real.exp (-(t * L x))) :=
    ((h2.const_mul (lam / 2)).add (h3.const_mul (alpha / 6))).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have i2 : Integrable (fun x => gamma / 24 * x ^ 4 * Real.exp (-(t * L x))) :=
    (h4.const_mul (gamma / 24)).congr (Eventually.of_forall fun x => by ring)
  have i1ψ : Integrable (fun x => (lam / 2 * x ^ 2 + alpha / 6 * x ^ 3) * ψ x *
      Real.exp (-(t * L x))) :=
    ((hψ2.const_mul (lam / 2)).add (hψ3.const_mul (alpha / 6))).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have i2ψ : Integrable (fun x => gamma / 24 * x ^ 4 * ψ x * Real.exp (-(t * L x))) :=
    (hψ4.const_mul (gamma / 24)).congr (Eventually.of_forall fun x => by ring)
  have j1 : Integrable (fun x => lam / 2 * x ^ 2 * Real.exp (-(t * L x))) :=
    (h2.const_mul (lam / 2)).congr (Eventually.of_forall fun x => by ring)
  have j2 : Integrable (fun x => alpha / 6 * x ^ 3 * Real.exp (-(t * L x))) :=
    (h3.const_mul (alpha / 6)).congr (Eventually.of_forall fun x => by ring)
  have j1ψ : Integrable (fun x => lam / 2 * x ^ 2 * ψ x * Real.exp (-(t * L x))) :=
    (hψ2.const_mul (lam / 2)).congr (Eventually.of_forall fun x => by ring)
  have j2ψ : Integrable (fun x => alpha / 6 * x ^ 3 * ψ x * Real.exp (-(t * L x))) :=
    (hψ3.const_mul (alpha / 6)).congr (Eventually.of_forall fun x => by ring)
  calc Laplace.gibbsCov L t L ψ
      = Laplace.gibbsCov L t
          (fun x => (lam / 2 * x ^ 2 + alpha / 6 * x ^ 3) + gamma / 24 * x ^ 4) ψ := by
        rw [← e1]
    _ = _ := by
        rw [Laplace.gibbsCov_add_left L t _ _ ψ i1 i2 i1ψ i2ψ,
          Laplace.gibbsCov_add_left L t _ _ ψ j1 j2 j1ψ j2ψ, Laplace.gibbsCov_smul_left,
          Laplace.gibbsCov_smul_left, Laplace.gibbsCov_smul_left]

/-- **`t² Cov[ℓ, x²] → 1/λ`**: eq:covK's `½ tr(HSBS)` with `B = 2`. -/
theorem covK_anharmonic_sq :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (anharmonicPotential lam alpha gamma) (fun x => x ^ 2)) atTop (𝓝 (1 / lam)) := by
  have h := (((cov_sq_sq_asymptotic hlam hgamma hdisc).const_mul (lam / 2)).add
    ((cov_cube_sq_asymptotic hlam hgamma hdisc).const_mul (alpha / 6))).add
    ((cov_fourth_sq_asymptotic hlam hgamma hdisc).const_mul (gamma / 24))
  have hne := hlam.ne'
  have hlim : lam / 2 * (2 / lam ^ 2) + alpha / 6 * 0 + gamma / 24 * 0 = 1 / lam := by
    field_simp
    ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hk : ∀ k : ℕ, Integrable (fun x => x ^ k * x ^ 2 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := fun k =>
    (Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic (k + 2) hlam hgamma hdisc ht).congr
      (Eventually.of_forall fun x => by simp only [pow_add])
  rw [gibbsCov_anharmonic_left hlam hgamma hdisc ht _ (hk 2) (hk 3) (hk 4)]
  ring

/-- **`t² Cov[ℓ, x] → −α/(2λ²)`**: eq:covK's three `b`-terms. -/
theorem covK_anharmonic_lin :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (anharmonicPotential lam alpha gamma) (fun x => x)) atTop (𝓝 (-alpha / (2 * lam ^ 2))) := by
  have h := (((cov_anharmonic_asymptotic hlam hgamma hdisc).const_mul (lam / 2)).add
    ((cov_cube_id_asymptotic hlam hgamma hdisc).const_mul (alpha / 6))).add
    ((cov_fourth_id_asymptotic hlam hgamma hdisc).const_mul (gamma / 24))
  have hne := hlam.ne'
  have hlim : lam / 2 * (-2 * alpha / lam ^ 3) + alpha / 6 * (3 / lam ^ 2) + gamma / 24 * 0 =
      -alpha / (2 * lam ^ 2) := by
    field_simp
    ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hk : ∀ k : ℕ, Integrable (fun x => x ^ k * x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := fun k =>
    (Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic (k + 1) hlam hgamma hdisc ht).congr
      (Eventually.of_forall fun x => by simp only [pow_succ])
  rw [gibbsCov_anharmonic_left hlam hgamma hdisc ht _ (hk 2) (hk 3) (hk 4)]
  ring

/-- **eq:covK for the exact anharmonic measure**: for the probe `ψ = (B/2)x² + bx`,
`t² Cov[ℓ, ψ] → B/(2λ) − bα/(2λ²)`. -/
theorem covK_anharmonic (B b : ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x)) atTop
      (𝓝 (B / (2 * lam) - b * alpha / (2 * lam ^ 2))) := by
  have h := ((covK_anharmonic_sq hlam hgamma hdisc).const_mul (B / 2)).add
    ((covK_anharmonic_lin hlam hgamma hdisc).const_mul b)
  have hne := hlam.ne'
  have hlim : B / 2 * (1 / lam) + b * (-alpha / (2 * lam ^ 2)) =
      B / (2 * lam) - b * alpha / (2 * lam ^ 2) := by
    field_simp
    ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  set L := anharmonicPotential lam alpha gamma with hL
  have hm : ∀ k : ℕ, Integrable (fun x => x ^ k * Real.exp (-(t * L x))) := fun k =>
    Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic k hlam hgamma hdisc ht
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
  ring

end Bilinear

/-! ### The four terms of eq:covK in one dimension -/

section Formula

/-- The note's eq:covK evaluated in one dimension: `H = λ`, `S = 1/(λt)`, `T = α`, probe
`ψ = (B/2)x² + bx`; the four terms `½ tr(HSBS)`, `½(Sb)(T:S)`, `−(t/2) b·S·H·S·(T:S)`,
`−(t/2)(Sb)(T:(SHS))`. -/
noncomputable def covKOneDim (lam alpha t B b : ℝ) : ℝ :=
  1 / 2 * (lam * (1 / (lam * t)) * B * (1 / (lam * t))) +
    1 / 2 * ((1 / (lam * t)) * b) * (alpha * (1 / (lam * t))) -
    t / 2 * (b * (1 / (lam * t)) * lam * (1 / (lam * t)) * (alpha * (1 / (lam * t)))) -
    t / 2 * ((1 / (lam * t)) * b) * (alpha * ((1 / (lam * t)) * lam * (1 / (lam * t))))

/-- The four terms sum to `(B/(2λ) − bα/(2λ²))/t²`. -/
theorem covKOneDim_eq {lam t : ℝ} (hlam : lam ≠ 0) (ht : t ≠ 0) (alpha B b : ℝ) :
    covKOneDim lam alpha t B b = (B / (2 * lam) - b * alpha / (2 * lam ^ 2)) / t ^ 2 := by
  unfold covKOneDim
  field_simp
  ring

variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- **The exact covariance agrees with eq:covK to leading order**: `t²(Cov[ℓ, ψ] − covK(t)) → 0`. -/
theorem covK_anharmonic_agree (B b : ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * (Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) -
        covKOneDim lam alpha t B b)) atTop (𝓝 0) := by
  have h := (covK_anharmonic hlam hgamma hdisc B b).sub_const
    (B / (2 * lam) - b * alpha / (2 * lam ^ 2))
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [covKOneDim_eq hlam.ne' ht.ne']
  have := ht.ne'
  field_simp

/-- **Relative agreement**: when `B/(2λ) − bα/(2λ²) ≠ 0`, `Cov[ℓ, ψ]/covK(t) → 1`. -/
theorem covK_anharmonic_ratio (B b : ℝ) (hc : B / (2 * lam) - b * alpha / (2 * lam ^ 2) ≠ 0) :
    Tendsto (fun t : ℝ => Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) /
        covKOneDim lam alpha t B b) atTop (𝓝 1) := by
  have h := (covK_anharmonic hlam hgamma hdisc B b).div_const
    (B / (2 * lam) - b * alpha / (2 * lam ^ 2))
  rw [div_self hc] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [covKOneDim_eq hlam.ne' ht.ne']
  have := ht.ne'
  field_simp

end Formula

end Laplace.OneD
