/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovKDerivativeMulti
import Laplace.Multi.GibbsIBP
import Laplace.Multi.LocalisedCovK

/-!
# The exact identities on the localised measure

Two exact identities for E3's localised Gibbs measure `∝ e^{−tL}·Φ`, `Φ = e^{−(g/2)|w − w₀|²}`
(`t`-independent):

* the derivative reading of the localised eq:covK, `d/dt ⟨ψ⟩_loc = −Cov_loc[L, ψ]` (the
  covariance of the *unlocalised* energy with the probe on the localised measure), from the ratio
  `⟨ψ⟩_loc(s) = ⟨ψΦ⟩_s/⟨Φ⟩_s` of fixed-potential expectations and the seabed's derivative lemma —
  the exact-measure counterpart of `CovKDerivativeLoc`;
* the localised Stein identity in one dimension, `⟨f'⟩_loc = ⟨f·(tℓ' + gx − a)⟩_loc`, and its moment
  recursion `(tλ + g)m_{k+1} + (tα/2)m_{k+2} + (tγ/6)m_{k+3} = k m_{k−1} + a m_k`.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

/-! ### The localiser weight and the ratio representation -/

section Ratio

variable {ι : Type*} [Fintype ι]

/-- `Φ(w) = e^{−(g/2)|w − w₀|²}`. -/
noncomputable def localiserWeight (g : ℝ) (w₀ : ι → ℝ) (w : ι → ℝ) : ℝ :=
  Real.exp (-(g / 2 * ∑ j, (w j - w₀ j) ^ 2))

theorem localiserWeight_pos (g : ℝ) (w₀ w : ι → ℝ) : 0 < localiserWeight g w₀ w := Real.exp_pos _

theorem localiserWeight_le_one {g : ℝ} (hg : 0 ≤ g) (w₀ w : ι → ℝ) : localiserWeight g w₀ w ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (div_nonneg hg (by norm_num))
    (Finset.sum_nonneg fun j _ => sq_nonneg _)))

theorem continuous_localiserWeight (g : ℝ) (w₀ : ι → ℝ) : Continuous (localiserWeight g w₀) := by
  unfold localiserWeight
  fun_prop

theorem exp_neg_localisedPotential_eq (L : (ι → ℝ) → ℝ) (g : ℝ) (w₀ : ι → ℝ) {t : ℝ} (ht : t ≠ 0)
    (w : ι → ℝ) :
    Real.exp (-(t * localisedPotential L g w₀ t w)) =
      Real.exp (-(t * L w)) * localiserWeight g w₀ w := by
  rw [exp_neg_localisedPotential L g w₀ ht w, localiserWeight, ← Real.exp_add, sub_eq_add_neg]

/-- Bounded-weight integrability: `ψ e^{−tL}` integrable gives `ψΦ e^{−tL}` integrable. -/
theorem integrable_mul_localiserWeight {L ψ : (ι → ℝ) → ℝ} {g : ℝ} (hg : 0 ≤ g) (w₀ : ι → ℝ)
    (t : ℝ) (hψ : Integrable (fun w => ψ w * Real.exp (-(t * L w)))) :
    Integrable (fun w => ψ w * localiserWeight g w₀ w * Real.exp (-(t * L w))) := by
  have h := hψ.bdd_mul (c := 1) (continuous_localiserWeight g w₀).aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_pos (localiserWeight_pos g w₀ w)]
      exact localiserWeight_le_one hg w₀ w)
  refine h.congr (Eventually.of_forall fun w => ?_)
  change localiserWeight g w₀ w * (ψ w * _) = _
  ring

/-- **The ratio representation**: `⟨ψ⟩_loc = ⟨ψΦ⟩/⟨Φ⟩`, for `t ≠ 0` with `⟨Φ⟩ ≠ 0` and `Z ≠ 0`. -/
theorem gibbsExpectation_localisedPotential_eq_ratio (L : (ι → ℝ) → ℝ) (g : ℝ) (w₀ : ι → ℝ)
    {t : ℝ} (ht : t ≠ 0) (ψ : (ι → ℝ) → ℝ) (hZ0 : partitionFunction L t ≠ 0) :
    gibbsExpectation (localisedPotential L g w₀ t) t ψ =
      gibbsExpectation L t (fun w => ψ w * localiserWeight g w₀ w) /
        gibbsExpectation L t (localiserWeight g w₀) := by
  unfold gibbsExpectation
  rw [div_div_div_cancel_right₀ hZ0]
  congr 1
  · exact integral_congr_ae (Eventually.of_forall fun w => by
      beta_reduce
      rw [exp_neg_localisedPotential_eq L g w₀ ht w]
      ring)
  · unfold partitionFunction
    exact integral_congr_ae (Eventually.of_forall fun w => by
      beta_reduce
      rw [exp_neg_localisedPotential_eq L g w₀ ht w]
      ring)

end Ratio

/-! ### The derivative identity on the separable frame -/

section Frame

variable {ι : Type*} [Fintype ι] {lam alpha gamma : ι → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

theorem gibbsExpectation_localiserWeight_pos (hg : 0 ≤ g) (u₀ : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    0 < gibbsExpectation (separableAnharmonic lam alpha gamma) t (localiserWeight g u₀) := by
  have hZ := partitionFunction_separableAnharmonic_pos hlam hgamma hdisc ht
  have hloc : 0 < partitionFunction
      (localisedPotential (separableAnharmonic lam alpha gamma) g u₀ t) t := by
    unfold partitionFunction
    refine integral_exp_pos ?_
    have := integrable_localised_of_integrable (L := separableAnharmonic lam alpha gamma)
      (φ := fun _ => (1 : ℝ)) hg u₀ ht (Continuous.aestronglyMeasurable (by
        have := continuous_localisedPotential (continuous_separableAnharmonic lam alpha gamma) g
          u₀ t
        fun_prop)) (by simpa using integrable_exp_neg_separableAnharmonic' hlam hgamma hdisc ht)
    simpa using this
  have e : (∫ w, localiserWeight g u₀ w * Real.exp (-(t * separableAnharmonic lam alpha gamma w)))
      = partitionFunction (localisedPotential (separableAnharmonic lam alpha gamma) g u₀ t) t := by
    unfold partitionFunction
    exact integral_congr_ae (Eventually.of_forall fun w => by
      beta_reduce
      rw [exp_neg_localisedPotential_eq (separableAnharmonic lam alpha gamma) g u₀ ht.ne' w]
      ring)
  unfold gibbsExpectation
  rw [e]
  exact div_pos hloc hZ

/-- `⟨ψ⟩_loc(s) = ⟨ψΦ⟩_s/⟨Φ⟩_s` on the separable frame. -/
theorem localised_separable_eq_ratio (u₀ : ι → ℝ) {s : ℝ} (hs : 0 < s)
    (ψ : (ι → ℝ) → ℝ) :
    gibbsExpectation (localisedPotential (separableAnharmonic lam alpha gamma) g u₀ s) s ψ =
      gibbsExpectation (separableAnharmonic lam alpha gamma) s
          (fun u => ψ u * localiserWeight g u₀ u) /
        gibbsExpectation (separableAnharmonic lam alpha gamma) s (localiserWeight g u₀) :=
  gibbsExpectation_localisedPotential_eq_ratio _ g u₀ hs.ne' ψ
    (partitionFunction_separableAnharmonic_pos hlam hgamma hdisc hs).ne'

/-- **The derivative identity on the localised measure (frame)**: for a continuous probe `ψ` with
`Lψe^{−(t/2)L}` and `ψe^{−(t/2)L}` integrable, `d/ds ⟨ψ⟩_loc(s) = −Cov_loc,t[L, ψ]` at `t > 0`. -/
theorem hasDerivAt_localised_separable (hg : 0 ≤ g) (u₀ : ι → ℝ) {t : ℝ} (ht : 0 < t)
    {ψ : (ι → ℝ) → ℝ} (hψ : Continuous ψ)
    (hint : Integrable (fun u => separableAnharmonic lam alpha gamma u * ψ u *
      Real.exp (-(t / 2 * separableAnharmonic lam alpha gamma u))))
    (hint0 : Integrable (fun u => ψ u *
      Real.exp (-(t / 2 * separableAnharmonic lam alpha gamma u)))) :
    HasDerivAt (fun s => gibbsExpectation
        (localisedPotential (separableAnharmonic lam alpha gamma) g u₀ s) s ψ)
      (-gibbsCov (localisedPotential (separableAnharmonic lam alpha gamma) g u₀ t) t
        (separableAnharmonic lam alpha gamma) ψ) t := by
  have ht2 := half_pos ht
  have hLc : Continuous (separableAnharmonic lam alpha gamma) :=
    continuous_separableAnharmonic lam alpha gamma
  have hL0 : ∀ u, 0 ≤ separableAnharmonic lam alpha gamma u :=
    separableAnharmonic_nonneg hgamma hdisc
  have hΦc : Continuous (localiserWeight g u₀) := continuous_localiserWeight g u₀
  have hZ := (partitionFunction_separableAnharmonic_pos hlam hgamma hdisc ht).ne'
  have hLe := integrable_energy_separableAnharmonic hlam hgamma hdisc ht2
  have he := integrable_exp_neg_separableAnharmonic' hlam hgamma hdisc ht2
  -- the numerator ⟨ψΦ⟩_s
  have hN : HasDerivAt (fun s => gibbsExpectation (separableAnharmonic lam alpha gamma) s
      (fun u => ψ u * localiserWeight g u₀ u))
      (-gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => ψ u * localiserWeight g u₀ u)) t := by
    refine hasDerivAt_gibbsExpectation_of_integrable (ψ := fun u => ψ u * localiserWeight g u₀ u)
      hLc hL0 (hψ.mul hΦc) ht ?_ ?_ hLe he hZ
    · have := integrable_mul_localiserWeight (L := separableAnharmonic lam alpha gamma)
        (ψ := fun u => separableAnharmonic lam alpha gamma u * ψ u) hg u₀ (t / 2) hint
      refine this.congr (Eventually.of_forall fun u => ?_)
      beta_reduce
      ring
    · exact integrable_mul_localiserWeight (L := separableAnharmonic lam alpha gamma) hg u₀ (t / 2)
        hint0
  -- the denominator ⟨Φ⟩_s
  have hD : HasDerivAt (fun s => gibbsExpectation (separableAnharmonic lam alpha gamma) s
      (localiserWeight g u₀))
      (-gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (localiserWeight g u₀)) t := by
    refine hasDerivAt_gibbsExpectation_of_integrable hLc hL0 hΦc ht ?_ ?_ hLe he hZ
    · have := integrable_mul_localiserWeight (L := separableAnharmonic lam alpha gamma)
        (ψ := fun u => separableAnharmonic lam alpha gamma u) hg u₀ (t / 2) hLe
      refine this.congr (Eventually.of_forall fun u => ?_)
      beta_reduce
      ring
    · have := integrable_mul_localiserWeight (L := separableAnharmonic lam alpha gamma)
        (ψ := fun _ => (1 : ℝ)) hg u₀ (t / 2) (by simpa using he)
      simpa using this
  have hDne : gibbsExpectation (separableAnharmonic lam alpha gamma) t (localiserWeight g u₀) ≠ 0 :=
    (gibbsExpectation_localiserWeight_pos hlam hgamma hdisc hg u₀ ht).ne'
  have hdiv := hN.div hD hDne
  have heq : (fun s => gibbsExpectation
      (localisedPotential (separableAnharmonic lam alpha gamma) g u₀ s) s ψ) =ᶠ[𝓝 t]
      fun s => gibbsExpectation (separableAnharmonic lam alpha gamma) s
        (fun u => ψ u * localiserWeight g u₀ u) /
        gibbsExpectation (separableAnharmonic lam alpha gamma) s (localiserWeight g u₀) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs =>
      localised_separable_eq_ratio hlam hgamma hdisc u₀ hs ψ
  refine (hdiv.congr_of_eventuallyEq heq).congr_deriv ?_
  -- the algebra of the quotient rule
  have hr := localised_separable_eq_ratio (g := g) hlam hgamma hdisc u₀ ht
  unfold gibbsCov
  rw [hr (fun u => separableAnharmonic lam alpha gamma u * ψ u),
    hr (separableAnharmonic lam alpha gamma), hr ψ]
  have e : (fun u => separableAnharmonic lam alpha gamma u * (ψ u * localiserWeight g u₀ u)) =
      fun u => separableAnharmonic lam alpha gamma u * ψ u * localiserWeight g u₀ u := by
    funext u
    ring
  rw [e]
  field_simp
  ring

end Frame

/-! ### E2: the rotated oscillator -/

section Rotated

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

omit hlam hgamma hdisc in
theorem localisedRotatedAnharmonic_eq_rotated_localised (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (s : ℝ) :
    localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s =
      rotated Q c
        (localisedPotential (separableAnharmonic lam alpha gamma) g (affineFrame Q c w₀) s) := by
  rw [rotated_localisedPotential hQ]
  rfl

/-- The frame quadratic probe's integrability inputs for the derivative lemma. -/
theorem integrable_energy_quadratic_separableAnharmonic {t : ℝ} (ht : 0 < t)
    (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) :
    Integrable (fun u : Fin d → ℝ => separableAnharmonic lam alpha gamma u *
      (∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  refine integrable_energy_mul_separableAnharmonic _ fun k => ?_
  have hpair : ∀ i j, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * (B i j / 2 * (u i * u j)) *
        Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := fun i j =>
    ((integrable_energy_coord_mul_separableAnharmonic hlam hgamma hdisc ht k i j).const_mul
      (B i j / 2)).congr (Eventually.of_forall fun u => by simp only; ring)
  have hlin : ∀ i, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * (b i * u i) *
        Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := fun i =>
    ((integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k i 1).const_mul
      (b i)).congr (Eventually.of_forall fun u => by simp only [pow_one]; ring)
  have h1 : Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * (∑ i, ∑ j, B i j / 2 * (u i * u j)) *
        Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin d)) fun j _ => hpair i j
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul]
  have h2 : Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * (∑ i, b i * u i) *
        Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hlin i
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul]
  refine (h1.add h2).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply]
  ring

theorem integrable_quadratic_separableAnharmonic {t : ℝ} (ht : 0 < t) (B : Fin d → Fin d → ℝ)
    (b : Fin d → ℝ) :
    Integrable (fun u : Fin d → ℝ => (∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  have hpair : ∀ i j, Integrable (fun u : Fin d → ℝ => B i j / 2 * (u i * u j) *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := fun i j =>
    ((integrable_coord_mul_separableAnharmonic hlam hgamma hdisc ht i j).const_mul
      (B i j / 2)).congr (Eventually.of_forall fun u => by simp only; ring)
  have hlin : ∀ i, Integrable (fun u : Fin d → ℝ => b i * u i *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := fun i =>
    ((integrable_coord_separableAnharmonic hlam hgamma hdisc ht i).const_mul (b i)).congr
      (Eventually.of_forall fun u => by simp only; ring)
  have h1 : Integrable (fun u : Fin d → ℝ => (∑ i, ∑ j, B i j / 2 * (u i * u j)) *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin d)) fun j _ => hpair i j
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [Finset.sum_mul]
  have h2 : Integrable (fun u : Fin d → ℝ => (∑ i, b i * u i) *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hlin i
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [Finset.sum_mul]
  refine (h1.add h2).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply]
  ring

/-- **`d/dt ⟨ψ⟩_loc = −Cov_loc[L∘A, ψ]` on E2's exact localised measure**, for the centred quadratic
probe `ψ(w) = ½(w − c)ᵀB(w − c) + bᵀ(w − c)`: the exact localised eq:covK is `−∂ₜ` of the exact
localised eq:mean/eq:cov, anchor term included. -/
theorem hasDerivAt_localisedRotatedAnharmonic_probe (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    HasDerivAt (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)))
      (-gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c))) t := by
  set u₀ := affineFrame Q c w₀ with hu₀
  have hc := continuous_separableAnharmonic lam alpha gamma
  have hψ : Continuous fun u : Fin d → ℝ =>
      ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) + ∑ i, (Qᵀ *ᵥ b) i * u i :=
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop).add
      (continuous_finsetSum _ fun i _ => by fun_prop)
  have hprobe : (fun w : Fin d → ℝ => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      rotated Q c (fun u => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) +
        ∑ i, (Qᵀ *ᵥ b) i * u i) :=
    funext (probe_affineFrame hQ c B b)
  have hexp : ∀ s, gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
      (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      gibbsExpectation (localisedPotential (separableAnharmonic lam alpha gamma) g u₀ s) s
        (fun u => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) + ∑ i, (Qᵀ *ᵥ b) i * u i) :=
      fun s => by
    rw [hprobe, localisedRotatedAnharmonic_eq_rotated_localised hQ c w₀ s]
    exact gibbsExpectation_rotated_of_continuous hQ c (continuous_localisedPotential hc g u₀ s) hψ s
  have hcov : gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma)
      (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      gibbsCov (localisedPotential (separableAnharmonic lam alpha gamma) g u₀ t) t
        (separableAnharmonic lam alpha gamma)
        (fun u => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) + ∑ i, (Qᵀ *ᵥ b) i * u i) := by
    rw [hprobe, localisedRotatedAnharmonic_eq_rotated_localised hQ c w₀ t,
      rotatedAnharmonic]
    exact gibbsCov_rotated_of_continuous hQ c (continuous_localisedPotential hc g u₀ t) hc hψ t
  simp only [hexp, hcov]
  exact hasDerivAt_localised_separable hlam hgamma hdisc hg u₀ ht hψ
    (integrable_energy_quadratic_separableAnharmonic hlam hgamma hdisc (half_pos ht) _ _)
    (integrable_quadratic_separableAnharmonic hlam hgamma hdisc (half_pos ht) _ _)

/-- **The exact localised eq:covK is the negative derivative of the exact localised
expectation.** -/
theorem localisedCovK_eq_neg_deriv (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      -deriv (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c))) t := by
  rw [(hasDerivAt_localisedRotatedAnharmonic_probe hlam hgamma hdisc hQ c w₀ hg ht B b).deriv,
    neg_neg]

end Rotated

/-! ### One dimension: the localised Stein identity -/

section Stein

theorem hasDerivAt_locWeight (g x₀ x : ℝ) :
    HasDerivAt (locWeight g x₀) ((g * x₀ - g * x) * locWeight g x₀ x) x := by
  have h : HasDerivAt (fun y => g * x₀ * y - g / 2 * y ^ 2) (g * x₀ - g * x) x := by
    have := ((hasDerivAt_id' x).const_mul (g * x₀)).sub ((hasDerivAt_pow 2 x).const_mul (g / 2))
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have := h.exp
  unfold locWeight
  exact this.congr_deriv (by ring)

/-- `(x^k φ)' = (k x^{k−1} + x^k(a − gx)) φ`. -/
theorem hasDerivAt_pow_mul_locWeight (g x₀ : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => y ^ k * locWeight g x₀ y)
      (((k : ℝ) * x ^ (k - 1) + x ^ k * (g * x₀ - g * x)) * locWeight g x₀ x) x := by
  have h := (hasDerivAt_pow k x).mul (hasDerivAt_locWeight g x₀ x)
  exact h.congr_deriv (by ring)

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- **The localised Stein identity on the weighted unlocalised measure**:
`⟨(kx^{k−1} + x^k(a − gx))φ⟩ = t⟨x^k ℓ' φ⟩`. -/
theorem stein_locWeight (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => ((k : ℝ) * x ^ (k - 1) + x ^ k * (g * x₀ - g * x)) * locWeight g x₀ x) =
      t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ k * locWeight g x₀ x * anharmonicDeriv lam alpha gamma x) := by
  have hp := integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀)
  refine stein_anharmonic (fun x => hasDerivAt_pow_mul_locWeight g x₀ k x) (hp k) ?_ ?_
  · have := (((hp (k - 1)).const_mul (k : ℝ)).add ((hp k).const_mul (g * x₀))).sub
      ((hp (k + 1)).const_mul g)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · have := (((hp (k + 1)).const_mul lam).add ((hp (k + 2)).const_mul (alpha / 2))).add
      ((hp (k + 3)).const_mul (gamma / 6))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    unfold anharmonicDeriv
    ring

/-- **The localised Stein identity**: `⟨kx^{k−1} + x^k(a − gx)⟩_loc = t⟨x^k ℓ'⟩_loc`. -/
theorem stein_loc_pow (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => (k : ℝ) * x ^ (k - 1) + x ^ k * (g * x₀ - g * x)) =
      t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ k * anharmonicDeriv lam alpha gamma x) := by
  rw [gibbsExpectation_locPotential1 hlam hgamma hdisc ht,
    gibbsExpectation_locPotential1 hlam hgamma hdisc ht, stein_locWeight hlam hgamma hdisc hg ht k,
    mul_div_assoc]
  congr 3
  funext x
  ring

/-- **The moment recursion of the localised measure**:
`(tλ + g)m_{k+1} + (tα/2)m_{k+2} + (tγ/6)m_{k+3} = k m_{k−1} + a m_k`, `m_j = ⟨x^j⟩_loc`. -/
theorem stein_loc_recursion (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (t * lam + g) * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ (k + 1)) +
      t * alpha / 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ (k + 2)) +
      t * gamma / 6 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ (k + 3)) =
      (k : ℝ) * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ (k - 1)) +
      g * x₀ * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ k) := by
  have hp := integrable_pow_locPotential1 hlam hgamma hdisc hg ht (x₀ := x₀)
  have h := stein_loc_pow hlam hgamma hdisc hg ht (x₀ := x₀) k
  have e1 : (fun x : ℝ => (k : ℝ) * x ^ (k - 1) + x ^ k * (g * x₀ - g * x)) =
      fun x => (k : ℝ) * x ^ (k - 1) + g * x₀ * x ^ k + (-g) * x ^ (k + 1) := by
    funext x
    ring
  have e2 : (fun x : ℝ => x ^ k * anharmonicDeriv lam alpha gamma x) =
      fun x => lam * x ^ (k + 1) + alpha / 2 * x ^ (k + 2) + gamma / 6 * x ^ (k + 3) := by
    funext x
    unfold anharmonicDeriv
    ring
  rw [e1, e2, gibbs_lin3 (hp (k - 1)) (hp k) (hp (k + 1)),
    gibbs_lin3 (hp (k + 1)) (hp (k + 2)) (hp (k + 3))] at h
  linear_combination -h

/-- The `k = 0` case: `(tλ + g)m₁ + (tα/2)m₂ + (tγ/6)m₃ = a` — the exact localised mean equation. -/
theorem stein_loc_zero (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    (t * lam + g) * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x) +
      t * alpha / 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 2) +
      t * gamma / 6 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 3) = g * x₀ := by
  have h := stein_loc_recursion hlam hgamma hdisc hg ht (x₀ := x₀) 0
  have hZ := partitionFunction_locPotential1_pos hlam hgamma hdisc hg ht (x₀ := x₀)
  have h1 : _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
      (fun x => x ^ 0) = 1 := by
    simp only [pow_zero]
    unfold _root_.Laplace.gibbsExpectation _root_.Laplace.partitionFunction
    simp only [one_mul]
    exact div_self hZ.ne'
  simp only [Nat.cast_zero, zero_mul, zero_add, pow_one] at h
  rw [h1] at h
  simpa using h

/-- `⟨x^0⟩_loc = 1`. -/
theorem locMoment_zero (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 0) =
      1 := by
  have hZ := partitionFunction_locPotential1_pos hlam hgamma hdisc hg ht (x₀ := x₀)
  simp only [pow_zero]
  unfold _root_.Laplace.gibbsExpectation _root_.Laplace.partitionFunction
  simp only [one_mul]
  exact div_self hZ.ne'

/-- **The localised Stein–covariance reduction** (`C_{r,n} = Cov_loc[x^r, xⁿ]`):
`t²Cov_loc[ℓ, xⁿ] = (n/2)t⟨xⁿ⟩_loc − (α/12)t²C_{3,n} − (γ/24)t²C_{4,n} − (g/2)tC_{2,n}
+ (a/2)tC_{1,n}`
— Stein on `x^{n+1}` minus `⟨xⁿ⟩_loc` times Stein on `x`, with `xℓ' = 2ℓ + (α/6)x³ + (γ/12)x⁴`. The
localised analogue of `covK_sq_stein`/`covK_lin_stein`; the new terms are the localiser's. -/
theorem stein_loc_cov_reduction (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ n) =
      (n : ℝ) / 2 * (t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ n)) -
      alpha / 12 * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 3) (fun x => x ^ n)) -
      gamma / 24 * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 4) (fun x => x ^ n)) -
      g / 2 * (t * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 2) (fun x => x ^ n)) +
      g * x₀ / 2 * (t * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x) (fun x => x ^ n)) := by
  have hp := integrable_pow_locPotential1 hlam hgamma hdisc hg ht (x₀ := x₀)
  have hrec := stein_loc_recursion hlam hgamma hdisc hg ht (x₀ := x₀) (n + 1)
  have hone := stein_loc_recursion hlam hgamma hdisc hg ht (x₀ := x₀) 1
  rw [show n + 1 - 1 = n by omega, show n + 1 + 1 = n + 2 by omega,
    show n + 1 + 2 = n + 3 by omega, show n + 1 + 3 = n + 4 by omega] at hrec
  rw [show (1 : ℕ) - 1 = 0 from rfl, locMoment_zero hlam hgamma hdisc hg ht,
    show (1 : ℕ) + 1 = 2 from rfl, show (1 : ℕ) + 2 = 3 from rfl,
    show (1 : ℕ) + 3 = 4 from rfl] at hone
  unfold _root_.Laplace.gibbsCov
  have eE : (fun x => anharmonicPotential lam alpha gamma x * x ^ n) =
      fun x => lam / 2 * x ^ (n + 2) + alpha / 6 * x ^ (n + 3) + gamma / 24 * x ^ (n + 4) := by
    funext x
    rw [anharmonicPotential_eq_lin]
    ring
  have e1 : (fun x : ℝ => x * x ^ n) = fun x => x ^ (n + 1) := by funext x; ring
  have e2 : (fun x : ℝ => x ^ 2 * x ^ n) = fun x => x ^ (n + 2) := by funext x; ring
  have e3 : (fun x : ℝ => x ^ 3 * x ^ n) = fun x => x ^ (n + 3) := by funext x; ring
  have e4 : (fun x : ℝ => x ^ 4 * x ^ n) = fun x => x ^ (n + 4) := by funext x; ring
  rw [eE, e1, e2, e3, e4, gibbs_lin3 (hp (n + 2)) (hp (n + 3)) (hp (n + 4)),
    locEnergy_eq hlam hgamma hdisc hg ht]
  simp only [Nat.cast_add, Nat.cast_one] at hrec
  simp only [pow_one, Nat.cast_one, one_mul] at hone
  linear_combination (t / 2) * hrec -
    (t / 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
      (fun x => x ^ n)) * hone

end Stein

end Laplace.Multi
