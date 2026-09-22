/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedAnharmonic
import Laplace.Multi.AmbientMoments
import Laplace.Multi.E2Matrix
import Laplace.Multi.CovKDerivativeLoc

/-!
# eq:mean's localisation term in `d` dimensions, on E2's exact localised measure

E3 localises the posterior with `(γ/2)|w − w₀|²`; eq:mean then reads
`⟨w⟩ − w* = −½ S (tT:S) + γ S (w₀ − w*) + O(S²)`, `S = (tH + γI)⁻¹`. For E2's rotated
anharmonic oscillator `L(Qᵀ(w − c))` with the isotropic localiser of strength `g` (the note's
`γ`; `γᵢ` is the quartic coefficient here) the localised measure
`e^{−tL(Qᵀ(w−c)) − (g/2)|w − w₀|²}` is separable in the eigenframe (`localiser_affineFrame`:
the isotropic localiser is frame invariant), so each frame coordinate is the one-dimensional
localised mean of `Laplace.Multi.LocalisedAnharmonic` (`localisedRotatedAnharmonic_frame_coord`,
`localisedRotatedAnharmonic_ambient_coord`). Consequences, with `a = Qᵀ(w₀ − c)`:

* `localisedRotatedAnharmonic_frame_rate`:
  `|t⟨(Qᵀ(w − c))ᵢ⟩_loc − (−αᵢ/(2λᵢ²) + g aᵢ/λᵢ)| ≤ K/√t`;
* `localisedRotatedAnharmonic_ambient_rate`: for every ambient coordinate,
  `|(⟨w⟩_loc − c − meanShift t H T − g (tH)⁻¹(w₀ − c))ⱼ| ≤ K/(t√t)`, eq:mean's two terms at
  `S = (tH)⁻¹`;
* `localisedRotatedAnharmonic_displayed_rate`: the same against the displayed formula
  `meanShiftLoc t g H T + g • (locS g H t *ᵥ (w₀ − c))`, i.e. with `S = (tH + gI)⁻¹`.

Leading-order certification only: the `O(S²)` remainder of eq:mean is not addressed.
-/

open Real MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

variable {ι : Type*} [Fintype ι]

/-! ### The localised potential and its frame invariance -/

/-- The isotropic localiser `(g/(2t))|w − w₀|²`, so that
`e^{−t(L + loc)} = e^{−tL − (g/2)|w − w₀|²}`. -/
noncomputable def localiser (g : ℝ) (w₀ : ι → ℝ) (t : ℝ) (w : ι → ℝ) : ℝ :=
  g / (2 * t) * ∑ j, (w j - w₀ j) ^ 2

/-- E3's localised potential `L + (g/(2t))|w − w₀|²`. -/
noncomputable def localisedPotential (L : (ι → ℝ) → ℝ) (g : ℝ) (w₀ : ι → ℝ) (t : ℝ) :
    (ι → ℝ) → ℝ :=
  fun w => L w + localiser g w₀ t w

theorem exp_neg_localisedPotential (L : (ι → ℝ) → ℝ) (g : ℝ) (w₀ : ι → ℝ) {t : ℝ} (ht : t ≠ 0)
    (w : ι → ℝ) :
    Real.exp (-(t * localisedPotential L g w₀ t w)) =
      Real.exp (-(t * L w) - g / 2 * ∑ j, (w j - w₀ j) ^ 2) := by
  unfold localisedPotential localiser
  congr 1
  field_simp
  ring

theorem localiser_nonneg {g : ℝ} (hg : 0 ≤ g) (w₀ : ι → ℝ) {t : ℝ} (ht : 0 < t) (w : ι → ℝ) :
    0 ≤ localiser g w₀ t w := by
  unfold localiser
  positivity

theorem continuous_localiser (g : ℝ) (w₀ : ι → ℝ) (t : ℝ) : Continuous (localiser g w₀ t) := by
  unfold localiser
  fun_prop

theorem continuous_localisedPotential {L : (ι → ℝ) → ℝ} (hL : Continuous L) (g : ℝ) (w₀ : ι → ℝ)
    (t : ℝ) : Continuous (localisedPotential L g w₀ t) :=
  hL.add (continuous_localiser g w₀ t)

theorem sum_sq_mulVec_transpose [DecidableEq ι] {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (v : ι → ℝ) :
    ∑ i, (Qᵀ *ᵥ v) i ^ 2 = ∑ j, v j ^ 2 := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have h : (Qᵀ *ᵥ v) ⬝ᵥ (Qᵀ *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hQQ, one_mulVec]
  simpa [dotProduct, sq] using h

/-- **The isotropic localiser is frame invariant**: `|A w − A w₀|² = |w − w₀|²`. -/
theorem localiser_affineFrame [DecidableEq ι] {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c w₀ : ι → ℝ)
    (g t : ℝ) (w : ι → ℝ) :
    localiser g (affineFrame Q c w₀) t (affineFrame Q c w) = localiser g w₀ t w := by
  unfold localiser
  congr 1
  have e : ∀ j, affineFrame Q c w j - affineFrame Q c w₀ j = (Qᵀ *ᵥ (w - w₀)) j := by
    intro j
    simp only [affineFrame]
    rw [← Pi.sub_apply (Qᵀ *ᵥ (w - c)) (Qᵀ *ᵥ (w₀ - c)), ← mulVec_sub, sub_sub_sub_cancel_right]
  simp only [e, sum_sq_mulVec_transpose hQ, Pi.sub_apply]

/-- Localising after rotating is rotating after localising at the transported anchor. -/
theorem rotated_localisedPotential [DecidableEq ι] {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1)
    (c w₀ : ι → ℝ) (L : (ι → ℝ) → ℝ) (g t : ℝ) :
    rotated Q c (localisedPotential L g (affineFrame Q c w₀) t) =
      localisedPotential (rotated Q c L) g w₀ t := by
  funext w
  simp only [rotated, localisedPotential, localiser_affineFrame hQ]

/-- The isotropic localiser keeps a separable potential separable. -/
theorem localisedPotential_separable (ℓ : ι → ℝ → ℝ) (g : ℝ) (u₀ : ι → ℝ) (t : ℝ) :
    localisedPotential (separablePotential ℓ) g u₀ t =
      separablePotential fun i x => ℓ i x + g / (2 * t) * (x - u₀ i) ^ 2 := by
  funext u
  simp only [localisedPotential, localiser, separablePotential, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- Localising only lowers the Boltzmann factor, so integrability is inherited. -/
theorem integrable_localised_of_integrable {L φ : (ι → ℝ) → ℝ} {g : ℝ} (hg : 0 ≤ g) (w₀ : ι → ℝ)
    {t : ℝ} (ht : 0 < t)
    (hmeas : AEStronglyMeasurable
      (fun w => φ w * Real.exp (-(t * localisedPotential L g w₀ t w))) volume)
    (hint : Integrable (fun w => φ w * Real.exp (-(t * L w)))) :
    Integrable (fun w => φ w * Real.exp (-(t * localisedPotential L g w₀ t w))) := by
  refine Integrable.mono' hint.norm hmeas (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, Real.norm_eq_abs, abs_mul, Real.abs_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have h0 := localiser_nonneg hg w₀ ht w
  unfold localisedPotential
  nlinarith [mul_nonneg ht.le h0]

/-! ### One dimension: the localised potential is tide 65's localised measure -/

section OneDim

variable {lam alpha gamma g x₀ : ℝ}

theorem exp_neg_localisedAnharmonic {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    Real.exp (-(t * (anharmonicPotential lam alpha gamma x + g / (2 * t) * (x - x₀) ^ 2))) =
      Real.exp (-(t * anharmonicPotential lam alpha gamma x) - g / 2 * (x - x₀) ^ 2) := by
  congr 1
  field_simp
  ring

theorem gibbsExpectation_localisedAnharmonic_id {t : ℝ} (ht : t ≠ 0) :
    _root_.Laplace.gibbsExpectation
        (fun x => anharmonicPotential lam alpha gamma x + g / (2 * t) * (x - x₀) ^ 2) t
        (fun x => x) =
      localisedMean lam alpha gamma g x₀ t := by
  simp only [_root_.Laplace.gibbsExpectation, _root_.Laplace.partitionFunction, localisedMean]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [exp_neg_localisedAnharmonic (g := g) (x₀ := x₀) ht]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [exp_neg_localisedAnharmonic (g := g) (x₀ := x₀) ht]

theorem partitionFunction_localisedAnharmonic_pos (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    0 < _root_.Laplace.partitionFunction
      (fun x => anharmonicPotential lam alpha gamma x + g / (2 * t) * (x - x₀) ^ 2) t := by
  unfold _root_.Laplace.partitionFunction
  refine integral_exp_pos ?_
  have h := (integrable_locWeight hlam hgamma hdisc hg ht (x₀ := x₀)).const_mul
    (Real.exp (-(g * x₀ ^ 2 / 2)))
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [exp_neg_localisedAnharmonic (g := g) (x₀ := x₀) ht.ne', locWeight]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end OneDim

/-! ### E2's oscillator with the isotropic localiser -/

section E2

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- E3's localised measure on E2's oscillator: the potential with Boltzmann factor
`e^{−t L(Qᵀ(w − c)) − (g/2)|w − w₀|²}`. -/
noncomputable def localisedRotatedAnharmonic (Q : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ)
    (lam alpha gamma : Fin d → ℝ) (g : ℝ) (w₀ : Fin d → ℝ) (t : ℝ) : (Fin d → ℝ) → ℝ :=
  localisedPotential (rotatedAnharmonic Q c lam alpha gamma) g w₀ t

theorem localisedRotatedAnharmonic_eq_rotated (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (t : ℝ) :
    localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t =
      rotated Q c (separablePotential fun i x =>
        anharmonicPotential (lam i) (alpha i) (gamma i) x +
          g / (2 * t) * (x - affineFrame Q c w₀ i) ^ 2) := by
  rw [localisedRotatedAnharmonic, rotatedAnharmonic, ← rotated_localisedPotential hQ,
    separableAnharmonic, localisedPotential_separable]

theorem continuous_localisedRotatedAnharmonic (Q : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ)
    (lam alpha gamma : Fin d → ℝ) (g : ℝ) (w₀ : Fin d → ℝ) (t : ℝ) :
    Continuous (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) :=
  continuous_localisedPotential
    ((continuous_separableAnharmonic lam alpha gamma).comp (by unfold affineFrame; fun_prop)) g w₀ t

/-- **Coordinate reduction**: in the eigenframe each localised coordinate mean is the
one-dimensional localised mean at the transported anchor. -/
theorem localisedRotatedAnharmonic_frame_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t)
    (i : Fin d) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i) =
      localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t := by
  have hcont := continuous_localisedPotential (continuous_separableAnharmonic lam alpha gamma) g
    (affineFrame Q c w₀) t
  rw [separableAnharmonic, localisedPotential_separable] at hcont
  rw [localisedRotatedAnharmonic_eq_rotated hQ, gibbsExpectation_rotated_coord hQ c hcont t i,
    gibbsExpectation_coord_separable _ t (fun k => (partitionFunction_localisedAnharmonic_pos
      (hlam k) (hgamma k) (hdisc k) hg ht).ne') i (fun x => x),
    gibbsExpectation_localisedAnharmonic_id ht.ne']

/-- **A: the frame coordinates of eq:mean at leading order.** -/
theorem localisedRotatedAnharmonic_frame_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (i : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i) -
        (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i)| ≤ K / Real.sqrt t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedMean_anharmonic_rate (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedRotatedAnharmonic_frame_coord hQ c w₀ hlam hgamma hdisc hg ht0 i]
  exact h ht

/-! ### The ambient coordinates -/

theorem integrable_exp_localisedRotatedAnharmonic (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    Integrable (fun w =>
      Real.exp (-(t * localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t w))) := by
  unfold localisedRotatedAnharmonic
  have hL : Continuous (localisedPotential (rotatedAnharmonic Q c lam alpha gamma) g w₀ t) :=
    continuous_localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t
  have h := integrable_localised_of_integrable (L := rotatedAnharmonic Q c lam alpha gamma)
    (φ := fun _ => (1 : ℝ)) hg w₀ ht (Continuous.aestronglyMeasurable (by fun_prop))
    (by simpa using integrable_exp_rotatedAnharmonic hQ c hlam hgamma hdisc ht)
  simpa using h

theorem partitionFunction_localisedRotatedAnharmonic_pos (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t := by
  unfold partitionFunction
  exact integral_exp_pos (integrable_exp_localisedRotatedAnharmonic hQ c w₀ hlam hgamma hdisc hg ht)

theorem integrable_frame_coord_localised (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (i : Fin d) :
    Integrable (fun w => affineFrame Q c w i *
      Real.exp (-(t * localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t w))) := by
  unfold localisedRotatedAnharmonic
  have hL : Continuous (localisedPotential (rotatedAnharmonic Q c lam alpha gamma) g w₀ t) :=
    continuous_localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t
  have hA : Continuous fun w : Fin d → ℝ => affineFrame Q c w i := by
    unfold affineFrame; fun_prop
  exact integrable_localised_of_integrable (L := rotatedAnharmonic Q c lam alpha gamma)
    (φ := fun w => affineFrame Q c w i) hg w₀ ht (Continuous.aestronglyMeasurable (by fun_prop))
    (integrable_coord_rotatedAnharmonic hQ c hlam hgamma hdisc ht i)

/-- **The ambient localised mean**:
`⟨wⱼ⟩_loc = cⱼ + ∑ᵢ Qⱼᵢ · localisedMean(λᵢ, αᵢ, γᵢ, g, aᵢ, t)`. -/
theorem localisedRotatedAnharmonic_ambient_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (j : Fin d) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j) =
      c j + ∑ i, Q j i * localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t := by
  have hZ := (partitionFunction_localisedRotatedAnharmonic_pos hQ c w₀ hlam hgamma hdisc hg ht).ne'
  have hA := integrable_frame_coord_localised hQ c w₀ hlam hgamma hdisc hg ht
  have hL := integrable_exp_localisedRotatedAnharmonic hQ c w₀ hlam hgamma hdisc hg ht
  have hQA : ∀ i, Integrable (fun w => Q j i * affineFrame Q c w i *
      Real.exp (-(t * localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t w))) := fun i =>
    ((hA i).const_mul (Q j i)).congr (Eventually.of_forall fun w => by ring)
  have hsum : Integrable (fun w => (∑ i, Q j i * affineFrame Q c w i) *
      Real.exp (-(t * localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t w))) :=
    (integrable_finsetSum Finset.univ fun i _ => hQA i).congr (Eventually.of_forall fun w => by
      simp only [Finset.sum_mul])
  have hfun : (fun w : Fin d → ℝ => w j) =
      fun w => (fun _ => c j) w + ∑ i, Q j i * affineFrame Q c w i := by
    funext w
    exact coord_eq_sum_affineFrame hQ c w j
  rw [hfun, gibbsExpectation_add_of_integrable _ _ _ _ (hL.const_mul _) hsum,
    gibbsExpectation_const_of_ne_zero _ _ _ hZ,
    gibbsExpectation_finsetSum _ _ Finset.univ _ (fun i _ => hQA i)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gibbsExpectation_const_mul,
    localisedRotatedAnharmonic_frame_coord hQ c w₀ hlam hgamma hdisc hg ht i]

/-! ### Rates for finite sums -/

theorem sum_rate_div_sqrt {κ : Type*} [Fintype κ] (a : κ → ℝ) (e : κ → ℝ → ℝ)
    (h : ∀ i, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |e i t| ≤ K / (t * Real.sqrt t)) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |∑ i, a i * e i t| ≤ K / (t * Real.sqrt t) := by
  choose K T hK hT h using h
  have hT0 : ∀ i, 0 ≤ T i := fun i => zero_le_one.trans (hT i)
  refine ⟨∑ i, |a i| * K i, 1 + ∑ i, T i,
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hK i),
    le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hT0 i), fun {t} ht => ?_⟩
  have hTi : ∀ i, T i ≤ t := fun i =>
    (Finset.single_le_sum (fun i _ => hT0 i) (Finset.mem_univ i)).trans
      ((le_add_of_nonneg_left zero_le_one).trans ht)
  calc |∑ i, a i * e i t| ≤ ∑ i, |a i * e i t| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |e i t| := by simp only [abs_mul]
    _ ≤ ∑ i, |a i| * (K i / (t * Real.sqrt t)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i (hTi i)) (abs_nonneg _)
    _ = (∑ i, |a i| * K i) / (t * Real.sqrt t) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The 1D leading form divided by `t`: `|localisedMean − (−α/(2λ²) + g x₀/λ)/t| ≤ K/(t√t)`. -/
theorem localisedMean_sub_leading_div_rate {lam alpha gamma x₀ : ℝ} (hlam : 0 < lam)
    (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |localisedMean lam alpha gamma g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) / t| ≤
        K / (t * Real.sqrt t) := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedMean_anharmonic_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith [hT]
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  set m := localisedMean lam alpha gamma g x₀ t
  set v := -alpha / (2 * lam ^ 2) + g * x₀ / lam
  have e : m - v / t = (t * m - v) / t := by field_simp
  rw [e, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  calc |t * m - v| ≤ K / Real.sqrt t := h ht
    _ = K / (t * Real.sqrt t) * t := by field_simp

/-! ### The note's matrix functionals on E2's tensors -/

theorem sub_eq_mulVec_affineFrame (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) :
    w₀ - c = Q *ᵥ affineFrame Q c w₀ := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  unfold affineFrame
  rw [Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]

/-- eq:mean's two terms at `S = (tH)⁻¹` are `Q (−αᵢ/(2λᵢ²) + g aᵢ/λᵢ)/t`. -/
theorem meanShift_add_localisation_rot (hQ : Qᵀ * Q = 1) (hlam : ∀ i, lam i ≠ 0)
    (alpha : Fin d → ℝ) (g : ℝ) (c w₀ : Fin d → ℝ) {t : ℝ} (ht : t ≠ 0) :
    meanShift t (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
        g • ((t • (Q * diagonal lam * Qᵀ))⁻¹ *ᵥ (w₀ - c)) =
      Q *ᵥ (fun i => (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i) / t) := by
  rw [meanShift_rot hQ hlam alpha ht, smul_conj_diagonal_inv hQ hlam ht,
    sub_eq_mulVec_affineFrame hQ, conj_mulVec_mulVec hQ, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := hlam i
  field_simp

theorem locPrec_rot (hQ : Qᵀ * Q = 1) (lam : Fin d → ℝ) (g t : ℝ) :
    locPrec g (Q * diagonal lam * Qᵀ) t = Q * diagonal (fun i => t * lam i + g) * Qᵀ := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  unfold locPrec
  have h1 : t • (Q * diagonal lam * Qᵀ) = Q * diagonal (fun i => t * lam i) * Qᵀ := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    rfl
  have h2 : g • (1 : Matrix (Fin d) (Fin d) ℝ) = Q * diagonal (fun _ => g) * Qᵀ := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQQ]
  rw [h1, h2, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]

/-- The displayed resolvent on E2's tensors: `(tH + gI)⁻¹ = Q diag(1/(tλᵢ + g)) Qᵀ`. -/
theorem locS_rot (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    locS g (Q * diagonal lam * Qᵀ) t = Q * diagonal (fun i => 1 / (t * lam i + g)) * Qᵀ := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  unfold locS
  rw [locPrec_rot hQ]
  apply Matrix.inv_eq_right_inv
  rw [conj_mul_conj hQ, diagonal_mul_diagonal]
  have h : (fun i => (t * lam i + g) * (1 / (t * lam i + g))) = fun _ => (1 : ℝ) := by
    funext i
    have := hlam i
    have hpos : 0 < t * lam i + g := by positivity
    field_simp
  rw [h, diagonal_one, Matrix.mul_one, hQQ]

/-- eq:mean's cubic term with the displayed `S`: `meanShiftLoc = Q(−αᵢ t/(2(tλᵢ + g)²))`. -/
theorem meanShiftLoc_rot (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (alpha : Fin d → ℝ) :
    meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) =
      Q *ᵥ (fun i => -alpha i * t / (2 * (t * lam i + g) ^ 2)) := by
  rw [meanShiftLoc, locS_rot hQ hlam hg ht, contractT_rot_mulVec hQ, Matrix.mulVec_smul,
    conj_mulVec_mulVec hQ, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have := hlam i
  have hpos : 0 < t * lam i + g := by positivity
  field_simp

/-- **eq:mean's displayed right-hand side on E2's tensors** is `Q (locLeading λᵢ αᵢ g aᵢ t)ᵢ`. -/
theorem displayed_mean_rot (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (alpha : Fin d → ℝ) (c w₀ : Fin d → ℝ) :
    meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
        g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c)) =
      Q *ᵥ (fun i => locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) t) := by
  rw [meanShiftLoc_rot hQ hlam hg ht alpha, locS_rot hQ hlam hg ht, sub_eq_mulVec_affineFrame hQ,
    conj_mulVec_mulVec hQ, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, locLeading]
  ring

/-! ### The main theorems -/

/-- **B: eq:mean's two terms at `S = (tH)⁻¹`, on E2's exact localised measure**: for every
ambient coordinate, `|(⟨w⟩_loc − c − meanShift − g (tH)⁻¹(w₀ − c))ⱼ| ≤ K/(t√t)`. -/
theorem localisedRotatedAnharmonic_ambient_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j) -
        c j - (meanShift t (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • ((t • (Q * diagonal lam * Qᵀ))⁻¹ *ᵥ (w₀ - c))) j| ≤ K / (t * Real.sqrt t) := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sqrt (fun i => Q j i)
    (fun i t => localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i) / t)
    (fun i => localisedMean_sub_leading_div_rate (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => w j) - c j - (meanShift t (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • ((t • (Q * diagonal lam * Qᵀ))⁻¹ *ᵥ (w₀ - c))) j =
      ∑ i, Q j i * (localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
        (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i) / t) := by
    rw [localisedRotatedAnharmonic_ambient_coord hQ c w₀ hlam hgamma hdisc hg ht0 j,
      meanShift_add_localisation_rot hQ (fun i => (hlam i).ne') alpha g c w₀ ht0.ne']
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [key]
  exact h ht

/-- **C: eq:mean's displayed right-hand side, `S = (tH + gI)⁻¹`, on E2's exact localised
measure**: for every ambient coordinate,
`|(⟨w⟩_loc − c − meanShiftLoc − g S (w₀ − c))ⱼ| ≤ K/(t√t)`. -/
theorem localisedRotatedAnharmonic_displayed_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j) -
        c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j| ≤ K / (t * Real.sqrt t) := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sqrt (fun i => Q j i)
    (fun i t => localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) t)
    (fun i => localisedMean_sub_locLeading_rate (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => w j) - c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j =
      ∑ i, Q j i * (localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
        locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) t) := by
    rw [localisedRotatedAnharmonic_ambient_coord hQ c w₀ hlam hgamma hdisc hg ht0 j,
      displayed_mean_rot hQ hlam hg ht0 alpha c w₀]
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [key]
  exact h ht

end E2

end Laplace.Multi
