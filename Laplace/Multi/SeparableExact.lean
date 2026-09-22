/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.Defs
import Laplace.Multi.OneLoop
import Laplace.OneD.AnharmonicGibbsRegularity
import Laplace.OneD.AnharmonicGibbsObservableMonomials
import Laplace.OneD.AnharmonicKappa3

/-!
# E2 exact: the Gibbs measure of a separable potential

E2 of the note measures the Laplace remainder of separable anharmonic oscillators against exact
quadrature. The exact statements behind that comparison:

* `separablePotential`, `exp_separablePotential`, `integral_prod_separable`,
  `partitionFunction_separable`, `gibbsExpectation_prod_separable`: for `L(w) = ∑ᵢ ℓᵢ(wᵢ)` the
  Boltzmann factor, the partition function and the expectation of a product observable factorise,
  `⟨∏ᵢ φᵢ(wᵢ)⟩_L = ∏ᵢ ⟨φᵢ⟩_{ℓᵢ}` (no hypotheses: Bochner integrals are total);
* `gibbsExpectation_coord_separable`, `gibbsExpectation_pair_separable`,
  `gibbsCov_coord_separable`: with nonzero coordinate partition functions,
  `⟨φ(wᵢ)⟩_L = ⟨φ⟩_{ℓᵢ}`, `⟨wᵢ wⱼ⟩_L = ⟨x⟩_{ℓᵢ}⟨x⟩_{ℓⱼ}` for `i ≠ j`, and
  `Cov_L[wᵢ, wⱼ] = δᵢⱼ Var_{ℓᵢ}[x]`;
* `separableAnharmonic` and its exact covariance `gibbsCov_separableAnharmonic`; the
  per-coordinate Laplace remainders `separableAnharmonic_var_second_order`
  (`t²(Var − 1/(λᵢt)) → αᵢ²/λᵢ⁴ − γᵢ/(2λᵢ³)`), `separableAnharmonic_var_relative_rate`
  (`t(λᵢ t Var − 1) → αᵢ²/λᵢ³ − γᵢ/(2λᵢ²)`), `separableAnharmonic_var_relative_rate_note`
  (`→ a² − 1/2` for `αᵢ² = a²λᵢ³`, `γᵢ = λᵢ²`: the one-loop constant of `OneLoopSeparable`, now for
  the exact moments) and the mean `separableAnharmonic_mean_asymptotic`.

* the energy: `energy_anharmonic_asymptotic` (`t⟨ℓ⟩ → 1/2` in one dimension, by the moment route
  `⟨ℓ⟩ = (λ/2)⟨x²⟩ + (α/6)⟨x³⟩ + (γ/24)⟨x⁴⟩`) and `separableAnharmonic_energy_asymptotic`
  (`t⟨L⟩_L → d/2`: the exact LLC of E2's oscillator tends to the Laplace value).

Wording for the note: the exact relative covariance error is `(a² − 1/2)/t + o(1/t)`, the leading
correction to the Gaussian value; "proportional to `1/t`" needs `a² ≠ 1/2`.
-/

open MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-! ### Factorisation -/

section Separable

/-- The separable potential `L(w) = ∑ᵢ ℓᵢ(wᵢ)`. -/
noncomputable def separablePotential (ℓ : ι → ℝ → ℝ) : (ι → ℝ) → ℝ :=
  fun w => ∑ i, ℓ i (w i)

theorem exp_separablePotential (ℓ : ι → ℝ → ℝ) (t : ℝ) (w : ι → ℝ) :
    Real.exp (-(t * separablePotential ℓ w)) = ∏ i, Real.exp (-(t * ℓ i (w i))) := by
  rw [← Real.exp_sum]
  congr 1
  rw [separablePotential, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- **Product observables factorise**: `∫ (∏ᵢ φᵢ(wᵢ)) e^{−tL} = ∏ᵢ ∫ φᵢ e^{−tℓᵢ}`. -/
theorem integral_prod_separable (ℓ : ι → ℝ → ℝ) (t : ℝ) (φ : ι → ℝ → ℝ) :
    ∫ w : ι → ℝ, (∏ i, φ i (w i)) * Real.exp (-(t * separablePotential ℓ w)) =
      ∏ i, ∫ x : ℝ, φ i x * Real.exp (-(t * ℓ i x)) := by
  calc ∫ w : ι → ℝ, (∏ i, φ i (w i)) * Real.exp (-(t * separablePotential ℓ w))
      = ∫ w : ι → ℝ, ∏ i, φ i (w i) * Real.exp (-(t * ℓ i (w i))) :=
        integral_congr_ae (Eventually.of_forall fun w => by
          simp only [exp_separablePotential, Finset.prod_mul_distrib])
    _ = ∏ i, ∫ x : ℝ, φ i x * Real.exp (-(t * ℓ i x)) :=
        integral_fintype_prod_volume_eq_prod (f := fun i x => φ i x * Real.exp (-(t * ℓ i x)))

/-- The partition function factorises: `Z_L = ∏ᵢ Z_{ℓᵢ}`. -/
theorem partitionFunction_separable (ℓ : ι → ℝ → ℝ) (t : ℝ) :
    partitionFunction (separablePotential ℓ) t =
      ∏ i, _root_.Laplace.partitionFunction (ℓ i) t := by
  have h := integral_prod_separable ℓ t (fun _ _ => 1)
  simp only [Finset.prod_const_one, one_mul] at h
  unfold partitionFunction _root_.Laplace.partitionFunction
  exact h

/-- **The Gibbs expectation of a product observable factorises**: `⟨∏ᵢ φᵢ(wᵢ)⟩_L = ∏ᵢ ⟨φᵢ⟩_{ℓᵢ}`. -/
theorem gibbsExpectation_prod_separable (ℓ : ι → ℝ → ℝ) (t : ℝ) (φ : ι → ℝ → ℝ) :
    gibbsExpectation (separablePotential ℓ) t (fun w => ∏ i, φ i (w i)) =
      ∏ i, _root_.Laplace.gibbsExpectation (ℓ i) t (φ i) := by
  unfold gibbsExpectation _root_.Laplace.gibbsExpectation
  rw [integral_prod_separable, partitionFunction_separable, Finset.prod_div_distrib]

theorem gibbsExpectation_one_of_ne_zero {L : ℝ → ℝ} {t : ℝ}
    (hZ : _root_.Laplace.partitionFunction L t ≠ 0) :
    _root_.Laplace.gibbsExpectation L t (fun _ => 1) = 1 := by
  unfold _root_.Laplace.gibbsExpectation
  simp only [one_mul]
  exact div_self hZ

/-- **Coordinate reduction**: `⟨φ(wᵢ₀)⟩_L = ⟨φ⟩_{ℓᵢ₀}` when the spectator partition functions are
nonzero. -/
theorem gibbsExpectation_coord_separable (ℓ : ι → ℝ → ℝ) (t : ℝ)
    (hZ : ∀ i, _root_.Laplace.partitionFunction (ℓ i) t ≠ 0) (i₀ : ι) (φ : ℝ → ℝ) :
    gibbsExpectation (separablePotential ℓ) t (fun w => φ (w i₀)) =
      _root_.Laplace.gibbsExpectation (ℓ i₀) t φ := by
  classical
  have h := gibbsExpectation_prod_separable ℓ t (fun i x => if i = i₀ then φ x else 1)
  have hL : (fun w : ι → ℝ => ∏ i, (if i = i₀ then φ (w i) else 1)) = fun w => φ (w i₀) := by
    funext w
    simp [Finset.prod_ite_eq']
  rw [hL] at h
  rw [h, Finset.prod_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ i₀) h)]
  · simp
  · simp only [hi, if_false]
    exact gibbsExpectation_one_of_ne_zero (hZ i)

/-- **Distinct coordinates are uncorrelated**: `⟨wᵢ wⱼ⟩_L = ⟨x⟩_{ℓᵢ} ⟨x⟩_{ℓⱼ}` for `i ≠ j`. -/
theorem gibbsExpectation_pair_separable (ℓ : ι → ℝ → ℝ) (t : ℝ)
    (hZ : ∀ i, _root_.Laplace.partitionFunction (ℓ i) t ≠ 0) {i j : ι} (hij : i ≠ j) :
    gibbsExpectation (separablePotential ℓ) t (fun w => w i * w j) =
      _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
        _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) := by
  classical
  have h := gibbsExpectation_prod_separable ℓ t (fun k x => if k = i ∨ k = j then x else 1)
  have hL : (fun w : ι → ℝ => ∏ k, (if k = i ∨ k = j then w k else 1)) = fun w => w i * w j := by
    funext w
    rw [Finset.prod_eq_mul i j hij (fun k _ hk => by simp [hk.1, hk.2])
      (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)]
    simp [hij]
  rw [hL] at h
  rw [h, Finset.prod_eq_mul i j hij (fun k _ hk => ?_)
    (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)]
  · simp [hij]
  · simp only [hk.1, hk.2, or_self, if_false]
    exact gibbsExpectation_one_of_ne_zero (hZ k)

/-- **The exact covariance of a separable potential is diagonal**:
`Cov_L[wᵢ, wⱼ] = δᵢⱼ Var_{ℓᵢ}[x]`. -/
theorem gibbsCov_coord_separable [DecidableEq ι] (ℓ : ι → ℝ → ℝ) (t : ℝ)
    (hZ : ∀ i, _root_.Laplace.partitionFunction (ℓ i) t ≠ 0) (i j : ι) :
    gibbsCov (separablePotential ℓ) t (fun w => w i) (fun w => w j) =
      if i = j then _root_.Laplace.gibbsCov (ℓ i) t (fun x => x) (fun x => x) else 0 := by
  unfold gibbsCov _root_.Laplace.gibbsCov
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, gibbsExpectation_coord_separable ℓ t hZ i (fun x => x * x),
      gibbsExpectation_coord_separable ℓ t hZ i (fun x => x)]
  · rw [if_neg hij, gibbsExpectation_pair_separable ℓ t hZ hij,
      gibbsExpectation_coord_separable ℓ t hZ i (fun x => x),
      gibbsExpectation_coord_separable ℓ t hZ j (fun x => x), sub_self]

end Separable

/-! ### The separable anharmonic oscillator -/

section Anharmonic

/-- The one-dimensional anharmonic partition function is positive. -/
theorem partitionFunction_anharmonic_pos {lam alpha gamma t : ℝ} (hlam : 0 < lam)
    (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    0 < _root_.Laplace.partitionFunction (anharmonicPotential lam alpha gamma) t := by
  unfold _root_.Laplace.partitionFunction
  exact integral_exp_pos (integrable_exp_neg_t_anharmonic hlam hgamma hdisc ht)

/-- The note's E2 potential: `L(w) = ∑ᵢ (λᵢ wᵢ²/2 + αᵢ wᵢ³/6 + γᵢ wᵢ⁴/24)`. -/
noncomputable def separableAnharmonic (lam alpha gamma : ι → ℝ) : (ι → ℝ) → ℝ :=
  separablePotential fun i => anharmonicPotential (lam i) (alpha i) (gamma i)

variable {lam alpha gamma : ι → ℝ}

theorem gibbsExpectation_coord_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (i : ι) (φ : ℝ → ℝ) :
    gibbsExpectation (separableAnharmonic lam alpha gamma) t (fun w => φ (w i)) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential (lam i) (alpha i) (gamma i)) t φ :=
  gibbsExpectation_coord_separable _ t
    (fun k => (partitionFunction_anharmonic_pos (hlam k) (hgamma k) (hdisc k) ht).ne') i φ

/-- **The exact covariance of the separable anharmonic oscillator is diagonal**, with the
one-dimensional anharmonic variances on the diagonal. -/
theorem gibbsCov_separableAnharmonic [DecidableEq ι] (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) (i j : ι) :
    gibbsCov (separableAnharmonic lam alpha gamma) t (fun w => w i) (fun w => w j) =
      if i = j then _root_.Laplace.gibbsCov (anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (fun x => x) (fun x => x) else 0 :=
  gibbsCov_coord_separable _ t
    (fun k => (partitionFunction_anharmonic_pos (hlam k) (hgamma k) (hdisc k) ht).ne') i j

/-- **E2, second order**: along each coordinate the exact variance has the one-loop remainder
`t²(Var − 1/(λᵢt)) → αᵢ²/λᵢ⁴ − γᵢ/(2λᵢ³)`. -/
theorem separableAnharmonic_var_second_order (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    Tendsto (fun t : ℝ => t ^ 2 * (gibbsCov (separableAnharmonic lam alpha gamma) t
        (fun w => w i) (fun w => w i) - 1 / (lam i * t))) atTop
      (𝓝 (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3))) := by
  classical
  refine (var_anharmonic_second_order (hlam i) (hgamma i) (hdisc i)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [gibbsCov_separableAnharmonic hlam hgamma hdisc ht i i, if_pos rfl]

/-- **E2, "relative error proportional to `1/t`"**:
`t(λᵢ t Var_L[wᵢ] − 1) → αᵢ²/λᵢ³ − γᵢ/(2λᵢ²)`. -/
theorem separableAnharmonic_var_relative_rate (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    Tendsto (fun t : ℝ => t * (lam i * t * gibbsCov (separableAnharmonic lam alpha gamma) t
        (fun w => w i) (fun w => w i) - 1)) atTop
      (𝓝 (alpha i ^ 2 / lam i ^ 3 - gamma i / (2 * lam i ^ 2))) := by
  have h := (separableAnharmonic_var_second_order hlam hgamma hdisc i).const_mul (lam i)
  have hne := (hlam i).ne'
  have hlim : lam i * (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3)) =
      alpha i ^ 2 / lam i ^ 3 - gamma i / (2 * lam i ^ 2) := by
    field_simp
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  field_simp

/-- **E2 in the note's parametrisation** (`αᵢ² = a² λᵢ³`, `γᵢ = λᵢ²`, `a² < 3`): the exact relative
covariance error along every coordinate is `(a² − 1/2)/t + o(1/t)`, independent of `κ` — the
one-loop constant of `oneLoopCov_separable_note_ratio`, now for the exact Gibbs moments. -/
theorem separableAnharmonic_var_relative_rate_note {a : ℝ} (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, gamma i = lam i ^ 2) (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3)
    (ha : a ^ 2 < 3) (i : ι) :
    Tendsto (fun t : ℝ => t * (lam i * t * gibbsCov (separableAnharmonic lam alpha gamma) t
        (fun w => w i) (fun w => w i) - 1)) atTop (𝓝 (a ^ 2 - 1 / 2)) := by
  have hg : ∀ i, 0 < gamma i := fun i => by rw [hgamma i]; exact pow_pos (hlam i) 2
  have hd : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i := fun i => by
    rw [halpha i, hgamma i]
    nlinarith [pow_pos (hlam i) 3]
  have h := separableAnharmonic_var_relative_rate hlam hg hd i
  have hne := (hlam i).ne'
  have hlim : alpha i ^ 2 / lam i ^ 3 - gamma i / (2 * lam i ^ 2) = a ^ 2 - 1 / 2 := by
    rw [halpha i, hgamma i]
    field_simp
  rwa [hlim] at h

/-- **E2, the mean shift**: `t ⟨wᵢ⟩_L → −αᵢ/(2λᵢ²)` along each coordinate. -/
theorem separableAnharmonic_mean_asymptotic (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    Tendsto (fun t : ℝ => t * gibbsExpectation (separableAnharmonic lam alpha gamma) t
        (fun w => w i)) atTop (𝓝 (-alpha i / (2 * lam i ^ 2))) := by
  refine (mean_anharmonic_asymptotic (hlam i) (hgamma i) (hdisc i)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [gibbsExpectation_coord_separableAnharmonic hlam hgamma hdisc ht i (fun x => x)]

end Anharmonic

/-! ### The energy: `t⟨L⟩ → d/2` -/

section Energy

/-- `xᵐ e^{−tℓ}` is integrable for the anharmonic potential. -/
theorem integrable_pow_mul_exp_neg_t_anharmonic {lam alpha gamma t : ℝ} (m : ℕ) (hlam : 0 < lam)
    (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ m * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  refine (integrable_abs_pow_mul_exp_neg_t_anharmonic m hlam hgamma hdisc ht).mono' ?_ ?_
  · have : Continuous (fun x : ℝ =>
        x ^ m * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
      unfold anharmonicPotential
      fun_prop
    exact this.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- `ℓ e^{−tℓ}` is integrable for the anharmonic potential. -/
theorem integrable_anharmonic_mul_exp {lam alpha gamma t : ℝ} (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Integrable (fun x : ℝ => anharmonicPotential lam alpha gamma x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  have h2 := (integrable_pow_mul_exp_neg_t_anharmonic 2 hlam hgamma hdisc ht).const_mul (lam / 2)
  have h3 := (integrable_pow_mul_exp_neg_t_anharmonic 3 hlam hgamma hdisc ht).const_mul (alpha / 6)
  have h4 := (integrable_pow_mul_exp_neg_t_anharmonic 4 hlam hgamma hdisc ht).const_mul (gamma / 24)
  refine ((h2.add h3).add h4).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

/-- The energy expectation as a combination of moments:
`⟨ℓ⟩ = (λ/2)⟨x²⟩ + (α/6)⟨x³⟩ + (γ/24)⟨x⁴⟩`. -/
theorem gibbsExpectation_anharmonic_energy {lam alpha gamma t : ℝ} (hlam : 0 < lam)
    (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) =
      lam / 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2) +
        alpha / 6 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) +
        gamma / 24 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) := by
  unfold _root_.Laplace.gibbsExpectation
  have h2 := integrable_pow_mul_exp_neg_t_anharmonic 2 hlam hgamma hdisc ht
  have h3 := integrable_pow_mul_exp_neg_t_anharmonic 3 hlam hgamma hdisc ht
  have h4 := integrable_pow_mul_exp_neg_t_anharmonic 4 hlam hgamma hdisc ht
  have h23 : Integrable (fun x : ℝ =>
      lam / 2 * (x ^ 2 * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) +
        alpha / 6 * (x ^ 3 * Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) :=
    (h2.const_mul _).add (h3.const_mul _)
  have hnum : ∫ x : ℝ, anharmonicPotential lam alpha gamma x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x)) =
      ∫ x : ℝ, (lam / 2 * (x ^ 2 * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) +
        alpha / 6 * (x ^ 3 * Real.exp (-(t * anharmonicPotential lam alpha gamma x)))) +
        gamma / 24 * (x ^ 4 * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integral_congr_ae (Eventually.of_forall fun x => by
      simp only [anharmonicPotential]
      ring)
  rw [hnum, integral_add h23 (h4.const_mul _), integral_add (h2.const_mul _) (h3.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- If `t² f(t)` converges then `t f(t) → 0`. -/
theorem tendsto_mul_of_tendsto_sq_mul {f : ℝ → ℝ} {c : ℝ}
    (h : Tendsto (fun t : ℝ => t ^ 2 * f t) atTop (𝓝 c)) :
    Tendsto (fun t : ℝ => t * f t) atTop (𝓝 0) := by
  have := tendsto_inv_atTop_zero.mul h
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hne := ht.ne'
  field_simp

/-- `t²⟨x⁴⟩ → 3/λ²`, from the explicit second-order rate. -/
theorem fourthMoment_anharmonic_asymptotic {lam alpha gamma : ℝ} (hlam : 0 < lam)
    (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Tendsto (fun t : ℝ => t ^ 2 * _root_.Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4)) atTop (𝓝 (3 / lam ^ 2)) := by
  obtain ⟨K, T, hK, hT, hbd⟩ := fourthMoment_anharmonic_order2_rate hlam hgamma hdisc
  set C : ℝ := (450 * cubicScale lam alpha ^ 2 - 96 * quarticScale lam gamma) / lam ^ 2 with hC
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_
    (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun t : ℝ => (|C| + K) / t) atTop (𝓝 0))
  filter_upwards [eventually_ge_atTop T] with t ht
  have ht1 : 1 ≤ t := hT.trans ht
  have hpos : 0 < t := by linarith
  have h1 : |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 4) - 3 / lam ^ 2 - C / t| ≤ K / (t * Real.sqrt t) := by
    rw [hC, div_div]
    exact hbd ht
  have hsqrt : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1
  have hK' : K / (t * Real.sqrt t) ≤ K / t :=
    div_le_div_of_nonneg_left hK hpos (le_mul_of_one_le_right hpos.le hsqrt)
  have hC' : |C / t| = |C| / t := by rw [abs_div, abs_of_pos hpos]
  have htri := abs_sub_abs_le_abs_sub (t ^ 2 * _root_.Laplace.gibbsExpectation
    (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4) - 3 / lam ^ 2) (C / t)
  rw [Real.norm_eq_abs]
  calc |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 4) - 3 / lam ^ 2|
      ≤ K / t + |C| / t := by rw [← hC']; linarith
    _ = (|C| + K) / t := by ring

/-- **`t⟨ℓ⟩_t → 1/2`**: the exact one-dimensional anharmonic energy has the Laplace value `1/(2t)`
to leading order. -/
theorem energy_anharmonic_asymptotic {lam alpha gamma : ℝ} (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Tendsto (fun t : ℝ => t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma)
        t (anharmonicPotential lam alpha gamma)) atTop (𝓝 (1 / 2)) := by
  have h2 := secondMoment_anharmonic_asymptotic hlam hgamma hdisc
  have h3 := tendsto_mul_of_tendsto_sq_mul (thirdMoment_anharmonic_asymptotic hlam hgamma hdisc)
  have h4 := tendsto_mul_of_tendsto_sq_mul (fourthMoment_anharmonic_asymptotic hlam hgamma hdisc)
  have h := ((h2.const_mul (lam / 2)).add (h3.const_mul (alpha / 6))).add
    (h4.const_mul (gamma / 24))
  have hne := hlam.ne'
  have hlim : lam / 2 * (1 / lam) + alpha / 6 * 0 + gamma / 24 * 0 = 1 / 2 := by
    field_simp
    ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [gibbsExpectation_anharmonic_energy hlam hgamma hdisc ht]
  ring

variable {lam alpha gamma : ι → ℝ}

/-- Each coordinate energy against the separable Boltzmann factor is integrable. -/
theorem integrable_coord_energy_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (i : ι) :
    Integrable (fun w : ι → ℝ => anharmonicPotential (lam i) (alpha i) (gamma i) (w i) *
      Real.exp (-(t * separableAnharmonic lam alpha gamma w))) := by
  classical
  have hf : ∀ j, Integrable (fun x : ℝ =>
      (if j = i then anharmonicPotential (lam j) (alpha j) (gamma j) x else 1) *
        Real.exp (-(t * anharmonicPotential (lam j) (alpha j) (gamma j) x))) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp only [if_true]
      exact integrable_anharmonic_mul_exp (hlam j) (hgamma j) (hdisc j) ht
    · simp only [hji, if_false, one_mul]
      exact integrable_exp_neg_t_anharmonic (hlam j) (hgamma j) (hdisc j) ht
  refine (Integrable.fintype_prod (f := fun j x =>
    (if j = i then anharmonicPotential (lam j) (alpha j) (gamma j) x else 1) *
      Real.exp (-(t * anharmonicPotential (lam j) (alpha j) (gamma j) x))) hf).congr
    (Eventually.of_forall fun w => ?_)
  simp only [separableAnharmonic, exp_separablePotential, Finset.prod_mul_distrib,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]

/-- **The energy is a sum of coordinate energies**: `⟨L⟩_L = ∑ᵢ ⟨ℓᵢ⟩_{ℓᵢ}`. -/
theorem gibbsExpectation_energy_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) :
    gibbsExpectation (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma) =
      ∑ i, _root_.Laplace.gibbsExpectation (anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) := by
  have hsum : gibbsExpectation (separableAnharmonic lam alpha gamma) t
      (separableAnharmonic lam alpha gamma) =
      ∑ i, gibbsExpectation (separableAnharmonic lam alpha gamma) t
        (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (w i)) := by
    unfold gibbsExpectation
    rw [← Finset.sum_div]
    congr 1
    rw [← integral_finsetSum _
      (fun i _ => integrable_coord_energy_separableAnharmonic hlam hgamma hdisc ht i)]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [separableAnharmonic, separablePotential, Finset.sum_mul]
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact gibbsExpectation_coord_separableAnharmonic hlam hgamma hdisc ht i _

/-- **E2's LLC**: for the separable anharmonic oscillator `t⟨L⟩_L → d/2`; the exact LLC tends to the
Laplace value (the note's "at `t = 3` the exact LLC is 4.76, not 5" is the finite-`t` deviation). -/
theorem separableAnharmonic_energy_asymptotic (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) :
    Tendsto (fun t : ℝ => t * gibbsExpectation (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma)) atTop (𝓝 ((Fintype.card ι : ℝ) / 2)) := by
  have h : Tendsto (fun t : ℝ => ∑ i, t * _root_.Laplace.gibbsExpectation
      (anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (anharmonicPotential (lam i) (alpha i) (gamma i))) atTop (𝓝 (∑ _i : ι, (1 / 2 : ℝ))) :=
    tendsto_finsetSum _ fun i _ => energy_anharmonic_asymptotic (hlam i) (hgamma i) (hdisc i)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hlim : (Fintype.card ι : ℝ) * (1 / 2) = Fintype.card ι / 2 := by ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [gibbsExpectation_energy_separableAnharmonic hlam hgamma hdisc ht, Finset.mul_sum]

end Energy

end Laplace.Multi
