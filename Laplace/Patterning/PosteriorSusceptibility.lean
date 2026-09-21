/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Multi.CovarianceSharp

/-!
# The posterior susceptibility at leading order (eq. chi_laplace)

Proposition 3.2 of the working note *Patterning flow*, eq. *(chi_laplace)*: under the localized
tempered posterior `p ∝ exp(-t L(w) - (tρ/2)‖w‖²)` (minimum placed at the origin, `t = nβ`),
`Cov_p[φ, ℓ] = aᵀ (H + ρ)⁻¹ g / t + O(t⁻²)`, hence `χ_{φℓ} = -β Cov_p[φ, ℓ] = -(1/n) aᵀ(H+ρ)⁻¹g`
to leading order. This is the primer's Lemma `lem:laplace_cov` (formalised as
`Laplace.Multi.gibbsCov_first_order_rate_sharp`) applied to the localized potential
`V = L + (ρ/2)‖·‖²`, whose Hessian is `H + ρ·id`.

**Scaling convention.** The localizer is scaled with the temperature: the weight is
`exp(-t V)` with `V = L + (ρ/2)‖w‖²`, so `ρ` is fixed as `t → ∞`. The note's `ρ = γ/(nβ)` at
fixed `γ` is a different limit (the localizer then disappears at leading order); the two agree
for the pair `(γ, nβ)` with `γ = ρ nβ`.

* `potentialJetApprox_localized`: the sharp potential package of `L` at Hessian `H` transfers to
  `L + (ρ/2)‖·‖²` at Hessian `H + ρ·id` for every `ρ ≥ 0`, with the same cubic jet and constants;
* `laplaceCovHypotheses_localized`: the Gaussian-input package at `H + ρ·id` from the one at `H`,
  given a right inverse `Rinv` of `H + ρ·id` and the Fubini–IBP identity for the shifted Gaussian
  (the two inputs the primer formalisation itself takes as hypotheses);
* `posterior_susceptibility_leading`: `|t Cov_t[φ, ℓ] - aᵀ Rinv g| ≤ K/t` for `t ≥ T₀`;
* `susceptibility_leading`: `|χ + (1/n) aᵀ Rinv g| ≤ β K/(nβ)²` with `χ = -β Cov_{nβ}[φ, ℓ]`.
-/

namespace Laplace.Patterning

open MeasureTheory Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The localized potential `L + (ρ/2)‖w‖²` (sup-norm coordinates: `∑ i, (w i)²`). -/
noncomputable def localized (L : (ι → ℝ) → ℝ) (ρ : ℝ) (w : ι → ℝ) : ℝ :=
  L w + ρ / 2 * ∑ i, (w i) ^ 2

/-- The shifted Hessian `H + ρ·id`. -/
noncomputable def shiftedHessian (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (ρ : ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  H + ρ • ContinuousLinearMap.id ℝ (ι → ℝ)

lemma shiftedHessian_apply (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (ρ : ℝ) (w : ι → ℝ) :
    shiftedHessian H ρ w = H w + ρ • w := by
  simp [shiftedHessian]

/-- `quadForm (H + ρ·id) w = quadForm H w + ρ ∑ i, (w i)²`. -/
lemma quadForm_shiftedHessian (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (ρ : ℝ) (w : ι → ℝ) :
    quadForm (shiftedHessian H ρ) w = quadForm H w + ρ * ∑ i, (w i) ^ 2 := by
  unfold quadForm
  simp only [shiftedHessian_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma sum_sq_nonneg (w : ι → ℝ) : 0 ≤ ∑ i, (w i) ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- `∑ i, (w i)² ≤ card ι · ‖w‖²` for the sup norm. -/
lemma sum_sq_le_card_mul_norm_sq (w : ι → ℝ) :
    ∑ i, (w i) ^ 2 ≤ (Fintype.card ι : ℝ) * ‖w‖ ^ 2 := by
  have h : ∀ i, (w i) ^ 2 ≤ ‖w‖ ^ 2 := fun i => by
    have := norm_le_pi_norm w i
    rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (w i), sq_abs (w i), norm_nonneg w]
  calc ∑ i, (w i) ^ 2 ≤ ∑ _i : ι, ‖w‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card ι : ℝ) * ‖w‖ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The Gaussian weight at the shifted Hessian is dominated by the one at `H` for `ρ ≥ 0`. -/
lemma gaussianWeight_shiftedHessian_le (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (u : ι → ℝ) : gaussianWeight (shiftedHessian H ρ) u ≤ gaussianWeight H u := by
  unfold gaussianWeight
  rw [quadForm_shiftedHessian]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hρ (sum_sq_nonneg u)]

/-- Polynomial growth is preserved by adding the quadratic localizer. -/
lemma hasPolyGrowth_localized (L : (ι → ℝ) → ℝ) (hL : HasPolyGrowth L) (ρ : ℝ) :
    HasPolyGrowth (localized L ρ) := by
  obtain ⟨K, p, hK, hbound⟩ := hL
  refine ⟨2 * K + |ρ| / 2 * Fintype.card ι, p + 2, by positivity, fun w => ?_⟩
  have hnorm : 0 ≤ ‖w‖ := norm_nonneg w
  have h1 : ‖w‖ ^ p ≤ 1 + ‖w‖ ^ (p + 2) := by
    rcases le_total ‖w‖ 1 with h | h
    · have := pow_le_one₀ hnorm h (n := p)
      linarith [pow_nonneg hnorm (p + 2)]
    · have := pow_le_pow_right₀ h (Nat.le_add_right p 2)
      linarith
  have h2 : ‖w‖ ^ 2 ≤ 1 + ‖w‖ ^ (p + 2) := by
    rcases le_total ‖w‖ 1 with h | h
    · have := pow_le_one₀ hnorm h (n := 2)
      linarith [pow_nonneg hnorm (p + 2)]
    · have := pow_le_pow_right₀ h (Nat.le_add_left 2 p)
      linarith
  have hsum := sum_sq_le_card_mul_norm_sq w
  have hsum0 := sum_sq_nonneg w
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  unfold localized
  calc |L w + ρ / 2 * ∑ i, (w i) ^ 2|
      ≤ |L w| + |ρ / 2 * ∑ i, (w i) ^ 2| := abs_add_le _ _
    _ = |L w| + |ρ| / 2 * ∑ i, (w i) ^ 2 := by
        rw [abs_mul, abs_of_nonneg hsum0, abs_div, abs_two]
    _ ≤ K * (1 + ‖w‖ ^ p) + |ρ| / 2 * (Fintype.card ι * ‖w‖ ^ 2) := by
        gcongr
        exact hbound w
    _ ≤ (2 * K + |ρ| / 2 * Fintype.card ι) * (1 + ‖w‖ ^ (p + 2)) := by
        nlinarith [mul_nonneg hK (sub_nonneg.mpr h1), mul_nonneg (abs_nonneg ρ)
          (mul_nonneg hcard (sub_nonneg.mpr h2)), pow_nonneg hnorm (p + 2), abs_nonneg ρ]

/-- **The sharp potential package transfers to the localized potential**, with the Hessian
shifted to `H + ρ·id`, the same cubic jet and the same constants. -/
noncomputable def potentialJetApprox_localized {L : (ι → ℝ) → ℝ} {H : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hL : PotentialJetApprox L H) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    PotentialJetApprox (localized L ρ) (shiftedHessian H ρ) where
  V_continuous := by
    unfold localized
    exact hL.V_continuous.add (by fun_prop)
  V_zero := by simp [localized, hL.V_zero]
  local_radius := hL.local_radius
  local_const := hL.local_const
  local_radius_pos := hL.local_radius_pos
  local_const_nonneg := hL.local_const_nonneg
  local_bound := fun w hw => by
    have := hL.local_bound w hw
    unfold localized
    rw [quadForm_shiftedHessian]
    convert this using 2
    ring
  coercive_const := hL.coercive_const
  coercive_const_pos := hL.coercive_const_pos
  coercive_bound := fun w => by
    have := hL.coercive_bound w
    unfold localized
    nlinarith [mul_nonneg hρ (sum_sq_nonneg w)]
  poly_growth := hasPolyGrowth_localized L hL.poly_growth ρ
  cV := hL.cV
  cV_continuous := hL.cV_continuous
  cV_odd := hL.cV_odd
  cV_bound_const := hL.cV_bound_const
  cV_bound_const_nonneg := hL.cV_bound_const_nonneg
  cV_bound := hL.cV_bound
  jet_radius := hL.jet_radius
  jet_const := hL.jet_const
  jet_radius_pos := hL.jet_radius_pos
  jet_const_nonneg := hL.jet_const_nonneg
  jet_bound := fun w hw => by
    have := hL.jet_bound w hw
    unfold localized
    rw [quadForm_shiftedHessian]
    convert this using 2
    ring
  int_norm_pow_gW := fun k => by
    refine (hL.int_norm_pow_gW k).mono' ?_ ?_
    · exact ((continuous_norm.pow k).mul
        (continuous_gaussianWeight (shiftedHessian H ρ))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg u) k)
        (gaussianWeight_pos _ u).le)]
      exact mul_le_mul_of_nonneg_left (gaussianWeight_shiftedHessian_le H hρ u)
        (pow_nonneg (norm_nonneg u) k)
  H_coercive_const := hL.H_coercive_const
  H_coercive_const_pos := hL.H_coercive_const_pos
  H_coercive_bound := fun u => by
    have := hL.H_coercive_bound u
    rw [quadForm_shiftedHessian]
    nlinarith [mul_nonneg hρ (sum_sq_nonneg u)]

/-- The shifted Hessian is injective, from the coercivity of its quadratic form. -/
lemma shiftedHessian_injective {L : (ι → ℝ) → ℝ} {H : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hL : PotentialJetApprox L H) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Function.Injective (shiftedHessian H ρ) := by
  have hpos := hL.H_coercive_const_pos
  intro x y hxy
  have hz : shiftedHessian H ρ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hq : quadForm (shiftedHessian H ρ) (x - y) = 0 := by
    unfold quadForm
    simp [hz]
  have hcoer := hL.H_coercive_bound (x - y)
  have hq2 := quadForm_shiftedHessian H ρ (x - y)
  rw [hq] at hq2
  have hsum := mul_nonneg hρ (sum_sq_nonneg (x - y))
  have hn : hL.H_coercive_const * ‖x - y‖ ^ 2 ≤ 0 := by linarith
  have hs : ‖x - y‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have h0 : ‖x - y‖ ^ 2 = 0 := le_antisymm hs (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0))

/-- **The Gaussian-input package at the shifted Hessian.** Given the package at `H`, a right
inverse `Rinv` of `H + ρ·id`, and the Fubini–IBP identity for the shifted Gaussian (the two
inputs that are genuinely new), everything else transfers. -/
theorem laplaceCovHypotheses_localized {L : (ι → ℝ) → ℝ} {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hL : PotentialJetApprox L H) (hG : LaplaceCovHypotheses H Hinv) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (Rinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hR : (shiftedHessian H ρ).comp Rinv = ContinuousLinearMap.id ℝ (ι → ℝ))
    (hfub : ∀ i j : ι, FubiniIBPHypothesis (shiftedHessian H ρ) i j) :
    LaplaceCovHypotheses (shiftedHessian H ρ) Rinv where
  H_symm := fun x y => by
    have h := hG.H_symm x y
    simp only [shiftedHessian_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  H_inv_right := hR
  H_inj := shiftedHessian_injective hL hρ
  Z_pos := by
    have hint := (potentialJetApprox_localized hL hρ).int_norm_pow_gW 0
    simp only [pow_zero, one_mul] at hint
    unfold gaussianZ
    unfold gaussianWeight at hint ⊢
    exact integral_exp_pos hint
  int_gW := by
    have hint := (potentialJetApprox_localized hL hρ).int_norm_pow_gW 0
    simpa using hint
  int_uk_uj_gW := fun k j => by
    have hint := (potentialJetApprox_localized hL hρ).int_norm_pow_gW 2
    refine hint.mono' ?_ ?_
    · exact (((continuous_apply k).mul (continuous_apply j)).mul
        (continuous_gaussianWeight (shiftedHessian H ρ))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun u => ?_
      have hk := norm_le_pi_norm u k
      have hj := norm_le_pi_norm u j
      rw [Real.norm_eq_abs] at hk hj
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hgW : 0 ≤ gaussianWeight (shiftedHessian H ρ) u := (Real.exp_pos _).le
      rw [abs_of_nonneg hgW]
      apply mul_le_mul_of_nonneg_right _ hgW
      nlinarith [abs_nonneg (u k), abs_nonneg (u j), norm_nonneg u]
  int_uj_Hi_gW := fun j i => by
    have hint := ((potentialJetApprox_localized hL hρ).int_norm_pow_gW 2).const_mul
      ‖shiftedHessian H ρ‖
    refine hint.mono' ?_ ?_
    · exact (((continuous_apply j).mul
        ((continuous_apply i).comp (shiftedHessian H ρ).continuous)).mul
        (continuous_gaussianWeight (shiftedHessian H ρ))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun u => ?_
      have hj := norm_le_pi_norm u j
      have hi := norm_le_pi_norm (shiftedHessian H ρ u) i
      have hop := (shiftedHessian H ρ).le_opNorm u
      rw [Real.norm_eq_abs] at hj hi
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hgW : 0 ≤ gaussianWeight (shiftedHessian H ρ) u := (Real.exp_pos _).le
      rw [abs_of_nonneg hgW]
      have h1 : |u j| * |shiftedHessian H ρ u i| ≤ ‖shiftedHessian H ρ‖ * ‖u‖ ^ 2 := by
        calc |u j| * |shiftedHessian H ρ u i|
            ≤ ‖u‖ * (‖shiftedHessian H ρ‖ * ‖u‖) :=
              mul_le_mul hj (hi.trans hop) (abs_nonneg _) (norm_nonneg _)
          _ = ‖shiftedHessian H ρ‖ * ‖u‖ ^ 2 := by ring
      calc |u j| * |shiftedHessian H ρ u i| * gaussianWeight (shiftedHessian H ρ) u
          ≤ ‖shiftedHessian H ρ‖ * ‖u‖ ^ 2 * gaussianWeight (shiftedHessian H ρ) u :=
            mul_le_mul_of_nonneg_right h1 hgW
        _ = ‖shiftedHessian H ρ‖ * (‖u‖ ^ 2 * gaussianWeight (shiftedHessian H ρ) u) := by ring
  fubini_ibp := hfub

/-- **Equation (chi_laplace).** For the localized posterior `exp(-t (L + (ρ/2)‖·‖²))`,
`|t Cov_t[φ, ℓ] - aᵀ Rinv g| ≤ K / t` for `t ≥ T₀`, with `Rinv` the inverse of `H + ρ·id`:
the covariance is `aᵀ(H + ρ)⁻¹ g / t + O(t⁻²)`. -/
theorem posterior_susceptibility_leading [Nonempty ι] {L φ ℓ : (ι → ℝ) → ℝ}
    {H Rinv : (ι → ℝ) →L[ℝ] (ι → ℝ)} {a g : ι → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hL : PotentialJetApprox L H) (hφ : ObservableJetApprox φ a) (hℓ : ObservableJetApprox ℓ g)
    (hG : LaplaceCovHypotheses (shiftedHessian H ρ) Rinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * gibbsCov (localized L ρ) t φ ℓ - dot a (Rinv g)| ≤ K / t :=
  gibbsCov_first_order_rate_sharp (localized L ρ) φ ℓ (shiftedHessian H ρ) Rinv a g
    (potentialJetApprox_localized hL hρ) hφ hℓ hG

/-- **The susceptibility.** With `t = nβ` and `χ = -β Cov_{nβ}[φ, ℓ]`,
`|χ + (1/n) aᵀ Rinv g| ≤ β K / (nβ)²`: `χ_{φℓ} = -(1/n) aᵀ (H + ρ)⁻¹ g + O((nβ)⁻²)`. -/
theorem susceptibility_leading [Nonempty ι] {L φ ℓ : (ι → ℝ) → ℝ}
    {H Rinv : (ι → ℝ) →L[ℝ] (ι → ℝ)} {a g : ι → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hL : PotentialJetApprox L H) (hφ : ObservableJetApprox φ a) (hℓ : ObservableJetApprox ℓ g)
    (hG : LaplaceCovHypotheses (shiftedHessian H ρ) Rinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ n β : ℝ, 0 < n → 0 < β → T₀ ≤ n * β →
      |-β * gibbsCov (localized L ρ) (n * β) φ ℓ + (1 / n) * dot a (Rinv g)|
        ≤ β * K / (n * β) ^ 2 := by
  obtain ⟨K, T₀, hT₀, hK⟩ := posterior_susceptibility_leading hρ hL hφ hℓ hG
  refine ⟨K, T₀, hT₀, fun n β hn hβ ht => ?_⟩
  have htpos : 0 < n * β := mul_pos hn hβ
  have h := hK (n * β) ht
  have hK0 : 0 ≤ K / (n * β) := by
    have := abs_nonneg (n * β * gibbsCov (localized L ρ) (n * β) φ ℓ - dot a (Rinv g))
    linarith
  have heq : -β * gibbsCov (localized L ρ) (n * β) φ ℓ + (1 / n) * dot a (Rinv g)
      = -(β / (n * β)) * (n * β * gibbsCov (localized L ρ) (n * β) φ ℓ - dot a (Rinv g)) := by
    field_simp
    ring
  rw [heq, abs_mul, abs_neg, abs_of_pos (div_pos hβ htpos)]
  calc β / (n * β) * |n * β * gibbsCov (localized L ρ) (n * β) φ ℓ - dot a (Rinv g)|
      ≤ β / (n * β) * (K / (n * β)) := by gcongr
    _ = β * K / (n * β) ^ 2 := by
        field_simp

end Laplace.Patterning
