/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.SecondOrderLaplace
import Laplace.Multi.ExpansionBridge
import Laplace.Multi.AnalyticGermRecovery

/-!
# Two-radial-probe rigidity of the quadratic germ (germbij Q2)

The elimination layer on top of the second-order expansion
(`tendsto_rescaledMoment_second_order`). If the rescaled moments of the two radial
probes `q = qform H` and `q²` agree with their Gaussian values beyond all orders,
then every Taylor term of `L` of degree `≥ 3` vanishes; for analytic `L` the germ
at the minimum is exactly the quadratic form.

The argument is an induction on the degree `k = ρ + 2`. Given that the terms of
degree `3, …, k − 1` vanish, the second-order expansion at `P = q` and `P = q²`,
combined with coefficient uniqueness (`coeffs_eq_zero_of_tendsto_div_pow`) and the
two radial covariance identities `Cov_γ(q, Q) = k E_γ Q`,
`Cov_γ(q², Q) = k(k + 2d + 2) E_γ Q` (`GaussianStein`), gives `E_γ Q_k = 0` and the
elimination `a_{q²} − (2d + 2k) a_q = 2k E_γ[Q_k²] = 0`; Gaussian covariance
rigidity then forces `Q_k = 0`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-! ### Coefficient uniqueness -/

/-- **Coefficient uniqueness**: a polynomial `∑_{j<n} c_j h^j` that is `O(h^n)` (in the
sense that the quotient by `h^n` converges) at `0⁺` has all coefficients zero, and the
limit is zero. -/
theorem coeffs_eq_zero_of_tendsto_div_pow :
    ∀ (n : ℕ) (c : ℕ → ℝ) (ℓ : ℝ),
      Tendsto (fun h : ℝ ↦ (∑ j ∈ Finset.range n, h ^ j * c j) / h ^ n) (𝓝[>] (0 : ℝ)) (𝓝 ℓ) →
      (∀ j < n, c j = 0) ∧ ℓ = 0 := by
  intro n
  induction n with
  | zero =>
    intro c ℓ hlim
    refine ⟨fun j hj ↦ absurd hj (Nat.not_lt_zero j), ?_⟩
    have h0 : Tendsto (fun h : ℝ ↦ (∑ j ∈ Finset.range 0, h ^ j * c j) / h ^ 0)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, zero_div]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim h0
  | succ n ih =>
    intro c ℓ hlim
    have hsplit : ∀ h : ℝ, (∑ j ∈ Finset.range (n + 1), h ^ j * c j) =
        c 0 + h * ∑ j ∈ Finset.range n, h ^ j * c (j + 1) := by
      intro h
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, one_mul]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    have hp0 : Tendsto (fun h : ℝ ↦ ∑ j ∈ Finset.range (n + 1), h ^ j * c j) (𝓝[>] (0 : ℝ))
        (𝓝 (c 0)) := by
      have hcont : Continuous fun h : ℝ ↦ ∑ j ∈ Finset.range (n + 1), h ^ j * c j := by
        fun_prop
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [hsplit 0, zero_mul, add_zero] at this
    have hpow : Tendsto (fun h : ℝ ↦ h ^ (n + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := ((continuous_pow (n + 1)).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [zero_pow (Nat.succ_ne_zero n)] at this
    have hp0' : Tendsto (fun h : ℝ ↦ ∑ j ∈ Finset.range (n + 1), h ^ j * c j) (𝓝[>] (0 : ℝ))
        (𝓝 0) := by
      have := hlim.mul hpow
      rw [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have : (h : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hh)
      field_simp
    have hc0 : c 0 = 0 := tendsto_nhds_unique hp0 hp0'
    have hq : Tendsto (fun h : ℝ ↦ (∑ j ∈ Finset.range n, h ^ j * c (j + 1)) / h ^ n)
        (𝓝[>] (0 : ℝ)) (𝓝 ℓ) := by
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hne : (h : ℝ) ≠ 0 := ne_of_gt hh
      rw [hsplit h, hc0, zero_add, pow_succ, mul_comm (h ^ n) h, ← div_div,
        mul_div_cancel_left₀ _ hne]
    obtain ⟨hcs, hℓ⟩ := ih (fun j ↦ c (j + 1)) ℓ hq
    refine ⟨fun j hj ↦ ?_, hℓ⟩
    rcases j with _ | j
    · exact hc0
    · exact hcs j (by omega)

/-! ### Certificates for Taylor terms and homogeneous functions -/

/-- Continuous homogeneous functions of positive degree have polynomial growth. -/
theorem hasPolynomialGrowth_of_isHomogeneous {Q : EuclidD d → ℝ} (hQc : Continuous Q)
    {k : ℕ} (hk : 0 < k) (hhom : IsHomogeneousOfDegree k Q) : HasPolynomialGrowth Q := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_isHomogeneous hQc hk hhom
  refine ⟨M, k, hM0, fun x ↦ (hM x).trans ?_⟩
  have := pow_nonneg (norm_nonneg x) k
  nlinarith

/-- **Derivative growth of homogeneous smooth functions**: the directional derivative of
a degree-`k ≥ 2` homogeneous smooth function is homogeneous of degree `k − 1`, hence of
polynomial growth. -/
theorem hasPolynomialGrowth_fderiv_of_isHomogeneous {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q)
    {k : ℕ} (hk : 2 ≤ k) (hhom : IsHomogeneousOfDegree k Q) (v : EuclidD d) :
    HasPolynomialGrowth fun x ↦ fderiv ℝ Q x v := by
  have hcont : Continuous fun x ↦ fderiv ℝ Q x v :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp (hQ.continuous_fderiv (by simp))
  have hhom' : IsHomogeneousOfDegree (k - 1) fun x ↦ fderiv ℝ Q x v := by
    intro s x
    rcases eq_or_ne s 0 with rfl | hs
    · have h0 : iteratedFDeriv ℝ 1 Q 0 = 0 :=
        iteratedFDeriv_zero_of_isHomogeneous hQ hhom (by omega)
      have := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ EuclidD d) ℝ ↦
        T (fun _ ↦ v)) h0
      simp only [iteratedFDeriv_one_apply, zero_apply] at this
      simp only [zero_smul]
      rw [zero_pow (by omega), zero_mul]
      exact this
    · have h := iteratedFDeriv_smul_eq_of_isHomogeneous hQ hhom 1 s x
      have h' := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ EuclidD d) ℝ ↦
        T (fun _ ↦ v)) h
      simp only [smul_apply, iteratedFDeriv_one_apply, smul_eq_mul,
        pow_one] at h'
      have hk' : s ^ k = s * s ^ (k - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      rw [hk'] at h'
      refine mul_left_cancel₀ hs ?_
      rw [h']
      ring
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_isHomogeneous hcont (by omega : 0 < k - 1) hhom'
  refine ⟨M, k - 1, hM0, fun x ↦ (hM x).trans ?_⟩
  have := pow_nonneg (norm_nonneg x) (k - 1)
  nlinarith

/-- Diagonal Taylor terms of positive degree lie in the homogeneous polynomial span. -/
theorem taylorHomogeneousTerm_mem_homogPolySpan (L : EuclidD d → ℝ) {m : ℕ} (hm : m ≠ 0) :
    taylorHomogeneousTerm m L ∈ homogPolySpan d m := by
  have h := taylorDifference_mem_homogPolySpan (k := m) L (fun _ ↦ (0 : ℝ))
  have hz : ∀ x, taylorHomogeneousTerm m (fun _ : EuclidD d ↦ (0 : ℝ)) x = 0 := by
    intro x
    unfold taylorHomogeneousTerm
    rw [iteratedFDeriv_const_of_ne hm]
    simp
  have : (fun x ↦ taylorHomogeneousTerm m L x -
      taylorHomogeneousTerm m (fun _ : EuclidD d ↦ (0 : ℝ)) x) = taylorHomogeneousTerm m L := by
    funext x
    rw [hz x, sub_zero]
  rw [this] at h
  exact h

theorem contDiff_taylorHomogeneousTerm (L : EuclidD d → ℝ) {m : ℕ} (hm : m ≠ 0) :
    ContDiff ℝ ∞ (taylorHomogeneousTerm m L) :=
  contDiff_of_mem_homogPolySpan (taylorHomogeneousTerm_mem_homogPolySpan L hm)

theorem isHomogeneous_taylorHomogeneousTerm (L : EuclidD d → ℝ) (m : ℕ) :
    IsHomogeneousOfDegree m (taylorHomogeneousTerm m L) :=
  fun a x ↦ taylorHomogeneousTerm_smul m L a x

/-- Bilinearity of the covariance at the second-order target `½ Q² − R`. -/
theorem gaussianCovariance_half_sq_sub {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {P Q R : EuclidD d → ℝ} (hPc : Continuous P) (hPg : HasPolynomialGrowth P)
    (hQc : Continuous Q) (hQg : HasPolynomialGrowth Q)
    (hRc : Continuous R) (hRg : HasPolynomialGrowth R) :
    gaussianCovariance H P (fun x ↦ 1 / 2 * Q x ^ 2 - R x) =
      1 / 2 * gaussianCovariance H P (fun x ↦ Q x ^ 2) - gaussianCovariance H P R := by
  have hQ2g : HasPolynomialGrowth fun x ↦ Q x ^ 2 :=
    hasPolynomialGrowth_of_eq (hQg.mul hQg) fun x ↦ sq _
  have hfun : (fun x ↦ 1 / 2 * Q x ^ 2 - R x) =
      ((1 / 2 : ℝ) • fun x ↦ Q x ^ 2) + ((-1 : ℝ) • R) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hc1 : Continuous ((1 / 2 : ℝ) • fun x ↦ Q x ^ 2) := (hQc.pow 2).const_smul _
  have hg1 : HasPolynomialGrowth ((1 / 2 : ℝ) • fun x ↦ Q x ^ 2) := hQ2g.const_smul _
  have hc2 : Continuous ((-1 : ℝ) • R) := hRc.const_smul _
  have hg2 : HasPolynomialGrowth ((-1 : ℝ) • R) := hRg.const_smul _
  rw [hfun, gaussianCovariance_add_right hH hPc hPg hc1 hg1 hc2 hg2,
    gaussianCovariance_const_smul_right, gaussianCovariance_const_smul_right]
  ring

/-! ### Flat second-order data -/

namespace HigherLaplaceDomain

variable {ρ : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- **Consequences of flat second-order data**: if the rescaled moment of `P` agrees with
its Gaussian value to `o(h^{2ρ})`, all intermediate covariances vanish and the top
coefficient vanishes. -/
theorem second_order_coefficients_of_flat (A : HigherLaplaceDomain (2 * ρ + 3) L H)
    (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P) (hP_growth : HasPolynomialGrowth P)
    (hflat : (fun h : ℝ ↦ A.rescaledMoment P h - gaussianExpectation H P)
      =o[𝓝[>] (0 : ℝ)] fun h ↦ h ^ (2 * ρ)) :
    (∀ j < ρ, gaussianCovariance H P (taylorHomogeneousTerm (ρ + j + 2) L) = 0) ∧
    gaussianCovariance H P (fun x ↦ 1 / 2 * taylorHomogeneousTerm (ρ + 2) L x ^ 2 -
        taylorHomogeneousTerm (2 * ρ + 2) L x) -
      gaussianExpectation H (taylorHomogeneousTerm (ρ + 2) L) *
        gaussianCovariance H P (taylorHomogeneousTerm (ρ + 2) L) = 0 := by
  have hexp := A.tendsto_rescaledMoment_second_order hρ hvanish hP_cont hP_growth
  have hflat' := hflat.tendsto_div_nhds_zero
  have hdiff := hexp.sub hflat'
  rw [sub_zero] at hdiff
  have hsum : Tendsto (fun h : ℝ ↦ (∑ j ∈ Finset.range ρ, h ^ j *
      gaussianCovariance H P (taylorHomogeneousTerm (ρ + j + 2) L)) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (gaussianCovariance H P
        (fun x ↦ 1 / 2 * taylorHomogeneousTerm (ρ + 2) L x ^ 2 -
          taylorHomogeneousTerm (2 * ρ + 2) L x) -
        gaussianExpectation H (taylorHomogeneousTerm (ρ + 2) L) *
          gaussianCovariance H P (taylorHomogeneousTerm (ρ + 2) L))) := by
    refine hdiff.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : (h : ℝ) ≠ 0 := ne_of_gt hh
    have hfac : ∑ j ∈ Finset.range ρ, h ^ (ρ + j) *
        gaussianCovariance H P (taylorHomogeneousTerm (ρ + j + 2) L) =
        h ^ ρ * ∑ j ∈ Finset.range ρ, h ^ j *
          gaussianCovariance H P (taylorHomogeneousTerm (ρ + j + 2) L) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [pow_add]
      ring
    rw [← sub_div, add_sub_cancel_left, hfac, show h ^ (2 * ρ) = h ^ ρ * h ^ ρ by
      rw [← pow_add, two_mul], ← div_div, mul_div_cancel_left₀ _ (pow_ne_zero ρ hne)]
  exact coeffs_eq_zero_of_tendsto_div_pow ρ _ _ hsum

/-- **The inductive step of two-radial-probe rigidity**: if the Taylor terms of degree
`3, …, ρ + 1` vanish and the rescaled moments of `q` and `q²` are flat to `o(h^{2ρ})`,
then `T_{ρ+2} L = 0`. -/
theorem taylorHomogeneousTerm_eq_zero_of_two_radial_flat (A : HigherLaplaceDomain (2 * ρ + 3) L H)
    (hρ : 0 < ρ)
    (hvanish : ∀ j, 3 ≤ j → j < ρ + 2 → taylorHomogeneousTerm j L = 0)
    (hq : (fun h : ℝ ↦ A.rescaledMoment (qform H) h - gaussianExpectation H (qform H))
      =o[𝓝[>] (0 : ℝ)] fun h ↦ h ^ (2 * ρ))
    (hq2 : (fun h : ℝ ↦ A.rescaledMoment (fun x ↦ qform H x ^ 2) h -
        gaussianExpectation H (fun x ↦ qform H x ^ 2)) =o[𝓝[>] (0 : ℝ)] fun h ↦ h ^ (2 * ρ)) :
    taylorHomogeneousTerm (ρ + 2) L = 0 := by
  have hH := A.hH_posDef
  have hqc : Continuous (qform H) := qform_continuous H
  have hqg : HasPolynomialGrowth (qform H) := hasPolynomialGrowth_qform H
  have hq2c : Continuous fun x ↦ qform H x ^ 2 := hqc.pow 2
  have hq2g : HasPolynomialGrowth fun x ↦ qform H x ^ 2 :=
    hasPolynomialGrowth_of_eq (hqg.mul hqg) fun x ↦ sq _
  obtain ⟨hcoef, htop⟩ := A.second_order_coefficients_of_flat hρ hvanish hqc hqg hq
  obtain ⟨_, htop2⟩ := A.second_order_coefficients_of_flat hρ hvanish hq2c hq2g hq2
  have h0 := hcoef 0 hρ
  simp only [add_zero] at h0
  -- certificates for `Q = T_{ρ+2}` and `R = T_{2ρ+2}`
  set Q := taylorHomogeneousTerm (ρ + 2) L with hQ_def
  set R := taylorHomogeneousTerm (2 * ρ + 2) L with hR_def
  have hQs : ContDiff ℝ ∞ Q := contDiff_taylorHomogeneousTerm L (by omega)
  have hQhom : IsHomogeneousOfDegree (ρ + 2) Q := isHomogeneous_taylorHomogeneousTerm L _
  have hQc : Continuous Q := hQs.continuous
  have hQg : HasPolynomialGrowth Q := taylorHomogeneousTerm_hasPolynomialGrowth _ L
  have hRs : ContDiff ℝ ∞ R := contDiff_taylorHomogeneousTerm L (by omega)
  have hRhom : IsHomogeneousOfDegree (2 * ρ + 2) R := isHomogeneous_taylorHomogeneousTerm L _
  have hRc : Continuous R := hRs.continuous
  have hRg : HasPolynomialGrowth R := taylorHomogeneousTerm_hasPolynomialGrowth _ L
  have hQ2s : ContDiff ℝ ∞ fun x ↦ Q x ^ 2 := hQs.pow 2
  have hQ2hom : IsHomogeneousOfDegree (2 * ρ + 4) fun x ↦ Q x ^ 2 := by
    intro a x
    simp only []
    rw [hQhom a x]
    ring
  have hQ2g : HasPolynomialGrowth fun x ↦ Q x ^ 2 :=
    hasPolynomialGrowth_of_eq (hQg.mul hQg) fun x ↦ sq _
  -- `E_γ Q = 0` from the leading coefficient at `P = q`
  have hEQ : gaussianExpectation H Q = 0 := by
    rw [gaussianCovariance_qform_of_isHomogeneous hH hQs hQhom hQg
      (hasPolynomialGrowth_fderiv_of_isHomogeneous hQs (by omega) hQhom)] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exfalso
      have : ((ρ + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      exact this h
    · exact h
  -- the two top coefficients in terms of `s = E_γ[Q²]` and `r = E_γ R`
  rw [gaussianCovariance_half_sq_sub hH hqc hqg hQc hQg hRc hRg, hEQ, zero_mul, sub_zero,
    gaussianCovariance_qform_of_isHomogeneous hH hQ2s hQ2hom hQ2g
      (hasPolynomialGrowth_fderiv_of_isHomogeneous hQ2s (by omega) hQ2hom),
    gaussianCovariance_qform_of_isHomogeneous hH hRs hRhom hRg
      (hasPolynomialGrowth_fderiv_of_isHomogeneous hRs (by omega) hRhom)] at htop
  rw [gaussianCovariance_half_sq_sub hH hq2c hq2g hQc hQg hRc hRg, hEQ, zero_mul, sub_zero,
    gaussianCovariance_qform_sq_of_isHomogeneous hH hQ2s hQ2hom hQ2g
      (hasPolynomialGrowth_fderiv_of_isHomogeneous hQ2s (by omega) hQ2hom),
    gaussianCovariance_qform_sq_of_isHomogeneous hH hRs hRhom hRg
      (hasPolynomialGrowth_fderiv_of_isHomogeneous hRs (by omega) hRhom)] at htop2
  push_cast at htop htop2
  -- elimination: `a_{q²} − (2d + 2k) a_q = 2k E_γ[Q²]`
  have hs : gaussianExpectation H (fun x ↦ Q x ^ 2) = 0 := by
    have h3 : (2 * (ρ : ℝ) + 4) * gaussianExpectation H (fun x ↦ Q x ^ 2) = 0 := by
      linear_combination htop2 - (2 * (ρ : ℝ) + 2 * (d : ℝ) + 4) * htop
    rcases mul_eq_zero.mp h3 with h | h
    · exfalso
      have : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
      linarith
    · exact h
  have hvar : gaussianCovariance H Q Q = 0 := by
    unfold gaussianCovariance
    rw [hEQ, mul_zero, sub_zero]
    have : (fun x ↦ Q x * Q x) = fun x ↦ Q x ^ 2 := funext fun x ↦ (sq (Q x)).symm
    rw [this]
    exact hs
  exact homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero hH (by omega : 0 < ρ + 2)
    hQc hQg hQhom hvar

/-! ### All orders -/

/-- The square of the quadratic form is homogeneous of degree `4`. -/
theorem isHomogeneousOfDegree_qform_sq (H : Matrix (Fin d) (Fin d) ℝ) :
    IsHomogeneousOfDegree 4 fun x ↦ qform H x ^ 2 := by
  intro a x
  simp only []
  rw [isHomogeneousOfDegree_qform H a x]
  ring

/-- **Two-radial-probe rigidity, Taylor form**: if for every certified grade the
temperature-level moments `⟨q⟩_{L,t}` and `⟨q²⟩_{L,t}` agree with the Gaussian values
`E_γ q / t` and `E_γ q² / t²` beyond all orders, every Taylor term of `L` of degree
`≥ 3` vanishes. -/
theorem taylorHomogeneousTerm_eq_zero_of_two_radial_superPoly
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L H)
    (hq : ∀ k (h2 : 2 < k), Laplace.SuperPoly (fun t : ℝ ↦
      (A k h2).toLocalLaplaceDomain.posteriorMomentT (qform H) t -
        gaussianExpectation H (qform H) / t))
    (hq2 : ∀ k (h2 : 2 < k), Laplace.SuperPoly (fun t : ℝ ↦
      (A k h2).toLocalLaplaceDomain.posteriorMomentT (fun x ↦ qform H x ^ 2) t -
        gaussianExpectation H (fun x ↦ qform H x ^ 2) / t ^ 2)) :
    ∀ k, 2 < k → taylorHomogeneousTerm k L = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨ρ, rfl⟩ : ∃ ρ, k = ρ + 2 := ⟨k - 2, by omega⟩
    have hρ : 0 < ρ := by omega
    have h2 : 2 < 2 * ρ + 3 := by omega
    refine taylorHomogeneousTerm_eq_zero_of_two_radial_flat (A _ h2) hρ
      (fun j h3 hj ↦ ih j (by omega) (by omega)) ?_ ?_
    · have hlo := isLittleO_pow_of_superPoly (hq _ h2) 2 (2 * ρ)
      refine hlo.congr' ?_ (EventuallyEq.refl _ _)
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh0 : (0 : ℝ) < h := hh
      have hne : (h : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hh0.ne'
      rw [LocalLaplaceDomain.posteriorMomentT_inv_sq _ _ hh0,
        LocalLaplaceDomain.posteriorMoment_eq_pow_mul _ (isHomogeneousOfDegree_qform H) hh0]
      unfold rescaledMoment
      field_simp
    · have hlo := isLittleO_pow_of_superPoly (hq2 _ h2) 4 (2 * ρ)
      refine hlo.congr' ?_ (EventuallyEq.refl _ _)
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh0 : (0 : ℝ) < h := hh
      have hne : (h : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hh0.ne'
      rw [LocalLaplaceDomain.posteriorMomentT_inv_sq _ _ hh0,
        LocalLaplaceDomain.posteriorMoment_eq_pow_mul _ (isHomogeneousOfDegree_qform_sq H) hh0]
      unfold rescaledMoment
      field_simp

/-- **Two-radial-probe rigidity, tensor form**: under the same data, every derivative
tensor of order `≥ 3` at the minimum vanishes (given the symmetry of the tensors). -/
theorem iteratedFDeriv_eq_zero_of_two_radial_superPoly
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L H)
    (hq : ∀ k (h2 : 2 < k), Laplace.SuperPoly (fun t : ℝ ↦
      (A k h2).toLocalLaplaceDomain.posteriorMomentT (qform H) t -
        gaussianExpectation H (qform H) / t))
    (hq2 : ∀ k (h2 : 2 < k), Laplace.SuperPoly (fun t : ℝ ↦
      (A k h2).toLocalLaplaceDomain.posteriorMomentT (fun x ↦ qform H x ^ 2) t -
        gaussianExpectation H (fun x ↦ qform H x ^ 2) / t ^ 2))
    (hsymm : ∀ k, 2 < k → (iteratedFDeriv ℝ k L 0).IsSymm) :
    ∀ k, 2 < k → iteratedFDeriv ℝ k L 0 = 0 := by
  intro k hk
  have hT := taylorHomogeneousTerm_eq_zero_of_two_radial_superPoly A hq hq2 k hk
  have hdiag : ∀ x : EuclidD d, iteratedFDeriv ℝ k L 0 (fun _ ↦ x) =
      (0 : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ EuclidD d) ℝ) (fun _ ↦ x) := by
    intro x
    have hx := congrFun hT x
    unfold taylorHomogeneousTerm at hx
    simp only [Pi.zero_apply] at hx
    rw [zero_apply]
    have hfac : ((k.factorial : ℝ))⁻¹ ≠ 0 :=
      inv_ne_zero (by exact_mod_cast k.factorial_ne_zero)
    exact (mul_eq_zero.mp hx).resolve_left hfac
  exact ContinuousMultilinearMap.eq_of_diag_eq _ _ (hsymm k hk) (fun _ _ ↦ by simp) hdiag

/-- The quadratic form is analytic. -/
theorem analyticAt_qform (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    AnalyticAt ℝ (qform H) x := by
  have h1 : AnalyticAt ℝ (fun y : EuclidD d ↦
      (innerSL ℝ (E := EuclidD d)) y (Matrix.toEuclideanCLM (𝕜 := ℝ) H y)) x :=
    ((innerSL ℝ (E := EuclidD d)).analyticAt_bilinear
      (x, Matrix.toEuclideanCLM (𝕜 := ℝ) H x)).comp₂ analyticAt_id
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) H).analyticAt x)
  convert h1 using 2 with y
  simp [qform]

/-- **Two-radial-probe rigidity of the quadratic germ** (germbij Q2): a loss analytic at
its minimum whose radial moments `⟨q⟩_{L,t}`, `⟨q²⟩_{L,t}` agree with the Gaussian values
beyond all orders in the temperature is, near the minimum, exactly its quadratic part. -/
theorem quadratic_germ_rigid_of_two_radial_superPoly
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L H)
    (hq : ∀ k (h2 : 2 < k), Laplace.SuperPoly (fun t : ℝ ↦
      (A k h2).toLocalLaplaceDomain.posteriorMomentT (qform H) t -
        gaussianExpectation H (qform H) / t))
    (hq2 : ∀ k (h2 : 2 < k), Laplace.SuperPoly (fun t : ℝ ↦
      (A k h2).toLocalLaplaceDomain.posteriorMomentT (fun x ↦ qform H x ^ 2) t -
        gaussianExpectation H (fun x ↦ qform H x ^ 2) / t ^ 2))
    (hL : AnalyticAt ℝ L 0) :
    ∀ᶠ y in 𝓝 (0 : EuclidD d), L y - L 0 = qform H y / 2 := by
  have hT := taylorHomogeneousTerm_eq_zero_of_two_radial_superPoly A hq hq2
  have hA3 := A 3 (by norm_num)
  -- the quadratic reference `g y = L 0 + qform H y * (1/2)`
  have hsm : ContDiff ℝ ∞ fun y : EuclidD d ↦ qform H y * (1 / 2) :=
    (contDiff_qform H).mul contDiff_const
  have hhom2 : IsHomogeneousOfDegree 2 fun y : EuclidD d ↦ qform H y * (1 / 2) := by
    intro a x
    simp only []
    rw [isHomogeneousOfDegree_qform H a x]
    ring
  have hqA : AnalyticAt ℝ (fun y : EuclidD d ↦ qform H y * (1 / 2)) 0 :=
    (analyticAt_qform H 0).mul analyticAt_const
  have hgA : AnalyticAt ℝ ((fun _ : EuclidD d ↦ L 0) + fun y ↦ qform H y * (1 / 2)) 0 :=
    analyticAt_const.add hqA
  have hjet : ∀ n : ℕ, 0 < n → iteratedFDeriv ℝ n L 0 =
      iteratedFDeriv ℝ n ((fun _ : EuclidD d ↦ L 0) + fun y ↦ qform H y * (1 / 2)) 0 := by
    intro n hn
    rw [iteratedFDeriv_add_apply contDiffAt_const (hsm.contDiffAt.of_le (mod_cast le_top)),
      iteratedFDeriv_const_of_ne hn.ne', Pi.zero_apply, zero_add]
    rcases lt_trichotomy n 2 with h | rfl | h
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [hA3.iteratedFDeriv_one_eq_zero (by norm_num),
        iteratedFDeriv_zero_of_isHomogeneous hsm hhom2 (by norm_num)]
    · refine iteratedFDeriv_eq_of_diag_eq_of_contDiffAt_omega hL.contDiffAt hqA.contDiffAt
        fun x ↦ ?_
      rw [hA3.iteratedFDeriv_two_diag (by norm_num) x,
        iteratedFDeriv_diag_of_isHomogeneous hsm hhom2 x]
      norm_num [Nat.factorial]
      ring
    · rw [iteratedFDeriv_zero_of_isHomogeneous hsm hhom2 (by omega)]
      have hdiag : ∀ x : EuclidD d, iteratedFDeriv ℝ n L 0 (fun _ ↦ x) =
          iteratedFDeriv ℝ n (fun _ : EuclidD d ↦ (0 : ℝ)) 0 (fun _ ↦ x) := by
        intro x
        have hx := congrFun (hT n h) x
        unfold taylorHomogeneousTerm at hx
        simp only [Pi.zero_apply] at hx
        rw [iteratedFDeriv_const_of_ne hn.ne', Pi.zero_apply, zero_apply]
        have hfac : ((n.factorial : ℝ))⁻¹ ≠ 0 :=
          inv_ne_zero (by exact_mod_cast n.factorial_ne_zero)
        exact (mul_eq_zero.mp hx).resolve_left hfac
      rw [iteratedFDeriv_eq_of_diag_eq_of_contDiffAt_omega hL.contDiffAt
        analyticAt_const.contDiffAt hdiag, iteratedFDeriv_const_of_ne hn.ne', Pi.zero_apply]
  have hgerm := analytic_germ_eq_of_jet_eq hL hgA hjet
  filter_upwards [hgerm] with y hy
  rw [hy]
  simp only [Pi.add_apply]
  have h0 : qform H 0 = 0 := by
    have := isHomogeneousOfDegree_qform H 0 0
    rw [zero_smul] at this
    linarith [this]
  rw [h0]
  ring

end HigherLaplaceDomain

end Laplace.Multi
