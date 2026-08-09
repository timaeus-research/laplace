/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Anchoring
import Laplace.Multi.HessianMoments
import Laplace.Multi.MonomialTests

/-!
# The expansion bridge: recovery in the note's own language

The merged jet-recovery theorems consume rate hypotheses — pairwise
rescaled moments matching to `o(q^(k-2))` — while the germbij note's
Theorem 3.1 speaks of equal asymptotic expansion families: moment
functions of the temperature agreeing beyond all orders. This file
closes the gap. `posteriorMoment` is the normalized localized moment
(the dilation prefactors cancel in the quotient), and for a
degree-`k` homogeneous observable it equals `q^k` times the rescaled
moment of the recovery machinery. A superpolynomially small
difference of temperature-level moment functions transports, through
the `t = q⁻²` substitution and a fixed-power division, to every
`o(q^r)` rate — in particular the `o(q^(k-2))` the recovery theorems
need. The headline `smooth_jet_recovery_of_superPoly_moments` then
states jet recovery from data in the note's own terms: monomial
moment families equal modulo superpolynomial error force equal
derivative tensors at every order.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d : ℕ}

/-! ## The filter bridge -/

/-- The substitution `t = q⁻²` sends `q → 0⁺` to `t → ∞`. -/
theorem tendsto_inv_sq_atTop :
    Tendsto (fun q : ℝ ↦ ((q ^ 2)⁻¹ : ℝ)) (𝓝[>] (0 : ℝ)) atTop := by
  have h : Tendsto (fun q : ℝ ↦ q ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h2 : Tendsto (fun q : ℝ ↦ q ^ 2) (𝓝 (0 : ℝ))
          (𝓝 ((0 : ℝ) ^ 2)) := (continuous_pow 2).tendsto (0 : ℝ)
      rw [show ((0 : ℝ) ^ 2) = 0 from by norm_num] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact pow_pos (Set.mem_Ioi.mp hq) 2
  exact tendsto_inv_nhdsGT_zero.comp h

/-- **Rate transport**: a superpolynomially small function of the
temperature becomes, after the substitution `t = q⁻²` and division
by any fixed power of `q`, smaller than every power of `q` at
`0⁺`. -/
theorem isLittleO_pow_of_superPoly {f : ℝ → ℝ}
    (hf : Laplace.SuperPoly f) (m r : ℕ) :
    (fun q : ℝ ↦ f ((q ^ 2)⁻¹) / q ^ m) =o[𝓝[>] (0 : ℝ)]
      fun q : ℝ ↦ q ^ r := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, m + r ≤ 2 * N := ⟨m + r, by omega⟩
  have hcomp := (hf N).comp_tendsto tendsto_inv_sq_atTop
  have hev : (fun q : ℝ ↦ (((q ^ 2)⁻¹ : ℝ)) ^ (-(N : ℝ)))
      =ᶠ[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (2 * N) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq2 : (0 : ℝ) < q ^ 2 := pow_pos (Set.mem_Ioi.mp hq) 2
    rw [Real.inv_rpow hq2.le, Real.rpow_neg hq2.le, inv_inv,
      Real.rpow_natCast, ← pow_mul]
  have h1 : (fun q : ℝ ↦ f ((q ^ 2)⁻¹)) =o[𝓝[>] (0 : ℝ)]
      fun q : ℝ ↦ q ^ (2 * N) :=
    hcomp.congr' (Filter.EventuallyEq.refl _ _) hev
  have h2 : (fun q : ℝ ↦ f ((q ^ 2)⁻¹) / q ^ m) =o[𝓝[>] (0 : ℝ)]
      fun q : ℝ ↦ q ^ (2 * N) * (q ^ m)⁻¹ := by
    have := h1.mul_isBigO
      (isBigO_refl (fun q : ℝ ↦ ((q ^ m)⁻¹ : ℝ)) (𝓝[>] (0 : ℝ)))
    refine this.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with q
    rw [div_eq_mul_inv]
  refine h2.trans_isBigO ?_
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (one_pos : (0:ℝ) < 1)] with q hq
  obtain ⟨hq0, hq1⟩ := hq
  have hqm : (0 : ℝ) < q ^ m := pow_pos hq0 m
  have hkey : q ^ (2 * N) * (q ^ m)⁻¹ =
      q ^ r * q ^ (2 * N - m - r) := by
    have h2N : 2 * N = r + (2 * N - m - r) + m := by omega
    calc q ^ (2 * N) * (q ^ m)⁻¹
        = q ^ (r + (2 * N - m - r) + m) * (q ^ m)⁻¹ := by rw [← h2N]
      _ = q ^ r * q ^ (2 * N - m - r) * q ^ m * (q ^ m)⁻¹ := by
          rw [pow_add, pow_add]
      _ = q ^ r * q ^ (2 * N - m - r) :=
          mul_inv_cancel_right₀ hqm.ne' _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hkey, abs_mul,
    abs_of_pos (pow_pos hq0 r), abs_of_pos (pow_pos hq0 _), one_mul]
  calc q ^ r * q ^ (2 * N - m - r) ≤ q ^ r * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_pos hq0 r).le
        exact pow_le_one₀ hq0.le hq1.le
    _ = q ^ r := mul_one _

/-! ## The temperature-level moment -/

namespace LocalLaplaceDomain

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The normalized localized posterior moment at scale `q`
(temperature `t = q⁻²`). -/
noncomputable def posteriorMoment (A : LocalLaplaceDomain L H)
    (f : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  A.posteriorIntegral f q / A.posteriorIntegral (fun _ ↦ 1) q

/-- The same moment parametrized by the temperature. -/
noncomputable def posteriorMomentT (A : LocalLaplaceDomain L H)
    (f : EuclidD d → ℝ) (t : ℝ) : ℝ :=
  A.posteriorMoment f (Real.sqrt t)⁻¹

/-- The two parametrizations agree along the substitution. -/
theorem posteriorMomentT_inv_sq (A : LocalLaplaceDomain L H)
    (f : EuclidD d → ℝ) {q : ℝ} (hq : 0 < q) :
    A.posteriorMomentT f ((q ^ 2)⁻¹) = A.posteriorMoment f q := by
  unfold posteriorMomentT
  rw [Real.sqrt_inv, Real.sqrt_sq hq.le, inv_inv]

/-- The rescaled integrand scales linearly in the observable. -/
theorem integrand_const_mul (A : LocalLaplaceDomain L H)
    (c : ℝ) (h : EuclidD d → ℝ) (q : ℝ) (x : EuclidD d) :
    A.integrand (fun y ↦ c * h y) q x = c * A.integrand h q x := by
  unfold integrand
  by_cases hm : x ∈ {x : EuclidD d | q • x ∈ A.U}
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
    ring
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm,
      mul_zero]

/-- **The homogeneity identity**: for a degree-`k` homogeneous
observable, the temperature-level normalized moment is `q^k` times
the rescaled moment of the recovery machinery. The dilation
prefactors cancel in the quotient. -/
theorem posteriorMoment_eq_pow_mul (A : LocalLaplaceDomain L H)
    {P : EuclidD d → ℝ} {k : ℕ} (hP : IsHomogeneousOfDegree k P)
    {q : ℝ} (hq : 0 < q) :
    A.posteriorMoment P q =
      q ^ k * ((∫ x : EuclidD d, A.integrand P q x) /
        ∫ x : EuclidD d, A.integrand (fun _ ↦ 1) q x) := by
  unfold posteriorMoment
  rw [A.posteriorIntegral_eq P hq, A.posteriorIntegral_eq _ hq]
  have hnum : ∫ x : EuclidD d, A.integrand (fun x ↦ P (q • x)) q x =
      q ^ k * ∫ x : EuclidD d, A.integrand P q x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [show (fun x : EuclidD d ↦ P (q • x)) =
        fun x : EuclidD d ↦ q ^ k * P x from
      funext fun x ↦ hP q x]
    exact A.integrand_const_mul (q ^ k) P q x
  have hden : (fun x : EuclidD d ↦
      A.integrand (fun x ↦ (fun _ : EuclidD d ↦ (1:ℝ)) (q • x)) q x) =
      fun x : EuclidD d ↦ A.integrand (fun _ ↦ 1) q x := rfl
  rw [hnum]
  have hpref : (0 : ℝ) < q ^ d * Real.exp (-(L 0 / q ^ 2)) := by
    positivity
  rw [show q ^ d * Real.exp (-(L 0 / q ^ 2)) *
        (q ^ k * ∫ x : EuclidD d, A.integrand P q x) =
      (q ^ d * Real.exp (-(L 0 / q ^ 2))) *
        (q ^ k * ∫ x : EuclidD d, A.integrand P q x) from by ring]
  rw [mul_div_mul_left _ _ hpref.ne', mul_div_assoc]

end LocalLaplaceDomain

/-! ## The headline: recovery from superpolynomially-equal moments -/

namespace HigherLaplaceDomain

variable {L₁ L₂ : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The rescaled moment is the temperature-level moment divided by
the homogeneity power. -/
theorem rescaledMoment_eq_posteriorMoment_div {k : ℕ}
    (A : HigherLaplaceDomain k L₁ H) {P : EuclidD d → ℝ}
    (hP : IsHomogeneousOfDegree k P) {q : ℝ} (hq : 0 < q) :
    A.rescaledMoment P q =
      A.toLocalLaplaceDomain.posteriorMoment P q / q ^ k := by
  rw [A.toLocalLaplaceDomain.posteriorMoment_eq_pow_mul hP hq]
  rw [mul_comm, mul_div_assoc, div_self (pow_pos hq k).ne', mul_one]
  rfl

/-- **Jet recovery in the note's language** (the expansion bridge):
two losses whose localized monomial moment families, as functions of
the temperature, agree beyond all orders — the note's "same
asymptotics" convention — have equal derivative tensors at every
order. -/
theorem smooth_jet_recovery_of_superPoly_moments
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H)
    (hbase : ∀ j < 3,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ k (h2 : 2 < k), ∀ m : Fin k → Fin d,
      Laplace.SuperPoly (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t -
        (B k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t)) :
    ∀ j, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 := by
  refine smooth_jet_recovery_of_monomial_rates A B hbase
    hsymm₁ hsymm₂ ?_
  intro k h2 m
  have htrans := isLittleO_pow_of_superPoly (hdata k h2 m) k (k - 2)
  refine htrans.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [LocalLaplaceDomain.posteriorMomentT_inv_sq _ _ hq,
    LocalLaplaceDomain.posteriorMomentT_inv_sq _ _ hq,
    sub_div,
    ← (A k h2).rescaledMoment_eq_posteriorMoment_div
      (monomialTest_isHomogeneous m) hq,
    ← (B k h2).rescaledMoment_eq_posteriorMoment_div
      (monomialTest_isHomogeneous m) hq]

end HigherLaplaceDomain

end Laplace.Multi
