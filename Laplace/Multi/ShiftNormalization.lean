/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.AsymptoticPolynomial
import Laplace.Multi.ForwardDomain
import Laplace.Multi.HessianBridge
import Laplace.Multi.AnalyticGermRecovery

/-!
# Shift normalization and the base-case-free recovery headline

The 2026-08-10 fidelity review found the superPoly-language headline
assuming what the germbij note's Theorem 3.1 derives: `hbase` demands
equal values (the constant the note proves is lost), equal gradients,
and equal Hessians. This file discharges all three.

The value: normalized posterior moments are exactly invariant under a
constant shift of the loss (`posteriorMoment_shift` — the factor
`exp (-(a/q²))` cancels between numerator and denominator), and the
domain packages transport (`LocalLaplaceDomain.shift`,
`HigherLaplaceDomain.shift`), so shifting `L₂` by `L₁ 0 - L₂ 0`
matches the values without touching the data. The gradient and the
Hessian: along rays the loss admits two order-2 asymptotic
expansions — the diagonal Taylor one (from the package's fixed-ball
remainder bound, `rayExpansion_taylor`) and the quadratic-Peano one
(`LocalQuadraticApprox.rayExpansion_quad`) — and stage-1 coefficient
uniqueness forces `T₁ = 0` and `T₂ = qform H / 2`, whence
`iteratedFDeriv ℝ 1 L 0 = 0` and the order-2 diagonal is `qform H`;
with the k = 2 covariance bridge supplying `H₁ = H₂`, polarization
identifies the order-2 tensors. The headline
`smooth_positive_jet_recovery_of_superPoly_moments` then concludes
equality of ALL positive-order derivative tensors from superPoly
moment data alone — no base case, no shared-`H` assumption — and
`analytic_germ_recovery_of_superPoly_moments_free` restates germbij
Corollary 3.2's inverse direction in the same freed form.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d : ℕ}

/-! ## Shift invariance of iterated derivatives -/

/-- Positive-order iterated derivatives ignore constant shifts. -/
theorem iteratedFDeriv_shift {n : ℕ} (hn : n ≠ 0) {L : EuclidD d → ℝ}
    (hL : ContDiffAt ℝ n L 0) (a : ℝ) :
    iteratedFDeriv ℝ n (fun w ↦ L w + a) 0 = iteratedFDeriv ℝ n L 0 := by
  have h := fun_iteratedFDeriv_add_apply (i := n) (f := L)
    (g := fun _ : EuclidD d ↦ a) (x := (0 : EuclidD d)) hL contDiffAt_const
  have h0 : iteratedFDeriv ℝ n (fun _ : EuclidD d ↦ a) (0 : EuclidD d) = 0 := by
    rw [iteratedFDeriv_const_of_ne hn]
    rfl
  rw [h, h0, add_zero]

/-! ## Package transport under constant shift -/

namespace LocalQuadraticApprox

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- Transport of the quadratic-approximation package under a constant
shift of the loss. -/
def shift (Q : LocalQuadraticApprox L H) (a : ℝ) :
    LocalQuadraticApprox (fun w ↦ L w + a) H where
  hH_posDef := Q.hH_posDef
  lambda := Q.lambda
  lambda_pos := Q.lambda_pos
  qform_lower := Q.qform_lower
  quadratic_peano :=
    Q.quadratic_peano.congr'
      (Filter.Eventually.of_forall fun y ↦ by ring)
      (Filter.EventuallyEq.refl _ _)

/-- **Ray expansion, quadratic side**: the loss along a ray admits the
quadratic-form coefficients as its order-2 asymptotic polynomial, from
the quadratic Peano field alone. -/
theorem rayExpansion_quad (Q : LocalQuadraticApprox L H) (z : EuclidD d) :
    Laplace.IsAsymptoticExpansionTo (fun t : ℝ ↦ L (t • z))
      (fun j ↦ if j = 0 then L 0 else
        if j = 2 then qform H z / 2 else 0) 2 := by
  unfold Laplace.IsAsymptoticExpansionTo
  have hpath : Tendsto (fun t : ℝ ↦ t • z) (𝓝[>] (0 : ℝ))
      (𝓝 (0 : EuclidD d)) := by
    have hc : Continuous fun t : ℝ ↦ t • z :=
      continuous_id.smul continuous_const
    have := hc.tendsto (0 : ℝ)
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hcomp := Q.quadratic_peano.comp_tendsto hpath
  have hev : (fun t : ℝ ↦ ‖t • z‖ ^ 2) =ᶠ[𝓝[>] (0 : ℝ)]
      fun t : ℝ ↦ ‖z‖ ^ 2 * t ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Set.mem_Ioi.mp ht),
      mul_pow]
    ring
  have h1 := hcomp.congr' (Filter.EventuallyEq.refl _ _) hev
  have h2 : (fun t : ℝ ↦ L (t • z) - L 0 - qform H (t • z) / 2)
      =o[𝓝[>] (0 : ℝ)] fun t : ℝ ↦ t ^ 2 :=
    h1.trans_isBigO ((isBigO_refl (fun t : ℝ ↦ (t : ℝ) ^ 2)
      _).const_mul_left (‖z‖ ^ 2))
  refine h2.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with t
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  norm_num
  rw [qform_smul]
  ring

end LocalQuadraticApprox

namespace LocalLaplaceDomain

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- Transport of the localized-domain package under a constant shift
of the loss: the region, coercivity, and quadratic approximation are
all statements about `L · - L 0`. -/
def shift (A : LocalLaplaceDomain L H) (a : ℝ) :
    LocalLaplaceDomain (fun w ↦ L w + a) H where
  toLocalQuadraticApprox := A.toLocalQuadraticApprox.shift a
  U := A.U
  measurableSet_U := A.measurableSet_U
  delta := A.delta
  delta_pos := A.delta_pos
  ball_subset_U := A.ball_subset_U
  c := A.c
  c_pos := A.c_pos
  rescaled_lower := fun {q x} hq hx ↦ by
    have h := A.rescaled_lower hq hx
    rw [show L (q • x) + a - (L 0 + a) = L (q • x) - L 0 from by ring]
    exact h
  measurable_L := A.measurable_L.add_const a

@[simp] theorem shift_U (A : LocalLaplaceDomain L H) (a : ℝ) :
    (A.shift a).U = A.U := rfl

/-- The unnormalized posterior integral of a shifted loss factors the
constant out exactly, at every scale. -/
theorem posteriorIntegral_shift (A : LocalLaplaceDomain L H) (a : ℝ)
    (f : EuclidD d → ℝ) (q : ℝ) :
    (A.shift a).posteriorIntegral f q =
      Real.exp (-(a / q ^ 2)) * A.posteriorIntegral f q := by
  unfold posteriorIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
  rw [shift_U]
  show Set.indicator A.U
      (fun w ↦ f w * Real.exp (-((L w + a) / q ^ 2))) w =
    Real.exp (-(a / q ^ 2)) *
      Set.indicator A.U (fun w ↦ f w * Real.exp (-(L w / q ^ 2))) w
  by_cases hw : w ∈ A.U
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
    rw [show -((L w + a) / q ^ 2) = -(L w / q ^ 2) + -(a / q ^ 2) from
      by ring, Real.exp_add]
    ring
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw,
      mul_zero]

/-- **Exact shift invariance of the normalized moment**: the constant
factor cancels between numerator and denominator, at every scale
(junk-consistent where the denominator vanishes). -/
theorem posteriorMoment_shift (A : LocalLaplaceDomain L H) (a : ℝ)
    (f : EuclidD d → ℝ) (q : ℝ) :
    (A.shift a).posteriorMoment f q = A.posteriorMoment f q := by
  unfold posteriorMoment
  rw [posteriorIntegral_shift, posteriorIntegral_shift,
    mul_div_mul_left _ _ (Real.exp_pos (-(a / q ^ 2))).ne']

/-- Shift invariance in the temperature parametrization. -/
theorem posteriorMomentT_shift (A : LocalLaplaceDomain L H) (a : ℝ)
    (f : EuclidD d → ℝ) (t : ℝ) :
    (A.shift a).posteriorMomentT f t = A.posteriorMomentT f t :=
  A.posteriorMoment_shift a f _

end LocalLaplaceDomain

namespace HigherLaplaceDomain

variable {k : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- Transport of the higher-order package under a constant shift: the
degree-0 diagonal Taylor term absorbs the constant and every other
field is shift-blind. -/
def shift (D : HigherLaplaceDomain k L H) (hk : k ≠ 0) (a : ℝ) :
    HigherLaplaceDomain k (fun w ↦ L w + a) H where
  toLocalLaplaceDomain := D.toLocalLaplaceDomain.shift a
  contDiff_k := D.contDiff_k.add contDiff_const
  taylorRadius := D.taylorRadius
  taylorRadius_pos := D.taylorRadius_pos
  taylorBall_subset := D.taylorBall_subset
  taylorRemainderConst := D.taylorRemainderConst
  taylorRemainderConst_nonneg := D.taylorRemainderConst_nonneg
  taylorRemainder_bound := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 :=
      ⟨k - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hk)).symm⟩
    intro y hy
    have hb := D.taylorRemainder_bound y hy
    have hsum : ∑ j ∈ Finset.range (n + 1),
        taylorHomogeneousTerm j (fun w ↦ L w + a) y =
        a + ∑ j ∈ Finset.range (n + 1), taylorHomogeneousTerm j L y := by
      rw [Finset.sum_range_succ' _ n, Finset.sum_range_succ' _ n]
      have hpos : ∀ i ∈ Finset.range n,
          taylorHomogeneousTerm (i + 1) (fun w ↦ L w + a) y =
          taylorHomogeneousTerm (i + 1) L y := by
        intro i hi
        have hik : ((i + 1 : ℕ) : WithTop ℕ∞) ≤ ((n + 1 : ℕ) : WithTop ℕ∞) := by
          exact_mod_cast Nat.succ_le_succ (Finset.mem_range.mp hi).le
        unfold taylorHomogeneousTerm
        rw [iteratedFDeriv_shift (Nat.succ_ne_zero i)
          ((D.contDiff_k.of_le hik).contDiffAt) a]
      rw [Finset.sum_congr rfl hpos]
      simp only [taylorHomogeneousTerm_zero]
      ring
    show |L y + a - ∑ j ∈ Finset.range (n + 1),
        taylorHomogeneousTerm j (fun w ↦ L w + a) y| ≤
      D.taylorRemainderConst * ‖y‖ ^ (n + 1)
    rw [hsum,
      show L y + a - (a + ∑ j ∈ Finset.range (n + 1),
        taylorHomogeneousTerm j L y) =
        L y - ∑ j ∈ Finset.range (n + 1),
          taylorHomogeneousTerm j L y from by ring]
    exact hb

@[simp] theorem shift_toLocalLaplaceDomain (D : HigherLaplaceDomain k L H)
    (hk : k ≠ 0) (a : ℝ) :
    (D.shift hk a).toLocalLaplaceDomain = D.toLocalLaplaceDomain.shift a :=
  rfl

/-! ## Ray uniqueness at the higher-domain level -/

/-- **Ray expansion, Taylor side**: from the fixed-ball remainder
bound, the loss along a ray admits the diagonal Taylor terms as its
order-2 asymptotic polynomial. -/
theorem rayExpansion_taylor (D : HigherLaplaceDomain k L H)
    (hk : 2 < k) (z : EuclidD d) :
    Laplace.IsAsymptoticExpansionTo (fun t : ℝ ↦ L (t • z))
      (fun j ↦ taylorHomogeneousTerm j L z) 2 := by
  unfold Laplace.IsAsymptoticExpansionTo
  have hrem : (fun t : ℝ ↦ L (t • z) - ∑ j ∈ Finset.range k,
      taylorHomogeneousTerm j L z * t ^ j)
      =o[𝓝[>] (0 : ℝ)] fun t : ℝ ↦ t ^ 2 := by
    have hbig : (fun t : ℝ ↦ L (t • z) - ∑ j ∈ Finset.range k,
        taylorHomogeneousTerm j L z * t ^ j)
        =O[𝓝[>] (0 : ℝ)] fun t : ℝ ↦ t ^ k := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨D.taylorRemainderConst * ‖z‖ ^ k, ?_⟩
      have hδ : (0 : ℝ) < D.taylorRadius / (‖z‖ + 1) := by
        have := D.taylorRadius_pos
        positivity
      filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      obtain ⟨ht0, htlt⟩ := ht
      have hball : t • z ∈ Metric.ball (0 : EuclidD d) D.taylorRadius := by
        rw [Metric.mem_ball, dist_zero_right, norm_smul,
          Real.norm_eq_abs, abs_of_pos ht0]
        calc t * ‖z‖ ≤ t * (‖z‖ + 1) := by
              refine mul_le_mul_of_nonneg_left ?_ ht0.le
              linarith
          _ < D.taylorRadius := by
              rw [← lt_div_iff₀ (by positivity : (0:ℝ) < ‖z‖ + 1)]
              exact htlt
      have hb := D.taylorRemainder_bound (t • z) hball
      have hsum : ∑ j ∈ Finset.range k,
          taylorHomogeneousTerm j L (t • z) =
          ∑ j ∈ Finset.range k,
            taylorHomogeneousTerm j L z * t ^ j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [taylorHomogeneousTerm_smul]
        ring
      rw [hsum] at hb
      have hnorm : ‖t • z‖ ^ k = ‖z‖ ^ k * t ^ k := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mul_pow]
        ring
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (pow_pos ht0 k)]
      calc |L (t • z) - ∑ j ∈ Finset.range k,
            taylorHomogeneousTerm j L z * t ^ j|
          ≤ D.taylorRemainderConst * ‖t • z‖ ^ k := hb
        _ = D.taylorRemainderConst * ‖z‖ ^ k * t ^ k := by
            rw [hnorm]; ring
    exact hbig.trans_isLittleO
      ((Asymptotics.isLittleO_pow_pow hk).mono nhdsWithin_le_nhds)
  have hpoly : (fun t : ℝ ↦ ∑ j ∈ Finset.Ico 3 k,
      taylorHomogeneousTerm j L z * t ^ j)
      =o[𝓝[>] (0 : ℝ)] fun t : ℝ ↦ t ^ 2 := by
    refine Asymptotics.IsLittleO.sum fun j hj ↦ ?_
    have h3 : 2 < j := by
      have := (Finset.mem_Ico.mp hj).1
      omega
    exact ((Asymptotics.isLittleO_pow_pow h3).mono
      nhdsWithin_le_nhds).const_mul_left _
  refine (hpoly.add hrem).congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with t
  have hsplit : ∑ j ∈ Finset.range k,
      taylorHomogeneousTerm j L z * t ^ j =
      (∑ j ∈ Finset.range 3, taylorHomogeneousTerm j L z * t ^ j) +
        ∑ j ∈ Finset.Ico 3 k, taylorHomogeneousTerm j L z * t ^ j := by
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)]
  rw [hsplit]
  ring

/-- **The degree-one diagonal term vanishes** at the higher-domain
level: coefficient uniqueness at order 1 between the two ray
expansions. -/
theorem taylorHomogeneousTerm_one_eq_zero
    (D : HigherLaplaceDomain k L H) (hk : 2 < k) :
    taylorHomogeneousTerm 1 L = fun _ : EuclidD d ↦ (0 : ℝ) := by
  funext z
  have h := Laplace.isAsymptoticExpansionTo_coeff_eq
    (D.rayExpansion_taylor hk z)
    (D.toLocalQuadraticApprox.rayExpansion_quad z) 1 (by omega)
  simpa using h

/-- **The `T₂`/qform tie** at the higher-domain level: coefficient
uniqueness at order 2. -/
theorem taylorHomogeneousTerm_two_eq_qform
    (D : HigherLaplaceDomain k L H) (hk : 2 < k) (z : EuclidD d) :
    taylorHomogeneousTerm 2 L z = qform H z / 2 := by
  have h := Laplace.isAsymptoticExpansionTo_coeff_eq
    (D.rayExpansion_taylor hk z)
    (D.toLocalQuadraticApprox.rayExpansion_quad z) 2 le_rfl
  simpa using h

/-- **The gradient tensor vanishes**: a 1-multilinear map vanishing on
diagonals vanishes. -/
theorem iteratedFDeriv_one_eq_zero (D : HigherLaplaceDomain k L H)
    (hk : 2 < k) : iteratedFDeriv ℝ 1 L 0 = 0 := by
  have h1 := D.taylorHomogeneousTerm_one_eq_zero hk
  ext v
  have hz := congrFun h1 (v 0)
  unfold taylorHomogeneousTerm at hz
  rw [Nat.factorial_one, Nat.cast_one, inv_one, one_mul] at hz
  have hv : v = fun _ : Fin 1 ↦ v 0 :=
    funext fun i ↦ by rw [Subsingleton.elim i 0]
  rw [hv, ContinuousMultilinearMap.zero_apply]
  exact hz

/-- **The order-2 diagonal is the quadratic form.** -/
theorem iteratedFDeriv_two_diag (D : HigherLaplaceDomain k L H)
    (hk : 2 < k) (z : EuclidD d) :
    iteratedFDeriv ℝ 2 L 0 (fun _ ↦ z) = qform H z := by
  have h2 := D.taylorHomogeneousTerm_two_eq_qform hk z
  unfold taylorHomogeneousTerm at h2
  have hfac : ((Nat.factorial 2 : ℝ))⁻¹ = 2⁻¹ := by norm_num
  rw [hfac] at h2
  linarith

end HigherLaplaceDomain

/-! ## The base-case-free headline -/

open LocalLaplaceDomain HigherLaplaceDomain in
/-- **Positive-order jet recovery from superPoly data alone**
(germbij Theorem 3.1, inverse direction, no base-case assumptions):
two localized nondegenerate losses whose second-moment and monomial
moment families agree beyond all orders in the temperature have equal
derivative tensors at every positive order. Neither equal values, nor
equal gradients, nor equal Hessians, nor a shared package matrix is
assumed. -/
theorem smooth_positive_jet_recovery_of_superPoly_moments
    {L₁ L₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H₁)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H₂)
    (hsymm₁ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata₂ : ∀ i j : Fin d, Laplace.SuperPoly (fun t : ℝ ↦
      (A 3 (by norm_num)).toLocalLaplaceDomain.posteriorMomentT
        (fun w ↦ w i * w j) t -
      (B 3 (by norm_num)).toLocalLaplaceDomain.posteriorMomentT
        (fun w ↦ w i * w j) t))
    (hdatak : ∀ k (h2 : 2 < k), ∀ m : Fin k → Fin d,
      Laplace.SuperPoly (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t -
        (B k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t)) :
    ∀ j, 0 < j → iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 := by
  have hH : H₁ = H₂ := hessian_recovery_of_superPoly_moments
    (A 3 (by norm_num)).toLocalLaplaceDomain
    (B 3 (by norm_num)).toLocalLaplaceDomain hdata₂
  subst hH
  set a : ℝ := L₁ 0 - L₂ 0 with ha
  have hCD : ∀ n : ℕ, ContDiffAt ℝ n L₂ 0 := by
    intro n
    exact ((B (n + 3) (by omega)).contDiff_k.of_le
      (by exact_mod_cast Nat.le_add_right n 3)).contDiffAt
  have hbase : ∀ j < 3, iteratedFDeriv ℝ j L₁ 0 =
      iteratedFDeriv ℝ j (fun w ↦ L₂ w + a) 0 := by
    intro j hj
    interval_cases j
    · ext v
      rw [iteratedFDeriv_zero_apply, iteratedFDeriv_zero_apply]
      rw [ha]
      ring
    · rw [iteratedFDeriv_shift one_ne_zero (hCD 1) a,
        (A 3 (by norm_num)).iteratedFDeriv_one_eq_zero (by norm_num),
        (B 3 (by norm_num)).iteratedFDeriv_one_eq_zero (by norm_num)]
    · rw [iteratedFDeriv_shift two_ne_zero (hCD 2) a]
      refine iteratedFDeriv_eq_of_diag_eq
        (hsymm₁ 2 one_lt_two) (hsymm₂ 2 one_lt_two) fun z ↦ ?_
      rw [(A 3 (by norm_num)).iteratedFDeriv_two_diag (by norm_num) z,
        (B 3 (by norm_num)).iteratedFDeriv_two_diag (by norm_num) z]
  have hsymm₂' : ∀ k, 2 < k →
      (iteratedFDeriv ℝ k (fun w ↦ L₂ w + a) 0).IsSymm := by
    intro k hk2
    rw [iteratedFDeriv_shift (by omega) (hCD k) a]
    exact hsymm₂ k (by omega)
  have hdatak' : ∀ k (h2 : 2 < k), ∀ m : Fin k → Fin d,
      Laplace.SuperPoly (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t -
        ((B k h2).shift (by omega) a).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t) := by
    intro k h2 m
    have heq : (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t -
        ((B k h2).shift (by omega) a).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t) =
        fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t -
        (B k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t := by
      funext t
      rw [HigherLaplaceDomain.shift_toLocalLaplaceDomain,
        posteriorMomentT_shift]
    rw [heq]
    exact hdatak k h2 m
  have hmain := HigherLaplaceDomain.smooth_jet_recovery_of_superPoly_moments
    A (fun k h2 ↦ (B k h2).shift (by omega) a) hbase
    (fun k hk2 ↦ hsymm₁ k (by omega)) hsymm₂' hdatak'
  intro j hj
  have h := hmain j
  rwa [iteratedFDeriv_shift hj.ne' (hCD j) a] at h

/-- **The analytic germ corollary, freed of base-case assumptions**
(germbij Corollary 3.2, inverse direction): for losses analytic at
their minimum, superPoly-matched second-moment and monomial moment
families determine the germ modulo the additive constant — with no
assumed agreement at orders 0, 1, 2 and no shared package matrix. -/
theorem analytic_germ_recovery_of_superPoly_moments_free
    {L₁ L₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H₁)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H₂)
    (hsymm₁ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 1 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata₂ : ∀ i j : Fin d, Laplace.SuperPoly (fun t : ℝ ↦
      (A 3 (by norm_num)).toLocalLaplaceDomain.posteriorMomentT
        (fun w ↦ w i * w j) t -
      (B 3 (by norm_num)).toLocalLaplaceDomain.posteriorMomentT
        (fun w ↦ w i * w j) t))
    (hdatak : ∀ k (h2 : 2 < k), ∀ m : Fin k → Fin d,
      Laplace.SuperPoly (fun t : ℝ ↦
        (A k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t -
        (B k h2).toLocalLaplaceDomain.posteriorMomentT
          (monomialTest m) t))
    (hL₁ : AnalyticAt ℝ L₁ 0) (hL₂ : AnalyticAt ℝ L₂ 0) :
    ∀ᶠ y in 𝓝 (0 : EuclidD d), L₁ y - L₁ 0 = L₂ y - L₂ 0 :=
  analytic_germ_eq_of_jet_eq hL₁ hL₂
    (smooth_positive_jet_recovery_of_superPoly_moments A B
      hsymm₁ hsymm₂ hdata₂ hdatak)

end Laplace.Multi
