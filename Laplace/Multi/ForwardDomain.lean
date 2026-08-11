/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.GaussianMeso

/-!
# The forward expansion domain and the exponent split

Stage 3 of the forward-expansion programme. The order-`N` moment
expansion needs one input beyond the merged `HigherLaplaceDomain`:
the Peano form of the Taylor remainder — the `O(‖y‖^(N+2))` bound
identifies no coefficient, while `o(‖y‖^(N+2))` pins the order-`N`
term. `ForwardExpansionDomain N` is that one-field mixin. On it the
exact exponent split holds: for `q > 0` at a critical point (the
degree-one term vanishing),
`(L(qz) - L(0))/q² = T₂(z) + ∑_{s=1}^N q^s V_s(z) + q^N ρ_q(z)`,
with `V_s` the degree-`(s+2)` diagonal Taylor term and the scaled
remainder `ρ_q` tending to zero pointwise (from the Peano field) and
polynomially bounded wherever `q`-scaling lands in the Taylor ball.
This is the object stage 4's graded exponential expands. The
identification of `T₂` with the quadratic form of `H` is bridged
separately, per the design consult.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d : ℕ}

/-- **The forward expansion domain**: the merged higher-order package
plus the Peano remainder — the one genuinely new input the order-`N`
expansion requires. -/
structure ForwardExpansionDomain (N : ℕ) (L : EuclidD d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ)
    extends HigherLaplaceDomain (N + 2) L H where
  taylorPeano :
    (fun y : EuclidD d ↦
      L y - ∑ m ∈ Finset.range (N + 3), taylorHomogeneousTerm m L y)
      =o[𝓝 (0 : EuclidD d)] fun y : EuclidD d ↦ ‖y‖ ^ (N + 2)

/-- The exponent's homogeneous correction terms: `V_s = T_(s+2)`. -/
noncomputable def exponentTerm (s : ℕ) (L : EuclidD d → ℝ)
    (z : EuclidD d) : ℝ :=
  taylorHomogeneousTerm (s + 2) L z

/-- The degree-zero diagonal Taylor term is the value. -/
theorem taylorHomogeneousTerm_zero (L : EuclidD d → ℝ)
    (z : EuclidD d) :
    taylorHomogeneousTerm 0 L z = L 0 := by
  unfold taylorHomogeneousTerm
  rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
  exact iteratedFDeriv_zero_apply _

/-- Positive-degree diagonal Taylor terms vanish at the origin. -/
theorem taylorHomogeneousTerm_zero_point {m : ℕ} (hm : m ≠ 0)
    (L : EuclidD d → ℝ) :
    taylorHomogeneousTerm m L (0 : EuclidD d) = 0 := by
  have h := taylorHomogeneousTerm_smul m L 0 (0 : EuclidD d)
  rw [zero_smul, zero_pow hm, zero_mul] at h
  exact h

/-- Pointwise bound for a diagonal Taylor term via the operator
norm. -/
theorem abs_taylorHomogeneousTerm_le (k : ℕ) (L : EuclidD d → ℝ)
    (z : EuclidD d) :
    |taylorHomogeneousTerm k L z| ≤
      (k.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ k L 0‖ * ‖z‖ ^ k := by
  unfold taylorHomogeneousTerm
  rw [abs_mul, abs_of_nonneg (by positivity :
    (0:ℝ) ≤ ((k.factorial : ℝ))⁻¹), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |(iteratedFDeriv ℝ k L 0) fun _ ↦ z|
      ≤ ‖iteratedFDeriv ℝ k L 0‖ * ∏ _i : Fin k, ‖z‖ := by
        have h := (iteratedFDeriv ℝ k L 0).le_opNorm (fun _ ↦ z)
        rwa [Real.norm_eq_abs] at h
    _ = ‖iteratedFDeriv ℝ k L 0‖ * ‖z‖ ^ k := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

namespace ForwardExpansionDomain

variable {N : ℕ} {L : EuclidD d → ℝ}
  {H : Matrix (Fin d) (Fin d) ℝ}

/-- The Taylor remainder through degree `N + 2`. -/
noncomputable def taylorRem (_D : ForwardExpansionDomain N L H)
    (y : EuclidD d) : ℝ :=
  L y - ∑ m ∈ Finset.range (N + 3), taylorHomogeneousTerm m L y

/-- The scaled Taylor remainder at scale `q`. -/
noncomputable def scaledRem (D : ForwardExpansionDomain N L H)
    (q : ℝ) (z : EuclidD d) : ℝ :=
  D.taylorRem (q • z) / q ^ (N + 2)

/-- The remainder vanishes at the origin. -/
theorem taylorRem_zero (D : ForwardExpansionDomain N L H) :
    D.taylorRem (0 : EuclidD d) = 0 := by
  unfold taylorRem
  rw [Finset.sum_eq_single 0]
  · rw [taylorHomogeneousTerm_zero, sub_self]
  · intro m _ hm
    exact taylorHomogeneousTerm_zero_point hm L
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Pointwise vanishing of the scaled remainder**, from the Peano
field. -/
theorem tendsto_scaledRem (D : ForwardExpansionDomain N L H)
    (z : EuclidD d) :
    Tendsto (fun q : ℝ ↦ D.scaledRem q z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  by_cases hz : z = 0
  · subst hz
    have hev : (fun q : ℝ ↦ D.scaledRem q (0 : EuclidD d)) =
        fun _ : ℝ ↦ (0 : ℝ) := by
      funext q
      unfold scaledRem
      rw [smul_zero, D.taylorRem_zero, zero_div]
    rw [hev]
    exact tendsto_const_nhds
  · have hpath : Tendsto (fun q : ℝ ↦ q • z) (𝓝[>] (0 : ℝ))
        (𝓝 (0 : EuclidD d)) := by
      have hc : Continuous fun q : ℝ ↦ q • z :=
        continuous_id.smul continuous_const
      have := hc.tendsto (0 : ℝ)
      rw [zero_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hcomp := D.taylorPeano.comp_tendsto hpath
    have hev : (fun q : ℝ ↦ ‖q • z‖ ^ (N + 2)) =ᶠ[𝓝[>] (0 : ℝ)]
        fun q : ℝ ↦ ‖z‖ ^ (N + 2) * q ^ (N + 2) := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (Set.mem_Ioi.mp hq), mul_pow]
      ring
    have h1 : (fun q : ℝ ↦ D.taylorRem (q • z)) =o[𝓝[>] (0 : ℝ)]
        fun q : ℝ ↦ ‖z‖ ^ (N + 2) * q ^ (N + 2) :=
      hcomp.congr' (Filter.EventuallyEq.refl _ _) hev
    have h2 : (fun q : ℝ ↦ D.taylorRem (q • z)) =o[𝓝[>] (0 : ℝ)]
        fun q : ℝ ↦ q ^ (N + 2) := by
      refine h1.trans_isBigO ?_
      exact (isBigO_refl (fun q : ℝ ↦ (q : ℝ) ^ (N + 2))
        _).const_mul_left (‖z‖ ^ (N + 2))
    exact h2.tendsto_div_nhds_zero

/-- The window constant for the scaled remainder. -/
noncomputable def remConst (D : ForwardExpansionDomain N L H) : ℝ :=
  D.taylorRemainderConst +
    (((N + 2).factorial : ℝ))⁻¹ * ‖iteratedFDeriv ℝ (N + 2) L 0‖

/-- **The window bound**: wherever `q`-scaling lands in the Taylor
ball, the scaled remainder is polynomially bounded in `z`, uniformly
in `q`. -/
theorem abs_scaledRem_le (D : ForwardExpansionDomain N L H)
    {q : ℝ} (hq : 0 < q) {z : EuclidD d}
    (hz : q • z ∈ Metric.ball (0 : EuclidD d) D.taylorRadius) :
    |D.scaledRem q z| ≤ D.remConst * ‖z‖ ^ (N + 2) := by
  have hsplit : D.taylorRem (q • z) =
      (L (q • z) - ∑ m ∈ Finset.range (N + 2),
        taylorHomogeneousTerm m L (q • z)) -
      taylorHomogeneousTerm (N + 2) L (q • z) := by
    unfold taylorRem
    rw [Finset.sum_range_succ]
    ring
  have h1 := D.taylorRemainder_bound (q • z) hz
  have h2 := abs_taylorHomogeneousTerm_le (N + 2) L (q • z)
  have habs : |D.taylorRem (q • z)| ≤ D.remConst * ‖q • z‖ ^ (N + 2) := by
    rw [hsplit]
    unfold remConst
    calc |(L (q • z) - ∑ m ∈ Finset.range (N + 2),
          taylorHomogeneousTerm m L (q • z)) -
          taylorHomogeneousTerm (N + 2) L (q • z)|
        ≤ |L (q • z) - ∑ m ∈ Finset.range (N + 2),
            taylorHomogeneousTerm m L (q • z)| +
          |taylorHomogeneousTerm (N + 2) L (q • z)| := abs_sub _ _
      _ ≤ D.taylorRemainderConst * ‖q • z‖ ^ (N + 2) +
          (((N + 2).factorial : ℝ))⁻¹ *
            ‖iteratedFDeriv ℝ (N + 2) L 0‖ * ‖q • z‖ ^ (N + 2) := by
          gcongr
      _ = (D.taylorRemainderConst +
          (((N + 2).factorial : ℝ))⁻¹ *
            ‖iteratedFDeriv ℝ (N + 2) L 0‖) * ‖q • z‖ ^ (N + 2) := by
          ring
  have hnorm : ‖q • z‖ ^ (N + 2) = q ^ (N + 2) * ‖z‖ ^ (N + 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq, mul_pow]
  unfold scaledRem
  rw [abs_div, abs_of_pos (pow_pos hq (N + 2))]
  rw [div_le_iff₀ (pow_pos hq (N + 2))]
  calc |D.taylorRem (q • z)| ≤ D.remConst * ‖q • z‖ ^ (N + 2) := habs
    _ = D.remConst * ‖z‖ ^ (N + 2) * q ^ (N + 2) := by
        rw [hnorm]; ring

/-- **The exact exponent split** at a critical point: for `q > 0`,
`(L(qz) - L(0))/q² = T₂(z) + ∑_{s=1}^N q^s V_s(z) + q^N ρ_q(z)`. -/
theorem exponent_split (D : ForwardExpansionDomain N L H)
    (hgrad : taylorHomogeneousTerm 1 L = fun _ ↦ (0 : ℝ))
    {q : ℝ} (hq : 0 < q) (z : EuclidD d) :
    (L (q • z) - L 0) / q ^ 2 =
      taylorHomogeneousTerm 2 L z +
      (∑ s ∈ Finset.range N, q ^ (s + 1) * exponentTerm (s + 1) L z) +
      q ^ N * D.scaledRem q z := by
  have hqne : (q : ℝ) ≠ 0 := hq.ne'
  have hL : L (q • z) = (∑ m ∈ Finset.range (N + 3),
      taylorHomogeneousTerm m L (q • z)) + D.taylorRem (q • z) := by
    unfold taylorRem
    ring
  have hsum : ∑ m ∈ Finset.range (N + 3),
      taylorHomogeneousTerm m L (q • z) =
      L 0 + q ^ 2 * taylorHomogeneousTerm 2 L z +
        ∑ s ∈ Finset.range N,
          q ^ (s + 3) * taylorHomogeneousTerm (s + 3) L z := by
    have hshift : ∀ m : ℕ, taylorHomogeneousTerm m L (q • z) =
        q ^ m * taylorHomogeneousTerm m L z := fun m ↦
      taylorHomogeneousTerm_smul m L q z
    rw [Finset.sum_congr rfl fun m _ ↦ hshift m]
    rw [Finset.sum_range_succ' _ (N + 2),
      Finset.sum_range_succ' _ (N + 1),
      Finset.sum_range_succ' _ N]
    rw [pow_zero, one_mul, taylorHomogeneousTerm_zero]
    rw [show taylorHomogeneousTerm (0 + 1) L z =
      taylorHomogeneousTerm 1 L z from rfl]
    rw [hgrad]
    have hidx : ∀ s : ℕ, s + 1 + 1 + 1 = s + 3 := fun s ↦ by omega
    have hcongr : ∑ s ∈ Finset.range N,
        q ^ (s + 1 + 1 + 1) * taylorHomogeneousTerm (s + 1 + 1 + 1) L z =
        ∑ s ∈ Finset.range N,
          q ^ (s + 3) * taylorHomogeneousTerm (s + 3) L z := by
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [hidx s]
    rw [hcongr]
    ring
  rw [hL, hsum]
  unfold scaledRem
  unfold exponentTerm
  have hpow : ∀ s : ℕ, q ^ (s + 3) = q ^ 2 * q ^ (s + 1) := fun s ↦ by
    rw [← pow_add]
    congr 1
    omega
  have hsum2 : ∑ s ∈ Finset.range N,
      q ^ (s + 3) * taylorHomogeneousTerm (s + 3) L z =
      q ^ 2 * ∑ s ∈ Finset.range N,
        q ^ (s + 1) * taylorHomogeneousTerm (s + 1 + 2) L z := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [hpow s, show s + 1 + 2 = s + 3 from by omega]
    ring
  rw [hsum2]
  have hq2 : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hqne
  have hqN2 : (q : ℝ) ^ (N + 2) ≠ 0 := pow_ne_zero (N + 2) hqne
  field_simp
  ring

end ForwardExpansionDomain

end Laplace.Multi
