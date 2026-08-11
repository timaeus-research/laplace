/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.AsymptoticPolynomial
import Laplace.Multi.ScalarBounds

/-!
# Gaussian absorption of the exponent corrections

Stage 5c-pre of the forward-expansion programme (items 1-3 of the
archived architecture consult). The domain ties `H` to `L` only
through the quadratic Peano condition, so the `T₂`/`qform` bridge is
proven by composing both Peano statements along rays and applying
stage 1's coefficient uniqueness at order 2 — which also yields the
vanishing of the degree-one term (the critical-point condition
consumed by the exponent split) for free. On the mesoscopic window
the Peano field gives arbitrary-small control of the scaled
remainder, the homogeneous corrections are `≤ ε‖z‖²` by the scale
arithmetic `q^s‖z‖^(s+2) = ‖z‖²(q‖z‖)^s ≤ ‖z‖²√q`, and the total
absolute correction absorbs into a Gaussian at a quarter of the
domain's rate. The absorption lemma is the exact interface the
`q`-uniform majorant of the next tide wants.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d N : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- `t^n = O(t^m)` at `0⁺` when `m ≤ n`. -/
theorem isBigO_pow_pow_nhdsGT {m n : ℕ} (h : m ≤ n) :
    (fun t : ℝ ↦ t ^ n) =O[𝓝[>] (0 : ℝ)] fun t : ℝ ↦ t ^ m := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos ht0 n),
    abs_of_pos (pow_pos ht0 m), one_mul]
  exact pow_le_pow_of_le_one ht0.le ht1.le h

namespace ForwardExpansionDomain

/-- The loss along a ray admits the diagonal Taylor terms as its
order-2 asymptotic polynomial. -/
theorem rayExpansion_taylor (D : ForwardExpansionDomain N L H)
    (z : EuclidD d) :
    Laplace.IsAsymptoticExpansionTo (fun t : ℝ ↦ L (t • z))
      (fun j ↦ taylorHomogeneousTerm j L z) 2 := by
  unfold Laplace.IsAsymptoticExpansionTo
  have hpath : Tendsto (fun t : ℝ ↦ t • z) (𝓝[>] (0 : ℝ))
      (𝓝 (0 : EuclidD d)) := by
    have hc : Continuous fun t : ℝ ↦ t • z :=
      continuous_id.smul continuous_const
    have := hc.tendsto (0 : ℝ)
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hrem : (fun t : ℝ ↦ D.taylorRem (t • z)) =o[𝓝[>] (0 : ℝ)]
      fun t : ℝ ↦ t ^ 2 := by
    have hcomp := D.taylorPeano.comp_tendsto hpath
    have hev : (fun t : ℝ ↦ ‖t • z‖ ^ (N + 2)) =ᶠ[𝓝[>] (0 : ℝ)]
        fun t : ℝ ↦ ‖z‖ ^ (N + 2) * t ^ (N + 2) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Set.mem_Ioi.mp ht),
        mul_pow]
      ring
    have h1 := hcomp.congr' (Filter.EventuallyEq.refl _ _) hev
    have h2 : (fun t : ℝ ↦ D.taylorRem (t • z)) =o[𝓝[>] (0 : ℝ)]
        fun t : ℝ ↦ t ^ (N + 2) :=
      h1.trans_isBigO ((isBigO_refl (fun t : ℝ ↦ (t : ℝ) ^ (N + 2))
        _).const_mul_left (‖z‖ ^ (N + 2)))
    exact h2.trans_isBigO (isBigO_pow_pow_nhdsGT (by omega))
  have hpoly : (fun t : ℝ ↦ ∑ m ∈ Finset.Ico 3 (N + 3),
      taylorHomogeneousTerm m L z * t ^ m) =o[𝓝[>] (0 : ℝ)]
      fun t : ℝ ↦ t ^ 2 := by
    refine Asymptotics.IsLittleO.sum fun m hm ↦ ?_
    have hm3 : 2 < m := by
      have := (Finset.mem_Ico.mp hm).1
      omega
    exact ((Asymptotics.isLittleO_pow_pow hm3).mono
      nhdsWithin_le_nhds).const_mul_left _
  refine ((hpoly.add hrem).congr' ?_ (Filter.EventuallyEq.refl _ _))
  filter_upwards with t
  have hL : L (t • z) = (∑ m ∈ Finset.range (N + 3),
      taylorHomogeneousTerm m L (t • z)) + D.taylorRem (t • z) := by
    unfold ForwardExpansionDomain.taylorRem
    ring
  have hsm : ∀ m : ℕ, taylorHomogeneousTerm m L (t • z) =
      taylorHomogeneousTerm m L z * t ^ m := fun m ↦ by
    rw [taylorHomogeneousTerm_smul]
    ring
  have hsp : ∑ m ∈ Finset.range (N + 3),
      taylorHomogeneousTerm m L z * t ^ m =
      (∑ m ∈ Finset.range 3, taylorHomogeneousTerm m L z * t ^ m) +
        ∑ m ∈ Finset.Ico 3 (N + 3),
          taylorHomogeneousTerm m L z * t ^ m := by
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)]
  rw [hL, Finset.sum_congr rfl fun m _ ↦ hsm m, hsp]
  ring

/-- The loss along a ray admits the quadratic-form coefficients as
its order-2 asymptotic polynomial. -/
theorem rayExpansion_quad (D : ForwardExpansionDomain N L H)
    (z : EuclidD d) :
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
  have hcomp := D.quadratic_peano.comp_tendsto hpath
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

/-- **The degree-one diagonal term vanishes**: the domain's
critical-point condition, from coefficient uniqueness at order 1. -/
theorem taylorHomogeneousTerm_one_eq_zero
    (D : ForwardExpansionDomain N L H) :
    taylorHomogeneousTerm 1 L = fun _ : EuclidD d ↦ (0 : ℝ) := by
  funext z
  have h := Laplace.isAsymptoticExpansionTo_coeff_eq
    (D.rayExpansion_taylor z) (D.rayExpansion_quad z) 1 (by omega)
  simpa using h

/-- **The `T₂`/`qform` bridge**: coefficient uniqueness at order 2. -/
theorem taylorHomogeneousTerm_two_eq_qform
    (D : ForwardExpansionDomain N L H) (z : EuclidD d) :
    taylorHomogeneousTerm 2 L z = qform H z / 2 := by
  have h := Laplace.isAsymptoticExpansionTo_coeff_eq
    (D.rayExpansion_taylor z) (D.rayExpansion_quad z) 2 le_rfl
  simpa using h

/-- The named Gaussian lower bound for the quadratic term. -/
theorem t2_lower (D : ForwardExpansionDomain N L H) (z : EuclidD d) :
    D.lambda / 2 * ‖z‖ ^ 2 ≤ taylorHomogeneousTerm 2 L z := by
  rw [D.taylorHomogeneousTerm_two_eq_qform z]
  have h := D.qform_lower z
  linarith

/-- **Arbitrary-small Peano control on the window**: for every
`ε > 0`, eventually `|ρ_q(z)| ≤ ε‖z‖^(N+2)` on the mesoscopic set. -/
theorem eventually_abs_scaledRem_le (D : ForwardExpansionDomain N L H)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), ∀ z ∈ mesoscopicSet d q,
      |D.scaledRem q z| ≤ ε * ‖z‖ ^ (N + 2) := by
  have hlittle := D.taylorPeano
  rw [Asymptotics.isLittleO_iff] at hlittle
  have hev := hlittle hε
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ0, hδ⟩ := hev
  filter_upwards [smul_mem_ball_of_mesoscopic hδ0,
    self_mem_nhdsWithin] with q hball hq0' z hz
  have hq0 : (0 : ℝ) < q := Set.mem_Ioi.mp hq0'
  have hmem : dist (q • z) (0 : EuclidD d) < δ := by
    rw [dist_zero_right]
    exact hball z hz
  have hb := hδ hmem
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hb
  unfold ForwardExpansionDomain.scaledRem
  rw [abs_div, abs_of_pos (pow_pos hq0 (N + 2)),
    div_le_iff₀ (pow_pos hq0 (N + 2))]
  calc |D.taylorRem (q • z)| ≤ ε * |‖q • z‖ ^ (N + 2)| := hb
    _ = ε * ‖z‖ ^ (N + 2) * q ^ (N + 2) := by
        rw [abs_of_nonneg (by positivity), norm_smul, Real.norm_eq_abs,
          abs_of_pos hq0, mul_pow]
        ring

/-- The scaled perturbation is `≤ ε‖z‖²` on the window: the factor
`(q‖z‖)^N ≤ 1` converts the order-`(N+2)` bound to quadratic. -/
theorem eventually_abs_scaledPerturbation_le_quadratic
    (D : ForwardExpansionDomain N L H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), ∀ z ∈ mesoscopicSet d q,
      |q ^ N * D.scaledRem q z| ≤ ε * ‖z‖ ^ 2 := by
  filter_upwards [D.eventually_abs_scaledRem_le hε,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with q h1 hq z hz
  obtain ⟨hq0, hq1⟩ := hq
  have hrem := h1 z hz
  have hw : Real.sqrt q * ‖z‖ ≤ 1 := hz
  have hqz : q * ‖z‖ ≤ 1 := by
    have hsq1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1.le
    have hqsq : q = Real.sqrt q * Real.sqrt q :=
      (Real.mul_self_sqrt hq0.le).symm
    calc q * ‖z‖ = Real.sqrt q * (Real.sqrt q * ‖z‖) := by
          rw [← mul_assoc, ← hqsq]
      _ ≤ 1 * 1 := mul_le_mul hsq1 hw
          (mul_nonneg (Real.sqrt_nonneg q) (norm_nonneg z))
          zero_le_one
      _ = 1 := one_mul 1
  calc |q ^ N * D.scaledRem q z|
      = q ^ N * |D.scaledRem q z| := by
        rw [abs_mul, abs_of_pos (pow_pos hq0 N)]
    _ ≤ q ^ N * (ε * ‖z‖ ^ (N + 2)) :=
        mul_le_mul_of_nonneg_left hrem (pow_pos hq0 N).le
    _ = ε * ((q * ‖z‖) ^ N * ‖z‖ ^ 2) := by
        rw [pow_add, mul_pow]
        ring
    _ ≤ ε * (1 * ‖z‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hε.le
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact pow_le_one₀
          (mul_nonneg hq0.le (norm_nonneg z)) hqz
    _ = ε * ‖z‖ ^ 2 := by ring

/-- The homogeneous corrections are `≤ ε‖z‖²` on the window, in
sum-of-absolute-values form: `q^s‖z‖^(s+2) = ‖z‖²(q‖z‖)^s ≤ ‖z‖²√q`
for `s ≥ 1`. -/
theorem eventually_exponentCorrection_le_quadratic
    (_D : ForwardExpansionDomain N L H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), ∀ z ∈ mesoscopicSet d q,
      ∑ s ∈ Finset.Icc 1 N, q ^ s * |exponentTerm s L z| ≤
        ε * ‖z‖ ^ 2 := by
  set M : ℝ := ∑ s ∈ Finset.Icc 1 N,
    ((s + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (s + 2) L 0‖
    with hM_def
  have hM0 : 0 ≤ M :=
    Finset.sum_nonneg fun s _ ↦ by positivity
  have hsqrt : Tendsto (fun q : ℝ ↦ Real.sqrt q) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    have := Real.continuous_sqrt.tendsto (0 : ℝ)
    rw [Real.sqrt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun q : ℝ ↦ Real.sqrt q * (M + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hsqrt.mul_const (M + 1)
    rwa [zero_mul] at this
  filter_upwards [hlim.eventually_le_const hε,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with q hqε hq z hz
  obtain ⟨hq0, hq1⟩ := hq
  have hw : Real.sqrt q * ‖z‖ ≤ 1 := hz
  have hsq1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1.le
  have hqz : q * ‖z‖ ≤ Real.sqrt q := by
    have hqsq : q = Real.sqrt q * Real.sqrt q :=
      (Real.mul_self_sqrt hq0.le).symm
    calc q * ‖z‖ = Real.sqrt q * (Real.sqrt q * ‖z‖) := by
          rw [← mul_assoc, ← hqsq]
      _ ≤ Real.sqrt q * 1 :=
          mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg q)
      _ = Real.sqrt q := mul_one _
  have hterm : ∀ s ∈ Finset.Icc 1 N,
      q ^ s * |exponentTerm s L z| ≤
        ((s + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (s + 2) L 0‖ *
          (Real.sqrt q * ‖z‖ ^ 2) := by
    intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hV : |exponentTerm s L z| ≤
        ((s + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (s + 2) L 0‖ *
          ‖z‖ ^ (s + 2) := abs_taylorHomogeneousTerm_le (s + 2) L z
    calc q ^ s * |exponentTerm s L z|
        ≤ q ^ s * (((s + 2).factorial : ℝ)⁻¹ *
            ‖iteratedFDeriv ℝ (s + 2) L 0‖ * ‖z‖ ^ (s + 2)) :=
          mul_le_mul_of_nonneg_left hV (pow_pos hq0 s).le
      _ = ((s + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (s + 2) L 0‖ *
            ((q * ‖z‖) ^ s * ‖z‖ ^ 2) := by
          rw [pow_add, mul_pow]
          ring
      _ ≤ ((s + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (s + 2) L 0‖ *
            (Real.sqrt q * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (q * ‖z‖) ^ s ≤ Real.sqrt q ^ s :=
                pow_le_pow_left₀
                  (mul_nonneg hq0.le (norm_nonneg z)) hqz s
            _ ≤ Real.sqrt q ^ 1 :=
                pow_le_pow_of_le_one (Real.sqrt_nonneg q) hsq1 hs1
            _ = Real.sqrt q := pow_one _
  calc ∑ s ∈ Finset.Icc 1 N, q ^ s * |exponentTerm s L z|
      ≤ ∑ s ∈ Finset.Icc 1 N,
          ((s + 2).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (s + 2) L 0‖ *
            (Real.sqrt q * ‖z‖ ^ 2) := Finset.sum_le_sum hterm
    _ = Real.sqrt q * M * ‖z‖ ^ 2 := by
        rw [← Finset.sum_mul, hM_def]
        ring
    _ ≤ ε * ‖z‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc Real.sqrt q * M ≤ Real.sqrt q * (M + 1) := by
              refine mul_le_mul_of_nonneg_left (by linarith)
                (Real.sqrt_nonneg q)
          _ ≤ ε := hqε

/-- **Gaussian absorption**: on the window, the Gaussian core times
the exponential of the total absolute correction is dominated by a
Gaussian at a quarter of the domain's rate. This is the interface the
`q`-uniform majorant consumes. -/
theorem gaussian_absorb (D : ForwardExpansionDomain N L H) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), ∀ z ∈ mesoscopicSet d q,
      Real.exp (-taylorHomogeneousTerm 2 L z) *
        Real.exp ((∑ s ∈ Finset.Icc 1 N, q ^ s * |exponentTerm s L z|) +
          |q ^ N * D.scaledRem q z|) ≤
      Real.exp (-(D.lambda / 4) * ‖z‖ ^ 2) := by
  have hlam := D.lambda_pos
  filter_upwards [D.eventually_exponentCorrection_le_quadratic
      (show (0 : ℝ) < D.lambda / 8 by positivity),
    D.eventually_abs_scaledPerturbation_le_quadratic
      (show (0 : ℝ) < D.lambda / 8 by positivity)] with q h1 h2 z hz
  have ha := h1 z hz
  have hb := h2 z hz
  have hT2 := D.t2_lower z
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hT2, ha, hb]

end ForwardExpansionDomain

/-- Reusable integrability: `(1+‖z‖)^K` against any Gaussian. -/
theorem integrable_one_add_norm_pow_mul_gaussian (K : ℕ) {γ : ℝ}
    (hγ : 0 < γ) :
    Integrable (fun z : EuclidD d ↦
      (1 + ‖z‖) ^ K * Real.exp (-γ * ‖z‖ ^ 2)) := by
  have hpt : ∀ z : EuclidD d,
      (1 + ‖z‖) ^ K * Real.exp (-γ * ‖z‖ ^ 2) =
      ∑ i ∈ Finset.range (K + 1),
        (K.choose i : ℝ) * (‖z‖ ^ i * Real.exp (-γ * ‖z‖ ^ 2)) := by
    intro z
    rw [add_comm (1 : ℝ) ‖z‖, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [one_pow, mul_one]
    ring
  rw [show (fun z : EuclidD d ↦
      (1 + ‖z‖) ^ K * Real.exp (-γ * ‖z‖ ^ 2)) =
      fun z ↦ ∑ i ∈ Finset.range (K + 1),
        (K.choose i : ℝ) * (‖z‖ ^ i * Real.exp (-γ * ‖z‖ ^ 2))
    from funext hpt]
  exact integrable_finset_sum _ fun i _ ↦
    (integrable_pow_mul_exp_neg_mul_sq hγ i).const_mul _

end Laplace.Multi
