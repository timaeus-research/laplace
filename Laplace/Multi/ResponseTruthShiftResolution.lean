/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSamplingBoundary
import Laplace.Multi.CoefficientTiltDifferentiation
import Laplace.Multi.DataRayBlocks
import Laplace.Multi.RateFunction
import Laplace.Multi.SusceptibilityDefect

/-!
# Truth-shift resolution: when a moving truth becomes sign-resolvable from samples

Two sources move the structural coordinate `⟨a, M⟩`: a change of the data law (the truth moves)
and the sampling noise of the empirical coordinate `⟨a, M̂_n⟩`. Along a data path `t ↦ ρ_t` with
population coordinate `c(t) = E_{ρ_t}⟨a,S⟩` and truth velocity `d = c'(0) ≠ 0`, the sign of the
shift `c(t) − c(0)` is the sign of `d` for small `t > 0`, and the empirical coordinate reports the
wrong sign only if its sampling deviation exceeds the shift.

* `measureReal_wrongSign_le`: for a fixed law and any baseline `b ≠ ⟨a, M_D⟩`, the empirical
  coordinate lands on the wrong side of `b` with probability `≤ Var_D⟨a,S⟩ / (n (⟨a,M_D⟩ − b)²)`
  (both orientations of the wall-crossing bound).
* `eventually_sign_of_hasDerivAt`: a differentiable path with `c'(0) = d ≠ 0` eventually has
  `(c(t) − c(0)) d > 0` and `|c(t) − c(0)| ≥ |d| t / 2` for `t → 0⁺`.
* `eventually_measureReal_wrongTruthSign_le`: **the local-alternative bound** — for small `t > 0`
  the probability that the empirical shift has the wrong sign is `≤ 4 Var_{ρ_t}⟨a,S⟩ / (n d² t²)`.
* `truthShift_sign_resolved_of_sampleSize`: under a local variance bound `V`, once
  `4 V ≤ ε n d² t²` the sign of the truth shift is read correctly with probability `≥ 1 − ε`:
  the truth shift is resolved exactly when the shift `|d| t` exceeds the sampling scale `√(V/n)`.
* `hasDerivAt_pathCoord_tilted`: along an exponential data journey `ρ_t = ν.tilted ⟨a_t, h⟩`
  the truth velocity is the covariance `Cov_{ρ_0}(⟨a,S⟩, ⟨a'_0, h⟩)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Sign

/-- A differentiable real path with nonzero derivative at `0` eventually moves in the direction of
its derivative, by at least half the linear rate. -/
theorem eventually_sign_of_hasDerivAt {c : ℝ → ℝ} {d : ℝ} (hc : HasDerivAt c d 0) (hd : d ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (c t - c 0) * d ∧ |d| * t / 2 ≤ |c t - c 0| := by
  have hslope : Tendsto (fun t : ℝ ↦ t⁻¹ • (c (0 + t) - c 0)) (𝓝[>] 0) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope_zero.mp hc).mono_left
      (nhdsWithin_mono _ fun t (ht : 0 < t) ↦ ht.ne')
  have hd2 : 0 < |d| / 2 := by positivity
  filter_upwards [hslope.eventually (Metric.ball_mem_nhds d hd2), self_mem_nhdsWithin]
    with t hq ht
  have ht : 0 < t := ht
  rw [Real.dist_eq, smul_eq_mul, zero_add] at hq
  set q := t⁻¹ * (c t - c 0) with hqdef
  have hct : c t - c 0 = t * q := by rw [hqdef, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  rw [hct, abs_mul, abs_of_pos ht]
  have hqd : 0 < q * d ∧ |d| / 2 ≤ |q| := by
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · rw [abs_of_neg hneg] at hq ⊢
      have hq' := abs_lt.mp hq
      have hq0 : q < 0 := by linarith
      rw [abs_of_neg hq0]
      constructor <;> nlinarith
    · rw [abs_of_pos hpos] at hq ⊢
      have hq' := abs_lt.mp hq
      have hq0 : 0 < q := by linarith
      rw [abs_of_pos hq0]
      constructor <;> nlinarith
  refine ⟨by rw [mul_assoc]; exact mul_pos ht hqd.1, ?_⟩
  rw [div_eq_mul_one_div, mul_comm |d|, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by rw [← div_eq_mul_one_div]; exact hqd.2) ht.le

end Sign

section Wall

variable {X : Type*} {J : Type*} {Ω : Type*} [MeasurableSpace X] [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hS hXm hid hlaw

/-- **Wrong sign of a finite truth shift**: for any baseline `b ≠ ⟨a, M_D⟩`, the empirical
coordinate lands on the wrong side of `b` (relative to the truth) with probability at most
`Var_D⟨a,S⟩ / (n (⟨a,M_D⟩ − b)²)`. -/
theorem measureReal_wrongSign_le (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) (a : J → ℝ) {b : ℝ} (hb : b ≠ dotJ a (fun j ↦ ∫ x, S j x ∂D)) :
    P.real {ω | (dotJ a (sampleResponse S Xs n ω) - b) *
        (dotJ a (fun j ↦ ∫ x, S j x ∂D) - b) ≤ 0} ≤
      lawCov D (dirLoss S a) (dirLoss S a) / (n * (dotJ a (fun j ↦ ∫ x, S j x ∂D) - b) ^ 2) := by
  set m : J → ℝ := fun j ↦ ∫ x, S j x ∂D with hm
  rcases lt_or_gt_of_ne hb with hlt | hgt
  · have hset : {ω | (dotJ a (sampleResponse S Xs n ω) - b) * (dotJ a m - b) ≤ 0} =
        {ω | dotJ a (sampleResponse S Xs n ω) ≤ b} := by
      ext ω
      simp only [mem_ofPred_eq]
      constructor <;> intro h <;> nlinarith
    rw [hset]
    exact measureReal_dotJ_sampleResponse_le_le hS P D Xs hXm hid hlaw hind hn a hlt
  · have hset : {ω | (dotJ a (sampleResponse S Xs n ω) - b) * (dotJ a m - b) ≤ 0} =
        {ω | dotJ (-a) (sampleResponse S Xs n ω) ≤ -b} := by
      ext ω
      simp only [mem_ofPred_eq, dotJ_neg_left]
      constructor <;> intro h <;> nlinarith
    have hlt' : -b < dotJ (-a) m := by rw [dotJ_neg_left]; linarith
    have h := measureReal_dotJ_sampleResponse_le_le hS P D Xs hXm hid hlaw hind hn (-a) hlt'
    have hneg : dirLoss S (-a) = fun x ↦ -dirLoss S a x := funext fun x ↦ dirLoss_neg a x
    rw [hneg, lawCov_neg_left, lawCov_neg_right_eq, neg_neg, dotJ_neg_left,
      show (-dotJ a m - -b) ^ 2 = (dotJ a m - b) ^ 2 by ring] at h
    rw [hset]
    exact h

end Wall

section Path

variable {X : Type*} {J : Type*} {Ω : Type*} [MeasurableSpace X] [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : ℝ → Measure X) [∀ t, IsProbabilityMeasure (D t)] (Xs : ℝ → ℕ → Ω → X)
  (hXm : ∀ t i, Measurable (Xs t i)) (hid : ∀ t i, IdentDistrib (Xs t i) (Xs t 0) P P)
  (hlaw : ∀ t, P.map (Xs t 0) = D t)

/-- The population structural coordinate `c(t) = ⟨a, E_{ρ_t} S⟩` along a data path. -/
noncomputable def pathCoord (S : J → X → ℝ) (D : ℝ → Measure X) (a : J → ℝ) (t : ℝ) : ℝ :=
  dotJ a fun j ↦ ∫ x, S j x ∂(D t)

include hS hXm hid hlaw

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] hXm hid hlaw in
/-- The population coordinate is the expectation of the direction observable. -/
theorem pathCoord_eq_integral (a : J → ℝ) (t : ℝ) :
    pathCoord S D a t = ∫ x, dirLoss S a x ∂(D t) := by
  rw [pathCoord, ← integral_dirLoss_eq_dotJ (u := a) (D t) hS]

/-- **The local-alternative wrong-sign bound**: if the population coordinate moves with velocity
`d ≠ 0` at `t = 0`, then for small `t > 0` the empirical shift `⟨a, M̂_n⟩ − c(0)` has the wrong sign
with probability at most `4 Var_{ρ_t}⟨a,S⟩ / (n d² t²)`. -/
theorem eventually_measureReal_wrongTruthSign_le
    (hind : ∀ t i k, i ≠ k → IndepFun (Xs t i) (Xs t k) P) {n : ℕ} (hn : 0 < n) (a : J → ℝ)
    {d : ℝ} (hd : d ≠ 0) (hc : HasDerivAt (pathCoord S D a) d 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      P.real {ω | (dotJ a (sampleResponse S (Xs t) n ω) - pathCoord S D a 0) * d ≤ 0} ≤
        4 * lawCov (D t) (dirLoss S a) (dirLoss S a) / (n * d ^ 2 * t ^ 2) := by
  filter_upwards [eventually_sign_of_hasDerivAt hc hd, self_mem_nhdsWithin] with t hsign ht
  have ht : 0 < t := ht
  obtain ⟨hpos, hlow⟩ := hsign
  set c0 := pathCoord S D a 0 with hc0
  set ct := pathCoord S D a t with hct
  have hne : c0 ≠ ct := fun h ↦ by rw [h, sub_self, zero_mul] at hpos; exact lt_irrefl _ hpos
  -- same sign: the wrong-sign event relative to `d` is the wrong-sign event relative to the shift
  have hset : {ω | (dotJ a (sampleResponse S (Xs t) n ω) - c0) * d ≤ 0} =
      {ω | (dotJ a (sampleResponse S (Xs t) n ω) - c0) * (ct - c0) ≤ 0} := by
    ext ω
    simp only [mem_ofPred_eq]
    rcases lt_or_gt_of_ne hd with hneg | hdpos
    · have hs : ct - c0 < 0 := by nlinarith
      constructor <;> intro h <;> nlinarith
    · have hs : 0 < ct - c0 := by nlinarith
      constructor <;> intro h <;> nlinarith
  have hbound := measureReal_wrongSign_le hS P (D t) (Xs t) (hXm t) (hid t) (hlaw t) (hind t) hn a
    (b := c0) hne
  rw [hset]
  refine hbound.trans ?_
  have hV := lawCov_self_nonneg (D t) (bdd_dirLoss hS a)
  have hsq : n * d ^ 2 * t ^ 2 / 4 ≤ n * (ct - c0) ^ 2 := by
    have h2 := pow_le_pow_left₀ (by positivity) hlow 2
    rw [div_pow, mul_pow, sq_abs, sq_abs] at h2
    have hn' : (0 : ℝ) ≤ n := by positivity
    calc n * d ^ 2 * t ^ 2 / 4 = n * (d ^ 2 * t ^ 2 / 2 ^ 2) := by ring
      _ ≤ n * (ct - c0) ^ 2 := mul_le_mul_of_nonneg_left h2 hn'
  have hpos' : 0 < n * d ^ 2 * t ^ 2 / 4 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  calc lawCov (D t) (dirLoss S a) (dirLoss S a) / (n * (ct - c0) ^ 2)
      ≤ lawCov (D t) (dirLoss S a) (dirLoss S a) / (n * d ^ 2 * t ^ 2 / 4) :=
        div_le_div_of_nonneg_left hV hpos' hsq
    _ = 4 * lawCov (D t) (dirLoss S a) (dirLoss S a) / (n * d ^ 2 * t ^ 2) := by
        rw [div_div_eq_mul_div]; ring

/-- **Truth-shift resolution**: under a local variance bound `Var_{ρ_t}⟨a,S⟩ ≤ V`, once the sample
size satisfies `4 V ≤ ε n d² t²` the sign of the truth shift is read correctly from `n` samples with
probability at least `1 − ε`. -/
theorem truthShift_sign_resolved_of_sampleSize
    (hind : ∀ t i k, i ≠ k → IndepFun (Xs t i) (Xs t k) P) {n : ℕ} (hn : 0 < n) (a : J → ℝ)
    {d : ℝ} (hd : d ≠ 0) (hc : HasDerivAt (pathCoord S D a) d 0) {V ε : ℝ}
    (hV : ∀ᶠ t in 𝓝[>] (0 : ℝ), lawCov (D t) (dirLoss S a) (dirLoss S a) ≤ V) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 4 * V ≤ ε * (n * d ^ 2 * t ^ 2) →
      1 - ε ≤ P.real {ω | 0 < (dotJ a (sampleResponse S (Xs t) n ω) - pathCoord S D a 0) * d} := by
  filter_upwards [eventually_measureReal_wrongTruthSign_le hS P D Xs hXm hid hlaw hind hn a hd hc,
    hV, self_mem_nhdsWithin] with t hwrong hVt ht hε
  have ht : 0 < t := ht
  have hmeas : MeasurableSet
      {ω | (dotJ a (sampleResponse S (Xs t) n ω) - pathCoord S D a 0) * d ≤ 0} :=
    measurableSet_le (((measurable_dotJ_sampleResponse hS (Xs t) (hXm t) n a).sub
      measurable_const).mul_const d) measurable_const
  have hcompl : {ω | 0 < (dotJ a (sampleResponse S (Xs t) n ω) - pathCoord S D a 0) * d} =
      {ω | (dotJ a (sampleResponse S (Xs t) n ω) - pathCoord S D a 0) * d ≤ 0}ᶜ := by
    ext ω; simp [not_le]
  rw [hcompl, measureReal_compl hmeas, probReal_univ]
  have hden : 0 < (n : ℝ) * d ^ 2 * t ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hle : 4 * lawCov (D t) (dirLoss S a) (dirLoss S a) / (n * d ^ 2 * t ^ 2) ≤ ε := by
    rw [div_le_iff₀ hden]
    linarith
  linarith

end Path

section Journey

variable {X : Type*} {J : Type*} [MeasurableSpace X] [Nonempty X] [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) {ι : Type*} [Fintype ι] (ν : Measure X) [IsProbabilityMeasure ν]
  {h : ι → X → ℝ} (hh : ∀ j, Bdd (h j)) {a a' : ℝ → ι → ℝ} (ha : ∀ t, HasDerivAt a (a' t) t)
  (ha' : Continuous a')
include hS hh ha ha'

/-- **The truth velocity of an exponential data journey** `ρ_t = ν.tilted ⟨a_t, h⟩` in the
structural direction `w` is the covariance `Cov_{ρ_0}(⟨w,S⟩, ⟨a'_0, h⟩)`. -/
theorem hasDerivAt_pathCoord_tilted (w : J → ℝ) :
    HasDerivAt (pathCoord S (fun t ↦ ν.tilted (dirLoss h (a t))) w)
      (lawCov (ν.tilted (dirLoss h (a 0))) (dirLoss S w) (dirLoss h (a' 0))) 0 := by
  have hP : ∀ t, IsProbabilityMeasure (ν.tilted (dirLoss h (a t))) := fun t ↦
    isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t)))
  refine (hasDerivAt_integral_tilted_dirLoss ν hh ha ha' (bdd_dirLoss hS w) 0).congr_of_eventuallyEq
    (Eventually.of_forall fun t ↦ ?_)
  exact (pathCoord_eq_integral hS (fun t ↦ ν.tilted (dirLoss h (a t))) w t)

end Journey

end Laplace.Multi
