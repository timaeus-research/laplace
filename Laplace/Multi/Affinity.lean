/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TauberianVariance

/-!
# Affinity and ambient Fisher–Rao distance along the featureless line

The Bhattacharyya affinity of two posteriors on the featureless line is a state-density functional:

  `∫ √(p_s p_t) = Z((s+t)/2) / √(Z(s) Z(t))`   (`integral_sqrt_lawDensity_mul`,
                                                 `integral_sqrt_posterior_mul` at the model level),

so the Bhattacharyya divergence `−log ρ(s,t)` is the midpoint Jensen gap of the log-partition
function `F = log Z` (`log_lawAffinity`), and the **ambient Fisher–Rao distance**
`d_FR(P_s, P_t) = 2 arccos ρ(s,t)` is computable from `Z` alone. Under regular variation of `Z` with
index `−λ > 0`, `Z(t) → 0` (`tendsto_lawMoment_zero_of_regVar`), `ρ(0,t)² / Z(t) → 2^{2λ}/Z(0)`
(`tendsto_lawAffinity_sq_div`), hence `ρ(0,t) → 0` and

  `d_FR(P_0, P_t) → π`   (`tendsto_fisherRao_pi`):

the featureless ray reaches the maximal ambient separation `π`, while its own length grows like
`√λ log t` (`FeaturelessLawFromPartition`): the `√λ log t`, `√t` and `log log t` laws measure the
length of the distinguished response path, not the endpoint distance in the full posterior space
(Astra, round 26, Theorem A).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The tilted density of a state density at temperature `u` (relative to `ν`). -/
noncomputable def lawDensity (ν : Measure ℝ) (u ℓ : ℝ) : ℝ := Real.exp (-(u * ℓ)) / lawMoment ν 0 u

/-- The Bhattacharyya affinity `ρ(s,t) = Z((s+t)/2)/√(Z(s)Z(t))` of two featureless-line
posteriors. -/
noncomputable def lawAffinity (ν : Measure ℝ) (s t : ℝ) : ℝ :=
  lawMoment ν 0 ((s + t) / 2) / Real.sqrt (lawMoment ν 0 s * lawMoment ν 0 t)

/-- **The affinity formula**: `∫ √(p_s p_t) dν = Z((s+t)/2)/√(Z(s)Z(t))`. -/
theorem integral_sqrt_lawDensity_mul (ν : Measure ℝ) {s t : ℝ} (hs : 0 < lawMoment ν 0 s)
    (ht : 0 < lawMoment ν 0 t) :
    ∫ ℓ, Real.sqrt (lawDensity ν s ℓ * lawDensity ν t ℓ) ∂ν = lawAffinity ν s t := by
  unfold lawDensity lawAffinity
  have e : ∀ ℓ, Real.sqrt (Real.exp (-(s * ℓ)) / lawMoment ν 0 s *
      (Real.exp (-(t * ℓ)) / lawMoment ν 0 t)) =
      Real.exp (-((s + t) / 2 * ℓ)) / Real.sqrt (lawMoment ν 0 s * lawMoment ν 0 t) := fun ℓ ↦ by
    rw [div_mul_div_comm, Real.sqrt_div' _ (mul_pos hs ht).le, ← Real.exp_add, ← Real.exp_half]
    congr 2
    ring
  simp_rw [e]
  rw [integral_div]
  simp [lawMoment]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **The affinity formula at the model level**: for the posteriors `p_u = e^{-uL} π / Z(u)`,
`∫ √(p_s p_t) dμ = Z((s+t)/2)/√(Z(s)Z(t))`. -/
theorem integral_sqrt_posterior_mul {π L : X → ℝ} (hπ : ∀ x, 0 ≤ π x) {s t : ℝ}
    (hs : 0 < priorZ μ π L s) (ht : 0 < priorZ μ π L t) :
    ∫ x, Real.sqrt (Real.exp (-(s * L x)) * π x / priorZ μ π L s *
      (Real.exp (-(t * L x)) * π x / priorZ μ π L t)) ∂μ =
      priorZ μ π L ((s + t) / 2) / Real.sqrt (priorZ μ π L s * priorZ μ π L t) := by
  have e : ∀ x, Real.sqrt (Real.exp (-(s * L x)) * π x / priorZ μ π L s *
      (Real.exp (-(t * L x)) * π x / priorZ μ π L t)) =
      Real.exp (-((s + t) / 2 * L x)) * π x / Real.sqrt (priorZ μ π L s * priorZ μ π L t) :=
    fun x ↦ by
    rw [div_mul_div_comm, Real.sqrt_div' _ (mul_pos hs ht).le,
      show Real.exp (-(s * L x)) * π x * (Real.exp (-(t * L x)) * π x) =
        Real.exp (-(s * L x) + -(t * L x)) * (π x * π x) by rw [Real.exp_add]; ring,
      Real.sqrt_mul (Real.exp_pos _).le, ← Real.exp_half, Real.sqrt_mul_self (hπ x)]
    congr 3
    ring
  simp_rw [e]
  rw [integral_div]
  rfl

/-- **The Bhattacharyya divergence is the midpoint Jensen gap of `F = log Z`.** -/
theorem log_lawAffinity (ν : Measure ℝ) {s t : ℝ} (hs : 0 < lawMoment ν 0 s)
    (ht : 0 < lawMoment ν 0 t) (hm : 0 < lawMoment ν 0 ((s + t) / 2)) :
    Real.log (lawAffinity ν s t) =
      Real.log (lawMoment ν 0 ((s + t) / 2)) -
        (Real.log (lawMoment ν 0 s) + Real.log (lawMoment ν 0 t)) / 2 := by
  unfold lawAffinity
  rw [Real.log_div hm.ne' (Real.sqrt_pos.mpr (mul_pos hs ht)).ne', Real.log_sqrt (mul_pos hs ht).le,
    Real.log_mul hs.ne' ht.ne']

/-- Under regular variation with index `−λ < 0` and a nonneg state density, `Z(t) → 0`. -/
theorem tendsto_lawMoment_zero_of_regVar (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
    (hint : ∀ u > 0, Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) {lam : ℝ} (hlam : 0 < lam) (hreg : RegVar ν lam) :
    Tendsto (fun u ↦ lawMoment ν 0 u) atTop (𝓝 0) := by
  -- `Z` is antitone on `(0, ∞)`
  have hanti : ∀ u v, 0 < u → u ≤ v → lawMoment ν 0 v ≤ lawMoment ν 0 u := fun u v hu huv ↦ by
    unfold lawMoment
    simp only [pow_zero, one_mul]
    refine integral_mono_ae (hint v (lt_of_lt_of_le hu huv)) (hint u hu) ?_
    filter_upwards [hpos] with ℓ hℓ
    exact Real.exp_le_exp.mpr (by nlinarith)
  -- doubling contracts by a factor `r < 1`
  set r : ℝ := ((2 : ℝ) ^ (-lam) + 1) / 2 with hr
  have h2lam : (2 : ℝ) ^ (-lam) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have h2pos : 0 < (2 : ℝ) ^ (-lam) := Real.rpow_pos_of_pos two_pos _
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hev := (hreg 2 two_pos).eventually
    (gt_mem_nhds (show (2 : ℝ) ^ (-lam) < r by rw [hr]; linarith))
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  set U := max U₀ 1 with hU
  have hU1 : 1 ≤ U := le_max_right _ _
  have hUpos : 0 < U := lt_of_lt_of_le one_pos hU1
  have hdouble : ∀ u, U ≤ u → lawMoment ν 0 (2 * u) ≤ r * lawMoment ν 0 u := fun u hu ↦ by
    have hu0 : 0 < u := lt_of_lt_of_le hUpos hu
    have := hU₀ u (le_trans (le_max_left _ _) hu)
    rw [div_lt_iff₀ (hZ u hu0)] at this
    exact this.le
  have hpow : ∀ n : ℕ, lawMoment ν 0 (2 ^ n * U) ≤ r ^ n * lawMoment ν 0 U := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hUn : U ≤ 2 ^ n * U := by
        have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        nlinarith
      calc lawMoment ν 0 (2 ^ (n + 1) * U) = lawMoment ν 0 (2 * (2 ^ n * U)) := by ring_nf
        _ ≤ r * lawMoment ν 0 (2 ^ n * U) := hdouble _ hUn
        _ ≤ r * (r ^ n * lawMoment ν 0 U) := by gcongr
        _ = r ^ (n + 1) * lawMoment ν 0 U := by ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ ↦ r ^ n * lawMoment ν 0 U) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).mul_const (lawMoment ν 0 U)
    simpa using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨2 ^ n * U, fun u hu ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (hZ u (lt_of_lt_of_le (by positivity) hu))]
  calc lawMoment ν 0 u ≤ lawMoment ν 0 (2 ^ n * U) := hanti _ _ (by positivity) hu
    _ ≤ r ^ n * lawMoment ν 0 U := hpow n
    _ < ε := hn

/-- `ρ(0,t)² / Z(t) → 2^{2λ} / Z(0)` under regular variation. -/
theorem tendsto_lawAffinity_sq_div (ν : Measure ℝ) (hZ : ∀ u, 0 ≤ u → 0 < lawMoment ν 0 u)
    {lam : ℝ} (hreg : RegVar ν lam) :
    Tendsto (fun t ↦ lawAffinity ν 0 t ^ 2 / lawMoment ν 0 t) atTop
      (𝓝 ((2 : ℝ) ^ (2 * lam) / lawMoment ν 0 0)) := by
  have h := hreg (1 / 2) (by norm_num)
  have e2 : ((1 : ℝ) / 2) ^ (-lam) = 2 ^ lam := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  rw [e2] at h
  have hlim := ((h.pow 2).div_const (lawMoment ν 0 0))
  have e3 : ((2 : ℝ) ^ lam) ^ 2 = 2 ^ (2 * lam) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
    ring_nf
  rw [e3] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  unfold lawAffinity
  have h0 := hZ 0 le_rfl
  have ht' := hZ t ht.le
  have hm : (0 + t) / 2 = 1 / 2 * t := by ring
  rw [hm]
  simp only [div_pow]
  rw [Real.sq_sqrt (mul_pos h0 ht').le]
  field_simp

/-- `ρ(0,t) → 0` under regular variation with `λ > 0`. -/
theorem tendsto_lawAffinity_zero (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
    (hint : ∀ u > 0, Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν)
    (hZ : ∀ u, 0 ≤ u → 0 < lawMoment ν 0 u) {lam : ℝ} (hlam : 0 < lam) (hreg : RegVar ν lam) :
    Tendsto (fun t ↦ lawAffinity ν 0 t) atTop (𝓝 0) := by
  have h1 := tendsto_lawAffinity_sq_div ν hZ hreg
  have h2 := tendsto_lawMoment_zero_of_regVar ν hpos hint (fun u hu ↦ hZ u hu.le) hlam hreg
  have hsq : Tendsto (fun t ↦ lawAffinity ν 0 t ^ 2) atTop (𝓝 0) := by
    have := h1.mul h2
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [div_mul_cancel₀ _ (hZ t ht.le).ne']
  have hnn : ∀ t, 0 < t → 0 ≤ lawAffinity ν 0 t := fun t ht ↦ by
    unfold lawAffinity
    exact div_nonneg (hZ _ (by positivity)).le (Real.sqrt_nonneg _)
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply]
  rw [Real.sqrt_sq (hnn t ht)]

/-- **The ambient Fisher–Rao distance to the featureless posterior tends to `π`**, while the length
of the featureless line grows like `√λ log t`. -/
theorem tendsto_fisherRao_pi (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
    (hint : ∀ u > 0, Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν)
    (hZ : ∀ u, 0 ≤ u → 0 < lawMoment ν 0 u) {lam : ℝ} (hlam : 0 < lam) (hreg : RegVar ν lam) :
    Tendsto (fun t ↦ 2 * Real.arccos (lawAffinity ν 0 t)) atTop (𝓝 Real.pi) := by
  have h := (Real.continuous_arccos.tendsto 0).comp
    (tendsto_lawAffinity_zero ν hpos hint hZ hlam hreg)
  rw [Real.arccos_zero] at h
  have := h.const_mul 2
  rw [show 2 * (Real.pi / 2) = Real.pi by ring] at this
  exact this

end Laplace.Multi
