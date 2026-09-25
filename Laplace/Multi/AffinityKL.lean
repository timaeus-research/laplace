/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.InformationProjection
import Laplace.Multi.Affinity

/-!
# The exact affinity–KL decomposition and the dilation geometry of the featureless line

**Part A (affine family, exact).** For `a_θ = (1−θ)a + θb` and the Jensen gap
`C_θ = (1−θ)A(a) + θA(b) − A(a_θ)` of the log-partition function `A = affLogZ`, every probability
density `q` satisfies the weighted decomposition

  `(1−θ) KL(q‖P_a) + θ KL(q‖P_b) = KL(q‖P_{a_θ}) + C_θ`   (`relEnt_convex_comb`).

At the midpoint `C_{1/2} = B(a,b) = −log ρ(a,b)` is the Bhattacharyya divergence, and taking
`q = P_a` gives the exact refinement of `B ≤ ½ KL`:

  `½ KL(P_a‖P_b) − B(a,b) = KL(P_a‖P_m)`   (`half_relEnt_sub_affBhat`),

together with the variational characterisation `B(a,b) = inf_q ½(KL(q‖P_a) + KL(q‖P_b))`, attained
at the normalised geometric mean `P_m` (`affBhat_le_half_add`, `affBhat_eq_at_mid`).

**Part B (featureless line, asymptotic).** Along a state density with regularly varying partition
function of index `−λ`, in log-temperature coordinates all three quantities have universal limits:

  `KL(P_{cu}‖P_{du}) → λ (d/c − 1 − log(d/c))`, `−log ρ(cu,du) → λ log((c+d)/(2√(cd)))`,
  `½ KL(P_u‖P_0) + log ρ(0,u) → λ (log 2 − ½)`

(`tendsto_lawKL_dilation`, `tendsto_neg_log_lawAffinity_dilation`, `tendsto_endpoint_identity`),
complementing `∫_{cu}^{du} √Var → √λ log(d/c)` (`TauberianVariance`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### Part A: the affine family -/

section General

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- `KL(p ‖ p) = 0`. -/
theorem relEnt_self (p : X → ℝ) : relEnt μ p p = 0 := by
  unfold relEnt
  have : ∀ x, p x * Real.log (p x / p x) = 0 := fun x ↦ by
    by_cases h : p x = 0
    · simp [h]
    · rw [div_self h, Real.log_one, mul_zero]
  simp only [this, integral_zero]

/-- `log p_{t,L}(x) = −tL(x) + log π(x) − log Z`. -/
theorem log_gibbsDensity_eq {π L : X → ℝ} (hπ : ∀ x, 0 < π x) {t : ℝ}
    (hZ : 0 < priorZ μ π L t) (x : X) :
    Real.log (gibbsDensity μ π L t x) =
      -(t * L x) + Real.log (π x) - Real.log (priorZ μ π L t) := by
  unfold gibbsDensity
  rw [Real.log_div (mul_pos (Real.exp_pos _) (hπ x)).ne' hZ.ne',
    Real.log_mul (Real.exp_pos _).ne' (hπ x).ne', Real.log_exp]

end General

section Affine

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

omit [MeasurableSpace X] in
/-- The affine loss is affine in the parameter. -/
theorem affLoss_convex_comb (L₀ : X → ℝ) (R : ι → X → ℝ) (θ : ℝ) (a b : ι → ℝ) (x : X) :
    affLoss L₀ R ((1 - θ) • a + θ • b) x = (1 - θ) * affLoss L₀ R a x + θ * affLoss L₀ R b x := by
  simp only [affLoss, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : ∑ i, ((1 - θ) * a i + θ * b i) * R i x =
      (1 - θ) * ∑ i, a i * R i x + θ * ∑ i, b i * R i x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [this]
  ring

/-- The Jensen gap of the log-partition function along the segment `[a, b]` at weight `θ`. -/
noncomputable def affJensenGap (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t θ : ℝ)
    (a b : ι → ℝ) : ℝ :=
  (1 - θ) * affLogZ μ π L₀ R t a + θ * affLogZ μ π L₀ R t b -
    affLogZ μ π L₀ R t ((1 - θ) • a + θ • b)

/-- The Bhattacharyya divergence `B(a,b) = (A(a) + A(b))/2 − A((a+b)/2) = −log ρ(a,b)`. -/
noncomputable def affBhat (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a b : ι → ℝ) :
    ℝ :=
  (affLogZ μ π L₀ R t a + affLogZ μ π L₀ R t b) / 2 - affLogZ μ π L₀ R t ((1 / 2 : ℝ) • (a + b))

omit [MeasurableSpace X] [Fintype ι] in
theorem convex_comb_half (a b : ι → ℝ) :
    (1 - (1 / 2 : ℝ)) • a + (1 / 2 : ℝ) • b = (1 / 2 : ℝ) • (a + b) := by
  rw [smul_add]; norm_num

theorem affJensenGap_half (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a b : ι → ℝ) :
    affJensenGap μ π L₀ R t (1 / 2) a b = affBhat μ π L₀ R t a b := by
  unfold affJensenGap affBhat
  rw [convex_comb_half]
  ring

variable {π L₀ : X → ℝ} (hπ : ∀ x, 0 < π x) {R : ι → X → ℝ} {t θ : ℝ} {a b : ι → ℝ}
  (hZa : 0 < priorZ μ π (affLoss L₀ R a) t) (hZb : 0 < priorZ μ π (affLoss L₀ R b) t)
  (hZθ : 0 < priorZ μ π (affLoss L₀ R ((1 - θ) • a + θ • b)) t)
include hπ hZa hZb hZθ

/-- The pointwise KL-integrand identity along the segment. -/
theorem relEnt_integrand_convex_comb (q : X → ℝ) (x : X) :
    q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R ((1 - θ) • a + θ • b)) t x) =
      (1 - θ) * (q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) +
        θ * (q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R b) t x)) -
        affJensenGap μ π L₀ R t θ a b * q x := by
  have hπ' : ∀ x, 0 ≤ π x := fun x ↦ (hπ x).le
  by_cases hq : q x = 0
  · simp [hq]
  rw [Real.log_div hq (gibbsDensity_pos hπ' hZθ (hπ x).ne').ne',
    Real.log_div hq (gibbsDensity_pos hπ' hZa (hπ x).ne').ne',
    Real.log_div hq (gibbsDensity_pos hπ' hZb (hπ x).ne').ne',
    log_gibbsDensity_eq hπ hZθ, log_gibbsDensity_eq hπ hZa, log_gibbsDensity_eq hπ hZb,
    affLoss_convex_comb]
  unfold affJensenGap affLogZ
  ring

/-- Integrability of the segment KL integrand from the endpoint ones. -/
theorem integrable_relEnt_integrand_convex_comb {q : X → ℝ} (hqi : Integrable q μ)
    (hka : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) μ)
    (hkb : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R b) t x)) μ) :
    Integrable (fun x ↦ q x *
      Real.log (q x / gibbsDensity μ π (affLoss L₀ R ((1 - θ) • a + θ • b)) t x)) μ := by
  have h : Integrable (fun x ↦ (1 - θ) *
      (q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) +
        θ * (q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R b) t x)) -
        affJensenGap μ π L₀ R t θ a b * q x) μ :=
    ((hka.const_mul _).add (hkb.const_mul _)).sub (hqi.const_mul _)
  exact h.congr (Filter.Eventually.of_forall fun x ↦
    (relEnt_integrand_convex_comb hπ hZa hZb hZθ q x).symm)

/-- **The weighted affinity–KL decomposition**:
`(1−θ) KL(q‖P_a) + θ KL(q‖P_b) = KL(q‖P_{a_θ}) + C_θ` for every probability density `q`. -/
theorem relEnt_convex_comb {q : X → ℝ} (hqi : Integrable q μ) (hq1 : ∫ x, q x ∂μ = 1)
    (hka : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) μ)
    (hkb : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R b) t x)) μ) :
    (1 - θ) * relEnt μ q (gibbsDensity μ π (affLoss L₀ R a) t) +
        θ * relEnt μ q (gibbsDensity μ π (affLoss L₀ R b) t) =
      relEnt μ q (gibbsDensity μ π (affLoss L₀ R ((1 - θ) • a + θ • b)) t) +
        affJensenGap μ π L₀ R t θ a b := by
  unfold relEnt
  have h1 : Integrable (fun x ↦ (1 - θ) *
      (q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) +
        θ * (q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R b) t x))) μ :=
    (hka.const_mul _).add (hkb.const_mul _)
  rw [integral_congr_ae
      (Filter.Eventually.of_forall (relEnt_integrand_convex_comb hπ hZa hZb hZθ q)),
    integral_sub h1 (hqi.const_mul _), integral_add (hka.const_mul _) (hkb.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, hq1]
  ring

end Affine

section Midpoint

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]
  {π L₀ : X → ℝ} (hπ : ∀ x, 0 < π x) {R : ι → X → ℝ} {t : ℝ} {a b : ι → ℝ}
  (hZa : 0 < priorZ μ π (affLoss L₀ R a) t) (hZb : 0 < priorZ μ π (affLoss L₀ R b) t)
  (hZm : 0 < priorZ μ π (affLoss L₀ R ((1 / 2 : ℝ) • (a + b))) t)
include hπ hZa hZb hZm

/-- **The midpoint decomposition**: `½ KL(q‖P_a) + ½ KL(q‖P_b) = KL(q‖P_m) + B(a,b)`. -/
theorem relEnt_midpoint {q : X → ℝ} (hqi : Integrable q μ) (hq1 : ∫ x, q x ∂μ = 1)
    (hka : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) μ)
    (hkb : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R b) t x)) μ) :
    (relEnt μ q (gibbsDensity μ π (affLoss L₀ R a) t) +
        relEnt μ q (gibbsDensity μ π (affLoss L₀ R b) t)) / 2 =
      relEnt μ q (gibbsDensity μ π (affLoss L₀ R ((1 / 2 : ℝ) • (a + b))) t) +
        affBhat μ π L₀ R t a b := by
  have hZθ : 0 < priorZ μ π (affLoss L₀ R ((1 - (1 / 2 : ℝ)) • a + (1 / 2 : ℝ) • b)) t := by
    rw [convex_comb_half]; exact hZm
  have h := relEnt_convex_comb hπ hZa hZb hZθ hqi hq1 hka hkb
  rw [convex_comb_half, affJensenGap_half] at h
  rw [← h]
  ring

/-- **The exact affinity–KL identity**: `½ KL(P_a‖P_b) − B(a,b) = KL(P_a‖P_m)`. -/
theorem half_relEnt_sub_affBhat
    (hZint : Integrable (fun x ↦ Real.exp (-(t * affLoss L₀ R a x)) * π x) μ)
    (hkab : Integrable (fun x ↦ gibbsDensity μ π (affLoss L₀ R a) t x *
      Real.log (gibbsDensity μ π (affLoss L₀ R a) t x /
        gibbsDensity μ π (affLoss L₀ R b) t x)) μ) :
    relEnt μ (gibbsDensity μ π (affLoss L₀ R a) t) (gibbsDensity μ π (affLoss L₀ R b) t) / 2 -
        affBhat μ π L₀ R t a b =
      relEnt μ (gibbsDensity μ π (affLoss L₀ R a) t)
        (gibbsDensity μ π (affLoss L₀ R ((1 / 2 : ℝ) • (a + b))) t) := by
  have hkaa : Integrable (fun x ↦ gibbsDensity μ π (affLoss L₀ R a) t x *
      Real.log (gibbsDensity μ π (affLoss L₀ R a) t x /
        gibbsDensity μ π (affLoss L₀ R a) t x)) μ := by
    refine (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    by_cases h : gibbsDensity μ π (affLoss L₀ R a) t x = 0
    · simp [h]
    · simp only [Pi.zero_apply, div_self h, Real.log_one, mul_zero]
  have h := relEnt_midpoint hπ hZa hZb hZm (integrable_gibbsDensity hZint)
    (integral_gibbsDensity hZa) hkaa hkab
  rw [relEnt_self, zero_add] at h
  linarith

/-- **Variational characterisation, inequality**: `B(a,b) ≤ ½(KL(q‖P_a) + KL(q‖P_b))` for every
probability density `q ≥ 0`. -/
theorem affBhat_le_half_add
    (hZint : Integrable
      (fun x ↦ Real.exp (-(t * affLoss L₀ R ((1 / 2 : ℝ) • (a + b)) x)) * π x) μ)
    {q : X → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hqi : Integrable q μ) (hq1 : ∫ x, q x ∂μ = 1)
    (hka : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) μ)
    (hkb : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R b) t x)) μ) :
    affBhat μ π L₀ R t a b ≤
      (relEnt μ q (gibbsDensity μ π (affLoss L₀ R a) t) +
        relEnt μ q (gibbsDensity μ π (affLoss L₀ R b) t)) / 2 := by
  rw [relEnt_midpoint hπ hZa hZb hZm hqi hq1 hka hkb]
  have hZθ : 0 < priorZ μ π (affLoss L₀ R ((1 - (1 / 2 : ℝ)) • a + (1 / 2 : ℝ) • b)) t := by
    rw [convex_comb_half]; exact hZm
  have hint := integrable_relEnt_integrand_convex_comb hπ hZa hZb hZθ hqi hka hkb
  rw [convex_comb_half] at hint
  have := relEnt_gibbsDensity_nonneg (fun x ↦ (hπ x).le) hZm hZint hq0
    (fun x _ ↦ (hπ x).ne') hq1 hqi hint
  linarith

/-- **Variational characterisation, attainment**: at the normalised geometric mean `q = P_m`,
`½(KL(P_m‖P_a) + KL(P_m‖P_b)) = B(a,b)`. -/
theorem affBhat_eq_at_mid
    (hkma : Integrable (fun x ↦ gibbsDensity μ π (affLoss L₀ R ((1 / 2 : ℝ) • (a + b))) t x *
      Real.log (gibbsDensity μ π (affLoss L₀ R ((1 / 2 : ℝ) • (a + b))) t x /
        gibbsDensity μ π (affLoss L₀ R a) t x)) μ)
    (hkmb : Integrable (fun x ↦ gibbsDensity μ π (affLoss L₀ R ((1 / 2 : ℝ) • (a + b))) t x *
      Real.log (gibbsDensity μ π (affLoss L₀ R ((1 / 2 : ℝ) • (a + b))) t x /
        gibbsDensity μ π (affLoss L₀ R b) t x)) μ)
    (hZint : Integrable
      (fun x ↦ Real.exp (-(t * affLoss L₀ R ((1 / 2 : ℝ) • (a + b)) x)) * π x) μ) :
    (relEnt μ (gibbsDensity μ π (affLoss L₀ R ((1 / 2 : ℝ) • (a + b))) t)
        (gibbsDensity μ π (affLoss L₀ R a) t) +
      relEnt μ (gibbsDensity μ π (affLoss L₀ R ((1 / 2 : ℝ) • (a + b))) t)
        (gibbsDensity μ π (affLoss L₀ R b) t)) / 2 = affBhat μ π L₀ R t a b := by
  rw [relEnt_midpoint hπ hZa hZb hZm (integrable_gibbsDensity hZint) (integral_gibbsDensity hZm)
    hkma hkmb, relEnt_self, zero_add]

end Midpoint

/-! ### Part B: dilation geometry of the featureless line -/

section Dilation

/-- The directed KL divergence `KL(P_s ‖ P_u)` along the featureless line, in closed form:
`(u − s)⟨ℓ⟩_s + log(Z(u)/Z(s))`. -/
noncomputable def lawKL (ν : Measure ℝ) (s u : ℝ) : ℝ :=
  (u - s) * (lawMoment ν 1 s / lawMoment ν 0 s) + Real.log (lawMoment ν 0 u / lawMoment ν 0 s)

/-- The closed form is the relative entropy of the tilted densities. -/
theorem relEnt_lawDensity_eq_lawKL (ν : Measure ℝ) {s u : ℝ} (hs : 0 < lawMoment ν 0 s)
    (hu : 0 < lawMoment ν 0 u) (hint0 : Integrable (fun ℓ ↦ Real.exp (-(s * ℓ))) ν)
    (hint1 : Integrable (fun ℓ ↦ ℓ * Real.exp (-(s * ℓ))) ν) :
    relEnt ν (lawDensity ν s) (lawDensity ν u) = lawKL ν s u := by
  unfold relEnt lawKL
  have e : ∀ ℓ, lawDensity ν s ℓ * Real.log (lawDensity ν s ℓ / lawDensity ν u ℓ) =
      (u - s) * (ℓ * Real.exp (-(s * ℓ)) / lawMoment ν 0 s) +
        Real.log (lawMoment ν 0 u / lawMoment ν 0 s) * (Real.exp (-(s * ℓ)) / lawMoment ν 0 s) := by
    intro ℓ
    unfold lawDensity
    have hes : 0 < Real.exp (-(s * ℓ)) := Real.exp_pos _
    have heu : 0 < Real.exp (-(u * ℓ)) := Real.exp_pos _
    rw [div_div_div_comm, Real.log_div (div_pos hes heu).ne' (div_pos hs hu).ne',
      Real.log_div hes.ne' heu.ne', Real.log_exp, Real.log_exp, Real.log_div hs.ne' hu.ne',
      Real.log_div hu.ne' hs.ne']
    ring
  simp_rw [e]
  rw [integral_add ((hint1.div_const _).const_mul _) ((hint0.div_const _).const_mul _),
    integral_const_mul, integral_const_mul, integral_div, integral_div]
  have h0 : (∫ ℓ, Real.exp (-(s * ℓ)) ∂ν) = lawMoment ν 0 s := by
    unfold lawMoment; simp only [pow_zero, one_mul]
  have h1 : (∫ ℓ, ℓ * Real.exp (-(s * ℓ)) ∂ν) = lawMoment ν 1 s := by
    unfold lawMoment; simp only [pow_one]
  rw [h0, h1, div_self hs.ne', mul_one]

variable (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
  (hint : ∀ u > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(u * ℓ))) ν)
  (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) {lam : ℝ} (hreg : RegVar ν lam)
include hpos hint hZ hreg

omit hpos hint in
/-- The dilated partition-function ratio: `Z(du)/Z(cu) → (d/c)^{-λ}`. -/
theorem tendsto_lawMoment_ratio_dilation {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Tendsto (fun u ↦ lawMoment ν 0 (d * u) / lawMoment ν 0 (c * u)) atTop
      (𝓝 ((d / c) ^ (-lam))) := by
  have h := (hreg d hd).div (hreg c hc) (Real.rpow_pos_of_pos hc _).ne'
  have e : d ^ (-lam) / c ^ (-lam) = (d / c) ^ (-lam) := (Real.div_rpow hd.le hc.le _).symm
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (hZ u hu).ne']

/-- **Dilation limit of the directed KL**: `KL(P_{cu} ‖ P_{du}) → λ (d/c − 1 − log(d/c))`. -/
theorem tendsto_lawKL_dilation {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Tendsto (fun u ↦ lawKL ν (c * u) (d * u)) atTop
      (𝓝 (lam * (d / c - 1 - Real.log (d / c)))) := by
  have hmean := (tendsto_mul_lawMoment_one_div_of_regVar ν hpos hint hZ hreg).comp
    ((tendsto_id.const_mul_atTop hc) : Tendsto (fun u : ℝ ↦ c * u) atTop atTop)
  have hlog := (tendsto_lawMoment_ratio_dilation ν hZ hreg hc hd).log
    (Real.rpow_pos_of_pos (div_pos hd hc) _).ne'
  rw [Real.log_rpow (div_pos hd hc)] at hlog
  have h := (hmean.const_mul (d / c - 1)).add hlog
  have hv : (d / c - 1) * lam + -lam * Real.log (d / c) =
      lam * (d / c - 1 - Real.log (d / c)) := by ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  simp only [Function.comp_apply, lawKL]
  have hZc := hZ (c * u) (by positivity)
  generalize lawMoment ν 1 (c * u) = N at *
  generalize lawMoment ν 0 (c * u) = Z at *
  have e : (d / c - 1) * (c * u * N / Z) = (d * u - c * u) * (N / Z) := by
    field_simp
  rw [e]

omit hpos hint in
/-- **Dilation limit of the Bhattacharyya divergence**:
`−log ρ(cu, du) → λ log((c+d)/(2√(cd)))`. -/
theorem tendsto_neg_log_lawAffinity_dilation {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Tendsto (fun u ↦ -Real.log (lawAffinity ν (c * u) (d * u))) atTop
      (𝓝 (lam * Real.log ((c + d) / (2 * Real.sqrt (c * d))))) := by
  set m : ℝ := (c + d) / 2 with hm
  have hmpos : 0 < m := by positivity
  have h1 := (tendsto_lawMoment_ratio_dilation ν hZ hreg hmpos hc).log
    (Real.rpow_pos_of_pos (div_pos hc hmpos) _).ne'
  have h2 := (tendsto_lawMoment_ratio_dilation ν hZ hreg hmpos hd).log
    (Real.rpow_pos_of_pos (div_pos hd hmpos) _).ne'
  rw [Real.log_rpow (div_pos hc hmpos)] at h1
  rw [Real.log_rpow (div_pos hd hmpos)] at h2
  have h := (h1.add h2).const_mul (1 / 2)
  have hval : 1 / 2 * (-lam * Real.log (c / m) + -lam * Real.log (d / m)) =
      lam * Real.log ((c + d) / (2 * Real.sqrt (c * d))) := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hcd : 0 < c + d := by positivity
    have hsqcd : 0 < Real.sqrt (c * d) := Real.sqrt_pos.mpr (by positivity)
    rw [Real.log_div hc.ne' hmpos.ne', Real.log_div hd.ne' hmpos.ne', hm,
      Real.log_div hcd.ne' h2, Real.log_div hcd.ne' (mul_pos two_pos hsqcd).ne',
      Real.log_mul h2 hsqcd.ne', Real.log_sqrt (by positivity), Real.log_mul hc.ne' hd.ne']
    ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hZc := hZ (c * u) (by positivity)
  have hZd := hZ (d * u) (by positivity)
  have hZm := hZ (m * u) (by positivity)
  have e : (c * u + d * u) / 2 = m * u := by rw [hm]; ring
  rw [log_lawAffinity ν hZc hZd (by rw [e]; exact hZm), e, Real.log_div hZc.ne' hZm.ne',
    Real.log_div hZd.ne' hZm.ne']
  ring

/-- **The endpoint identity**: `½ KL(P_u ‖ P_0) + log ρ(0, u) → λ (log 2 − ½)`. -/
theorem tendsto_endpoint_identity (hZ0 : 0 < lawMoment ν 0 0) :
    Tendsto (fun u ↦ lawKL ν u 0 / 2 + Real.log (lawAffinity ν 0 u)) atTop
      (𝓝 (lam * (Real.log 2 - 1 / 2))) := by
  have hmean := tendsto_mul_lawMoment_one_div_of_regVar ν hpos hint hZ hreg
  have hhalf := (hreg (1 / 2) (by norm_num)).log
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [Real.log_rpow (by norm_num), show Real.log (1 / 2) = -Real.log 2 by
    rw [one_div, Real.log_inv]] at hhalf
  have h := (hmean.const_mul (-(1 / 2))).add hhalf
  have hval : -(1 / 2) * lam + -lam * -Real.log 2 = lam * (Real.log 2 - 1 / 2) := by ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hZu := hZ u hu
  have e : (0 + u) / 2 = 1 / 2 * u := by ring
  simp only [lawKL]
  rw [log_lawAffinity ν hZ0 hZu (by rw [e]; exact hZ (1 / 2 * u) (by positivity)), e,
    Real.log_div hZ0.ne' hZu.ne', Real.log_div (hZ (1 / 2 * u) (by positivity)).ne' hZu.ne']
  ring

end Dilation

end Laplace.Multi
