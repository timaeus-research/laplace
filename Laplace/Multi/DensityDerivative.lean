/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiltRateQuadratic

/-!
# The `L¹` derivative of the family density in the natural chart

For bounded features `S` the family `P_θ = e^{−⟨θ,S⟩}ν/Z(θ)` has density `p_θ = e^{−⟨θ,S⟩}/Z(θ)`.
Its derivative in the natural parameter, in `L¹(ν)`, is the density times the centred score,

`p_{θ+η} = p_θ + p_θ (⟨η, m(θ)⟩ − ⟨η, S⟩) + r_η`, `‖r_η‖_{L¹(ν)} ≤ 10 K² ‖η‖²` for `K‖η‖ ≤ 1/4`,

with `K = |J| · sup|S|` and `m(θ) = E_{P_θ} S`. The remainder is bounded pointwise by a constant
times
`‖η‖² p_θ`; integrating against the probability density `p_θ` gives the `L¹` bound with no further
integrability input. The proof expands the weight `e^{−⟨θ+η,S⟩} = e^{−⟨θ,S⟩} e^{−⟨η,S⟩}` and the
normaliser to second order (`Real.abs_exp_sub_one_sub_id_le`), and clears the two denominators by
hand.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Chart

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

/-- The unnormalised family weight `e^{−⟨θ,S⟩}`. -/
noncomputable def famWeight (S : J → X → ℝ) (θ : J → ℝ) (x : X) : ℝ := Real.exp (-dirLoss S θ x)

/-- The normaliser `Z(θ) = ∫ e^{−⟨θ,S⟩} dν`. -/
noncomputable def famZ (S : J → X → ℝ) (ν : Measure X) (θ : J → ℝ) : ℝ := ∫ x, famWeight S θ x ∂ν

/-- The family density `p_θ = e^{−⟨θ,S⟩}/Z(θ)`. -/
noncomputable def famDens (S : J → X → ℝ) (ν : Measure X) (θ : J → ℝ) (x : X) : ℝ :=
  famWeight S θ x / famZ S ν θ

/-- The response `m(θ) = E_{P_θ} S`. -/
noncomputable def famMean (S : J → X → ℝ) (ν : Measure X) (θ : J → ℝ) : J → ℝ :=
  fun i ↦ ∫ x, S i x * famDens S ν θ x ∂ν

omit [MeasurableSpace X] in
theorem famWeight_pos (θ : J → ℝ) (x : X) : 0 < famWeight S θ x := Real.exp_pos _

omit [MeasurableSpace X] in
theorem famWeight_add (θ η : J → ℝ) (x : X) :
    famWeight S (θ + η) x = famWeight S θ x * Real.exp (-dirLoss S η x) := by
  unfold famWeight
  rw [dirLoss_add, ← Real.exp_add]
  congr 1
  ring

include hS

theorem integrable_famWeight (θ : J → ℝ) : Integrable (famWeight S θ) ν := by
  have h := integrable_exp_of_bdd ν (Bdd.const_mul (-1) (bdd_dirLoss hS θ))
  refine h.congr (Eventually.of_forall fun x ↦ ?_)
  simp only [famWeight, neg_one_mul]

theorem famZ_pos (θ : J → ℝ) : 0 < famZ S ν θ :=
  integral_exp_pos (f := fun x ↦ -dirLoss S θ x) (integrable_famWeight hS ν θ)

theorem famDens_nonneg (θ : J → ℝ) (x : X) : 0 ≤ famDens S ν θ x :=
  div_nonneg (famWeight_pos θ x).le (famZ_pos hS ν θ).le

theorem integrable_famDens (θ : J → ℝ) : Integrable (famDens S ν θ) ν :=
  (integrable_famWeight hS ν θ).div_const _

theorem integral_famDens (θ : J → ℝ) : ∫ x, famDens S ν θ x ∂ν = 1 := by
  unfold famDens
  rw [integral_div]
  exact div_self (famZ_pos hS ν θ).ne'

variable {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B)
include hB0 hB

omit [MeasurableSpace X] hS in
theorem abs_dirLoss_le_card_mul (η : J → ℝ) (x : X) :
    |dirLoss S η x| ≤ (Fintype.card J : ℝ) * B * ‖η‖ := by
  have h : ‖fun i ↦ S i x‖ ≤ B := (pi_norm_le_iff_of_nonneg hB0).2 fun i ↦ by
    rw [Real.norm_eq_abs]
    exact hB i x
  calc |dirLoss S η x| = |dotJ η (fun i ↦ S i x)| := rfl
    _ ≤ (Fintype.card J : ℝ) * ‖η‖ * ‖fun i ↦ S i x‖ := abs_dotJ_le_card_mul η _
    _ ≤ (Fintype.card J : ℝ) * ‖η‖ * B := by gcongr
    _ = (Fintype.card J : ℝ) * B * ‖η‖ := by ring

omit hB0 in
theorem abs_famMean_le (θ : J → ℝ) (i : J) : |famMean S ν θ i| ≤ B := by
  unfold famMean
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((integrable_famDens hS ν θ).const_mul B)
    (Eventually.of_forall fun x ↦ ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (famDens_nonneg hS ν θ x)]
    exact mul_le_mul_of_nonneg_right (hB i x) (famDens_nonneg hS ν θ x)
  · rw [integral_const_mul, integral_famDens hS ν, mul_one]

theorem abs_dotJ_famMean_le (θ η : J → ℝ) :
    |dotJ η (famMean S ν θ)| ≤ (Fintype.card J : ℝ) * B * ‖η‖ := by
  have h : ‖famMean S ν θ‖ ≤ B := (pi_norm_le_iff_of_nonneg hB0).2 fun i ↦ by
    rw [Real.norm_eq_abs]
    exact abs_famMean_le hS ν hB θ i
  calc |dotJ η (famMean S ν θ)| ≤ (Fintype.card J : ℝ) * ‖η‖ * ‖famMean S ν θ‖ :=
        abs_dotJ_le_card_mul η _
    _ ≤ (Fintype.card J : ℝ) * ‖η‖ * B := by gcongr
    _ = (Fintype.card J : ℝ) * B * ‖η‖ := by ring

omit hB0 hB in
/-- The centred first moment of the weight: `∫ ⟨η,S⟩ e^{−⟨θ,S⟩} dν = Z(θ) ⟨η, m(θ)⟩`. -/
theorem integral_dirLoss_mul_famWeight (θ η : J → ℝ) :
    ∫ x, dirLoss S η x * famWeight S θ x ∂ν = famZ S ν θ * dotJ η (famMean S ν θ) := by
  have hZ := famZ_pos hS ν θ
  have hSw : ∀ i, Integrable (fun x ↦ S i x * famWeight S θ x) ν := fun i ↦ by
    obtain ⟨M, hM⟩ := (hS i).2
    exact (integrable_famWeight hS ν θ).bdd_mul (c := M) (hS i).1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hM x)
  unfold famMean famDens dotJ dirLoss
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ ↦ ((hSw i).const_mul (η i)).congr
    (Eventually.of_forall fun x ↦ by ring), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have e : ∀ x, S i x * (famWeight S θ x / famZ S ν θ) = (S i x * famWeight S θ x) / famZ S ν θ :=
    fun x ↦ by ring
  have e2 : ∀ x, η i * S i x * famWeight S θ x = η i * (S i x * famWeight S θ x) :=
    fun x ↦ by ring
  simp_rw [e, e2]
  rw [integral_div, integral_const_mul, mul_comm (famZ S ν θ), mul_assoc,
    div_mul_cancel₀ _ hZ.ne']

omit [MeasurableSpace X] hS hB0 hB in
/-- Second-order expansion of the weight: for `|⟨η,S(x)⟩| ≤ 1`,
`|e^{−⟨θ+η,S⟩} − e^{−⟨θ,S⟩} + ⟨η,S⟩ e^{−⟨θ,S⟩}| ≤ ⟨η,S⟩² e^{−⟨θ,S⟩}`. -/
theorem abs_famWeight_add_sub_le (θ η : J → ℝ) (x : X) (h1 : |dirLoss S η x| ≤ 1) :
    |famWeight S (θ + η) x - famWeight S θ x + dirLoss S η x * famWeight S θ x| ≤
      famWeight S θ x * (dirLoss S η x) ^ 2 := by
  rw [famWeight_add]
  have h := Real.abs_exp_sub_one_sub_id_le (x := -dirLoss S η x) (by rwa [abs_neg])
  rw [neg_sq] at h
  have e : famWeight S θ x * Real.exp (-dirLoss S η x) - famWeight S θ x +
      dirLoss S η x * famWeight S θ x =
      famWeight S θ x * (Real.exp (-dirLoss S η x) - 1 - -dirLoss S η x) := by ring
  rw [e, abs_mul, abs_of_pos (famWeight_pos θ x)]
  exact mul_le_mul_of_nonneg_left h (famWeight_pos θ x).le

/-- Second-order expansion of the normaliser: for `K‖η‖ ≤ 1`,
`|Z(θ+η) − Z(θ) + Z(θ)⟨η, m(θ)⟩| ≤ Z(θ) (K‖η‖)²`. -/
theorem abs_famZ_add_sub_le (θ η : J → ℝ) (h1 : (Fintype.card J : ℝ) * B * ‖η‖ ≤ 1) :
    |famZ S ν (θ + η) - famZ S ν θ + famZ S ν θ * dotJ η (famMean S ν θ)| ≤
      famZ S ν θ * ((Fintype.card J : ℝ) * B * ‖η‖) ^ 2 := by
  have hint := integral_dirLoss_mul_famWeight hS ν θ η
  have hI1 := integrable_famWeight hS ν (θ + η)
  have hI2 := integrable_famWeight hS ν θ
  have hI3 : Integrable (fun x ↦ dirLoss S η x * famWeight S θ x) ν :=
    hI2.bdd_mul (c := (Fintype.card J : ℝ) * B * ‖η‖) (bdd_dirLoss hS η).1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]; exact abs_dirLoss_le_card_mul hB0 hB η x)
  have hI12 : Integrable (fun x ↦ famWeight S (θ + η) x - famWeight S θ x) ν := hI1.sub hI2
  have e : famZ S ν (θ + η) - famZ S ν θ + famZ S ν θ * dotJ η (famMean S ν θ) =
      ∫ x, (famWeight S (θ + η) x - famWeight S θ x + dirLoss S η x * famWeight S θ x) ∂ν := by
    rw [integral_add hI12 hI3, integral_sub hI1 hI2, hint]
    rfl
  rw [e, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hI2.mul_const (((Fintype.card J : ℝ) * B * ‖η‖) ^ 2))
    (Eventually.of_forall fun x ↦ ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    refine (abs_famWeight_add_sub_le θ η x ((abs_dirLoss_le_card_mul hB0 hB η x).trans h1)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (famWeight_pos θ x).le
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_dirLoss_le_card_mul hB0 hB η x) 2
  · rw [integral_mul_const]
    exact le_rfl

/-- **Pointwise second-order bound for the density**: for `K‖η‖ ≤ 1/4`,
`|p_{θ+η} − p_θ − p_θ(⟨η,m(θ)⟩ − ⟨η,S⟩)| ≤ 10 (K‖η‖)² p_θ`. -/
theorem abs_famDens_remainder_le (θ η : J → ℝ)
    (h1 : (Fintype.card J : ℝ) * B * ‖η‖ ≤ 1 / 4) (x : X) :
    |famDens S ν (θ + η) x - famDens S ν θ x -
        famDens S ν θ x * (dotJ η (famMean S ν θ) - dirLoss S η x)| ≤
      10 * ((Fintype.card J : ℝ) * B * ‖η‖) ^ 2 * famDens S ν θ x := by
  unfold famDens
  set ε := (Fintype.card J : ℝ) * B * ‖η‖ with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε14 : ε ≤ 1 / 4 := h1
  have hε1 : ε ≤ 1 := by linarith
  set a := famWeight S θ x with ha
  set a' := famWeight S (θ + η) x with ha'
  set Z := famZ S ν θ with hZ
  set Z' := famZ S ν (θ + η) with hZ'
  set v := dirLoss S η x with hv
  set w := dotJ η (famMean S ν θ) with hw
  have ha0 : 0 < a := famWeight_pos θ x
  have hZ0 : 0 < Z := famZ_pos hS ν θ
  have hZ'0 : 0 < Z' := famZ_pos hS ν (θ + η)
  have hv1 : |v| ≤ ε := abs_dirLoss_le_card_mul hB0 hB η x
  have hw1 : |w| ≤ ε := abs_dotJ_famMean_le hS ν hB0 hB θ η
  have hrN : |a' - a + v * a| ≤ a * ε ^ 2 := by
    refine (abs_famWeight_add_sub_le θ η x (hv1.trans hε1)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ ha0.le
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hv1 2
  have hrZ : |Z' - Z + Z * w| ≤ Z * ε ^ 2 := abs_famZ_add_sub_le hS ν hB0 hB θ η hε1
  -- the perturbed normaliser is at least half the normaliser
  have hZ'half : Z / 2 ≤ Z' := by
    have h1' := (abs_le.1 hrZ).1
    have h2' : Z * w ≤ Z * ε := mul_le_mul_of_nonneg_left (abs_le.1 hw1).2 hZ0.le
    have h3' : Z * ε ≤ Z * (1 / 4) := mul_le_mul_of_nonneg_left hε14 hZ0.le
    have h4' : Z * ε ^ 2 ≤ Z * (1 / 4) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε0 hε14 2) hZ0.le
    linarith
  have hZinv : Z⁻¹ * Z = 1 := inv_mul_cancel₀ hZ0.ne'
  have hZ'inv : Z'⁻¹ * Z' = 1 := inv_mul_cancel₀ hZ'0.ne'
  -- the numerator identity
  have hnum : (a' / Z' - a / Z - a / Z * (w - v)) * (Z * Z') =
      (a' - a + v * a) * Z - a * (Z' - Z + Z * w) + a * Z * w * (w - v) -
        a * (Z' - Z + Z * w) * (w - v) := by
    simp only [div_eq_mul_inv]
    linear_combination (a' * Z) * hZ'inv - (a * Z' + a * Z' * (w - v)) * hZinv
  have hwv : |w - v| ≤ 2 * ε := by
    calc |w - v| ≤ |w| + |v| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hbound : |(a' - a + v * a) * Z - a * (Z' - Z + Z * w) + a * Z * w * (w - v) -
      a * (Z' - Z + Z * w) * (w - v)| ≤ 5 * a * Z * ε ^ 2 := by
    have t1 : |(a' - a + v * a) * Z| ≤ a * ε ^ 2 * Z := by
      rw [abs_mul, abs_of_pos hZ0]
      exact mul_le_mul_of_nonneg_right hrN hZ0.le
    have t2 : |a * (Z' - Z + Z * w)| ≤ a * (Z * ε ^ 2) := by
      rw [abs_mul, abs_of_pos ha0]
      exact mul_le_mul_of_nonneg_left hrZ ha0.le
    have t3 : |a * Z * w * (w - v)| ≤ a * Z * ε * (2 * ε) := by
      rw [abs_mul, abs_mul, abs_of_pos (mul_pos ha0 hZ0)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hw1 (mul_pos ha0 hZ0).le) hwv (abs_nonneg _)
        (by positivity)
    have t4 : |a * (Z' - Z + Z * w) * (w - v)| ≤ a * (Z * ε ^ 2) * (2 * ε) := by
      rw [abs_mul]
      exact mul_le_mul t2 hwv (abs_nonneg _) (by positivity)
    calc |(a' - a + v * a) * Z - a * (Z' - Z + Z * w) + a * Z * w * (w - v) -
          a * (Z' - Z + Z * w) * (w - v)|
        ≤ |(a' - a + v * a) * Z| + |a * (Z' - Z + Z * w)| + |a * Z * w * (w - v)| +
            |a * (Z' - Z + Z * w) * (w - v)| := by
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ a * ε ^ 2 * Z + a * (Z * ε ^ 2) + a * Z * ε * (2 * ε) + a * (Z * ε ^ 2) * (2 * ε) := by
          linarith
      _ ≤ 5 * a * Z * ε ^ 2 := by
          have h5 : a * (Z * ε ^ 2) * (2 * ε) ≤ a * (Z * ε ^ 2) * (2 * (1 / 4)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h6 : a * ε ^ 2 * Z + a * (Z * ε ^ 2) + a * Z * ε * (2 * ε) +
              a * (Z * ε ^ 2) * (2 * (1 / 4)) = (9 / 2) * (a * Z * ε ^ 2) := by ring
          have h7 : 0 ≤ a * Z * ε ^ 2 := by positivity
          linarith
  have hZZ' : 0 < Z * Z' := mul_pos hZ0 hZ'0
  refine le_of_mul_le_mul_right ?_ hZZ'
  rw [← abs_of_pos hZZ', ← abs_mul, abs_of_pos hZZ', hnum]
  refine hbound.trans ?_
  have e : 10 * ε ^ 2 * (a / Z) * (Z * Z') = 10 * a * Z' * ε ^ 2 := by
    simp only [div_eq_mul_inv]
    linear_combination (10 * ε ^ 2 * a * Z') * hZinv
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hZ'half (mul_nonneg ha0.le (sq_nonneg ε))]

/-- **The `L¹` derivative of the family density in the natural chart**: for `K‖η‖ ≤ 1/4`,
`∫ |p_{θ+η} − p_θ − p_θ(⟨η,m(θ)⟩ − ⟨η,S⟩)| dν ≤ 10 K² ‖η‖²`, `K = |J| sup|S|`. -/
theorem integral_abs_famDens_remainder_le (θ η : J → ℝ)
    (h1 : (Fintype.card J : ℝ) * B * ‖η‖ ≤ 1 / 4) :
    ∫ x, |famDens S ν (θ + η) x - famDens S ν θ x -
        famDens S ν θ x * (dotJ η (famMean S ν θ) - dirLoss S η x)| ∂ν ≤
      10 * ((Fintype.card J : ℝ) * B) ^ 2 * ‖η‖ ^ 2 := by
  have hint : Integrable (fun x ↦ 10 * ((Fintype.card J : ℝ) * B * ‖η‖) ^ 2 * famDens S ν θ x) ν :=
    (integrable_famDens hS ν θ).const_mul _
  calc ∫ x, |famDens S ν (θ + η) x - famDens S ν θ x -
        famDens S ν θ x * (dotJ η (famMean S ν θ) - dirLoss S η x)| ∂ν
      ≤ ∫ x, 10 * ((Fintype.card J : ℝ) * B * ‖η‖) ^ 2 * famDens S ν θ x ∂ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun x ↦ abs_nonneg _) hint
          (Eventually.of_forall fun x ↦ abs_famDens_remainder_le hS ν hB0 hB θ η h1 x)
    _ = 10 * ((Fintype.card J : ℝ) * B) ^ 2 * ‖η‖ ^ 2 := by
        rw [integral_const_mul, integral_famDens hS ν, mul_one]
        ring

/-- The `L¹` remainder of the family density is `O(‖η‖²)` at every natural parameter. -/
theorem isBigO_famDens_remainder (θ : J → ℝ) :
    (fun η : J → ℝ ↦ ∫ x, |famDens S ν (θ + η) x - famDens S ν θ x -
        famDens S ν θ x * (dotJ η (famMean S ν θ) - dirLoss S η x)| ∂ν) =O[𝓝 0]
      fun η ↦ ‖η‖ ^ 2 := by
  refine Asymptotics.IsBigO.of_bound (10 * ((Fintype.card J : ℝ) * B) ^ 2) ?_
  have hK : 0 ≤ (Fintype.card J : ℝ) * B := by positivity
  have hδ : (0 : ℝ) < 1 / (4 * ((Fintype.card J : ℝ) * B + 1)) := by
    apply div_pos one_pos
    linarith
  filter_upwards [Metric.closedBall_mem_nhds (0 : J → ℝ) hδ] with η hη
  rw [Metric.mem_closedBall, dist_zero_right] at hη
  have h1 : (Fintype.card J : ℝ) * B * ‖η‖ ≤ 1 / 4 := by
    calc (Fintype.card J : ℝ) * B * ‖η‖ ≤ (Fintype.card J : ℝ) * B *
          (1 / (4 * ((Fintype.card J : ℝ) * B + 1))) := mul_le_mul_of_nonneg_left hη hK
      _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖η‖)]
  exact integral_abs_famDens_remainder_le hS ν hB0 hB θ η h1

end Chart

end Laplace.Multi
