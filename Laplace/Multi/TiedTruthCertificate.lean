/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TwoScaledInner
import Laplace.Multi.VertexCertificate
import Laplace.Multi.PartialTiedModel

/-!
# The tied-truth two-scaled certificate

At a tied-truth optimum of the constrained LP two scaled coordinates can be integrable: the
cutoff `D ∏ u^{−Q/q} < ρ` supplies a second coercive constraint. With the scaled block
`S = Fin 2`, the boxed block `ν`, the dual decomposition `a_S = η κ_S − θ Q_S` (`η, θ > 0`,
`Δ = κ₀Q₁ − κ₁Q₀ ≠ 0`) and `β_j = a_j − ηκ_j + θQ_j > 0` on the boxed block, the dominating
profile `tiedDom = 1_{limitDomain} ∏u^r e^{−c₀∏u^κ}` is integrable
(`integrable_tiedDom_twoScaled`), with the exact value

`Γ(η) c₀^{−η} (D/ρ)^{−θq} / (θ|Δ|) · ∏_ν ρ^{β_j}/β_j`

(`integral_tiedDom_twoScaled`): slicing along the boxed block, each slice is the two-scaled
quadrant integral `integral_twoScaledInner` at the effective constants `c₀ ∏_ν z^κ` and
`h(z) = q log(D ∏_ν z^{−Q/q}/ρ)`, and the residual box integrand is `∏_ν z^{β_j − 1}`. The two
envelope integrabilities of the certificate follow from `Integrable tiedDom` alone whenever the
phase constraint is tied (`integrable_envelope_of_tiedDom`,
`integrable_envelope_mul_profile_of_tiedDom`): the generic form of the vertex argument.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

section Generic

variable {ι : Type*} [Fintype ι]

/-- The dominating profile with the unit frozen at its lower bound, general index. -/
noncomputable def tiedDom (ρ D γ q c₀ : ℝ) (Q κ r α : ι → ℝ) (u : ι → ℝ) : ℝ :=
  (limitDomain ρ D γ q Q α).indicator (fun u ↦ (∏ i, u i ^ r i) * exp (-(c₀ * ∏ i, u i ^ κ i))) u

theorem tiedDom_nonneg (ρ D γ q c₀ : ℝ) (Q κ r α : ι → ℝ) (u : ι → ℝ) :
    0 ≤ tiedDom ρ D γ q c₀ Q κ r α u := by
  unfold tiedDom
  refine Set.indicator_nonneg (fun u hu ↦ ?_) u
  exact mul_nonneg (Finset.prod_nonneg fun i _ ↦ rpow_nonneg (limitDomain_pos hu i).le _)
    (exp_pos _).le

theorem measurable_tiedDom (ρ D γ q c₀ : ℝ) (Q κ r α : ι → ℝ) :
    Measurable (tiedDom ρ D γ q c₀ Q κ r α) :=
  ((Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _).mul
    (Real.measurable_exp.comp ((measurable_const.mul
      (Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _)).neg))).indicator
    measurableSet_limitDomain

/-- On the limiting domain with a tied phase constraint the profile is `B a₀ ∏ u^κ`. -/
theorem dsProfile_of_tied {ρ B D γ q δ : ℝ} {Q κ α : ι → ℝ} {a₀ : (ι → ℝ) → ℝ}
    (htied : ∑ j, κ j * α j = δ) {u : ι → ℝ} (hu : u ∈ limitDomain ρ D γ q Q α) :
    dsProfile ρ B D γ q δ Q κ α a₀ u = B * a₀ u * ∏ i, u i ^ κ i := by
  unfold dsProfile
  rw [if_pos hu, if_pos htied]

/-- The first certificate integrability from the dominating profile (tied phase). -/
theorem integrable_envelope_of_tiedDom {ρ B D γ q δ c amin : ℝ} {Q κ r α : ι → ℝ}
    {a₀ : (ι → ℝ) → ℝ} (hB : 0 < B) (hc : 0 < c) (htied : ∑ j, κ j * α j = δ)
    (hI : Integrable (tiedDom ρ D γ q (c * B * amin) Q κ r α)) (ha₀m : Measurable a₀)
    (ha₀ : ∀ u ∈ limitDomain ρ D γ q Q α, amin ≤ a₀ u) :
    Integrable fun u ↦ dsEnvelope ρ D γ q Q r α 1 u *
      exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u)) := by
  refine hI.mono' ((measurable_dsEnvelope_one ρ D γ q Q r α).mul (Real.measurable_exp.comp
    ((measurable_const.mul (measurable_dsProfile ha₀m)).neg))).aestronglyMeasurable
    (Eventually.of_forall fun u ↦ ?_)
  unfold tiedDom dsEnvelope
  by_cases hu : u ∈ limitDomain ρ D γ q Q α
  · simp only [Set.indicator_of_mem hu, one_mul]
    rw [dsProfile_of_tied htied hu]
    have hprod : 0 ≤ ∏ i, u i ^ r i :=
      Finset.prod_nonneg fun i _ ↦ rpow_nonneg (limitDomain_pos hu i).le _
    have hP : 0 < ∏ i, u i ^ κ i :=
      Finset.prod_pos fun i _ ↦ rpow_pos_of_pos (limitDomain_pos hu i) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprod (exp_pos _).le)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hprod
    have h := mul_nonneg (mul_pos (mul_pos hc hB) hP).le (sub_nonneg.mpr (ha₀ u hu))
    nlinarith [h]
  · simp only [Set.indicator_of_notMem hu]
    simp

/-- The second certificate integrability from the dominating profile (tied phase). -/
theorem integrable_envelope_mul_profile_of_tiedDom {ρ B D γ q δ c amin : ℝ} {Q κ r α : ι → ℝ}
    {a₀ : (ι → ℝ) → ℝ} (hB : 0 < B) (hc : 0 < c) (htied : ∑ j, κ j * α j = δ)
    (hI : Integrable (tiedDom ρ D γ q (c * B * amin / 2) Q κ r α)) (ha₀m : Measurable a₀)
    (hamin : 0 < amin) (ha₀ : ∀ u ∈ limitDomain ρ D γ q Q α, amin ≤ a₀ u) :
    Integrable fun u ↦ dsEnvelope ρ D γ q Q r α 1 u *
      (dsProfile ρ B D γ q δ Q κ α a₀ u * exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u))) := by
  have hI := hI.const_mul (2 / c)
  have hmP := measurable_dsProfile (ρ := ρ) (B := B) (D := D) (γ := γ) (q := q) (δ := δ)
    (Q := Q) (κ := κ) (α := α) ha₀m
  refine hI.mono' ((measurable_dsEnvelope_one ρ D γ q Q r α).mul (hmP.mul
    (Real.measurable_exp.comp ((measurable_const.mul hmP).neg)))).aestronglyMeasurable
    (Eventually.of_forall fun u ↦ ?_)
  unfold tiedDom dsEnvelope
  by_cases hu : u ∈ limitDomain ρ D γ q Q α
  · simp only [Set.indicator_of_mem hu, one_mul]
    rw [dsProfile_of_tied htied hu]
    have hprod : 0 ≤ ∏ i, u i ^ r i :=
      Finset.prod_nonneg fun i _ ↦ rpow_nonneg (limitDomain_pos hu i).le _
    have hP : 0 < ∏ i, u i ^ κ i :=
      Finset.prod_pos fun i _ ↦ rpow_pos_of_pos (limitDomain_pos hu i) _
    set X := B * a₀ u * ∏ i, u i ^ κ i with hX
    have hXge : B * amin * ∏ i, u i ^ κ i ≤ X := by
      rw [hX]
      have h := mul_nonneg (mul_pos hB hP).le (sub_nonneg.mpr (ha₀ u hu))
      nlinarith [h]
    have hX0 : 0 ≤ X := (mul_pos (mul_pos hB hamin) hP).le.trans hXge
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprod (mul_nonneg hX0 (exp_pos _).le))]
    have hsplit : exp (-(c * X)) = exp (-(c * X / 2)) * exp (-(c * X / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h1 : c * X / 2 * exp (-(c * X / 2)) ≤ 1 := by
      have := mul_exp_neg_half_le_two (c * X)
      have e : c * X * exp (-(c * X / 2)) = 2 * (c * X / 2 * exp (-(c * X / 2))) := by ring
      linarith
    have h2 : exp (-(c * X / 2)) ≤ exp (-(c * B * amin / 2 * ∏ i, u i ^ κ i)) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_left hXge hc.le
      nlinarith [this]
    have hcc : 2 / c * (c / 2) = 1 := by field_simp
    have key : X * exp (-(c * X)) ≤ 2 / c * exp (-(c * B * amin / 2 * ∏ i, u i ^ κ i)) := by
      calc X * exp (-(c * X))
          = 2 / c * (c * X / 2 * exp (-(c * X / 2))) * exp (-(c * X / 2)) := by
            rw [hsplit]
            linear_combination (-(X * exp (-(c * X / 2)) * exp (-(c * X / 2)))) * hcc
        _ ≤ 2 / c * 1 * exp (-(c * B * amin / 2 * ∏ i, u i ^ κ i)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (exp_pos _).le
              (by positivity)
        _ = _ := by ring
    calc (∏ i, u i ^ r i) * (X * exp (-(c * X)))
        ≤ (∏ i, u i ^ r i) * (2 / c * exp (-(c * B * amin / 2 * ∏ i, u i ^ κ i))) :=
          mul_le_mul_of_nonneg_left key hprod
      _ = _ := by ring
  · simp only [Set.indicator_of_notMem hu]
    simp


/-- `∫_{(0,ρ)} x^e = ρ^{e+1}/(e+1)`. -/
theorem integral_Ioo_rpow {ρ : ℝ} (hρ : 0 < ρ) {e : ℝ} (he : -1 < e) :
    ∫ x in Ioo (0 : ℝ) ρ, x ^ e = ρ ^ (e + 1) / (e + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le,
    integral_rpow (Or.inl he), Real.zero_rpow (by linarith), sub_zero]

/-- The box integral of a monomial. -/
theorem integral_box_prod_rpow {ρ : ℝ} (hρ : 0 < ρ) {e : ι → ℝ} (he : ∀ j, -1 < e j) :
    ∫ z in Set.pi univ (fun _ : ι ↦ Ioo (0 : ℝ) ρ), ∏ j, z j ^ e j =
      ∏ j, ρ ^ (e j + 1) / (e j + 1) := by
  rw [← integral_indicator (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo)]
  have e1 : (fun z : ι → ℝ ↦ (Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ).indicator
      (fun z ↦ ∏ j, z j ^ e j) z) =
      fun z ↦ ∏ j, (Ioo (0 : ℝ) ρ).indicator (fun x ↦ x ^ e j) (z j) := by
    funext z
    exact (prod_indicator_eq' (fun j x ↦ x ^ e j) z).symm
  rw [e1, integral_fintype_prod_volume_eq_prod (fun j x ↦ (Ioo (0 : ℝ) ρ).indicator
    (fun x ↦ x ^ e j) x)]
  exact Finset.prod_congr rfl fun j _ ↦ by
    rw [integral_indicator measurableSet_Ioo, integral_Ioo_rpow hρ (he j)]

end Generic

section TwoScaled

variable {ν : Type*} [Fintype ν]

theorem prod_rpow_add' {ι : Type*} [Fintype ι] {z : ι → ℝ} (hz : ∀ j, 0 < z j) (a b : ι → ℝ) :
    (∏ j, z j ^ a j) * ∏ j, z j ^ b j = ∏ j, z j ^ (a j + b j) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ ↦ (Real.rpow_add (hz j) _ _).symm

/-- The logarithmic form of the cutoff on the scaled block. -/
theorem cut_iff_log {D ρ q P : ℝ} (hD : 0 < D) (hρ : 0 < ρ) (hq : 0 < q) (hP : 0 < P)
    {y : Fin 2 → ℝ} (hy : ∀ i, 0 < y i) (QS : Fin 2 → ℝ) :
    D * (P * ∏ i, y i ^ (-(QS i / q))) < ρ ↔
      q * log (D * P / ρ) < ∑ i, QS i * log (y i) := by
  have e1 : ∏ i, y i ^ (-(QS i / q)) = exp (-((∑ i, QS i * log (y i)) / q)) := by
    rw [show -((∑ i, QS i * log (y i)) / q) = ∑ i, log (y i) * (-(QS i / q)) by
      rw [Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ ↦ Real.rpow_def_of_pos (hy i) _
  rw [e1]
  have hDP : 0 < D * P := mul_pos hD hP
  rw [show D * (P * exp (-((∑ i, QS i * log (y i)) / q))) =
    (D * P) * exp (-((∑ i, QS i * log (y i)) / q)) by ring, ← lt_div_iff₀' hDP,
    ← Real.lt_log_iff_exp_lt (div_pos hρ hDP), Real.log_div hρ.ne' hDP.ne',
    Real.log_div hDP.ne' hρ.ne', neg_lt, neg_sub, lt_div_iff₀ hq,
    mul_comm (log (D * P) - log ρ) q]

theorem elim_mem_limitDomain {ρ D γ q : ℝ} {Q : Fin 2 ⊕ ν → ℝ} {αS : Fin 2 → ℝ}
    (hαS : ∀ i, 0 < αS i) (hQα : ∑ j, Q j * Sum.elim αS 0 j = γ) (y : Fin 2 → ℝ) (z : ν → ℝ) :
    Sum.elim y z ∈ limitDomain ρ D γ q Q (Sum.elim αS 0) ↔
      (∀ i, 0 < y i) ∧ (∀ j, z j ∈ Ioo (0 : ℝ) ρ) ∧
        D * ∏ j, Sum.elim y z j ^ (-(Q j / q)) < ρ := by
  unfold limitDomain
  rw [Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_ofPred_eq, Sum.forall]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, (hαS _).ne', if_false, if_true, mem_Ioi,
    hQα, forall_const]
  tauto

/-- The slice of the dominating profile over the scaled block at a boxed point. -/
theorem tiedDom_elim {ρ D γ q c₀ : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    {Q κ r : Fin 2 ⊕ ν → ℝ} {αS : Fin 2 → ℝ} (hαS : ∀ i, 0 < αS i)
    (hQα : ∑ j, Q j * Sum.elim αS 0 j = γ) (y : Fin 2 → ℝ) {z : ν → ℝ}
    (hz : ∀ j, z j ∈ Ioo (0 : ℝ) ρ) :
    tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0) (Sum.elim y z) =
      (∏ j, z j ^ r (Sum.inr j)) *
        twoScaledInner (fun i ↦ κ (Sum.inl i)) (fun i ↦ Q (Sum.inl i))
          (fun i ↦ r (Sum.inl i) + 1) (c₀ * ∏ j, z j ^ κ (Sum.inr j))
          (q * log (D * (∏ j, z j ^ (-(Q (Sum.inr j) / q))) / ρ)) y := by
  have hzpos : ∀ j, 0 < z j := fun j ↦ (hz j).1
  have hP : 0 < ∏ j, z j ^ (-(Q (Sum.inr j) / q)) :=
    Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (hzpos j) _
  unfold tiedDom twoScaledInner
  by_cases hy : ∀ i, 0 < y i
  · have hypos : y ∈ Set.pi univ fun _ : Fin 2 ↦ Ioi (0 : ℝ) := Set.mem_univ_pi.mpr hy
    rw [Set.indicator_of_mem hypos]
    have hcut : D * ∏ j, Sum.elim y z j ^ (-(Q j / q)) < ρ ↔
        q * log (D * (∏ j, z j ^ (-(Q (Sum.inr j) / q))) / ρ) <
          ∑ i, Q (Sum.inl i) * log (y i) := by
      rw [prod_elim_rpow, mul_comm (∏ i, y i ^ _)]
      exact cut_iff_log hD hρ hq hP hy _
    by_cases hc : D * ∏ j, Sum.elim y z j ^ (-(Q j / q)) < ρ
    · rw [Set.indicator_of_mem ((elim_mem_limitDomain hαS hQα y z).mpr ⟨hy, hz, hc⟩),
        Set.indicator_of_mem (show y ∈ {y : Fin 2 → ℝ | _ < ∑ i, Q (Sum.inl i) * log (y i)}
          from hcut.mp hc), prod_elim_rpow, prod_elim_rpow]
      simp only [add_sub_cancel_right]
      have e : c₀ * ((∏ i, y i ^ κ (Sum.inl i)) * ∏ j, z j ^ κ (Sum.inr j)) =
          c₀ * (∏ j, z j ^ κ (Sum.inr j)) * ∏ i, y i ^ κ (Sum.inl i) := by ring
      rw [e]
      ring
    · rw [Set.indicator_of_notMem (fun h ↦ hc ((elim_mem_limitDomain hαS hQα y z).mp h).2.2),
        Set.indicator_of_notMem (show y ∉ {y : Fin 2 → ℝ | _ < ∑ i, Q (Sum.inl i) * log (y i)}
          from fun h ↦ hc (hcut.mpr h)), mul_zero]
  · rw [Set.indicator_of_notMem (fun h ↦ hy ((elim_mem_limitDomain hαS hQα y z).mp h).1),
      Set.indicator_of_notMem (s := Set.pi univ fun _ : Fin 2 ↦ Ioi (0 : ℝ))
        (fun h ↦ hy fun i ↦ Set.mem_univ_pi.mp h i), mul_zero]

theorem tiedDom_elim_of_notMem {ρ D γ q c₀ : ℝ} {Q κ r : Fin 2 ⊕ ν → ℝ} {αS : Fin 2 → ℝ}
    (hαS : ∀ i, 0 < αS i) (hQα : ∑ j, Q j * Sum.elim αS 0 j = γ) (y : Fin 2 → ℝ) {z : ν → ℝ}
    (hz : ¬ ∀ j, z j ∈ Ioo (0 : ℝ) ρ) :
    tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0) (Sum.elim y z) = 0 := by
  unfold tiedDom
  exact Set.indicator_of_notMem (fun h ↦ hz ((elim_mem_limitDomain hαS hQα y z).mp h).2.1) _

/-- The two-scaled constant `Γ(η) c₀^{−η} (D/ρ)^{−θq} / (θ|Δ|)`. -/
noncomputable def twoScaledConst (η θ c₀ D ρ q Δ : ℝ) : ℝ :=
  Gamma η * c₀ ^ (-η) * (D / ρ) ^ (-(θ * q)) / (θ * |Δ|)

theorem twoScaledConst_nonneg {η θ c₀ D ρ q : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hc₀ : 0 < c₀)
    (hD : 0 < D) (hρ : 0 < ρ) (Δ : ℝ) : 0 ≤ twoScaledConst η θ c₀ D ρ q Δ := by
  unfold twoScaledConst
  have hΓ := Gamma_pos_of_pos hη
  have hDρ : (0 : ℝ) ≤ D / ρ := by positivity
  exact div_nonneg (mul_nonneg (mul_nonneg hΓ.le (rpow_nonneg hc₀.le _)) (rpow_nonneg hDρ _))
    (mul_nonneg hθ.le (abs_nonneg _))

/-- The residual exponents of the boxed block. -/
noncomputable def resExp (η θ : ℝ) (Q κ r : Fin 2 ⊕ ν → ℝ) (j : ν) : ℝ :=
  r (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j)

/-- The slice value: the two-scaled constant times the residual monomial. -/
theorem integral_tiedDom_elim {ρ D γ q c₀ η θ : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    (hc₀ : 0 < c₀) {Q κ r : Fin 2 ⊕ ν → ℝ} {αS : Fin 2 → ℝ} (hαS : ∀ i, 0 < αS i)
    (hQα : ∑ j, Q j * Sum.elim αS 0 j = γ)
    (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    (haS : ∀ i, r (Sum.inl i) + 1 = η * κ (Sum.inl i) - θ * Q (Sum.inl i))
    (hη : 0 < η) (hθ : 0 < θ) {z : ν → ℝ} (hz : ∀ j, z j ∈ Ioo (0 : ℝ) ρ) :
    ∫ y, tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0) (Sum.elim y z) =
      twoScaledConst η θ c₀ D ρ q (κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0)) *
        ∏ j, z j ^ resExp η θ Q κ r j := by
  unfold twoScaledConst
  have hzpos : ∀ j, 0 < z j := fun j ↦ (hz j).1
  have hPκ : 0 < ∏ j, z j ^ κ (Sum.inr j) := Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (hzpos j) _
  have hPQ : 0 < ∏ j, z j ^ (-(Q (Sum.inr j) / q)) :=
    Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (hzpos j) _
  simp_rw [tiedDom_elim hρ hD hq hαS hQα _ hz]
  rw [integral_const_mul, integral_twoScaledInner hΔ haS hη hθ (mul_pos hc₀ hPκ)]
  -- the exponential of the cut level
  have hX : 0 < D * (∏ j, z j ^ (-(Q (Sum.inr j) / q))) / ρ := by positivity
  have e1 : exp (-(θ * (q * log (D * (∏ j, z j ^ (-(Q (Sum.inr j) / q))) / ρ)))) =
      (D / ρ) ^ (-(θ * q)) * ∏ j, z j ^ (θ * Q (Sum.inr j)) := by
    have hX' : 0 < D / ρ * ∏ j, z j ^ (-(Q (Sum.inr j) / q)) := by positivity
    rw [show D * (∏ j, z j ^ (-(Q (Sum.inr j) / q))) / ρ =
      D / ρ * ∏ j, z j ^ (-(Q (Sum.inr j) / q)) by ring,
      show -(θ * (q * log (D / ρ * ∏ j, z j ^ (-(Q (Sum.inr j) / q))))) =
        log (D / ρ * ∏ j, z j ^ (-(Q (Sum.inr j) / q))) * (-(θ * q)) by ring,
      ← Real.rpow_def_of_pos hX', Real.mul_rpow (by positivity) hPQ.le,
      ← Real.finsetProd_rpow _ _ (fun j _ ↦ rpow_nonneg (hzpos j).le _)]
    congr 1
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← Real.rpow_mul (hzpos j).le]
    congr 1
    field_simp
  rw [e1]
  -- the power of the effective constant
  have e3 : (c₀ * ∏ j, z j ^ κ (Sum.inr j)) ^ (-η) =
      c₀ ^ (-η) * ∏ j, z j ^ (-(η * κ (Sum.inr j))) := by
    rw [Real.mul_rpow hc₀.le hPκ.le, ← Real.finsetProd_rpow _ _
      (fun j _ ↦ rpow_nonneg (hzpos j).le _)]
    congr 1
    exact Finset.prod_congr rfl fun j _ ↦ by rw [← Real.rpow_mul (hzpos j).le]; ring_nf
  rw [e3]
  -- assemble the residual monomial
  unfold resExp
  have e4 : (∏ j, z j ^ r (Sum.inr j)) * ((∏ j, z j ^ (-(η * κ (Sum.inr j)))) *
      ∏ j, z j ^ (θ * Q (Sum.inr j))) =
      ∏ j, z j ^ (r (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j)) := by
    rw [prod_rpow_add' hzpos, prod_rpow_add' hzpos]
    exact Finset.prod_congr rfl fun j _ ↦ by congr 1; ring
  rw [← e4]
  ring

/-- **The two-scaled tied-truth certificate**: the dominating profile is integrable. -/
theorem integrable_tiedDom_twoScaled {ρ D γ q c₀ η θ : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    (hc₀ : 0 < c₀) {Q κ r : Fin 2 ⊕ ν → ℝ} {αS : Fin 2 → ℝ} (hαS : ∀ i, 0 < αS i)
    (hQα : ∑ j, Q j * Sum.elim αS 0 j = γ)
    (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    (haS : ∀ i, r (Sum.inl i) + 1 = η * κ (Sum.inl i) - θ * Q (Sum.inl i))
    (hη : 0 < η) (hθ : 0 < θ) (hβ : ∀ j, -1 < resExp η θ Q κ r j) :
    Integrable (tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0)) := by
  have hmp := (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ ν ↦ ℝ)).symm
  rw [← hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hmeas : AEStronglyMeasurable (fun p : (Fin 2 → ℝ) × (ν → ℝ) ↦
      tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0) (Sum.elim p.1 p.2)) (volume.prod volume) :=
    ((measurable_tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0)).comp
      (MeasurableEquiv.measurable (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin 2 ⊕ ν ↦ ℝ)).symm)).aestronglyMeasurable
  change Integrable (fun p : (Fin 2 → ℝ) × (ν → ℝ) ↦
    tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0) (Sum.elim p.1 p.2)) (volume.prod volume)
  rw [integrable_prod_iff' hmeas]
  constructor
  · refine ae_of_all _ fun z ↦ ?_
    by_cases hz : ∀ j, z j ∈ Ioo (0 : ℝ) ρ
    · simp only [tiedDom_elim hρ hD hq hαS hQα _ hz]
      exact (integrable_twoScaledInner hΔ haS hη hθ (mul_pos hc₀ (Finset.prod_pos fun j _ ↦
        rpow_pos_of_pos (hz j).1 _)) _).const_mul _
    · simp only [tiedDom_elim_of_notMem hαS hQα _ hz]
      exact integrable_zero _ _ _
  · refine ((integrable_box_prod_rpow' hρ hβ).const_mul (twoScaledConst η θ c₀ D ρ q
      (κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0)))).congr
      (Eventually.of_forall fun z ↦ ?_)
    simp only
    by_cases hz : ∀ j, z j ∈ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem (Set.mem_univ_pi.mpr hz), ← integral_tiedDom_elim hρ hD hq hc₀ hαS
        hQα hΔ haS hη hθ hz]
      exact integral_congr_ae (Eventually.of_forall fun y ↦
        (Real.norm_of_nonneg (tiedDom_nonneg _ _ _ _ _ _ _ _ _ _)).symm)
    · rw [Set.indicator_of_notMem (fun h ↦ hz (Set.mem_univ_pi.mp h)), mul_zero]
      simp only [tiedDom_elim_of_notMem hαS hQα _ hz, norm_zero, integral_zero]

/-- **The value of the two-scaled tied-truth integral**:
`Γ(η) c₀^{−η} (D/ρ)^{−θq} / (θ|Δ|) · ∏_ν ρ^{β_j}/β_j`. -/
theorem integral_tiedDom_twoScaled {ρ D γ q c₀ η θ : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    (hc₀ : 0 < c₀) {Q κ r : Fin 2 ⊕ ν → ℝ} {αS : Fin 2 → ℝ} (hαS : ∀ i, 0 < αS i)
    (hQα : ∑ j, Q j * Sum.elim αS 0 j = γ)
    (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    (haS : ∀ i, r (Sum.inl i) + 1 = η * κ (Sum.inl i) - θ * Q (Sum.inl i))
    (hη : 0 < η) (hθ : 0 < θ) (hβ : ∀ j, -1 < resExp η θ Q κ r j) :
    ∫ u, tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0) u =
      twoScaledConst η θ c₀ D ρ q (κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0)) *
        ∏ j, ρ ^ (resExp η θ Q κ r j + 1) / (resExp η θ Q κ r j + 1) := by
  have hmp := (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ ν ↦ ℝ)).symm
  have hint := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr
    (integrable_tiedDom_twoScaled hρ hD hq hc₀ hαS hQα hΔ haS hη hθ hβ)
  rw [← hmp.integral_comp' (tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0)),
    Measure.volume_eq_prod (Fin 2 → ℝ) (ν → ℝ),
    integral_prod_symm (fun p : (Fin 2 → ℝ) × (ν → ℝ) ↦ tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ ν ↦ ℝ)).symm p)) hint]
  change (∫ z, ∫ y, tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0) (Sum.elim y z)) = _
  have hboxN : MeasurableSet (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hpt : ∀ z : ν → ℝ, (∫ y, tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0) (Sum.elim y z)) =
      (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ).indicator (fun z ↦
        twoScaledConst η θ c₀ D ρ q
          (κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0)) *
          ∏ j, z j ^ resExp η θ Q κ r j) z := by
    intro z
    by_cases hz : ∀ j, z j ∈ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem (Set.mem_univ_pi.mpr hz)]
      exact integral_tiedDom_elim hρ hD hq hc₀ hαS hQα hΔ haS hη hθ hz
    · rw [Set.indicator_of_notMem (fun h ↦ hz (Set.mem_univ_pi.mp h))]
      simp only [tiedDom_elim_of_notMem hαS hQα _ hz, integral_zero]
  simp_rw [hpt]
  rw [integral_indicator hboxN, integral_const_mul, integral_box_prod_rpow hρ hβ]

end TwoScaled

end Laplace.Multi
