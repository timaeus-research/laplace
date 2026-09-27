/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SqrtDensityAffinity
import Laplace.Multi.FisherDistance

/-!
# Hellinger distance is controlled by the Fisher length

For a `C¹` path `γ` from `a` to `b`, test the square-root densities against the chord
`h = q_b − q_a`: `A(t) = ∫ q_{γ_t} h dν` has derivative `A'(t) = −½ ∫ h q_{γ_t}(ℓ_t − E ℓ_t) dν`
(from the affinity identity and the derivative of the partition function), so
`|A'(t)| ≤ ½ H F(γ_t, γ'_t)` by Cauchy–Schwarz, where `H = ‖h‖₂` is the Hellinger distance; and
`A(1) − A(0) = H²`. Hence
`H² ≤ ½ H L(γ)`, i.e. **`H(a,b) ≤ ½ L(γ)`**, and on the direction space **`H ≤ ½ d_F`**.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Defs

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (S : J → X → ℝ) (ν : Measure X)

/-- The Hellinger distance `‖q_θ − q_η‖_{L²(ν)}`. -/
noncomputable def hellingerDist (θ η : J → ℝ) : ℝ :=
  √(∫ x, (rootDens S ν θ x - rootDens S ν η x) * (rootDens S ν θ x - rootDens S ν η x) ∂ν)

theorem hellingerDist_nonneg (θ η : J → ℝ) : 0 ≤ hellingerDist S ν θ η := Real.sqrt_nonneg _

theorem hellingerDist_sq (θ η : J → ℝ) :
    hellingerDist S ν θ η ^ 2 =
      ∫ x, (rootDens S ν θ x - rootDens S ν η x) * (rootDens S ν θ x - rootDens S ν η x) ∂ν :=
  Real.sq_sqrt (integral_nonneg fun _ ↦ mul_self_nonneg _)

end Defs

section Chord

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] in
theorem bdd_famWeight (θ : J → ℝ) : Bdd (famWeight S θ) := by
  obtain ⟨hm, K, hK⟩ := bdd_dirLoss hS θ
  refine ⟨hm.neg.exp, Real.exp K, fun x ↦ ?_⟩
  rw [famWeight, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hK x)).1])

theorem continuous_famZ : Continuous (famZ S ν) :=
  continuous_iff_continuousAt.2 fun θ ↦ (hasFDerivAt_famZ hS ν θ).continuousAt

/-- The partition function along a `C¹` path. -/
theorem hasDerivAt_famZ_comp {γ γ' : ℝ → J → ℝ} {t : ℝ} (hγ : HasDerivAt γ (γ' t) t) :
    HasDerivAt (fun s ↦ famZ S ν (γ s))
      (-famZ S ν (γ t) * dotJ (γ' t) (famMean S ν (γ t))) t := by
  have h := (hasFDerivAt_famZ hS ν (γ t)).comp_hasDerivAt t hγ
  simp only [smul_apply, smul_eq_mul, dotCLM_apply] at h
  exact h

/-- **The chord derivative**: for fixed `z`,
`d/dt ∫ q_{γ_t} q_z = −½ ∫ q_z q_{γ_t}(ℓ_t − E ℓ_t)`. -/
theorem hasDerivAt_integral_rootDens_mul {γ γ' : ℝ → J → ℝ} {t : ℝ} (hγ : HasDerivAt γ (γ' t) t)
    (z : J → ℝ) :
    HasDerivAt (fun s ↦ ∫ x, rootDens S ν (γ s) x * rootDens S ν z x ∂ν)
      (-(1 / 2) * ∫ x, rootDens S ν z x * (rootDens S ν (γ t) x *
        (dirLoss S (γ' t) x - dotJ (γ' t) (famMean S ν (γ t)))) ∂ν) t := by
  have e : (fun s ↦ ∫ x, rootDens S ν (γ s) x * rootDens S ν z x ∂ν) =
      fun s ↦ famZ S ν ((1 / 2 : ℝ) • (γ s + z)) / √(famZ S ν (γ s) * famZ S ν z) :=
    funext fun s ↦ integral_rootDens_mul hS ν (γ s) z
  rw [e]
  -- the numerator and the denominator
  have hm : HasDerivAt (fun s ↦ (1 / 2 : ℝ) • (γ s + z)) ((1 / 2 : ℝ) • γ' t) t :=
    (hγ.add_const z).const_smul (1 / 2 : ℝ)
  have hN := hasDerivAt_famZ_comp hS ν (γ := fun s ↦ (1 / 2 : ℝ) • (γ s + z))
    (γ' := fun s ↦ (1 / 2 : ℝ) • γ' s) hm
  have hZγ := hasDerivAt_famZ_comp hS ν hγ
  have hpos : 0 < famZ S ν (γ t) * famZ S ν z := mul_pos (famZ_pos hS ν _) (famZ_pos hS ν _)
  have hD := (hZγ.mul_const (famZ S ν z)).sqrt hpos.ne'
  have hD0 : √(famZ S ν (γ t) * famZ S ν z) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  refine (hN.div hD hD0).congr_deriv ?_
  -- the value of the derivative
  set m : J → ℝ := (1 / 2 : ℝ) • (γ t + z) with hm_def
  set s : ℝ := √(famZ S ν (γ t) * famZ S ν z) with hs_def
  have hs : s * s = famZ S ν (γ t) * famZ S ν z := Real.mul_self_sqrt hpos.le
  have hs0 : s ≠ 0 := hD0
  have hZγ0 : famZ S ν (γ t) ≠ 0 := (famZ_pos hS ν _).ne'
  -- the integral of the centred product
  have hbz := bdd_rootDens hS ν z
  have hbγ := bdd_rootDens hS ν (γ t)
  have hℓ := bdd_dirLoss hS (γ' t)
  have hI : ∫ x, rootDens S ν z x * (rootDens S ν (γ t) x *
      (dirLoss S (γ' t) x - dotJ (γ' t) (famMean S ν (γ t)))) ∂ν =
      famZ S ν m * dotJ (γ' t) (famMean S ν m) / s -
        dotJ (γ' t) (famMean S ν (γ t)) * (famZ S ν m / s) := by
    have e1 : ∀ x, rootDens S ν z x * (rootDens S ν (γ t) x *
        (dirLoss S (γ' t) x - dotJ (γ' t) (famMean S ν (γ t)))) =
        (famWeight S m x * dirLoss S (γ' t) x) / s -
          dotJ (γ' t) (famMean S ν (γ t)) * (rootDens S ν (γ t) x * rootDens S ν z x) := fun x ↦ by
      rw [mul_comm (rootDens S ν z x), mul_assoc, ← mul_comm (rootDens S ν z x),
        ← mul_assoc, rootDens_mul hS ν (γ t) z, ← hs_def, ← hm_def]
      ring
    simp_rw [e1]
    have i1 : Integrable (fun x ↦ (famWeight S m x * dirLoss S (γ' t) x) / s) ν :=
      (integrable_of_bdd_prob ν ((bdd_famWeight hS m).mul hℓ)).div_const _
    have i2 : Integrable (fun x ↦ dotJ (γ' t) (famMean S ν (γ t)) *
        (rootDens S ν (γ t) x * rootDens S ν z x)) ν :=
      (integrable_of_bdd_prob ν (hbγ.mul hbz)).const_mul _
    rw [integral_sub i1 i2, integral_div, integral_famWeight_mul_dirLoss hS ν, integral_const_mul,
      integral_rootDens_mul hS ν, ← hs_def, ← hm_def]
  rw [hI]
  -- the algebra
  have hdot : dotJ ((1 / 2 : ℝ) • γ' t) (famMean S ν m) = 1 / 2 * dotJ (γ' t) (famMean S ν m) :=
    dotJ_smul_left _ _ _
  simp only [hdot]
  clear_value s m
  have hz : famZ S ν z = s * s / famZ S ν (γ t) := (eq_div_iff hZγ0).2 (by rw [hs]; ring)
  rw [hz]
  field_simp
  ring

/-- `|A'(t)| ≤ ½ ‖h‖₂ F(γ_t, γ'_t)` for the chord `h = q_b − q_a`. -/
theorem abs_chord_deriv_le (θ a b v : J → ℝ) :
    |∫ x, (rootDens S ν b x - rootDens S ν a x) * (rootDens S ν θ x *
      (dirLoss S v x - dotJ v (famMean S ν θ))) ∂ν| ≤
      hellingerDist S ν b a * fisherNorm S ν θ v := by
  have hh : Bdd fun x ↦ rootDens S ν b x - rootDens S ν a x :=
    (bdd_rootDens hS ν b).sub (bdd_rootDens hS ν a)
  have hg : Bdd fun x ↦ rootDens S ν θ x * (dirLoss S v x - dotJ v (famMean S ν θ)) :=
    (bdd_rootDens hS ν θ).mul ((bdd_dirLoss hS v).sub (Bdd.const _))
  have h1 := sq_integral_mul_le ν hh hg
  refine (Real.abs_le_sqrt h1).trans_eq ?_
  rw [Real.sqrt_mul (integral_nonneg fun x ↦ mul_self_nonneg _), hellingerDist, fisherNorm,
    ← integral_rootDens_mul_centred_sq hS ν θ v]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [sq]

/-- **Hellinger is at most half the Fisher length of any `C¹` path.** -/
theorem hellingerDist_le_half_integral {γ γ' : ℝ → J → ℝ} (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hγ' : Continuous γ') :
    hellingerDist S ν (γ 1) (γ 0) ≤ 1 / 2 * ∫ t in (0 : ℝ)..1, fisherNorm S ν (γ t) (γ' t) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t ↦ (hγ t).continuousAt
  set H := hellingerDist S ν (γ 1) (γ 0) with hH
  set L := ∫ t in (0 : ℝ)..1, fisherNorm S ν (γ t) (γ' t) with hL
  have hH0 : 0 ≤ H := hellingerDist_nonneg S ν _ _
  have hL0 : 0 ≤ L :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ ↦ fisherNorm_nonneg _ _ _ _
  -- the chord function
  set A : ℝ → ℝ := fun s ↦ (∫ x, rootDens S ν (γ s) x * rootDens S ν (γ 1) x ∂ν) -
    ∫ x, rootDens S ν (γ s) x * rootDens S ν (γ 0) x ∂ν with hA
  have hA' : ∀ t, HasDerivAt A (-(1 / 2) * ∫ x, (rootDens S ν (γ 1) x - rootDens S ν (γ 0) x) *
      (rootDens S ν (γ t) x * (dirLoss S (γ' t) x - dotJ (γ' t) (famMean S ν (γ t)))) ∂ν) t :=
    fun t ↦ by
    have h := (hasDerivAt_integral_rootDens_mul hS ν (hγ t) (γ 1)).sub
      (hasDerivAt_integral_rootDens_mul hS ν (hγ t) (γ 0))
    refine h.congr_deriv ?_
    rw [← mul_sub, ← integral_sub]
    · congr 1
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      ring
    · exact integrable_of_bdd_prob ν ((bdd_rootDens hS ν _).mul ((bdd_rootDens hS ν _).mul
        ((bdd_dirLoss hS _).sub (Bdd.const _))))
    · exact integrable_of_bdd_prob ν ((bdd_rootDens hS ν _).mul ((bdd_rootDens hS ν _).mul
        ((bdd_dirLoss hS _).sub (Bdd.const _))))
  -- the comparison function
  set B : ℝ → ℝ := fun t ↦ 1 / 2 * H * ∫ s in (0 : ℝ)..t, fisherNorm S ν (γ s) (γ' s) with hB
  have hF : Continuous fun s ↦ fisherNorm S ν (γ s) (γ' s) :=
    continuous_fisherNorm_comp hS ν hγc hγ'
  have hB' : ∀ t, HasDerivAt B (1 / 2 * H * fisherNorm S ν (γ t) (γ' t)) t := fun t ↦
    ((hF.integral_hasStrictDerivAt 0 t).hasDerivAt).const_mul _
  -- `B − A` is monotone
  have hmono : Monotone fun t ↦ B t - A t := by
    have hd : ∀ t, HasDerivAt (fun t ↦ B t - A t)
        (1 / 2 * H * fisherNorm S ν (γ t) (γ' t) - -(1 / 2) *
          ∫ x, (rootDens S ν (γ 1) x - rootDens S ν (γ 0) x) *
            (rootDens S ν (γ t) x * (dirLoss S (γ' t) x - dotJ (γ' t) (famMean S ν (γ t)))) ∂ν)
        t := fun t ↦ (hB' t).sub (hA' t)
    refine monotone_of_deriv_nonneg (fun t ↦ (hd t).differentiableAt) fun t ↦ ?_
    rw [(hd t).deriv]
    have h1 := abs_chord_deriv_le hS ν (γ t) (γ 0) (γ 1) (γ' t)
    have h2 := neg_abs_le (∫ x, (rootDens S ν (γ 1) x - rootDens S ν (γ 0) x) *
      (rootDens S ν (γ t) x * (dirLoss S (γ' t) x - dotJ (γ' t) (famMean S ν (γ t)))) ∂ν)
    rw [← hH] at h1
    nlinarith [h1, h2, fisherNorm_nonneg S ν (γ t) (γ' t)]
  have hmono01 := hmono zero_le_one
  simp only [hB, intervalIntegral.integral_same, mul_zero, zero_sub] at hmono01
  -- `A 1 − A 0 = H²`
  have hA10 : A 1 - A 0 = H ^ 2 := by
    rw [hH, hellingerDist_sq S ν, hA]
    simp only
    have hb1 := bdd_rootDens hS ν (γ 1)
    have hb0 := bdd_rootDens hS ν (γ 0)
    rw [← integral_sub (integrable_of_bdd_prob ν (hb1.mul hb1))
      (integrable_of_bdd_prob ν (hb1.mul hb0)), ← integral_sub
      (integrable_of_bdd_prob ν (hb0.mul hb1)) (integrable_of_bdd_prob ν (hb0.mul hb0)),
      ← integral_sub]
    · refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      ring
    · exact (integrable_of_bdd_prob ν (hb1.mul hb1)).sub (integrable_of_bdd_prob ν (hb1.mul hb0))
    · exact (integrable_of_bdd_prob ν (hb0.mul hb1)).sub (integrable_of_bdd_prob ν (hb0.mul hb0))
  -- conclude
  have hkey : H ^ 2 ≤ 1 / 2 * H * L := by
    rw [← hA10]
    linarith [hmono01]
  rcases eq_or_lt_of_le hH0 with h | h
  · rw [← h]
    positivity
  · nlinarith [hkey]

/-- **Hellinger is at most half the intrinsic Fisher distance on the direction space.** -/
theorem hellingerDist_le_half_fisherDist (x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    hellingerDist S ν (y : J → ℝ) (x : J → ℝ) ≤ 1 / 2 * fisherDist S ν x y := by
  have h : 2 * hellingerDist S ν (y : J → ℝ) (x : J → ℝ) ≤ fisherDist S ν x y := by
    refine le_csInf fisherLengths_nonempty fun _ ⟨p, hp⟩ ↦ hp ▸ ?_
    have := hellingerDist_le_half_integral hS ν (γ := fun t ↦ (p.toFun t : J → ℝ))
      (γ' := fun t ↦ (p.vel t : J → ℝ)) (p.hasDerivAt_coe ν)
      (continuous_subtype_val.comp p.continuous_vel)
    rw [p.source, p.target] at this
    simp only [FisherPath.length]
    linarith [this]
  linarith

end Chord

end Laplace.Multi
