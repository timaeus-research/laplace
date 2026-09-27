/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.HellingerFisherControl
import Laplace.Multi.FaceMassHellinger
import Laplace.Multi.FisherCompletionLaws
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# The spherical statistical distance, Fisher length and face separation

The **affinity** `ρ(θ,η) = ∫ √(p_θ p_η) dν` (`affinity`) of two model laws is the inner product of
their root densities, unit vectors of `L²(ν)`; the **spherical statistical distance**
`d_sph(θ,η) = 2 arccos ρ(θ,η)` (`sphericalDist`) is twice the angle between them, hence a metric
(`sphericalDist_triangle`), related to the Hellinger chord by `H² = 2 − 2ρ`
(`hellingerDist_sq_eq_affinity`). Its key property is the **angle-versus-length inequality**: along
every `C¹` path in the natural parameters,

  `2 arccos ρ(γ 1, γ 0) ≤ ∫₀¹ √G_{γ t}(γ' t, γ' t) dt`   (`two_arccos_affinity_le_integral`),

because the root density moves on the unit sphere of `L²(ν)` with speed half the Fisher norm and
the affinity derivative is controlled by the orthogonal component (`abs_affinity_deriv_le`). This
sharpens the chordal bound `H ≤ ½ ∫ √G` of `HellingerFisherControl`.

Towards a boundary face: if a unit density `q` is supported on a measurable set `A`, then
`ρ(p_θ, q) ≤ √P_θ(A)` (`integral_rootDens_mul_sqrt_le`), with equality for the conditioned law
`1_A p_θ / P_θ(A)` (`integral_rootDens_mul_sqrt_faceCondDens`); hence every Fisher path from `θ₀`
whose endpoint law has affinity `ρ₁` with `q` has length at least

  `2 arccos √P_{θ₀}(A) − 2 arccos ρ₁`   (`two_arccos_sqrt_real_le_integral_add`):

the face mass of the starting law is an exact ambient cost of approaching a law supported on the
face.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Affinity

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

variable (S) in
omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **The affinity** `ρ(θ,η) = ∫ √(p_θ p_η) dν` of two model laws. -/
noncomputable def affinity (θ η : J → ℝ) : ℝ := ∫ x, rootDens S ν θ x * rootDens S ν η x ∂ν

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem affinity_comm (θ η : J → ℝ) : affinity S ν θ η = affinity S ν η θ :=
  integral_congr_ae (Eventually.of_forall fun _ ↦ mul_comm _ _)

variable (S) in
omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem affinity_nonneg (θ η : J → ℝ) : 0 ≤ affinity S ν θ η :=
  integral_nonneg fun x ↦ mul_nonneg (rootDens_nonneg S ν θ x) (rootDens_nonneg S ν η x)

omit [Nonempty X] [Nonempty J] in
theorem affinity_self (θ : J → ℝ) : affinity S ν θ θ = 1 := by
  unfold affinity
  simp_rw [← sq]
  exact integral_rootDens_sq hS ν θ

omit [Nonempty X] [Nonempty J] in
theorem affinity_le_one (θ η : J → ℝ) : affinity S ν θ η ≤ 1 := by
  have h := sq_integral_mul_le ν (bdd_rootDens hS ν θ) (bdd_rootDens hS ν η)
  have e1 : ∫ x, rootDens S ν θ x * rootDens S ν θ x ∂ν = 1 := affinity_self hS ν θ
  have e2 : ∫ x, rootDens S ν η x * rootDens S ν η x ∂ν = 1 := affinity_self hS ν η
  rw [e1, e2, one_mul] at h
  have h0 := affinity_nonneg S ν θ η
  change affinity S ν θ η ^ 2 ≤ 1 at h
  nlinarith

omit [Nonempty X] [Nonempty J] in
/-- The Hellinger chord and the affinity: `H(θ,η)² = 2 − 2ρ(θ,η)`. -/
theorem hellingerDist_sq_eq_affinity (θ η : J → ℝ) :
    hellingerDist S ν θ η ^ 2 = 2 - 2 * affinity S ν θ η := by
  rw [hellingerDist_sq]
  have e : ∀ x, (rootDens S ν θ x - rootDens S ν η x) * (rootDens S ν θ x - rootDens S ν η x) =
      rootDens S ν θ x * rootDens S ν θ x - 2 * (rootDens S ν θ x * rootDens S ν η x) +
        rootDens S ν η x * rootDens S ν η x := fun x ↦ by ring
  simp_rw [e]
  have i1 := integrable_of_bdd_prob ν ((bdd_rootDens hS ν θ).mul (bdd_rootDens hS ν θ))
  have i2 := integrable_of_bdd_prob ν ((bdd_rootDens hS ν θ).mul (bdd_rootDens hS ν η))
  have i3 := integrable_of_bdd_prob ν ((bdd_rootDens hS ν η).mul (bdd_rootDens hS ν η))
  have i12 : Integrable (fun x ↦ rootDens S ν θ x * rootDens S ν θ x -
      2 * (rootDens S ν θ x * rootDens S ν η x)) ν := i1.sub (i2.const_mul 2)
  rw [integral_add i12 i3, integral_sub i1 (i2.const_mul 2), integral_const_mul]
  have e1 : ∫ x, rootDens S ν θ x * rootDens S ν θ x ∂ν = 1 := affinity_self hS ν θ
  have e2 : ∫ x, rootDens S ν η x * rootDens S ν η x ∂ν = 1 := affinity_self hS ν η
  rw [e1, e2]
  unfold affinity
  ring

variable (S) in
omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **The spherical statistical distance** `d_sph(θ,η) = 2 arccos ρ(θ,η)`. -/
noncomputable def sphericalDist (θ η : J → ℝ) : ℝ := 2 * Real.arccos (affinity S ν θ η)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem sphericalDist_nonneg (θ η : J → ℝ) : 0 ≤ sphericalDist S ν θ η :=
  mul_nonneg zero_le_two (Real.arccos_nonneg _)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem sphericalDist_comm (θ η : J → ℝ) : sphericalDist S ν θ η = sphericalDist S ν η θ := by
  unfold sphericalDist
  rw [affinity_comm]

omit [Nonempty X] [Nonempty J] in
theorem sphericalDist_self (θ : J → ℝ) : sphericalDist S ν θ θ = 0 := by
  unfold sphericalDist
  rw [affinity_self hS ν, Real.arccos_one, mul_zero]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem sphericalDist_le_pi (θ η : J → ℝ) : sphericalDist S ν θ η ≤ Real.pi := by
  unfold sphericalDist
  have := Real.arccos_le_pi_div_two.2 (affinity_nonneg S ν θ η)
  linarith

/-- The root density as a unit vector of `L²(ν)`. -/
noncomputable def rootDensL2 (θ : J → ℝ) : Lp ℝ 2 ν := (memLp_rootDens hS ν θ).toLp _

omit [Nonempty X] [Nonempty J] in
theorem inner_rootDensL2 (θ η : J → ℝ) :
    inner ℝ (rootDensL2 hS ν θ) (rootDensL2 hS ν η) = affinity S ν θ η := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_rootDens hS ν θ),
    MemLp.coeFn_toLp (memLp_rootDens hS ν η)] with x h1 h2
  rw [rootDensL2, rootDensL2, h1, h2, RCLike.inner_apply, conj_trivial, mul_comm]

omit [Nonempty X] [Nonempty J] in
theorem norm_rootDensL2 (θ : J → ℝ) : ‖rootDensL2 hS ν θ‖ = 1 := by
  have h : ‖rootDensL2 hS ν θ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_rootDensL2 hS ν, affinity_self hS ν]
  nlinarith [norm_nonneg (rootDensL2 hS ν θ)]

omit [Nonempty X] [Nonempty J] in
/-- The spherical distance is twice the angle between the root densities. -/
theorem sphericalDist_eq_angle (θ η : J → ℝ) :
    sphericalDist S ν θ η =
      2 * InnerProductGeometry.angle (rootDensL2 hS ν θ) (rootDensL2 hS ν η) := by
  unfold sphericalDist InnerProductGeometry.angle
  rw [inner_rootDensL2 hS ν, norm_rootDensL2 hS ν, norm_rootDensL2 hS ν, mul_one, div_one]

omit [Nonempty X] [Nonempty J] in
/-- **The spherical statistical distance satisfies the triangle inequality.** -/
theorem sphericalDist_triangle (θ η ζ : J → ℝ) :
    sphericalDist S ν θ ζ ≤ sphericalDist S ν θ η + sphericalDist S ν η ζ := by
  rw [sphericalDist_eq_angle hS ν, sphericalDist_eq_angle hS ν, sphericalDist_eq_angle hS ν]
  linarith [InnerProductGeometry.angle_le_angle_add_angle (rootDensL2 hS ν θ) (rootDensL2 hS ν η)
    (rootDensL2 hS ν ζ)]

omit [Nonempty J] in
/-- **The orthogonal-component bound on the affinity derivative**:
`|∫ q_z q_θ (ℓ − Eℓ)| ≤ √(1 − ρ(θ,z)²) ‖ℓ‖_θ`. -/
theorem abs_affinity_deriv_le (θ v z : J → ℝ) :
    |∫ x, rootDens S ν z x * (rootDens S ν θ x *
      (dirLoss S v x - dotJ v (famMean S ν θ))) ∂ν| ≤
      √(1 - affinity S ν θ z ^ 2) * fisherNorm S ν θ v := by
  set a := affinity S ν θ z with ha
  set c : X → ℝ := fun x ↦ dirLoss S v x - dotJ v (famMean S ν θ) with hc
  have hbc : Bdd c := (bdd_dirLoss hS v).sub (Bdd.const _)
  have hbθ := bdd_rootDens hS ν θ
  have hbz := bdd_rootDens hS ν z
  -- the centred product integrates to zero against `q_θ²`
  have h0 : ∫ x, rootDens S ν θ x * (rootDens S ν θ x * c x) ∂ν = 0 := by
    have e : ∀ x, rootDens S ν θ x * (rootDens S ν θ x * c x) =
        famDens S ν θ x * dirLoss S v x - dotJ v (famMean S ν θ) * famDens S ν θ x := fun x ↦ by
      rw [← mul_assoc, ← sq, rootDens_sq hS ν, hc]
      ring
    simp_rw [e]
    obtain ⟨M, hM⟩ := (bdd_dirLoss hS v).2
    have i1 : Integrable (fun x ↦ famDens S ν θ x * dirLoss S v x) ν :=
      ((integrable_famDens hS ν θ).bdd_mul (bdd_dirLoss hS v).1.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hM x)).congr
        (Eventually.of_forall fun x ↦ mul_comm _ _)
    rw [integral_sub i1 ((integrable_famDens hS ν θ).const_mul _),
      integral_famDens_mul_dirLoss hS ν, integral_const_mul, integral_famDens hS ν, mul_one,
      sub_self]
  -- replace `q_z` by its orthogonal component
  have hh0 : Bdd fun x ↦ rootDens S ν z x - a * rootDens S ν θ x := hbz.sub (hbθ.const_mul a)
  have e : ∫ x, rootDens S ν z x * (rootDens S ν θ x * c x) ∂ν =
      ∫ x, (rootDens S ν z x - a * rootDens S ν θ x) * (rootDens S ν θ x * c x) ∂ν := by
    have i1 := integrable_of_bdd_prob ν (hbz.mul (hbθ.mul hbc))
    rw [← sub_eq_zero, ← integral_sub i1 (integrable_of_bdd_prob ν (hh0.mul (hbθ.mul hbc)))]
    have e2 : ∀ x, rootDens S ν z x * (rootDens S ν θ x * c x) -
        (rootDens S ν z x - a * rootDens S ν θ x) * (rootDens S ν θ x * c x) =
        a * (rootDens S ν θ x * (rootDens S ν θ x * c x)) := fun x ↦ by ring
    simp_rw [e2]
    rw [integral_const_mul, h0, mul_zero]
  rw [e]
  have hg : Bdd fun x ↦ rootDens S ν θ x * c x := hbθ.mul hbc
  have h1 := sq_integral_mul_le ν hh0 hg
  have hnorm : ∫ x, (rootDens S ν z x - a * rootDens S ν θ x) *
      (rootDens S ν z x - a * rootDens S ν θ x) ∂ν = 1 - a ^ 2 := by
    have e3 : ∀ x, (rootDens S ν z x - a * rootDens S ν θ x) *
        (rootDens S ν z x - a * rootDens S ν θ x) =
        rootDens S ν z x * rootDens S ν z x - (2 * a) * (rootDens S ν θ x * rootDens S ν z x) +
          a ^ 2 * (rootDens S ν θ x * rootDens S ν θ x) := fun x ↦ by ring
    simp_rw [e3]
    have i1 := integrable_of_bdd_prob ν (hbz.mul hbz)
    have i2 := integrable_of_bdd_prob ν (hbθ.mul hbz)
    have i3 := integrable_of_bdd_prob ν (hbθ.mul hbθ)
    have i12 : Integrable (fun x ↦ rootDens S ν z x * rootDens S ν z x -
        (2 * a) * (rootDens S ν θ x * rootDens S ν z x)) ν := i1.sub (i2.const_mul _)
    rw [integral_add i12 (i3.const_mul _), integral_sub i1 (i2.const_mul _), integral_const_mul,
      integral_const_mul]
    have e1 : ∫ x, rootDens S ν z x * rootDens S ν z x ∂ν = 1 := affinity_self hS ν z
    have e2 : ∫ x, rootDens S ν θ x * rootDens S ν θ x ∂ν = 1 := affinity_self hS ν θ
    rw [e1, e2]
    change 1 - 2 * a * affinity S ν θ z + a ^ 2 * 1 = 1 - a ^ 2
    rw [← ha]
    ring
  have ha1 : 0 ≤ 1 - a ^ 2 := by
    have := affinity_le_one hS ν θ z
    have := affinity_nonneg S ν θ z
    nlinarith
  refine (Real.abs_le_sqrt h1).trans_eq ?_
  rw [hnorm, Real.sqrt_mul ha1, fisherNorm, ← integral_rootDens_mul_centred_sq hS ν θ v]
  congr 2
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hc, sq])

omit [Nonempty J] in
/-- **The angle-versus-length inequality**: the spherical distance between the endpoints of a
`C¹` path is at most its Fisher length,
`2 arccos ρ(γ 1, γ 0) ≤ ∫₀¹ ‖γ' t‖_{γ t} dt`. -/
theorem two_arccos_affinity_le_integral {γ γ' : ℝ → J → ℝ} (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hγ' : Continuous γ') :
    2 * Real.arccos (affinity S ν (γ 1) (γ 0)) ≤
      ∫ t in (0 : ℝ)..1, fisherNorm S ν (γ t) (γ' t) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t ↦ (hγ t).continuousAt
  have hF : Continuous fun s ↦ fisherNorm S ν (γ s) (γ' s) :=
    continuous_fisherNorm_comp hS ν hγc hγ'
  set a : ℝ → ℝ := fun v ↦ affinity S ν (γ v) (γ 0) with ha_def
  have ha : ∀ v, HasDerivAt a (-(1 / 2) * ∫ x, rootDens S ν (γ 0) x * (rootDens S ν (γ v) x *
      (dirLoss S (γ' v) x - dotJ (γ' v) (famMean S ν (γ v)))) ∂ν) v :=
    fun v ↦ hasDerivAt_integral_rootDens_mul hS ν (hγ v) (γ 0)
  have hac : Continuous a := continuous_iff_continuousAt.2 fun v ↦ (ha v).continuousAt
  set L : ℝ → ℝ := fun v ↦ ∫ t in (0 : ℝ)..v, fisherNorm S ν (γ t) (γ' t) with hL_def
  have hL : ∀ v, HasDerivAt L (fisherNorm S ν (γ v) (γ' v)) v := fun v ↦
    (hF.integral_hasStrictDerivAt 0 v).hasDerivAt
  have hLc : Continuous L := continuous_iff_continuousAt.2 fun v ↦ (hL v).continuousAt
  have ha0 : ∀ v, 0 ≤ a v := fun v ↦ affinity_nonneg S ν _ _
  have ha1 : ∀ v, a v ≤ 1 := fun v ↦ affinity_le_one hS ν _ _
  -- the monotone comparison function for each `ε ∈ (0,1)`
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 →
      2 * Real.arccos ((1 - ε) * a 1) ≤ L 1 + 2 * Real.arccos (1 - ε) := by
    intro ε hε0 hε1
    set Φ : ℝ → ℝ := fun v ↦ L v / 2 - Real.arccos ((1 - ε) * a v) with hΦ_def
    have hx : ∀ v, ((1 - ε) * a v) ^ 2 < 1 := fun v ↦ by
      have h1 : 0 ≤ 1 - ε := by linarith
      have h3 : 0 ≤ (1 - ε) * a v := mul_nonneg h1 (ha0 v)
      have h4 : (1 - ε) * a v ≤ 1 - ε := mul_le_of_le_one_right h1 (ha1 v)
      exact pow_lt_one₀ h3 (lt_of_le_of_lt h4 (by linarith)) two_ne_zero
    have hΦ : ∀ v, HasDerivAt Φ (fisherNorm S ν (γ v) (γ' v) / 2 -
        (-(1 / √(1 - ((1 - ε) * a v) ^ 2))) * ((1 - ε) * (-(1 / 2) *
          ∫ x, rootDens S ν (γ 0) x * (rootDens S ν (γ v) x *
            (dirLoss S (γ' v) x - dotJ (γ' v) (famMean S ν (γ v)))) ∂ν))) v := fun v ↦ by
      have h1 := (hL v).div_const 2
      have hne1 : (1 - ε) * a v ≠ -1 := by
        have h0 : 0 ≤ (1 - ε) * a v := mul_nonneg (by linarith) (ha0 v)
        intro h
        rw [h] at h0
        norm_num at h0
      have hne2 : (1 - ε) * a v ≠ 1 := by
        have := hx v
        intro h
        rw [h] at this
        norm_num at this
      have h2 := (Real.hasDerivAt_arccos hne1 hne2).comp v ((ha v).const_mul (1 - ε))
      exact h1.sub h2
    have hΦ' : ∀ v, 0 ≤ deriv Φ v := fun v ↦ by
      rw [(hΦ v).deriv]
      set I := ∫ x, rootDens S ν (γ 0) x * (rootDens S ν (γ v) x *
        (dirLoss S (γ' v) x - dotJ (γ' v) (famMean S ν (γ v)))) ∂ν with hI
      set F := fisherNorm S ν (γ v) (γ' v) with hF_def
      set s := √(1 - ((1 - ε) * a v) ^ 2) with hs_def
      have hs : 0 < s := Real.sqrt_pos.2 (by linarith [hx v])
      have hF0 : 0 ≤ F := fisherNorm_nonneg _ _ _ _
      have hb := abs_affinity_deriv_le hS ν (γ v) (γ' v) (γ 0)
      rw [← hI, ← hF_def] at hb
      have hsle : √(1 - a v ^ 2) ≤ s := by
        refine Real.sqrt_le_sqrt ?_
        have h1e : ((1 : ℝ) - ε) ^ 2 ≤ 1 := by nlinarith
        rw [mul_pow]
        nlinarith [mul_le_mul_of_nonneg_right h1e (sq_nonneg (a v))]
      have hIle : (1 - ε) * I ≤ s * F := by
        have h1 : I ≤ √(1 - a v ^ 2) * F := (le_abs_self I).trans hb
        have h2 : √(1 - a v ^ 2) * F ≤ s * F := mul_le_mul_of_nonneg_right hsle hF0
        have h3 : (1 - ε) * I ≤ I ∨ (1 - ε) * I ≤ 0 := by
          rcases le_or_gt 0 I with hI0 | hI0
          · left
            nlinarith
          · right
            nlinarith
        rcases h3 with h3 | h3
        · linarith
        · exact h3.trans (mul_nonneg hs.le hF0)
      have e : F / 2 - (-(1 / s)) * ((1 - ε) * (-(1 / 2) * I)) =
          (s * F - (1 - ε) * I) / (2 * s) := by
        field_simp
      rw [e]
      exact div_nonneg (by linarith) (by positivity)
    have hΦc : Continuous Φ :=
      (hLc.div_const 2).sub (Real.continuous_arccos.comp (continuous_const.mul hac))
    have hmono : MonotoneOn Φ (Icc 0 1) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hΦc.continuousOn
        (fun v _ ↦ (hΦ v).differentiableAt.differentiableWithinAt) (fun v _ ↦ hΦ' v)
    have h01 := hmono (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
    have hL0 : L 0 = 0 := intervalIntegral.integral_same
    have ha00 : a 0 = 1 := affinity_self hS ν _
    simp only [hΦ_def, hL0, ha00, mul_one, zero_div, zero_sub] at h01
    linarith
  -- let `ε → 0⁺`
  have h1 : Tendsto (fun ε : ℝ ↦ 2 * Real.arccos ((1 - ε) * a 1)) (𝓝[>] 0)
      (𝓝 (2 * Real.arccos (a 1))) := by
    have hc : Continuous fun ε : ℝ ↦ 2 * Real.arccos ((1 - ε) * a 1) :=
      continuous_const.mul (Real.continuous_arccos.comp ((continuous_const.sub continuous_id).mul
        continuous_const))
    have := hc.tendsto 0
    simp only [sub_zero, one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ ↦ L 1 + 2 * Real.arccos (1 - ε)) (𝓝[>] 0)
      (𝓝 (L 1 + 2 * Real.arccos 1)) := by
    have hc : Continuous fun ε : ℝ ↦ L 1 + 2 * Real.arccos (1 - ε) :=
      continuous_const.add (continuous_const.mul (Real.continuous_arccos.comp
        (continuous_const.sub continuous_id)))
    have := hc.tendsto 0
    simp only [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 2 * Real.arccos ((1 - ε) * a 1) ≤
      L 1 + 2 * Real.arccos (1 - ε) := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds one_pos).filter_mono
      nhdsWithin_le_nhds] with ε hε0 hε1
    exact key ε hε0 hε1
  have := le_of_tendsto_of_tendsto h1 h2 hev
  rw [Real.arccos_one, mul_zero, add_zero] at this
  exact this

omit [Nonempty J] in
/-- The spherical distance between the endpoints of a `C¹` path is at most its Fisher length. -/
theorem sphericalDist_le_integral {γ γ' : ℝ → J → ℝ} (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hγ' : Continuous γ') :
    sphericalDist S ν (γ 1) (γ 0) ≤ ∫ t in (0 : ℝ)..1, fisherNorm S ν (γ t) (γ' t) :=
  two_arccos_affinity_le_integral hS ν hγ hγ'

end Affinity

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] [Nonempty J] in
/-- **The face margin**: a unit density supported on `A` has affinity at most `√P_θ(A)` with the
model law `P_θ`. -/
theorem integral_rootDens_mul_sqrt_le (θ : J → ℝ) {q : X → ℝ} (hqm : Measurable q)
    (hq0 : ∀ x, 0 ≤ q x) (hqi : Integrable q ν) (hq1 : ∫ x, q x ∂ν = 1) {A : Set X}
    (hA : MeasurableSet A) (hsupp : ∀ x, x ∉ A → q x = 0) :
    ∫ x, rootDens S ν θ x * √(q x) ∂ν ≤ √((Pfam θ).real A) := by
  have hbθ := bdd_rootDens hS ν θ
  have hqq : ∀ x, √(q x) * √(q x) = q x := fun x ↦ Real.mul_self_sqrt (hq0 x)
  have hsq : Integrable (fun x ↦ √(q x) * √(q x)) (ν.restrict A) := by
    simp_rw [hqq]
    exact hqi.restrict
  have hff : Integrable (fun x ↦ rootDens S ν θ x * rootDens S ν θ x) (ν.restrict A) :=
    (integrable_of_bdd_prob ν (hbθ.mul hbθ)).restrict
  have hfg : Integrable (fun x ↦ rootDens S ν θ x * √(q x)) (ν.restrict A) := by
    obtain ⟨M, hM⟩ := hbθ.2
    have hsqrtL : Integrable (fun x ↦ √(q x)) (ν.restrict A) := by
      refine ((memLp_two_iff_integrable_sq hqm.sqrt.aestronglyMeasurable).2 ?_).integrable
        one_le_two
      simp_rw [sq, hqq]
      exact hqi.restrict
    exact hsqrtL.bdd_mul (c := M) hbθ.1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hM x)
  have hcs := integral_mul_sq_le hff hsq hfg
  have hA1 : ∫ x in A, √(q x) * √(q x) ∂ν = 1 := by
    simp_rw [hqq]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, hq1]
  have hA2 : ∫ x in A, rootDens S ν θ x * rootDens S ν θ x ∂ν = (Pfam θ).real A :=
    (real_family_eq_integral_rootDens_mul_self hS ν θ hA).symm
  have hfull : ∫ x, rootDens S ν θ x * √(q x) ∂ν = ∫ x in A, rootDens S ν θ x * √(q x) ∂ν := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_).symm
    rw [hsupp x hx, Real.sqrt_zero, mul_zero]
  rw [hA1, hA2, mul_one] at hcs
  rw [hfull]
  have hnn : 0 ≤ ∫ x in A, rootDens S ν θ x * √(q x) ∂ν :=
    integral_nonneg fun x ↦ mul_nonneg (rootDens_nonneg S ν θ x) (Real.sqrt_nonneg _)
  exact (Real.le_sqrt hnn measureReal_nonneg).2 hcs

omit [Nonempty X] [Nonempty J] in
/-- The spherical distance from a model law to a law supported on `A` is at least
`2 arccos √P_θ(A)`. -/
theorem two_arccos_sqrt_real_le (θ : J → ℝ) {q : X → ℝ} (hqm : Measurable q)
    (hq0 : ∀ x, 0 ≤ q x) (hqi : Integrable q ν) (hq1 : ∫ x, q x ∂ν = 1) {A : Set X}
    (hA : MeasurableSet A) (hsupp : ∀ x, x ∉ A → q x = 0) :
    2 * Real.arccos (√((Pfam θ).real A)) ≤
      2 * Real.arccos (∫ x, rootDens S ν θ x * √(q x) ∂ν) :=
  mul_le_mul_of_nonneg_left (Real.arccos_le_arccos
    (integral_rootDens_mul_sqrt_le hS ν θ hqm hq0 hqi hq1 hA hsupp)) zero_le_two

variable (S) in
omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The model law conditioned on `A`, as a density: `1_A p_θ / P_θ(A)`. -/
noncomputable def faceCondDens (θ : J → ℝ) (A : Set X) : X → ℝ :=
  fun x ↦ A.indicator (famDens S ν θ) x / (Pfam θ).real A

omit [Nonempty X] [Nonempty J] in
/-- **The face margin is attained** by the conditioned law: `ρ(p_θ, 1_A p_θ/P_θ(A)) = √P_θ(A)`. -/
theorem integral_rootDens_mul_sqrt_faceCondDens (θ : J → ℝ) {A : Set X} (hA : MeasurableSet A)
    (hpos : 0 < (Pfam θ).real A) :
    ∫ x, rootDens S ν θ x * √(faceCondDens S ν θ A x) ∂ν = √((Pfam θ).real A) := by
  set m := (Pfam θ).real A with hm
  have e : ∀ x, rootDens S ν θ x * √(faceCondDens S ν θ A x) =
      A.indicator (fun x ↦ rootDens S ν θ x * rootDens S ν θ x) x / √m := by
    intro x
    by_cases hx : x ∈ A
    · simp only [faceCondDens, Set.indicator_of_mem hx]
      rw [Real.sqrt_div (famDens_nonneg hS ν θ x), ← rootDens_sq hS ν, Real.sqrt_sq
        (rootDens_nonneg S ν θ x)]
      ring
    · simp [faceCondDens, Set.indicator_of_notMem hx]
  simp_rw [e]
  rw [integral_div, integral_indicator hA, ← real_family_eq_integral_rootDens_mul_self hS ν θ hA,
    ← hm]
  have hs : 0 < √m := Real.sqrt_pos.2 hpos
  field_simp
  exact (Real.sq_sqrt hpos.le).symm

omit [Nonempty J] in
/-- **Face separation along Fisher paths**: a `C¹` path starting at `θ₀` whose endpoint law has
affinity `ρ₁` with a unit density supported on `A` has Fisher length at least
`2 arccos √P_{θ₀}(A) − 2 arccos ρ₁`. -/
theorem two_arccos_sqrt_real_le_integral_add {γ γ' : ℝ → J → ℝ}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') {q : X → ℝ} (hqm : Measurable q)
    (hq0 : ∀ x, 0 ≤ q x) (hqi : Integrable q ν) (hq1 : ∫ x, q x ∂ν = 1) {A : Set X}
    (hA : MeasurableSet A) (hsupp : ∀ x, x ∉ A → q x = 0) :
    2 * Real.arccos (√((Pfam (γ 0)).real A)) ≤
      (∫ t in (0 : ℝ)..1, fisherNorm S ν (γ t) (γ' t)) +
        2 * Real.arccos (∫ x, rootDens S ν (γ 1) x * √(q x) ∂ν) := by
  -- the root of `q` as a unit vector of `L²(ν)`
  have hqL : MemLp (fun x ↦ √(q x)) 2 ν := by
    refine (memLp_two_iff_integrable_sq hqm.sqrt.aestronglyMeasurable).2 ?_
    simp_rw [sq, fun x ↦ Real.mul_self_sqrt (hq0 x)]
    exact hqi
  set sq : Lp ℝ 2 ν := hqL.toLp _ with hsq
  have hinner : ∀ θ, inner ℝ (rootDensL2 hS ν θ) sq = ∫ x, rootDens S ν θ x * √(q x) ∂ν := by
    intro θ
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_rootDens hS ν θ), MemLp.coeFn_toLp hqL] with x h1 h2
    rw [rootDensL2, hsq, h1, h2, RCLike.inner_apply, conj_trivial, mul_comm]
  have hnorm : ‖sq‖ = 1 := by
    have h : ‖sq‖ ^ 2 = 1 := by
      rw [hsq, norm_toLp_sq]
      simp_rw [fun x ↦ Real.mul_self_sqrt (hq0 x)]
      exact hq1
    nlinarith [norm_nonneg sq]
  have hang : ∀ θ, 2 * Real.arccos (∫ x, rootDens S ν θ x * √(q x) ∂ν) =
      2 * InnerProductGeometry.angle (rootDensL2 hS ν θ) sq := by
    intro θ
    unfold InnerProductGeometry.angle
    rw [hinner, norm_rootDensL2 hS ν, hnorm, mul_one, div_one]
  have htri := InnerProductGeometry.angle_le_angle_add_angle (rootDensL2 hS ν (γ 0))
    (rootDensL2 hS ν (γ 1)) sq
  have hlen := two_arccos_affinity_le_integral hS ν hγ hγ'
  have hlen' : 2 * InnerProductGeometry.angle (rootDensL2 hS ν (γ 1)) (rootDensL2 hS ν (γ 0)) ≤
      ∫ t in (0 : ℝ)..1, fisherNorm S ν (γ t) (γ' t) := by
    rw [← sphericalDist_eq_angle hS ν]
    exact hlen
  have hmargin := two_arccos_sqrt_real_le hS ν (γ 0) hqm hq0 hqi hq1 hA hsupp
  rw [hang (γ 0)] at hmargin
  rw [hang (γ 1), InnerProductGeometry.angle_comm (rootDensL2 hS ν (γ 1))] at *
  linarith

end Face

end Laplace.Multi
