/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSimplexIdentification
import Laplace.Multi.ResponseIntrinsicDistance
import Laplace.Multi.FisherCauchyRealisation

/-!
# The sphere theorem: the intrinsic Fisher distance of a saturated finite family

For a saturated finite family the response space is the open simplex
(`ResponseSimplexIdentification`), and the intrinsic Fisher distance is **exactly** the spherical
distance of the square roots:

`d_F(θ₀, θ₁) = 2 arccos ∑_x √(B(θ₀)_x B(θ₁)_x)` (`fisherDist_eq_two_arccos`), i.e. the spherical
lower bound `sphericalDist_le_fisherDist` of `ResponseIntrinsicDistance` is attained
(`fisherDist_eq_sphericalDist`).

The lower bound is the seabed's Hellinger-angle bound with the affinity evaluated as a finite sum
(`affinity_eq_sum_sqrt_atomMass`). The upper bound is a path: the **great circle**
`u_t = (sin((1−t)α)√p + sin(tα)√q)/sin α` on the unit sphere (`greatCircle`, `sum_sq_greatCircle`,
`sum_sq_greatCircleDeriv`: unit vectors with speed `α = arccos ∑√(pq)`), reparametrised by the
cosine step `φ(s) = (1 − cos πs)/2` (a global `C¹` map into `[0,1]`) so that it is a global `C¹`
path of *positive* vectors, squared to a path of simplex points `p_s = u_{φ(s)}²` (`spherePath`),
and lifted through the smooth inverse of the atom-mass map
(`sphereLift = B⁻¹ ∘ p`). The Fisher speed of the lift is computed through the log-lift: the loss
contrast of the velocity is `−ṗ/p` up to a constant, so `G(θ̇,θ̇) = ∑ ṗ_x²/p_x`
(`fisherVar_sphereLift`), which for `p = u²` is `4|u̇|²φ'² = 4α²φ'²`. The length is `2α`.

Consequences: `fisherDist_lt_pi` — the response space of a saturated finite family has Fisher
diameter at most `π`, so it is bounded and (being homeomorphic to an open simplex) not complete;
the geodesic between two responses is the great circle of their square-root laws, whereas the
featureless (mixture) journey is the straight segment — the two answer different questions.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Trig

/-- `sin²A + sin²B + 2 sin A sin B cos(A+B) = sin²(A+B)`. -/
theorem sin_sq_add_sin_sq_add_two_mul_cos_add (A B : ℝ) :
    Real.sin A ^ 2 + Real.sin B ^ 2 + 2 * Real.sin A * Real.sin B * Real.cos (A + B) =
      Real.sin (A + B) ^ 2 := by
  rw [Real.cos_add, Real.sin_add]
  linear_combination (-Real.sin A ^ 2) * Real.sin_sq_add_cos_sq B +
    (-Real.sin B ^ 2) * Real.sin_sq_add_cos_sq A

/-- `cos²A + cos²B − 2 cos A cos B cos(A+B) = sin²(A+B)`. -/
theorem cos_sq_add_cos_sq_sub_two_mul_cos_add (A B : ℝ) :
    Real.cos A ^ 2 + Real.cos B ^ 2 - 2 * Real.cos A * Real.cos B * Real.cos (A + B) =
      Real.sin (A + B) ^ 2 := by
  rw [Real.cos_add, Real.sin_add]
  linear_combination (-Real.cos A ^ 2) * Real.sin_sq_add_cos_sq B +
    (-Real.cos B ^ 2) * Real.sin_sq_add_cos_sq A

/-- **The cosine step** `φ(s) = (1 − cos πs)/2`: a global `C¹` map into `[0,1]` with `φ(0) = 0`,
`φ(1) = 1`, nondecreasing on `[0,1]`. -/
noncomputable def cosStep (s : ℝ) : ℝ := (1 - Real.cos (Real.pi * s)) / 2

/-- The derivative `φ'(s) = (π/2) sin(πs)` of the cosine step. -/
noncomputable def cosStepDeriv (s : ℝ) : ℝ := Real.pi / 2 * Real.sin (Real.pi * s)

theorem hasDerivAt_cosStep (s : ℝ) : HasDerivAt cosStep (cosStepDeriv s) s := by
  have h := (((hasDerivAt_id s).const_mul Real.pi).cos.const_sub 1).div_const 2
  refine h.congr_deriv ?_
  unfold cosStepDeriv
  simp only [id_eq, mul_one]
  ring

theorem cosStep_zero : cosStep 0 = 0 := by simp [cosStep]

theorem cosStep_one : cosStep 1 = 1 := by norm_num [cosStep, Real.cos_pi]

theorem cosStep_mem_Icc (s : ℝ) : cosStep s ∈ Icc (0 : ℝ) 1 := by
  unfold cosStep
  constructor
  · linarith [Real.cos_le_one (Real.pi * s)]
  · linarith [Real.neg_one_le_cos (Real.pi * s)]

theorem cosStepDeriv_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : 0 ≤ cosStepDeriv s :=
  mul_nonneg (by positivity) (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos]))

theorem continuous_cosStep : Continuous cosStep := by
  unfold cosStep
  fun_prop

theorem continuous_cosStepDeriv : Continuous cosStepDeriv := by
  unfold cosStepDeriv
  fun_prop

end Trig

section GreatCircle

variable {X : Type*} [Fintype X] [Nonempty X]

/-- The affinity `∑_x √(p_x q_x)` of two points of the simplex. -/
noncomputable def sphereAffinity (p q : X → ℝ) : ℝ := ∑ x, √(p x) * √(q x)

/-- The spherical angle `arccos ∑ √(pq)` between two points of the simplex. -/
noncomputable def sphereAngle (p q : X → ℝ) : ℝ := Real.arccos (sphereAffinity p q)

variable {p q : X → ℝ}

omit [Nonempty X] in
theorem sum_sq_sqrt (hp : p ∈ posSimplex X) : ∑ x, √(p x) ^ 2 = 1 := by
  rw [← hp.2]
  exact Finset.sum_congr rfl fun x _ ↦ Real.sq_sqrt (hp.1 x).le

theorem sphereAffinity_pos (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) :
    0 < sphereAffinity p q :=
  Finset.sum_pos (fun x _ ↦ mul_pos (Real.sqrt_pos.2 (hp.1 x)) (Real.sqrt_pos.2 (hq.1 x)))
    Finset.univ_nonempty

theorem sphereAffinity_le_one (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) :
    sphereAffinity p q ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x ↦ √(p x)) (fun x ↦ √(q x))
  rw [sum_sq_sqrt hp, sum_sq_sqrt hq, one_mul] at h
  exact (pow_le_one_iff_of_nonneg (sphereAffinity_pos hp hq).le two_ne_zero).mp h

omit [Nonempty X] in
theorem sphereAffinity_self (hp : p ∈ posSimplex X) : sphereAffinity p p = 1 := by
  unfold sphereAffinity
  rw [← hp.2]
  exact Finset.sum_congr rfl fun x _ ↦ Real.mul_self_sqrt (hp.1 x).le

omit [Nonempty X] in
theorem sphereAngle_self (hp : p ∈ posSimplex X) : sphereAngle p p = 0 := by
  rw [sphereAngle, sphereAffinity_self hp, Real.arccos_one]

/-- Distinct points of the simplex have affinity `< 1`. -/
theorem sphereAffinity_lt_one (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) :
    sphereAffinity p q < 1 := by
  refine lt_of_le_of_ne (sphereAffinity_le_one hp hq) fun h1 ↦ hne ?_
  have hsq : ∀ x, (√(p x) - √(q x)) ^ 2 = p x + q x - 2 * (√(p x) * √(q x)) := by
    intro x
    rw [sub_sq, Real.sq_sqrt (hp.1 x).le, Real.sq_sqrt (hq.1 x).le]
    ring
  have hsum : ∑ x, (√(p x) - √(q x)) ^ 2 = 0 := by
    simp only [hsq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have := h1
    unfold sphereAffinity at this
    rw [hp.2, hq.2, this]
    ring
  rw [Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ sq_nonneg _] at hsum
  funext x
  have := hsum x (Finset.mem_univ x)
  rw [sq_eq_zero_iff, sub_eq_zero, Real.sqrt_inj (hp.1 x).le (hq.1 x).le] at this
  exact this

theorem sphereAngle_pos (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) :
    0 < sphereAngle p q :=
  Real.arccos_pos.2 (sphereAffinity_lt_one hp hq hne)

theorem sphereAngle_lt_pi_div_two (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) :
    sphereAngle p q < Real.pi / 2 :=
  Real.arccos_lt_pi_div_two.2 (sphereAffinity_pos hp hq)

theorem sin_sphereAngle_pos (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) :
    0 < Real.sin (sphereAngle p q) :=
  Real.sin_pos_of_pos_of_lt_pi (sphereAngle_pos hp hq hne)
    ((sphereAngle_lt_pi_div_two hp hq).trans (half_lt_self Real.pi_pos))

theorem cos_sphereAngle (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) :
    Real.cos (sphereAngle p q) = sphereAffinity p q :=
  Real.cos_arccos (by linarith [sphereAffinity_pos hp hq]) (sphereAffinity_le_one hp hq)

variable (p q) in
/-- **The great circle** from `√p` to `√q`: `u_t = (sin((1−t)α)√p + sin(tα)√q)/sin α`. -/
noncomputable def greatCircle (t : ℝ) (x : X) : ℝ :=
  (Real.sin ((1 - t) * sphereAngle p q) * √(p x) + Real.sin (t * sphereAngle p q) * √(q x)) /
    Real.sin (sphereAngle p q)

variable (p q) in
/-- The velocity of the great circle. -/
noncomputable def greatCircleDeriv (t : ℝ) (x : X) : ℝ :=
  sphereAngle p q * (-Real.cos ((1 - t) * sphereAngle p q) * √(p x) +
    Real.cos (t * sphereAngle p q) * √(q x)) / Real.sin (sphereAngle p q)

theorem greatCircle_zero (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) (x : X) :
    greatCircle p q 0 x = √(p x) := by
  unfold greatCircle
  rw [sub_zero, one_mul, zero_mul, Real.sin_zero, zero_mul, add_zero,
    mul_div_cancel_left₀ _ (sin_sphereAngle_pos hp hq hne).ne']

theorem greatCircle_one (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) (x : X) :
    greatCircle p q 1 x = √(q x) := by
  unfold greatCircle
  rw [sub_self, zero_mul, Real.sin_zero, zero_mul, zero_add, one_mul,
    mul_div_cancel_left₀ _ (sin_sphereAngle_pos hp hq hne).ne']

/-- The great circle stays in the positive orthant on `[0,1]`. -/
theorem greatCircle_pos (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : X) : 0 < greatCircle p q t x := by
  have hα := sphereAngle_pos hp hq hne
  have hαπ := (sphereAngle_lt_pi_div_two hp hq).trans (half_lt_self Real.pi_pos)
  have h1 : 0 ≤ Real.sin ((1 - t) * sphereAngle p q) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
  have h2 : 0 ≤ Real.sin (t * sphereAngle p q) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
  have ha := Real.sqrt_pos.2 (hp.1 x)
  have hb := Real.sqrt_pos.2 (hq.1 x)
  refine div_pos ?_ (sin_sphereAngle_pos hp hq hne)
  rcases lt_or_eq_of_le ht1 with h | h
  · have : 0 < Real.sin ((1 - t) * sphereAngle p q) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
    exact add_pos_of_pos_of_nonneg (mul_pos this ha) (mul_nonneg h2 hb.le)
  · subst h
    rw [sub_self, zero_mul, Real.sin_zero, zero_mul, zero_add, one_mul]
    exact mul_pos (sin_sphereAngle_pos hp hq hne) hb

/-- The great circle lies on the unit sphere. -/
theorem sum_sq_greatCircle (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) (t : ℝ) :
    ∑ x, greatCircle p q t x ^ 2 = 1 := by
  have hs := (sin_sphereAngle_pos hp hq hne).ne'
  set α := sphereAngle p q with hα
  have key : ∀ x, greatCircle p q t x ^ 2 = (1 / Real.sin α) ^ 2 *
      (Real.sin ((1 - t) * α) ^ 2 * √(p x) ^ 2 +
        Real.sin (t * α) ^ 2 * √(q x) ^ 2 +
        2 * Real.sin ((1 - t) * α) * Real.sin (t * α) * (√(p x) * √(q x))) := by
    intro x
    unfold greatCircle
    rw [← hα]
    field_simp
    ring
  simp only [key, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [sum_sq_sqrt hp, sum_sq_sqrt hq]
  have hA : ∑ x, √(p x) * √(q x) = Real.cos α := (cos_sphereAngle hp hq).symm
  rw [hA, mul_one, mul_one]
  have h := sin_sq_add_sin_sq_add_two_mul_cos_add ((1 - t) * α) (t * α)
  rw [show (1 - t) * α + t * α = α by ring] at h
  rw [h]
  field_simp

/-- The great-circle velocity has constant speed `α`. -/
theorem sum_sq_greatCircleDeriv (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q)
    (t : ℝ) : ∑ x, greatCircleDeriv p q t x ^ 2 = sphereAngle p q ^ 2 := by
  have hs := (sin_sphereAngle_pos hp hq hne).ne'
  set α := sphereAngle p q with hα
  have key : ∀ x, greatCircleDeriv p q t x ^ 2 = (α / Real.sin α) ^ 2 *
      (Real.cos ((1 - t) * α) ^ 2 * √(p x) ^ 2 +
        Real.cos (t * α) ^ 2 * √(q x) ^ 2 -
        2 * Real.cos ((1 - t) * α) * Real.cos (t * α) * (√(p x) * √(q x))) := by
    intro x
    unfold greatCircleDeriv
    rw [← hα]
    field_simp
    ring
  simp only [key, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_sq_sqrt hp, sum_sq_sqrt hq]
  have hA : ∑ x, √(p x) * √(q x) = Real.cos α := (cos_sphereAngle hp hq).symm
  rw [hA, mul_one, mul_one]
  have h := cos_sq_add_cos_sq_sub_two_mul_cos_add ((1 - t) * α) (t * α)
  rw [show (1 - t) * α + t * α = α by ring] at h
  rw [h]
  field_simp

omit [Nonempty X] in
theorem hasDerivAt_greatCircle (t : ℝ) (x : X) :
    HasDerivAt (fun t ↦ greatCircle p q t x) (greatCircleDeriv p q t x) t := by
  have h1 : HasDerivAt (fun t ↦ Real.sin ((1 - t) * sphereAngle p q) * √(p x))
      (Real.cos ((1 - t) * sphereAngle p q) * (-1 * sphereAngle p q) * √(p x)) t :=
    (((hasDerivAt_id t).const_sub 1).mul_const (sphereAngle p q)).sin.mul_const _
  have h2 : HasDerivAt (fun t ↦ Real.sin (t * sphereAngle p q) * √(q x))
      (Real.cos (t * sphereAngle p q) * (1 * sphereAngle p q) * √(q x)) t :=
    ((hasDerivAt_id t).mul_const (sphereAngle p q)).sin.mul_const _
  refine ((h1.add h2).div_const (Real.sin (sphereAngle p q))).congr_deriv ?_
  unfold greatCircleDeriv
  ring

omit [Nonempty X] in
theorem continuous_greatCircleDeriv (x : X) : Continuous fun t ↦ greatCircleDeriv p q t x := by
  unfold greatCircleDeriv
  fun_prop

variable (p q) in
/-- **The sphere path**: the squared great circle, reparametrised by the smoothstep, a global
`C¹` path of simplex points. -/
noncomputable def spherePath (s : ℝ) (x : X) : ℝ := greatCircle p q (cosStep s) x ^ 2

variable (p q) in
/-- The velocity of the sphere path. -/
noncomputable def spherePathDeriv (s : ℝ) (x : X) : ℝ :=
  2 * greatCircle p q (cosStep s) x * (greatCircleDeriv p q (cosStep s) x * cosStepDeriv s)

omit [Nonempty X] in
theorem hasDerivAt_spherePath (s : ℝ) (x : X) :
    HasDerivAt (fun s ↦ spherePath p q s x) (spherePathDeriv p q s x) s := by
  have h := ((hasDerivAt_greatCircle (p := p) (q := q) (cosStep s) x).comp s
    (hasDerivAt_cosStep s)).pow 2
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, spherePathDeriv, Function.comp_def]

omit [Nonempty X] in
theorem continuous_spherePathDeriv (x : X) : Continuous fun s ↦ spherePathDeriv p q s x := by
  unfold spherePathDeriv
  have h1 : Continuous fun s ↦ greatCircle p q (cosStep s) x :=
    continuous_iff_continuousAt.2 fun s ↦
      ((hasDerivAt_greatCircle (cosStep s) x).comp s (hasDerivAt_cosStep s)).continuousAt
  exact (continuous_const.mul h1).mul
    (((continuous_greatCircleDeriv x).comp continuous_cosStep).mul continuous_cosStepDeriv)

omit [Nonempty X] in
theorem continuous_spherePath (x : X) : Continuous fun s ↦ spherePath p q s x :=
  continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_spherePath s x).continuousAt

theorem spherePath_pos (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) (s : ℝ)
    (x : X) : 0 < spherePath p q s x := by
  obtain ⟨h0, h1⟩ := cosStep_mem_Icc s
  exact pow_pos (greatCircle_pos hp hq hne h0 h1 x) 2

theorem spherePath_mem_posSimplex (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q)
    (s : ℝ) : spherePath p q s ∈ posSimplex X :=
  ⟨spherePath_pos hp hq hne s, sum_sq_greatCircle hp hq hne _⟩

/-- The velocity of the sphere path sums to zero. -/
theorem sum_spherePathDeriv (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q)
    (s : ℝ) : ∑ x, spherePathDeriv p q s x = 0 := by
  have h1 : HasDerivAt (fun s ↦ ∑ x, spherePath p q s x) (∑ x, spherePathDeriv p q s x) s :=
    HasDerivAt.fun_sum fun x _ ↦ hasDerivAt_spherePath s x
  have h2 : HasDerivAt (fun s ↦ ∑ x, spherePath p q s x) 0 s := by
    have : (fun s ↦ ∑ x, spherePath p q s x) = fun _ ↦ (1 : ℝ) := by
      funext s; exact (spherePath_mem_posSimplex hp hq hne s).2
    rw [this]; exact hasDerivAt_const s 1
  exact h1.unique h2

/-- **The Fisher energy of the sphere path**: `∑ ṗ_x²/p_x = 4 α² φ'(s)²`. -/
theorem sum_sq_div_spherePath (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q)
    (s : ℝ) : ∑ x, spherePathDeriv p q s x ^ 2 / spherePath p q s x =
      4 * sphereAngle p q ^ 2 * cosStepDeriv s ^ 2 := by
  obtain ⟨h0, h1⟩ := cosStep_mem_Icc s
  have key : ∀ x, spherePathDeriv p q s x ^ 2 / spherePath p q s x =
      4 * cosStepDeriv s ^ 2 * greatCircleDeriv p q (cosStep s) x ^ 2 := by
    intro x
    have hu := (greatCircle_pos hp hq hne h0 h1 x).ne'
    unfold spherePathDeriv spherePath
    field_simp
    ring
  simp only [key, ← Finset.mul_sum, sum_sq_greatCircleDeriv hp hq hne]
  ring

end GreatCircle

section Lift

variable {X : Type*} [MeasurableSpace X] [Nonempty X] [Fintype X] [MeasurableSingletonClass X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} ≠ 0) (hspan : SpansAffine S ν)
include hS hν hspan

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The loss contrast of `L⁻¹[g]` is `g` up to a constant. -/
theorem dirLoss_logInv (g : X → ℝ) :
    ∃ c : ℝ, ∀ x, dirLoss S (logInv hS ν hν hspan g : J → ℝ) x = g x + c := by
  have h : logLift S ν (logInv hS ν hν hspan g) = Submodule.Quotient.mk g := by
    change (logEquiv hS ν hν hspan) ((logEquiv hS ν hν hspan).symm (Submodule.mkQ _ g)) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [logLift_apply, Submodule.Quotient.eq, Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun x ↦ ?_⟩
  have := congrFun hc x
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Pi.sub_apply] at this
  linarith

omit [Nonempty X] [Nonempty J] hν hspan in
/-- **The affinity of two model laws is the simplex affinity of their atom masses.** -/
theorem affinity_eq_sum_sqrt_atomMass (θ η : J → ℝ) :
    affinity S ν θ η = ∑ x, √(atomMass S ν θ x) * √(atomMass S ν η x) := by
  unfold affinity
  rw [integral_fintype (integrable_of_bdd_prob _ (bdd_of_fintype _))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [smul_eq_mul, atomMass_eq hS ν, atomMass_eq hS ν, Real.sqrt_mul (famDens_nonneg hS ν θ x),
    Real.sqrt_mul (famDens_nonneg hS ν η x)]
  unfold rootDens
  have h := Real.mul_self_sqrt (measureReal_nonneg (μ := ν) (s := {x}))
  conv_lhs => rw [← h]
  ring

variable (p q : X → ℝ)

/-- **The lifted great circle** `θ_s = B⁻¹(p_s)` in the response space. -/
noncomputable def sphereLift (s : ℝ) : J → ℝ :=
  (simplexInv hS ν hν hspan (spherePath p q s) : J → ℝ)

/-- Its velocity `L⁻¹[−ṗ/p]`. -/
noncomputable def sphereLiftDeriv (s : ℝ) : J → ℝ :=
  (logInv hS ν hν hspan fun x ↦ -(spherePathDeriv p q s x / spherePath p q s x) : J → ℝ)

theorem sphereLift_mem (s : ℝ) : sphereLift hS ν hν hspan p q s ∈ 𝕍 :=
  (simplexInv hS ν hν hspan (spherePath p q s)).2

variable {p q}

theorem hasDerivAt_sphereLift (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q)
    (s : ℝ) :
    HasDerivAt (sphereLift hS ν hν hspan p q) (sphereLiftDeriv hS ν hν hspan p q s) s := by
  have hg : HasDerivAt (fun s ↦ fun x ↦ -Real.log (spherePath p q s x / ν.real {x}))
      (fun x ↦ -(spherePathDeriv p q s x / spherePath p q s x)) s := by
    refine hasDerivAt_pi.2 fun x ↦ ?_
    have hc := (measureReal_singleton_pos_of_ne_zero ν hν x).ne'
    have hpos := (spherePath_pos hp hq hne s x).ne'
    have h := (((hasDerivAt_spherePath s x).div_const (ν.real {x})).log
      (div_ne_zero hpos hc)).neg
    refine h.congr_deriv ?_
    rw [div_div_div_cancel_right₀ hc]
  have hL := (LinearMap.toContinuousLinearMap (logInv hS ν hν hspan)).hasFDerivAt.comp_hasDerivAt
    s hg
  exact (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt s hL

theorem continuous_sphereLiftDeriv (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) :
    Continuous (sphereLiftDeriv hS ν hν hspan p q) := by
  have hg : Continuous fun s ↦ fun x ↦ -(spherePathDeriv p q s x / spherePath p q s x) := by
    refine continuous_pi fun x ↦ ?_
    exact ((continuous_spherePathDeriv x).div (continuous_spherePath x)
      fun s ↦ (spherePath_pos hp hq hne s x).ne').neg
  exact (𝕍).subtypeL.continuous.comp
    ((LinearMap.toContinuousLinearMap (logInv hS ν hν hspan)).continuous.comp hg)

theorem sphereLift_zero (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) :
    sphereLift hS ν hν hspan p q 0 = (simplexInv hS ν hν hspan p : J → ℝ) := by
  unfold sphereLift
  congr 2
  funext x
  rw [spherePath, cosStep_zero, greatCircle_zero hp hq hne, Real.sq_sqrt (hp.1 x).le]

theorem sphereLift_one (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q) :
    sphereLift hS ν hν hspan p q 1 = (simplexInv hS ν hν hspan q : J → ℝ) := by
  unfold sphereLift
  congr 2
  funext x
  rw [spherePath, cosStep_one, greatCircle_one hp hq hne, Real.sq_sqrt (hq.1 x).le]

/-- **The Fisher speed of the lift**: `G(θ̇_s, θ̇_s) = ∑_x ṗ_x²/p_x`. -/
theorem fisherVar_sphereLift (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q)
    (s : ℝ) : fisherVar S ν (sphereLift hS ν hν hspan p q s) (sphereLiftDeriv hS ν hν hspan p q s) =
      ∑ x, spherePathDeriv p q s x ^ 2 / spherePath p q s x := by
  have hB : atomMass S ν (sphereLift hS ν hν hspan p q s) = spherePath p q s :=
    atomMass_simplexInv hS ν hν hspan (spherePath_mem_posSimplex hp hq hne s)
  have hpos : ∀ x, 0 < spherePath p q s x := spherePath_pos hp hq hne s
  have hsum : ∑ x, spherePath p q s x = 1 := (spherePath_mem_posSimplex hp hq hne s).2
  have hsumD := sum_spherePathDeriv hp hq hne s
  unfold fisherVar lawCov
  rw [integral_familyMeasure_eq_sum hS ν, integral_familyMeasure_eq_sum hS ν, hB]
  obtain ⟨c, hc⟩ := dirLoss_logInv hS ν hν hspan
    fun x ↦ -(spherePathDeriv p q s x / spherePath p q s x)
  have e1 : ∀ x, spherePath p q s x * (dirLoss S (sphereLiftDeriv hS ν hν hspan p q s) x *
      dirLoss S (sphereLiftDeriv hS ν hν hspan p q s) x) =
      spherePathDeriv p q s x ^ 2 / spherePath p q s x - 2 * c * spherePathDeriv p q s x +
        c ^ 2 * spherePath p q s x := by
    intro x
    unfold sphereLiftDeriv
    rw [hc x]
    field_simp [(hpos x).ne']
    ring
  have e2 : ∀ x, spherePath p q s x * dirLoss S (sphereLiftDeriv hS ν hν hspan p q s) x =
      -spherePathDeriv p q s x + c * spherePath p q s x := by
    intro x
    unfold sphereLiftDeriv
    rw [hc x]
    field_simp [(hpos x).ne']
  simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_neg_distrib, hsum, hsumD]
  ring

/-- The Fisher speed of the lift is `2αφ'(s)` on `[0,1]`. -/
theorem fisherNorm_sphereLift (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    fisherNorm S ν (sphereLift hS ν hν hspan p q s) (sphereLiftDeriv hS ν hν hspan p q s) =
      2 * sphereAngle p q * cosStepDeriv s := by
  unfold fisherNorm
  rw [fisherVar_sphereLift hS ν hν hspan hp hq hne s, sum_sq_div_spherePath hp hq hne s,
    show 4 * sphereAngle p q ^ 2 * cosStepDeriv s ^ 2 =
      (2 * sphereAngle p q * cosStepDeriv s) ^ 2 by ring]
  exact Real.sqrt_sq (mul_nonneg (mul_nonneg two_pos.le (Real.arccos_nonneg _))
    (cosStepDeriv_nonneg hs.1 hs.2))

/-- **The sphere theorem in simplex coordinates**: `d_F(B⁻¹p, B⁻¹q) = 2 arccos ∑√(pq)`. -/
theorem fisherDist_simplexInv (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) :
    fisherDist S ν (simplexInv hS ν hν hspan p) (simplexInv hS ν hν hspan q) =
      2 * sphereAngle p q := by
  by_cases hne : p = q
  · subst hne
    rw [fisherDist_self hS ν, sphereAngle_self hp, mul_zero]
  refine le_antisymm ?_ ?_
  · -- the lifted great circle has length `2α`
    have h := fisherDist_le_integral hS ν (sphereLift_mem hS ν hν hspan p q)
      (hasDerivAt_sphereLift hS ν hν hspan hp hq hne)
      (continuous_sphereLiftDeriv hS ν hν hspan hp hq hne) zero_le_one
    have h0 : (⟨sphereLift hS ν hν hspan p q 0, sphereLift_mem hS ν hν hspan p q 0⟩ : 𝕍) =
        simplexInv hS ν hν hspan p := Subtype.ext (sphereLift_zero hS ν hν hspan hp hq hne)
    have h1 : (⟨sphereLift hS ν hν hspan p q 1, sphereLift_mem hS ν hν hspan p q 1⟩ : 𝕍) =
        simplexInv hS ν hν hspan q := Subtype.ext (sphereLift_one hS ν hν hspan hp hq hne)
    rw [h0, h1] at h
    refine h.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_congr (g := fun s ↦ 2 * sphereAngle p q * cosStepDeriv s)
      fun s hs ↦ fisherNorm_sphereLift hS ν hν hspan hp hq hne
        (by rwa [uIcc_of_le zero_le_one] at hs)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hasDerivAt_cosStep s)
        (continuous_cosStepDeriv.intervalIntegrable _ _), cosStep_one, cosStep_zero]
    ring
  · -- the Hellinger-angle lower bound
    have h := sphericalDist_le_fisherDist hS ν (simplexInv hS ν hν hspan p)
      (simplexInv hS ν hν hspan q)
    unfold sphericalDist at h
    rwa [affinity_eq_sum_sqrt_atomMass hS ν, atomMass_simplexInv hS ν hν hspan hp,
      atomMass_simplexInv hS ν hν hspan hq] at h

/-- **THE SPHERE THEOREM**: for a saturated finite family,
`d_F(θ₀, θ₁) = 2 arccos ∑_x √(B(θ₀)_x B(θ₁)_x)`. -/
theorem fisherDist_eq_two_arccos (θ₀ θ₁ : 𝕍) :
    fisherDist S ν θ₀ θ₁ =
      2 * Real.arccos (∑ x, √(atomMass S ν (θ₀ : J → ℝ) x) * √(atomMass S ν (θ₁ : J → ℝ) x)) := by
  have := fisherDist_simplexInv hS ν hν hspan (atomMass_mem_posSimplex hS ν hν (θ₀ : J → ℝ))
    (atomMass_mem_posSimplex hS ν hν (θ₁ : J → ℝ))
  rwa [simplexInv_atomMass hS ν hν hspan, simplexInv_atomMass hS ν hν hspan] at this

set_option linter.unusedFintypeInType false in
/-- **The spherical lower bound is attained**: `d_F = 2 arccos(affinity)`. -/
theorem fisherDist_eq_sphericalDist (θ₀ θ₁ : 𝕍) :
    fisherDist S ν θ₀ θ₁ = sphericalDist S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ) := by
  rw [fisherDist_eq_two_arccos hS ν hν hspan]
  unfold sphericalDist
  rw [affinity_eq_sum_sqrt_atomMass hS ν]

set_option linter.unusedFintypeInType false in
/-- **The response space of a saturated finite family has Fisher diameter below `π`**: it is
bounded, hence (being an open simplex) not complete. -/
theorem fisherDist_lt_pi (θ₀ θ₁ : 𝕍) : fisherDist S ν θ₀ θ₁ < Real.pi := by
  rw [fisherDist_eq_two_arccos hS ν hν hspan]
  have h := sphereAngle_lt_pi_div_two (atomMass_mem_posSimplex hS ν hν (θ₀ : J → ℝ))
    (atomMass_mem_posSimplex hS ν hν (θ₁ : J → ℝ))
  unfold sphereAngle sphereAffinity at h
  linarith

end Lift

end Laplace.Multi
