/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.AngularBound

/-!
# Two-valued contrasts are great circles: the equality case of the angular bound

The angular bound `2 arccos ρ(s,t) ≤ ∫_s^t √Var_u` (`AngularBound`) compares the length of the
featureless line with the ambient Fisher–Rao distance of its endpoints. This module identifies when
it is an equality (Astra round 27 item 2, in its computable form):

* **Quadratic characterisation** (`twoValued_of_quadratic`, `quadratic_of_twoValued`): a centred
  contrast `X` satisfies `X² − Var = c X` a.e. — the condition for the square-root image of the
  natural line to be an unparametrised great circle — iff `X` takes at most two values a.e.
* **The two-atom state density** `ν = p δ_α + q δ_β` (`twoAtom`): the tilted laws form the Bernoulli
  family with weight `w_u = p e^{-uα}/(p e^{-uα} + q e^{-uβ})`, `Var_u = (β−α)² w_u(1−w_u)`
  (`lawVar_twoAtom`), and with `θ_u = arcsin √w_u`,

  `∫_s^t √Var_u du = 2θ_t − 2θ_s = 2 arccos ρ(s,t)`   (`twoAtom_length_eq_two_arccos`):

  the featureless line of a two-valued loss is a great circle of the square-root sphere, traversed
  at Fisher speed, and the angular bound is attained.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### The quadratic characterisation -/

/-- A contrast satisfying `X² − v = c X` a.e. (with `v ≥ 0`) takes at most two values a.e. -/
theorem twoValued_of_quadratic {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    {c v : ℝ} (hv : 0 ≤ v) (h : ∀ᵐ x ∂μ, f x ^ 2 - v = c * f x) :
    ∀ᵐ x ∂μ, f x = (c + Real.sqrt (c ^ 2 + 4 * v)) / 2 ∨
      f x = (c - Real.sqrt (c ^ 2 + 4 * v)) / 2 := by
  filter_upwards [h] with x hx
  have hq : (1 : ℝ) * (f x * f x) + (-c) * f x + (-v) = 0 := by linear_combination hx
  have hd : discrim 1 (-c) (-v) = Real.sqrt (c ^ 2 + 4 * v) * Real.sqrt (c ^ 2 + 4 * v) := by
    rw [discrim, Real.mul_self_sqrt (by positivity)]
    ring
  rcases (quadratic_eq_zero_iff one_ne_zero hd (f x)).mp hq with h1 | h1
  · left; rw [h1]; ring
  · right; rw [h1]; ring

/-- Conversely a two-valued function satisfies a quadratic identity. -/
theorem quadratic_of_twoValued {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    {α β : ℝ} (h : ∀ᵐ x ∂μ, f x = α ∨ f x = β) :
    ∀ᵐ x ∂μ, f x ^ 2 - (-(α * β)) = (α + β) * f x := by
  filter_upwards [h] with x hx
  rcases hx with hx | hx <;> rw [hx] <;> ring

/-! ### The two-atom state density -/

/-- The two-atom state density `p δ_α + q δ_β`. -/
noncomputable def twoAtom (p q α β : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac α + ENNReal.ofReal q • Measure.dirac β

theorem integral_twoAtom {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (α β : ℝ) (f : ℝ → ℝ) :
    ∫ ℓ, f ℓ ∂(twoAtom p q α β) = p * f α + q * f β := by
  unfold twoAtom
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq, smul_eq_mul, smul_eq_mul]

/-- The Bernoulli weight `w_u = p e^{-uα}/(p e^{-uα} + q e^{-uβ})` of the atom at `α`. -/
noncomputable def atomWeight (p q α β u : ℝ) : ℝ :=
  p * Real.exp (-(u * α)) / (p * Real.exp (-(u * α)) + q * Real.exp (-(u * β)))

/-- The partition function `Z(u) = p e^{-uα} + q e^{-uβ}`. -/
noncomputable def twoAtomZ (p q α β u : ℝ) : ℝ := p * Real.exp (-(u * α)) + q * Real.exp (-(u * β))

section TwoAtom

variable {p q α β : ℝ} (hp : 0 < p) (hq : 0 < q)
include hp hq

theorem twoAtomZ_pos (u : ℝ) : 0 < twoAtomZ p q α β u := by
  unfold twoAtomZ; positivity

theorem lawMoment_twoAtom_zero (u : ℝ) : lawMoment (twoAtom p q α β) 0 u = twoAtomZ p q α β u := by
  unfold lawMoment twoAtomZ
  rw [integral_twoAtom hp.le hq.le]
  simp only [pow_zero, one_mul]

theorem lawExp_twoAtom (f : ℝ → ℝ) (u : ℝ) :
    lawExp (twoAtom p q α β) f u =
      (p * (f α * Real.exp (-(u * α))) + q * (f β * Real.exp (-(u * β)))) / twoAtomZ p q α β u := by
  unfold lawExp twoAtomZ
  rw [integral_twoAtom hp.le hq.le, integral_twoAtom hp.le hq.le]

theorem atomWeight_pos (u : ℝ) : 0 < atomWeight p q α β u := by
  unfold atomWeight; positivity

theorem atomWeight_lt_one (u : ℝ) : atomWeight p q α β u < 1 := by
  unfold atomWeight
  rw [div_lt_one (by positivity)]
  have : 0 < q * Real.exp (-(u * β)) := by positivity
  linarith

/-- **The Bernoulli variance**: `Var_u(ℓ) = (β − α)² w_u (1 − w_u)`. -/
theorem lawVar_twoAtom (u : ℝ) :
    lawVar (twoAtom p q α β) u =
      (β - α) ^ 2 * (atomWeight p q α β u * (1 - atomWeight p q α β u)) := by
  unfold lawVar atomWeight
  rw [lawExp_twoAtom hp hq, lawExp_twoAtom hp hq]
  have hZ := twoAtomZ_pos hp hq (α := α) (β := β) u
  unfold twoAtomZ at hZ ⊢
  field_simp
  ring

/-- `w_u' = (β − α) w_u (1 − w_u)`. -/
theorem hasDerivAt_atomWeight (u : ℝ) :
    HasDerivAt (fun u ↦ atomWeight p q α β u)
      ((β - α) * (atomWeight p q α β u * (1 - atomWeight p q α β u))) u := by
  have hnα : HasDerivAt (fun x ↦ -(x * α)) (-α) u := (hasDerivAt_mul_const α).neg
  have hnβ : HasDerivAt (fun x ↦ -(x * β)) (-β) u := (hasDerivAt_mul_const β).neg
  have hN : HasDerivAt (fun x ↦ p * Real.exp (-(x * α))) (p * (Real.exp (-(u * α)) * -α)) u :=
    hnα.exp.const_mul p
  have hM : HasDerivAt (fun x ↦ q * Real.exp (-(x * β))) (q * (Real.exp (-(u * β)) * -β)) u :=
    hnβ.exp.const_mul q
  have hZ := twoAtomZ_pos hp hq (α := α) (β := β) u
  unfold twoAtomZ at hZ
  have hZ' : HasDerivAt (fun x ↦ p * Real.exp (-(x * α)) + q * Real.exp (-(x * β)))
      (p * (Real.exp (-(u * α)) * -α) + q * (Real.exp (-(u * β)) * -β)) u := hN.add hM
  have hdiv : HasDerivAt
      (fun x ↦ p * Real.exp (-(x * α)) / (p * Real.exp (-(x * α)) + q * Real.exp (-(x * β))))
      ((p * (Real.exp (-(u * α)) * -α) * (p * Real.exp (-(u * α)) + q * Real.exp (-(u * β))) -
        p * Real.exp (-(u * α)) *
          (p * (Real.exp (-(u * α)) * -α) + q * (Real.exp (-(u * β)) * -β))) /
        (p * Real.exp (-(u * α)) + q * Real.exp (-(u * β))) ^ 2) u := hN.div hZ' hZ.ne'
  refine hdiv.congr_deriv ?_
  unfold atomWeight
  have hZne : p * Real.exp (-(u * α)) + q * Real.exp (-(u * β)) ≠ 0 := hZ.ne'
  field_simp
  ring

theorem continuous_atomWeight : Continuous (fun u ↦ atomWeight p q α β u) :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_atomWeight hp hq u).continuousAt

/-- `u ↦ w_u` is monotone when `α < β`: the posterior concentrates on the smaller loss. -/
theorem atomWeight_monotone (hαβ : α < β) : Monotone (fun u ↦ atomWeight p q α β u) := by
  refine monotone_of_deriv_nonneg (fun u ↦ (hasDerivAt_atomWeight hp hq u).differentiableAt)
    fun u ↦ ?_
  rw [(hasDerivAt_atomWeight hp hq u).deriv]
  have h1 := atomWeight_pos hp hq (α := α) (β := β) u
  have h2 := atomWeight_lt_one hp hq (α := α) (β := β) u
  have : 0 ≤ β - α := by linarith
  have : 0 ≤ 1 - atomWeight p q α β u := by linarith
  positivity

/-- The angle `θ_u = arcsin √w_u ∈ [0, π/2]`. -/
noncomputable def atomAngle (p q α β u : ℝ) : ℝ := Real.arcsin (Real.sqrt (atomWeight p q α β u))

omit hp hq in
theorem atomAngle_nonneg (u : ℝ) : 0 ≤ atomAngle p q α β u :=
  Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)

omit hp hq in
theorem atomAngle_le (u : ℝ) : atomAngle p q α β u ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _

theorem sin_atomAngle (u : ℝ) : Real.sin (atomAngle p q α β u) = Real.sqrt (atomWeight p q α β u) :=
  Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg _))
    (Real.sqrt_le_one.mpr (atomWeight_lt_one hp hq u).le)

theorem cos_atomAngle (u : ℝ) :
    Real.cos (atomAngle p q α β u) = Real.sqrt (1 - atomWeight p q α β u) := by
  unfold atomAngle
  rw [Real.cos_arcsin, Real.sq_sqrt (atomWeight_pos hp hq u).le]

/-- **The Fisher speed is the angular speed**: `d/du (2θ_u) = √Var_u`. -/
theorem hasDerivAt_two_atomAngle (hαβ : α < β) (u : ℝ) :
    HasDerivAt (fun u ↦ 2 * atomAngle p q α β u) (Real.sqrt (lawVar (twoAtom p q α β) u)) u := by
  have hw0 := atomWeight_pos hp hq (α := α) (β := β) u
  have hw1 := atomWeight_lt_one hp hq (α := α) (β := β) u
  have hw := hasDerivAt_atomWeight hp hq (α := α) (β := β) u
  have hsqrt := hw.sqrt hw0.ne'
  have hx1 : Real.sqrt (atomWeight p q α β u) ≠ -1 :=
    ne_of_gt (by linarith [Real.sqrt_nonneg (atomWeight p q α β u)])
  have hx2 : Real.sqrt (atomWeight p q α β u) ≠ 1 := by
    rw [Ne, Real.sqrt_eq_one]
    exact hw1.ne
  have harc := (Real.hasDerivAt_arcsin hx1 hx2).comp u hsqrt
  refine (harc.const_mul 2).congr_deriv ?_
  rw [lawVar_twoAtom hp hq, Real.sq_sqrt hw0.le, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by linarith), Real.sqrt_mul hw0.le]
  set a := Real.sqrt (atomWeight p q α β u) with ha
  set b := Real.sqrt (1 - atomWeight p q α β u) with hb
  have ha2 : a ^ 2 = atomWeight p q α β u := Real.sq_sqrt hw0.le
  have hb2 : b ^ 2 = 1 - atomWeight p q α β u := Real.sq_sqrt (by linarith)
  have ha0 : 0 < a := Real.sqrt_pos.mpr hw0
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  clear_value a b
  rw [← ha2] at hb2 ⊢
  rw [← hb2]
  field_simp

theorem continuous_sqrt_lawVar_twoAtom :
    Continuous (fun u ↦ Real.sqrt (lawVar (twoAtom p q α β) u)) := by
  have e : (fun u ↦ Real.sqrt (lawVar (twoAtom p q α β) u)) = fun u ↦
      Real.sqrt ((β - α) ^ 2 * (atomWeight p q α β u * (1 - atomWeight p q α β u))) := by
    funext u; rw [lawVar_twoAtom hp hq]
  rw [e]
  have hw := continuous_atomWeight hp hq (α := α) (β := β)
  exact Real.continuous_sqrt.comp (continuous_const.mul (hw.mul (continuous_const.sub hw)))

/-- **The length of the Bernoulli line is the angular displacement.** -/
theorem twoAtom_length_eq (hαβ : α < β) (s t : ℝ) :
    ∫ u in s..t, Real.sqrt (lawVar (twoAtom p q α β) u) =
      2 * atomAngle p q α β t - 2 * atomAngle p q α β s :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hasDerivAt_two_atomAngle hp hq hαβ u)
    ((continuous_sqrt_lawVar_twoAtom hp hq).intervalIntegrable (μ := volume) s t)

/-- **The Bernoulli affinity**: `ρ(s,t) = √(w_s w_t) + √((1−w_s)(1−w_t))`. -/
theorem lawAffinity_twoAtom (s t : ℝ) :
    lawAffinity (twoAtom p q α β) s t =
      Real.sqrt (atomWeight p q α β s * atomWeight p q α β t) +
        Real.sqrt ((1 - atomWeight p q α β s) * (1 - atomWeight p q α β t)) := by
  have hZs := twoAtomZ_pos hp hq (α := α) (β := β) s
  have hZt := twoAtomZ_pos hp hq (α := α) (β := β) t
  have hZst : 0 < twoAtomZ p q α β s * twoAtomZ p q α β t := mul_pos hZs hZt
  have hw1 : ∀ u, 1 - atomWeight p q α β u =
      q * Real.exp (-(u * β)) / twoAtomZ p q α β u := fun u ↦ by
    have := twoAtomZ_pos hp hq (α := α) (β := β) u
    unfold atomWeight twoAtomZ at this ⊢
    field_simp
    ring
  have hsq : ∀ (c : ℝ) (γ : ℝ), 0 ≤ c → c * Real.exp (-(s * γ)) * (c * Real.exp (-(t * γ))) =
      (c * Real.exp (-((s + t) / 2 * γ))) * (c * Real.exp (-((s + t) / 2 * γ))) := fun c γ _ ↦ by
    rw [mul_mul_mul_comm, ← Real.exp_add, mul_mul_mul_comm, ← Real.exp_add]
    congr 2
    ring
  have h1 : Real.sqrt (atomWeight p q α β s * atomWeight p q α β t) =
      p * Real.exp (-((s + t) / 2 * α)) / Real.sqrt (twoAtomZ p q α β s * twoAtomZ p q α β t) := by
    rw [show atomWeight p q α β s = p * Real.exp (-(s * α)) / twoAtomZ p q α β s from rfl,
      show atomWeight p q α β t = p * Real.exp (-(t * α)) / twoAtomZ p q α β t from rfl,
      div_mul_div_comm, Real.sqrt_div' _ hZst.le, hsq p α hp.le,
      Real.sqrt_mul_self (by positivity)]
  have h2 : Real.sqrt ((1 - atomWeight p q α β s) * (1 - atomWeight p q α β t)) =
      q * Real.exp (-((s + t) / 2 * β)) / Real.sqrt (twoAtomZ p q α β s * twoAtomZ p q α β t) := by
    rw [hw1 s, hw1 t, div_mul_div_comm, Real.sqrt_div' _ hZst.le, hsq q β hq.le,
      Real.sqrt_mul_self (by positivity)]
  rw [h1, h2, ← add_div]
  unfold lawAffinity
  rw [lawMoment_twoAtom_zero hp hq, lawMoment_twoAtom_zero hp hq, lawMoment_twoAtom_zero hp hq]
  rfl

/-- `ρ(s,t) = cos(θ_t − θ_s)`. -/
theorem lawAffinity_twoAtom_eq_cos (s t : ℝ) :
    lawAffinity (twoAtom p q α β) s t = Real.cos (atomAngle p q α β t - atomAngle p q α β s) := by
  have hlt : 0 ≤ 1 - atomWeight p q α β s := by
    linarith [atomWeight_lt_one hp hq (α := α) (β := β) s]
  rw [lawAffinity_twoAtom hp hq, Real.cos_sub, cos_atomAngle hp hq, cos_atomAngle hp hq,
    sin_atomAngle hp hq, sin_atomAngle hp hq, Real.sqrt_mul (atomWeight_pos hp hq s).le,
    Real.sqrt_mul hlt]
  ring

/-- **Two-valued losses are great circles**: on the two-atom state density the angular bound is an
equality, `∫_s^t √Var_u du = 2 arccos ρ(s,t)`. -/
theorem twoAtom_length_eq_two_arccos (hαβ : α < β) {s t : ℝ} (hst : s ≤ t) :
    ∫ u in s..t, Real.sqrt (lawVar (twoAtom p q α β) u) =
      2 * Real.arccos (lawAffinity (twoAtom p q α β) s t) := by
  rw [twoAtom_length_eq hp hq hαβ, lawAffinity_twoAtom_eq_cos hp hq]
  have hmono : atomAngle p q α β s ≤ atomAngle p q α β t :=
    Real.monotone_arcsin (Real.sqrt_le_sqrt (atomWeight_monotone hp hq hαβ hst))
  have h0 : 0 ≤ atomAngle p q α β t - atomAngle p q α β s := by linarith
  have hπ : atomAngle p q α β t - atomAngle p q α β s ≤ Real.pi := by
    linarith [atomAngle_le (p := p) (q := q) (α := α) (β := β) t,
      atomAngle_nonneg (p := p) (q := q) (α := α) (β := β) s, Real.pi_pos]
  rw [Real.arccos_cos h0 hπ]
  ring

/-- The same statement in the form of `AngularBound`: equality in `two_arccos_affinityExp_le`. -/
theorem twoAtom_two_arccos_affinityExp_eq (hαβ : α < β) {s t : ℝ} (hst : s ≤ t) :
    2 * Real.arccos (affinityExp (twoAtom p q α β) s t) =
      ∫ u in s..t, Real.sqrt (lawVar (twoAtom p q α β) u) := by
  rw [affinityExp_eq _ (by rw [lawMoment_twoAtom_zero hp hq]; exact twoAtomZ_pos hp hq s)
    (by rw [lawMoment_twoAtom_zero hp hq]; exact twoAtomZ_pos hp hq t)
    (by rw [lawMoment_twoAtom_zero hp hq]; exact twoAtomZ_pos hp hq _),
    twoAtom_length_eq_two_arccos hp hq hαβ hst]

end TwoAtom

end Laplace.Multi
