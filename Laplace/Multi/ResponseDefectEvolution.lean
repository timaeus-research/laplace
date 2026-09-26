/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDefect
import Laplace.Multi.ResponseSpeedDistortion

/-!
# The second derivative of the response defect

Along the data path `ρ_t = ν.tilted(t h)` the defect `ℰ(t) = D(ρ_t ‖ q_{m_t})` has
`ℰ'(t) = t Var_{ρ_t}(h) + ⟨θ_t, Cov_{ρ_t}(S,h)⟩` (`ResponseDefect`).  Differentiating once more,

  `ℰ''(t) = Var_{ρ_t}(h) − |q'_t|²_F + Cov_{ρ_t}((h − E_{ρ_t} h)², t h + ⟨θ_t, S⟩)`
  (`hasDerivAt_deriv_responseDefect`),

the **data speed squared minus the response speed squared plus an off-family correction**: the
last term is the covariance of the squared centred score with `log(dρ_t/dq_t)` (which equals
`t h + ⟨θ_t, S⟩` up to a constant).  At `t = 0` the correction vanishes (`θ_0 = 0`) and the identity
reduces to the residual-variance theorem; away from the family the correction can have either
sign, so the defect need not be convex (Astra's three-point example has `ℰ(0) = 0`, `ℰ > 0` on
`(0, ∞)` and `ℰ(t) → 0`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Evolution

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

omit [Nonempty X] [Fintype J] [Nonempty J] hS hh in
/-- Expansion of `∫ (f − c)² g` for bounded `f, g`. -/
theorem integral_sub_sq_mul (ρ : Measure X) [IsProbabilityMeasure ρ] {f g : X → ℝ} (hf : Bdd f)
    (hg : Bdd g) (c : ℝ) :
    ∫ x, (f x - c) ^ 2 * g x ∂ρ =
      (∫ x, g x * f x * f x ∂ρ) - 2 * c * (∫ x, g x * f x ∂ρ) + c ^ 2 * ∫ x, g x ∂ρ := by
  have e : ∀ x, (f x - c) ^ 2 * g x = g x * f x * f x - 2 * c * (g x * f x) + c ^ 2 * g x :=
    fun x ↦ by ring
  simp_rw [e]
  have h1 := integrable_of_bdd_prob ρ ((hg.mul hf).mul hf)
  have h2 := integrable_of_bdd_prob ρ (hg.mul hf)
  have h3 := integrable_of_bdd_prob ρ hg
  have h12 : Integrable (fun x ↦ g x * f x * f x - 2 * c * (g x * f x)) ρ :=
    h1.sub (h2.const_mul _)
  rw [integral_add h12 (h3.const_mul _), integral_sub h1 (h2.const_mul _), integral_const_mul,
    integral_const_mul]

omit [Nonempty X] [Fintype J] [Nonempty J] hS hh in
/-- Expansion of `∫ (f − c)²` for bounded `f`. -/
theorem integral_sub_sq (ρ : Measure X) [IsProbabilityMeasure ρ] {f : X → ℝ} (hf : Bdd f)
    (c : ℝ) :
    ∫ x, (f x - c) ^ 2 ∂ρ = (∫ x, f x * f x ∂ρ) - 2 * c * (∫ x, f x ∂ρ) + c ^ 2 := by
  have := integral_sub_sq_mul ρ hf (Bdd.const 1) c
  simp only [mul_one, one_mul] at this
  rw [this, integral_const, probReal_univ, one_smul, mul_one]

/-- The data law along the path. -/
local notation "ρ" t => ν.tilted fun x ↦ t * h x

/-- **The second derivative of the defect**:
`ℰ''(t) = Var_{ρ_t}(h) − |q'_t|²_F + Cov_{ρ_t}((h − E h)², t h + ⟨θ_t, S⟩)`. -/
theorem hasDerivAt_deriv_responseDefect (t : ℝ) :
    HasDerivAt (deriv (responseDefect S ν h))
      (lawCov (ρ t) h h - responseSpeedSq hS ν hh t +
        lawCov (ρ t) (fun x ↦ (h x - ∫ y, h y ∂(ρ t)) ^ 2)
          (fun x ↦ t * h x + dirLoss S (dataTheta hS ν hh t : J → ℝ) x)) t := by
  have hP : IsProbabilityMeasure (ρ t) := isProbabilityMeasure_dataPath ν hh t
  -- the first derivative as a function
  have e : deriv (responseDefect S ν h) = fun s ↦
      s * lawCov (ρ s) h h + dotJ (dataTheta hS ν hh s : J → ℝ) (dataCov S ν h s) :=
    funext fun s ↦ (hasDerivAt_responseDefect hS ν hh s).deriv
  rw [e]
  -- atoms
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∫ x, h x ∂(ρ t) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∫ x, h x * h x ∂(ρ t) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ x, h x * h x * h x ∂(ρ t) := ⟨_, rfl⟩
  obtain ⟨P, hP'⟩ : ∃ P : J → ℝ, P = fun j ↦ ∫ x, S j x ∂(ρ t) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : J → ℝ, Q = fun j ↦ ∫ x, S j x * h x ∂(ρ t) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : J → ℝ, R = fun j ↦ ∫ x, S j x * h x * h x ∂(ρ t) := ⟨_, rfl⟩
  -- derivative of the variance
  have hV : HasDerivAt (fun s ↦ lawCov (ρ s) h h)
      ((C - B * A) - ((B - A * A) * A + A * (B - A * A))) t := by
    have h1 := hasDerivAt_integral_tilted ν hh (hh.mul hh) t
    have h2 := hasDerivAt_integral_tilted ν hh hh t
    have := h1.sub (h2.mul h2)
    rw [← hA, ← hB, ← hC] at this
    exact this
  -- derivative of the data forcing
  have hPj : ∀ j, (∫ x, S j x ∂(ρ t)) = P j := fun j ↦ by rw [hP']
  have hQj : ∀ j, (∫ x, S j x * h x ∂(ρ t)) = Q j := fun j ↦ by rw [hQ]
  have hRj : ∀ j, (∫ x, S j x * h x * h x ∂(ρ t)) = R j := fun j ↦ by rw [hR]
  have hb : HasDerivAt (dataCov S ν h)
      (fun j ↦ (R j - Q j * A) - ((Q j - P j * A) * A + P j * (B - A * A))) t := by
    refine hasDerivAt_pi.2 fun j ↦ ?_
    have h1 := hasDerivAt_integral_tilted ν hh ((hS j).mul hh) t
    have h2 := hasDerivAt_integral_tilted ν hh (hS j) t
    have h3 := hasDerivAt_integral_tilted ν hh hh t
    have := h1.sub (h2.mul h3)
    rw [← hA, ← hB, hPj, hQj, hRj] at this
    exact this
  -- derivative of the natural coordinates
  have hθ : HasDerivAt (fun s ↦ (dataTheta hS ν hh s : J → ℝ)) (dataThetaVel hS ν hh t : J → ℝ) t :=
    (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_dataTheta_vel hS ν hh t)
  -- the pairing
  have hpair : HasDerivAt (fun s ↦ dotJ (dataTheta hS ν hh s : J → ℝ) (dataCov S ν h s))
      (∑ j, ((dataThetaVel hS ν hh t : J → ℝ) j * dataCov S ν h t j +
        (dataTheta hS ν hh t : J → ℝ) j *
          ((R j - Q j * A) - ((Q j - P j * A) * A + P j * (B - A * A))))) t := by
    simp only [dotJ]
    refine HasDerivAt.fun_sum fun j _ ↦ ?_
    exact (hasDerivAt_pi.1 hθ j).mul (hasDerivAt_pi.1 hb j)
  have hprod : HasDerivAt (fun s ↦ s * lawCov (ρ s) h h)
      (1 * lawCov (ρ t) h h + t * ((C - B * A) - ((B - A * A) * A + A * (B - A * A)))) t :=
    (hasDerivAt_id t).mul hV
  refine (hprod.add hpair).congr_deriv ?_
  -- identify the pieces
  rw [responseSpeedSq_eq_neg_dotJ hS ν hh t]
  have hcov1 : lawCov (ρ t) h h = B - A * A := by rw [lawCov, ← hA, ← hB]
  have hcov2 : lawCov (ρ t) (fun x ↦ (h x - ∫ y, h y ∂(ρ t)) ^ 2)
      (fun x ↦ t * h x + dirLoss S (dataTheta hS ν hh t : J → ℝ) x) =
      t * ((C - 2 * A * B + A ^ 2 * A) - (B - 2 * A * A + A ^ 2) * A) +
        ∑ j, (dataTheta hS ν hh t : J → ℝ) j *
          ((R j - 2 * A * Q j + A ^ 2 * P j) - (B - 2 * A * A + A ^ 2) * P j) := by
    obtain ⟨θ, hθ⟩ : ∃ θ : J → ℝ, θ = (dataTheta hS ν hh t : J → ℝ) := ⟨_, rfl⟩
    rw [← hθ, ← hA]
    have hsq : Bdd (fun x ↦ (h x - A) ^ 2) := by
      have := (hh.sub (Bdd.const A)).mul (hh.sub (Bdd.const A))
      simpa only [sq] using this
    have e1 : ∀ x, (h x - A) ^ 2 * (t * h x + dirLoss S θ x) =
        t * ((h x - A) ^ 2 * h x) + ∑ j, θ j * ((h x - A) ^ 2 * S j x) := by
      intro x
      simp only [dirLoss, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun j _ ↦ by ring
    have e2 : ∀ x, t * h x + dirLoss S θ x = t * h x + ∑ j, θ j * S j x := fun x ↦ rfl
    have hint1 : Integrable (fun x ↦ t * ((h x - A) ^ 2 * h x)) (ρ t) :=
      integrable_of_bdd_prob _ ((hsq.mul hh).const_mul t)
    have hint2 : Integrable (fun x ↦ ∑ j, θ j * ((h x - A) ^ 2 * S j x)) (ρ t) :=
      integrable_finsetSum _ fun j _ ↦ integrable_of_bdd_prob _ ((hsq.mul (hS j)).const_mul (θ j))
    have hint3 : Integrable (fun x ↦ t * h x) (ρ t) := integrable_of_bdd_prob _ (hh.const_mul t)
    have hint4 : Integrable (fun x ↦ ∑ j, θ j * S j x) (ρ t) :=
      integrable_finsetSum _ fun j _ ↦ integrable_of_bdd_prob _ ((hS j).const_mul (θ j))
    simp only [lawCov]
    simp_rw [e1, e2]
    rw [integral_add hint1 hint2, integral_add hint3 hint4, integral_const_mul, integral_const_mul,
      integral_finsetSum _ (fun j _ ↦ integrable_of_bdd_prob _ ((hsq.mul (hS j)).const_mul (θ j))),
      integral_finsetSum _ (fun j _ ↦ integrable_of_bdd_prob _ ((hS j).const_mul (θ j)))]
    simp only [integral_const_mul]
    rw [integral_sub_sq_mul (ρ t) hh hh A, integral_sub_sq (ρ t) hh A]
    have e3 : ∀ j, (∫ x, (h x - A) ^ 2 * S j x ∂(ρ t)) =
        R j - 2 * A * Q j + A ^ 2 * P j := fun j ↦ by
      rw [integral_sub_sq_mul (ρ t) hh (hS j) A, hPj, hQj, hRj]
    simp only [e3, hPj, ← hA, ← hB, ← hC]
    have e5 : (B - 2 * A * A + A ^ 2) * (t * A + ∑ j, θ j * P j) =
        (B - 2 * A * A + A ^ 2) * (t * A) + ∑ j, θ j * ((B - 2 * A * A + A ^ 2) * P j) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e5, add_sub_add_comm, ← Finset.sum_sub_distrib]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hcov1, hcov2]
  simp only [dotJ]
  have e6 : ∑ j, (dataTheta hS ν hh t : J → ℝ) j *
      ((R j - Q j * A) - ((Q j - P j * A) * A + P j * (B - A * A))) =
      ∑ j, (dataTheta hS ν hh t : J → ℝ) j *
        ((R j - 2 * A * Q j + A ^ 2 * P j) - (B - 2 * A * A + A ^ 2) * P j) :=
    Finset.sum_congr rfl fun j _ ↦ by ring
  rw [Finset.sum_add_distrib, e6]
  ring

/-- The second derivative of the defect as a value. -/
theorem deriv_deriv_responseDefect (t : ℝ) :
    deriv (deriv (responseDefect S ν h)) t =
      lawCov (ρ t) h h - responseSpeedSq hS ν hh t +
        lawCov (ρ t) (fun x ↦ (h x - ∫ y, h y ∂(ρ t)) ^ 2)
          (fun x ↦ t * h x + dirLoss S (dataTheta hS ν hh t : J → ℝ) x) :=
  (hasDerivAt_deriv_responseDefect hS ν hh t).deriv

/-- **Bounding the curvature**: `ℰ''(t) ≤ Var_{ρ_t}(h) + Cov_{ρ_t}((h − E h)², t h + ⟨θ_t, S⟩)`,
since the response speed is a variance. -/
theorem deriv_deriv_responseDefect_le (t : ℝ) :
    deriv (deriv (responseDefect S ν h)) t ≤
      lawCov (ρ t) h h + lawCov (ρ t) (fun x ↦ (h x - ∫ y, h y ∂(ρ t)) ^ 2)
        (fun x ↦ t * h x + dirLoss S (dataTheta hS ν hh t : J → ℝ) x) := by
  rw [deriv_deriv_responseDefect hS ν hh t]
  linarith [responseSpeedSq_nonneg hS ν hh t]

end Evolution

end Laplace.Multi
