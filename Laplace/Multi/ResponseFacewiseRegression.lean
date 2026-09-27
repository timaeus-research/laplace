/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseGlobalLipschitz
import Laplace.Multi.FiniteMinimalFace
import Laplace.Multi.FaceCoercivity
import Laplace.Multi.ResponseFiniteFibres

/-!
# Facewise convergence of the regression directions

At a boundary mean `M` of the moment polytope the response law `R_M` charges the atoms of the
support `A = supp q*(M)` only; its covariance form is positive definite on the **face direction
space** `W_A = span{S(x) − S(y) : x, y ∈ A}` (`covForm_pos_faceSpan`) and degenerate on the
rest of `W`. The regression direction `u_H(θ(M_k))` of an observable at interior means `M_k → M`
need not converge in `W`, but its **tangential component** does: with `π_A` the `Σ_{R_M}`-projection
onto `W_A` (`faceProj`; it agrees with the Euclidean orthogonal projection, since the discarded
component has a feature that is constant on the face) and `u_H^A` the regression direction of the
face law on `W_A` (`faceReg`),

`π_A(u_H(θ(M_k))) → u_H^A`   (`tendsto_faceProj_regressionDir`),

with the quantitative law-level estimate `‖π_A u − u_H^A‖ ≤ (3B(LB + K_H)/λ_A) Σ_x |p_x − q_x|`
(`norm_faceProj_sub_faceReg_le`) for any law `p` at which `u` solves the regression normal
equations on `W_A`, any bound `‖u‖ ≤ L`, and `λ_A` the coercivity constant of the face covariance.
The inputs are the `L¹` stability of covariances of a finite configuration
(`abs_lawCov_vecMeasure_sub_le`), the uniform regression bound of
`ResponseRegressionUniformBound`, and the continuity of the entropy projection on the polytope.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Stability

variable {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- Sums against a probability vector are bounded by the sup bound. -/
theorem abs_sum_mul_le_of_stdSimplex {q : X → ℝ} (hq : q ∈ stdSimplex ℝ X) {f : X → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) : |∑ x, q x * f x| ≤ K := by
  calc |∑ x, q x * f x| ≤ ∑ x, |q x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, q x * K := Finset.sum_le_sum fun x _ ↦ by
        rw [abs_mul, abs_of_nonneg (hq.1 x)]
        exact mul_le_mul_of_nonneg_left (hf x) (hq.1 x)
    _ = K := by rw [← Finset.sum_mul, hq.2, one_mul]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- The change of a sum against two weight vectors. -/
theorem abs_sum_mul_sub_sum_mul_le {p q : X → ℝ} {f : X → ℝ} {K : ℝ} (hf : ∀ x, |f x| ≤ K) :
    |(∑ x, p x * f x) - ∑ x, q x * f x| ≤ K * ∑ x, |p x - q x| := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ ↦ ?_)
  rw [← sub_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)

/-- **`L¹` stability of covariances on a finite configuration**:
`|Cov_p(f,g) − Cov_q(f,g)| ≤ 3 K_f K_g Σ_x |p_x − q_x|`. -/
theorem abs_lawCov_vecMeasure_sub_le {p q : X → ℝ} (hp : p ∈ stdSimplex ℝ X)
    (hq : q ∈ stdSimplex ℝ X) {f g : X → ℝ} {Kf Kg : ℝ} (hKf : 0 ≤ Kf)
    (hf : ∀ x, |f x| ≤ Kf) (hg : ∀ x, |g x| ≤ Kg) :
    |lawCov (vecMeasure p) f g - lawCov (vecMeasure q) f g| ≤
      3 * Kf * Kg * ∑ x, |p x - q x| := by
  unfold lawCov
  rw [integral_vecMeasure hp.1, integral_vecMeasure hp.1, integral_vecMeasure hp.1,
    integral_vecMeasure hq.1, integral_vecMeasure hq.1, integral_vecMeasure hq.1]
  have hfg : ∀ x, |f x * g x| ≤ Kf * Kg := fun x ↦ by
    rw [abs_mul]
    exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hKf
  have h1 := abs_sum_mul_sub_sum_mul_le (p := p) (q := q) hfg
  have h2 := abs_sum_mul_sub_sum_mul_le (p := p) (q := q) hf
  have h3 := abs_sum_mul_sub_sum_mul_le (p := p) (q := q) hg
  have h4 := abs_sum_mul_le_of_stdSimplex hp hg
  have h5 := abs_sum_mul_le_of_stdSimplex hq hf
  have hD : 0 ≤ ∑ x, |p x - q x| := Finset.sum_nonneg fun x _ ↦ abs_nonneg _
  have e : (∑ x, p x * (f x * g x)) - (∑ x, p x * f x) * (∑ x, p x * g x) -
      ((∑ x, q x * (f x * g x)) - (∑ x, q x * f x) * (∑ x, q x * g x)) =
      ((∑ x, p x * (f x * g x)) - ∑ x, q x * (f x * g x)) -
        (((∑ x, p x * f x) - ∑ x, q x * f x) * (∑ x, p x * g x) +
          (∑ x, q x * f x) * ((∑ x, p x * g x) - ∑ x, q x * g x)) := by ring
  rw [e]
  calc _ ≤ |(∑ x, p x * (f x * g x)) - ∑ x, q x * (f x * g x)| +
        (|(∑ x, p x * f x) - ∑ x, q x * f x| * |∑ x, p x * g x| +
          |∑ x, q x * f x| * |(∑ x, p x * g x) - ∑ x, q x * g x|) := by
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ ≤ Kf * Kg * ∑ x, |p x - q x| +
        ((Kf * ∑ x, |p x - q x|) * Kg + Kf * (Kg * ∑ x, |p x - q x|)) := by
        refine add_le_add h1 (add_le_add ?_ ?_)
        · exact mul_le_mul h2 h4 (abs_nonneg _) (by positivity)
        · exact mul_le_mul h5 h3 (abs_nonneg _) hKf
    _ = 3 * Kf * Kg * ∑ x, |p x - q x| := by ring

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- On a finite configuration every visible contrast is bounded by `B ‖u‖`, with
`B = Σ_j Σ_x |S_j(x)|`. -/
theorem abs_dirLoss_le_sum_norm {J : Type*} [Fintype J] (S : J → X → ℝ) (u : J → ℝ) (x : X) :
    |dirLoss S u x| ≤ (∑ j, ∑ y, |S j y|) * ‖u‖ := by
  unfold dirLoss
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [abs_mul, mul_comm]
  refine mul_le_mul ?_ ?_ (abs_nonneg _) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  · exact Finset.single_le_sum (f := fun y ↦ |S j y|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ x)
  · rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm u j

/-- A function with zero variance under a probability vector is constant on its support. -/
theorem eq_of_lawCov_vecMeasure_self_eq_zero {q : X → ℝ} (hq : q ∈ stdSimplex ℝ X) {f : X → ℝ}
    (h0 : lawCov (vecMeasure q) f f = 0) {x y : X} (hx : 0 < q x) (hy : 0 < q y) : f x = f y := by
  have hm : lawCov (vecMeasure q) f f = ∑ z, q z * (f z - ∑ w, q w * f w) ^ 2 := by
    unfold lawCov
    rw [integral_vecMeasure hq.1, integral_vecMeasure hq.1]
    have e : ∀ z, q z * (f z - ∑ w, q w * f w) ^ 2 =
        q z * (f z * f z) - (2 * ∑ w, q w * f w) * (q z * f z) +
          q z * (∑ w, q w * f w) ^ 2 := fun z ↦ by ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hq.2]
    ring
  rw [hm] at h0
  have hz : ∀ z, 0 < q z → f z = ∑ w, q w * f w := by
    intro z hz
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦
      mul_nonneg (hq.1 w) (sq_nonneg _)).1 h0 z (Finset.mem_univ z)
    rcases mul_eq_zero.1 hterm with h | h
    · exact absurd h hz.ne'
    · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  rw [hz x hx, hz y hy]

end Stability

section FaceForm

variable {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
  {J : Type*} [Fintype J] (S : J → X → ℝ) {q : X → ℝ} (hq : q ∈ stdSimplex ℝ X)
include hq

/-- The law of a probability vector. -/
local notation "Q" => vecMeasure q

/-- **The covariance form of the visible contrasts** under the law `q`,
`Σ_q(u, v) = Cov_q(⟨u,S⟩, ⟨v,S⟩)`. -/
noncomputable def covForm : LinearMap.BilinForm ℝ (J → ℝ) :=
  haveI := isProbabilityMeasure_vecMeasure hq
  LinearMap.mk₂ ℝ (fun u v ↦ lawCov Q (dirLoss S u) (dirLoss S v))
    (fun u u' v ↦ by
      rw [dirLoss_add, lawCov_add_left_eq _ (bdd_of_fintype _) (bdd_of_fintype _)
        (bdd_of_fintype _)])
    (fun c u v ↦ by rw [dirLoss_smul, lawCov_const_mul_left_eq, smul_eq_mul])
    (fun u v v' ↦ by
      rw [lawCov_comm, dirLoss_add, lawCov_add_left_eq _ (bdd_of_fintype _) (bdd_of_fintype _)
        (bdd_of_fintype _), lawCov_comm, lawCov_comm (vecMeasure q) (dirLoss S v')])
    (fun c u v ↦ by
      rw [lawCov_comm, dirLoss_smul, lawCov_const_mul_left_eq, smul_eq_mul, lawCov_comm])

theorem covForm_apply (u v : J → ℝ) :
    covForm S hq u v = lawCov Q (dirLoss S u) (dirLoss S v) := rfl

theorem covForm_comm (u v : J → ℝ) : covForm S hq u v = covForm S hq v u := by
  rw [covForm_apply, covForm_apply, lawCov_comm]

variable (V : Submodule ℝ (J → ℝ))

/-- Positive definiteness of the covariance form on a subspace. -/
def PosDefOn : Prop := ∀ w ∈ V, w ≠ 0 → 0 < covForm S hq w w

variable {S V}

theorem covForm_restrict_nondegenerate (hpd : PosDefOn S hq V) :
    ((covForm S hq).restrict V).Nondegenerate := by
  have hrefl : ((covForm S hq).restrict V).IsRefl := fun w w' h ↦ by
    change covForm S hq w w' = 0 at h
    change covForm S hq w' w = 0
    rw [covForm_comm]
    exact h
  refine hrefl.nondegenerate_iff_separatingLeft.2 fun w hw ↦ ?_
  by_contra hne
  have := hpd w w.2 (fun h ↦ hne (Subtype.ext h))
  have h0 := hw w
  change covForm S hq w w = 0 at h0
  rw [h0] at this
  exact lt_irrefl _ this

variable (S V) in
/-- The covariance functional `w ↦ Cov_q(H, ⟨w,S⟩)` on `V`. -/
noncomputable def covFun (H : X → ℝ) : Module.Dual ℝ V where
  toFun w := lawCov Q H (dirLoss S (w : J → ℝ))
  map_add' w w' := by
    have := isProbabilityMeasure_vecMeasure hq
    rw [Submodule.coe_add, lawCov_comm, dirLoss_add, lawCov_add_left_eq _ (bdd_of_fintype _)
      (bdd_of_fintype _) (bdd_of_fintype _), lawCov_comm, lawCov_comm (vecMeasure q) (dirLoss S _)]
  map_smul' c w := by
    have := isProbabilityMeasure_vecMeasure hq
    rw [Submodule.coe_smul, lawCov_comm, dirLoss_smul, lawCov_const_mul_left_eq, lawCov_comm,
      RingHom.id_apply, smul_eq_mul]

theorem covFun_apply (H : X → ℝ) (w : V) :
    covFun S hq V H w = lawCov Q H (dirLoss S (w : J → ℝ)) := rfl

variable (S V) in
/-- The functional `w ↦ Σ_q(u, w)` on `V`. -/
noncomputable def projFun (u : J → ℝ) : Module.Dual ℝ V :=
  (covForm S hq u) ∘ₗ V.subtype

theorem projFun_apply (u : J → ℝ) (w : V) : projFun S hq V u w = covForm S hq u w := rfl

/-- **The face regression direction** `u_H^A ∈ V`: the `Σ_q`-Riesz representative of
`w ↦ Cov_q(H, ⟨w,S⟩)` on `V`. -/
noncomputable def faceReg (hpd : PosDefOn S hq V) (H : X → ℝ) : V :=
  (((covForm S hq).restrict V).toDual (covForm_restrict_nondegenerate hq hpd)).symm
    (covFun S hq V H)

/-- **The tangential projection** `π_A u ∈ V`: the `Σ_q`-Riesz representative of `w ↦ Σ_q(u, w)`
on `V`. -/
noncomputable def faceProj (hpd : PosDefOn S hq V) (u : J → ℝ) : V :=
  (((covForm S hq).restrict V).toDual (covForm_restrict_nondegenerate hq hpd)).symm
    (projFun S hq V u)

/-- The defining property of the face regression direction. -/
theorem covForm_faceReg (hpd : PosDefOn S hq V) (H : X → ℝ) (w : V) :
    covForm S hq (faceReg hq hpd H : J → ℝ) w = lawCov Q H (dirLoss S (w : J → ℝ)) := by
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (B := (covForm S hq).restrict V)
    (hB := covForm_restrict_nondegenerate hq hpd) (covFun S hq V H) w
  rw [covFun_apply] at h
  exact h

/-- The defining property of the tangential projection. -/
theorem covForm_faceProj (hpd : PosDefOn S hq V) (u : J → ℝ) (w : V) :
    covForm S hq (faceProj hq hpd u : J → ℝ) w = covForm S hq u w := by
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (B := (covForm S hq).restrict V)
    (hB := covForm_restrict_nondegenerate hq hpd) (projFun S hq V u) w
  rw [projFun_apply] at h
  exact h

/-- The tangential projection fixes `V`. -/
theorem faceProj_of_mem (hpd : PosDefOn S hq V) {u : J → ℝ} (hu : u ∈ V) :
    (faceProj hq hpd u : J → ℝ) = u := by
  have hd : ∀ w : V, covForm S hq ((faceProj hq hpd u : J → ℝ) - u) w = 0 := fun w ↦ by
    rw [map_sub, LinearMap.sub_apply, covForm_faceProj, sub_self]
  by_contra hne
  have hne' : (faceProj hq hpd u : J → ℝ) - u ≠ 0 := sub_ne_zero.2 hne
  have hmem : (faceProj hq hpd u : J → ℝ) - u ∈ V := V.sub_mem (faceProj hq hpd u).2 hu
  have := hpd _ hmem hne'
  rw [hd ⟨_, hmem⟩] at this
  exact lt_irrefl _ this

/-- **Coercivity of a positive definite covariance form on a subspace**: `λ ‖w‖² ≤ Σ_q(w,w)`. -/
theorem exists_coercive_covForm (hpd : PosDefOn S hq V) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ w ∈ V, lam * ‖w‖ ^ 2 ≤ covForm S hq w w := by
  have := isProbabilityMeasure_vecMeasure hq
  have hcont : Continuous fun w : J → ℝ ↦ covForm S hq w w :=
    continuous_lawCov_dirLoss_self (fun j ↦ bdd_of_fintype (S j)) (vecMeasure q)
  set K : Set (J → ℝ) := Metric.sphere 0 1 ∩ (V : Set (J → ℝ)) with hK
  have hKc : IsCompact K :=
    (isCompact_sphere 0 1).inter_right (Submodule.closed_of_finiteDimensional _)
  by_cases hne : K.Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hKc.exists_isMinOn hne hcont.continuousOn
    have hw₀n : ‖w₀‖ = 1 := by simpa using hw₀.1
    refine ⟨covForm S hq w₀ w₀, hpd w₀ hw₀.2 (by rintro rfl; simp at hw₀n), fun w hw ↦ ?_⟩
    by_cases hw0 : w = 0
    · subst hw0
      simp
    · have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
      have hw' : ‖w‖⁻¹ • w ∈ K := by
        refine ⟨?_, Submodule.smul_mem _ _ hw⟩
        simp [norm_smul, hnw.ne']
      have h1 := (isMinOn_iff.1 hmin) _ hw'
      have h2 : covForm S hq w w = ‖w‖ ^ 2 * covForm S hq (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) := by
        rw [covForm_apply, covForm_apply, lawCov_dirLoss_smul_self _, ← mul_assoc, ← mul_pow,
          mul_inv_cancel₀ hnw.ne', one_pow, one_mul]
      rw [h2, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · refine ⟨1, one_pos, fun w hw ↦ ?_⟩
    have hw0 : w = 0 := by
      by_contra h
      have hnw : 0 < ‖w‖ := norm_pos_iff.2 h
      exact hne ⟨‖w‖⁻¹ • w, by simp [norm_smul, hnw.ne'], Submodule.smul_mem _ _ hw⟩
    subst hw0
    simp

/-- **THE LAW-LEVEL FACE STABILITY ESTIMATE**: if `u` solves the regression normal equations of
`H` on `V` under a law `p`, `‖u‖ ≤ L`, and `λ` is a coercivity constant of `Σ_q` on `V`, then
`‖π_V u − u_H^V‖ ≤ (3B(LB + K_H)/λ) Σ_x |p_x − q_x|` with `B = Σ_j Σ_x |S_j(x)|`. -/
theorem norm_faceProj_sub_faceReg_le (hpd : PosDefOn S hq V) {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ w ∈ V, lam * ‖w‖ ^ 2 ≤ covForm S hq w w) {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X)
    {H : X → ℝ} {KH : ℝ} (hKH : 0 ≤ KH) (hH : ∀ x, |H x| ≤ KH) {u : J → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hu : ‖u‖ ≤ L)
    (hreg : ∀ w ∈ V, lawCov (vecMeasure p) (dirLoss S u) (dirLoss S w) =
      lawCov (vecMeasure p) H (dirLoss S w)) :
    ‖(faceProj hq hpd u : J → ℝ) - (faceReg hq hpd H : J → ℝ)‖ ≤
      3 * (∑ j, ∑ y, |S j y|) * (L * (∑ j, ∑ y, |S j y|) + KH) / lam * ∑ x, |p x - q x| := by
  set B := ∑ j, ∑ y, |S j y| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  set D := ∑ x, |p x - q x| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  set d : V := faceProj hq hpd u - faceReg hq hpd H with hd
  have hdc : (d : J → ℝ) = (faceProj hq hpd u : J → ℝ) - (faceReg hq hpd H : J → ℝ) := by
    rw [hd, Submodule.coe_sub]
  -- the defect functional
  have hdef : ∀ w : V, covForm S hq (d : J → ℝ) w =
      (lawCov Q (dirLoss S u) (dirLoss S w) -
        lawCov (vecMeasure p) (dirLoss S u) (dirLoss S w)) +
      (lawCov (vecMeasure p) H (dirLoss S w) - lawCov Q H (dirLoss S w)) := by
    intro w
    rw [hdc, map_sub, LinearMap.sub_apply, covForm_faceProj, covForm_faceReg, hreg w w.2,
      covForm_apply]
    ring
  have hbound : ∀ w : V,
      |covForm S hq (d : J → ℝ) w| ≤ 3 * B * (L * B + KH) * ‖(w : J → ℝ)‖ * D := by
    intro w
    rw [hdef]
    have hu' : ∀ x, |dirLoss S u x| ≤ L * B := fun x ↦
      (abs_dirLoss_le_sum_norm S u x).trans (by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hu hB0)
    have hw' : ∀ x, |dirLoss S (w : J → ℝ) x| ≤ B * ‖(w : J → ℝ)‖ :=
      abs_dirLoss_le_sum_norm S _
    have h1 := abs_lawCov_vecMeasure_sub_le hp hq (mul_nonneg hL0 hB0) hu' hw'
    rw [abs_sub_comm] at h1
    have h2 := abs_lawCov_vecMeasure_sub_le hp hq hKH hH hw'
    calc _ ≤ |lawCov Q (dirLoss S u) (dirLoss S w) -
          lawCov (vecMeasure p) (dirLoss S u) (dirLoss S w)| +
          |lawCov (vecMeasure p) H (dirLoss S w) - lawCov Q H (dirLoss S w)| := abs_add_le _ _
      _ ≤ 3 * (L * B) * (B * ‖(w : J → ℝ)‖) * D + 3 * KH * (B * ‖(w : J → ℝ)‖) * D :=
          add_le_add h1 h2
      _ = 3 * B * (L * B + KH) * ‖(w : J → ℝ)‖ * D := by ring
  -- coercivity closes the estimate
  have hcd : lam * ‖(d : J → ℝ)‖ ^ 2 ≤ 3 * B * (L * B + KH) * ‖(d : J → ℝ)‖ * D :=
    (hcoer d d.2).trans ((le_abs_self _).trans (hbound d))
  rw [← hdc]
  by_cases hd0 : ‖(d : J → ℝ)‖ = 0
  · rw [hd0]
    positivity
  · have hpos : 0 < ‖(d : J → ℝ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0)
    have h2 : lam * ‖(d : J → ℝ)‖ ≤ 3 * B * (L * B + KH) * D := by
      refine le_of_mul_le_mul_right ?_ hpos
      calc lam * ‖(d : J → ℝ)‖ * ‖(d : J → ℝ)‖ = lam * ‖(d : J → ℝ)‖ ^ 2 := by ring
        _ ≤ 3 * B * (L * B + KH) * ‖(d : J → ℝ)‖ * D := hcd
        _ = 3 * B * (L * B + KH) * D * ‖(d : J → ℝ)‖ := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam, mul_comm]
    exact h2

/-- **Facewise convergence at the law level**: along laws `p_k → q` at which `u_k` solve the
regression normal equations of `H` on `V` with a uniform bound `‖u_k‖ ≤ L`, the tangential
projections converge to the face regression direction, `π_V u_k → u_H^V`. -/
theorem tendsto_faceProj (hpd : PosDefOn S hq V) {ι : Type*} {l : Filter ι} {p : ι → X → ℝ}
    (hp : ∀ k, p k ∈ stdSimplex ℝ X) (hpq : Tendsto p l (𝓝 q)) {H : X → ℝ} {KH : ℝ}
    (hKH : 0 ≤ KH) (hH : ∀ x, |H x| ≤ KH) {u : ι → J → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hu : ∀ k, ‖u k‖ ≤ L)
    (hreg : ∀ k, ∀ w ∈ V, lawCov (vecMeasure (p k)) (dirLoss S (u k)) (dirLoss S w) =
      lawCov (vecMeasure (p k)) H (dirLoss S w)) :
    Tendsto (fun k ↦ (faceProj hq hpd (u k) : J → ℝ)) l (𝓝 (faceReg hq hpd H : J → ℝ)) := by
  obtain ⟨lam, hlam, hcoer⟩ := exists_coercive_covForm hq hpd
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hD : Tendsto (fun k ↦ ∑ x, |p k x - q x|) l (𝓝 0) := by
    have : Tendsto (fun k ↦ ∑ x, |p k x - q x|) l (𝓝 (∑ x : X, |q x - q x|)) :=
      tendsto_finsetSum _ fun x _ ↦ ((tendsto_pi_nhds.1 hpq x).sub_const (q x)).abs
    simpa using this
  refine squeeze_zero (fun k ↦ norm_nonneg _) (fun k ↦ norm_faceProj_sub_faceReg_le hq hpd hlam
    hcoer (hp k) hKH hH hL0 (hu k) (hreg k)) ?_
  simpa using hD.const_mul (3 * (∑ j, ∑ y, |S j y|) * (L * (∑ j, ∑ y, |S j y|) + KH) / lam)

end FaceForm

section Boundary

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The regression direction. -/
local notation "uF" => regressionDir hS ν

omit [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- Interior means lie in the polytope. -/
theorem mem_hull_of_mem_Ω {M : J → ℝ} (hM : M ∈ Ω) : M ∈ hull := by
  rw [← momentBody_eq_convexHull hS ν hν]
  exact intrinsicInterior_subset hM

/-- The atom masses of a boundary mean form a probability vector. -/
theorem qStarVec_mem_stdSimplex_of_mem_hull {M : J → ℝ} (hM : M ∈ hull) :
    qStarVec hS ν M ∈ stdSimplex ℝ X :=
  qStarVec_mem_stdSimplex hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM)

omit [Nonempty J] hν in
/-- The model law is the law of its atom masses. -/
theorem familyMeasure_eq_vecMeasure_atomMass (θ : J → ℝ) :
    Pfam θ = vecMeasure (atomMass S ν θ) := by
  have := isProbabilityMeasure_family hS ν θ
  refine Measure.ext_iff_singleton.2 fun x ↦ ?_
  rw [vecMeasure_apply_singleton]
  unfold atomMass
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

variable (S) in
omit hS hν [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The face direction space** of a boundary mean: the span of the feature differences on the
support of `R_M`. -/
def faceSpan (M : J → ℝ) : Submodule ℝ (J → ℝ) :=
  vectorSpan ℝ (statPoint S '' supportSet hS ν M)

omit [MeasurableSingletonClass X] [IsProbabilityMeasure ν] in
/-- The face direction space lies in the direction space. -/
theorem faceSpan_le_dirSpan (M : J → ℝ) : faceSpan S hS ν M ≤ 𝕍 := by
  rw [dirSpan_eq_vectorSpan hS ν hν]
  exact vectorSpan_mono ℝ (image_subset_range _ _)

/-- **The face covariance is positive definite on the face direction space.** -/
theorem posDefOn_faceSpan {M : J → ℝ} (hM : M ∈ hull) :
    PosDefOn S (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM) (faceSpan S hS ν M) := by
  intro w hw hw0
  have hq := qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM
  have := isProbabilityMeasure_vecMeasure hq
  rw [covForm_apply]
  refine lt_of_le_of_ne (lawCov_self_nonneg _ (bdd_of_fintype _)) fun h0 ↦ hw0 ?_
  have hconst : ∀ x ∈ supportSet hS ν M, ∀ y ∈ supportSet hS ν M,
      dirLoss S w x = dirLoss S w y :=
    fun x hx y hy ↦ eq_of_lawCov_vecMeasure_self_eq_zero hq h0.symm hx hy
  have hker : faceSpan S hS ν M ≤
      LinearMap.ker (IsLinearMap.mk' (dotJ w) (isLinearMap_dotJ w)) := by
    unfold faceSpan
    rw [vectorSpan_def]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, IsLinearMap.mk'_apply]
    beta_reduce
    rw [vsub_eq_sub, (isLinearMap_dotJ w).map_sub, ← dirLoss_eq_dotJ_statPoint,
      ← dirLoss_eq_dotJ_statPoint, hconst x hx y hy, sub_self]
  have h1 : dotJ w w = 0 := hker hw
  unfold dotJ at h1
  funext j
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ mul_self_nonneg (w j)).1 h1 j
    (Finset.mem_univ j)
  exact mul_self_eq_zero.1 this

/-- **FACEWISE CONVERGENCE OF THE REGRESSION DIRECTIONS**: for interior means `M_k → M ∈ conv S(X)`
and a bounded observable `H`, the tangential projections of the regression directions converge to
the regression direction of the face law, `π_A(u_H(θ(M_k))) → u_H^A`. -/
theorem tendsto_faceProj_regressionDir {M : J → ℝ} (hM : M ∈ hull) {ι : Type*} {l : Filter ι}
    {Mk : ι → J → ℝ} (hMk : ∀ k, Mk k ∈ Ω) (hlim : Tendsto Mk l (𝓝 M)) {H : X → ℝ}
    (hH : Bdd H) :
    Tendsto (fun k ↦ (faceProj (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM)
        (posDefOn_faceSpan hS ν hν hM) (uF H (θr (Mk k)) : J → ℝ) : J → ℝ)) l
      (𝓝 (faceReg (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM)
        (posDefOn_faceSpan hS ν hν hM) H : J → ℝ)) := by
  obtain ⟨L, hL⟩ := exists_uniform_regressionDir_bound hS ν (fun x ↦ (hν x).ne') hH
  obtain ⟨KH, hKH⟩ := hH.2
  have hKH0 : 0 ≤ KH := (abs_nonneg _).trans (hKH (Classical.arbitrary X))
  refine tendsto_faceProj _ _ (p := fun k ↦ qStarVec hS ν (Mk k))
    (fun k ↦ qStarVec_mem_stdSimplex_of_mem_hull hS ν hν (mem_hull_of_mem_Ω hS ν hν (hMk k)))
    ?_ hKH0 hKH (L := |L|) (abs_nonneg L) (fun k ↦ (hL _).trans (le_abs_self L)) ?_
  · have hq : Tendsto (qStarVec hS ν) (𝓝[hull] M) (𝓝 (qStarVec hS ν M)) :=
      (continuousOn_qStarVec hS ν hν).continuousWithinAt hM
    exact hq.comp (tendsto_nhdsWithin_iff.2
      ⟨hlim, Eventually.of_forall fun k ↦ mem_hull_of_mem_Ω hS ν hν (hMk k)⟩)
  · intro k w hw
    have := fisherInner_regressionDir hS ν hH (θr (Mk k)) ⟨w, faceSpan_le_dirSpan hS ν hν _ hw⟩
    change lawCov (Pfam (θr (Mk k) : J → ℝ)) (dirLoss S (uF H (θr (Mk k)) : J → ℝ))
      (dirLoss S w) = lawCov (Pfam (θr (Mk k) : J → ℝ)) H (dirLoss S w) at this
    rwa [familyMeasure_eq_vecMeasure_atomMass hS ν, atomMass_responseTheta_eq_qStarVec hS ν (hMk k)]
      at this

end Boundary

end Laplace.Multi
