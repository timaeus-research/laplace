/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RotatedDerivatives

/-!
# `a² < 3` keeps the minimum unique

The note's separable potential has coordinate potentials `ℓ(x) = λx²/2 + αx³/6 + γx⁴/24` with
`α = a λ^{3/2}`, `γ = λ²`, and says "`a² < 3` keeps the minimum unique". The seabed carries the
hypothesis `α² < 3λγ` (`a² < 3`) throughout; this file is the statement about the minimum itself,
made sharp:

* `anharmonicPotential_pos`: `α² < 3λγ → ℓ(x) > 0` for `x ≠ 0`, so `0` is the unique global
  minimiser (`anharmonicPotential_zero_lt`);
* `anharmonicPotential_root_of_disc_eq`, `anharmonicPotential_neg_of_disc_gt`: at `α² = 3λγ` the
  point `x₀ = −2α/γ` is a second zero (the minimiser is not unique), and for `α² > 3λγ` `ℓ(x₀) < 0`;
* `anharmonic_crit_iff`: `ℓ'` has a nonzero root iff `8λγ/3 ≤ α²` (`a² ≥ 8/3`): unimodality is lost
  before uniqueness of the global minimiser, so for `8/3 ≤ a² < 3` the potential has a local maximum
  and a second local minimum while `0` is still the unique global minimiser;
* `rotatedAnharmonic_pos`: E2's potential `L∘A` is positive away from its centre `c` (unique global
  minimiser in `d` dimensions), and `rotatedHess_posDef`: its Hessian `Q diag λ Qᵀ` is positive
  definite ("all are Morse at `w*`").
-/

open Matrix

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

section OneDim

variable {lam alpha gamma : ℝ}

/-- `ℓ(x) = x² q(x)`, `q(x) = λ/2 + αx/6 + γx²/24`. -/
theorem anharmonicPotential_eq_mul_sq (lam alpha gamma x : ℝ) :
    anharmonicPotential lam alpha gamma x =
      x ^ 2 * (lam / 2 + alpha / 6 * x + gamma / 24 * x ^ 2) := by
  simp only [anharmonicPotential]
  ring

/-- `24γ q(x) = (γx + 2α)² + (12λγ − 4α²)`. -/
theorem quad_factor_pos (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (x : ℝ) :
    0 < lam / 2 + alpha / 6 * x + gamma / 24 * x ^ 2 := by
  have h : 24 * gamma * (lam / 2 + alpha / 6 * x + gamma / 24 * x ^ 2) =
      (gamma * x + 2 * alpha) ^ 2 + (12 * lam * gamma - 4 * alpha ^ 2) := by ring
  have hpos : 0 < 24 * gamma * (lam / 2 + alpha / 6 * x + gamma / 24 * x ^ 2) := by
    rw [h]
    nlinarith [sq_nonneg (gamma * x + 2 * alpha)]
  exact (mul_pos_iff_of_pos_left (by positivity)).mp hpos

/-- **`α² < 3λγ` makes `0` the unique global minimiser**: `ℓ(x) > 0` for `x ≠ 0`. -/
theorem anharmonicPotential_pos (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    {x : ℝ} (hx : x ≠ 0) : 0 < anharmonicPotential lam alpha gamma x := by
  rw [anharmonicPotential_eq_mul_sq]
  exact mul_pos (by positivity) (quad_factor_pos hgamma hdisc x)

theorem anharmonicPotential_zero (lam alpha gamma : ℝ) :
    anharmonicPotential lam alpha gamma 0 = 0 := by
  simp [anharmonicPotential]

theorem anharmonicPotential_nonneg (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    (x : ℝ) : 0 ≤ anharmonicPotential lam alpha gamma x := by
  rcases eq_or_ne x 0 with hx | hx
  · rw [hx, anharmonicPotential_zero]
  · exact (anharmonicPotential_pos hgamma hdisc hx).le

theorem anharmonicPotential_zero_lt (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    {x : ℝ} (hx : x ≠ 0) :
    anharmonicPotential lam alpha gamma 0 < anharmonicPotential lam alpha gamma x := by
  rw [anharmonicPotential_zero]
  exact anharmonicPotential_pos hgamma hdisc hx

/-- `q(−2α/γ) = (3λγ − α²)/(6γ)`. -/
theorem quad_factor_at (hgamma : gamma ≠ 0) :
    lam / 2 + alpha / 6 * (-(2 * alpha / gamma)) + gamma / 24 * (-(2 * alpha / gamma)) ^ 2 =
      (3 * lam * gamma - alpha ^ 2) / (6 * gamma) := by
  field_simp
  ring

/-- **Sharpness at equality**: for `α² = 3λγ` the point `−2α/γ` is a second zero of `ℓ`. -/
theorem anharmonicPotential_root_of_disc_eq (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 = 3 * lam * gamma) :
    anharmonicPotential lam alpha gamma (-(2 * alpha / gamma)) = 0 := by
  rw [anharmonicPotential_eq_mul_sq, quad_factor_at hgamma.ne', hdisc, sub_self, zero_div,
    mul_zero]

/-- **Beyond the threshold** `0` is not a global minimiser: `ℓ(−2α/γ) < 0` when `α² > 3λγ`. -/
theorem anharmonicPotential_neg_of_disc_gt (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : 3 * lam * gamma < alpha ^ 2) :
    anharmonicPotential lam alpha gamma (-(2 * alpha / gamma)) < 0 := by
  have halpha : alpha ≠ 0 := by
    rintro rfl
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3) hlam) hgamma
    simp at hdisc
    linarith
  rw [anharmonicPotential_eq_mul_sq, quad_factor_at hgamma.ne']
  have hx : (-(2 * alpha / gamma)) ^ 2 > 0 := by
    have : -(2 * alpha / gamma) ≠ 0 := by
      intro h
      have := neg_eq_zero.mp h
      rw [div_eq_zero_iff] at this
      rcases this with h2 | h2
      · exact halpha (by linarith)
      · exact hgamma.ne' h2
    positivity
  exact mul_neg_of_pos_of_neg hx (div_neg_of_neg_of_pos (by linarith) (by positivity))

/-- `24γ q(x) ≥ 0` when `α² ≤ 3λγ`: `ℓ ≥ 0` up to and including the threshold. -/
theorem anharmonicPotential_nonneg_of_disc_le (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 ≤ 3 * lam * gamma) (x : ℝ) : 0 ≤ anharmonicPotential lam alpha gamma x := by
  rw [anharmonicPotential_eq_mul_sq]
  refine mul_nonneg (sq_nonneg x) ?_
  have h : 24 * gamma * (lam / 2 + alpha / 6 * x + gamma / 24 * x ^ 2) =
      (gamma * x + 2 * alpha) ^ 2 + (12 * lam * gamma - 4 * alpha ^ 2) := by ring
  have hnn : 0 ≤ 24 * gamma * (lam / 2 + alpha / 6 * x + gamma / 24 * x ^ 2) := by
    rw [h]
    nlinarith [sq_nonneg (gamma * x + 2 * alpha)]
  exact nonneg_of_mul_nonneg_right hnn (by positivity)

/-- **Two global minimisers at the threshold**: for `α² = 3λγ`, `0` and `−2α/γ ≠ 0` both
minimise. -/
theorem anharmonicPotential_two_minimisers (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 = 3 * lam * gamma) :
    -(2 * alpha / gamma) ≠ 0 ∧ anharmonicPotential lam alpha gamma (-(2 * alpha / gamma)) = 0 ∧
      ∀ x, 0 ≤ anharmonicPotential lam alpha gamma x := by
  have halpha : alpha ≠ 0 := by
    rintro rfl
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3) hlam) hgamma
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at hdisc
    linarith
  refine ⟨?_, anharmonicPotential_root_of_disc_eq hgamma hdisc,
    anharmonicPotential_nonneg_of_disc_le hgamma hdisc.le⟩
  intro h
  have := neg_eq_zero.mp h
  rw [div_eq_zero_iff] at this
  rcases this with h2 | h2
  · exact halpha (by linarith)
  · exact hgamma.ne' h2

/-- **Critical points**: `ℓ'` has a nonzero root iff `8λγ/3 ≤ α²`. -/
theorem anharmonic_crit_iff (hlam : 0 < lam) (hgamma : 0 < gamma) :
    (∃ x, x ≠ 0 ∧ anhD1 lam alpha gamma x = 0) ↔ 8 * lam * gamma / 3 ≤ alpha ^ 2 := by
  have hfac : ∀ x, anhD1 lam alpha gamma x = x * (gamma / 6 * (x * x) + alpha / 2 * x + lam) := by
    intro x
    simp only [anhD1]
    ring
  have ha : gamma / 6 ≠ 0 := by positivity
  have hdisc : discrim (gamma / 6) (alpha / 2) lam = alpha ^ 2 / 4 - 2 * lam * gamma / 3 := by
    simp only [discrim]
    ring
  constructor
  · rintro ⟨x, hx, h⟩
    rw [hfac, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h hx
    · have hsq := discrim_eq_sq_of_quadratic_eq_zero h
      rw [hdisc] at hsq
      nlinarith [sq_nonneg (2 * (gamma / 6) * x + alpha / 2)]
  · intro hle
    set D := alpha ^ 2 / 4 - 2 * lam * gamma / 3 with hD
    have hD0 : 0 ≤ D := by rw [hD]; linarith
    have hs : discrim (gamma / 6) (alpha / 2) lam = Real.sqrt D * Real.sqrt D := by
      rw [hdisc, Real.mul_self_sqrt hD0]
    refine ⟨(-(alpha / 2) - Real.sqrt D) / (2 * (gamma / 6)), ?_, ?_⟩
    · intro h0
      rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD0
        have hs' : Real.sqrt D = -(alpha / 2) := by linarith
        rw [hs'] at hsq
        have := mul_pos hlam hgamma
        rw [hD] at hsq
        nlinarith
      · linarith
    · rw [hfac]
      have := (quadratic_eq_zero_iff ha hs ((-(alpha / 2) - Real.sqrt D) / (2 * (gamma / 6)))).mpr
        (Or.inr rfl)
      rw [this, mul_zero]

/-- **At `α² = 8λγ/3` the extra critical point is a stationary inflection**: `x* = −3α/(2γ)` has
`ℓ'(x*) = 0 = ℓ''(x*)`. -/
theorem anharmonic_inflection (hgamma : 0 < gamma) (hdisc : alpha ^ 2 = 8 * lam * gamma / 3) :
    anhD1 lam alpha gamma (-(3 * alpha / (2 * gamma))) = 0 ∧
      anhD2 lam alpha gamma (-(3 * alpha / (2 * gamma))) = 0 := by
  have hne := hgamma.ne'
  have hlam : lam = 3 * alpha ^ 2 / (8 * gamma) := by
    field_simp
    linarith
  constructor
  · simp only [anhD1]
    rw [hlam]
    field_simp
    ring
  · simp only [anhD2]
    rw [hlam]
    field_simp
    ring

/-- **A global convexity bound**: `2γ ℓ''(x) = (γx + α)² + (2λγ − α²)`, so `ℓ'' ≥ λ − α²/(2γ)`;
for `α² < 2λγ` (the note's `a² < 2`, which covers E2's `a ∈ {½, 1}`) the potential is strongly
convex. -/
theorem anhD2_ge (hgamma : 0 < gamma) (x : ℝ) :
    lam - alpha ^ 2 / (2 * gamma) ≤ anhD2 lam alpha gamma x := by
  have h : 2 * gamma * (anhD2 lam alpha gamma x - (lam - alpha ^ 2 / (2 * gamma))) =
      (gamma * x + alpha) ^ 2 := by
    simp only [anhD2]
    field_simp
    ring
  have hnn : 0 ≤ 2 * gamma * (anhD2 lam alpha gamma x - (lam - alpha ^ 2 / (2 * gamma))) := by
    rw [h]; exact sq_nonneg _
  have := nonneg_of_mul_nonneg_right hnn (by positivity : (0 : ℝ) < 2 * gamma)
  linarith

/-- `ℓ''(0) = λ > 0`: the minimiser is nondegenerate. -/
theorem anhD2_zero_pos (hlam : 0 < lam) : 0 < anhD2 lam alpha gamma 0 := by
  simp [anhD2, hlam]

end OneDim

/-! ### The `d`-dimensional potential -/

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ}

theorem affineFrame_ne_zero (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) {w : Fin d → ℝ} (hw : w ≠ c) :
    affineFrame Q c w ≠ 0 := by
  intro h
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have : w - c = Q *ᵥ (Qᵀ *ᵥ (w - c)) := by
    rw [Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
  have h' : Qᵀ *ᵥ (w - c) = 0 := h
  rw [h', Matrix.mulVec_zero, sub_eq_zero] at this
  exact hw this

/-- **`c` is the unique global minimiser of E2's potential**: `L∘A(w) > 0` for `w ≠ c`. -/
theorem rotatedAnharmonic_pos (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {w : Fin d → ℝ} (hw : w ≠ c) :
    0 < rotatedAnharmonic Q c lam alpha gamma w := by
  change 0 < ∑ i, anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (affineFrame_ne_zero hQ c hw)
  refine Finset.sum_pos' (fun j _ => anharmonicPotential_nonneg (hgamma j) (hdisc j) _)
    ⟨i, Finset.mem_univ i, anharmonicPotential_pos (hgamma i) (hdisc i) hi⟩

theorem rotatedAnharmonic_center_lt (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {w : Fin d → ℝ} (hw : w ≠ c) :
    rotatedAnharmonic Q c lam alpha gamma c < rotatedAnharmonic Q c lam alpha gamma w := by
  rw [rotatedAnharmonic_center]
  exact rotatedAnharmonic_pos hQ c hgamma hdisc hw

/-- **Morse at `w*`**: the Hessian `Q diag λ Qᵀ` of E2's potential is positive definite. -/
theorem rotatedHess_posDef (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) :
    (Q * diagonal lam * Qᵀ).PosDef := by
  have hdiag : (diagonal lam).PosDef := Matrix.PosDef.diagonal hlam
  have hinj : Function.Injective (Qᵀ).mulVec := by
    intro x y hxy
    have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
    have := congrArg Q.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hQQ] using this
  have := Matrix.PosDef.conjTranspose_mul_mul_same hdiag hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at this

end Multi

end Laplace.Multi
