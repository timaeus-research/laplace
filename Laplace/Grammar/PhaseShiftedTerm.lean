/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseTaylorTail

/-!
# Shifted-exponent transport for the phase expansion

Unit 200 (programme A, step 2). The `j`-th Taylor term of the phase factor `e^{βNu^kξ(u)}` is
`(βN)^j/j! · ξ(u)^j u^{jk}`, so it turns the dressed integral with exponents `h` into one with
exponents `h + jk` and amplitude `ξ^j η`. This file records that the shift
`h ↦ h + jk`, `λ ↦ λ + j/2` leaves the whole face structure invariant, and packages the `j`-th term
as a limit in the chart variable `N` (monomial parameter `N²`, leading scale
`N^{-2λ}(log N)^{m-1}`).

* `phaseShift h k j = fun i => h i + j * k i`; `prod_pow_phaseShift`: `u^{h+jk} = u^h (u^k)^j`.
* `ratioExp_phaseShift`: `ratioExp (h+jk) k i = ratioExp h k i + j/2`; hence `multCount_phaseShift`,
  `faceProj_phaseShift`, `residualWeight_phaseShift` (the residual exponents `hᵢ + jkᵢ − 2kᵢ(λ+j/2)`
  are `hᵢ − 2kᵢλ`), and the explicit `faceLeadConst_phaseShift`, `amplitudeCoeff_phaseShift`.
* `shifted_term_tendsto`: `N^j ∫ η u^{h+jk} e^{-βN²u^{2k}} / (N^{-2λ}(log N)^{m-1})
  → 2^{m-1} amplitudeCoeff (h+jk) k (λ+j/2) β η`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- The shifted exponent vector `h + j·k`. -/
def phaseShift {d : ℕ} (h k : Fin d → ℕ) (j : ℕ) : Fin d → ℕ := fun i => h i + j * k i

theorem prod_pow_phaseShift {d : ℕ} (h k : Fin d → ℕ) (j : ℕ) (x : Fin d → ℝ) :
    ∏ i, x i ^ phaseShift h k j i = (∏ i, x i ^ h i) * (∏ i, x i ^ k i) ^ j := by
  simp only [phaseShift, pow_add, Finset.prod_mul_distrib, pow_mul', Finset.prod_pow]

theorem ratioExp_phaseShift {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : ℕ) (i : Fin d) :
    ratioExp (phaseShift h k j) k i = ratioExp h k i + j / 2 := by
  unfold ratioExp phaseShift
  have : (k i : ℝ) ≠ 0 := by exact_mod_cast (hk i).ne'
  push_cast
  field_simp
  ring

theorem ratioExp_phaseShift_eq_iff {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : ℕ) (l : ℝ)
    (i : Fin d) : ratioExp (phaseShift h k j) k i = l + j / 2 ↔ ratioExp h k i = l := by
  rw [ratioExp_phaseShift h k hk j i, add_left_inj]

theorem multCount_phaseShift {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : ℕ) (l : ℝ) :
    multCount (ratioExp (phaseShift h k j) k) (l + j / 2) = multCount (ratioExp h k) l := by
  unfold multCount
  simp only [ratioExp_phaseShift_eq_iff h k hk j l]

theorem faceProj_phaseShift {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : ℕ) (l : ℝ) :
    faceProj (phaseShift h k j) k (l + j / 2) = faceProj h k l := by
  funext u i
  simp only [faceProj, ratioExp_phaseShift_eq_iff h k hk j l]

theorem residualWeight_phaseShift {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : ℕ) (l : ℝ) :
    residualWeight (phaseShift h k j) k (l + j / 2) = residualWeight h k l := by
  funext u
  unfold residualWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : ratioExp h k i = l
  · rw [if_pos hi, if_pos ((ratioExp_phaseShift_eq_iff h k hk j l i).2 hi)]
  · rw [if_neg hi, if_neg fun h' => hi ((ratioExp_phaseShift_eq_iff h k hk j l i).1 h')]
    congr 1
    simp only [phaseShift]
    push_cast
    ring

theorem faceLeadConst_phaseShift {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : ℕ) (l β : ℝ) :
    faceLeadConst (phaseShift h k j) k (l + j / 2) β =
      Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) /
          ((multCount (ratioExp h k) l - 1).factorial : ℝ) *
        ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1 := by
  unfold faceLeadConst
  rw [multCount_phaseShift h k hk j l]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [ratioExp_phaseShift_eq_iff h k hk j l]

/-- The shifted face functional is the unshifted face integral with the shifted Gamma constant. -/
theorem amplitudeCoeff_phaseShift {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : ℕ) (l β : ℝ)
    (η : (Fin d → ℝ) → ℝ) :
    amplitudeCoeff (phaseShift h k j) k (l + j / 2) β η =
      Real.Gamma (l + j / 2) * β ^ (-(l + j / 2)) /
          ((multCount (ratioExp h k) l - 1).factorial : ℝ) *
        (∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1) *
        ∫ u in unitBox d, η (faceProj h k l u) * residualWeight h k l u := by
  unfold amplitudeCoeff
  rw [faceLeadConst_phaseShift h k hk j l β, faceProj_phaseShift h k hk j l,
    residualWeight_phaseShift h k hk j l]

/-- **Shifted-exponent term**: the `j`-th Taylor term of the phase expansion, in the chart variable
`N` (monomial parameter `N²`), normalised by the leading scale `N^{-2λ}(log N)^{m-1}`. -/
theorem shifted_term_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (η : (Fin (d + 1) → ℝ) → ℝ) (hη : Continuous η) (j : ℕ) :
    Tendsto (fun N : ℝ => N ^ j * (∫ x in unitBox (d + 1),
        η x * ((∏ i, x i ^ phaseShift h k j i) *
          Real.exp (-(β * N ^ 2 * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-(2 * l)) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (2 ^ (multCount (ratioExp h k) l - 1) *
        amplitudeCoeff (phaseShift h k j) k (l + j / 2) β η)) := by
  have hmin' : ∀ i, l + j / 2 ≤ ratioExp (phaseShift h k j) k i := fun i => by
    rw [ratioExp_phaseShift h k hk j i]
    linarith [hmin i]
  have hatt' : ∃ i, ratioExp (phaseShift h k j) k i = l + j / 2 := by
    obtain ⟨i, hi⟩ := hatt
    exact ⟨i, by rw [ratioExp_phaseShift h k hk j i, hi]⟩
  have hT := amplitude_tendsto d (phaseShift h k j) k hk (l + j / 2) β (by positivity) hβ hmin'
    hatt' η hη
  rw [multCount_phaseShift h k hk j l] at hT
  have hS := tendsto_powLog_comp_sq (fun T => ∫ x in unitBox (d + 1),
    η x * ((∏ i, x i ^ phaseShift h k j i) * Real.exp (-(β * T * ∏ i, x i ^ (2 * k i)))))
    (l + j / 2) _ (multCount (ratioExp h k) l - 1) hT
  refine hS.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have h1 : N ^ (-(2 * (l + j / 2))) = N ^ (-(2 * l)) * (N ^ j)⁻¹ := by
    rw [show -(2 * (l + j / 2)) = -(2 * l) + (-(j : ℝ)) by ring, Real.rpow_add hN0,
      Real.rpow_neg hN0.le (2 * l), Real.rpow_neg hN0.le (j : ℝ), Real.rpow_natCast]
  rw [h1]
  have hpow : N ^ (-(2 * l)) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hNj : N ^ j ≠ 0 := pow_ne_zero _ hN0.ne'
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  field_simp

end Laplace.Grammar
