/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedCovKOrder2

/-!
# eq:covK on E2's exact localised measure to second order

The rotated form of `LocalisedCovKOrder2`: for the centred quadratic probe on E2's rotated
separable oscillator with the isotropic localiser,

`t²Cov_loc[L∘A, ψ] = C_loc + C'_loc/t + O(t⁻²)`,
`C'_loc = ∑ᵢ (B̃ᵢᵢ c₂',ᵢ + 2b̃ᵢ c'ᵢ) + ∑_{i≠j} B̃ᵢⱼ cᵢcⱼ`,

the off-diagonal pairs contributing `2cᵢcⱼ/t` through the leading localised means (which carry the
anchor); and the expectation side `t⟨ψ⟩_loc = C_loc + (C'_loc/2)/t + O(t⁻²)`, so the exact
localised eq:covK is coefficientwise `−∂ₜ` of the exact localised expectation through second order.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- The leading localised mean of the `i`-th frame oscillator, `cᵢ = −αᵢ/(2λᵢ²) + g u₀ᵢ/λᵢ`. -/
noncomputable def locLeadMean (lam alpha : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ) (i : Fin d) : ℝ :=
  -alpha i / (2 * lam i ^ 2) + g * u₀ i / lam i

/-- The second-order pair coefficient on the localised measure: `2c₂',ᵢ` on the diagonal,
`2cᵢcⱼ` off it. -/
noncomputable def locCovKPairCoeff2 (lam alpha gamma : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ)
    (i j : Fin d) : ℝ :=
  if i = j then 2 * locSecondCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i)
  else 2 * (locLeadMean lam alpha g u₀ i * locLeadMean lam alpha g u₀ j)

/-- The expectation side's second-order pair coefficient: `c₂',ᵢ` on the diagonal, `cᵢcⱼ` off it. -/
noncomputable def locProbePairCoeff2 (lam alpha gamma : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ)
    (i j : Fin d) : ℝ :=
  if i = j then locSecondCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i)
  else locLeadMean lam alpha g u₀ i * locLeadMean lam alpha g u₀ j

theorem locCovKPairCoeff2_eq_two_mul (lam alpha gamma : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ)
    (i j : Fin d) :
    locCovKPairCoeff2 lam alpha gamma g u₀ i j = 2 *
      locProbePairCoeff2 lam alpha gamma g u₀ i j := by
  unfold locCovKPairCoeff2 locProbePairCoeff2
  split_ifs <;> ring

/-- `C'_loc` for the frame probe `ψ̃ = ∑ᵢⱼ (B̃ᵢⱼ/2)uᵢuⱼ + ∑ᵢ b̃ᵢuᵢ`. -/
noncomputable def locCovKCoeff2Sep (lam alpha gamma : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ)
    (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) : ℝ :=
  ∑ p : Fin d × Fin d, B p.1 p.2 / 2 * locCovKPairCoeff2 lam alpha gamma g u₀ p.1 p.2 +
    ∑ i, b i * (2 * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i))

/-- The expectation side's coefficient, `C'_loc/2`. -/
noncomputable def locProbeCoeff2 (lam alpha gamma : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ)
    (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) : ℝ :=
  ∑ p : Fin d × Fin d, B p.1 p.2 / 2 * locProbePairCoeff2 lam alpha gamma g u₀ p.1 p.2 +
    ∑ i, b i * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i)

/-- **The derivative reading coefficientwise on E2**: `C'_loc = 2 × (C'_loc/2)`. -/
theorem locCovKCoeff2Sep_eq_two_mul (lam alpha gamma : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ)
    (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) :
    locCovKCoeff2Sep lam alpha gamma g u₀ B b = 2 * locProbeCoeff2 lam alpha gamma g u₀ B b := by
  unfold locCovKCoeff2Sep locProbeCoeff2
  simp only [locCovKPairCoeff2_eq_two_mul, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun p _ => by ring
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- `C'_loc = ∑ᵢ (B̃ᵢᵢ c₂',ᵢ + 2b̃ᵢ c'ᵢ) + ∑_{i≠j} B̃ᵢⱼ cᵢcⱼ`. -/
theorem locCovKCoeff2Sep_eq (lam alpha gamma : Fin d → ℝ) (g : ℝ) (u₀ : Fin d → ℝ)
    (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) :
    locCovKCoeff2Sep lam alpha gamma g u₀ B b =
      ∑ i, (B i i * locSecondCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i) +
        2 * b i * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i)) +
      ∑ p : Fin d × Fin d, if p.1 = p.2 then 0 else
        B p.1 p.2 * (locLeadMean lam alpha g u₀ p.1 * locLeadMean lam alpha g u₀ p.2) := by
  unfold locCovKCoeff2Sep locCovKPairCoeff2
  have hsplit : ∀ p : Fin d × Fin d, B p.1 p.2 / 2 * (if p.1 = p.2 then
      2 * locSecondCoeff2 (lam p.1) (alpha p.1) (gamma p.1) g (u₀ p.1)
      else 2 * (locLeadMean lam alpha g u₀ p.1 * locLeadMean lam alpha g u₀ p.2)) =
      (if p.1 = p.2 then B p.1 p.2 * locSecondCoeff2 (lam p.1) (alpha p.1) (gamma p.1) g (u₀ p.1)
        else 0) +
      (if p.1 = p.2 then 0 else
        B p.1 p.2 * (locLeadMean lam alpha g u₀ p.1 * locLeadMean lam alpha g u₀ p.2)) := by
    intro p
    split_ifs <;> ring
  simp only [hsplit, Finset.sum_add_distrib]
  have hdiag : ∑ p : Fin d × Fin d, (if p.1 = p.2 then
      B p.1 p.2 * locSecondCoeff2 (lam p.1) (alpha p.1) (gamma p.1) g (u₀ p.1) else 0) =
      ∑ i, B i i * locSecondCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hdiag]
  have e : ∀ i, b i * (2 * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i)) =
      2 * b i * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (u₀ i) := fun i => by ring
  simp only [e]
  ring

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-! ### A. The pair covariances to second order -/

theorem localisedCovK_frame_sq_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (i : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
        1 / lam i - 2 * locSecondCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedCovK_sq_order2_rate (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedCovK_frame_coord hlam hgamma hdisc hQ c w₀ hg ht0 i 2]
  exact h ht

theorem localisedCovK_frame_lin_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (i : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) -
        locLeadMean lam alpha g (affineFrame Q c w₀) i -
        2 * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t| ≤
          K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedCovK_lin_order2_rate (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e := localisedCovK_frame_coord hlam hgamma hdisc hQ c w₀ hg ht0 i 1
  simp only [pow_one] at e
  rw [e]
  exact h ht

/-- **The off-diagonal pairs on the localised measure at second order**:
`|t²Cov_loc[L∘A, uᵢuⱼ] − 2cᵢcⱼ/t| ≤
  K/t²` for `i ≠ j` — the product of the leading localised means. -/
theorem localisedCovK_frame_offdiag_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {i j : Fin d} (hij : i ≠ j) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w i * affineFrame Q c w j) -
        2 * (locLeadMean lam alpha g (affineFrame Q c w₀) i *
          locLeadMean lam alpha g (affineFrame Q c w₀) j) / t| ≤ K / t ^ 2 := by
  obtain ⟨Ki, Ti, hKi, hTi, hi⟩ := locMean_loc_leading (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  obtain ⟨Kj, Tj, hKj, hTj, hj⟩ := locMean_loc_leading (hlam j) (hgamma j) (hdisc j) hg
    (x₀ := affineFrame Q c w₀ j)
  obtain ⟨Li, Si, hLi, hSi, gi⟩ := localisedCovK_lin_rate (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  obtain ⟨Lj, Sj, hLj, hSj, gj⟩ := localisedCovK_lin_rate (hlam j) (hgamma j) (hdisc j) hg
    (x₀ := affineFrame Q c w₀ j)
  set ci := locLeadMean lam alpha g (affineFrame Q c w₀) i with hci
  set cj := locLeadMean lam alpha g (affineFrame Q c w₀) j with hcj
  have hci' : ci = -alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i := rfl
  have hcj' : cj = -alpha j / (2 * lam j ^ 2) + g * affineFrame Q c w₀ j / lam j := rfl
  refine ⟨(Kj * (|ci| + Li) + |cj| * Li) + (Ki * (|cj| + Lj) + |ci| * Lj), Ti + Tj + Si + Sj,
    by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [localisedCovK_frame_pair hlam hgamma hdisc hQ c w₀ hg ht0 hij]
  set Mj := _root_.Laplace.gibbsExpectation
    (locPotential1 (lam j) (alpha j) (gamma j) g (affineFrame Q c w₀ j) t) t (fun x => x) with hMj
  set Mi := _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => x) with hMi
  set Ci := _root_.Laplace.gibbsCov
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
    (anharmonicPotential (lam i) (alpha i) (gamma i)) (fun x => x) with hCi
  set Cj := _root_.Laplace.gibbsCov
    (locPotential1 (lam j) (alpha j) (gamma j) g (affineFrame Q c w₀ j) t) t
    (anharmonicPotential (lam j) (alpha j) (gamma j)) (fun x => x) with hCj
  have ej : |t * Mj - cj| ≤ Kj / t := by rw [hcj']; exact hj (t := t) (by linarith)
  have ei : |t * Mi - ci| ≤ Ki / t := by rw [hci']; exact hi (t := t) (by linarith)
  have fi : |t ^ 2 * Ci - ci| ≤ Li / t := by rw [hci']; exact gi (t := t) (by linarith)
  have fj : |t ^ 2 * Cj - cj| ≤ Lj / t := by rw [hcj']; exact gj (t := t) (by linarith)
  have p1 := prod_rate t (t * Mj) (t ^ 2 * Ci) cj ci Kj Li ht1 hKj hLi ej fi
  have p2 := prod_rate t (t * Mi) (t ^ 2 * Cj) ci cj Ki Lj ht1 hKi hLj ei fj
  have key : t ^ 2 * (Mj * Ci + Mi * Cj) - 2 * (ci * cj) / t =
      ((t * Mj) * (t ^ 2 * Ci) - cj * ci) / t + ((t * Mi) * (t ^ 2 * Cj) - ci * cj) / t := by
    field_simp
    ring
  rw [key]
  calc _ ≤ |((t * Mj) * (t ^ 2 * Ci) - cj * ci) / t| + |((t * Mi) * (t ^ 2 * Cj) - ci * cj) / t| :=
        abs_add_le _ _
    _ ≤ (Kj * (|ci| + Li) + |cj| * Li) / t / t + (Ki * (|cj| + Lj) + |ci| * Lj) / t / t := by
        rw [abs_div, abs_div, abs_of_pos ht0]
        gcongr
    _ = _ := by ring

/-- The pair covariances at second order, unified. -/
theorem localisedCovK_frame_pair_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (i j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w i * affineFrame Q c w j) -
        (if i = j then 1 / lam i else 0) -
        locCovKPairCoeff2 lam alpha gamma g (affineFrame Q c w₀) i j / t| ≤ K / t ^ 2 := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨K, T, hK, hT, h⟩ := localisedCovK_frame_sq_order2_rate hlam hgamma hdisc hQ c w₀ hg i
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    rw [if_pos rfl, locCovKPairCoeff2, if_pos rfl]
    have := h ht
    simpa only [sq] using this
  · obtain ⟨K, T, hK, hT, h⟩ :=
      localisedCovK_frame_offdiag_order2_rate hlam hgamma hdisc hQ c w₀ hg hij
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    rw [if_neg hij, sub_zero, locCovKPairCoeff2, if_neg hij]
    exact h ht

/-! ### B. eq:covK on E2's exact localised measure to second order -/

theorem localisedCovK_frame_quadratic_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
            ∑ i, b i * affineFrame Q c w i) -
        ∑ i, (B i i / (2 * lam i) + b i * locLeadMean lam alpha g (affineFrame Q c w₀) i) -
        locCovKCoeff2Sep lam alpha gamma g (affineFrame Q c w₀) B b / t| ≤ K / t ^ 2 := by
  obtain ⟨Kp, Tp, hKp, hTp, hp⟩ := sum_rate_div_sq (fun p : Fin d × Fin d => B p.1 p.2 / 2)
    (fun p t => t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma)
      (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) -
      (if p.1 = p.2 then 1 / lam p.1 else 0) -
      locCovKPairCoeff2 lam alpha gamma g (affineFrame Q c w₀) p.1 p.2 / t)
    (fun p => localisedCovK_frame_pair_order2_rate hlam hgamma hdisc hQ c w₀ hg p.1 p.2)
  obtain ⟨Kl, Tl, hKl, hTl, hl⟩ := sum_rate_div_sq (fun i => b i)
    (fun i t => t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) -
      locLeadMean lam alpha g (affineFrame Q c w₀) i -
      2 * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t)
    (fun i => localisedCovK_frame_lin_order2_rate hlam hgamma hdisc hQ c w₀ hg i)
  refine ⟨Kp + Kl, Tp + Tl, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hdiag : ∑ p : Fin d × Fin d, B p.1 p.2 / 2 * (if p.1 = p.2 then 1 / lam p.1 else 0) =
      ∑ i, B i i / (2 * lam i) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
          ∑ i, b i * affineFrame Q c w i) -
      ∑ i, (B i i / (2 * lam i) + b i * locLeadMean lam alpha g (affineFrame Q c w₀) i) -
      locCovKCoeff2Sep lam alpha gamma g (affineFrame Q c w₀) B b / t =
      (∑ p : Fin d × Fin d, B p.1 p.2 / 2 *
        (t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) -
          (if p.1 = p.2 then 1 / lam p.1 else 0) -
          locCovKPairCoeff2 lam alpha gamma g (affineFrame Q c w₀) p.1 p.2 / t)) +
      ∑ i, b i * (t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) -
        locLeadMean lam alpha g (affineFrame Q c w₀) i -
        2 * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t) := by
    rw [localisedCovK_quadratic_split hlam hgamma hdisc hQ c w₀ hg ht0 B b]
    unfold locCovKCoeff2Sep
    simp only [mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
      add_div, Finset.sum_div]
    rw [hdiag]
    have e1 : ∀ p : Fin d × Fin d, B p.1 p.2 / 2 *
        (t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2)) =
        t ^ 2 * (B p.1 p.2 / 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2)) := fun p => by ring
    have e2 : ∀ i, b i * (t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t)
        t (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)) =
        t ^ 2 * (b i * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)) :=
      fun i => by ring
    have e3 : ∀ p : Fin d × Fin d, B p.1 p.2 / 2 *
        (locCovKPairCoeff2 lam alpha gamma g (affineFrame Q c w₀) p.1 p.2 / t) =
        B p.1 p.2 / 2 * locCovKPairCoeff2 lam alpha gamma g (affineFrame Q c w₀) p.1 p.2 / t :=
      fun p => by ring
    have e4 : ∀ i, b i * (2 * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) /
        t) = b i * (2 * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t :=
      fun i => by ring
    simp only [e1, e2, e3, e4, ← Finset.mul_sum, ← Finset.sum_div]
    ring
  rw [key]
  calc _ ≤ _ + _ := abs_add_le _ _
    _ ≤ Kp / t ^ 2 + Kl / t ^ 2 :=
        add_le_add (hp (t := t) (by linarith)) (hl (t := t) (by linarith))
    _ = _ := by ring

/-- **eq:covK on E2's exact localised measure to second order** (ambient probe):
`|t²Cov_loc[L∘A, ψ] − C_loc − C'_loc/t| ≤ K/t²`, `C'_loc = ∑ᵢ (B̃ᵢᵢ c₂',ᵢ + 2b̃ᵢ c'ᵢ) +
  ∑_{i≠j} B̃ᵢⱼ cᵢcⱼ`. -/
theorem localisedRotatedAnharmonic_covK_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) -
        ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) +
          (Qᵀ *ᵥ b) i * locLeadMean lam alpha g (affineFrame Q c w₀) i) -
        locCovKCoeff2Sep lam alpha gamma g (affineFrame Q c w₀) (fun i j => (Qᵀ * B * Q) i j)
          (Qᵀ *ᵥ b) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedCovK_frame_quadratic_order2_rate hlam hgamma hdisc hQ c w₀
    hg (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have hprobe : (fun w : Fin d → ℝ => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      fun w => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
        ∑ i, (Qᵀ *ᵥ b) i * affineFrame Q c w i :=
    funext (probe_affineFrame hQ c B b)
  rw [hprobe]
  exact h ht

/-! ### C. The expectation side: `t⟨ψ⟩_loc = C_loc + (C'_loc/2)/t + O(t⁻²)` -/

omit hlam hgamma hdisc in
/-- The rotation step for expectations. -/
theorem localisedRotated_gibbsExpectation_eq (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (t : ℝ)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotated Q c ψ) =
      gibbsExpectation (separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)) t
        ψ := by
  rw [localisedRotatedAnharmonic_eq_rotated_locFamily hQ c w₀ t]
  exact gibbsExpectation_rotated_of_continuous hQ c (continuous_separablePotential_locFamily _ t)
    hψ t

/-- `⟨uᵢ^m⟩_loc = ⟨x^m⟩_loc,i`. -/
theorem localised_frame_coord_expectation (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) (i : Fin d) (m : ℕ) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i ^ m) =
      _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (fun x => x ^ m) := by
  have e : (fun w => affineFrame Q c w i ^ m) = rotated Q c (fun u : Fin d → ℝ => u i ^ m) := rfl
  rw [e, localisedRotated_gibbsExpectation_eq hQ c w₀ t (by fun_prop)]
  exact gibbsExpectation_coord_separable _ t
    (partitionFunction_locFamily_ne hlam hgamma hdisc hg _ ht) i (fun x => x ^ m)

/-- `⟨uᵢuⱼ⟩_loc = ⟨x⟩_loc,i ⟨x⟩_loc,j` for `i ≠ j` (the localised frame measure is a product). -/
theorem localised_frame_pair_expectation (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) {i j : Fin d} (hij : i ≠ j) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i * affineFrame Q c w j) =
      _root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => x) *
        _root_.Laplace.gibbsExpectation
          (locPotential1 (lam j) (alpha j) (gamma j) g (affineFrame Q c w₀ j) t) t
            (fun x => x) := by
  have e : (fun w => affineFrame Q c w i * affineFrame Q c w j) =
      rotated Q c (fun u : Fin d → ℝ => u i * u j) := rfl
  rw [e, localisedRotated_gibbsExpectation_eq hQ c w₀ t (by fun_prop)]
  exact gibbsExpectation_two_coord_separable _ t
    (partitionFunction_locFamily_ne hlam hgamma hdisc hg _ ht) hij (fun x => x) (fun x => x)

/-- The quadratic frame probe's expectation splits into pairs and coordinates. -/
theorem localised_quadratic_expectation_split (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
          ∑ i, b i * affineFrame Q c w i) =
      ∑ p : Fin d × Fin d, B p.1 p.2 / 2 *
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) +
      ∑ i, b i * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i) := by
  set u₀ := affineFrame Q c w₀ with hu₀
  have hψ : Continuous fun u : Fin d → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i :=
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop).add
      (continuous_finsetSum _ fun i _ => by fun_prop)
  have e : (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
      ∑ i, b i * affineFrame Q c w i) =
      rotated Q c (fun u : Fin d → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) := rfl
  have hp' : ∀ p : Fin d × Fin d,
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) =
      gibbsExpectation (separablePotential (locFamily lam alpha gamma g u₀ t)) t
        (fun u => u p.1 * u p.2) := fun p =>
    localisedRotated_gibbsExpectation_eq hQ c w₀ t (ψ := fun u => u p.1 * u p.2) (by fun_prop)
  have hc' : ∀ i, gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i) =
      gibbsExpectation (separablePotential (locFamily lam alpha gamma g u₀ t)) t (fun u => u i) :=
    fun i => localisedRotated_gibbsExpectation_eq hQ c w₀ t (ψ := fun u => u i) (by fun_prop)
  rw [e, localisedRotated_gibbsExpectation_eq hQ c w₀ t hψ]
  simp only [hp', hc']
  set L := separablePotential (locFamily lam alpha gamma g u₀ t) with hL
  have hcm : ∀ i j, Integrable (fun u : Fin d → ℝ => u i * u j * Real.exp (-(t * L u))) :=
    fun i j => integrable_locFamily_of_integrable hg u₀ ht (by fun_prop)
      (integrable_coord_mul_separableAnharmonic hlam hgamma hdisc ht i j)
  have hc : ∀ i, Integrable (fun u : Fin d → ℝ => u i * Real.exp (-(t * L u))) :=
    fun i => integrable_locFamily_of_integrable hg u₀ ht (by fun_prop)
      (integrable_coord_separableAnharmonic hlam hgamma hdisc ht i)
  have hφP : ∀ p : Fin d × Fin d, Integrable (fun u : Fin d → ℝ =>
      B p.1 p.2 / 2 * (u p.1 * u p.2) * Real.exp (-(t * L u))) := fun p =>
    ((hcm p.1 p.2).const_mul (B p.1 p.2 / 2)).congr (Eventually.of_forall fun u => by ring)
  have hφQ : ∀ i, Integrable (fun u : Fin d → ℝ => b i * u i * Real.exp (-(t * L u))) := fun i =>
    ((hc i).const_mul (b i)).congr (Eventually.of_forall fun u => by ring)
  have hP : Integrable (fun u : Fin d → ℝ =>
      (∑ p : Fin d × Fin d, B p.1 p.2 / 2 * (u p.1 * u p.2)) * Real.exp (-(t * L u))) :=
    (integrable_finsetSum (Finset.univ : Finset (Fin d × Fin d)) fun p _ => hφP p).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hQ' : Integrable (fun u : Fin d → ℝ => (∑ i, b i * u i) * Real.exp (-(t * L u))) :=
    (integrable_finsetSum Finset.univ fun i _ => hφQ i).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hprobe : (fun u : Fin d → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) =
      fun u => (∑ p : Fin d × Fin d, B p.1 p.2 / 2 * (u p.1 * u p.2)) + ∑ i, b i * u i := by
    funext u
    congr 1
    exact (Fintype.sum_prod_type' fun a c => B a c / 2 * (u a * u c)).symm
  rw [hprobe, gibbsExpectation_add_of_integrable L t _ _ hP hQ',
    gibbsExpectation_finsetSum L t Finset.univ _ (fun p _ => hφP p),
    gibbsExpectation_finsetSum L t Finset.univ _ (fun i _ => hφQ i)]
  congr 1
  · exact Finset.sum_congr rfl fun p _ => by rw [gibbsExpectation_const_mul]
  · exact Finset.sum_congr rfl fun i _ => by rw [gibbsExpectation_const_mul]

/-- `|t⟨uᵢ⟩_loc − cᵢ − c'ᵢ/t| ≤ K/t²`. -/
theorem localised_frame_lin_expectation_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (i : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i) - locLeadMean lam alpha g (affineFrame Q c w₀) i -
        meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := locMean_loc_order2 (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e := localised_frame_coord_expectation hlam hgamma hdisc hQ c w₀ hg ht0 i 1
  simp only [pow_one] at e
  rw [e]
  exact h ht

/-- `|t⟨uᵢuⱼ⟩_loc − (if i = j then 1/λᵢ else 0) − (if i = j then c₂',ᵢ else cᵢcⱼ)/t| ≤ K/t²`. -/
theorem localised_frame_pair_expectation_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (i j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i * affineFrame Q c w j) -
        (if i = j then 1 / lam i else 0) -
        locProbePairCoeff2 lam alpha gamma g (affineFrame Q c w₀) i j / t| ≤ K / t ^ 2 := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨K, T, hK, hT, h⟩ := locSecondMoment_loc_rate2 (hlam i) (hgamma i) (hdisc i) hg
      (x₀ := affineFrame Q c w₀ i)
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    have ht0 : 0 < t := by linarith
    rw [if_pos rfl, locProbePairCoeff2, if_pos rfl]
    have e := localised_frame_coord_expectation hlam hgamma hdisc hQ c w₀ hg ht0 i 2
    have e' : (fun w => affineFrame Q c w i * affineFrame Q c w i) =
        fun w => affineFrame Q c w i ^ 2 := by funext w; ring
    rw [e', e]
    exact h ht
  · obtain ⟨Ki, Ti, hKi, hTi, hi⟩ := locMean_loc_leading (hlam i) (hgamma i) (hdisc i) hg
      (x₀ := affineFrame Q c w₀ i)
    obtain ⟨Kj, Tj, hKj, hTj, hj⟩ := locMean_loc_leading (hlam j) (hgamma j) (hdisc j) hg
      (x₀ := affineFrame Q c w₀ j)
    set ci := locLeadMean lam alpha g (affineFrame Q c w₀) i with hci
    set cj := locLeadMean lam alpha g (affineFrame Q c w₀) j with hcj
    have hci' : ci = -alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i := rfl
    have hcj' : cj = -alpha j / (2 * lam j ^ 2) + g * affineFrame Q c w₀ j / lam j := rfl
    refine ⟨Ki * (|cj| + Kj) + |ci| * Kj, Ti + Tj, by positivity, by linarith, fun {t} ht => ?_⟩
    have ht1 : 1 ≤ t := by linarith
    have ht0 : 0 < t := by linarith
    rw [if_neg hij, sub_zero, locProbePairCoeff2, if_neg hij,
      localised_frame_pair_expectation hlam hgamma hdisc hQ c w₀ hg ht0 hij]
    set Mi := _root_.Laplace.gibbsExpectation
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => x)
      with hMi
    set Mj := _root_.Laplace.gibbsExpectation
      (locPotential1 (lam j) (alpha j) (gamma j) g (affineFrame Q c w₀ j) t) t (fun x => x)
      with hMj
    have ei : |t * Mi - ci| ≤ Ki / t := by rw [hci']; exact hi (t := t) (by linarith)
    have ej : |t * Mj - cj| ≤ Kj / t := by rw [hcj']; exact hj (t := t) (by linarith)
    have p := prod_rate t (t * Mi) (t * Mj) ci cj Ki Kj ht1 hKi hKj ei ej
    have key : t * (Mi * Mj) - ci * cj / t = ((t * Mi) * (t * Mj) - ci * cj) / t := by
      field_simp
    rw [key, abs_div, abs_of_pos ht0]
    calc |(t * Mi) * (t * Mj) - ci * cj| / t ≤ (Ki * (|cj| + Kj) + |ci| * Kj) / t / t :=
          div_le_div_of_nonneg_right p ht0.le
      _ = _ := by ring

/-- **The expectation side to second order**: `|t⟨ψ⟩_loc − C_loc − (C'_loc/2)/t| ≤ K/t²`. -/
theorem localised_frame_quadratic_expectation_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (B : Fin d → Fin d → ℝ) (b : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
            ∑ i, b i * affineFrame Q c w i) -
        ∑ i, (B i i / (2 * lam i) + b i * locLeadMean lam alpha g (affineFrame Q c w₀) i) -
        locProbeCoeff2 lam alpha gamma g (affineFrame Q c w₀) B b / t| ≤ K / t ^ 2 := by
  obtain ⟨Kp, Tp, hKp, hTp, hp⟩ := sum_rate_div_sq (fun p : Fin d × Fin d => B p.1 p.2 / 2)
    (fun p t => t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) -
      (if p.1 = p.2 then 1 / lam p.1 else 0) -
      locProbePairCoeff2 lam alpha gamma g (affineFrame Q c w₀) p.1 p.2 / t)
    (fun p => localised_frame_pair_expectation_order2_rate hlam hgamma hdisc hQ c w₀ hg p.1 p.2)
  obtain ⟨Kl, Tl, hKl, hTl, hl⟩ := sum_rate_div_sq (fun i => b i)
    (fun i t => t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (fun w => affineFrame Q c w i) - locLeadMean lam alpha g (affineFrame Q c w₀) i -
      meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t)
    (fun i => localised_frame_lin_expectation_order2_rate hlam hgamma hdisc hQ c w₀ hg i)
  refine ⟨Kp + Kl, Tp + Tl, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hdiag : ∑ p : Fin d × Fin d, B p.1 p.2 / 2 * (if p.1 = p.2 then 1 / lam p.1 else 0) =
      ∑ i, B i i / (2 * lam i) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
          ∑ i, b i * affineFrame Q c w i) -
      ∑ i, (B i i / (2 * lam i) + b i * locLeadMean lam alpha g (affineFrame Q c w₀) i) -
      locProbeCoeff2 lam alpha gamma g (affineFrame Q c w₀) B b / t =
      (∑ p : Fin d × Fin d, B p.1 p.2 / 2 *
        (t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2) -
          (if p.1 = p.2 then 1 / lam p.1 else 0) -
          locProbePairCoeff2 lam alpha gamma g (affineFrame Q c w₀) p.1 p.2 / t)) +
      ∑ i, b i * (t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i) - locLeadMean lam alpha g (affineFrame Q c w₀) i -
        meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t) := by
    rw [localised_quadratic_expectation_split hlam hgamma hdisc hQ c w₀ hg ht0 B b]
    unfold locProbeCoeff2
    simp only [mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
      add_div, Finset.sum_div]
    rw [hdiag]
    have e1 : ∀ p : Fin d × Fin d, B p.1 p.2 / 2 *
        (t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2)) =
        t * (B p.1 p.2 / 2 * gibbsExpectation
          (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t)
          t (fun w => affineFrame Q c w p.1 * affineFrame Q c w p.2)) := fun p => by ring
    have e2 : ∀ i, b i * (t * gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t)
        t (fun w => affineFrame Q c w i)) =
        t * (b i * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i)) := fun i => by ring
    have e3 : ∀ p : Fin d × Fin d, B p.1 p.2 / 2 *
        (locProbePairCoeff2 lam alpha gamma g (affineFrame Q c w₀) p.1 p.2 / t) =
        B p.1 p.2 / 2 * locProbePairCoeff2 lam alpha gamma g (affineFrame Q c w₀) p.1 p.2 / t :=
      fun p => by ring
    have e4 : ∀ i, b i * (meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t) =
        b i * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t :=
      fun i => by ring
    simp only [e1, e2, e3, e4, ← Finset.mul_sum, ← Finset.sum_div]
    ring
  rw [key]
  calc _ ≤ _ + _ := abs_add_le _ _
    _ ≤ Kp / t ^ 2 + Kl / t ^ 2 :=
        add_le_add (hp (t := t) (by linarith)) (hl (t := t) (by linarith))
    _ = _ := by ring

/-- **The derivative reading coefficientwise on E2** (ambient probe): `t⟨ψ⟩_loc = C_loc +
(C'_loc/2)/t + O(t⁻²)` with the same `C_loc`,
  `C'_loc` as `localisedRotatedAnharmonic_covK_order2_rate`
(`locCovKCoeff2Sep_eq_two_mul`): the exact localised eq:covK is `−∂ₜ` of the exact localised
expectation coefficient by coefficient through second order. -/
theorem localisedRotatedAnharmonic_probe_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) -
        ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) +
          (Qᵀ *ᵥ b) i * locLeadMean lam alpha g (affineFrame Q c w₀) i) -
        (locCovKCoeff2Sep lam alpha gamma g (affineFrame Q c w₀) (fun i j => (Qᵀ * B * Q) i j)
          (Qᵀ *ᵥ b) / 2) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localised_frame_quadratic_expectation_order2_rate hlam hgamma hdisc
    hQ c w₀ hg (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have hprobe : (fun w : Fin d → ℝ => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      fun w => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
        ∑ i, (Qᵀ *ᵥ b) i * affineFrame Q c w i :=
    funext (probe_affineFrame hQ c B b)
  rw [hprobe, locCovKCoeff2Sep_eq_two_mul, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  exact h ht

end Multi

end Laplace.Multi
