/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovKOrder2
import Laplace.Multi.CovKRateSeparable
import Laplace.Multi.LocalisedAnharmonicSharp

/-!
# eq:covK to second order for E2's rotated oscillator

`CovKRateSeparable` certified eq:covK for the separable and rotated oscillators with an `O(1/t)`
rate on `t²Cov[L, ψ]`; `CovKOrder2` identified the `1/t` coefficient per eigendirection. Here the
two are combined: for the frame probe `ψ̃ = ∑ᵢⱼ (B̃ᵢⱼ/2)uᵢuⱼ + ∑ᵢ b̃ᵢuᵢ`,

`t²Cov[L, ψ̃] = ∑ᵢ (B̃ᵢᵢ/(2λᵢ) − b̃ᵢαᵢ/(2λᵢ²)) + C'/t + O(t⁻²)`,
`C' = ∑ᵢ (B̃ᵢᵢ C'_sq,i/2 + b̃ᵢ C'_lin,i) + ∑_{i≠j} B̃ᵢⱼ aᵢaⱼ`, `aᵢ = −αᵢ/(2λᵢ²)`.

Unlike the leading order, the off-diagonal part of the probe contributes at second order,
through the product of the leading mean shifts: for `i ≠ j`, `t²Cov[L, uᵢuⱼ] = 2aᵢaⱼ/t + O(t⁻²)`.
The ambient form against `covKFormula` and the relative form follow.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

/-! ### Abstract bookkeeping -/

section Abstract

/-- A product of two leading-order rates: `|XY − ab| ≤ (K_X(|b| + K_Y) + |a|K_Y)/t`. -/
theorem prod_rate (t X Y a b K_X K_Y : ℝ) (ht1 : 1 ≤ t) (hK_X : 0 ≤ K_X) (hK_Y : 0 ≤ K_Y)
    (hX : |X - a| ≤ K_X / t) (hY : |Y - b| ≤ K_Y / t) :
    |X * Y - a * b| ≤ (K_X * (|b| + K_Y) + |a| * K_Y) / t := by
  have ht0 : 0 < t := by linarith
  have hYb : |Y| ≤ |b| + K_Y := by
    calc |Y| = |b + (Y - b)| := by ring_nf
      _ ≤ |b| + |Y - b| := abs_add_le _ _
      _ ≤ |b| + K_Y / t := add_le_add le_rfl hY
      _ ≤ |b| + K_Y := add_le_add le_rfl (div_le_self hK_Y ht1)
  have key : X * Y - a * b = (X - a) * Y + a * (Y - b) := by ring
  rw [key]
  calc |(X - a) * Y + a * (Y - b)| ≤ |(X - a) * Y| + |a * (Y - b)| := abs_add_le _ _
    _ = |X - a| * |Y| + |a| * |Y - b| := by rw [abs_mul, abs_mul]
    _ ≤ K_X / t * (|b| + K_Y) + |a| * (K_Y / t) := by gcongr
    _ = (K_X * (|b| + K_Y) + |a| * K_Y) / t := by ring

end Abstract

/-! ### The separable oscillator -/

section Separable

variable {ι : Type*} [Fintype ι] {lam alpha gamma : ι → ℝ}

/-- `|t²Cov[L, uᵢ²] − 1/λᵢ − C'_sq,i/t| ≤ K/t²`. -/
theorem covK_separable_sq_order2_rate (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i ^ 2) - 1 / lam i -
        covKCoeff2Sq (lam i) (alpha i) (gamma i) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := covK_sq_order2_rate (hlam i) (hgamma i) (hdisc i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [gibbsCov_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht0 i 2]
  exact h ht

/-- `|t²Cov[L, uᵢ] − aᵢ − C'_lin,i/t| ≤ K/t²`. -/
theorem covK_separable_lin_order2_rate (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i) - (-alpha i / (2 * lam i ^ 2)) -
        covKCoeff2Lin (lam i) (alpha i) (gamma i) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := covK_lin_order2_rate (hlam i) (hgamma i) (hdisc i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e := gibbsCov_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht0 i 1
  simp only [pow_one] at e
  rw [e, show -alpha i / (2 * lam i ^ 2) = -(alpha i / (2 * lam i ^ 2)) by ring, sub_neg_eq_add]
  exact h ht

/-- **The off-diagonal pair covariance to second order**: for `i ≠ j`,
`|t²Cov[L, uᵢuⱼ] − 2aᵢaⱼ/t| ≤ K/t²`, `aᵢ = −αᵢ/(2λᵢ²)`, from the exact identity
`Cov[L, uᵢuⱼ] = ⟨xⱼ⟩Cov_i[ℓᵢ, x] + ⟨xᵢ⟩Cov_j[ℓⱼ, x]`. -/
theorem covK_separable_offdiag_order2_rate (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {i j : ι} (hij : i ≠ j) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i * u j) -
        2 * ((-alpha i / (2 * lam i ^ 2)) * (-alpha j / (2 * lam j ^ 2))) / t| ≤ K / t ^ 2 := by
  obtain ⟨Ki, Ti, hKi, hTi, hi⟩ := mean_anharmonic_O2_rate (hlam i) (hgamma i) (hdisc i)
  obtain ⟨Kj, Tj, hKj, hTj, hj⟩ := mean_anharmonic_O2_rate (hlam j) (hgamma j) (hdisc j)
  obtain ⟨Li, Si, hLi, hSi, gi⟩ := covK_lin_rate (hlam i) (hgamma i) (hdisc i)
  obtain ⟨Lj, Sj, hLj, hSj, gj⟩ := covK_lin_rate (hlam j) (hgamma j) (hdisc j)
  set ai := -alpha i / (2 * lam i ^ 2) with hai
  set aj := -alpha j / (2 * lam j ^ 2) with haj
  refine ⟨(Kj * (|ai| + Li) + |aj| * Li) + (Ki * (|aj| + Lj) + |ai| * Lj), Ti + Tj + Si + Sj,
    by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [gibbsCov_energy_pair_separableAnharmonic hlam hgamma hdisc ht0 hij]
  set Mj := _root_.Laplace.gibbsExpectation (anharmonicPotential (lam j) (alpha j) (gamma j)) t
    (fun x => x) with hMj
  set Mi := _root_.Laplace.gibbsExpectation (anharmonicPotential (lam i) (alpha i) (gamma i)) t
    (fun x => x) with hMi
  set Ci := _root_.Laplace.gibbsCov (anharmonicPotential (lam i) (alpha i) (gamma i)) t
    (anharmonicPotential (lam i) (alpha i) (gamma i)) (fun x => x) with hCi
  set Cj := _root_.Laplace.gibbsCov (anharmonicPotential (lam j) (alpha j) (gamma j)) t
    (anharmonicPotential (lam j) (alpha j) (gamma j)) (fun x => x) with hCj
  have ej : |t * Mj - aj| ≤ Kj / t := hj (t := t) (by linarith)
  have ei : |t * Mi - ai| ≤ Ki / t := hi (t := t) (by linarith)
  have fi : |t ^ 2 * Ci - ai| ≤ Li / t := by
    rw [show ai = -(alpha i / (2 * lam i ^ 2)) by rw [hai]; ring, sub_neg_eq_add]
    exact gi (t := t) (by linarith)
  have fj : |t ^ 2 * Cj - aj| ≤ Lj / t := by
    rw [show aj = -(alpha j / (2 * lam j ^ 2)) by rw [haj]; ring, sub_neg_eq_add]
    exact gj (t := t) (by linarith)
  have p1 := prod_rate t (t * Mj) (t ^ 2 * Ci) aj ai Kj Li ht1 hKj hLi ej fi
  have p2 := prod_rate t (t * Mi) (t ^ 2 * Cj) ai aj Ki Lj ht1 hKi hLj ei fj
  have key : t ^ 2 * (Mj * Ci + Mi * Cj) - 2 * (ai * aj) / t =
      ((t * Mj) * (t ^ 2 * Ci) - aj * ai) / t + ((t * Mi) * (t ^ 2 * Cj) - ai * aj) / t := by
    field_simp
    ring
  rw [key]
  calc _ ≤ |((t * Mj) * (t ^ 2 * Ci) - aj * ai) / t| + |((t * Mi) * (t ^ 2 * Cj) - ai * aj) / t| :=
        abs_add_le _ _
    _ ≤ (Kj * (|ai| + Li) + |aj| * Li) / t / t + (Ki * (|aj| + Lj) + |ai| * Lj) / t / t := by
        rw [abs_div, abs_div, abs_of_pos ht0]
        gcongr
    _ = _ := by ring

/-- The second-order coefficient of the pair `uᵢuⱼ`: `C'_sq,i` on the diagonal, `2aᵢaⱼ` off it. -/
noncomputable def covKPairCoeff2 (lam alpha gamma : ι → ℝ) [DecidableEq ι] (i j : ι) : ℝ :=
  if i = j then covKCoeff2Sq (lam i) (alpha i) (gamma i)
  else 2 * ((-alpha i / (2 * lam i ^ 2)) * (-alpha j / (2 * lam j ^ 2)))

/-- **The pair covariances to second order**: for all `i, j`,
`|t²Cov[L, uᵢuⱼ] − (if i = j then 1/λᵢ else 0) − covKPairCoeff2 i j/t| ≤ K/t²`. -/
theorem covK_separable_pair_order2_rate [DecidableEq ι] (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i j : ι) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i * u j) -
        (if i = j then 1 / lam i else 0) - covKPairCoeff2 lam alpha gamma i j / t| ≤ K / t ^ 2 := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨K, T, hK, hT, h⟩ := covK_separable_sq_order2_rate hlam hgamma hdisc i
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    rw [if_pos rfl, covKPairCoeff2, if_pos rfl]
    have := h ht
    simpa only [sq] using this
  · obtain ⟨K, T, hK, hT, h⟩ := covK_separable_offdiag_order2_rate hlam hgamma hdisc hij
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    rw [if_neg hij, sub_zero, covKPairCoeff2, if_neg hij]
    exact h ht

/-- **The second-order coefficient of eq:covK for the frame probe**
`ψ̃ = ∑ᵢⱼ (B̃ᵢⱼ/2)uᵢuⱼ + ∑ᵢ b̃ᵢuᵢ`. -/
noncomputable def covKCoeff2Sep (lam alpha gamma : ι → ℝ) [DecidableEq ι] (B : ι → ι → ℝ)
    (b : ι → ℝ) : ℝ :=
  ∑ p : ι × ι, B p.1 p.2 / 2 * covKPairCoeff2 lam alpha gamma p.1 p.2 +
    ∑ i, b i * covKCoeff2Lin (lam i) (alpha i) (gamma i)

/-- `C' = ∑ᵢ (B̃ᵢᵢ C'_sq,i/2 + b̃ᵢ C'_lin,i) + ∑_{i≠j} B̃ᵢⱼ aᵢaⱼ`: the diagonal part is the
eigendirection-wise coefficient, the off-diagonal part the product of the leading mean shifts. At
leading order only the eigenframe-diagonal part of the quadratic component survives
(`covK_separable_quadratic`); at second order the off-diagonal components *can* contribute, and
the coefficient differs from the diagonal-only one precisely when `∑_{i≠j} B̃ᵢⱼaᵢaⱼ ≠ 0`. -/
theorem covKCoeff2Sep_eq [DecidableEq ι] (B : ι → ι → ℝ) (b : ι → ℝ) :
    covKCoeff2Sep lam alpha gamma B b =
      ∑ i, (B i i / 2 * covKCoeff2Sq (lam i) (alpha i) (gamma i) +
        b i * covKCoeff2Lin (lam i) (alpha i) (gamma i)) +
      ∑ p : ι × ι, if p.1 = p.2 then 0 else
        B p.1 p.2 * ((-alpha p.1 / (2 * lam p.1 ^ 2)) * (-alpha p.2 / (2 * lam p.2 ^ 2))) := by
  unfold covKCoeff2Sep covKPairCoeff2
  have hsplit : ∀ p : ι × ι, B p.1 p.2 / 2 * (if p.1 = p.2 then covKCoeff2Sq (lam p.1) (alpha p.1)
      (gamma p.1) else 2 * ((-alpha p.1 / (2 * lam p.1 ^ 2)) * (-alpha p.2 / (2 * lam p.2 ^ 2)))) =
      (if p.1 = p.2 then B p.1 p.2 / 2 * covKCoeff2Sq (lam p.1) (alpha p.1) (gamma p.1) else 0) +
      (if p.1 = p.2 then 0 else
        B p.1 p.2 * ((-alpha p.1 / (2 * lam p.1 ^ 2)) * (-alpha p.2 / (2 * lam p.2 ^ 2)))) := by
    intro p
    split_ifs <;> ring
  simp only [hsplit, Finset.sum_add_distrib]
  have hdiag : ∑ p : ι × ι, (if p.1 = p.2 then B p.1 p.2 / 2 * covKCoeff2Sq (lam p.1) (alpha p.1)
      (gamma p.1) else 0) = ∑ i, B i i / 2 * covKCoeff2Sq (lam i) (alpha i) (gamma i) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hdiag]
  ring

/-- The off-diagonal part in closed form: `∑_{i≠j} B̃ᵢⱼaᵢaⱼ = aᵀB̃a − ∑ᵢ B̃ᵢᵢaᵢ²` (no order on `ι`,
no symmetry of `B̃` needed). -/
theorem covKCoeff2Sep_offdiag_eq [DecidableEq ι] (B : ι → ι → ℝ) (a : ι → ℝ) :
    (∑ p : ι × ι, if p.1 = p.2 then 0 else B p.1 p.2 * (a p.1 * a p.2)) =
      (∑ i, ∑ j, B i j * (a i * a j)) - ∑ i, B i i * a i ^ 2 := by
  have e : ∀ p : ι × ι, (if p.1 = p.2 then 0 else B p.1 p.2 * (a p.1 * a p.2)) =
      B p.1 p.2 * (a p.1 * a p.2) - (if p.1 = p.2 then B p.1 p.2 * (a p.1 * a p.2) else 0) := by
    intro p
    split_ifs <;> ring
  simp only [e, Finset.sum_sub_distrib]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **eq:covK to second order for the separable oscillator, general quadratic probe**:
`|t²Cov[L, ψ̃] − ∑ᵢ (B̃ᵢᵢ/(2λᵢ) − b̃ᵢαᵢ/(2λᵢ²)) − C'/t| ≤ K/t²`. -/
theorem covK_separable_quadratic_order2_rate [DecidableEq ι] (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
    (B : ι → ι → ℝ) (b : ι → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma)
        (fun u => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) -
        ∑ i, (B i i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)) -
        covKCoeff2Sep lam alpha gamma B b / t| ≤ K / t ^ 2 := by
  set L := separableAnharmonic lam alpha gamma with hL
  obtain ⟨Kp, Tp, hKp, hTp, hp⟩ := sum_rate_div_sq (fun p : ι × ι => B p.1 p.2 / 2)
    (fun p t => t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2) -
      (if p.1 = p.2 then 1 / lam p.1 else 0) - covKPairCoeff2 lam alpha gamma p.1 p.2 / t)
    (fun p => covK_separable_pair_order2_rate hlam hgamma hdisc p.1 p.2)
  obtain ⟨Kl, Tl, hKl, hTl, hl⟩ := sum_rate_div_sq (fun i => b i)
    (fun i t => t ^ 2 * gibbsCov L t L (fun u => u i) - (-alpha i / (2 * lam i ^ 2)) -
      covKCoeff2Lin (lam i) (alpha i) (gamma i) / t)
    (fun i => covK_separable_lin_order2_rate hlam hgamma hdisc i)
  refine ⟨Kp + Kl, Tp + Tl, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hdiag : ∑ p : ι × ι, B p.1 p.2 / 2 * (if p.1 = p.2 then 1 / lam p.1 else 0) =
      ∑ i, B i i / (2 * lam i) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : t ^ 2 * gibbsCov L t L (fun u => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) -
      ∑ i, (B i i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)) -
      covKCoeff2Sep lam alpha gamma B b / t =
      (∑ p : ι × ι, B p.1 p.2 / 2 * (t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2) -
        (if p.1 = p.2 then 1 / lam p.1 else 0) - covKPairCoeff2 lam alpha gamma p.1 p.2 / t)) +
      ∑ i, b i * (t ^ 2 * gibbsCov L t L (fun u => u i) - (-alpha i / (2 * lam i ^ 2)) -
        covKCoeff2Lin (lam i) (alpha i) (gamma i) / t) := by
    rw [gibbsCov_energy_quadratic_split hlam hgamma hdisc ht0 B b, ← hL]
    unfold covKCoeff2Sep
    simp only [mul_sub, Finset.sum_sub_distrib, mul_add, Finset.mul_sum, add_div, Finset.sum_div]
    rw [hdiag]
    have e1 : ∀ p : ι × ι, B p.1 p.2 / 2 * (t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2)) =
        t ^ 2 * (B p.1 p.2 / 2 * gibbsCov L t L (fun u => u p.1 * u p.2)) := fun p => by ring
    have e2 : ∀ i, b i * (t ^ 2 * gibbsCov L t L (fun u => u i)) =
        t ^ 2 * (b i * gibbsCov L t L (fun u => u i)) := fun i => by ring
    have e3 : ∀ p : ι × ι, B p.1 p.2 / 2 * (covKPairCoeff2 lam alpha gamma p.1 p.2 / t) =
        B p.1 p.2 / 2 * covKPairCoeff2 lam alpha gamma p.1 p.2 / t := fun p => by ring
    have e4 : ∀ i, b i * (covKCoeff2Lin (lam i) (alpha i) (gamma i) / t) =
        b i * covKCoeff2Lin (lam i) (alpha i) (gamma i) / t := fun i => by ring
    have e5 : ∀ i, b i * (-alpha i / (2 * lam i ^ 2)) = -(b i * alpha i / (2 * lam i ^ 2)) :=
      fun i => by ring
    simp only [e1, e2, e3, e4, e5, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    ring
  rw [key]
  calc _ ≤ _ + _ := abs_add_le _ _
    _ ≤ Kp / t ^ 2 + Kl / t ^ 2 :=
        add_le_add (hp (t := t) (by linarith)) (hl (t := t) (by linarith))
    _ = _ := by ring

end Separable

/-! ### E2: the rotated oscillator, ambient probe -/

section Rotated

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ}

/-- **eq:covK to second order in the note's frame**: for the ambient probe
`ψ(w) = ½(w − c)ᵀB(w − c) + bᵀ(w − c)`,
`|Cov[L∘A, ψ] − covKFormula t H T B b − C'(QᵀBQ, Qᵀb)/t³| ≤ K/t⁴`. -/
theorem covKFormula_rot_order2_rate (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) -
        covKFormula t (Q * diagonal lam * Qᵀ) (rotT Q alpha) B b -
        covKCoeff2Sep lam alpha gamma (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b) / t ^ 3| ≤
        K / t ^ 4 := by
  obtain ⟨K, T, hK, hT, h⟩ := covK_separable_quadratic_order2_rate hlam hgamma hdisc
    (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have htne := ht0.ne'
  have hlne : ∀ i, lam i ≠ 0 := fun i => (hlam i).ne'
  have hc := continuous_separableAnharmonic lam alpha gamma
  have hψ : Continuous fun u : Fin d → ℝ =>
      ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) + ∑ i, (Qᵀ *ᵥ b) i * u i :=
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop).add
      (continuous_finsetSum _ fun i _ => by fun_prop)
  have hrot := gibbsCov_rotated_of_continuous hQ c hc hc hψ t
  have hprobe : (fun w : Fin d → ℝ => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      rotated Q c (fun u => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) +
        ∑ i, (Qᵀ *ᵥ b) i * u i) :=
    funext (probe_affineFrame hQ c B b)
  have hcov : gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
      (rotatedAnharmonic Q c lam alpha gamma)
      (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) + ∑ i, (Qᵀ *ᵥ b) i * u i) := by
    rw [hprobe, ← hrot]
    rfl
  rw [hcov, covKFormula_rot hQ hlne alpha htne B b]
  set V := gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
    (fun u => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) + ∑ i, (Qᵀ *ᵥ b) i * u i) with hV
  set C := ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) - (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2)) with hC
  set C' := covKCoeff2Sep lam alpha gamma (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b) with hC'
  have key : V - C / t ^ 2 - C' / t ^ 3 = (t ^ 2 * V - C - C' / t) / t ^ 2 := by
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  calc |t ^ 2 * V - C - C' / t| / t ^ 2 ≤ (K / t ^ 2) / t ^ 2 :=
        div_le_div_of_nonneg_right (h ht) (by positivity)
    _ = K / t ^ 4 := by ring

/-- **The relative form to second order**: when the leading constant `C ≠ 0`,
`|Cov[L∘A, ψ]/covKFormula − 1 − (C'/C)/t| ≤ K/t²` — E2's "relative error proportional to `1/t`"
with its coefficient, in the rotated frame. -/
theorem covKFormula_rot_ratio_order2_rate (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (B : Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → ℝ)
    (hc : ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) - (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2)) ≠ 0) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) /
        covKFormula t (Q * diagonal lam * Qᵀ) (rotT Q alpha) B b - 1 -
        (covKCoeff2Sep lam alpha gamma (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b) /
          ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) - (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2))) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := covKFormula_rot_order2_rate hQ c hlam hgamma hdisc B b
  set C := ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) - (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2)) with hC
  set C' := covKCoeff2Sep lam alpha gamma (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b) with hC'
  refine ⟨K / |C|, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have htne := ht0.ne'
  have hlne : ∀ i, lam i ≠ 0 := fun i => (hlam i).ne'
  have e := h ht
  rw [covKFormula_rot hQ hlne alpha htne B b] at e ⊢
  set V := gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
    (rotatedAnharmonic Q c lam alpha gamma)
    (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) with hV
  have key : V / (C / t ^ 2) - 1 - C' / C / t = (V - C / t ^ 2 - C' / t ^ 3) * (t ^ 2 / C) := by
    field_simp
  rw [key, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  calc |V - C / t ^ 2 - C' / t ^ 3| * (t ^ 2 / |C|) ≤ K / t ^ 4 * (t ^ 2 / |C|) :=
        mul_le_mul_of_nonneg_right e (by positivity)
    _ = K / |C| / t ^ 2 := by
        field_simp

end Rotated

end Laplace.Multi
