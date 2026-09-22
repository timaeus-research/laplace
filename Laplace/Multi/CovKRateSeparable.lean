/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovKSeparable
import Laplace.Multi.E2Matrix
import Laplace.OneD.CovKRate

/-!
# eq:covK with a rate for the separable and rotated oscillators

The one-dimensional rate of `CovKRate` lifts to E2's oscillator: for the eigen-coordinates
`|t² Cov_L[L, uᵢ²] − 1/λᵢ| ≤ K/t`, `|t² Cov_L[L, uᵢ] + αᵢ/(2λᵢ²)| ≤ K/t` and, for `i ≠ j`,
`|t² Cov_L[L, uᵢuⱼ]| ≤ K/t` (from the exact off-diagonal identity, `⟨x⟩ = O(1/t)`); hence for the
full quadratic probe `|t² Cov_L[L, ½∑Bᵢⱼuᵢuⱼ + ∑bᵢuᵢ] − ∑ᵢ (Bᵢᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²))| ≤ K/t`
(`covK_separable_quadratic_rate`), and in the note's frame, for the ambient probe
`ψ(w) = ½(w−c)ᵀB(w−c) + bᵀ(w−c)`,

`|Cov[L∘A, ψ] − covKFormula t H T B b| ≤ K/t³` (`covKFormula_rot_rate`):

eq:covK is exact to relative `O(1/t)` for E2's oscillator, which is E2's finding "relative error
proportional to `1/t` … including for the second-order quantity eq:covK" (as an upper bound). The
relative form `covKFormula_rot_ratio_rate` needs the constant to be nonzero.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section Separable

variable {ι : Type*} [Fintype ι] {lam alpha gamma : ι → ℝ}

/-- `|t² Cov_L[L, uᵢ²] − 1/λᵢ| ≤ K/t`. -/
theorem covK_separable_sq_rate (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i ^ 2) - 1 / lam i| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := covK_sq_rate (hlam i) (hgamma i) (hdisc i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [gibbsCov_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht0 i 2]
  exact h ht

/-- `|t² Cov_L[L, uᵢ] + αᵢ/(2λᵢ²)| ≤ K/t`. -/
theorem covK_separable_lin_rate (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i) + alpha i / (2 * lam i ^ 2)| ≤
        K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := covK_lin_rate (hlam i) (hgamma i) (hdisc i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e := gibbsCov_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht0 i 1
  simp only [pow_one] at e
  rw [e]
  exact h ht

/-- `|t² Cov_L[L, uᵢuⱼ]| ≤ K/t` for `i ≠ j`. -/
theorem covK_separable_offdiag_rate (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {i j : ι} (hij : i ≠ j) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i * u j)| ≤ K / t := by
  obtain ⟨Ki, Ti, hKi, hTi, hi⟩ := mean_anharmonic_rate_div (hlam i) (hgamma i) (hdisc i)
  obtain ⟨Kj, Tj, hKj, hTj, hj⟩ := mean_anharmonic_rate_div (hlam j) (hgamma j) (hdisc j)
  obtain ⟨Li, Si, hLi, hSi, gi⟩ := covK_lin_rate (hlam i) (hgamma i) (hdisc i)
  obtain ⟨Lj, Sj, hLj, hSj, gj⟩ := covK_lin_rate (hlam j) (hgamma j) (hdisc j)
  set mi : ℝ := -alpha i / (2 * lam i ^ 2) with hmi
  set mj : ℝ := -alpha j / (2 * lam j ^ 2) with hmj
  set Di : ℝ := |-(alpha i / (2 * lam i ^ 2))| + Li with hDi
  set Dj : ℝ := |-(alpha j / (2 * lam j ^ 2))| + Lj with hDj
  refine ⟨(|mj| + Kj) * Di + (|mi| + Ki) * Dj, Ti + Tj + Si + Sj, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  -- the means are `O(1/t)`
  have hmean : ∀ {m K E : ℝ}, 0 ≤ K → |E - m / t| ≤ K / t ^ 2 → |E| ≤ (|m| + K) / t := by
    intro m K E hK hE
    have h1 : K / t ^ 2 ≤ K / t := by
      apply div_le_div_of_nonneg_left hK ht0
      calc t = t * 1 := (mul_one t).symm
        _ ≤ t * t := by gcongr
        _ = t ^ 2 := (sq t).symm
    calc |E| = |m / t + (E - m / t)| := by ring_nf
      _ ≤ |m / t| + |E - m / t| := abs_add_le _ _
      _ ≤ |m| / t + K / t := by
          rw [abs_div, abs_of_pos ht0]
          exact add_le_add le_rfl (hE.trans h1)
      _ = (|m| + K) / t := by ring
  have bi := hmean hKi (hi (show Ti ≤ t by linarith))
  have bj := hmean hKj (hj (show Tj ≤ t by linarith))
  -- the one-dimensional energy–coordinate covariances are bounded
  have ci : |t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential (lam i) (alpha i) (gamma i)) t
      (anharmonicPotential (lam i) (alpha i) (gamma i)) (fun x => x)| ≤ Di := by
    have g := gi (show Si ≤ t by linarith)
    rw [← sub_neg_eq_add] at g
    exact rate_bounded ht1 hLi g
  have cj : |t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential (lam j) (alpha j) (gamma j)) t
      (anharmonicPotential (lam j) (alpha j) (gamma j)) (fun x => x)| ≤ Dj := by
    have g := gj (show Sj ≤ t by linarith)
    rw [← sub_neg_eq_add] at g
    exact rate_bounded ht1 hLj g
  rw [gibbsCov_energy_pair_separableAnharmonic hlam hgamma hdisc ht0 hij]
  set Ei := _root_.Laplace.gibbsExpectation (anharmonicPotential (lam i) (alpha i) (gamma i)) t
    (fun x => x) with hEi
  set Ej := _root_.Laplace.gibbsExpectation (anharmonicPotential (lam j) (alpha j) (gamma j)) t
    (fun x => x) with hEj
  set Ci := _root_.Laplace.gibbsCov (anharmonicPotential (lam i) (alpha i) (gamma i)) t
    (anharmonicPotential (lam i) (alpha i) (gamma i)) (fun x => x) with hCi
  set Cj := _root_.Laplace.gibbsCov (anharmonicPotential (lam j) (alpha j) (gamma j)) t
    (anharmonicPotential (lam j) (alpha j) (gamma j)) (fun x => x) with hCj
  have key : t ^ 2 * (Ej * Ci + Ei * Cj) = Ej * (t ^ 2 * Ci) + Ei * (t ^ 2 * Cj) := by ring
  rw [key]
  calc |Ej * (t ^ 2 * Ci) + Ei * (t ^ 2 * Cj)|
      ≤ |Ej| * |t ^ 2 * Ci| + |Ei| * |t ^ 2 * Cj| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ (|mj| + Kj) / t * Di + (|mi| + Ki) / t * Dj :=
        add_le_add (mul_le_mul bj ci (abs_nonneg _) (by positivity))
          (mul_le_mul bi cj (abs_nonneg _) (by positivity))
    _ = ((|mj| + Kj) * Di + (|mi| + Ki) * Dj) / t := by ring

/-- `|t² Cov_L[L, uᵢuⱼ] − δᵢⱼ/λᵢ| ≤ K/t`. -/
theorem covK_separable_pair_rate [DecidableEq ι] (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i j : ι) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i * u j) -
        (if i = j then 1 / lam i else 0)| ≤ K / t := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨K, T, hK, hT, h⟩ := covK_separable_sq_rate hlam hgamma hdisc i
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    rw [if_pos rfl]
    have := h ht
    simpa only [sq] using this
  · obtain ⟨K, T, hK, hT, h⟩ := covK_separable_offdiag_rate hlam hgamma hdisc hij
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    rw [if_neg hij, sub_zero]
    exact h ht

/-- The energy–probe covariance of a full quadratic probe, split into pairs (as in
`covK_separable_quadratic`). -/
theorem gibbsCov_energy_quadratic_split (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) (B : ι → ι → ℝ)
    (b : ι → ℝ) :
    gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
      (fun u => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) =
      ∑ p : ι × ι, B p.1 p.2 / 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u p.1 * u p.2) +
      ∑ i, b i * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i) := by
  classical
  set L := separableAnharmonic lam alpha gamma with hL
  have hcm : ∀ i j, Integrable (fun u : ι → ℝ => u i * u j * Real.exp (-(t * L u))) :=
    fun i j => integrable_coord_mul_separableAnharmonic hlam hgamma hdisc ht i j
  have hc : ∀ i, Integrable (fun u : ι → ℝ => u i * Real.exp (-(t * L u))) :=
    fun i => integrable_coord_separableAnharmonic hlam hgamma hdisc ht i
  have hLcm : ∀ i j, Integrable (fun u : ι → ℝ =>
      L u * (u i * u j) * Real.exp (-(t * L u))) := fun i j =>
    integrable_energy_mul_separableAnharmonic _ fun k =>
      integrable_energy_coord_mul_separableAnharmonic hlam hgamma hdisc ht k i j
  have hLc : ∀ i, Integrable (fun u : ι → ℝ => L u * u i * Real.exp (-(t * L u))) := fun i =>
    integrable_energy_mul_separableAnharmonic (fun u => u i) fun k =>
      (integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k i 1).congr
        (Eventually.of_forall fun u => by simp only [pow_one])
  have hφP : ∀ p : ι × ι, Integrable (fun u : ι → ℝ =>
      B p.1 p.2 / 2 * (u p.1 * u p.2) * Real.exp (-(t * L u))) := fun p =>
    ((hcm p.1 p.2).const_mul (B p.1 p.2 / 2)).congr (Eventually.of_forall fun u => by ring)
  have hφPL : ∀ p : ι × ι, Integrable (fun u : ι → ℝ =>
      B p.1 p.2 / 2 * (u p.1 * u p.2) * L u * Real.exp (-(t * L u))) := fun p =>
    ((hLcm p.1 p.2).const_mul (B p.1 p.2 / 2)).congr (Eventually.of_forall fun u => by ring)
  have hφQ : ∀ i, Integrable (fun u : ι → ℝ => b i * u i * Real.exp (-(t * L u))) := fun i =>
    ((hc i).const_mul (b i)).congr (Eventually.of_forall fun u => by ring)
  have hφQL : ∀ i, Integrable (fun u : ι → ℝ => b i * u i * L u * Real.exp (-(t * L u))) :=
    fun i => ((hLc i).const_mul (b i)).congr (Eventually.of_forall fun u => by ring)
  have hP : Integrable (fun u : ι → ℝ =>
      (∑ p : ι × ι, B p.1 p.2 / 2 * (u p.1 * u p.2)) * Real.exp (-(t * L u))) :=
    (integrable_finsetSum (Finset.univ : Finset (ι × ι)) fun p _ => hφP p).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hQ : Integrable (fun u : ι → ℝ => (∑ i, b i * u i) * Real.exp (-(t * L u))) :=
    (integrable_finsetSum Finset.univ fun i _ => hφQ i).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hPL : Integrable (fun u : ι → ℝ =>
      (∑ p : ι × ι, B p.1 p.2 / 2 * (u p.1 * u p.2)) * L u * Real.exp (-(t * L u))) :=
    (integrable_finsetSum (Finset.univ : Finset (ι × ι)) fun p _ => hφPL p).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hQL : Integrable (fun u : ι → ℝ => (∑ i, b i * u i) * L u * Real.exp (-(t * L u))) :=
    (integrable_finsetSum Finset.univ fun i _ => hφQL i).congr
      (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
  have hprobe : (fun u : ι → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) =
      fun u => (∑ p : ι × ι, B p.1 p.2 / 2 * (u p.1 * u p.2)) + ∑ i, b i * u i := by
    funext u
    congr 1
    exact (Fintype.sum_prod_type' fun a c => B a c / 2 * (u a * u c)).symm
  rw [hprobe, gibbsCov_comm, gibbsCov_add_left_of_integrable L t _ _ _ hP hQ hPL hQL,
    gibbsCov_finsetSum_left L t Finset.univ _ _ (fun p _ => hφP p) (fun p _ => hφPL p),
    gibbsCov_finsetSum_left L t Finset.univ _ _ (fun i _ => hφQ i) (fun i _ => hφQL i)]
  congr 1
  · exact Finset.sum_congr rfl fun p _ => by rw [gibbsCov_const_mul_left, gibbsCov_comm]
  · exact Finset.sum_congr rfl fun i _ => by rw [gibbsCov_const_mul_left, gibbsCov_comm]

/-- **eq:covK with a rate for the separable oscillator and any quadratic probe**:
`|t² Cov_L[L, ½∑Bᵢⱼuᵢuⱼ + ∑bᵢuᵢ] − ∑ᵢ (Bᵢᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²))| ≤ K/t` eventually. -/
theorem covK_separable_quadratic_rate (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (B : ι → ι → ℝ) (b : ι → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma)
        (fun u => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) -
        ∑ i, (B i i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2))| ≤ K / t := by
  classical
  choose Kp Tp hKp hTp hp using fun p : ι × ι =>
    covK_separable_pair_rate hlam hgamma hdisc p.1 p.2
  choose Kl Tl hKl hTl hl using fun i : ι => covK_separable_lin_rate hlam hgamma hdisc i
  set L := separableAnharmonic lam alpha gamma with hL
  refine ⟨∑ p : ι × ι, |B p.1 p.2 / 2| * Kp p + ∑ i, |b i| * Kl i,
    1 + ∑ p : ι × ι, Tp p + ∑ i, Tl i,
    add_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (hKp p))
      (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hKl i)), ?_, fun {t} ht => ?_⟩
  · have h1 : 0 ≤ ∑ p : ι × ι, Tp p := Finset.sum_nonneg fun p _ => zero_le_one.trans (hTp p)
    have h2 : 0 ≤ ∑ i, Tl i := Finset.sum_nonneg fun i _ => zero_le_one.trans (hTl i)
    linarith
  have hsp : 0 ≤ ∑ p : ι × ι, Tp p := Finset.sum_nonneg fun p _ => zero_le_one.trans (hTp p)
  have hsl : 0 ≤ ∑ i, Tl i := Finset.sum_nonneg fun i _ => zero_le_one.trans (hTl i)
  have hTpi : ∀ p, Tp p ≤ t := fun p => by
    have := Finset.single_le_sum (f := Tp) (fun q _ => zero_le_one.trans (hTp q))
      (Finset.mem_univ p)
    linarith
  have hTli : ∀ i, Tl i ≤ t := fun i => by
    have := Finset.single_le_sum (f := Tl) (fun q _ => zero_le_one.trans (hTl q))
      (Finset.mem_univ i)
    linarith
  have htpos : 0 < t := by linarith
  rw [gibbsCov_energy_quadratic_split hlam hgamma hdisc htpos B b]
  have hlim : ∑ i, (B i i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)) =
      (∑ p : ι × ι, B p.1 p.2 / 2 * (if p.1 = p.2 then 1 / lam p.1 else 0)) +
        ∑ i, b i * (-alpha i / (2 * lam i ^ 2)) := by
    rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  rw [hlim]
  have key : t ^ 2 * (∑ p : ι × ι, B p.1 p.2 / 2 * gibbsCov L t L (fun u => u p.1 * u p.2) +
        ∑ i, b i * gibbsCov L t L (fun u => u i)) -
      ((∑ p : ι × ι, B p.1 p.2 / 2 * (if p.1 = p.2 then 1 / lam p.1 else 0)) +
        ∑ i, b i * (-alpha i / (2 * lam i ^ 2))) =
      ∑ p : ι × ι, B p.1 p.2 / 2 * (t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2) -
          (if p.1 = p.2 then 1 / lam p.1 else 0)) +
        ∑ i, b i * (t ^ 2 * gibbsCov L t L (fun u => u i) - (-alpha i / (2 * lam i ^ 2))) := by
    have e1 : ∑ p : ι × ι, t ^ 2 * (B p.1 p.2 / 2 * gibbsCov L t L (fun u => u p.1 * u p.2)) =
        ∑ p : ι × ι, B p.1 p.2 / 2 * (t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2)) :=
      Finset.sum_congr rfl fun p _ => by ring
    have e2 : ∑ i, t ^ 2 * (b i * gibbsCov L t L (fun u => u i)) =
        ∑ i, b i * (t ^ 2 * gibbsCov L t L (fun u => u i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, e1, e2]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [key]
  calc |∑ p : ι × ι, B p.1 p.2 / 2 * (t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2) -
          (if p.1 = p.2 then 1 / lam p.1 else 0)) +
        ∑ i, b i * (t ^ 2 * gibbsCov L t L (fun u => u i) - (-alpha i / (2 * lam i ^ 2)))|
      ≤ |∑ p : ι × ι, B p.1 p.2 / 2 * (t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2) -
          (if p.1 = p.2 then 1 / lam p.1 else 0))| +
        |∑ i, b i * (t ^ 2 * gibbsCov L t L (fun u => u i) - (-alpha i / (2 * lam i ^ 2)))| :=
        abs_add_le _ _
    _ ≤ ∑ p : ι × ι, |B p.1 p.2 / 2| * (Kp p / t) + ∑ i, |b i| * (Kl i / t) := by
        gcongr
        · calc |∑ p : ι × ι, B p.1 p.2 / 2 * (t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2) -
                (if p.1 = p.2 then 1 / lam p.1 else 0))|
              ≤ ∑ p : ι × ι, |B p.1 p.2 / 2 * (t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2) -
                (if p.1 = p.2 then 1 / lam p.1 else 0))| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ p : ι × ι, |B p.1 p.2 / 2| * (Kp p / t) := Finset.sum_le_sum fun p _ => by
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_left (hp p (hTpi p)) (abs_nonneg _)
        · calc |∑ i, b i * (t ^ 2 * gibbsCov L t L (fun u => u i) - (-alpha i / (2 * lam i ^ 2)))|
              ≤ ∑ i, |b i * (t ^ 2 * gibbsCov L t L (fun u => u i) -
                (-alpha i / (2 * lam i ^ 2)))| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i, |b i| * (Kl i / t) := Finset.sum_le_sum fun i _ => by
                rw [abs_mul, neg_div, sub_neg_eq_add]
                exact mul_le_mul_of_nonneg_left (hl i (hTli i)) (abs_nonneg _)
    _ = (∑ p : ι × ι, |B p.1 p.2 / 2| * Kp p + ∑ i, |b i| * Kl i) / t := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

end Separable

/-! ### The note's frame -/

section Rotated

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ}

/-- **eq:covK is exact to `O(t⁻³)` for E2's oscillator**: for the ambient probe
`ψ(w) = ½(w−c)ᵀB(w−c) + bᵀ(w−c)`, `|Cov[L∘A, ψ] − covKFormula t H T B b| ≤ K/t³` eventually, with
`H = Q diag λ Qᵀ` and the rotated tensors. -/
theorem covKFormula_rot_rate (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) -
        covKFormula t (Q * diagonal lam * Qᵀ) (rotT Q alpha) B b| ≤ K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ := covK_separable_quadratic_rate hlam hgamma hdisc
    (fun i j => (Qᵀ * B * Q) i j) (Qᵀ *ᵥ b)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have htne := ht0.ne'
  have hlne : ∀ i, lam i ≠ 0 := fun i => (hlam i).ne'
  -- transport the covariance to the eigenframe
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
  have key : V - C / t ^ 2 = (t ^ 2 * V - C) / t ^ 2 := by
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  calc |t ^ 2 * V - C| / t ^ 2 ≤ (K / t) / t ^ 2 :=
        div_le_div_of_nonneg_right (h ht) (by positivity)
    _ = K / t ^ 3 := by ring

/-- **The relative form**: when `∑ᵢ ((QᵀBQ)ᵢᵢ/(2λᵢ) − (Qᵀb)ᵢαᵢ/(2λᵢ²)) ≠ 0`,
`|Cov[L∘A, ψ] / covKFormula − 1| ≤ K/t`: eq:covK has relative error `O(1/t)` (E2). -/
theorem covKFormula_rot_ratio_rate (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (hc : ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) - (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2)) ≠ 0) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) /
        covKFormula t (Q * diagonal lam * Qᵀ) (rotT Q alpha) B b - 1| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := covKFormula_rot_rate hQ c hlam hgamma hdisc B b
  set C := ∑ i, ((Qᵀ * B * Q) i i / (2 * lam i) - (Qᵀ *ᵥ b) i * alpha i / (2 * lam i ^ 2)) with hC
  refine ⟨K / |C|, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have htne := ht0.ne'
  have hlne : ∀ i, lam i ≠ 0 := fun i => (hlam i).ne'
  have e := h ht
  rw [covKFormula_rot hQ hlne alpha htne B b] at e ⊢
  set V := gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
    (rotatedAnharmonic Q c lam alpha gamma)
    (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) with hV
  have key : V / (C / t ^ 2) - 1 = (V - C / t ^ 2) * (t ^ 2 / C) := by
    field_simp
  rw [key, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  calc |V - C / t ^ 2| * (t ^ 2 / |C|) ≤ K / t ^ 3 * (t ^ 2 / |C|) :=
        mul_le_mul_of_nonneg_right e (by positivity)
    _ = K / |C| / t := by
        field_simp

end Rotated

end Laplace.Multi
