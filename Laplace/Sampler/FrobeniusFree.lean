/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.GaussianTable

/-!
# The spectrum-free E4 bound for the covariance

E4 of the Sanity on Sampling note: "The covariance error follows `√(d/(CN))` with a prefactor set by
the autocorrelation times." Tide `gaussian-table` proved the spectral form `frobenius_ula_le`,
`E‖Σ̂ − EΣ̂‖_F² ≤ (1/(CN)) ∑ᵢⱼ (1 + δᵢⱼ) s₂ᵢ s₂ⱼ (1 + ρᵢρⱼ)/(1 − ρᵢρⱼ)` with `ρᵢ = 1 − h pᵢ` and
`s₂ᵢ = 2h/(1 − ρᵢ²)` the ULA variances (`∑ᵢ s₂ᵢ² = ‖Σ_ULA‖_F²`). Here, with `r = 1 − h pmin` the
flattest direction's AR(1) coefficient and `τ(x) = (1 + x)/(1 − x)`:

* `sum_sum_ite_mul_le`: `∑ᵢⱼ (1 + δᵢⱼ) aᵢ aⱼ τᵢⱼ ≤ τmax (d + 1) ∑ᵢ aᵢ²` (Cauchy–Schwarz);
* `frobenius_ula_le_free`: `E‖Σ̂ − EΣ̂‖_F² ≤ (d + 1) τ(r²)/(CN) · ∑ᵢ s₂ᵢ²`;
* `frobenius_ula_relative_le_free`: the relative squared Frobenius error is at most
  `(d + 1) τ(r²)/(CN)` — the note's `√(d/(CN))` with prefactor `√((d+1)/d · τ(r²))`, exact in the
  isotropic case.
-/

open Finset MeasureTheory ProbabilityTheory

namespace Laplace.Sampler

/-! ### Algebra -/

section Algebra

/-- `(1 + x)/(1 − x)` is increasing on `[0, 1)`. -/
theorem tau_lin_mono {x x' : ℝ} (h : x ≤ x') (h1 : x' < 1) :
    (1 + x) / (1 - x) ≤ (1 + x') / (1 - x') := by
  have hx1 : x < 1 := lt_of_le_of_lt h h1
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Cauchy–Schwarz for the E4 double sum**:
`∑ᵢⱼ (1 + δᵢⱼ) aᵢ aⱼ τᵢⱼ ≤ τmax ((d + 1) ∑ᵢ aᵢ²)` for `aᵢ ≥ 0`, `τᵢⱼ ≤ τmax`, `τmax ≥ 0`. -/
theorem sum_sum_ite_mul_le (a : ι → ℝ) (τ : ι → ι → ℝ) {τmax : ℝ} (ha : ∀ i, 0 ≤ a i)
    (hτ : ∀ i j, τ i j ≤ τmax) (hτmax : 0 ≤ τmax) :
    ∑ i, ∑ j, (if i = j then (2 : ℝ) else 1) * (a i * a j * τ i j) ≤
      τmax * ((Fintype.card ι + 1) * ∑ i, a i ^ 2) := by
  have h1 : ∀ i j, (if i = j then (2 : ℝ) else 1) * (a i * a j * τ i j) ≤
      τmax * (a i * a j) + τmax * (if i = j then a i * a j else 0) := by
    intro i j
    have hij0 : 0 ≤ a i * a j := mul_nonneg (ha i) (ha j)
    have := mul_le_mul_of_nonneg_left (hτ i j) hij0
    split_ifs with hij
    · nlinarith
    · nlinarith
  have hrow : ∀ i, ∑ j, (τmax * (a i * a j) + τmax * (if i = j then a i * a j else 0)) =
      τmax * (a i * ∑ j, a j) + τmax * a i ^ 2 := by
    intro i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, sq]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := a)
  rw [Finset.card_univ] at hcs
  calc ∑ i, ∑ j, (if i = j then (2 : ℝ) else 1) * (a i * a j * τ i j)
      ≤ ∑ i, ∑ j, (τmax * (a i * a j) + τmax * (if i = j then a i * a j else 0)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = τmax * (∑ i, a i) ^ 2 + τmax * ∑ i, a i ^ 2 := by
        simp_rw [hrow]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, sq]
    _ ≤ τmax * (Fintype.card ι * ∑ i, a i ^ 2) + τmax * ∑ i, a i ^ 2 :=
        add_le_add_left (mul_le_mul_of_nonneg_left hcs hτmax) _
    _ = τmax * ((Fintype.card ι + 1) * ∑ i, a i ^ 2) := by ring

end Algebra

/-! ### The spectrum-free covariance bound -/

section ULA

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **E4 for the covariance, spectrum-free**: with `pmin ≤ pᵢ ≤ pmax`, `0 < h pmin`, `h pmax ≤ 1`,
`r = 1 − h pmin`, `E‖Σ̂ − EΣ̂‖_F² ≤ (d + 1) τ(r²)/(CN) · ∑ᵢ s₂ᵢ²`, `s₂ᵢ = 2h/(1 − ρᵢ²)`. -/
theorem frobenius_ula_le_free [DecidableEq ι] {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h pmin pmax : ℝ}
    (hh : 0 < h) (hpmin : 0 < pmin) (hpp : pmin ≤ pmax) (hmin : ∀ i, pmin ≤ hQ.1.eigenvalues i)
    (hmax : ∀ i, hQ.1.eigenvalues i ≤ pmax) (hstab : h * pmax ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ∑ i, ∑ j,
        (pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω))
            N b i j ω -
          ∫ ω', pooledSecondMoment
            (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω' ∂P) ^ 2
        ∂P ≤
      (Fintype.card ι + 1) * ((1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2)) / (C * N) *
        ∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2)) ^ 2 := by
  have hstab' : ∀ i, h * hQ.1.eigenvalues i ≤ 1 := fun i =>
    le_trans (mul_le_mul_of_nonneg_left (hmax i) hh.le) hstab
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr1 : 1 - h * pmin < 1 := by linarith [mul_pos hh hpmin]
  have hr0 : 0 ≤ 1 - h * pmin := by linarith [mul_le_mul_of_nonneg_left hpp hh.le]
  have hr2 : (1 - h * pmin) ^ 2 < 1 := by nlinarith
  have hρ0 : ∀ i, 0 ≤ 1 - h * hQ.1.eigenvalues i := fun i => by linarith [hstab' i]
  have hρr : ∀ i, 1 - h * hQ.1.eigenvalues i ≤ 1 - h * pmin := fun i => by
    linarith [mul_le_mul_of_nonneg_left (hmin i) hh.le]
  have hρ1 : ∀ i, 1 - h * hQ.1.eigenvalues i < 1 := fun i => lt_of_le_of_lt (hρr i) hr1
  have hs₂ : ∀ i, 0 ≤ 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) := fun i => by
    have := hρ0 i
    have := hρ1 i
    have hd : 0 < 1 - (1 - h * hQ.1.eigenvalues i) ^ 2 := by nlinarith
    positivity
  have hτmax : 0 ≤ (1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) :=
    div_nonneg (by positivity) (by linarith)
  refine le_trans (frobenius_ula_le hQ hh hstab' hC hN b ξ hmeas hlaw hind) ?_
  have hterm : ∀ i j, (if i = j then (2 : ℝ) else 1) / (C * N) *
      (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        (2 * h / (1 - (1 - h * hQ.1.eigenvalues j) ^ 2)) *
        (1 + (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) /
        (1 - (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j))) =
      (1 / (C * N)) * ((if i = j then (2 : ℝ) else 1) *
        (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
          (2 * h / (1 - (1 - h * hQ.1.eigenvalues j) ^ 2)) *
          ((1 + (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) /
            (1 - (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j))))) := by
    intro i j
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  have hτle : ∀ i j, (1 + (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) /
      (1 - (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) ≤
      (1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) := by
    intro i j
    apply tau_lin_mono _ hr2
    rw [sq]
    exact mul_le_mul (hρr i) (hρr j) (hρ0 j) hr0
  have key := sum_sum_ite_mul_le (fun i => 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2))
    (fun i j => (1 + (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) /
      (1 - (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j))) hs₂ hτle hτmax
  calc (1 / ((C : ℝ) * N)) * ∑ i, ∑ j, (if i = j then (2 : ℝ) else 1) *
        (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
          (2 * h / (1 - (1 - h * hQ.1.eigenvalues j) ^ 2)) *
          ((1 + (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) /
            (1 - (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j))))
      ≤ (1 / ((C : ℝ) * N)) * ((1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) *
          ((Fintype.card ι + 1) * ∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2)) ^ 2)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (Fintype.card ι + 1) * ((1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2)) / (C * N) *
        ∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2)) ^ 2 := by ring

/-- **The relative Frobenius error, spectrum-free**: `E‖Σ̂ − EΣ̂‖_F² / ∑ᵢ s₂ᵢ² ≤ (d + 1) τ(r²)/(CN)`
(`∑ᵢ s₂ᵢ² = ‖Σ_ULA‖_F²`): the note's `√(d/(CN))` with prefactor `√((d + 1)/d · τ(r²))`. -/
theorem frobenius_ula_relative_le_free [DecidableEq ι] [Nonempty ι] {Q : Matrix ι ι ℝ}
    (hQ : Q.PosDef) {h pmin pmax : ℝ} (hh : 0 < h) (hpmin : 0 < pmin)
    (hmin : ∀ i, pmin ≤ hQ.1.eigenvalues i) (hmax : ∀ i, hQ.1.eigenvalues i ≤ pmax)
    (hstab : h * pmax ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    (∫ ω, ∑ i, ∑ j,
        (pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω))
            N b i j ω -
          ∫ ω', pooledSecondMoment
            (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω' ∂P) ^ 2
        ∂P) / ∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2)) ^ 2 ≤
      (Fintype.card ι + 1) * ((1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2)) / (C * N) := by
  have hpp : pmin ≤ pmax := le_trans (hmin (Classical.arbitrary ι)) (hmax _)
  have hstab' : ∀ i, h * hQ.1.eigenvalues i ≤ 1 := fun i =>
    le_trans (mul_le_mul_of_nonneg_left (hmax i) hh.le) hstab
  have hpos : 0 < ∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2)) ^ 2 := by
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    have hρ0 : 0 ≤ 1 - h * hQ.1.eigenvalues i := by linarith [hstab' i]
    have hρ1 : 1 - h * hQ.1.eigenvalues i < 1 := by
      linarith [mul_pos hh (hQ.eigenvalues_pos i)]
    have hd : 0 < 1 - (1 - h * hQ.1.eigenvalues i) ^ 2 := by nlinarith
    positivity
  rw [div_le_iff₀ hpos]
  exact frobenius_ula_le_free hQ hh hpmin hpp hmin hmax hstab hC hN b ξ hmeas hlaw hind

/-- **The relative RMS Frobenius error, spectrum-free**:
`√E‖Σ̂ − EΣ̂‖_F² / √(∑ᵢ s₂ᵢ²) ≤ √((d + 1) τ(r²)/(CN))` — E4's "`√(d/(CN))` with a prefactor set by
the autocorrelation times", the prefactor being `√((d+1)/d · τ(r²))`. -/
theorem frobenius_ula_rms_le_free [DecidableEq ι] [Nonempty ι] {Q : Matrix ι ι ℝ}
    (hQ : Q.PosDef) {h pmin pmax : ℝ} (hh : 0 < h) (hpmin : 0 < pmin)
    (hmin : ∀ i, pmin ≤ hQ.1.eigenvalues i) (hmax : ∀ i, hQ.1.eigenvalues i ≤ pmax)
    (hstab : h * pmax ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    Real.sqrt (∫ ω, ∑ i, ∑ j,
        (pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω))
            N b i j ω -
          ∫ ω', pooledSecondMoment
            (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω' ∂P) ^ 2
        ∂P) / Real.sqrt (∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2)) ^ 2) ≤
      Real.sqrt ((Fintype.card ι + 1) * ((1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2)) /
        (C * N)) := by
  have hrel := frobenius_ula_relative_le_free hQ hh hpmin hmin hmax hstab hC hN b ξ hmeas hlaw hind
  have hnn : 0 ≤ ∫ ω, ∑ i, ∑ j,
      (pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω))
          N b i j ω -
        ∫ ω', pooledSecondMoment
          (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω' ∂P) ^ 2
      ∂P :=
    integral_nonneg fun ω => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 := Real.sqrt_le_sqrt hrel
  rwa [Real.sqrt_div hnn] at h2

end ULA

end Laplace.Sampler
