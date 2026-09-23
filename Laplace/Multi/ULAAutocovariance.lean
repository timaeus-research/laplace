/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ULAFluctuationBudget
import Laplace.Multi.AnchoredCovarianceGap

/-!
# Stationary autocovariance and long-run variance of the ULA-sampled energy (E5)

The stationary law of ULA on the anchored Gaussian `N(m, P⁻¹)` is `N(m, Σ)`, `Σ = ulaCov P h`; its
lag-`ℓ`
energy autocovariance is defined kernel-wise, as the covariance under `N(m, Σ)` between `Y = ½uᵀHu`
and its
`ℓ`-step conditional mean `condEnergy ℓ x₀ = ⟨½uᵀHu⟩_{ℓ-step law from x₀}` (`ulaAutoCov`; for a
stationary chain
this is `Cov(Y₀, Y_ℓ)` by conditioning). The conditional mean is the quadratic-plus-linear probe
`½x₀ᵀB_ℓx₀ + b_ℓ·x₀ + c_ℓ`, `B_ℓ = U diag(λᵢρᵢ^{2ℓ}) Uᵀ`, `b_ℓ = U diag(λᵢρᵢ^ℓ(1 − ρᵢ^ℓ)) Uᵀ m`
(`condEnergy_eq`), and the
mixed Wick covariance of `AnchoredCovarianceGap` gives, in any orthogonal frame diagonalising `P`
(`p`) and `H` (`λ`),
**`ulaAutoCov ℓ = ½∑ᵢλᵢ²σᵢ⁴ρᵢ^{2ℓ} + ∑ᵢλᵢ²σᵢ²m̂ᵢ²ρᵢ^ℓ`**, `σᵢ² = 1/(pᵢκᵢ)`, `ρᵢ = 1 − hpᵢ`, `m̂ =
Uᵀm` (`ulaAutoCov_eq`, all
`ℓ`; the lag-0 value is the stationary variance). Summing the geometric series
(`ulaAutoCov_summable`) gives the
long-run variance **`τ² = c₀ + 2∑_{ℓ≥1}c_ℓ = ½∑ᵢλᵢ²σᵢ⁴(1+ρᵢ²)/(1−ρᵢ²) + ∑ᵢλᵢ²σᵢ²m̂ᵢ²(1+ρᵢ)/(1−ρᵢ)`**
(`ulaLongRunVar_eq`), `= ∑ᵢλᵢ²(1+ρᵢ²)/(4hpᵢ³κᵢ³) + 2∑ᵢλᵢ²m̂ᵢ²/(hpᵢ²)` in sampler variables
(`ulaLongRunVar_eq_sampler`),
nonnegative (`ulaLongRunVar_nonneg`); the integrated autocorrelation times `(1+ρᵢ²)/(1−ρᵢ²)` and
`(1+ρᵢ)/(1−ρᵢ)`
are asymptotically `t`-independent at the β-scaled step. The exact lag-sum variance functional of
the `n`-step chain
average, `(1/n²)(n c₀ + 2∑_{j<n}(n−(j+1))c_{j+1})`, is
**`(1/n²)∑ᵢ[aᵢ(n + 2G_n(ρᵢ²)) + bᵢ(n + 2G_n(ρᵢ))]`**, `G_n(r) = r(n(1−r) − (1−rⁿ))/(1−r)²`
(`lagSumVar_eq`,
`sum_range_cesaro_geometric`), i.e. **`τ²/n − (2/n²)∑ᵢ[aᵢρᵢ²(1−ρᵢ^{2n})/(1−ρᵢ²)² +
bᵢρᵢ(1−ρᵢⁿ)/(1−ρᵢ)²]`**
(`lagSumVar_eq_longRun_sub`): `n·Var(Ȳ_n) → τ²`.

The tilted-Gaussian layer supplies constant shifts of expectations and covariances
(`tiltedExpectation_add_const`,
`tiltedCov_add_const`) with the integrability of the shifted energy, probe and their product.
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

/-! ### Cesàro-weighted geometric sums -/

/-- `∑_{j<n} (n − (j+1)) r^{j+1} = r(n(1−r) − (1−rⁿ))/(1−r)²`. -/
theorem sum_range_cesaro_geometric (r : ℝ) (hr : r ≠ 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * r ^ (j + 1) =
      r * (n * (1 - r) - (1 - r ^ n)) / (1 - r) ^ 2 := by
  have h1 : 1 - r ≠ 0 := sub_ne_zero.2 (Ne.symm hr)
  have h2 : r - 1 ≠ 0 := sub_ne_zero.2 hr
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ∀ j ∈ Finset.range n, (((n + 1 : ℕ) : ℝ) - (j + 1)) * r ^ (j + 1) =
        ((n : ℝ) - (j + 1)) * r ^ (j + 1) + r ^ (j + 1) := fun j _ => by push_cast; ring
    have hg : ∑ j ∈ Finset.range n, r ^ (j + 1) = r * (r ^ n - 1) / (r - 1) := by
      simp_rw [pow_succ]
      rw [← Finset.sum_mul, geom_sum_eq hr]
      ring
    rw [Finset.sum_range_succ, Finset.sum_congr rfl e, Finset.sum_add_distrib, ih, hg]
    push_cast
    field_simp
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Constant shifts of tilted expectations and covariances -/

/-- `⟨φ + c⟩ = ⟨φ⟩ + c` for the normalised tilted Gaussian. -/
theorem tiltedExpectation_add_const {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ)
    (φ : (ι → ℝ) → ℝ) (c : ℝ)
    (hφ : Integrable (fun u : ι → ℝ => φ (u + tiltMean P v) * gaussianWeight (matCLM P) u)) :
    tiltedExpectation P v (fun u => φ u + c) = tiltedExpectation P v φ + c := by
  rw [tiltedExpectation_eq hP v, tiltedExpectation_eq hP v]
  have hZ0 : gaussianZ (matCLM P) ≠ 0 := (gaussianZ_matCLM_pos hP).ne'
  have hZ : ∫ u : ι → ℝ, gaussianWeight (matCLM P) u = gaussianZ (matCLM P) := rfl
  have e : ∀ u : ι → ℝ, (φ (u + tiltMean P v) + c) * gaussianWeight (matCLM P) u =
      φ (u + tiltMean P v) * gaussianWeight (matCLM P) u + c * gaussianWeight (matCLM P) u :=
    fun u => by ring
  simp_rw [e]
  rw [integral_add hφ ((integrable_gaussianWeight_matCLM hP).const_mul c), integral_const_mul, hZ,
    add_div, mul_div_assoc, div_self hZ0, mul_one]

/-- `⟨q·(f + c)⟩ = ⟨q·f⟩ + c⟨q⟩`. -/
theorem tiltedExpectation_mul_add_const {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ)
    (q f : (ι → ℝ) → ℝ) (c : ℝ)
    (hqf : Integrable (fun u : ι → ℝ =>
      q (u + tiltMean P v) * f (u + tiltMean P v) * gaussianWeight (matCLM P) u))
    (hq : Integrable (fun u : ι → ℝ => q (u + tiltMean P v) * gaussianWeight (matCLM P) u)) :
    tiltedExpectation P v (fun u => q u * (f u + c)) =
      tiltedExpectation P v (fun u => q u * f u) + c * tiltedExpectation P v q := by
  rw [tiltedExpectation_eq hP v, tiltedExpectation_eq hP v, tiltedExpectation_eq hP v]
  have e : ∀ u : ι → ℝ, q (u + tiltMean P v) * (f (u + tiltMean P v) + c) *
      gaussianWeight (matCLM P) u =
      q (u + tiltMean P v) * f (u + tiltMean P v) * gaussianWeight (matCLM P) u +
        c * (q (u + tiltMean P v) * gaussianWeight (matCLM P) u) := fun u => by ring
  simp_rw [e]
  rw [integral_add hqf (hq.const_mul c), integral_const_mul, add_div, mul_div_assoc]

/-- **Covariances ignore constant shifts**: `Cov(q, f + c) = Cov(q, f)`. -/
theorem tiltedCov_add_const {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ)
    (q f : (ι → ℝ) → ℝ) (c : ℝ)
    (hqf : Integrable (fun u : ι → ℝ =>
      q (u + tiltMean P v) * f (u + tiltMean P v) * gaussianWeight (matCLM P) u))
    (hq : Integrable (fun u : ι → ℝ => q (u + tiltMean P v) * gaussianWeight (matCLM P) u))
    (hf : Integrable (fun u : ι → ℝ => f (u + tiltMean P v) * gaussianWeight (matCLM P) u)) :
    tiltedExpectation P v (fun u => q u * (f u + c)) -
      tiltedExpectation P v q * tiltedExpectation P v (fun u => f u + c) =
    tiltedExpectation P v (fun u => q u * f u) -
      tiltedExpectation P v q * tiltedExpectation P v f := by
  rw [tiltedExpectation_mul_add_const hP v q f c hqf hq, tiltedExpectation_add_const hP v f c hf]
  ring

/-! ### Integrability of the shifted energy, probe and their product -/

theorem integrable_shift_energy {P : Matrix ι ι ℝ} (hP : P.PosDef) {H : Matrix ι ι ℝ} (hH :
    H.IsHermitian)
    (m : ι → ℝ) :
    Integrable (fun u : ι → ℝ => (1 / 2 * ((u + m) ⬝ᵥ H *ᵥ (u + m))) * gaussianWeight (matCLM P) u)
      := by
  have hlinH : ∀ u : ι → ℝ, (u + m) ⬝ᵥ H *ᵥ (u + m) =
      u ⬝ᵥ H *ᵥ u + 2 * (u ⬝ᵥ (H *ᵥ m)) + m ⬝ᵥ H *ᵥ m := by
    intro u
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_mulVec_symm_of_isHermitian hH m u]
    ring
  have hexp : ∀ u : ι → ℝ, (1 / 2 * ((u + m) ⬝ᵥ H *ᵥ (u + m))) * gaussianWeight (matCLM P) u = ((1 /
      2) * (u ⬝ᵥ H *ᵥ u * gaussianWeight (matCLM P) u) + ((1) * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight
      (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m)) * (gaussianWeight (matCLM P) u))) := by
    intro u
    rw [hlinH]
    ring
  simp_rw [hexp]
  have I1 := (integrable_quadForm_mul_gaussianWeight_matCLM hP H).const_mul (1 / 2)
  have I2 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m)).const_mul (1)
  have I3 := (integrable_gaussianWeight_matCLM hP).const_mul (1 / 2 * (m ⬝ᵥ H *ᵥ m))
  have I4 : Integrable (fun u : ι → ℝ => (1) * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight (matCLM P) u) + (1 /
      2 * (m ⬝ᵥ H *ᵥ m)) * (gaussianWeight (matCLM P) u)) := I2.add I3
  have I5 : Integrable (fun u : ι → ℝ => (1 / 2) * (u ⬝ᵥ H *ᵥ u * gaussianWeight (matCLM P) u) +
      ((1) * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m)) *
      (gaussianWeight (matCLM P) u))) := I1.add I4
  exact I5

theorem integrable_shift_quadProbe {P : Matrix ι ι ℝ} (hP : P.PosDef) {B : Matrix ι ι ℝ} (hB :
    B.IsHermitian)
    (b m : ι → ℝ) :
    Integrable (fun u : ι → ℝ => (1 / 2 * ((u + m) ⬝ᵥ B *ᵥ (u + m)) + (u + m) ⬝ᵥ b) * gaussianWeight
      (matCLM P) u) := by
  have hlinB : ∀ u : ι → ℝ, (u + m) ⬝ᵥ B *ᵥ (u + m) =
      u ⬝ᵥ B *ᵥ u + 2 * (u ⬝ᵥ (B *ᵥ m)) + m ⬝ᵥ B *ᵥ m := by
    intro u
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_mulVec_symm_of_isHermitian hB m u]
    ring
  have hexp : ∀ u : ι → ℝ, (1 / 2 * ((u + m) ⬝ᵥ B *ᵥ (u + m)) + (u + m) ⬝ᵥ b) * gaussianWeight
      (matCLM P) u = (((1 / 2) * (u ⬝ᵥ B *ᵥ u * gaussianWeight (matCLM P) u) + (1) * (u ⬝ᵥ (B *ᵥ m)
      * gaussianWeight (matCLM P) u)) + ((1 / 2 * (m ⬝ᵥ B *ᵥ m)) * (gaussianWeight (matCLM P) u) +
      ((1) * (u ⬝ᵥ b * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) * (gaussianWeight (matCLM P) u)))) :=
      by
    intro u
    rw [hlinB, add_dotProduct]
    ring
  simp_rw [hexp]
  have J1 := (integrable_quadForm_mul_gaussianWeight_matCLM hP B).const_mul (1 / 2)
  have J2 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (B *ᵥ m)).const_mul (1)
  have J3 : Integrable (fun u : ι → ℝ => (1 / 2) * (u ⬝ᵥ B *ᵥ u * gaussianWeight (matCLM P) u) + (1)
      * (u ⬝ᵥ (B *ᵥ m) * gaussianWeight (matCLM P) u)) := J1.add J2
  have J4 := (integrable_gaussianWeight_matCLM hP).const_mul (1 / 2 * (m ⬝ᵥ B *ᵥ m))
  have J5 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP b).const_mul (1)
  have J6 := (integrable_gaussianWeight_matCLM hP).const_mul (m ⬝ᵥ b)
  have J7 : Integrable (fun u : ι → ℝ => (1) * (u ⬝ᵥ b * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) *
      (gaussianWeight (matCLM P) u)) := J5.add J6
  have J8 : Integrable (fun u : ι → ℝ => (1 / 2 * (m ⬝ᵥ B *ᵥ m)) * (gaussianWeight (matCLM P) u) +
      ((1) * (u ⬝ᵥ b * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) * (gaussianWeight (matCLM P) u))) :=
      J4.add J7
  have J9 : Integrable (fun u : ι → ℝ => ((1 / 2) * (u ⬝ᵥ B *ᵥ u * gaussianWeight (matCLM P) u) +
      (1) * (u ⬝ᵥ (B *ᵥ m) * gaussianWeight (matCLM P) u)) + ((1 / 2 * (m ⬝ᵥ B *ᵥ m)) *
      (gaussianWeight (matCLM P) u) + ((1) * (u ⬝ᵥ b * gaussianWeight (matCLM P) u) + (m ⬝ᵥ b) *
      (gaussianWeight (matCLM P) u)))) := J3.add J8
  exact J9

theorem integrable_shift_energy_mul_quadProbe {P : Matrix ι ι ℝ} (hP : P.PosDef) {H B : Matrix ι ι
    ℝ}
    (hH : H.IsHermitian) (hB : B.IsHermitian) (b m : ι → ℝ) :
    Integrable (fun u : ι → ℝ => (1 / 2 * ((u + m) ⬝ᵥ H *ᵥ (u + m))) * (1 / 2 * ((u + m) ⬝ᵥ B *ᵥ (u
      + m)) + (u + m) ⬝ᵥ b) * gaussianWeight (matCLM P) u) := by
  have hlinH : ∀ u : ι → ℝ, (u + m) ⬝ᵥ H *ᵥ (u + m) =
      u ⬝ᵥ H *ᵥ u + 2 * (u ⬝ᵥ (H *ᵥ m)) + m ⬝ᵥ H *ᵥ m := by
    intro u
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_mulVec_symm_of_isHermitian hH m u]
    ring
  have hlinB : ∀ u : ι → ℝ, (u + m) ⬝ᵥ B *ᵥ (u + m) =
      u ⬝ᵥ B *ᵥ u + 2 * (u ⬝ᵥ (B *ᵥ m)) + m ⬝ᵥ B *ᵥ m := by
    intro u
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_mulVec_symm_of_isHermitian hB m u]
    ring
  have hexp : ∀ u : ι → ℝ, (1 / 2 * ((u + m) ⬝ᵥ H *ᵥ (u + m))) * (1 / 2 * ((u + m) ⬝ᵥ B *ᵥ (u + m))
      + (u + m) ⬝ᵥ b) * gaussianWeight (matCLM P) u = ((((1 / 4) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) *
      gaussianWeight (matCLM P) u) + ((1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u) + (1 / 4 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ H *ᵥ u * gaussianWeight (matCLM P) u))) + (((1
      / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ b)) * (u ⬝ᵥ H
      *ᵥ u * gaussianWeight (matCLM P) u)) + ((1 / 2) * ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) *
      gaussianWeight (matCLM P) u) + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u)))) + ((((1 / 2 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight (matCLM P) u)
      + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u)) + ((m ⬝ᵥ b) * (u ⬝ᵥ (H *ᵥ
      m) * gaussianWeight (matCLM P) u) + (1 / 4 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ B *ᵥ u * gaussianWeight
      (matCLM P) u))) + (((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m) * gaussianWeight (matCLM P) u) +
      (1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) * (gaussianWeight (matCLM P) u)) + ((1 / 2 * (m ⬝ᵥ H
      *ᵥ m)) * (u ⬝ᵥ b * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b))) *
      (gaussianWeight (matCLM P) u))))) := by
    intro u
    rw [hlinH, hlinB, add_dotProduct]
    ring
  simp_rw [hexp]
  have K1 := (integrable_quadForm_mul_quadForm_mul_gaussianWeight_matCLM hP H B).const_mul (1 / 4)
  have K2 := (integrable_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM hP H (B *ᵥ m)).const_mul
      (1 / 2)
  have K3 := (integrable_quadForm_mul_gaussianWeight_matCLM hP H).const_mul (1 / 4 * (m ⬝ᵥ B *ᵥ m))
  have K4 : Integrable (fun u : ι → ℝ => (1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u) + (1 / 4 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ H *ᵥ u * gaussianWeight (matCLM P) u)) :=
      K2.add K3
  have K5 : Integrable (fun u : ι → ℝ => (1 / 4) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) * gaussianWeight
      (matCLM P) u) + ((1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u) +
      (1 / 4 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ H *ᵥ u * gaussianWeight (matCLM P) u))) := K1.add K4
  have K6 := (integrable_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM hP H b).const_mul (1 / 2)
  have K7 := (integrable_quadForm_mul_gaussianWeight_matCLM hP H).const_mul (1 / 2 * (m ⬝ᵥ b))
  have K8 : Integrable (fun u : ι → ℝ => (1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ b) * gaussianWeight
      (matCLM P) u) + (1 / 2 * (m ⬝ᵥ b)) * (u ⬝ᵥ H *ᵥ u * gaussianWeight (matCLM P) u)) := K6.add K7
  have K9 := (integrable_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM hP B (H *ᵥ m)).const_mul
      (1 / 2)
  have K10 := (integrable_dotProduct_mul_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m) (B *ᵥ
      m)).const_mul (1)
  have K11 : Integrable (fun u : ι → ℝ => (1 / 2) * ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) *
      gaussianWeight (matCLM P) u) + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u)) := K9.add K10
  have K12 : Integrable (fun u : ι → ℝ => ((1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ b) * gaussianWeight
      (matCLM P) u) + (1 / 2 * (m ⬝ᵥ b)) * (u ⬝ᵥ H *ᵥ u * gaussianWeight (matCLM P) u)) + ((1 / 2) *
      ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u) + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u
      ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u))) := K8.add K11
  have K13 : Integrable (fun u : ι → ℝ => ((1 / 4) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) * gaussianWeight
      (matCLM P) u) + ((1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u) +
      (1 / 4 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ H *ᵥ u * gaussianWeight (matCLM P) u))) + (((1 / 2) * ((u ⬝ᵥ H
      *ᵥ u) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ b)) * (u ⬝ᵥ H *ᵥ u *
      gaussianWeight (matCLM P) u)) + ((1 / 2) * ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) * gaussianWeight
      (matCLM P) u) + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight (matCLM P) u)))) :=
      K5.add K12
  have K14 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m)).const_mul (1 / 2 * (m
      ⬝ᵥ B *ᵥ m))
  have K15 := (integrable_dotProduct_mul_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m)
      b).const_mul (1)
  have K16 : Integrable (fun u : ι → ℝ => (1 / 2 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight
      (matCLM P) u) + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u)) := K14.add
      K15
  have K17 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m)).const_mul (m ⬝ᵥ b)
  have K18 := (integrable_quadForm_mul_gaussianWeight_matCLM hP B).const_mul (1 / 4 * (m ⬝ᵥ H *ᵥ m))
  have K19 : Integrable (fun u : ι → ℝ => (m ⬝ᵥ b) * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight (matCLM P) u) +
      (1 / 4 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ B *ᵥ u * gaussianWeight (matCLM P) u)) := K17.add K18
  have K20 : Integrable (fun u : ι → ℝ => ((1 / 2 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight
      (matCLM P) u) + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u)) + ((m ⬝ᵥ b)
      * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight (matCLM P) u) + (1 / 4 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ B *ᵥ u *
      gaussianWeight (matCLM P) u))) := K16.add K19
  have K21 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (B *ᵥ m)).const_mul (1 / 2 * (m
      ⬝ᵥ H *ᵥ m))
  have K22 := (integrable_gaussianWeight_matCLM hP).const_mul (1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ
      m)))
  have K23 : Integrable (fun u : ι → ℝ => (1 / 2 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m) * gaussianWeight
      (matCLM P) u) + (1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) * (gaussianWeight (matCLM P) u)) :=
      K21.add K22
  have K24 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP b).const_mul (1 / 2 * (m ⬝ᵥ H *ᵥ
      m))
  have K25 := (integrable_gaussianWeight_matCLM hP).const_mul (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b)))
  have K26 : Integrable (fun u : ι → ℝ => (1 / 2 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ b * gaussianWeight (matCLM
      P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b))) * (gaussianWeight (matCLM P) u)) := K24.add K25
  have K27 : Integrable (fun u : ι → ℝ => ((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m) * gaussianWeight
      (matCLM P) u) + (1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) * (gaussianWeight (matCLM P) u)) + ((1
      / 2 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ b * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ
      b))) * (gaussianWeight (matCLM P) u))) := K23.add K26
  have K28 : Integrable (fun u : ι → ℝ => (((1 / 2 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ (H *ᵥ m) *
      gaussianWeight (matCLM P) u) + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b) * gaussianWeight (matCLM P)
      u)) + ((m ⬝ᵥ b) * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight (matCLM P) u) + (1 / 4 * (m ⬝ᵥ H *ᵥ m)) * (u
      ⬝ᵥ B *ᵥ u * gaussianWeight (matCLM P) u))) + (((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m) *
      gaussianWeight (matCLM P) u) + (1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) * (gaussianWeight
      (matCLM P) u)) + ((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ b * gaussianWeight (matCLM P) u) + (1 / 2 *
      (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b))) * (gaussianWeight (matCLM P) u)))) := K20.add K27
  have K29 : Integrable (fun u : ι → ℝ => (((1 / 4) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ B *ᵥ u) *
      gaussianWeight (matCLM P) u) + ((1 / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u) + (1 / 4 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ H *ᵥ u * gaussianWeight (matCLM P) u))) + (((1
      / 2) * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ b)) * (u ⬝ᵥ H
      *ᵥ u * gaussianWeight (matCLM P) u)) + ((1 / 2) * ((u ⬝ᵥ B *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) *
      gaussianWeight (matCLM P) u) + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m)) * gaussianWeight
      (matCLM P) u)))) + ((((1 / 2 * (m ⬝ᵥ B *ᵥ m)) * (u ⬝ᵥ (H *ᵥ m) * gaussianWeight (matCLM P) u)
      + (1) * ((u ⬝ᵥ (H *ᵥ m)) * (u ⬝ᵥ b) * gaussianWeight (matCLM P) u)) + ((m ⬝ᵥ b) * (u ⬝ᵥ (H *ᵥ
      m) * gaussianWeight (matCLM P) u) + (1 / 4 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ B *ᵥ u * gaussianWeight
      (matCLM P) u))) + (((1 / 2 * (m ⬝ᵥ H *ᵥ m)) * (u ⬝ᵥ (B *ᵥ m) * gaussianWeight (matCLM P) u) +
      (1 / 4 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ B *ᵥ m))) * (gaussianWeight (matCLM P) u)) + ((1 / 2 * (m ⬝ᵥ H
      *ᵥ m)) * (u ⬝ᵥ b * gaussianWeight (matCLM P) u) + (1 / 2 * (m ⬝ᵥ H *ᵥ m * (m ⬝ᵥ b))) *
      (gaussianWeight (matCLM P) u))))) := K13.add K28
  exact K29

omit [DecidableEq ι] in
/-- The covariance of the energy with a quadratic-plus-linear probe is unchanged by a constant. -/
theorem tiltedCov_energy_quadProbe_add_const {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ)
    {H B : Matrix ι ι ℝ} (hH : H.IsHermitian) (hB : B.IsHermitian) (b : ι → ℝ) (c : ℝ) :
    tiltedExpectation P v (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * (1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b + c))
        -
      tiltedExpectation P v (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u)) *
        tiltedExpectation P v (fun u => 1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b + c) =
    tiltedExpectation P v (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * (1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b)) -
      tiltedExpectation P v (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u)) *
        tiltedExpectation P v (fun u => 1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b) := by
  classical
  exact tiltedCov_add_const hP v (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u))
    (fun u => 1 / 2 * (u ⬝ᵥ B *ᵥ u) + u ⬝ᵥ b) c
    (integrable_shift_energy_mul_quadProbe hP hH hB b _) (integrable_shift_energy hP hH _)
    (integrable_shift_quadProbe hP hB b _)

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

/-! ### Frame lemmas -/

theorem conj_diagonal_transpose_frame (U : Matrix ι ι ℝ) (d : ι → ℝ) :
    (U * diagonal d * Uᵀ)ᵀ = U * diagonal d * Uᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

theorem isHermitian_conj_diagonal (U : Matrix ι ι ℝ) (d : ι → ℝ) :
    (U * diagonal d * Uᵀ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, conj_diagonal_transpose_frame]

/-- `∑ₐ∑_c (UD₁Uᵀ)ₐ_c (UD₂Uᵀ)_cₐ = tr(D₁D₂) = ∑ᵢ d₁ᵢd₂ᵢ`. -/
theorem sum_sum_conj_mul_conj (hU : Uᵀ * U = 1) (d₁ d₂ : ι → ℝ) :
    ∑ a, ∑ c, (U * diagonal d₁ * Uᵀ) a c * (U * diagonal d₂ * Uᵀ) c a = ∑ i, d₁ i * d₂ i := by
  have e : ∑ a, ∑ c, (U * diagonal d₁ * Uᵀ) a c * (U * diagonal d₂ * Uᵀ) c a =
      ((U * diagonal d₁ * Uᵀ) * (U * diagonal d₂ * Uᵀ)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [e, conj_mul_conj_frame hU, Matrix.diagonal_mul_diagonal, Matrix.trace_mul_cycle, hU,
    Matrix.one_mul, Matrix.trace_diagonal]

/-- Bilinear frame form: `x ⬝ᵥ (UDUᵀ)y = ∑ᵢ dᵢ x̂ᵢ ŷᵢ`. -/
theorem dotProduct_conj_diagonal_mulVec₂ (U : Matrix ι ι ℝ) (d : ι → ℝ) (x y : ι → ℝ) :
    x ⬝ᵥ (U * diagonal d * Uᵀ) *ᵥ y = ∑ i, d i * (Uᵀ *ᵥ x) i * (Uᵀ *ᵥ y) i := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem transpose_mulVec_conj_mulVec (hU : Uᵀ * U = 1) (d : ι → ℝ) (x : ι → ℝ) :
    Uᵀ *ᵥ ((U * diagonal d * Uᵀ) *ᵥ x) = diagonal d *ᵥ (Uᵀ *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]

/-- `(UD₁Uᵀx) ⬝ᵥ (UD₂Uᵀ)(UD₃Uᵀy) = ∑ᵢ d₁ᵢd₂ᵢd₃ᵢ x̂ᵢŷᵢ`. -/
theorem conj_mulVec_dotProduct_conj_mulVec (hU : Uᵀ * U = 1) (d₁ d₂ d₃ : ι → ℝ) (x y : ι → ℝ) :
    ((U * diagonal d₁ * Uᵀ) *ᵥ x) ⬝ᵥ (U * diagonal d₂ * Uᵀ) *ᵥ ((U * diagonal d₃ * Uᵀ) *ᵥ y) =
      ∑ i, d₁ i * d₂ i * d₃ i * (Uᵀ *ᵥ x) i * (Uᵀ *ᵥ y) i := by
  rw [Matrix.mulVec_mulVec, conj_mul_conj_frame hU, Matrix.diagonal_mul_diagonal,
    dotProduct_conj_diagonal_mulVec₂]
  simp only [transpose_mulVec_conj_mulVec hU, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The stationary ULA law `N(m, Σ)`, `Σ = ulaCov P h`, as a tilted Gaussian -/

theorem ulaCov_posDef_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hev : ∀ i, h * p i < 2) : (ulaCov P h).PosDef := by
  rw [ulaCov_eq_conj_frame hU hdiag hp hev]
  exact posDef_conj_diagonal hU fun i => div_pos one_pos (mul_pos (hp i) (by linarith [hev i]))

theorem ulaCov_inv_inv_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hev : ∀ i, h * p i < 2) : (ulaCov P h)⁻¹⁻¹ = ulaCov P h :=
  Matrix.nonsing_inv_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ulaCov_posDef_frame hU hdiag hp hev).det_pos.ne')

end Frame

/-- The tilt `Σ⁻¹m` of the stationary law `N(m, Σ)` written as `tiltedExpectation Σ⁻¹ (Σ⁻¹m)`. -/
noncomputable def statTilt (P : Matrix ι ι ℝ) (h : ℝ) (m : ι → ℝ) : ι → ℝ := (ulaCov P h)⁻¹ *ᵥ m

theorem tiltMean_statTilt {P : Matrix ι ι ℝ} {h : ℝ} (hS : (ulaCov P h).PosDef) (m : ι → ℝ) :
    tiltMean (ulaCov P h)⁻¹ (statTilt P h m) = m :=
  tiltMean_mulVec_self hS.inv m

/-- The `ℓ`-step conditional mean of the energy `½xᵀHx` from a start `x₀` under the ULA kernel on
`N(m, P⁻¹)`: the energy itself at `ℓ = 0`, the mean under the `ℓ`-step law otherwise. -/
noncomputable def condEnergy (P H : Matrix ι ι ℝ) (h : ℝ) (m : ι → ℝ) (ℓ : ℕ) (x₀ : ι → ℝ) : ℝ :=
  if ℓ = 0 then 1 / 2 * (x₀ ⬝ᵥ H *ᵥ x₀) else
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * ℓ)))⁻¹ (burnInTiltAnch P h ℓ m x₀)
      (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u))

/-- Lag-`ℓ` autocovariance of the energy along the stationary ULA chain: the covariance under the
stationary law `N(m, Σ)` between `½uᵀHu` and its `ℓ`-step conditional mean. -/
noncomputable def ulaAutoCov (P H : Matrix ι ι ℝ) (h : ℝ) (m : ι → ℝ) (ℓ : ℕ) : ℝ :=
  tiltedExpectation (ulaCov P h)⁻¹ (statTilt P h m)
      (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * condEnergy P H h m ℓ u) -
    tiltedExpectation (ulaCov P h)⁻¹ (statTilt P h m) (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u)) *
      tiltedExpectation (ulaCov P h)⁻¹ (statTilt P h m) (condEnergy P H h m ℓ)

/-- The long-run variance `τ² = c₀ + 2∑_{ℓ≥1} c_ℓ` of the energy along the stationary chain. -/
noncomputable def ulaLongRunVar (P H : Matrix ι ι ℝ) (h : ℝ) (m : ι → ℝ) : ℝ :=
  ulaAutoCov P H h m 0 + 2 * ∑' ℓ : ℕ, ulaAutoCov P H h m (ℓ + 1)

/-- The lag-sum variance functional `(1/n²)(n c₀ + 2∑_{j<n}(n − (j+1)) c_{j+1})` of the `n`-step
chain average. -/
noncomputable def lagSumVar (P H : Matrix ι ι ℝ) (h : ℝ) (m : ι → ℝ) (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 2 * (n * ulaAutoCov P H h m 0 +
    2 * ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * ulaAutoCov P H h m (j + 1))

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

/-! ### The conditional mean as a quadratic-plus-linear probe -/

/-- `condEnergy ℓ x₀ = ½x₀ᵀB_ℓx₀ + b_ℓ·x₀ + c_ℓ` for `ℓ ≥ 1`. -/
theorem condEnergy_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (m x₀ : ι → ℝ) :
    condEnergy P H h m ℓ x₀ = 1 / 2 * (x₀ ⬝ᵥ (U * diagonal (fun i => lam i * (1 - h * p i) ^ (2 *
      ℓ)) * Uᵀ) *ᵥ x₀) + x₀ ⬝ᵥ (U * diagonal (fun i => lam i * (1 - h * p i) ^ ℓ * (1 - (1 - h * p
      i) ^ ℓ)) * Uᵀ) *ᵥ m + (1 / 2 * ∑ i, lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p
      i) ^ (2 * ℓ))) + 1 / 2 * ∑ i, lam i * ((1 - (1 - h * p i) ^ ℓ) * (Uᵀ *ᵥ m) i) ^ 2) := by
  unfold condEnergy
  rw [if_neg (Nat.one_le_iff_ne_zero.1 hℓ), burnInAnch_energy_frame hU hdiag hp hh hev hdiagH hℓ m
      x₀,
    dotProduct_conj_diagonal_mulVec, dotProduct_conj_diagonal_mulVec₂]
  simp only [Matrix.mulVec_sub, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The autocovariance -/

theorem isHermitian_of_frame (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam) :
    H.IsHermitian := by
  rw [frame_eq_conj hU hdiagH]
  exact isHermitian_conj_diagonal U lam

/-- Lag 0: the stationary variance `½∑ᵢλᵢ²σᵢ⁴ + ∑ᵢλᵢ²σᵢ²m̂ᵢ²`. -/
theorem ulaAutoCov_zero_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (m : ι → ℝ) :
    ulaAutoCov P H h m 0 = 1 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 + ∑ i, lam i ^
      2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2 := by
  have hS := ulaCov_posDef_frame hU hdiag hp hev
  have hQ : (ulaCov P h)⁻¹.PosDef := hS.inv
  have hinv := ulaCov_inv_inv_frame hU hdiag hp hev
  have hH := isHermitian_of_frame hU hdiagH
  have hc0 : condEnergy P H h m 0 = fun x₀ => 1 / 2 * (x₀ ⬝ᵥ H *ᵥ x₀) := funext fun x₀ => by
    unfold condEnergy
    exact if_pos rfl
  have e1 : (fun u : ι → ℝ => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * (1 / 2 * (u ⬝ᵥ H *ᵥ u))) =
      fun u => (1 / 4 : ℝ) * (u ⬝ᵥ H *ᵥ u) ^ 2 := by
    funext u
    ring
  unfold ulaAutoCov
  simp only [hc0]
  rw [e1, tiltedExpectation_const_mul, tiltedExpectation_const_mul]
  have hvar := tiltedVar_quadForm hQ (statTilt P h m) hH
  rw [tiltMean_statTilt hS, hinv] at hvar
  rw [show ∀ a b : ℝ, 1 / 4 * a - 1 / 2 * b * (1 / 2 * b) = 1 / 4 * (a - b ^ 2) from
    fun a b => by ring, hvar, ulaCov_eq_conj_frame hU hdiag hp hev, frame_eq_conj hU hdiagH]
  simp only [conj_mul_conj_frame hU, Matrix.diagonal_mul_diagonal, sum_sum_conj_mul_conj hU,
      conj_mulVec_dotProduct_conj_mulVec hU, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Lag `ℓ ≥ 1`: `½∑ᵢλᵢ²σᵢ⁴ρᵢ^{2ℓ} + ∑ᵢλᵢ²σᵢ²m̂ᵢ²ρᵢ^ℓ`. -/
theorem ulaAutoCov_eq_of_pos (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (m : ι → ℝ) :
    ulaAutoCov P H h m ℓ = 1 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 * (1 - h * p
      i) ^ (2 * ℓ) + ∑ i, lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2 * (1 - h * p
      i) ^ ℓ := by
  have hS := ulaCov_posDef_frame hU hdiag hp hev
  have hQ : (ulaCov P h)⁻¹.PosDef := hS.inv
  have hinv := ulaCov_inv_inv_frame hU hdiag hp hev
  have hH := isHermitian_of_frame hU hdiagH
  have hcond : condEnergy P H h m ℓ = fun x₀ => 1 / 2 * (x₀ ⬝ᵥ (U * diagonal (fun i => lam i * (1 -
      h * p i) ^ (2 * ℓ)) * Uᵀ) *ᵥ x₀) + x₀ ⬝ᵥ (U * diagonal (fun i => lam i * (1 - h * p i) ^ ℓ *
      (1 - (1 - h * p i) ^ ℓ)) * Uᵀ) *ᵥ m + (1 / 2 * ∑ i, lam i * (1 / (p i * (1 - h * p i / 2)) *
      (1 - (1 - h * p i) ^ (2 * ℓ))) + 1 / 2 * ∑ i, lam i * ((1 - (1 - h * p i) ^ ℓ) * (Uᵀ *ᵥ m) i)
      ^ 2) := funext fun x₀ => condEnergy_eq hU hdiag hp hh hev hdiagH hℓ m x₀
  unfold ulaAutoCov
  simp only [hcond]
  rw [tiltedCov_energy_quadProbe_add_const hQ (statTilt P h m) hH (isHermitian_conj_diagonal U _)
    _ _, tiltedCov_quadForm_quadProbe hQ (statTilt P h m) hH (isHermitian_conj_diagonal U _) _,
    tiltMean_statTilt hS, hinv, ulaCov_eq_conj_frame hU hdiag hp hev, frame_eq_conj hU hdiagH]
  simp only [conj_mul_conj_frame hU, Matrix.diagonal_mul_diagonal, sum_sum_conj_mul_conj hU,
      conj_mulVec_dotProduct_conj_mulVec hU, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The stationary energy autocovariance of ULA**, all lags. -/
theorem ulaAutoCov_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (ℓ : ℕ) (m :
        ι → ℝ) :
    ulaAutoCov P H h m ℓ = 1 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 * (1 - h * p
      i) ^ (2 * ℓ) + ∑ i, lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2 * (1 - h * p
      i) ^ ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · subst hℓ
    rw [ulaAutoCov_zero_eq hU hdiag hp hev hdiagH m]
    simp only [mul_zero, pow_zero, mul_one]
  · exact ulaAutoCov_eq_of_pos hU hdiag hp hh hev hdiagH hℓ m

/-! ### The long-run variance -/

omit [Fintype ι] [DecidableEq ι] in
theorem abs_rho_lt_one (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (i : ι) :
    |1 - h * p i| < 1 ∧ |(1 - h * p i) ^ 2| < 1 :=
  ⟨abs_one_sub_mul_lt_one hh (hp i) (hev i), by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg _) (abs_one_sub_mul_lt_one hh (hp i) (hev i)) two_ne_zero⟩

theorem ulaAutoCov_summable (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (m : ι → ℝ) :
    Summable (fun ℓ : ℕ => ulaAutoCov P H h m ℓ) := by
  have e : ∀ ℓ : ℕ, ulaAutoCov P H h m ℓ = ∑ i, (1 / 2 * (lam i * (1 / (p i * (1 - h * p i / 2)))) ^
      2 * ((1 - h * p i) ^ 2) ^ ℓ + lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2 *
      (1 - h * p i) ^ ℓ) := by
    intro ℓ
    rw [ulaAutoCov_eq hU hdiag hp hh hev hdiagH ℓ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul]; ring
  simp_rw [e]
  exact summable_sum fun i _ =>
    ((summable_geometric_of_abs_lt_one (abs_rho_lt_one hp hh hev i).2).mul_left _).add
      ((summable_geometric_of_abs_lt_one (abs_rho_lt_one hp hh hev i).1).mul_left _)

/-- **The long-run variance** `τ² = ½∑ᵢλᵢ²σᵢ⁴(1+ρᵢ²)/(1−ρᵢ²) + ∑ᵢλᵢ²σᵢ²m̂ᵢ²(1+ρᵢ)/(1−ρᵢ)`. -/
theorem ulaLongRunVar_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (m : ι → ℝ) :
    ulaLongRunVar P H h m = 1 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 * ((1 + (1 -
      h * p i) ^ 2) / (1 - (1 - h * p i) ^ 2)) + ∑ i, lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) *
      (Uᵀ *ᵥ m) i ^ 2 * ((1 + (1 - h * p i)) / (1 - (1 - h * p i))) := by
  have hρ := abs_rho_lt_one hp hh hev
  have hac : ∀ ℓ : ℕ, ulaAutoCov P H h m (ℓ + 1) = ∑ i, (1 / 2 * (lam i * (1 / (p i * (1 - h * p i /
      2)))) ^ 2 * ((1 - h * p i) ^ 2) ^ ℓ * (1 - h * p i) ^ 2 + lam i ^ 2 * (1 / (p i * (1 - h * p i
      / 2))) * (Uᵀ *ᵥ m) i ^ 2 * ((1 - h * p i) ^ ℓ * (1 - h * p i))) := by
    intro ℓ
    rw [ulaAutoCov_eq hU hdiag hp hh hev hdiagH (ℓ + 1) m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul]; ring
  have hs1 : ∀ i, Summable (fun ℓ : ℕ => 1 / 2 * (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 * ((1
      - h * p i) ^ 2) ^ ℓ * (1 - h * p i) ^ 2) := fun i => ((summable_geometric_of_abs_lt_one (hρ
      i).2).mul_left _).mul_right _
  have hs2 : ∀ i, Summable (fun ℓ : ℕ => lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^
      2 * ((1 - h * p i) ^ ℓ * (1 - h * p i))) := fun i => ((summable_geometric_of_abs_lt_one (hρ
      i).1).mul_right _).mul_left _
  have hs : ∀ i, Summable (fun ℓ : ℕ => 1 / 2 * (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 * ((1
      - h * p i) ^ 2) ^ ℓ * (1 - h * p i) ^ 2 + lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ
      m) i ^ 2 * ((1 - h * p i) ^ ℓ * (1 - h * p i))) := fun i => (hs1 i).add (hs2 i)
  have hval : ∀ i, ∑' ℓ : ℕ, (1 / 2 * (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 * ((1 - h * p i)
      ^ 2) ^ ℓ * (1 - h * p i) ^ 2 + lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2 *
      ((1 - h * p i) ^ ℓ * (1 - h * p i))) = 1 / 2 * (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 *
      (1 - (1 - h * p i) ^ 2)⁻¹ * (1 - h * p i) ^ 2 + lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) *
      (Uᵀ *ᵥ m) i ^ 2 * ((1 - (1 - h * p i))⁻¹ * (1 - h * p i)) := by
    intro i
    rw [(hs1 i).tsum_add (hs2 i)]
    simp only [tsum_mul_left, tsum_mul_right, tsum_geometric_of_abs_lt_one (hρ i).2,
      tsum_geometric_of_abs_lt_one (hρ i).1]
  unfold ulaLongRunVar
  rw [ulaAutoCov_zero_eq hU hdiag hp hev hdiagH m]
  simp_rw [hac]
  rw [Summable.tsum_finsetSum fun i _ => hs i]
  simp only [hval, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : 1 - (1 - h * p i) ≠ 0 := (sub_pos.2 (abs_lt.1 (hρ i).1).2).ne'
  have h2 : 1 - (1 - h * p i) ^ 2 ≠ 0 := (sub_pos.2 (abs_lt.1 (hρ i).2).2).ne'
  generalize 1 / (p i * (1 - h * p i / 2)) = s
  field_simp
  ring

/-- The long-run variance in sampler variables: `∑ᵢλᵢ²(1+ρᵢ²)/(4hpᵢ³κᵢ³) + 2∑ᵢλᵢ²m̂ᵢ²/(hpᵢ²)`. -/
theorem ulaLongRunVar_eq_sampler (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 <
    p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (m : ι → ℝ) :
    ulaLongRunVar P H h m =
      ∑ i, lam i ^ 2 * (1 + (1 - h * p i) ^ 2) / (4 * h * p i ^ 3 * (1 - h * p i / 2) ^ 3) +
        2 * ∑ i, lam i ^ 2 * (Uᵀ *ᵥ m) i ^ 2 / (h * p i ^ 2) := by
  rw [ulaLongRunVar_eq hU hdiag hp hh hev hdiagH m]
  have hρ := abs_rho_lt_one hp hh hev
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpi : p i ≠ 0 := (hp i).ne'
  have hh' : h ≠ 0 := hh.ne'
  have hκ : 1 - h * p i / 2 ≠ 0 := by linarith [hev i]
  have hκ' : 2 - h * p i ≠ 0 := by linarith [hev i]
  have hκ'' : 2 - p i * h ≠ 0 := by linarith [hev i]
  have e1 : 1 - (1 - h * p i) = h * p i := by ring
  have e2 : 1 - (1 - h * p i) ^ 2 = h * p i * (2 - h * p i) := by ring
  have e3 : 1 + (1 - h * p i) = 2 - h * p i := by ring
  rw [e1, e2, e3]
  field_simp
  ring

theorem ulaLongRunVar_nonneg (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (m : ι → ℝ)
        : 0 ≤ ulaLongRunVar P H h m := by
  rw [ulaLongRunVar_eq hU hdiag hp hh hev hdiagH m]
  have hρ := abs_rho_lt_one hp hh hev
  refine add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_))
    (Finset.sum_nonneg fun i _ => ?_)
  · exact mul_nonneg (sq_nonneg _)
      (div_nonneg (by positivity) (sub_pos.2 (abs_lt.1 (hρ i).2).2).le)
  · have hσ : 0 ≤ 1 / (p i * (1 - h * p i / 2)) := div_nonneg one_pos.le (mul_pos (hp i) (by
      linarith [hev i])).le
    have hn : 0 ≤ 1 + (1 - h * p i) := by linarith [(abs_lt.1 (hρ i).1).1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hσ) (sq_nonneg _))
      (div_nonneg hn (sub_pos.2 (abs_lt.1 (hρ i).1).2).le)

/-! ### The exact finite-`n` lag-sum variance of the chain average -/

/-- `(1/n²)(n c₀ + 2∑_{j<n}(n−(j+1))c_{j+1}) = (1/n²)∑ᵢ[aᵢ(n + 2G_n(ρᵢ²)) + bᵢ(n + 2G_n(ρᵢ))]`. -/
theorem lagSumVar_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (m : ι → ℝ)
        (n : ℕ) :
    lagSumVar P H h m n = 1 / (n : ℝ) ^ 2 * ∑ i, (1 / 2 * (lam i * (1 / (p i * (1 - h * p i / 2))))
      ^ 2 * (n + 2 * (((1 - h * p i) ^ 2) * (n * (1 - ((1 - h * p i) ^ 2)) - (1 - ((1 - h * p i) ^
      2) ^ n)) / (1 - ((1 - h * p i) ^ 2)) ^ 2)) + lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ
      *ᵥ m) i ^ 2 * (n + 2 * ((1 - h * p i) * (n * (1 - (1 - h * p i)) - (1 - (1 - h * p i) ^ n)) /
      (1 - (1 - h * p i)) ^ 2))) := by
  have hρ := abs_rho_lt_one hp hh hev
  have hac : ∀ j : ℕ, ulaAutoCov P H h m (j + 1) = ∑ i, (1 / 2 * (lam i * (1 / (p i * (1 - h * p i /
      2)))) ^ 2 * ((1 - h * p i) ^ 2) ^ (j + 1) + lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ
      *ᵥ m) i ^ 2 * (1 - h * p i) ^ (j + 1)) := by
    intro j
    rw [ulaAutoCov_eq hU hdiag hp hh hev hdiagH (j + 1) m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul]; ring
  have hc0 : ulaAutoCov P H h m 0 = ∑ i, (1 / 2 * (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 +
      lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2) := by
    rw [ulaAutoCov_zero_eq hU hdiag hp hev hdiagH m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold lagSumVar
  rw [hc0]
  simp_rw [hac]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ j ∈ Finset.range n, 2 * (((n : ℝ) - (j + 1)) * (1 / 2 * (lam i * (1 / (p i * (1 - h * p
      i / 2)))) ^ 2 * ((1 - h * p i) ^ 2) ^ (j + 1) + lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) *
      (Uᵀ *ᵥ m) i ^ 2 * (1 - h * p i) ^ (j + 1))) = 2 * (1 / 2 * (lam i * (1 / (p i * (1 - h * p i /
      2)))) ^ 2) * (((n : ℝ) - (j + 1)) * ((1 - h * p i) ^ 2) ^ (j + 1)) + 2 * (lam i ^ 2 * (1 / (p
      i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2) * (((n : ℝ) - (j + 1)) * (1 - h * p i) ^ (j + 1))
      := fun j _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_range_cesaro_geometric _ (abs_lt.1 (hρ i).2).2.ne,
    sum_range_cesaro_geometric _ (abs_lt.1 (hρ i).1).2.ne]
  ring

/-- `Var(Ȳ_n) = τ²/n − (2/n²)∑ᵢ[aᵢρᵢ²(1−ρᵢ^{2n})/(1−ρᵢ²)² + bᵢρᵢ(1−ρᵢⁿ)/(1−ρᵢ)²]`: `n·Var(Ȳ_n) →
τ²`. -/
theorem lagSumVar_eq_longRun_sub (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 <
    p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (m : ι → ℝ)
        {n : ℕ} (hn : n ≠ 0) :
    lagSumVar P H h m n = ulaLongRunVar P H h m / n - 2 / (n : ℝ) ^ 2 * ∑ i, (1 / 2 * (lam i * (1 /
      (p i * (1 - h * p i / 2)))) ^ 2 * (((1 - h * p i) ^ 2) * (1 - ((1 - h * p i) ^ 2) ^ n) / (1 -
      ((1 - h * p i) ^ 2)) ^ 2) + lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2 *
      ((1 - h * p i) * (1 - (1 - h * p i) ^ n) / (1 - (1 - h * p i)) ^ 2)) := by
  rw [lagSumVar_eq hU hdiag hp hh hev hdiagH m n, ulaLongRunVar_eq hU hdiag hp hh hev hdiagH m]
  have hρ := abs_rho_lt_one hp hh hev
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [add_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : 1 - (1 - h * p i) ≠ 0 := (sub_pos.2 (abs_lt.1 (hρ i).1).2).ne'
  have h2 : 1 - (1 - h * p i) ^ 2 ≠ 0 := (sub_pos.2 (abs_lt.1 (hρ i).2).2).ne'
  generalize 1 / (p i * (1 - h * p i / 2)) = s
  field_simp
  ring

end Frame

end Laplace.Sampler
