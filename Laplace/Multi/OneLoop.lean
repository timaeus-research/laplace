/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.TwoD.Rosenbrock
import Laplace.OneD.MomentSecondOrder
import Laplace.OneD.IntegralRemainder

/-!
# The one-loop covariance formula

For `e^{-tL}` with `L = ½ wᵀHw + (1/6) T w³ + (1/24) Q w⁴ + …` the connected two-point
function to one loop is

  `Cov = S + S Π S`,  `S = (tH)⁻¹`,  `Π = -(t/2)(Q:S) + (t²/2) TSST + (t²/2) T·S·(T:S)`,

with `(Q:S)ᵢⱼ = Qᵢⱼₖₗ Sₖₗ` (quartic tadpole), `(TSST)ᵢⱼ = Tᵢₖₗ Sₖₖ' Sₗₗ' Tⱼₖ'ₗ'` (cubic bubble) and
`(T·S·(T:S))ᵢⱼ = Tᵢⱼₖ Sₖₗ (T:S)ₗ` (cubic tadpole on the line). This file defines the functional
`oneLoopCov` on `Fin d` and proves its two checkable instances:

* in one dimension it is `1/(λt) + (α²/λ⁴ − γ/(2λ³))/t²` (`oneLoopCov_oneDim`), and this is the
  true second-order variance of the anharmonic Gibbs law (`var_anharmonic_second_order`, from the
  seabed's second-order moment rates);
* for the Rosenbrock potential in two dimensions it equals the exact covariance at every `t`
  (`oneLoopCov_rosenbrock`): `Π = 2a² (2, -1)(2, -1)ᵀ` and `SΠS = (2/t²) e_y e_yᵀ`, the correction
  in `rosenCov_eq_laplace_add`. The series terminates.
-/

open Matrix Filter Topology Laplace.TwoD Laplace.OneD

namespace Laplace.Multi

variable {d : ℕ}

/-! ### The functional -/

/-- The quartic tadpole `(Q:S)ᵢⱼ = ∑ₖₗ Qᵢⱼₖₗ Sₖₗ`. -/
noncomputable def contractQ (Q : Fin d → Fin d → Fin d → Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, Q i j k l * S k l

/-- `(T:S)ₗ = ∑ₘₙ Tₗₘₙ Sₘₙ`. -/
noncomputable def contractT (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    Fin d → ℝ :=
  fun l => ∑ m, ∑ n, T l m n * S m n

/-- The cubic bubble `(TSST)ᵢⱼ = ∑ Tᵢₖₗ Sₖₘ Sₗₙ Tⱼₘₙ`. -/
noncomputable def bubble (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, ∑ m, ∑ n, T i k l * S k m * S l n * T j m n

/-- The cubic tadpole on the line `(T·S·(T:S))ᵢⱼ = ∑ₖₗ Tᵢⱼₖ Sₖₗ (T:S)ₗ`. -/
noncomputable def tadpoleLine (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, T i j k * S k l * contractT T S l

/-- `Π = -(t/2)(Q:S) + (t²/2) TSST + (t²/2) T·S·(T:S)`. -/
noncomputable def oneLoopPi (t : ℝ) (T : Fin d → Fin d → Fin d → ℝ)
    (Q : Fin d → Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (-(t / 2)) • contractQ Q S + (t ^ 2 / 2) • bubble T S + (t ^ 2 / 2) • tadpoleLine T S

/-- The one-loop covariance `S + S Π S` with `S = (tH)⁻¹`. -/
noncomputable def oneLoopCov (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (Q : Fin d → Fin d → Fin d → Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (t • H)⁻¹ + (t • H)⁻¹ * oneLoopPi t T Q (t • H)⁻¹ * (t • H)⁻¹

/-! ### One dimension -/

theorem smul_single_inv {lam t : ℝ} (hlam : lam ≠ 0) (ht : t ≠ 0) :
    (t • (!![lam] : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = !![1 / (t * lam)] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply]
  field_simp

/-- **The note's one-dimensional formula**: `Var = 1/(λt) + (α²/λ⁴ − γ/(2λ³))/t²`. -/
theorem oneLoopCov_oneDim {lam t : ℝ} (alpha gamma : ℝ) (hlam : lam ≠ 0) (ht : t ≠ 0) :
    oneLoopCov t !![lam] (fun _ _ _ => alpha) (fun _ _ _ _ => gamma) =
      !![1 / (lam * t) + (alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3)) / t ^ 2] := by
  rw [oneLoopCov, smul_single_inv hlam ht]
  ext i j
  fin_cases i; fin_cases j
  simp [oneLoopPi, contractQ, bubble, tadpoleLine, contractT, Matrix.vecHead, Pi.smul_apply,
    smul_eq_mul]
  field_simp
  ring

/-- The second-order second moment of the anharmonic Gibbs law as a limit:
`t (t⟨x²⟩ − 1/λ) → (45A² − 12B)/λ`. -/
theorem secondMoment_anharmonic_second_order {lam alpha gamma : ℝ} (hlam : 0 < lam)
    (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Tendsto (fun t : ℝ => t * (t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 2) - 1 / lam)) atTop
      (𝓝 ((45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma) / lam)) := by
  obtain ⟨K, T, hK, hT, hb⟩ := secondMoment_anharmonic_order2_rate hlam hgamma hdisc
  set c := (45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma) / lam with hc
  have hev : ∀ᶠ t in atTop,
      |t * (t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2) - 1 / lam) - c| ≤ K / Real.sqrt t := by
    filter_upwards [eventually_ge_atTop T, eventually_gt_atTop (0 : ℝ)] with t htT ht
    have hb' : |t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2) - 1 / lam - c / t| ≤ K / (t * Real.sqrt t) := by
      rw [hc, div_div]
      exact hb htT
    have heq : t * (t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2) - 1 / lam - c / t) =
        t * (t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2) - 1 / lam) - c := by
      rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ c ht.ne']
    rw [← heq, abs_mul, abs_of_pos ht]
    calc t * |t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2) - 1 / lam - c / t| ≤ t * (K / (t * Real.sqrt t)) :=
          mul_le_mul_of_nonneg_left hb' ht.le
      _ = K / Real.sqrt t := by field_simp
  have hk : Tendsto (fun t : ℝ => K / Real.sqrt t) atTop (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    simpa [div_eq_mul_inv] using hi.const_mul K
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun t => abs_nonneg _) hev hk

/-- **The one-dimensional one-loop formula is the true second-order variance**: for
`L = λx²/2 + αx³/6 + γx⁴/24` with `λ, γ > 0`, `α² < 3λγ`,
`t² (Var_t[x] − 1/(λt)) → α²/λ⁴ − γ/(2λ³)`. -/
theorem var_anharmonic_second_order {lam alpha gamma : ℝ} (hlam : 0 < lam)
    (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Tendsto (fun t : ℝ => t ^ 2 * (Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
      (fun x => x) (fun x => x) - 1 / (lam * t))) atTop
      (𝓝 (alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3))) := by
  have h2 := secondMoment_anharmonic_second_order hlam hgamma hdisc
  have h1 := mean_anharmonic_asymptotic hlam hgamma hdisc
  have hlim := h2.sub (h1.pow 2)
  have hA : cubicScale lam alpha ^ 2 = alpha ^ 2 / (36 * lam ^ 3) := by
    unfold cubicScale
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hlam.le]
    ring
  have hval : (45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma) / lam -
      (-alpha / (2 * lam ^ 2)) ^ 2 = alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3) := by
    rw [hA]
    unfold quarticScale
    field_simp
    ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Laplace.gibbsCov, ← pow_two]
  field_simp
  ring

/-! ### Rosenbrock in two dimensions -/

/-- The cubic Taylor tensor of the Rosenbrock potential at `(1, 1)`: `T_zzz = 12a`,
`T_zzw = T_zwz = T_wzz = −2a`, all else `0`. -/
noncomputable def rosenT (a : ℝ) : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  ![![![12 * a, -2 * a], ![-2 * a, 0]], ![![-2 * a, 0], ![0, 0]]]

/-- The quartic Taylor tensor of the Rosenbrock potential at `(1, 1)`: `Q_zzzz = 12a`. -/
noncomputable def rosenQ (a : ℝ) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun i j k l => if i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 then 12 * a else 0

/-- **Taylor identity** certifying `rosenT`, `rosenQ`: the Rosenbrock potential is exactly its
quadratic, cubic and quartic Taylor terms at `(1, 1)`. -/
theorem rosenbrock_taylor_full (a z w : ℝ) :
    rosenbrock a (1 + z, 1 + w) =
      (1 / 2) * (![z, w] ⬝ᵥ (rosenHess a).mulVec ![z, w])
        + (1 / 6) * ∑ i, ∑ j, ∑ k, rosenT a i j k * ![z, w] i * ![z, w] j * ![z, w] k
        + (1 / 24) * ∑ i, ∑ j, ∑ k, ∑ l,
            rosenQ a i j k l * ![z, w] i * ![z, w] j * ![z, w] k * ![z, w] l := by
  simp [rosenbrock, rosenHess, rosenT, rosenQ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `Σ = t (tH)⁻¹` for Rosenbrock. -/
noncomputable def rosenSigma (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 2, 4 + 1 / a]

theorem rosenHess_smul_inv {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (t • rosenHess a)⁻¹ = (1 / t) • rosenSigma a := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rosenHess, rosenSigma, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem contractQ_rosenbrock (a t : ℝ) :
    contractQ (rosenQ a) ((1 / t) • rosenSigma a) = (12 * a / t) • !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [contractQ, rosenQ, rosenSigma, Fin.sum_univ_two]
  ring

theorem contractT_rosenbrock (a t : ℝ) (ha : a ≠ 0) :
    contractT (rosenT a) ((1 / t) • rosenSigma a) = ![4 * a / t, -2 * a / t] := by
  ext l
  fin_cases l <;> simp [contractT, rosenT, rosenSigma, Fin.sum_univ_two] <;> field_simp
  ring

theorem bubble_rosenbrock (a t : ℝ) (ha : a ≠ 0) :
    bubble (rosenT a) ((1 / t) • rosenSigma a) =
      (1 / t ^ 2) • !![16 * a ^ 2 + 8 * a, -8 * a ^ 2; -8 * a ^ 2, 4 * a ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bubble, rosenT, rosenSigma, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem tadpoleLine_rosenbrock (a t : ℝ) (ha : a ≠ 0) :
    tadpoleLine (rosenT a) ((1 / t) • rosenSigma a) = (4 * a / t ^ 2) • !![1, 0; 0, 0] := by
  ext i j
  simp only [tadpoleLine, Matrix.of_apply, contractT_rosenbrock a t ha]
  fin_cases i <;> fin_cases j <;> simp [rosenT, rosenSigma, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- `Π = 2a² (2, −1)(2, −1)ᵀ` for Rosenbrock. -/
theorem oneLoopPi_rosenbrock (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    oneLoopPi t (rosenT a) (rosenQ a) ((1 / t) • rosenSigma a) =
      (2 * a ^ 2) • !![4, -2; -2, 1] := by
  rw [oneLoopPi, contractQ_rosenbrock a t, bubble_rosenbrock a t ha, tadpoleLine_rosenbrock a t ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-- **The one-loop formula is exact for Rosenbrock**: `S + SΠS = rosenCov a t` at every `t`. -/
theorem oneLoopCov_rosenbrock {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    oneLoopCov t (rosenHess a) (rosenT a) (rosenQ a) = rosenCov a t := by
  rw [rosenCov_eq_laplace_add ha ht, oneLoopCov, rosenHess_smul_inv ha ht,
    oneLoopPi_rosenbrock a t ha.ne' ht.ne']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rosenSigma] <;> field_simp <;> ring

end Laplace.Multi
