/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallPhaseData
import Laplace.Multi.WallKernelExplicit

/-!
# The normalised branch integrand

Astra's lemmas 1 and 2 (`research_kernel_asymptotics_v1`): with the phase data of a chart and a
nonnegative loss, the Boltzmann integrand of the fibre kernel at truth `s`, on the branch
`u = (w, σV)` with `V = (|s|/|c(w)|)^{1/q_k}`, reads
`e^{−t |a(u)| |s|^ν ∏|w_j|^{κ_j}} · φ(rep u) · wt(u) |b(u)| · (1/q_k) |s|^p ∏ |w_j|^{r_j}`,
with `ν = k_k/q_k`, `κ_j = k_j − q_j ν`, `p = (h_k+1)/q_k − 1`, `r_j = h_j − q_j (p+1)`
(`WallChartsData.Phase.branch_integrand_eq`), and the unit bounds sandwich it between the
constant-unit integrands with `a = M_a` and `a = m_a` (`branch_integrand_le`,
`branch_integrand_ge`). The moving cutoff is the hypothesis `u ∈ closedBall 0 ρ_i`; off the open
ball the density vanishes.
-/

open Real MeasureTheory Set

namespace Laplace.Multi

variable {m : ℕ}

/-- The solved point of chart `i` on the branch `σ` at truth `s` over `w`. -/
noncomputable def WallChartsData.solvedPt {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}
    (D : WallChartsData m ℓ L') (i : D.ι) (σ s : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  (D.k i).insertNth (σ * solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) w) (D.q i (D.k i)) s) w

namespace WallChartsData.Phase

variable {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)} {D : WallChartsData m ℓ L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- The loss exponent `ν = k_k / q_k` of chart `i`. -/
noncomputable def nu (i : D.ι) : ℝ := (P.kF i (D.k i) : ℝ) / D.q i (D.k i)

/-- The transverse loss exponents `κ_j = k_j − q_j ν`. -/
noncomputable def kappa (i : D.ι) (j : Fin m) : ℝ :=
  (P.kF i ((D.k i).succAbove j) : ℝ) -
    D.q i ((D.k i).succAbove j) * (P.kF i (D.k i) : ℝ) / D.q i (D.k i)

/-- The density exponent `p = (h_k + 1)/q_k − 1`. -/
noncomputable def pExp (i : D.ι) : ℝ := ((P.hJ i (D.k i) : ℝ) + 1) / D.q i (D.k i) - 1

/-- The transverse density exponents `r_j = h_j − q_j (h_k + 1)/q_k`. -/
noncomputable def rExp (i : D.ι) (j : Fin m) : ℝ :=
  (P.hJ i ((D.k i).succAbove j) : ℝ) -
    D.q i ((D.k i).succAbove j) * ((P.hJ i (D.k i) : ℝ) + 1) / D.q i (D.k i)

/-- The loss on the fibre: `F(rep u) = |a(u)| |s|^ν ∏ |w_j|^{κ_j}` at the solved point. -/
theorem loss_solvedPt (i : D.ι) (hS : |D.S i| = 1) {s : ℝ} (hs : s ≠ 0) {w : Fin m → ℝ}
    (hw : ∀ j, w j ≠ 0) {σ : ℝ} (hσ : |σ| = 1)
    (hu : D.solvedPt i σ s w ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i))
    (hF0 : 0 ≤ F (D.rep i (D.solvedPt i σ s w))) :
    F (D.rep i (D.solvedPt i σ s w)) =
      |P.a i (D.solvedPt i σ s w)| * (|s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j) := by
  rw [← abs_of_nonneg hF0, P.abs_loss i hu]
  congr 1
  have h := abs_monomial_insertNth_solved (D.k i) hS (D.q i) (P.kF i) hs hw σ hσ
  rw [Finset.abs_prod] at h
  simp only [abs_pow] at h
  exact h

/-- The density times the fibre factor at the solved point:
`dens(u) V/(q_k|s|) = wt(u) |b(u)| (1/q_k) |s|^p ∏ |w_j|^{r_j}`. -/
theorem dens_mul_solvedPt (i : D.ι) (hS : |D.S i| = 1) {s : ℝ} (hs : s ≠ 0) {w : Fin m → ℝ}
    (hw : ∀ j, w j ≠ 0) {σ : ℝ} (hσ : |σ| = 1)
    (hu : D.solvedPt i σ s w ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i)) :
    D.dens i (D.solvedPt i σ s w) *
        (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) w) (D.q i (D.k i)) s /
          (D.q i (D.k i) * |s|)) =
      P.wt i (D.solvedPt i σ s w) * |P.b i (D.solvedPt i σ s w)| *
        (1 / D.q i (D.k i) * |s| ^ P.pExp i * ∏ j, |w j| ^ P.rExp i j) := by
  rw [P.dens_eq i _ hu, abs_mul]
  have h : |∏ j, D.solvedPt i σ s w j ^ P.hJ i j| *
      (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) w) (D.q i (D.k i)) s /
        (D.q i (D.k i) * |s|)) =
      1 / D.q i (D.k i) * |s| ^ P.pExp i * ∏ j, |w j| ^ P.rExp i j :=
    density_insertNth_solved (D.k i) hS (D.q_pos i) (P.hJ i) hs hw σ hσ
  rw [mul_assoc, mul_assoc, h, ← mul_assoc]

/-- **The normalised branch integrand** for the Boltzmann weight `e^{−tF} φ`. -/
theorem branch_integrand_eq (i : D.ι) (hS : |D.S i| = 1) (t : ℝ) (φ : (Fin (m + 1) → ℝ) → ℝ)
    {s : ℝ} (hs : s ≠ 0) {w : Fin m → ℝ} (hw : ∀ j, w j ≠ 0) {σ : ℝ} (hσ : |σ| = 1)
    (hu : D.solvedPt i σ s w ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i))
    (hF0 : 0 ≤ F (D.rep i (D.solvedPt i σ s w))) :
    exp (-(t * F (D.rep i (D.solvedPt i σ s w)))) * φ (D.rep i (D.solvedPt i σ s w)) *
        D.dens i (D.solvedPt i σ s w) *
        (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) w) (D.q i (D.k i)) s /
          (D.q i (D.k i) * |s|)) =
      exp (-(t * (|P.a i (D.solvedPt i σ s w)| * (|s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j)))) *
        φ (D.rep i (D.solvedPt i σ s w)) *
        (P.wt i (D.solvedPt i σ s w) * |P.b i (D.solvedPt i σ s w)| *
          (1 / D.q i (D.k i) * |s| ^ P.pExp i * ∏ j, |w j| ^ P.rExp i j)) := by
  rw [P.loss_solvedPt i hS hs hw hσ hu hF0, mul_assoc, P.dens_mul_solvedPt i hS hs hw hσ hu]

/-- **The moving-unit sandwich (upper).** With `t ≥ 0`, `φ ≥ 0`, the unit is replaced by its lower
bound `m_a` in the exponent. -/
theorem branch_integrand_le (i : D.ι) (hS : |D.S i| = 1) {t : ℝ} (ht : 0 ≤ t)
    {φ : (Fin (m + 1) → ℝ) → ℝ} (hφ : ∀ z, 0 ≤ φ z) {s : ℝ} (hs : s ≠ 0) {w : Fin m → ℝ}
    (hw : ∀ j, w j ≠ 0) {σ : ℝ} (hσ : |σ| = 1)
    (hu : D.solvedPt i σ s w ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i))
    (hF0 : 0 ≤ F (D.rep i (D.solvedPt i σ s w))) :
    exp (-(t * F (D.rep i (D.solvedPt i σ s w)))) * φ (D.rep i (D.solvedPt i σ s w)) *
        D.dens i (D.solvedPt i σ s w) *
        (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) w) (D.q i (D.k i)) s /
          (D.q i (D.k i) * |s|)) ≤
      exp (-(t * (P.ma i * (|s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j)))) *
        φ (D.rep i (D.solvedPt i σ s w)) *
        (P.wt i (D.solvedPt i σ s w) * P.Mb i *
          (1 / D.q i (D.k i) * |s| ^ P.pExp i * ∏ j, |w j| ^ P.rExp i j)) := by
  rw [P.branch_integrand_eq i hS t φ hs hw hσ hu hF0]
  have hmono : 0 ≤ |s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j :=
    mul_nonneg (rpow_nonneg (abs_nonneg _) _)
      (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (abs_nonneg _) _)
  have hdens : 0 ≤ 1 / D.q i (D.k i) * |s| ^ P.pExp i * ∏ j, |w j| ^ P.rExp i j :=
    mul_nonneg (mul_nonneg (by positivity) (rpow_nonneg (abs_nonneg _) _))
      (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (abs_nonneg _) _)
  have hexp : exp (-(t * (|P.a i (D.solvedPt i σ s w)| *
      (|s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j)))) ≤
      exp (-(t * (P.ma i * (|s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j)))) := by
    rw [exp_le_exp]
    have := (P.a_bounds i _ hu).1
    nlinarith [mul_nonneg ht hmono]
  refine mul_le_mul (mul_le_mul_of_nonneg_right hexp (hφ _)) ?_ ?_
    (mul_nonneg (exp_pos _).le (hφ _))
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (P.b_bounds i _ hu).2 (P.wt_nonneg i _)) hdens
  · exact mul_nonneg (mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)) hdens

/-- **The moving-unit sandwich (lower).** -/
theorem branch_integrand_ge (i : D.ι) (hS : |D.S i| = 1) {t : ℝ} (ht : 0 ≤ t)
    {φ : (Fin (m + 1) → ℝ) → ℝ} (hφ : ∀ z, 0 ≤ φ z) {s : ℝ} (hs : s ≠ 0) {w : Fin m → ℝ}
    (hw : ∀ j, w j ≠ 0) {σ : ℝ} (hσ : |σ| = 1)
    (hu : D.solvedPt i σ s w ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i))
    (hF0 : 0 ≤ F (D.rep i (D.solvedPt i σ s w))) :
    exp (-(t * (P.Ma i * (|s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j)))) *
        φ (D.rep i (D.solvedPt i σ s w)) *
        (P.wt i (D.solvedPt i σ s w) * P.mb i *
          (1 / D.q i (D.k i) * |s| ^ P.pExp i * ∏ j, |w j| ^ P.rExp i j)) ≤
      exp (-(t * F (D.rep i (D.solvedPt i σ s w)))) * φ (D.rep i (D.solvedPt i σ s w)) *
        D.dens i (D.solvedPt i σ s w) *
        (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) w) (D.q i (D.k i)) s /
          (D.q i (D.k i) * |s|)) := by
  rw [P.branch_integrand_eq i hS t φ hs hw hσ hu hF0]
  have hmono : 0 ≤ |s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j :=
    mul_nonneg (rpow_nonneg (abs_nonneg _) _)
      (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (abs_nonneg _) _)
  have hdens : 0 ≤ 1 / D.q i (D.k i) * |s| ^ P.pExp i * ∏ j, |w j| ^ P.rExp i j :=
    mul_nonneg (mul_nonneg (by positivity) (rpow_nonneg (abs_nonneg _) _))
      (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (abs_nonneg _) _)
  have hexp : exp (-(t * (P.Ma i * (|s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j)))) ≤
      exp (-(t * (|P.a i (D.solvedPt i σ s w)| *
        (|s| ^ P.nu i * ∏ j, |w j| ^ P.kappa i j)))) := by
    rw [exp_le_exp]
    have := (P.a_bounds i _ hu).2
    nlinarith [mul_nonneg ht hmono]
  refine mul_le_mul (mul_le_mul_of_nonneg_right hexp (hφ _)) ?_ ?_
    (mul_nonneg (exp_pos _).le (hφ _))
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (P.b_bounds i _ hu).1 (P.wt_nonneg i _)) hdens
  · exact mul_nonneg (mul_nonneg (P.wt_nonneg i _) (P.mb_pos i).le) hdens

end WallChartsData.Phase

end Laplace.Multi
