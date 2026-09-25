/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallKernelNormalised
import Laplace.Multi.OrthantSplit
import Laplace.Multi.ConstrainedLP

/-!
# From the wall-chart kernels to the constrained model

Astra's step 1.1 completed (`research_kernel_asymptotics_v1`): along the schedule `s = σ t^{-γ}`,
the fibre kernel of a chart with phase data is a finite sum, over the `2^m` orthants `ε` of
the unsolved coordinates and the two branches `±V` of the solved coordinate, of constrained model
kernels (`ConstrainedLP.modelKernel`) with the constants
`A = |σ|^p / q_k`, `B = |σ|^ν`, `D = |σ|^{1/q_k}`, `δ = 1 − γν`, the truth exponents `Q_j = q_j`,
the exponents `κ, r` of the fibre formulas, the weight
`W(x, v) = 1_{dom}(u) φ(rep u) wt(u) |b(u)|` and the unit `a(x, v) = |a(u)|` evaluated at the
branch point `u = (ε·x, ±v)`. The branch admissibility `0 < S ∏ (±1)^{q_j} (±1)^{q_k} σ` is
constant on each orthant.

This file: the pointwise identities. `branchKernel_orth_eq` writes the branch kernel at `w = ε·x`
as the sum over admissible branches of the real branch integrand `branchReal`;
`branchReal_eq_model` identifies `branchReal` with `A t^{-γp}` times the model integrand
(through `TruthChartsData.Phase.branch_integrand_eq`).
-/

open Real MeasureTheory Set
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)}

namespace TruthChartsData

variable {T : (Fin (m + 1) → ℝ) → ℝ} (D : TruthChartsData m T L')

/-- The sign of the truth coefficient on the orthant `ε`: `S ∏ (±1)^{q_j}`. -/
noncomputable def orthSign (i : D.ι) (ε : Fin m → Bool) : ℝ :=
  D.S i * ∏ j, bsign (ε j) ^ D.q i ((D.k i).succAbove j)

theorem solvedCoeff_orth (i : D.ι) (ε : Fin m → Bool) (x : Fin m → ℝ) :
    solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x) =
      D.orthSign i ε * ∏ j, x j ^ D.q i ((D.k i).succAbove j) := by
  unfold solvedCoeff orthSign orth
  simp only [mul_pow, Finset.prod_mul_distrib]
  ring

theorem abs_orthSign (i : D.ι) (hS : |D.S i| = 1) (ε : Fin m → Bool) : |D.orthSign i ε| = 1 := by
  unfold orthSign
  rw [abs_mul, hS, one_mul, Finset.abs_prod]
  simp [abs_pow, abs_bsign]

/-- Branch admissibility at the truth sign `σ`: `b = true` is the `+V` branch, `b = false` the
`−V` branch. -/
def admissible (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ : ℝ) : Prop :=
  0 < D.orthSign i ε * (if b then 1 else (-1) ^ D.q i (D.k i)) * σ

/-- The truth exponents of the unsolved coordinates, as reals. -/
noncomputable def Qexp (i : D.ι) (j : Fin m) : ℝ := D.q i ((D.k i).succAbove j)

/-- The branch point `u = (ε·x, ±v)`. -/
noncomputable def bridgePt (i : D.ι) (ε : Fin m → Bool) (b : Bool) (x : Fin m → ℝ) (v : ℝ) :
    Fin (m + 1) → ℝ :=
  (D.k i).insertNth (bsign b * v) (orth ε x)

/-- The model cutoff constant `D = |σ|^{1/q_k}`. -/
noncomputable def constD (i : D.ι) (σ : ℝ) : ℝ := |σ| ^ (1 / (D.q i (D.k i) : ℝ))

theorem bridgePt_eq_solvedPt (i : D.ι) (ε : Fin m → Bool) (b : Bool) (x : Fin m → ℝ) (s : ℝ) :
    D.bridgePt i ε b x (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x))
      (D.q i (D.k i)) s) = D.solvedPt i (bsign b) s (orth ε x) := rfl

/-- The solved coordinate on the orthant `ε` along the schedule is the model cutoff variable. -/
theorem solvedCoord_orth_eq_cutVar (i : D.ι) (hS : |D.S i| = 1) (ε : Fin m → Bool) {σ γ t : ℝ}
    (ht : 0 < t) {x : Fin m → ℝ} (hx : ∀ j, 0 < x j) :
    solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x)) (D.q i (D.k i)) (σ * t ^ (-γ)) =
      cutVar (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) t x := by
  rw [solvedCoord_eq_wallSolve _ hS]
  unfold wallSolve cutVar constD Qexp
  have hax : ∀ j, |orth ε x j| = x j := fun j ↦ by rw [abs_orth, abs_of_pos (hx j)]
  simp only [hax]
  have hs : |σ * t ^ (-γ)| = |σ| * t ^ (-γ) := by
    rw [abs_mul, abs_of_pos (rpow_pos_of_pos ht _)]
  have hP : 0 ≤ ∏ j, x j ^ (-(D.q i ((D.k i).succAbove j) : ℝ)) :=
    Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hx j).le _
  rw [hs, Real.mul_rpow (mul_nonneg (abs_nonneg _) (rpow_pos_of_pos ht _).le) hP,
    Real.mul_rpow (abs_nonneg _) (rpow_pos_of_pos ht _).le, ← Real.rpow_mul ht.le,
    ← Real.finsetProd_rpow _ _ fun j _ ↦ rpow_nonneg (hx j).le _]
  congr 1
  · congr 1
    ring_nf
  · refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← Real.rpow_mul (hx j).le]
    congr 1
    ring

theorem bridgePt_mem_ball_iff (i : D.ι) (ε : Fin m → Bool) (b : Bool) {ρ : ℝ} (hρ : 0 < ρ)
    {x : Fin m → ℝ} (hx : ∀ j, 0 < x j) {v : ℝ} (hv : 0 ≤ v) :
    D.bridgePt i ε b x v ∈ Metric.ball (0 : Fin (m + 1) → ℝ) ρ ↔ (∀ j, x j < ρ) ∧ v < ρ := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff hρ, Fin.forall_iff_succAbove (D.k i)]
  have hax : ∀ j, |orth ε x j| = x j := fun j ↦ by rw [abs_orth, abs_of_pos (hx j)]
  simp only [bridgePt, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Real.norm_eq_abs,
    abs_mul, abs_bsign, one_mul, abs_of_nonneg hv, hax]
  exact and_comm

/-- The real branch integrand of the Boltzmann weight `e^{-tF} φ` at `w = ε·x` and truth
`s = σ t^{-γ}`: `1_{dom}(u) e^{-tF(rep u)} φ(rep u) dens(u) · V/(q_k|s|)`. -/
noncomputable def branchReal (F : (Fin (m + 1) → ℝ) → ℝ) (i : D.ι) (φ : (Fin (m + 1) → ℝ) → ℝ)
    (ε : Fin m → Bool) (b : Bool) (t γ σ : ℝ) (x : Fin m → ℝ) : ℝ :=
  (D.dom i).indicator (fun u ↦ exp (-(t * F (D.rep i u))) * φ (D.rep i u) * D.dens i u)
      (D.bridgePt i ε b x (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x))
        (D.q i (D.k i)) (σ * t ^ (-γ)))) *
    (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x)) (D.q i (D.k i)) (σ * t ^ (-γ)) /
      (D.q i (D.k i) * |σ * t ^ (-γ)|))

theorem admissible_iff_pos (i : D.ι) (ε : Fin m → Bool) {σ γ t : ℝ} (ht : 0 < t)
    {x : Fin m → ℝ} (hx : ∀ j, 0 < x j) (cb : ℝ) :
    0 < solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x) * cb * (σ * t ^ (-γ)) ↔
      0 < D.orthSign i ε * cb * σ := by
  have hP : 0 < ∏ j, x j ^ D.q i ((D.k i).succAbove j) :=
    Finset.prod_pos fun j _ ↦ pow_pos (hx j) _
  rw [D.solvedCoeff_orth]
  have e : D.orthSign i ε * (∏ j, x j ^ D.q i ((D.k i).succAbove j)) * cb * (σ * t ^ (-γ)) =
      ((∏ j, x j ^ D.q i ((D.k i).succAbove j)) * t ^ (-γ)) * (D.orthSign i ε * cb * σ) := by
    ring
  rw [e]
  exact mul_pos_iff_of_pos_left (mul_pos hP (rpow_pos_of_pos ht _))

end TruthChartsData

namespace TruthChartsData.Phase

variable {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- The model weight of a branch: `1_{dom}(u) φ(rep u) wt(u) |b(u)|` at the branch point (the
chart domain is the closed ball intersected with `rep⁻¹ L'`). -/
noncomputable def weightFn (i : D.ι) (φ : (Fin (m + 1) → ℝ) → ℝ) (ε : Fin m → Bool) (b : Bool)
    (x : Fin m → ℝ) (v : ℝ) : ℝ :=
  (D.dom i).indicator (fun u ↦ φ (D.rep i u) * (P.wt i u * |P.b i u|)) (D.bridgePt i ε b x v)

/-- The model unit of a branch: `|a(u)|` at the branch point. -/
noncomputable def unitFn (i : D.ι) (ε : Fin m → Bool) (b : Bool) (x : Fin m → ℝ) (v : ℝ) : ℝ :=
  |P.a i (D.bridgePt i ε b x v)|

/-- The model constants `A = |σ|^p / q_k`, `B = |σ|^ν`, `δ = 1 − γν`. -/
noncomputable def constA (i : D.ι) (σ : ℝ) : ℝ := |σ| ^ P.pExp i / D.q i (D.k i)

noncomputable def constB (i : D.ι) (σ : ℝ) : ℝ := |σ| ^ P.nu i

noncomputable def phaseExp (i : D.ι) (γ : ℝ) : ℝ := 1 - γ * P.nu i

variable {i : D.ι} {φ : (Fin (m + 1) → ℝ) → ℝ} {ε : Fin m → Bool} {t γ σ : ℝ} {x : Fin m → ℝ}

/-- The chart function times the fibre factor is the real branch integrand. -/
theorem chartFun_mul_ofReal (hφ : ∀ z, 0 ≤ φ z) (b : Bool) :
    D.chartFun (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * φ z)) i
        (D.bridgePt i ε b x (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x))
          (D.q i (D.k i)) (σ * t ^ (-γ)))) *
      ENNReal.ofReal (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x))
        (D.q i (D.k i)) (σ * t ^ (-γ)) / (D.q i (D.k i) * |σ * t ^ (-γ)|)) =
    ENNReal.ofReal (D.branchReal F i φ ε b t γ σ x) := by
  unfold chartFun TruthChartsData.branchReal
  set u := D.bridgePt i ε b x (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x))
    (D.q i (D.k i)) (σ * t ^ (-γ)))
  by_cases hu : u ∈ D.dom i
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    have h1 : 0 ≤ exp (-(t * F (D.rep i u))) * φ (D.rep i u) :=
      mul_nonneg (exp_pos _).le (hφ _)
    rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul (mul_nonneg h1 (D.dens_nonneg i u))]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul, zero_mul,
      ENNReal.ofReal_zero]

open scoped Classical in
/-- **The branch kernel on an orthant** as the sum over admissible branches of the real branch
integrands. -/
theorem branchKernel_orth_eq (hφ : ∀ z, 0 ≤ φ z) (ht : 0 < t) (hx : ∀ j, 0 < x j) :
    branchKernel (D.k i) (D.S i) (D.q i)
        (D.chartFun (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * φ z)) i) (orth ε x)
        (σ * t ^ (-γ)) =
      ∑ b : Bool, if D.admissible i ε b σ then ENNReal.ofReal (D.branchReal F i φ ε b t γ σ x)
        else 0 := by
  unfold branchKernel
  rw [Fintype.sum_bool, add_comm]
  congr 1
  · -- the `+V` branch
    have hset : σ * t ^ (-γ) ∈ {s | 0 < solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x) * s} ↔
        D.admissible i ε true σ := by
      simp only [mem_ofPred_eq, admissible, if_true, mul_one]
      have := D.admissible_iff_pos i ε (σ := σ) (γ := γ) ht hx 1
      rwa [mul_one, mul_one] at this
    have hpt : ((D.k i).insertNth (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x))
        (D.q i (D.k i)) (σ * t ^ (-γ))) (orth ε x) : Fin (m + 1) → ℝ) =
        D.bridgePt i ε true x (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x))
          (D.q i (D.k i)) (σ * t ^ (-γ))) := by
      simp only [TruthChartsData.bridgePt, bsign, if_true, one_mul]
    by_cases hadm : D.admissible i ε true σ
    · rw [Set.indicator_of_mem (hset.mpr hadm), if_pos hadm, hpt, chartFun_mul_ofReal hφ]
    · rw [Set.indicator_of_notMem (hset.not.mpr hadm), if_neg hadm]
  · -- the `−V` branch
    have hset : σ * t ^ (-γ) ∈ {s | 0 < solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x) *
        (-1) ^ D.q i (D.k i) * s} ↔ D.admissible i ε false σ := by
      simp only [mem_ofPred_eq, admissible, Bool.false_eq_true, if_false]
      exact D.admissible_iff_pos i ε ht hx _
    have hpt : ((D.k i).insertNth (-solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x))
        (D.q i (D.k i)) (σ * t ^ (-γ))) (orth ε x) : Fin (m + 1) → ℝ) =
        D.bridgePt i ε false x (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x))
          (D.q i (D.k i)) (σ * t ^ (-γ))) := by
      simp only [TruthChartsData.bridgePt, bsign, Bool.false_eq_true, if_false, neg_one_mul]
    by_cases hadm : D.admissible i ε false σ
    · rw [Set.indicator_of_mem (hset.mpr hadm), if_pos hadm, hpt, chartFun_mul_ofReal hφ]
    · rw [Set.indicator_of_notMem (hset.not.mpr hadm), if_neg hadm]

/-- **The real branch integrand is the model integrand**, up to the prefactor `A t^{-γp}`. -/
theorem branchReal_eq_model (hS : |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (ht : 0 < t) (hσ : σ ≠ 0)
    (hx : ∀ j, 0 < x j) (b : Bool) :
    D.branchReal F i φ ε b t γ σ x =
      P.constA i σ * t ^ (-(γ * P.pExp i)) *
        modelIntegrand (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
          (D.Qexp i) (P.kappa i) (P.rExp i) (P.weightFn i φ ε b) (P.unitFn i ε b) t x := by
  have hV := D.solvedCoord_orth_eq_cutVar i hS ε (σ := σ) (γ := γ) ht hx
  set V := solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x)) (D.q i (D.k i))
    (σ * t ^ (-γ)) with hVdef
  have hV0 : 0 ≤ V := solvedCoord_nonneg _ _ _
  set u := D.bridgePt i ε b x V with hudef
  have hball := D.bridgePt_mem_ball_iff i ε b (D.ρ_pos i) hx hV0 (x := x) (v := V)
  have hmodel : x ∈ modelDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) t ↔
      (∀ j, x j < D.ρ i) ∧ V < D.ρ i := by
    simp only [modelDomain, mem_inter_iff, Set.mem_univ_pi, mem_Ioo, mem_ofPred_eq, ← hV]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun j ↦ (h1 j).2, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun j ↦ ⟨hx j, h1 j⟩, h2⟩
  unfold modelIntegrand weightFn unitFn
  by_cases hb : u ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i)
  · have hxm := hmodel.mpr (hball.mp hb)
    have hcb : u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
      Metric.ball_subset_closedBall hb
    have hdom : u ∈ D.dom i ↔ D.rep i u ∈ L' := by
      rw [D.dom_eq]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hcb, h⟩⟩
    rw [Set.indicator_of_mem hxm]
    rw [← hV]
    by_cases hL : D.rep i u ∈ L'
    · unfold TruthChartsData.branchReal
      rw [Set.indicator_of_mem (hdom.mpr hL), Set.indicator_of_mem (hdom.mpr hL)]
      have hw : ∀ j, orth ε x j ≠ 0 := fun j ↦ by
        rw [orth]; exact mul_ne_zero (bsign_ne_zero _) (hx j).ne'
      have hs : σ * t ^ (-γ) ≠ 0 := mul_ne_zero hσ (rpow_pos_of_pos ht _).ne'
      have key := P.branch_integrand_eq i hS t φ hs hw (abs_bsign b) hcb (hF _)
      have key' : exp (-(t * F (D.rep i u))) * φ (D.rep i u) * D.dens i u *
          (V / (D.q i (D.k i) * |σ * t ^ (-γ)|)) =
          exp (-(t * (|P.a i u| * (|σ * t ^ (-γ)| ^ P.nu i *
            ∏ j, |orth ε x j| ^ P.kappa i j)))) * φ (D.rep i u) *
          (P.wt i u * |P.b i u| * (1 / D.q i (D.k i) * |σ * t ^ (-γ)| ^ P.pExp i *
            ∏ j, |orth ε x j| ^ P.rExp i j)) := key
      rw [key']
      have hax : ∀ j, |orth ε x j| = x j := fun j ↦ by rw [abs_orth, abs_of_pos (hx j)]
      simp only [hax]
      have habs : |σ * t ^ (-γ)| = |σ| * t ^ (-γ) := by
        rw [abs_mul, abs_of_pos (rpow_pos_of_pos ht _)]
      rw [habs, Real.mul_rpow (abs_nonneg _) (rpow_pos_of_pos ht _).le,
        Real.mul_rpow (abs_nonneg _) (rpow_pos_of_pos ht _).le, ← Real.rpow_mul ht.le,
        ← Real.rpow_mul ht.le]
      have e1 : t ^ (1 - γ * P.nu i) = t * t ^ (-γ * P.nu i) := by
        rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_one, neg_mul]
      unfold constA constB phaseExp
      rw [e1, neg_mul, ← hudef]
      ring_nf
    · unfold TruthChartsData.branchReal
      rw [Set.indicator_of_notMem (hdom.not.mpr hL), Set.indicator_of_notMem (hdom.not.mpr hL)]
      simp
  · have hxm : x ∉ modelDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) t :=
      fun h ↦ hb (hball.mpr (hmodel.mp h))
    have hdens : D.dens i u = 0 := by
      by_contra h
      exact hb (D.dens_supp i u h)
    rw [Set.indicator_of_notMem hxm, mul_zero]
    unfold TruthChartsData.branchReal
    rw [Set.indicator_apply_eq_zero.mpr fun _ ↦ by rw [hdens, mul_zero], zero_mul]

end TruthChartsData.Phase

end Laplace.Multi
