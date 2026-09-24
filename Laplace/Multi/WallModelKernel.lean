/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallModelBridge
import Laplace.Multi.FibrePointwise

/-!
# The chart kernel along the schedule is a sum of model kernels

The integrated form of `WallModelBridge`: for a chart with phase data, `|S| = 1`, a nonnegative
measurable loss `F`, a bounded nonnegative measurable observable `φ`, and the schedule
`s = σ t^{-γ}`, the fibre kernel of the Boltzmann weight `e^{-tF} φ` equals
`∑_ε ∑_b 1_{admissible} modelKernel(ε, b)` (`fibreKernel_eq_sum_modelKernel`), hence the total
kernel of the record is the sum over charts, orthants and admissible branches of constrained
model kernels (`totalKernel_eq_sum_modelKernel`, real form `totalKernel_toReal`). Through the fibre
identity `WallChartsData.fibre_eq` this is the ambient fibre integral `∫_{A'} e^{-tF} φ` over the
fibre at truth `s`. Each model kernel is then handled by the dominant-scale certificate.
-/

open Real MeasureTheory Set Function Filter
open scoped ENNReal

namespace Laplace.Multi

theorem measurableSet_posOrthant {ι : Type*} [Countable ι] :
    MeasurableSet (posOrthant : Set (ι → ℝ)) :=
  MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData

variable (D : WallChartsData m ℓ L')

theorem measurable_bridgePt (i : D.ι) (ε : Fin m → Bool) (b : Bool) :
    Measurable fun p : (Fin m → ℝ) × ℝ ↦ D.bridgePt i ε b p.1 p.2 := by
  have e : (fun p : (Fin m → ℝ) × ℝ ↦ D.bridgePt i ε b p.1 p.2) = fun p ↦
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) (D.k i)).symm (bsign b * p.2, orth ε p.1) := rfl
  rw [e]
  exact (MeasurableEquiv.measurable _).comp
    ((measurable_const.mul measurable_snd).prodMk ((measurable_orth ε).comp measurable_fst))

end WallChartsData

namespace WallChartsData.Phase

variable {D : WallChartsData m ℓ L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
variable {i : D.ι} {φ : (Fin (m + 1) → ℝ) → ℝ} {ε : Fin m → Bool} {b : Bool} {t γ σ : ℝ}

theorem measurable_weightFn (hφ : Measurable φ) :
    Measurable (uncurry (P.weightFn i φ ε b)) := by
  have hg : Measurable fun u ↦ φ (D.rep i u) * (P.wt i u * |P.b i u|) :=
    (hφ.comp (D.rep_meas i)).mul
      ((P.wt_cont i).measurable.mul (continuous_abs.comp (P.b_cont i)).measurable)
  exact (hg.indicator (D.dom_meas i)).comp (D.measurable_bridgePt i ε b)

theorem measurable_unitFn : Measurable (uncurry (P.unitFn i ε b)) :=
  (continuous_abs.comp (P.a_cont i)).measurable.comp (D.measurable_bridgePt i ε b)

omit P in
theorem branchReal_nonneg (hφ : ∀ z, 0 ≤ φ z) (x : Fin m → ℝ) :
    0 ≤ D.branchReal F i φ ε b t γ σ x := by
  unfold WallChartsData.branchReal
  exact mul_nonneg (Set.indicator_nonneg (fun u _ ↦
    mul_nonneg (mul_nonneg (exp_pos _).le (hφ _)) (D.dens_nonneg i u)) _)
    (div_nonneg (solvedCoord_nonneg _ _ _) (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))

omit P in
/-- The real branch integrand is bounded by `C Mφ ρ / (q_k |s|)`. -/
theorem branchReal_le (hF : ∀ z, 0 ≤ F z) (ht : 0 < t) {C : ℝ} (hC : ∀ u, D.dens i u ≤ C)
    {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ) (hφ : ∀ z, 0 ≤ φ z) (x : Fin m → ℝ) :
    D.branchReal F i φ ε b t γ σ x ≤ C * Mφ * (D.ρ i / (D.q i (D.k i) * |σ * t ^ (-γ)|)) := by
  have hC0 : 0 ≤ C := (D.dens_nonneg i 0).trans (hC 0)
  have hMφ0 : 0 ≤ Mφ := (hφ 0).trans (hMφ 0)
  have hq : 0 ≤ (D.q i (D.k i) : ℝ) * |σ * t ^ (-γ)| :=
    mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hden : 0 ≤ D.ρ i / (D.q i (D.k i) * |σ * t ^ (-γ)|) := div_nonneg (D.ρ_pos i).le hq
  unfold WallChartsData.branchReal
  set V := solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x)) (D.q i (D.k i))
    (σ * t ^ (-γ)) with hVdef
  have hV0 : 0 ≤ V := solvedCoord_nonneg _ _ _
  set u := D.bridgePt i ε b x V with hudef
  by_cases hu : u ∈ D.dom i
  · rw [Set.indicator_of_mem hu]
    have hcb : u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i) := by
      rw [D.dom_eq] at hu
      exact hu.1
    have hVρ : V ≤ D.ρ i := by
      have h1 : ‖u (D.k i)‖ ≤ D.ρ i :=
        (norm_le_pi_norm u (D.k i)).trans (mem_closedBall_zero_iff.mp hcb)
      rwa [hudef, WallChartsData.bridgePt, Fin.insertNth_apply_same, Real.norm_eq_abs, abs_mul,
        abs_bsign, one_mul, abs_of_nonneg hV0] at h1
    have he : exp (-(t * F (D.rep i u))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht.le (hF _)))
    calc exp (-(t * F (D.rep i u))) * φ (D.rep i u) * D.dens i u *
          (V / (D.q i (D.k i) * |σ * t ^ (-γ)|))
        ≤ 1 * Mφ * C * (D.ρ i / (D.q i (D.k i) * |σ * t ^ (-γ)|)) :=
          mul_le_mul (mul_le_mul (mul_le_mul he (hMφ _) (hφ _) zero_le_one) (hC _)
            (D.dens_nonneg _ _) (mul_nonneg zero_le_one hMφ0))
            (div_le_div_of_nonneg_right hVρ hq) (div_nonneg hV0 hq)
            (mul_nonneg (mul_nonneg zero_le_one hMφ0) hC0)
      _ = C * Mφ * (D.ρ i / (D.q i (D.k i) * |σ * t ^ (-γ)|)) := by ring
  · rw [Set.indicator_of_notMem hu, zero_mul]
    exact mul_nonneg (mul_nonneg hC0 hMφ0) hden

/-- The model function of a branch: `A t^{-γp}` times the model integrand. -/
noncomputable def modelG (i : D.ι) (φ : (Fin (m + 1) → ℝ) → ℝ) (ε : Fin m → Bool) (b : Bool)
    (t γ σ : ℝ) (x : Fin m → ℝ) : ℝ :=
  P.constA i σ * t ^ (-(γ * P.pExp i)) *
    modelIntegrand (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
      (D.Qexp i) (P.kappa i) (P.rExp i) (P.weightFn i φ ε b) (P.unitFn i ε b) t x

/-- The model kernel of a branch. -/
noncomputable def modelKernelOf (i : D.ι) (φ : (Fin (m + 1) → ℝ) → ℝ) (ε : Fin m → Bool)
    (b : Bool) (t γ σ : ℝ) : ℝ :=
  modelKernel (D.ρ i) (P.constA i σ) (P.constB i σ) (D.constD i σ) γ (P.pExp i) (D.q i (D.k i))
    (P.phaseExp i γ) (D.Qexp i) (P.kappa i) (P.rExp i) (P.weightFn i φ ε b) (P.unitFn i ε b) t

theorem modelKernelOf_eq_integral :
    P.modelKernelOf i φ ε b t γ σ = ∫ x, P.modelG i φ ε b t γ σ x := by
  unfold modelKernelOf modelKernel modelG
  rw [integral_const_mul]

theorem modelG_eq_zero_of_notMem {x : Fin m → ℝ}
    (hx : x ∉ Set.pi univ fun _ : Fin m ↦ Ioo (0 : ℝ) (D.ρ i)) :
    P.modelG i φ ε b t γ σ x = 0 := by
  unfold modelG modelIntegrand
  rw [Set.indicator_of_notMem, mul_zero]
  exact fun h ↦ hx h.1

theorem modelG_eq_branchReal (hS : |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (ht : 0 < t) (hσ : σ ≠ 0)
    {x : Fin m → ℝ} (hx : ∀ j, 0 < x j) :
    P.modelG i φ ε b t γ σ x = D.branchReal F i φ ε b t γ σ x :=
  (P.branchReal_eq_model hS hF ht hσ hx b).symm

theorem modelG_nonneg (hS : |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (ht : 0 < t) (hσ : σ ≠ 0)
    (hφ : ∀ z, 0 ≤ φ z) (x : Fin m → ℝ) : 0 ≤ P.modelG i φ ε b t γ σ x := by
  by_cases hx : ∀ j, 0 < x j
  · rw [P.modelG_eq_branchReal hS hF ht hσ hx]
    exact branchReal_nonneg hφ x
  · rw [P.modelG_eq_zero_of_notMem fun h ↦ hx fun j ↦ (Set.mem_univ_pi.mp h j).1]

theorem measurable_modelG (hφ : Measurable φ) : Measurable (P.modelG i φ ε b t γ σ) :=
  measurable_const.mul
    (measurable_modelIntegrand (P.measurable_weightFn hφ) P.measurable_unitFn t)

theorem integrable_modelG (hS : |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (hφm : Measurable φ)
    (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ) (ht : 0 < t) (hσ : σ ≠ 0) {C : ℝ}
    (hC : ∀ u, D.dens i u ≤ C) : Integrable (P.modelG i φ ε b t γ σ) := by
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin m ↦ Ioo (0 : ℝ) (D.ρ i)) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hvol : volume (Set.pi univ fun _ : Fin m ↦ Ioo (0 : ℝ) (D.ρ i)) ≠ ⊤ := by
    rw [Real.volume_pi_Ioo]
    exact (ENNReal.prod_lt_top fun _ _ ↦ ENNReal.ofReal_lt_top).ne
  have hsupp : support (P.modelG i φ ε b t γ σ) ⊆ Set.pi univ fun _ : Fin m ↦ Ioo (0 : ℝ) (D.ρ i) :=
    fun x hx ↦ by
      by_contra h
      exact hx (P.modelG_eq_zero_of_notMem h)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  refine Measure.integrableOn_of_bounded hvol (P.measurable_modelG hφm).aestronglyMeasurable
    (M := C * Mφ * (D.ρ i / (D.q i (D.k i) * |σ * t ^ (-γ)|))) ?_
  rw [ae_restrict_iff' hbox]
  refine Eventually.of_forall fun x hx ↦ ?_
  have hx' : ∀ j, 0 < x j := fun j ↦ (Set.mem_univ_pi.mp hx j).1
  rw [Real.norm_eq_abs, P.modelG_eq_branchReal hS hF ht hσ hx',
    abs_of_nonneg (branchReal_nonneg hφ x)]
  exact branchReal_le hF ht hC hMφ hφ x

theorem modelKernelOf_nonneg (hS : |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (ht : 0 < t) (hσ : σ ≠ 0)
    (hφ : ∀ z, 0 ≤ φ z) : 0 ≤ P.modelKernelOf i φ ε b t γ σ := by
  rw [P.modelKernelOf_eq_integral]
  exact integral_nonneg (P.modelG_nonneg hS hF ht hσ hφ)

open scoped Classical in
/-- **The chart kernel along the schedule is a sum of model kernels** over the orthants and the
admissible branches. -/
theorem fibreKernel_eq_sum_modelKernel (hS : |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (hFm : Measurable F)
    (hφm : Measurable φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (ht : 0 < t) (hσ : σ ≠ 0) :
    fibreKernel (D.k i) (D.S i) (D.q i)
        (D.chartFun (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * φ z)) i) (σ * t ^ (-γ)) =
      ∑ ε : Fin m → Bool, ∑ b : Bool, if D.admissible i ε b σ then
        ENNReal.ofReal (P.modelKernelOf i φ ε b t γ σ) else 0 := by
  obtain ⟨C, hC⟩ := D.exists_dens_bound i
  have hθ : Measurable fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * φ z) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp ((measurable_const.mul hFm).neg)).mul hφm)
  have hK : Measurable (uncurry (branchKernel (D.k i) (D.S i) (D.q i)
      (D.chartFun (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * φ z)) i))) :=
    measurable_branchKernel_uncurry _ _ _ (D.measurable_chartFun hθ i)
  unfold fibreKernel
  rw [lintegral_eq_sum_orthants _ hK.of_uncurry_right]
  refine Finset.sum_congr rfl fun ε _ ↦ ?_
  have hpt : ∀ x ∈ (posOrthant : Set (Fin m → ℝ)), branchKernel (D.k i) (D.S i) (D.q i)
      (D.chartFun (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * φ z)) i) (orth ε x)
        (σ * t ^ (-γ)) =
      ∑ b : Bool, if D.admissible i ε b σ then ENNReal.ofReal (P.modelG i φ ε b t γ σ x)
        else 0 := fun x hx ↦ by
    rw [branchKernel_orth_eq (F := F) hφ ht (mem_posOrthant.mp hx)]
    simp only [P.modelG_eq_branchReal hS hF ht hσ (mem_posOrthant.mp hx)]
  have hmeas : ∀ b : Bool, Measurable fun x ↦
      if D.admissible i ε b σ then ENNReal.ofReal (P.modelG i φ ε b t γ σ x) else 0 := fun b ↦ by
    by_cases hadm : D.admissible i ε b σ
    · simp only [if_pos hadm]
      exact ENNReal.measurable_ofReal.comp (P.measurable_modelG hφm)
    · simp only [if_neg hadm]
      exact measurable_const
  rw [setLIntegral_congr_fun measurableSet_posOrthant hpt, lintegral_finsetSum _ fun b _ ↦ hmeas b]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  by_cases hadm : D.admissible i ε b σ
  · simp only [if_pos hadm]
    have hsupp : support (fun x ↦ ENNReal.ofReal (P.modelG i φ ε b t γ σ x)) ⊆
        (posOrthant : Set (Fin m → ℝ)) := fun x hx ↦ by
      rw [mem_support] at hx
      by_contra h
      apply hx
      rw [P.modelG_eq_zero_of_notMem fun hb ↦ h (mem_posOrthant.mpr fun j ↦
        (Set.mem_univ_pi.mp hb j).1), ENNReal.ofReal_zero]
    rw [setLIntegral_eq_of_support_subset hsupp,
      ← ofReal_integral_eq_lintegral_ofReal (P.integrable_modelG hS hF hφm hφ hMφ ht hσ hC)
        (Eventually.of_forall (P.modelG_nonneg hS hF ht hσ hφ)), P.modelKernelOf_eq_integral]
  · simp only [if_neg hadm, lintegral_zero]

open scoped Classical in
/-- **The total kernel along the schedule** is the sum over charts, orthants and admissible
branches of model kernels. -/
theorem totalKernel_eq_sum_modelKernel (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z)
    (hFm : Measurable F) (hφm : Measurable φ) (hφ : ∀ z, 0 ≤ φ z)
    {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ) (ht : 0 < t) (hσ : σ ≠ 0) :
    D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * φ z)) (σ * t ^ (-γ)) =
      ∑ i, ∑ ε : Fin m → Bool, ∑ b : Bool, if D.admissible i ε b σ then
        ENNReal.ofReal (P.modelKernelOf i φ ε b t γ σ) else 0 := by
  unfold WallChartsData.totalKernel
  exact Finset.sum_congr rfl fun i _ ↦
    P.fibreKernel_eq_sum_modelKernel (hS i) hF hFm hφm hφ hMφ ht hσ

open scoped Classical in
/-- The real form of `totalKernel_eq_sum_modelKernel`. -/
theorem totalKernel_toReal (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (hFm : Measurable F)
    (hφm : Measurable φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (ht : 0 < t) (hσ : σ ≠ 0) :
    (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * φ z)) (σ * t ^ (-γ))).toReal =
      ∑ i, ∑ ε : Fin m → Bool, ∑ b : Bool, if D.admissible i ε b σ then
        P.modelKernelOf i φ ε b t γ σ else 0 := by
  rw [P.totalKernel_eq_sum_modelKernel hS hF hFm hφm hφ hMφ ht hσ]
  have hne : ∀ (i : D.ι) (ε : Fin m → Bool) (b : Bool),
      (if D.admissible i ε b σ then ENNReal.ofReal (P.modelKernelOf i φ ε b t γ σ) else 0) ≠ ⊤ :=
    fun i ε b ↦ by split_ifs <;> simp
  rw [ENNReal.toReal_sum fun i _ ↦ (ENNReal.sum_ne_top.mpr fun ε _ ↦
    (ENNReal.sum_ne_top.mpr fun b _ ↦ hne i ε b))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ENNReal.toReal_sum fun ε _ ↦ ENNReal.sum_ne_top.mpr fun b _ ↦ hne i ε b]
  refine Finset.sum_congr rfl fun ε _ ↦ ?_
  rw [ENNReal.toReal_sum fun b _ ↦ hne i ε b]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  split_ifs with hadm
  · exact ENNReal.toReal_ofReal (P.modelKernelOf_nonneg (hS i) hF ht hσ hφ)
  · exact ENNReal.toReal_zero

end WallChartsData.Phase

end Laplace.Multi
