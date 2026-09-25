/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallPartialTerm
import Laplace.Multi.LimitingMeasure
import Laplace.Multi.WallFibreExpectationLog
import Laplace.Multi.NormalisedMeasure

/-!
# Partially tied faces as measures, and the lexicographic coefficient measure

The coefficient of a partially tied wall term (`tendsto_modelKernelOf_partial`) is packaged as a
finite measure on the ambient space: the push-forward under the face point map
`z ↦ ρ_i(bridgePt (partialFace e z) 0)` of the face density
`A δ^k Γ(λ)/k! ∏_T κ^{-1} · wt|b| (B|a|)^{-λ} ∏_N z^{r−λκ}` on the box `(0,ρ)^N`
(`partialMeasure`, `integral_partialMeasure`, `isFiniteMeasure_partialMeasure`), so that
`t^{γp+δλ}/(log t)^k K_{i,ε,b}(t) → ∫ φ dμ_{i,ε,b}` for every certified observable
(`tendsto_modelKernelOf_partial_measure`, `tendsto_termKernel_partial_measure`).

The lexicographic assembly then reads at the level of measures
(`tendsto_fibre_expectation_lex_measure`): if every term `p` carries a finite measure `μ_p` with
`t^{λ_p}/(log t)^{k_p} K_p(φ) → ∫ φ dμ_p`, the fibre expectation converges to `∫ψ dμ_* / ∫χ dμ_*`
for the coefficient measure `μ_* = ∑_{(λ_p,k_p) = (λ_*,k_*)} μ_p` of the lexicographically dominant
terms. The distinguishability statements of `NormalisedMeasure` apply verbatim to `μ_*`: the
leading expectations know exactly the normalised lexicographic coefficient measure on `L'`,
logarithmic and power-law terms alike (Astra's target (1), `research_round3_v1.md`).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

namespace TruthChartsData

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  (D : TruthChartsData m T L')
variable {k : ℕ} {ν : Type*} [Fintype ν]

omit [Fintype ν] in
theorem measurable_partialFace (e : Fin (k + 1) ⊕ ν ≃ Fin m) :
    Measurable fun z : ν → ℝ ↦ partialFace e z := by
  refine measurable_pi_lambda _ fun j ↦ ?_
  unfold partialFace
  generalize e.symm j = s
  cases s with
  | inl l => exact measurable_const
  | inr l => exact measurable_pi_apply l

/-- The chart point of a partially tied face: solved coordinate `0`, tied coordinates `0`, worse
coordinates `±z`. -/
noncomputable def partialPt (i : D.ι) (ε : Fin m → Bool) (b : Bool) (e : Fin (k + 1) ⊕ ν ≃ Fin m)
    (z : ν → ℝ) : Fin (m + 1) → ℝ :=
  D.bridgePt i ε b (partialFace e z) 0

omit [Fintype ν] in
theorem measurable_partialPt (i : D.ι) (ε : Fin m → Bool) (b : Bool)
    (e : Fin (k + 1) ⊕ ν ≃ Fin m) : Measurable (D.partialPt i ε b e) :=
  (D.measurable_bridgePt i ε b).comp ((measurable_partialFace e).prodMk measurable_const)

omit [Fintype ν] in
theorem partialPt_mem_ball (i : D.ι) (ε : Fin m → Bool) (b : Bool) (e : Fin (k + 1) ⊕ ν ≃ Fin m)
    {z : ν → ℝ} (hz : ∀ j, z j ∈ Ioo (0 : ℝ) (D.ρ i)) :
    D.partialPt i ε b e z ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
  D.bridgePt_mem_ball_of_abs_lt i ε b (D.ρ_pos i) (abs_partialFace_lt e (D.ρ_pos i) hz)
    (by rw [abs_zero]; exact D.ρ_pos i)

/-- The ambient face point `ρ_i(pt_z)`: the push-forward map of the coefficient measure. -/
noncomputable def partialFacePt (i : D.ι) (ε : Fin m → Bool) (b : Bool)
    (e : Fin (k + 1) ⊕ ν ≃ Fin m) (z : ν → ℝ) : Fin (m + 1) → ℝ :=
  D.rep i (D.partialPt i ε b e z)

omit [Fintype ν] in
theorem measurable_partialFacePt (i : D.ι) (ε : Fin m → Bool) (b : Bool)
    (e : Fin (k + 1) ⊕ ν ≃ Fin m) : Measurable (D.partialFacePt i ε b e) :=
  (D.rep_meas i).comp (D.measurable_partialPt i ε b e)

namespace Phase

variable {D} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
variable {i : D.ι} {ε : Fin m → Bool} {b : Bool} {σ γ lam : ℝ} {φ : (Fin (m + 1) → ℝ) → ℝ}

/-- The tied-block constant `A δ^k Γ(λ)/k! ∏_T κ^{-1}`. -/
noncomputable def partialConst (i : D.ι) (σ γ lam : ℝ) (e : Fin (k + 1) ⊕ ν ≃ Fin m) : ℝ :=
  P.constA i σ *
    (P.phaseExp i γ ^ k * (Gamma lam / k.factorial * ∏ j, 1 / P.kappa i (e (Sum.inl j))))

/-- The face density on the worse block: the tied-block constant times
`wt|b| (B|a|)^{-λ} ∏_N z^{r−λκ}` at the face point, on the box `(0,ρ)^N`. -/
noncomputable def partialDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ lam : ℝ)
    (e : Fin (k + 1) ⊕ ν ≃ Fin m) (z : ν → ℝ) : ℝ :=
  (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)).indicator (fun z ↦
    P.partialConst i σ γ lam e *
      ((P.wt i (D.partialPt i ε b e z) * |P.b i (D.partialPt i ε b e z)|) *
        (P.constB i σ * |P.a i (D.partialPt i ε b e z)|) ^ (-lam) *
        ∏ j, z j ^ (P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j))))) z

omit [Fintype ν] in
theorem partialConst_nonneg (hlam : 0 < lam) (hκ : ∀ j, 0 < P.kappa i j)
    (hδ : 0 ≤ P.phaseExp i γ) (e : Fin (k + 1) ⊕ ν ≃ Fin m) :
    0 ≤ P.partialConst i σ γ lam e := by
  unfold partialConst
  refine mul_nonneg P.constA_nonneg (mul_nonneg (pow_nonneg hδ _) (mul_nonneg
    (div_nonneg (Gamma_pos_of_pos hlam).le (Nat.cast_nonneg _)) ?_))
  exact Finset.prod_nonneg fun j _ ↦ div_nonneg zero_le_one (hκ _).le

theorem partialDensity_nonneg (hlam : 0 < lam) (hκ : ∀ j, 0 < P.kappa i j)
    (hδ : 0 ≤ P.phaseExp i γ) (e : Fin (k + 1) ⊕ ν ≃ Fin m) (z : ν → ℝ) :
    0 ≤ P.partialDensity i ε b σ γ lam e z := by
  unfold partialDensity
  refine Set.indicator_nonneg (fun z hz ↦ ?_) z
  refine mul_nonneg (P.partialConst_nonneg hlam hκ hδ e) (mul_nonneg (mul_nonneg
    (mul_nonneg (P.wt_nonneg i _) (abs_nonneg _))
    (rpow_nonneg (mul_nonneg (rpow_nonneg (abs_nonneg _) _) (abs_nonneg _)) _)) ?_)
  exact Finset.prod_nonneg fun j _ ↦ rpow_nonneg (Set.mem_univ_pi.mp hz j).1.le _

theorem measurable_partialDensity (e : Fin (k + 1) ⊕ ν ≃ Fin m) :
    Measurable (P.partialDensity i ε b σ γ lam e) := by
  unfold partialDensity
  have hpt := D.measurable_partialPt i ε b e
  refine Measurable.indicator ?_ (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo)
  refine measurable_const.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_)
  · exact ((P.wt_cont i).measurable.comp hpt).mul
      ((continuous_abs.comp (P.b_cont i)).measurable.comp hpt)
  · exact (measurable_const.mul
      ((continuous_abs.comp (P.a_cont i)).measurable.comp hpt)).pow_const _
  · exact Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _

theorem integrable_partialDensity (hσ : σ ≠ 0) (hlam : 0 < lam) (hκ : ∀ j, 0 < P.kappa i j)
    (hδ : 0 ≤ P.phaseExp i γ) (e : Fin (k + 1) ⊕ ν ≃ Fin m)
    (hgap : ∀ j, lam * P.kappa i (e (Sum.inr j)) < P.rExp i (e (Sum.inr j)) + 1) :
    Integrable (P.partialDensity i ε b σ γ lam e) := by
  have hρ := D.ρ_pos i
  have hB : 0 < P.constB i σ := P.constB_pos hσ
  have hC := P.partialConst_nonneg (σ := σ) hlam hκ hδ e
  have hMb : 0 ≤ P.Mb i :=
    (abs_nonneg _).trans (P.b_bounds i 0 (Metric.mem_closedBall_self hρ.le)).2
  refine ((integrable_box_prod_rpow' hρ
    (r := fun j ↦ P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j)))
    fun j ↦ by have := hgap j; linarith).const_mul
    (P.partialConst i σ γ lam e * (P.Mb i * (P.constB i σ * P.ma i) ^ (-lam)))).mono'
    (P.measurable_partialDensity e).aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_of_nonneg (P.partialDensity_nonneg hlam hκ hδ e z)]
  unfold partialDensity
  by_cases hz : z ∈ Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    have hzb : ∀ j, z j ∈ Ioo (0 : ℝ) (D.ρ i) := Set.mem_univ_pi.mp hz
    have hball := Metric.ball_subset_closedBall (D.partialPt_mem_ball i ε b e hzb)
    have hprod : 0 ≤ ∏ j, z j ^ (P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j))) :=
      Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hzb j).1.le _
    have h1 : P.wt i (D.partialPt i ε b e z) * |P.b i (D.partialPt i ε b e z)| ≤ P.Mb i := by
      calc P.wt i (D.partialPt i ε b e z) * |P.b i (D.partialPt i ε b e z)|
          ≤ 1 * P.Mb i := mul_le_mul (P.wt_le_one i _) (P.b_bounds i _ hball).2 (abs_nonneg _)
            zero_le_one
        _ = P.Mb i := one_mul _
    have h2 : (P.constB i σ * |P.a i (D.partialPt i ε b e z)|) ^ (-lam) ≤
        (P.constB i σ * P.ma i) ^ (-lam) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hB (P.ma_pos i))
        (mul_le_mul_of_nonneg_left (P.a_bounds i _ hball).1 hB.le) (neg_nonpos.mpr hlam.le)
    calc P.partialConst i σ γ lam e *
          ((P.wt i (D.partialPt i ε b e z) * |P.b i (D.partialPt i ε b e z)|) *
            (P.constB i σ * |P.a i (D.partialPt i ε b e z)|) ^ (-lam) *
            ∏ j, z j ^ (P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j))))
        ≤ P.partialConst i σ γ lam e * ((P.Mb i * (P.constB i σ * P.ma i) ^ (-lam)) *
            ∏ j, z j ^ (P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hprod) hC
          exact mul_le_mul h1 h2 (rpow_nonneg (mul_nonneg hB.le (abs_nonneg _)) _) hMb
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]

/-- **The coefficient measure of a partially tied face**: the push-forward of the face density
under the face point map. -/
noncomputable def partialMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ lam : ℝ)
    (e : Fin (k + 1) ⊕ ν ≃ Fin m) : Measure (Fin (m + 1) → ℝ) :=
  (volume.withDensity fun z ↦ ENNReal.ofReal (P.partialDensity i ε b σ γ lam e z)).map
    (D.partialFacePt i ε b e)

theorem integral_partialMeasure (hlam : 0 < lam) (hκ : ∀ j, 0 < P.kappa i j)
    (hδ : 0 ≤ P.phaseExp i γ) (e : Fin (k + 1) ⊕ ν ≃ Fin m) (hφm : Measurable φ) :
    ∫ x, φ x ∂(P.partialMeasure i ε b σ γ lam e) =
      ∫ z, φ (D.partialFacePt i ε b e z) * P.partialDensity i ε b σ γ lam e z := by
  unfold partialMeasure
  have hm : Measurable fun z ↦ ENNReal.ofReal (P.partialDensity i ε b σ γ lam e z) :=
    ENNReal.measurable_ofReal.comp (P.measurable_partialDensity e)
  rw [integral_map (D.measurable_partialFacePt i ε b e).aemeasurable hφm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (P.partialDensity_nonneg hlam hκ hδ e z), smul_eq_mul, mul_comm]

theorem isFiniteMeasure_partialMeasure (hσ : σ ≠ 0) (hlam : 0 < lam) (hκ : ∀ j, 0 < P.kappa i j)
    (hδ : 0 ≤ P.phaseExp i γ) (e : Fin (k + 1) ⊕ ν ≃ Fin m)
    (hgap : ∀ j, lam * P.kappa i (e (Sum.inr j)) < P.rExp i (e (Sum.inr j)) + 1) :
    IsFiniteMeasure (P.partialMeasure i ε b σ γ lam e) := by
  unfold partialMeasure
  have := isFiniteMeasure_withDensity_ofReal
    (P.integrable_partialDensity (ε := ε) (b := b) hσ hlam hκ hδ e hgap).hasFiniteIntegral
  infer_instance

/-- **The partially tied term in measure form**: the normalised term kernel converges to the
integral of the observable against the coefficient measure of the face. -/
theorem tendsto_modelKernelOf_partial_measure (e : Fin (k + 1) ⊕ ν ≃ Fin m) (hσ : σ ≠ 0)
    (hγ : 0 < γ) (hQ : D.Qexp i = 0) (hκ : ∀ j, 0 < P.kappa i j) (hlam : 0 < lam)
    (htied : ∀ j, (P.rExp i (e (Sum.inl j)) + 1) / P.kappa i (e (Sum.inl j)) = lam)
    (hgap : ∀ j, lam * P.kappa i (e (Sum.inr j)) < P.rExp i (e (Sum.inr j)) + 1)
    (hδ : 0 < P.phaseExp i γ) (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + P.phaseExp i γ * lam) / log t ^ k *
        P.modelKernelOf i φ ε b t γ σ) atTop
      (𝓝 (∫ x, φ x ∂(P.partialMeasure i ε b σ γ lam e))) := by
  have h := P.tendsto_modelKernelOf_partial (ε := ε) (b := b) e hσ hγ hQ hκ hlam htied hgap hδ
    hφc hφ hMφ hφL
  rw [P.integral_partialMeasure hlam hκ hδ.le e hφc.measurable]
  have hbox : MeasurableSet (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have e1 : (fun z ↦ φ (D.partialFacePt i ε b e z) * P.partialDensity i ε b σ γ lam e z) =
      (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)).indicator (fun z ↦
        P.partialConst i σ γ lam e * (φ (D.partialFacePt i ε b e z) *
          (P.wt i (D.partialPt i ε b e z) * |P.b i (D.partialPt i ε b e z)|) *
          (P.constB i σ * |P.a i (D.partialPt i ε b e z)|) ^ (-lam) *
          ∏ j, z j ^ (P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j))))) := by
    funext z
    unfold partialDensity
    by_cases hz : z ∈ Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      ring
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  rw [e1, integral_indicator hbox, integral_const_mul]
  exact h

open scoped Classical in
/-- The `termKernel` form of the partially tied coefficient measure. -/
theorem tendsto_termKernel_partial_measure (e : Fin (k + 1) ⊕ ν ≃ Fin m) (hσ : σ ≠ 0)
    (hγ : 0 < γ) (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') {p : TruthChartsData.Phase.TermIdx D}
    (hadm : D.admissible p.1 p.2.1 p.2.2 σ) (hQ : D.Qexp p.1 = 0) (hκ : ∀ j, 0 < P.kappa p.1 j)
    (hlam : 0 < lam)
    (htied : ∀ j, (P.rExp p.1 (e (Sum.inl j)) + 1) / P.kappa p.1 (e (Sum.inl j)) = lam)
    (hgap : ∀ j, lam * P.kappa p.1 (e (Sum.inr j)) < P.rExp p.1 (e (Sum.inr j)) + 1)
    (hδ : 0 < P.phaseExp p.1 γ) :
    Tendsto (fun t ↦ t ^ (γ * P.pExp p.1 + P.phaseExp p.1 γ * lam) / log t ^ k *
        P.termKernel φ σ γ p t) atTop
      (𝓝 (∫ x, φ x ∂(P.partialMeasure p.1 p.2.1 p.2.2 σ γ lam e))) := by
  have h := P.tendsto_modelKernelOf_partial_measure (ε := p.2.1) (b := p.2.2) e hσ hγ hQ hκ hlam
    htied hgap hδ hφc hφ hMφ hφL
  unfold TruthChartsData.Phase.termKernel
  simp only [if_pos hadm]
  exact h

/-- **The lexicographic coefficient measure.** If every term `p` carries a finite measure `μ_p`
with `t^{λ_p}/(log t)^{k_p} K_p(φ) → ∫ φ dμ_p` for the two observables, the fibre expectation
converges to `∫ψ dμ_* / ∫χ dμ_*` for the sum `μ_*` of the measures of the lexicographically
dominant terms. -/
theorem tendsto_fibre_expectation_lex_measure (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z)
    (hFm : Measurable F) (hσ : σ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ)
    (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ} (hMψ : ∀ z, ψ z ≤ Mψ) (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z)
    {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) {lam : TermIdx D → ℝ} {kk : TermIdx D → ℕ}
    {μ : TermIdx D → Measure (Fin (m + 1) → ℝ)} [∀ p, IsFiniteMeasure (μ p)] {lam₀ : ℝ} {k₀ : ℕ}
    (hmin : ∀ p, lam₀ ≤ lam p ∧ (lam p = lam₀ → kk p ≤ k₀))
    (hKψ : ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel ψ σ γ p t) atTop
      (𝓝 (∫ z, ψ z ∂(μ p))))
    (hKχ : ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel χ σ γ p t) atTop
      (𝓝 (∫ z, χ z ∂(μ p))))
    (hpos : (∫ z, χ z ∂(∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), μ p)) ≠ 0) :
    Tendsto (fun t ↦
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ * t ^ (-γ))).toReal /
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ * t ^ (-γ))).toReal)
      atTop
      (𝓝 ((∫ z, ψ z ∂(∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), μ p)) /
        ∫ z, χ z ∂(∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), μ p))) := by
  have hint : ∀ (f : (Fin (m + 1) → ℝ) → ℝ), Continuous f → (∀ z, 0 ≤ f z) → ∀ (M : ℝ),
      (∀ z, f z ≤ M) → ∀ p, Integrable f (μ p) := fun f hfc hf M hM p ↦
    (integrable_const M).mono' hfc.aestronglyMeasurable (ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf z)]; exact hM z)
  rw [integral_finsetSum_measure fun p _ ↦ hint χ hχc hχ Mχ hMχ p] at hpos
  rw [integral_finsetSum_measure fun p _ ↦ hint ψ hψc hψ Mψ hMψ p,
    integral_finsetSum_measure fun p _ ↦ hint χ hχc hχ Mχ hMχ p]
  exact P.tendsto_fibre_expectation_lex hS hF hFm hσ hψc hψ hMψ hχc hχ hMχ hmin hKψ hKχ hpos

end Phase

end TruthChartsData

end Laplace.Multi
