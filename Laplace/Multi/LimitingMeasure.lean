/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallTermPositivity

/-!
# The limiting measure on the dominant strata

What the expectation values along the fibre retain. Each admissible term `p = (i, ε, b)` at a
certified scale carries the finite measure

`μ_p := (rep_i ∘ limitBranchPt_p)_* ( A · 1_L · wt|b|(bp u) ∏ u^r e^{-Φ₀(u)} du )`

on the ambient space (`termMeasure`), and its term constant is `∫ φ dμ_p` (`termConst_eq_integral`).
Summing over the dominant admissible terms gives the limiting measure `μ` (`limitMeasure`), and
the main theorem reads `⟨ψ⟩_χ(t) → ∫ ψ dμ / ∫ χ dμ` (`tendsto_fibre_expectation_measure`): the
expectation values along the fibre retain exactly the normalised measure `μ/μ(1)` and nothing
else — not the exponent `λ₀`, not the overall amplitude. The measure vanishes off the face images
`rep_i(limitBranchPt_p(L_p))` (`limitMeasure_eq_zero`), so when every dominant face map is
constant — the case of the toy and blow-up instances, where the limiting branch point is the
wall point — all limits are point evaluations: `⟨ψ⟩_χ(t) → ψ(z₀)/χ(z₀)`
(`tendsto_fibre_expectation_point`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData

variable (D : WallChartsData m ℓ L')

/-- The face map of a term: the chart representative of the limiting branch point. -/
noncomputable def faceMap (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ) (α : Fin m → ℝ)
    (u : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  D.rep i (D.limitBranchPt i ε b σ γ α u)

theorem measurable_faceMap (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ) (α : Fin m → ℝ) :
    Measurable (D.faceMap i ε b σ γ α) :=
  (D.rep_meas i).comp (D.measurable_limitBranchPt i ε b σ γ α)

namespace Phase

variable {D} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
variable {i : D.ι} {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ} {α : Fin m → ℝ}
  {φ : (Fin (m + 1) → ℝ) → ℝ}

theorem constA_nonneg : 0 ≤ P.constA i σ := by
  unfold WallChartsData.Phase.constA
  exact div_nonneg (rpow_nonneg (abs_nonneg _) _) (Nat.cast_nonneg _)

/-- The term integrand `1_L W₀(φ) ∏u^r e^{-Φ₀}` is integrable for a bounded observable. -/
theorem integrable_termIntegrand (hσ : σ ≠ 0) (hφm : Measurable φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (hprof : P.ProfileIntegrableOf i ε b σ γ α) :
    Integrable fun u ↦ dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i)
      (P.rExp i) α (P.limitWeight i φ ε b σ γ α) u *
      exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
        (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u) := by
  have hprodpos : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      0 < ∏ j, u j ^ P.rExp i j := fun u hu ↦
    Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (limitDomain_pos hu j) _
  have hW0 : ∀ u, 0 ≤ P.limitWeight i φ ε b σ γ α u := fun u ↦
    mul_nonneg (hφ _) (mul_nonneg (P.wt_nonneg i _) (abs_nonneg _))
  have hf0 : ∀ u, 0 ≤ dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α
      (P.limitWeight i φ ε b σ γ α) u *
      exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
        (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u) := fun u ↦ by
    unfold dsWeight₀
    exact mul_nonneg (Set.indicator_nonneg (fun u hu ↦
      mul_nonneg (hW0 u) (hprodpos u hu).le) u) (exp_pos _).le
  have hmeas : Measurable fun u ↦ dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i)
      (P.rExp i) α (P.limitWeight i φ ε b σ γ α) u *
      exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
        (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u) := by
    unfold dsWeight₀
    exact (((P.measurable_limitWeight hφm).mul
      (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)).indicator
        measurableSet_limitDomain).mul
      (Real.measurable_exp.comp (measurable_dsProfile_of P.measurable_limitUnit).neg)
  have hc1 : P.ma i / P.Ma i ≤ 1 := by
    have h := P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)
    have hMa : 0 < P.Ma i := (P.ma_pos i).trans_le (h.1.trans h.2)
    rw [div_le_one hMa]
    exact h.1.trans h.2
  refine Integrable.mono' (hprof.int' _ (Mφ * P.Mb i)) hmeas.aestronglyMeasurable
    (Eventually.of_forall fun u ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 u)]
  unfold dsWeight₀ dsEnvelope
  by_cases hu : u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    have hΦ := P.dsProfile_nonneg' (i := i) (ε := ε) (b := b) (γ := γ) (α := α) hσ u
    refine mul_le_mul (mul_le_mul_of_nonneg_right (P.limitWeight_le hφ hMφ hu)
      (hprodpos u hu).le) (Real.exp_le_exp.mpr ?_) (exp_pos _).le
      (mul_nonneg (mul_nonneg ((hφ 0).trans (hMφ 0)) P.Mb_nonneg) (hprodpos u hu).le)
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hΦ]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul, mul_zero, zero_mul]

/-- The limiting density of a term on the transverse coordinates:
`A · 1_L · wt|b|(bp u) ∏ u^r e^{-Φ₀(u)}`. -/
noncomputable def termDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ) (α : Fin m → ℝ)
    (u : Fin m → ℝ) : ℝ :=
  P.constA i σ * (dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α
      (P.limitWeight i (fun _ ↦ 1) ε b σ γ α) u *
    exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
      (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u))

theorem termDensity_nonneg (u : Fin m → ℝ) : 0 ≤ P.termDensity i ε b σ γ α u := by
  unfold termDensity dsWeight₀
  refine mul_nonneg P.constA_nonneg (mul_nonneg (Set.indicator_nonneg (fun u hu ↦ ?_) u)
    (exp_pos _).le)
  exact mul_nonneg (mul_nonneg zero_le_one (mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)))
    (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (limitDomain_pos hu j).le _)

theorem termDensity_eq_zero_of_notMem {u : Fin m → ℝ}
    (hu : u ∉ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α) :
    P.termDensity i ε b σ γ α u = 0 := by
  unfold termDensity dsWeight₀
  rw [Set.indicator_of_notMem hu, zero_mul, mul_zero]

theorem measurable_termDensity : Measurable (P.termDensity i ε b σ γ α) := by
  unfold termDensity dsWeight₀
  exact measurable_const.mul ((((P.measurable_limitWeight measurable_const).mul
    (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)).indicator
      measurableSet_limitDomain).mul
    (Real.measurable_exp.comp (measurable_dsProfile_of P.measurable_limitUnit).neg))

theorem integrable_termDensity (hσ : σ ≠ 0) (hprof : P.ProfileIntegrableOf i ε b σ γ α) :
    Integrable (P.termDensity i ε b σ γ α) :=
  (P.integrable_termIntegrand hσ measurable_const (fun _ ↦ zero_le_one) (Mφ := 1)
    (fun _ ↦ le_rfl) hprof).const_mul _

/-- The term integrand of the observable `φ` is the density times `φ ∘ faceMap`. -/
theorem termDensity_mul_faceMap (u : Fin m → ℝ) :
    P.termDensity i ε b σ γ α u * φ (D.faceMap i ε b σ γ α u) =
      P.constA i σ * (dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α
          (P.limitWeight i φ ε b σ γ α) u *
        exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
          (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u)) := by
  unfold termDensity dsWeight₀ WallChartsData.Phase.limitWeight WallChartsData.faceMap
  by_cases hu : u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    ring
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
    ring

/-- The limiting measure of a term on the ambient space. -/
noncomputable def termMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ)
    (α : Fin m → ℝ) : Measure (Fin (m + 1) → ℝ) :=
  (volume.withDensity fun u ↦ ENNReal.ofReal (P.termDensity i ε b σ γ α u)).map
    (D.faceMap i ε b σ γ α)

/-- **The term constant is the integral of the observable against the term measure.** -/
theorem termConst_eq_integral (hφm : Measurable φ) :
    P.termConst i φ ε b σ γ α = ∫ z, φ z ∂(P.termMeasure i ε b σ γ α) := by
  unfold termMeasure
  have hm : Measurable fun u ↦ ENNReal.ofReal (P.termDensity i ε b σ γ α u) :=
    ENNReal.measurable_ofReal.comp P.measurable_termDensity
  rw [integral_map (D.measurable_faceMap i ε b σ γ α).aemeasurable hφm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  unfold WallChartsData.Phase.termConst
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (P.termDensity_nonneg u), smul_eq_mul, P.termDensity_mul_faceMap]

theorem isFiniteMeasure_termMeasure (hσ : σ ≠ 0) (hprof : P.ProfileIntegrableOf i ε b σ γ α) :
    IsFiniteMeasure (P.termMeasure i ε b σ γ α) := by
  unfold termMeasure
  have := isFiniteMeasure_withDensity_ofReal (P.integrable_termDensity hσ hprof).hasFiniteIntegral
  infer_instance

theorem integrable_termMeasure (hσ : σ ≠ 0) (hprof : P.ProfileIntegrableOf i ε b σ γ α)
    (hφm : Measurable φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ) :
    Integrable φ (P.termMeasure i ε b σ γ α) := by
  have := P.isFiniteMeasure_termMeasure hσ hprof
  exact (integrable_const Mφ).mono' hφm.aestronglyMeasurable (ae_of_all _ fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ z)]; exact hMφ z)

/-- The term measure vanishes off the image of the limiting domain under the face map. -/
theorem termMeasure_eq_zero {s : Set (Fin (m + 1) → ℝ)} (hs : MeasurableSet s)
    (hdisj : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      D.faceMap i ε b σ γ α u ∉ s) :
    P.termMeasure i ε b σ γ α s = 0 := by
  unfold termMeasure
  have hpre : MeasurableSet (D.faceMap i ε b σ γ α ⁻¹' s) := D.measurable_faceMap i ε b σ γ α hs
  rw [Measure.map_apply (D.measurable_faceMap i ε b σ γ α) hs, withDensity_apply _ hpre]
  refine (setLIntegral_congr_fun hpre fun u hu ↦ ?_).trans lintegral_zero
  have hu' : u ∉ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α :=
    fun h ↦ hdisj u h hu
  rw [P.termDensity_eq_zero_of_notMem hu', ENNReal.ofReal_zero]

/-- The total mass of a term measure is the term constant of the observable `1`. -/
theorem termMeasure_univ (hσ : σ ≠ 0) (hprof : P.ProfileIntegrableOf i ε b σ γ α) :
    P.termMeasure i ε b σ γ α univ = ENNReal.ofReal (P.termConst i (fun _ ↦ 1) ε b σ γ α) := by
  unfold termMeasure
  rw [Measure.map_apply (D.measurable_faceMap i ε b σ γ α) MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (P.integrable_termDensity hσ hprof)
      (ae_of_all _ (P.termDensity_nonneg))]
  congr 1
  unfold termDensity WallChartsData.Phase.termConst
  rw [integral_const_mul]

/-! ### The limiting measure -/

variable (σ γ) (αf : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ) (lam₀ : ℝ)

open scoped Classical in
/-- The dominant admissible terms: exponent `lam₀` and admissible branch. -/
noncomputable def dominantTerms : Finset (TermIdx D) :=
  Finset.univ.filter fun p ↦ P.termLam γ αf p = lam₀ ∧ D.admissible p.1 p.2.1 p.2.2 σ

/-- **The limiting measure on the dominant strata.** -/
noncomputable def limitMeasure : Measure (Fin (m + 1) → ℝ) :=
  ∑ p ∈ P.dominantTerms σ γ αf lam₀, P.termMeasure p.1 p.2.1 p.2.2 σ γ (αf p.1 p.2.1 p.2.2)

theorem isFiniteMeasure_limitMeasure (hσ : σ ≠ 0)
    (hprof : ∀ i ε b, D.admissible i ε b σ → P.ProfileIntegrableOf i ε b σ γ (αf i ε b)) :
    IsFiniteMeasure (P.limitMeasure σ γ αf lam₀) := by
  classical
  refine ⟨?_⟩
  unfold limitMeasure
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.mpr fun p hp ↦ ?_
  have := P.isFiniteMeasure_termMeasure hσ
    (hprof p.1 p.2.1 p.2.2 (Finset.mem_filter.mp hp).2.2)
  exact measure_lt_top _ _

theorem termMeasure_le_limitMeasure {p : TermIdx D} (hp : p ∈ P.dominantTerms σ γ αf lam₀)
    (s : Set (Fin (m + 1) → ℝ)) :
    P.termMeasure p.1 p.2.1 p.2.2 σ γ (αf p.1 p.2.1 p.2.2) s ≤ P.limitMeasure σ γ αf lam₀ s := by
  unfold limitMeasure
  rw [Measure.finsetSum_apply]
  exact Finset.single_le_sum (f := fun p : TermIdx D ↦
    P.termMeasure p.1 p.2.1 p.2.2 σ γ (αf p.1 p.2.1 p.2.2) s) (fun _ _ ↦ zero_le) hp

/-- **The dominant sum of term constants is the integral against the limiting measure.** -/
theorem sum_termConst'_eq_integral (hσ : σ ≠ 0) (hφm : Measurable φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ)
    (hprof : ∀ i ε b, D.admissible i ε b σ → P.ProfileIntegrableOf i ε b σ γ (αf i ε b)) :
    (∑ p : TermIdx D, if P.termLam γ αf p = lam₀ then P.termConst' φ σ γ αf p else 0) =
      ∫ z, φ z ∂(P.limitMeasure σ γ αf lam₀) := by
  classical
  unfold limitMeasure
  rw [integral_finsetSum_measure fun p hp ↦ P.integrable_termMeasure hσ
    (hprof p.1 p.2.1 p.2.2 (Finset.mem_filter.mp hp).2.2) hφm hφ hMφ]
  unfold dominantTerms
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  unfold WallChartsData.Phase.termConst'
  by_cases h1 : P.termLam γ αf p = lam₀
  · by_cases h2 : D.admissible p.1 p.2.1 p.2.2 σ
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      exact P.termConst_eq_integral hφm
    · rw [if_pos h1, if_neg h2, if_neg fun h ↦ h2 h.2]
  · rw [if_neg h1, if_neg fun h ↦ h1 h.1]

/-- The limiting measure vanishes off the face images of the dominant terms. -/
theorem limitMeasure_eq_zero {s : Set (Fin (m + 1) → ℝ)} (hs : MeasurableSet s)
    (hdisj : ∀ p ∈ P.dominantTerms σ γ αf lam₀,
      ∀ u ∈ limitDomain (D.ρ p.1) (D.constD p.1 σ) γ (D.q p.1 (D.k p.1)) (D.Qexp p.1)
        (αf p.1 p.2.1 p.2.2), D.faceMap p.1 p.2.1 p.2.2 σ γ (αf p.1 p.2.1 p.2.2) u ∉ s) :
    P.limitMeasure σ γ αf lam₀ s = 0 := by
  unfold limitMeasure
  rw [Measure.finsetSum_apply]
  exact Finset.sum_eq_zero fun p hp ↦ P.termMeasure_eq_zero hs (hdisj p hp)

/-- If every dominant face map is constant, the limiting measure is a multiple of a Dirac mass:
integrals are point evaluations times the total mass. -/
theorem integral_limitMeasure_of_faceMap_const {z₀ : Fin (m + 1) → ℝ}
    (hpt : ∀ p ∈ P.dominantTerms σ γ αf lam₀,
      ∀ u ∈ limitDomain (D.ρ p.1) (D.constD p.1 σ) γ (D.q p.1 (D.k p.1)) (D.Qexp p.1)
        (αf p.1 p.2.1 p.2.2), D.faceMap p.1 p.2.1 p.2.2 σ γ (αf p.1 p.2.1 p.2.2) u = z₀)
    (φ : (Fin (m + 1) → ℝ) → ℝ) :
    ∫ z, φ z ∂(P.limitMeasure σ γ αf lam₀) =
      φ z₀ * (P.limitMeasure σ γ αf lam₀ univ).toReal := by
  have h0 : P.limitMeasure σ γ αf lam₀ ({z₀}ᶜ) = 0 :=
    P.limitMeasure_eq_zero σ γ αf lam₀ (measurableSet_singleton z₀).compl
      fun p hp u hu h ↦ h (hpt p hp u hu)
  have hae : ∀ᵐ z ∂(P.limitMeasure σ γ αf lam₀), φ z = φ z₀ := by
    filter_upwards [compl_mem_ae_iff.mpr h0] with z hz
    have : z = z₀ := by simpa using hz
    rw [this]
  rw [integral_congr_ae hae, integral_const, measureReal_def, smul_eq_mul, mul_comm]

/-! ### The main theorem in measure form -/

variable {σ γ αf lam₀}

/-- **What expectation values know**: the ratio of the total kernels converges to the ratio of
the integrals of the observables against the limiting measure on the dominant strata. -/
theorem tendsto_fibre_expectation_measure (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z)
    (hFm : Measurable F)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    (hσ : σ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ L') (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hfeas : ∀ i ε b, D.admissible i ε b σ →
      ConstrainedFeasible (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) (αf i ε b))
    (hprof : ∀ i ε b, D.admissible i ε b σ → P.ProfileIntegrableOf i ε b σ γ (αf i ε b))
    (hmin : ∀ p : TermIdx D, lam₀ ≤ P.termLam γ αf p)
    (hpos : (∫ z, χ z ∂(P.limitMeasure σ γ αf lam₀)) ≠ 0) :
    Tendsto (fun t ↦
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ * t ^ (-γ))).toReal /
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ * t ^ (-γ))).toReal)
      atTop
      (𝓝 ((∫ z, ψ z ∂(P.limitMeasure σ γ αf lam₀)) / ∫ z, χ z ∂(P.limitMeasure σ γ αf lam₀))) := by
  have hψ' := P.sum_termConst'_eq_integral σ γ αf lam₀ hσ hψc.measurable hψ hMψ hprof
  have hχ' := P.sum_termConst'_eq_integral σ γ αf lam₀ hσ hχc.measurable hχ hMχ hprof
  rw [← hψ', ← hχ']
  exact P.tendsto_fibre_expectation hS hF hFm htruth hσ hψc hψ hMψ hψL hχc hχ hMχ hχL hfeas hprof
    hmin (by rwa [hχ'])

/-- **Concentration at a point**: if every dominant face map is constant at `z₀`, the fibre
expectation converges to the point evaluation `ψ(z₀)/χ(z₀)`. -/
theorem tendsto_fibre_expectation_point (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z)
    (hFm : Measurable F)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    (hσ : σ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ L') (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hfeas : ∀ i ε b, D.admissible i ε b σ →
      ConstrainedFeasible (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) (αf i ε b))
    (hprof : ∀ i ε b, D.admissible i ε b σ → P.ProfileIntegrableOf i ε b σ γ (αf i ε b))
    (hmin : ∀ p : TermIdx D, lam₀ ≤ P.termLam γ αf p) {z₀ : Fin (m + 1) → ℝ}
    (hpt : ∀ p ∈ P.dominantTerms σ γ αf lam₀,
      ∀ u ∈ limitDomain (D.ρ p.1) (D.constD p.1 σ) γ (D.q p.1 (D.k p.1)) (D.Qexp p.1)
        (αf p.1 p.2.1 p.2.2), D.faceMap p.1 p.2.1 p.2.2 σ γ (αf p.1 p.2.1 p.2.2) u = z₀)
    (hχ0 : χ z₀ ≠ 0) (hmass : P.limitMeasure σ γ αf lam₀ univ ≠ 0) :
    Tendsto (fun t ↦
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ * t ^ (-γ))).toReal /
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ * t ^ (-γ))).toReal)
      atTop (𝓝 (ψ z₀ / χ z₀)) := by
  have := P.isFiniteMeasure_limitMeasure σ γ αf lam₀ hσ hprof
  have hM : (P.limitMeasure σ γ αf lam₀ univ).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hmass, measure_ne_top _ _⟩
  have hψ' := P.integral_limitMeasure_of_faceMap_const σ γ αf lam₀ hpt ψ
  have hχ' := P.integral_limitMeasure_of_faceMap_const σ γ αf lam₀ hpt χ
  have h := P.tendsto_fibre_expectation_measure hS hF hFm htruth hσ hψc hψ hMψ hψL hχc hχ hMχ
    hχL hfeas hprof hmin (by rw [hχ']; exact mul_ne_zero hχ0 hM)
  rwa [hψ', hχ', mul_div_mul_right _ _ hM] at h

end Phase

end WallChartsData

end Laplace.Multi
