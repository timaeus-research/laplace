/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TermMeasureCertificate

/-!
# Certified term data from the three shapes

The per-term input of a `TermMeasureCertificate`: `TermData P σ γ p` is a power, a logarithmic
order and a finite coefficient measure of the term `p` certified against every continuous
nonnegative bounded observable supported in `L'`. The three established asymptotics supply it: a
non-admissible branch carries the zero measure (`TermData.ofNotAdmissible`), an admissible branch
at a certified isolated scale carries `(λ_p, 0, termMeasure)` (`TermData.vertex`), a fully tied
chart carries `(γp + δλ, k, c · δ_{rep 0})` with the tied constant `c` (`TermData.tied`), and a
partially tied chart carries `(γp + δλ, k, partialMeasure)` (`TermData.partial`). Certified data
for every term assembles into a certificate (`TermMeasureCertificate.ofTermData`), hence into the
fibre expectation of every observable (Astra, round 5, target 2: the assembly from per-chart data).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

/-- The tied constant is nonnegative. -/
theorem tiedConst_nonneg {k : ℕ} {A B δ : ℝ} {κ r : Fin (k + 1) → ℝ} {lam R a w : ℝ} (hA : 0 ≤ A)
    (hw : 0 ≤ w) (hR : 0 < R) (hBa : 0 ≤ B * a) (hδ : 0 ≤ δ) (hlam : 0 < lam)
    (hκ : ∀ i, 0 < κ i) : 0 ≤ tiedConst A B δ κ r lam R a w := by
  unfold tiedConst
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA hw) (rpow_nonneg hR.le _))
    (rpow_nonneg (mul_nonneg hBa (rpow_nonneg hR.le _)) _)) (pow_nonneg hδ _)) ?_
  exact mul_nonneg (div_nonneg (Real.Gamma_pos_of_pos hlam).le (Nat.cast_nonneg _))
    (Finset.prod_nonneg fun i _ ↦ div_nonneg zero_le_one (hκ i).le)

namespace TruthChartsData.Phase

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {σ γ : ℝ}

/-- The certified data of one term: a power, a logarithmic order and a finite coefficient
measure, certified against every continuous nonnegative bounded observable supported in `L'`. -/
structure TermData (P : D.Phase F) (σ γ : ℝ) (p : TermIdx D) where
  lam : ℝ
  kk : ℕ
  μ : Measure (Fin (m + 1) → ℝ)
  finite : IsFiniteMeasure μ
  tendsto : ∀ φ : (Fin (m + 1) → ℝ) → ℝ, Continuous φ → (∀ z, 0 ≤ φ z) → (∃ M, ∀ z, φ z ≤ M) →
    (∀ z, φ z ≠ 0 → z ∈ L') →
    Tendsto (fun t ↦ t ^ lam / log t ^ kk * P.termKernel φ σ γ p t) atTop (𝓝 (∫ z, φ z ∂μ))

/-- **The certificate from certified data for every term.** -/
noncomputable def TermMeasureCertificate.ofTermData [Nonempty D.ι] (T : ∀ p, P.TermData σ γ p) :
    P.TermMeasureCertificate σ γ :=
  TermMeasureCertificate.ofTerms (fun p ↦ (T p).lam) (fun p ↦ (T p).kk) (fun p ↦ (T p).μ)
    (fun p ↦ (T p).finite) fun φ hφc hφ hM hφL p ↦ (T p).tendsto φ hφc hφ hM hφL

/-- A non-admissible branch: the zero measure, at any order. -/
def TermData.ofNotAdmissible {p : TermIdx D} (h : ¬ D.admissible p.1 p.2.1 p.2.2 σ) (lam : ℝ)
    (kk : ℕ) : P.TermData σ γ p where
  lam := lam
  kk := kk
  μ := 0
  finite := inferInstance
  tendsto := fun _ _ _ _ _ ↦ by
    rw [integral_zero_measure]
    exact P.tendsto_termKernel_of_not_admissible h lam kk

/-- An admissible branch at a certified isolated scale: `(λ_p, 0, termMeasure)`. -/
noncomputable def TermData.vertex (hS : ∀ i, |D.S i| = 1) (hσ : σ ≠ 0)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      T (D.rep i u) = truthMono (D.S i) (D.q i) u)
    {α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ} {p : TermIdx D}
    (hadm : D.admissible p.1 p.2.1 p.2.2 σ)
    (hfeas : ConstrainedFeasible (D.Qexp p.1) (P.kappa p.1) γ (P.phaseExp p.1 γ)
      (α p.1 p.2.1 p.2.2))
    (hprof : P.ProfileIntegrableOf p.1 p.2.1 p.2.2 σ γ (α p.1 p.2.1 p.2.2)) :
    P.TermData σ γ p where
  lam := P.termLam γ α p
  kk := 0
  μ := P.termMeasure p.1 p.2.1 p.2.2 σ γ (α p.1 p.2.1 p.2.2)
  finite := P.isFiniteMeasure_termMeasure hσ hprof
  tendsto := fun φ hφc hφ ⟨M, hM⟩ hφL ↦ by
    classical
    have h := P.tendsto_termKernel_vertex hS hσ htruth hφc hφ hM hφL hadm hfeas hprof
    unfold TruthChartsData.Phase.termConst' at h
    rwa [if_pos hadm, P.termConst_eq_integral hφc.measurable] at h

end TruthChartsData.Phase

section Tied

variable {k : ℕ} {L' : Set (Fin (k + 1 + 1) → ℝ)}
  {T : (Fin (k + 1 + 1) → ℝ) → ℝ}
  {D : TruthChartsData (k + 1) T L'} {F : (Fin (k + 1 + 1) → ℝ) → ℝ} (P : D.Phase F) {σ γ : ℝ}

/-- An admissible branch of a fully tied chart: `(γp + δλ, k, c · δ_{rep 0})` with the tied
constant `c`. -/
noncomputable def TruthChartsData.Phase.TermData.tied (hσ : σ ≠ 0) (hγ : 0 < γ)
    {p : TruthChartsData.Phase.TermIdx D} (hadm : D.admissible p.1 p.2.1 p.2.2 σ)
    (hQ : D.Qexp p.1 = 0) (hκ : ∀ j, 0 < P.kappa p.1 j) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ j, (P.rExp p.1 j + 1) / P.kappa p.1 j = lam) (hδ : 0 < P.phaseExp p.1 γ) :
    P.TermData σ γ p where
  lam := γ * P.pExp p.1 + P.phaseExp p.1 γ * lam
  kk := k
  μ := ENNReal.ofReal (tiedConst (P.constA p.1 σ) (P.constB p.1 σ) (P.phaseExp p.1 γ) (P.kappa p.1)
    (P.rExp p.1) lam (D.ρ p.1) |P.a p.1 0| (P.wt p.1 0 * |P.b p.1 0|)) • Measure.dirac (D.rep p.1 0)
  finite := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  tendsto := fun φ hφc hφ ⟨M, hM⟩ hφL ↦ by
    have h := P.tendsto_termKernel_tied hσ hγ hφc hφ hM hφL hadm hQ hκ hlam htied hδ
    have hnn : 0 ≤ tiedConst (P.constA p.1 σ) (P.constB p.1 σ) (P.phaseExp p.1 γ) (P.kappa p.1)
        (P.rExp p.1) lam (D.ρ p.1) |P.a p.1 0| (P.wt p.1 0 * |P.b p.1 0|) :=
      tiedConst_nonneg P.constA_nonneg (mul_nonneg (P.wt_nonneg _ _) (abs_nonneg _)) (D.ρ_pos _)
        (mul_nonneg (P.constB_pos hσ).le (abs_nonneg _)) hδ.le hlam hκ
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hnn, smul_eq_mul]
    have e : tiedConst (P.constA p.1 σ) (P.constB p.1 σ) (P.phaseExp p.1 γ) (P.kappa p.1)
        (P.rExp p.1) lam (D.ρ p.1) |P.a p.1 0| (φ (D.rep p.1 0) * (P.wt p.1 0 * |P.b p.1 0|)) =
        tiedConst (P.constA p.1 σ) (P.constB p.1 σ) (P.phaseExp p.1 γ) (P.kappa p.1)
          (P.rExp p.1) lam (D.ρ p.1) |P.a p.1 0| (P.wt p.1 0 * |P.b p.1 0|) * φ (D.rep p.1 0) := by
      unfold tiedConst
      ring
    rwa [e] at h

end Tied

section Partial

variable {m k : ℕ} {ν : Type*} [Fintype ν] {L' : Set (Fin (m + 1) → ℝ)}
  {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {σ γ : ℝ}

/-- An admissible branch of a partially tied chart: `(γp + δλ, k, partialMeasure)`. -/
noncomputable def TruthChartsData.Phase.TermData.partial (e : Fin (k + 1) ⊕ ν ≃ Fin m) (hσ : σ ≠ 0)
    (hγ : 0 < γ) {p : TruthChartsData.Phase.TermIdx D} (hadm : D.admissible p.1 p.2.1 p.2.2 σ)
    (hQ : D.Qexp p.1 = 0) (hκ : ∀ j, 0 < P.kappa p.1 j) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ j, (P.rExp p.1 (e (Sum.inl j)) + 1) / P.kappa p.1 (e (Sum.inl j)) = lam)
    (hgap : ∀ j, lam * P.kappa p.1 (e (Sum.inr j)) < P.rExp p.1 (e (Sum.inr j)) + 1)
    (hδ : 0 < P.phaseExp p.1 γ) : P.TermData σ γ p where
  lam := γ * P.pExp p.1 + P.phaseExp p.1 γ * lam
  kk := k
  μ := P.partialMeasure p.1 p.2.1 p.2.2 σ γ lam e
  finite := P.isFiniteMeasure_partialMeasure hσ hlam hκ hδ.le e hgap
  tendsto := fun _ hφc hφ ⟨_, hM⟩ hφL ↦
    P.tendsto_termKernel_partial_measure e hσ hγ hφc hφ hM hφL hadm hQ hκ hlam htied hgap hδ

end Partial

end Laplace.Multi
