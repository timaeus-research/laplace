/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallCertificate
import Laplace.Multi.PowerAssembly

/-!
# The expectation along the truth fibre

The end-to-end statement on the Euclidean side. For a chart record with phase data, along the
schedule `s = σ t^{-γ}`, the total kernels of two localised Boltzmann weights `e^{-tF} ψ` and
`e^{-tF} χ` (continuous, nonnegative, bounded, supported in `L'`) are finite sums of model kernels
over the terms (chart, orthant, admissible branch); with a certified scale for every admissible
term (feasibility for the chart's constrained LP and integrability of the limiting profile) each
term has the asymptotic `t^{λ_p} K_p → C_p`, and the pure-power assembly gives
`⟨ψ⟩_χ(t) := K^ψ(t)/K^χ(t) → ∑_{λ_p = λ₀} C^ψ_p / ∑_{λ_p = λ₀} C^χ_p`
(`tendsto_fibre_expectation`). Through the fibre identity, `K^ψ(t)` is the ambient integral of
`e^{-tF} ψ` over the truth fibre `{z_ℓ = σ t^{-γ}}`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

theorem dsEnvelope_const (ρ D γ q : ℝ) (Q r α : ι → ℝ) (c : ℝ) (u : ι → ℝ) :
    dsEnvelope ρ D γ q Q r α c u = c * dsEnvelope ρ D γ q Q r α 1 u := by
  unfold dsEnvelope
  ring

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData.Phase

variable {D : WallChartsData m ℓ L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- The profile-integrability certificate of a term at the scale `α` (envelope constant `1`; the
observable enters only through a constant). -/
structure ProfileIntegrableOf (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ) (α : Fin m → ℝ) :
    Prop where
  int : Integrable fun u ↦
    dsEnvelope (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α 1 u *
      exp (-(P.ma i / P.Ma i * dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i))
        (P.phaseExp i γ) (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u))
  Φint : Integrable fun u ↦
    dsEnvelope (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α 1 u *
      (dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
          (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u *
        exp (-(P.ma i / P.Ma i * dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ
          (D.q i (D.k i)) (P.phaseExp i γ) (D.Qexp i) (P.kappa i) α
            (P.limitUnit i ε b σ γ α) u)))

variable {i : D.ι} {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ} {α : Fin m → ℝ}

theorem ProfileIntegrableOf.int' (h : P.ProfileIntegrableOf i ε b σ γ α) (c : ℝ) :
    Integrable fun u ↦
      dsEnvelope (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α c u *
        exp (-(P.ma i / P.Ma i * dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ
          (D.q i (D.k i)) (P.phaseExp i γ) (D.Qexp i) (P.kappa i) α
            (P.limitUnit i ε b σ γ α) u)) :=
  (h.int.const_mul c).congr (Eventually.of_forall fun u ↦ by
    beta_reduce
    rw [dsEnvelope_const (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α c]
    ring)

theorem ProfileIntegrableOf.Φint' (h : P.ProfileIntegrableOf i ε b σ γ α) (c : ℝ) :
    Integrable fun u ↦
      dsEnvelope (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α c u *
        (dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
            (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u *
          exp (-(P.ma i / P.Ma i * dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ
            (D.q i (D.k i)) (P.phaseExp i γ) (D.Qexp i) (P.kappa i) α
              (P.limitUnit i ε b σ γ α) u))) :=
  (h.Φint.const_mul c).congr (Eventually.of_forall fun u ↦ by
    beta_reduce
    rw [dsEnvelope_const (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α c]
    ring)

/-- The limiting constant of a term for the observable `φ` at the scale `α`. -/
noncomputable def termConst (i : D.ι) (φ : (Fin (m + 1) → ℝ) → ℝ) (ε : Fin m → Bool) (b : Bool)
    (σ γ : ℝ) (α : Fin m → ℝ) : ℝ :=
  P.constA i σ * ∫ u, dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α
      (P.limitWeight i φ ε b σ γ α) u *
    exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
      (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u)

/-- The asymptotic of an admissible term with a certified scale. -/
theorem tendsto_term (hS : |D.S i| = 1) (hσ : σ ≠ 0) (hadm : D.admissible i ε b σ)
    (htruth : ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    {φ : (Fin (m + 1) → ℝ) → ℝ} (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L')
    (hfeas : ConstrainedFeasible (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) α)
    (hprof : P.ProfileIntegrableOf i ε b σ γ α) :
    Tendsto (fun t ↦ t ^ lpExponent γ (P.pExp i) (fun j ↦ P.rExp i j + 1) α *
        P.modelKernelOf i φ ε b t γ σ) atTop (𝓝 (P.termConst i φ ε b σ γ α)) :=
  P.tendsto_modelKernelOf hS hσ hadm htruth
    (Eventually.of_forall fun _ z _ hz ↦ hφL z hz) hφc hφ hMφ hfeas (hprof.int' _ _)
    (hprof.Φint' _ _)

/-! ### The assembly over all terms -/

/-- The term index: chart, orthant, branch. -/
abbrev TermIdx (D : WallChartsData m ℓ L') : Type := D.ι × (Fin m → Bool) × Bool

/-- The scale exponent of a term. -/
noncomputable def termLam (γ : ℝ) (α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ) (p : TermIdx D) :
    ℝ :=
  lpExponent γ (P.pExp p.1) (fun j ↦ P.rExp p.1 j + 1) (α p.1 p.2.1 p.2.2)

open scoped Classical in
/-- The kernel of a term (zero if the branch is not admissible). -/
noncomputable def termKernel (φ : (Fin (m + 1) → ℝ) → ℝ) (σ γ : ℝ) (p : TermIdx D) (t : ℝ) : ℝ :=
  if D.admissible p.1 p.2.1 p.2.2 σ then P.modelKernelOf p.1 φ p.2.1 p.2.2 t γ σ else 0

open scoped Classical in
/-- The limiting constant of a term (zero if the branch is not admissible). -/
noncomputable def termConst' (φ : (Fin (m + 1) → ℝ) → ℝ) (σ γ : ℝ)
    (α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ) (p : TermIdx D) : ℝ :=
  if D.admissible p.1 p.2.1 p.2.2 σ then P.termConst p.1 φ p.2.1 p.2.2 σ γ (α p.1 p.2.1 p.2.2)
  else 0

theorem tendsto_termKernel (hS : ∀ i, |D.S i| = 1) (hσ : σ ≠ 0)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    {φ : (Fin (m + 1) → ℝ) → ℝ} (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L')
    {α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ}
    (hfeas : ∀ i ε b, D.admissible i ε b σ →
      ConstrainedFeasible (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) (α i ε b))
    (hprof : ∀ i ε b, D.admissible i ε b σ → P.ProfileIntegrableOf i ε b σ γ (α i ε b))
    (p : TermIdx D) :
    Tendsto (fun t ↦ t ^ P.termLam γ α p * P.termKernel φ σ γ p t) atTop
      (𝓝 (P.termConst' φ σ γ α p)) := by
  classical
  unfold termKernel termConst'
  by_cases hadm : D.admissible p.1 p.2.1 p.2.2 σ
  · simp only [if_pos hadm]
    exact P.tendsto_term (hS _) hσ hadm (htruth _) hφc hφ hMφ hφL (hfeas _ _ _ hadm)
      (hprof _ _ _ hadm)
  · simp only [if_neg hadm, mul_zero]
    exact tendsto_const_nhds

open scoped Classical in
theorem totalKernel_toReal_eq_sum_terms (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z)
    (hFm : Measurable F) {φ : (Fin (m + 1) → ℝ) → ℝ} (hφm : Measurable φ) (hφ : ∀ z, 0 ≤ φ z)
    {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ) {t : ℝ} (ht : 0 < t) (hσ : σ ≠ 0) :
    (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * φ z)) (σ * t ^ (-γ))).toReal =
      ∑ p : TermIdx D, P.termKernel φ σ γ p t := by
  rw [P.totalKernel_toReal hS hF hFm hφm hφ hMφ ht hσ, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fintype.sum_prod_type]
  rfl

/-- **The expectation along the truth fibre.** For two localised observables `ψ, χ`, along the
schedule `s = σ t^{-γ}`, with a certified scale for every admissible term and a nonzero dominant
denominator constant, the ratio of the total kernels converges to the ratio of the dominant
constants. -/
theorem tendsto_fibre_expectation (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (hFm : Measurable F)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    (hσ : σ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ L') (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    {α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ}
    (hfeas : ∀ i ε b, D.admissible i ε b σ →
      ConstrainedFeasible (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) (α i ε b))
    (hprof : ∀ i ε b, D.admissible i ε b σ → P.ProfileIntegrableOf i ε b σ γ (α i ε b))
    {lam₀ : ℝ} (hmin : ∀ p : TermIdx D, lam₀ ≤ P.termLam γ α p)
    (hpos : (∑ p : TermIdx D, if P.termLam γ α p = lam₀ then P.termConst' χ σ γ α p else 0) ≠ 0) :
    Tendsto (fun t ↦
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ * t ^ (-γ))).toReal /
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ * t ^ (-γ))).toReal)
      atTop
      (𝓝 ((∑ p : TermIdx D, if P.termLam γ α p = lam₀ then P.termConst' ψ σ γ α p else 0) /
        ∑ p : TermIdx D, if P.termLam γ α p = lam₀ then P.termConst' χ σ γ α p else 0)) := by
  classical
  have hK := P.tendsto_termKernel hS hσ htruth hχc hχ hMχ hχL hfeas hprof
  have hKψ := P.tendsto_termKernel hS hσ htruth hψc hψ hMψ hψL hfeas hprof
  refine (tendsto_sum_ratio hmin hK hKψ hpos).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [P.totalKernel_toReal_eq_sum_terms hS hF hFm hψc.measurable hψ hMψ ht hσ,
    P.totalKernel_toReal_eq_sum_terms hS hF hFm hχc.measurable hχ hMχ ht hσ]

end WallChartsData.Phase

end Laplace.Multi
