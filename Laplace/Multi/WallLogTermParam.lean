/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ParameterStability
import Laplace.Multi.WallFibreExpectationLog

/-!
# The logarithmic term with a moving parameter `σ(t) → σ₀`

The parameter `σ` of the truth ray `s = σ t^{-γ}` enters the chart kernels only through the three
constants `A = |σ|^p/q`, `B = |σ|^ν`, `D = |σ|^{1/q}`, which are continuous in `σ ≠ 0`
(`tendsto_constA`, `tendsto_constB`, `tendsto_constD`), and through the admissibility of a sign
branch, which is eventually constant along `σ(t) → σ₀ ≠ 0` (`admissible_eventually_iff`). Hence
the power–log law of a fully tied chart holds along a moving parameter with the constant at `σ₀`
(`tendsto_modelKernelOf_tied_param`, `tendsto_termKernel_tied_param`), and the lexicographic
assembly of the fibre expectation holds along `σ(t)` (`tendsto_fibre_expectation_lex_param`): the
leading expectations at a moving parameter converge to the ratio of the limiting coefficients at
`σ₀` (Astra, round 5, target 1: parameter stability).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData

variable (D : WallChartsData m ℓ L') {i : D.ι} {ε : Fin m → Bool} {b : Bool} {σ : ℝ → ℝ} {σ₀ : ℝ}

theorem tendsto_abs_comp (hσ : Tendsto σ atTop (𝓝 σ₀)) :
    Tendsto (fun t ↦ |σ t|) atTop (𝓝 |σ₀|) :=
  (continuous_abs.tendsto σ₀).comp hσ

omit D in
theorem tendsto_abs_rpow (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) (e : ℝ) :
    Tendsto (fun t ↦ |σ t| ^ e) atTop (𝓝 (|σ₀| ^ e)) :=
  (tendsto_abs_comp hσ).rpow_const (Or.inl (abs_ne_zero.mpr hσ₀))

/-- The cutoff constant is continuous in the parameter. -/
theorem tendsto_constD (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) :
    Tendsto (fun t ↦ D.constD i (σ t)) atTop (𝓝 (D.constD i σ₀)) :=
  tendsto_abs_rpow hσ hσ₀ _

/-- The cutoff variable `D(σ(t)) t^{-γ/q}` vanishes along a convergent parameter. -/
theorem tendsto_constD_cut (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) {γ q : ℝ}
    (hγq : 0 < γ / q) :
    Tendsto (fun t ↦ D.constD i (σ t) * t ^ (-(γ / q))) atTop (𝓝 0) := by
  have := (D.tendsto_constD (i := i) hσ hσ₀).mul (tendsto_rpow_neg_atTop hγq)
  rwa [mul_zero] at this

/-- Admissibility of a sign branch is eventually constant along `σ(t) → σ₀ ≠ 0`. -/
theorem admissible_eventually_iff (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) :
    ∀ᶠ t in atTop, (D.admissible i ε b (σ t) ↔ D.admissible i ε b σ₀) := by
  unfold admissible
  have hc : D.orthSign i ε * (if b then 1 else (-1) ^ D.q i (D.k i)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · unfold orthSign
      exact mul_ne_zero (D.S_ne i) (Finset.prod_ne_zero_iff.mpr fun j _ ↦
        pow_ne_zero _ (by cases ε j <;> simp [bsign]))
    · split_ifs
      · exact one_ne_zero
      · exact pow_ne_zero _ (by norm_num)
  have hlim : Tendsto (fun t ↦ D.orthSign i ε * (if b then 1 else (-1) ^ D.q i (D.k i)) * σ t)
      atTop (𝓝 (D.orthSign i ε * (if b then 1 else (-1) ^ D.q i (D.k i)) * σ₀)) :=
    hσ.const_mul _
  rcases lt_or_gt_of_ne (mul_ne_zero hc hσ₀) with h | h
  · filter_upwards [hlim.eventually_lt_const h] with t ht
    exact ⟨fun h' ↦ absurd h' (not_lt.mpr ht.le), fun h' ↦ absurd h' (not_lt.mpr h.le)⟩
  · filter_upwards [hlim.eventually_const_lt h] with t ht
    exact ⟨fun _ ↦ h, fun _ ↦ ht⟩

namespace Phase

variable {D} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- The model prefactor is continuous in the parameter. -/
theorem tendsto_constA (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) :
    Tendsto (fun t ↦ P.constA i (σ t)) atTop (𝓝 (P.constA i σ₀)) :=
  (tendsto_abs_rpow hσ hσ₀ _).div_const _

/-- The model scale is continuous in the parameter. -/
theorem tendsto_constB (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) :
    Tendsto (fun t ↦ P.constB i (σ t)) atTop (𝓝 (P.constB i σ₀)) :=
  tendsto_abs_rpow hσ hσ₀ _

end Phase

end WallChartsData

section Tied

variable {k : ℕ} {ℓ : Fin (k + 1 + 1)} {L' : Set (Fin (k + 1 + 1) → ℝ)}
  {D : WallChartsData (k + 1) ℓ L'} {F : (Fin (k + 1 + 1) → ℝ) → ℝ} (P : D.Phase F)
  {i : D.ι} {ε : Fin (k + 1) → Bool} {b : Bool} {σ : ℝ → ℝ} {σ₀ γ : ℝ}
  {φ : (Fin (k + 1 + 1) → ℝ) → ℝ}

/-- **The logarithmic term along a moving parameter**: the power–log law of a fully tied chart
with `σ(t) → σ₀ ≠ 0`, with the constant at `σ₀`. -/
theorem WallChartsData.Phase.tendsto_modelKernelOf_tied_param (hσ : Tendsto σ atTop (𝓝 σ₀))
    (hσ₀ : σ₀ ≠ 0) (hγ : 0 < γ) (hQ : D.Qexp i = 0) (hκ : ∀ j, 0 < P.kappa i j) {lam : ℝ}
    (hlam : 0 < lam) (htied : ∀ j, (P.rExp i j + 1) / P.kappa i j = lam)
    (hδ : 0 < P.phaseExp i γ) (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + P.phaseExp i γ * lam) / log t ^ k *
        P.modelKernelOf i φ ε b t γ (σ t)) atTop
      (𝓝 (tiedConst (P.constA i σ₀) (P.constB i σ₀) (P.phaseExp i γ) (P.kappa i) (P.rExp i) lam
        (D.ρ i) |P.a i 0| (φ (D.rep i 0) * (P.wt i 0 * |P.b i 0|)))) := by
  unfold WallChartsData.Phase.modelKernelOf
  rw [hQ]
  refine tendsto_modelKernel_tied_param (D.ρ_pos i) hκ hlam htied (P.tendsto_constA hσ hσ₀)
    (Eventually.of_forall fun _ ↦ P.constA_nonneg) (P.tendsto_constB hσ hσ₀) (P.constB_pos hσ₀)
    (Eventually.of_forall fun t ↦ D.constD_nonneg i (σ t))
    (D.tendsto_constD_cut hσ hσ₀ (div_pos hγ (Nat.cast_pos.mpr (D.q_pos i)))) hδ (P.ma_pos i)
    (P.measurable_weightFn hφc.measurable) P.measurable_unitFn (P.weightFn_nonneg hφ)
    (fun x v ↦ (le_abs_self _).trans (P.abs_weightFn_le hφ hMφ x v))
    (fun x v hx hv0 hv ↦ P.ma_le_unitFn hx hv0 hv) ((P.ma_pos i).trans_le P.ma_le_abs_a_zero)
    (mul_nonneg (hφ _) (mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)))
    (P.tendsto_weightFn_face hφc hφL) P.tendsto_unitFn_face

open scoped Classical in
/-- An admissible (at `σ₀`) branch of a fully tied chart along a moving parameter. -/
theorem WallChartsData.Phase.tendsto_termKernel_tied_param (hσ : Tendsto σ atTop (𝓝 σ₀))
    (hσ₀ : σ₀ ≠ 0) (hγ : 0 < γ) {p : WallChartsData.Phase.TermIdx D}
    (hadm : D.admissible p.1 p.2.1 p.2.2 σ₀) (hQ : D.Qexp p.1 = 0)
    (hκ : ∀ j, 0 < P.kappa p.1 j) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ j, (P.rExp p.1 j + 1) / P.kappa p.1 j = lam) (hδ : 0 < P.phaseExp p.1 γ)
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp p.1 + P.phaseExp p.1 γ * lam) / log t ^ k *
        P.termKernel φ (σ t) γ p t) atTop
      (𝓝 (tiedConst (P.constA p.1 σ₀) (P.constB p.1 σ₀) (P.phaseExp p.1 γ) (P.kappa p.1)
        (P.rExp p.1) lam (D.ρ p.1) |P.a p.1 0|
        (φ (D.rep p.1 0) * (P.wt p.1 0 * |P.b p.1 0|)))) := by
  have h := P.tendsto_modelKernelOf_tied_param (ε := p.2.1) (b := p.2.2) hσ hσ₀ hγ hQ hκ hlam htied
    hδ hφc hφ hMφ hφL
  refine h.congr' ?_
  filter_upwards [D.admissible_eventually_iff (i := p.1) (ε := p.2.1) (b := p.2.2) hσ hσ₀] with t ht
  unfold WallChartsData.Phase.termKernel
  rw [if_pos (ht.mpr hadm)]

open scoped Classical in
/-- A non-admissible (at `σ₀`) branch is eventually zero along a moving parameter. -/
theorem WallChartsData.Phase.tendsto_termKernel_of_not_admissible_param
    (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) {p : WallChartsData.Phase.TermIdx D}
    (h : ¬ D.admissible p.1 p.2.1 p.2.2 σ₀) (lam : ℝ) (k' : ℕ) :
    Tendsto (fun t ↦ t ^ lam / log t ^ k' * P.termKernel φ (σ t) γ p t) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [D.admissible_eventually_iff (i := p.1) (ε := p.2.1) (b := p.2.2) hσ hσ₀] with t ht
  unfold WallChartsData.Phase.termKernel
  rw [if_neg (fun h' ↦ h (ht.mp h')), mul_zero]

end Tied

/-- **The fibre expectation along a moving parameter.** The lexicographic assembly with every
term certified along `σ(t)`. -/
theorem WallChartsData.Phase.tendsto_fibre_expectation_lex_param {D : WallChartsData m ℓ L'}
    {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {σ : ℝ → ℝ} {σ₀ γ : ℝ}
    (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (hFm : Measurable F)
    (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ}
    (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ} (hMψ : ∀ z, ψ z ≤ Mψ) (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ)
    {lam : WallChartsData.Phase.TermIdx D → ℝ} {kk : WallChartsData.Phase.TermIdx D → ℕ}
    {Cψ Cχ : WallChartsData.Phase.TermIdx D → ℝ} {lam₀ : ℝ} {k₀ : ℕ}
    (hmin : ∀ p, lam₀ ≤ lam p ∧ (lam p = lam₀ → kk p ≤ k₀))
    (hKψ : ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel ψ (σ t) γ p t) atTop
      (𝓝 (Cψ p)))
    (hKχ : ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel χ (σ t) γ p t) atTop
      (𝓝 (Cχ p)))
    (hpos : (∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), Cχ p) ≠ 0) :
    Tendsto (fun t ↦
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ t * t ^ (-γ))).toReal /
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ t * t ^ (-γ))).toReal)
      atTop
      (𝓝 ((∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), Cψ p) /
        ∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), Cχ p)) := by
  classical
  refine (tendsto_sum_ratio_lex hmin hKχ hKψ hpos).congr' ?_
  filter_upwards [eventually_gt_atTop 0, hσ.eventually_ne hσ₀] with t ht hσt
  rw [P.totalKernel_toReal_eq_sum_terms hS hF hFm hψc.measurable hψ hMψ ht hσt,
    P.totalKernel_toReal_eq_sum_terms hS hF hFm hχc.measurable hχ hMχ ht hσt]

end Laplace.Multi
