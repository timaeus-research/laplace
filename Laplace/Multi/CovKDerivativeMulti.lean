/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovKRateSeparable
import Laplace.Multi.UniqueMinimum

/-!
# The temperature derivative of a Gibbs expectation, in `d` dimensions

For a `t`-independent observable `ψ` and a Gibbs measure `e^{−tL}` on `ι → ℝ`,
`d/dt ⟨ψ⟩_t = −Cov_t[L, ψ]`. This file proves it for any continuous `L ≥ 0` and continuous `ψ` with
the natural integrability at temperature `t/2` (`hasDerivAt_gibbsExpectation_of_integrable`, by
dominated differentiation on `s > t/2` and the quotient rule), then instantiates it for the
separable anharmonic measure and the observables of eq:covK — coordinates
(`hasDerivAt_gibbsExpectation_coord`), pairs
(`hasDerivAt_gibbsExpectation_coord_mul`) and quadratic probes
(`hasDerivAt_gibbsExpectation_quadratic`, by linearity and `gibbsCov_energy_quadratic_split`) — and
transports it to E2's rotated oscillator for the ambient probe `½(w−c)ᵀB(w−c) + bᵀ(w−c)`
(`hasDerivAt_gibbsExpectation_rotatedAnharmonic_probe`). So the left-hand side of eq:covK is exactly
`−∂ₜ` of the left-hand side of eq:cov's trace term plus `bᵀ` eq:mean, as its right-hand side is of
theirs (`covKFormula_eq_neg_deriv`, tide `covK-derivative`).
-/

open MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

variable {ι : Type*} [Fintype ι]

/-! ### The general identity -/

section General

variable {L ψ : (ι → ℝ) → ℝ}

/-- `d/ds ∫ ψ e^{−sL} = −∫ L ψ e^{−sL}` at `s = t > 0`, for continuous `L ≥ 0` and `ψ` with
`ψ e^{−(t/2)L}` and `L ψ e^{−(t/2)L}` integrable. -/
theorem hasDerivAt_integral_mul_exp (hL : Continuous L) (hL0 : ∀ u, 0 ≤ L u) (hψ : Continuous ψ)
    {t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun u => L u * ψ u * Real.exp (-(t / 2 * L u))))
    (hint0 : Integrable (fun u => ψ u * Real.exp (-(t / 2 * L u)))) :
    HasDerivAt (fun s : ℝ => ∫ u, ψ u * Real.exp (-(s * L u)))
      (-∫ u, L u * ψ u * Real.exp (-(t * L u))) t := by
  have hexp : ∀ {s : ℝ}, t / 2 ≤ s → ∀ u,
      Real.exp (-(s * L u)) ≤ Real.exp (-(t / 2 * L u)) := fun {s} hs u => by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hs (hL0 u)
    linarith
  have hbound : ∀ u, ‖ψ u * Real.exp (-(t * L u))‖ ≤ ‖ψ u * Real.exp (-(t / 2 * L u))‖ := by
    intro u
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
    exact hexp (by linarith) u
  have hmeas : AEStronglyMeasurable (fun u => ψ u * Real.exp (-(t * L u))) volume :=
    (hψ.mul ((hL.const_mul t).neg.rexp)).aestronglyMeasurable
  have hF_int : Integrable (fun u => ψ u * Real.exp (-(t * L u))) :=
    Integrable.mono' hint0.norm hmeas (Eventually.of_forall hbound)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s u => ψ u * Real.exp (-(s * L u)))
    (F' := fun s u => -(L u * ψ u * Real.exp (-(s * L u))))
    (bound := fun u => ‖L u * ψ u * Real.exp (-(t / 2 * L u))‖)
    (x₀ := t) (s := Set.Ioi (t / 2)) (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun s => (hψ.mul ((hL.const_mul s).neg.rexp)).aestronglyMeasurable)
    hF_int
    (((hL.mul hψ).mul ((hL.const_mul t).neg.rexp)).neg.aestronglyMeasurable)
    (Eventually.of_forall fun u s hs => ?_) hint.norm
    (Eventually.of_forall fun u s _ => ?_)
  · rw [integral_neg] at key
    exact key.2
  · rw [norm_neg, norm_mul (L u * ψ u), norm_mul (L u * ψ u)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (L u * ψ u))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
    exact hexp (Set.mem_Ioi.mp hs).le u
  · have h := (((hasDerivAt_id' (x := s)).mul_const (L u)).neg.exp).const_mul (ψ u)
    exact h.congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- **`d/ds ⟨ψ⟩_s = −Cov_t[L, ψ]`** for continuous `L ≥ 0`, continuous `ψ`, the integrability of
`ψ e^{−(t/2)L}`, `L ψ e^{−(t/2)L}`, `e^{−(t/2)L}`, `L e^{−(t/2)L}`, and `Z(t) ≠ 0`. -/
theorem hasDerivAt_gibbsExpectation_of_integrable (hL : Continuous L) (hL0 : ∀ u, 0 ≤ L u)
    (hψ : Continuous ψ) {t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun u => L u * ψ u * Real.exp (-(t / 2 * L u))))
    (hint0 : Integrable (fun u => ψ u * Real.exp (-(t / 2 * L u))))
    (hintL : Integrable (fun u => L u * Real.exp (-(t / 2 * L u))))
    (hint1 : Integrable (fun u => Real.exp (-(t / 2 * L u))))
    (hZ : partitionFunction L t ≠ 0) :
    HasDerivAt (fun s => gibbsExpectation L s ψ) (-gibbsCov L t L ψ) t := by
  have hN := hasDerivAt_integral_mul_exp hL hL0 hψ ht hint hint0
  have hZ' := hasDerivAt_integral_mul_exp (ψ := fun _ => (1 : ℝ)) hL hL0 continuous_const ht
    (by simpa using hintL) (by simpa using hint1)
  simp only [mul_one, one_mul] at hZ'
  have hZne : (∫ u, Real.exp (-(t * L u))) ≠ 0 := hZ
  have h := hN.div hZ' hZne
  refine h.congr_deriv ?_
  simp only [gibbsCov, gibbsExpectation, partitionFunction]
  set N := ∫ u, ψ u * Real.exp (-(t * L u)) with hN'
  set Z := ∫ u, Real.exp (-(t * L u)) with hZ''
  set LN := ∫ u, L u * ψ u * Real.exp (-(t * L u)) with hLN
  set LZ := ∫ u, L u * Real.exp (-(t * L u)) with hLZ
  clear_value N Z LN LZ
  field_simp
  ring

/-- Gibbs expectations are linear in the observable, given integrability of each piece. -/
theorem gibbsExpectation_finsetSum_of_integrable {κ : Type*} (s : Finset κ)
    (f : κ → (ι → ℝ) → ℝ) (t : ℝ)
    (hf : ∀ k ∈ s, Integrable (fun u => f k u * Real.exp (-(t * L u)))) :
    gibbsExpectation L t (fun u => ∑ k ∈ s, f k u) = ∑ k ∈ s, gibbsExpectation L t (f k) := by
  unfold gibbsExpectation
  rw [← Finset.sum_div, ← integral_finsetSum s hf]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Finset.sum_mul]

end General

/-! ### The separable anharmonic measure -/

section Separable

variable {lam alpha gamma : ι → ℝ}

theorem separableAnharmonic_nonneg (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (u : ι → ℝ) :
    0 ≤ separableAnharmonic lam alpha gamma u :=
  Finset.sum_nonneg fun i _ => anharmonicPotential_nonneg (hgamma i) (hdisc i) (u i)

theorem partitionFunction_separableAnharmonic_pos (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) :
    0 < partitionFunction (separableAnharmonic lam alpha gamma) t := by
  rw [separableAnharmonic, partitionFunction_separable]
  exact Finset.prod_pos fun i _ => partitionFunction_anharmonic_pos (hlam i) (hgamma i) (hdisc i) ht

theorem integrable_exp_neg_separableAnharmonic' (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) :
    Integrable (fun u : ι → ℝ => Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  have := integrable_monomial_separableAnharmonic hlam hgamma hdisc ht (fun _ => 0)
  simpa using this

theorem integrable_energy_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) :
    Integrable (fun u : ι → ℝ => separableAnharmonic lam alpha gamma u *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  have := integrable_energy_mul_separableAnharmonic (lam := lam) (alpha := alpha) (gamma := gamma)
    (t := t) (fun _ => (1 : ℝ)) (fun k => by
      simpa using integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k k 0)
  simpa using this

/-- `d/ds ⟨uᵢ⟩_s = −Cov_t[L, uᵢ]`. -/
theorem hasDerivAt_gibbsExpectation_coord (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t)
    (i : ι) :
    HasDerivAt (fun s => gibbsExpectation (separableAnharmonic lam alpha gamma) s (fun u => u i))
      (-gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => u i)) t := by
  have ht2 := half_pos ht
  refine hasDerivAt_gibbsExpectation_of_integrable (continuous_separableAnharmonic lam alpha gamma)
    (separableAnharmonic_nonneg hgamma hdisc) (continuous_apply i) ht ?_
    (integrable_coord_separableAnharmonic hlam hgamma hdisc ht2 i)
    (integrable_energy_separableAnharmonic hlam hgamma hdisc ht2)
    (integrable_exp_neg_separableAnharmonic' hlam hgamma hdisc ht2)
    (partitionFunction_separableAnharmonic_pos hlam hgamma hdisc ht).ne'
  exact integrable_energy_mul_separableAnharmonic (fun u => u i) fun k => by
    simpa using integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht2 k i 1

/-- `d/ds ⟨uᵢuⱼ⟩_s = −Cov_t[L, uᵢuⱼ]`. -/
theorem hasDerivAt_gibbsExpectation_coord_mul (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) (i j : ι) :
    HasDerivAt (fun s => gibbsExpectation (separableAnharmonic lam alpha gamma) s
        (fun u => u i * u j))
      (-gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => u i * u j)) t := by
  have ht2 := half_pos ht
  refine hasDerivAt_gibbsExpectation_of_integrable (continuous_separableAnharmonic lam alpha gamma)
    (separableAnharmonic_nonneg hgamma hdisc) ((continuous_apply i).mul (continuous_apply j)) ht
    (integrable_energy_mul_separableAnharmonic (fun u => u i * u j) fun k =>
      integrable_energy_coord_mul_separableAnharmonic hlam hgamma hdisc ht2 k i j)
    (integrable_coord_mul_separableAnharmonic hlam hgamma hdisc ht2 i j)
    (integrable_energy_separableAnharmonic hlam hgamma hdisc ht2)
    (integrable_exp_neg_separableAnharmonic' hlam hgamma hdisc ht2)
    (partitionFunction_separableAnharmonic_pos hlam hgamma hdisc ht).ne'

/-- The quadratic probe's expectation is the linear combination of pair and coordinate moments. -/
theorem gibbsExpectation_quadratic_eq (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {s : ℝ} (hs : 0 < s) (B : ι → ι → ℝ)
    (b : ι → ℝ) :
    gibbsExpectation (separableAnharmonic lam alpha gamma) s
        (fun u => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) =
      ∑ p : ι × ι, B p.1 p.2 / 2 * gibbsExpectation (separableAnharmonic lam alpha gamma) s
        (fun u => u p.1 * u p.2) +
      ∑ i, b i * gibbsExpectation (separableAnharmonic lam alpha gamma) s (fun u => u i) := by
  have hcm : ∀ p : ι × ι, Integrable (fun u : ι → ℝ => B p.1 p.2 / 2 * (u p.1 * u p.2) *
      Real.exp (-(s * separableAnharmonic lam alpha gamma u))) := fun p => by
    have := (integrable_coord_mul_separableAnharmonic hlam hgamma hdisc hs p.1 p.2).const_mul
      (B p.1 p.2 / 2)
    exact this.congr (Eventually.of_forall fun u => by ring)
  have hc : ∀ i, Integrable (fun u : ι → ℝ => b i * u i *
      Real.exp (-(s * separableAnharmonic lam alpha gamma u))) := fun i => by
    have := (integrable_coord_separableAnharmonic hlam hgamma hdisc hs i).const_mul (b i)
    exact this.congr (Eventually.of_forall fun u => by ring)
  have e : (fun u : ι → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) =
      fun u => (∑ p : ι × ι, B p.1 p.2 / 2 * (u p.1 * u p.2)) + ∑ i, b i * u i := by
    funext u
    rw [← Fintype.sum_prod_type']
  have h1 : Integrable (fun u : ι → ℝ => (∑ p : ι × ι, B p.1 p.2 / 2 * (u p.1 * u p.2)) *
      Real.exp (-(s * separableAnharmonic lam alpha gamma u))) :=
    (integrable_finsetSum Finset.univ fun p _ => hcm p).congr (Eventually.of_forall fun u => by
      simp only [Finset.sum_mul])
  have h2 : Integrable (fun u : ι → ℝ => (∑ i, b i * u i) *
      Real.exp (-(s * separableAnharmonic lam alpha gamma u))) :=
    (integrable_finsetSum Finset.univ fun i _ => hc i).congr (Eventually.of_forall fun u => by
      simp only [Finset.sum_mul])
  rw [e, gibbsExpectation_add_of_integrable (L := separableAnharmonic lam alpha gamma) (t := s) _ _
    h1 h2,
    gibbsExpectation_finsetSum_of_integrable _ _ _ (fun p _ => hcm p),
    gibbsExpectation_finsetSum_of_integrable _ _ _ (fun i _ => hc i)]
  simp only [gibbsExpectation_const_mul]

/-- **`d/ds ⟨ψ⟩_s = −Cov_t[L, ψ]` for the quadratic probe** `ψ(u) = ∑ᵢⱼ Bᵢⱼ/2 uᵢuⱼ + ∑ᵢ bᵢuᵢ`. -/
theorem hasDerivAt_gibbsExpectation_quadratic (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) (B : ι → ι → ℝ)
    (b : ι → ℝ) :
    HasDerivAt (fun s => gibbsExpectation (separableAnharmonic lam alpha gamma) s
        (fun u => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i))
      (-gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i)) t := by
  have h := (HasDerivAt.sum (u := Finset.univ) fun (p : ι × ι) _ =>
      (hasDerivAt_gibbsExpectation_coord_mul hlam hgamma hdisc ht p.1 p.2).const_mul
        (B p.1 p.2 / 2)).add
    (HasDerivAt.sum (u := Finset.univ) fun i _ =>
      (hasDerivAt_gibbsExpectation_coord hlam hgamma hdisc ht i).const_mul (b i))
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [gibbsExpectation_quadratic_eq hlam hgamma hdisc hs B b]
    simp [Finset.sum_apply]
  · rw [gibbsCov_energy_quadratic_split hlam hgamma hdisc ht B b]
    simp only [mul_neg, Finset.sum_neg_distrib, neg_add]

end Separable

/-! ### E2's rotated oscillator -/

section Rotated

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ}

/-- **The left-hand side of eq:covK is `−∂ₜ` of the probe's expectation**, for E2's oscillator and
the ambient probe `½(w−c)ᵀB(w−c) + bᵀ(w−c)`. -/
theorem hasDerivAt_gibbsExpectation_rotatedAnharmonic_probe (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    HasDerivAt (fun s => gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) s
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)))
      (-gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c))) t := by
  have hc := continuous_separableAnharmonic lam alpha gamma
  have hψ : Continuous fun u : Fin d → ℝ =>
      ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) + ∑ i, (Qᵀ *ᵥ b) i * u i :=
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop).add
      (continuous_finsetSum _ fun i _ => by fun_prop)
  have hprobe : (fun w : Fin d → ℝ => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      rotated Q c (fun u => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) +
        ∑ i, (Qᵀ *ᵥ b) i * u i) :=
    funext (probe_affineFrame hQ c B b)
  have hexp : ∀ s, gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) s
      (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      gibbsExpectation (separableAnharmonic lam alpha gamma) s
        (fun u => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) + ∑ i, (Qᵀ *ᵥ b) i * u i) :=
      fun s => by
    rw [hprobe]
    exact gibbsExpectation_rotated_of_continuous hQ c hc hψ s
  have hcov : gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
      (rotatedAnharmonic Q c lam alpha gamma)
      (fun w => 1 / 2 * ((w - c) ⬝ᵥ (B *ᵥ (w - c))) + b ⬝ᵥ (w - c)) =
      gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => ∑ i, ∑ j, (Qᵀ * B * Q) i j / 2 * (u i * u j) + ∑ i, (Qᵀ *ᵥ b) i * u i) := by
    rw [hprobe]
    exact gibbsCov_rotated_of_continuous hQ c hc hc hψ t
  simp only [hexp, hcov]
  exact hasDerivAt_gibbsExpectation_quadratic hlam hgamma hdisc ht (fun i j => (Qᵀ * B * Q) i j)
    (Qᵀ *ᵥ b)

end Rotated

end Laplace.Multi
