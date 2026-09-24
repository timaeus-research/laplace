/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GaussianMomentsPosDef

/-!
# The constrained exponent LP and its compatibility with the rescaling

Astra's lemma 5 (`research_kernel_asymptotics_v1`, §1.2 and §8). Under the logarithmic scaling
`x_j = t^{-α_j} u_j` of the unsolved coordinates of a wall chart, the box gives `α ≥ 0`, the moving
cutoff `v_t(x) = D t^{-γ/q} ∏ x_j^{-Q_j/q} < 1` gives `Q·α ≤ γ`, and avoiding exponential
suppression of the phase `t^{δ} ∏ x_j^{κ_j}` (`δ = 1 − γν`) gives `κ·α ≥ δ`. The relevant
polyhedron is `P_γ = {α ≥ 0, Q·α ≤ γ, κ·α ≥ δ}` (`ConstrainedFeasible`) and the exponent is
`λ = γp + min_{P_γ} b·α` with `b_j = r_j + 1` (`lpExponent`). A `ConstrainedLPCert` is a feasible
`α` together with dual multipliers `μ, τ ≥ 0` certifying optimality by weak duality
(`ConstrainedLPCert.le`).

The compatibility statement (`modelKernel_eq_rescaled`): the constrained model kernel
`K(t) = A t^{-γp} ∫_{(0,1)^d, v_t < 1} W(x, v_t) ∏x^r e^{-B t^δ a(x, v_t) ∏x^κ} dx`
is exactly `A t^{-λ}` times the rescaled integral over `u ∈ ∏(0, t^{α_j})` with cutoff
`D t^{-(γ − Q·α)/q} ∏u^{-Q/q} < 1` and phase `B t^{δ − κ·α} a ∏u^κ` — so the exponent that factors
out is the LP value at `α`, and the two feasibility conditions say exactly that the remaining
`t`-powers are `≤ 1` for `t ≥ 1` (`rpow_truth_le_one`, `rpow_phase_le_one`), tending to `0` when
the constraint is strict. This is the moving-kernel form consumed by `ProfileCertificate`.
-/

open Real MeasureTheory Filter Topology Set
open scoped Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-! ### The constrained LP -/

/-- Feasibility for `P_γ = {α ≥ 0, Q·α ≤ γ, κ·α ≥ δ}`. -/
def ConstrainedFeasible (Q κ : ι → ℝ) (γ δ : ℝ) (α : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ α j) ∧ ∑ j, Q j * α j ≤ γ ∧ δ ≤ ∑ j, κ j * α j

/-- An optimality certificate for `min_{P_γ} b·α`: a feasible `α` and dual multipliers `μ` (for
`Q·α ≤ γ`) and `τ` (for `κ·α ≥ δ`) with `b + μQ − τκ ≥ 0` and `b·α = τδ − μγ`. -/
structure ConstrainedLPCert (Q κ b : ι → ℝ) (γ δ : ℝ) (α : ι → ℝ) (μ τ : ℝ) : Prop where
  feasible : ConstrainedFeasible Q κ γ δ α
  hμ : 0 ≤ μ
  hτ : 0 ≤ τ
  dual : ∀ j, 0 ≤ b j + μ * Q j - τ * κ j
  slack : ∑ j, b j * α j = τ * δ - μ * γ

/-- **Weak duality**: a certified `α` minimises `b·α` over `P_γ`. -/
theorem ConstrainedLPCert.le {Q κ b : ι → ℝ} {γ δ : ℝ} {α : ι → ℝ} {μ τ : ℝ}
    (hc : ConstrainedLPCert Q κ b γ δ α μ τ) {α' : ι → ℝ}
    (hα' : ConstrainedFeasible Q κ γ δ α') : ∑ j, b j * α j ≤ ∑ j, b j * α' j := by
  obtain ⟨h0, htruth, hphase⟩ := hα'
  have h1 : 0 ≤ ∑ j, (b j + μ * Q j - τ * κ j) * α' j :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hc.dual j) (h0 j)
  have e : ∑ j, (b j + μ * Q j - τ * κ j) * α' j =
      ∑ j, b j * α' j + μ * ∑ j, Q j * α' j - τ * ∑ j, κ j * α' j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have h2 := mul_le_mul_of_nonneg_left htruth hc.hμ
  have h3 := mul_le_mul_of_nonneg_left hphase hc.hτ
  rw [hc.slack]
  linarith

/-- The exponent `λ = γp + b·α`. -/
noncomputable def lpExponent (γ p : ℝ) (b α : ι → ℝ) : ℝ := γ * p + ∑ j, b j * α j

theorem lpExponent_succ (γ p : ℝ) (r α : ι → ℝ) :
    lpExponent γ p (fun j ↦ r j + 1) α = γ * p + ∑ j, r j * α j + ∑ j, α j := by
  unfold lpExponent
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-! ### The rescaling `x = t^{-α} u` -/

/-- The logarithmic rescaling `u ↦ (t^{-α_j} u_j)_j`. -/
noncomputable def rescale (t : ℝ) (α : ι → ℝ) (u : ι → ℝ) : ι → ℝ := fun j ↦ t ^ (-α j) * u j

omit [Fintype ι] in
theorem rescale_pos {t : ℝ} (ht : 0 < t) (α : ι → ℝ) {u : ι → ℝ} (hu : ∀ j, 0 < u j) (j : ι) :
    0 < rescale t α u j :=
  mul_pos (rpow_pos_of_pos ht _) (hu j)

/-- A monomial under the rescaling: `∏ (t^{-α_j} u_j)^{e_j} = t^{-e·α} ∏ u_j^{e_j}`. -/
theorem prod_rpow_rescale {t : ℝ} (ht : 0 < t) (α : ι → ℝ) {u : ι → ℝ} (hu : ∀ j, 0 < u j)
    (e : ι → ℝ) :
    ∏ j, rescale t α u j ^ e j = t ^ (-∑ j, e j * α j) * ∏ j, u j ^ e j := by
  have h : ∀ j, rescale t α u j ^ e j = t ^ (-(e j * α j)) * u j ^ e j := fun j ↦ by
    unfold rescale
    rw [Real.mul_rpow (rpow_pos_of_pos ht _).le (hu j).le, ← Real.rpow_mul ht.le]
    congr 2
    ring
  simp only [h, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos ht]

omit [Fintype ι] in
theorem mem_Ioo_rescale_iff {t : ℝ} (ht : 0 < t) (α : ι → ℝ) (u : ι → ℝ) (j : ι) :
    rescale t α u j ∈ Ioo (0 : ℝ) 1 ↔ u j ∈ Ioo 0 (t ^ α j) := by
  have hc : 0 < t ^ α j := rpow_pos_of_pos ht _
  unfold rescale
  rw [mem_Ioo, mem_Ioo, Real.rpow_neg ht.le, inv_mul_lt_iff₀ hc, mul_one,
    mul_pos_iff_of_pos_left (inv_pos.mpr hc)]

/-- The Lebesgue change of variables `x = t^{-α} u` on `ι → ℝ`. -/
theorem integral_comp_rescale {t : ℝ} (ht : 0 < t) (α : ι → ℝ) (g : (ι → ℝ) → ℝ)
    (hg : AEStronglyMeasurable g volume) :
    ∫ x, g x = (∏ j, t ^ (-α j)) * ∫ u, g (rescale t α u) := by
  classical
  have hdet : (Matrix.diagonal fun j ↦ t ^ (-α j)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact (Finset.prod_pos fun j _ ↦ rpow_pos_of_pos ht _).ne'
  have hres : ∀ v, (Matrix.diagonal fun j ↦ t ^ (-α j)) *ᵥ v = rescale t α v := fun v ↦ by
    funext j
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [integral_comp_mulVec _ hdet g hg, Matrix.det_diagonal,
    abs_of_pos (Finset.prod_pos fun j _ ↦ rpow_pos_of_pos ht _)]
  simp only [hres]

/-! ### The constrained model kernel -/

/-- The moving cutoff variable `v_t(x) = D t^{-γ/q} ∏ x_j^{-Q_j/q}`. -/
noncomputable def cutVar (D γ q : ℝ) (Q : ι → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  D * t ^ (-(γ / q)) * ∏ j, x j ^ (-(Q j / q))

/-- The model domain: the open unit box cut by `v_t < 1`. -/
def modelDomain (D γ q : ℝ) (Q : ι → ℝ) (t : ℝ) : Set (ι → ℝ) :=
  Set.pi univ (fun _ ↦ Ioo (0 : ℝ) 1) ∩ {x | cutVar D γ q Q t x < 1}

/-- The model integrand `1_{domain} W(x, v_t) ∏x^r e^{-B t^δ a(x, v_t) ∏x^κ}`. -/
noncomputable def modelIntegrand (B D γ q δ : ℝ) (Q κ r : ι → ℝ) (W a : (ι → ℝ) → ℝ → ℝ) (t : ℝ)
    (x : ι → ℝ) : ℝ :=
  (modelDomain D γ q Q t).indicator (fun x ↦
    W x (cutVar D γ q Q t x) * (∏ j, x j ^ r j) *
      exp (-(B * t ^ δ * a x (cutVar D γ q Q t x) * ∏ j, x j ^ κ j))) x

/-- The constrained model kernel `K(t) = A t^{-γp} ∫ modelIntegrand`. -/
noncomputable def modelKernel (A B D γ p q δ : ℝ) (Q κ r : ι → ℝ) (W a : (ι → ℝ) → ℝ → ℝ)
    (t : ℝ) : ℝ :=
  A * t ^ (-(γ * p)) * ∫ x, modelIntegrand B D γ q δ Q κ r W a t x

/-- The rescaled cutoff variable `D t^{-(γ − Q·α)/q} ∏ u_j^{-Q_j/q}`. -/
noncomputable def rescaledCut (D γ q : ℝ) (Q α : ι → ℝ) (t : ℝ) (u : ι → ℝ) : ℝ :=
  D * t ^ (-((γ - ∑ j, Q j * α j) / q)) * ∏ j, u j ^ (-(Q j / q))

/-- The rescaled domain `∏ (0, t^{α_j})` cut by the rescaled cutoff. -/
def rescaledDomain (D γ q : ℝ) (Q α : ι → ℝ) (t : ℝ) : Set (ι → ℝ) :=
  Set.pi univ (fun j ↦ Ioo (0 : ℝ) (t ^ α j)) ∩ {u | rescaledCut D γ q Q α t u < 1}

/-- The rescaled integrand: the moving-kernel form with phase `B t^{δ − κ·α} a ∏u^κ`. -/
noncomputable def rescaledIntegrand (B D γ q δ : ℝ) (Q κ r α : ι → ℝ) (W a : (ι → ℝ) → ℝ → ℝ)
    (t : ℝ) (u : ι → ℝ) : ℝ :=
  (rescaledDomain D γ q Q α t).indicator (fun u ↦
    W (rescale t α u) (rescaledCut D γ q Q α t u) * (∏ j, u j ^ r j) *
      exp (-(B * t ^ (δ - ∑ j, κ j * α j) * a (rescale t α u) (rescaledCut D γ q Q α t u) *
        ∏ j, u j ^ κ j))) u

variable {D γ q : ℝ} {Q α : ι → ℝ}

theorem cutVar_rescale {t : ℝ} (ht : 0 < t) {u : ι → ℝ} (hu : ∀ j, 0 < u j) :
    cutVar D γ q Q t (rescale t α u) = rescaledCut D γ q Q α t u := by
  unfold cutVar rescaledCut
  rw [prod_rpow_rescale ht α hu, ← mul_assoc, mul_assoc D, ← Real.rpow_add ht]
  have e : ∑ j, -(Q j / q) * α j = -(∑ j, Q j * α j) / q := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [e]
  congr 2
  ring_nf

theorem mem_modelDomain_rescale_iff {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    rescale t α u ∈ modelDomain D γ q Q t ↔ u ∈ rescaledDomain D γ q Q α t := by
  simp only [modelDomain, rescaledDomain, mem_inter_iff, Set.mem_univ_pi, mem_ofPred_eq,
    mem_Ioo_rescale_iff ht]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [cutVar_rescale ht fun j ↦ (h1 j).1] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [cutVar_rescale ht fun j ↦ (h1 j).1]

variable {B δ : ℝ} {κ r : ι → ℝ} {W a : (ι → ℝ) → ℝ → ℝ}

/-- The model integrand under the rescaling: the density exponent `r·α` factors out. -/
theorem modelIntegrand_rescale {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    modelIntegrand B D γ q δ Q κ r W a t (rescale t α u) =
      t ^ (-∑ j, r j * α j) * rescaledIntegrand B D γ q δ Q κ r α W a t u := by
  unfold modelIntegrand rescaledIntegrand
  by_cases h : u ∈ rescaledDomain D γ q Q α t
  · have h' := (mem_modelDomain_rescale_iff ht u).mpr h
    have hu : ∀ j, 0 < u j := fun j ↦ ((Set.mem_univ_pi.mp h.1) j).1
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h', cutVar_rescale ht hu,
      prod_rpow_rescale ht α hu, prod_rpow_rescale ht α hu]
    have e1 : t ^ δ * t ^ (-∑ j, κ j * α j) = t ^ (δ - ∑ j, κ j * α j) := by
      rw [← Real.rpow_add ht, sub_eq_add_neg]
    rw [← e1]
    ring_nf
  · have h' := (mem_modelDomain_rescale_iff ht u).not.mpr h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h', mul_zero]

theorem measurable_cutVar (t : ℝ) : Measurable (cutVar D γ q Q t) :=
  measurable_const.mul (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)

theorem measurableSet_modelDomain (t : ℝ) : MeasurableSet (modelDomain D γ q Q t) :=
  (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo).inter
    (measurableSet_lt (measurable_cutVar t) measurable_const)

theorem measurable_modelIntegrand (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) (t : ℝ) :
    Measurable (modelIntegrand B D γ q δ Q κ r W a t) := by
  have hcut := measurable_cutVar (D := D) (γ := γ) (q := q) (Q := Q) t
  have hWc : Measurable fun x ↦ W x (cutVar D γ q Q t x) :=
    hW.comp (measurable_id.prodMk hcut)
  have hac : Measurable fun x ↦ a x (cutVar D γ q Q t x) :=
    ha.comp (measurable_id.prodMk hcut)
  have hr : Measurable fun x : ι → ℝ ↦ ∏ j, x j ^ r j :=
    Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
  have hκ : Measurable fun x : ι → ℝ ↦ ∏ j, x j ^ κ j :=
    Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
  have h1 : Measurable fun x ↦ W x (cutVar D γ q Q t x) * ∏ j, x j ^ r j := hWc.mul hr
  have h2 : Measurable fun x ↦ B * t ^ δ * a x (cutVar D γ q Q t x) :=
    (measurable_const (a := B * t ^ δ)).mul hac
  have h3 : Measurable fun x ↦ B * t ^ δ * a x (cutVar D γ q Q t x) * ∏ j, x j ^ κ j := h2.mul hκ
  have h4 : Measurable fun x ↦ exp (-(B * t ^ δ * a x (cutVar D γ q Q t x) * ∏ j, x j ^ κ j)) :=
    Real.measurable_exp.comp h3.neg
  exact Measurable.indicator (h1.mul h4) (measurableSet_modelDomain t)

/-- **LP/profile compatibility.** The constrained model kernel is `A t^{-λ}` times the rescaled
integral, with `λ = γp + ∑ (r_j + 1) α_j` the LP value at `α`. -/
theorem modelKernel_eq_rescaled (A p : ℝ) (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) {t : ℝ} (ht : 0 < t) :
    modelKernel A B D γ p q δ Q κ r W a t =
      A * t ^ (-lpExponent γ p (fun j ↦ r j + 1) α) *
        ∫ u, rescaledIntegrand B D γ q δ Q κ r α W a t u := by
  unfold modelKernel
  rw [integral_comp_rescale ht α _ (measurable_modelIntegrand hW ha t).aestronglyMeasurable]
  simp only [modelIntegrand_rescale ht]
  rw [integral_const_mul, lpExponent_succ, ← Real.rpow_sum_of_pos ht]
  have e : t ^ (-(γ * p)) * (t ^ (∑ j, -α j) * t ^ (-∑ j, r j * α j)) =
      t ^ (-(γ * p + ∑ j, r j * α j + ∑ j, α j)) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, Finset.sum_neg_distrib]
    congr 1
    ring
  rw [← e]
  ring

/-! ### What feasibility says about the remaining `t`-powers -/

theorem rpow_phase_le_one {t : ℝ} (ht : 1 ≤ t) (h : δ ≤ ∑ j, κ j * α j) :
    t ^ (δ - ∑ j, κ j * α j) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)

theorem rpow_truth_le_one {t : ℝ} (ht : 1 ≤ t) (hq : 0 < q) (h : ∑ j, Q j * α j ≤ γ) :
    t ^ (-((γ - ∑ j, Q j * α j) / q)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos ht (neg_nonpos.mpr (div_nonneg (by linarith) hq.le))

theorem tendsto_rpow_phase (h : δ < ∑ j, κ j * α j) :
    Tendsto (fun t : ℝ ↦ t ^ (δ - ∑ j, κ j * α j)) atTop (𝓝 0) := by
  have := tendsto_rpow_neg_atTop (sub_pos.mpr h)
  simpa [neg_sub] using this

theorem tendsto_rpow_truth (hq : 0 < q) (h : ∑ j, Q j * α j < γ) :
    Tendsto (fun t : ℝ ↦ t ^ (-((γ - ∑ j, Q j * α j) / q))) atTop (𝓝 0) :=
  tendsto_rpow_neg_atTop (div_pos (sub_pos.mpr h) hq)

/-- Feasibility of a certified `α` gives both bounds at once. -/
theorem ConstrainedLPCert.rpow_le_one {b : ι → ℝ} {μ τ : ℝ}
    (hc : ConstrainedLPCert Q κ b γ δ α μ τ) (hq : 0 < q) {t : ℝ} (ht : 1 ≤ t) :
    t ^ (δ - ∑ j, κ j * α j) ≤ 1 ∧ t ^ (-((γ - ∑ j, Q j * α j) / q)) ≤ 1 :=
  ⟨rpow_phase_le_one ht hc.feasible.2.2, rpow_truth_le_one ht hq hc.feasible.2.1⟩

end Laplace.Multi
