/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.CutoffMonomialFamily

/-!
# The fixed cutoff–monomial family for a non-isolated zero set: common cylinders

The first non-isolated instance of the fixed-family sufficiency (germbij, singular case):
both losses are *cylindrical* over a splitting `ι = ι₁ ⊕ ι₂` of the coordinates,
`L_j w = K_j (w ∘ inl)`, so the common zero set is `{p₁} × ℝ^{ι₂}` near `p` — positive
dimensional. With a product cutoff `χ w = χ₁ (w ∘ inl) · χ₂ (w ∘ inr)`, Fubini along the
measure-preserving splitting `(ι → ℝ) ≃ (ι₁ → ℝ) × (ι₂ → ℝ)` factors every monomial datum
with tangential degree zero into `(∫ χ₂)` times the transverse datum, so the transverse
losses `K₁, K₂` satisfy the isolated-zero hypotheses of the Q1 theorem
(`normalized_families_force_germ_eq_at_of_cutoff_monomials`) in the transverse variables,
and `K₁ = K₂` near `p₁` lifts to `L₁ = L₂` near `p`.

No tangential polynomial approximation is needed: the tangential variables integrate out.
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The transverse coordinates of a point of the product space. -/
abbrev transverse (w : ι₁ ⊕ ι₂ → ℝ) : ι₁ → ℝ := fun i ↦ w (Sum.inl i)

/-- The tangential coordinates. -/
abbrev tangential (w : ι₁ ⊕ ι₂ → ℝ) : ι₂ → ℝ := fun i ↦ w (Sum.inr i)

/-- **Fubini for the coordinate splitting**: a product integrand factors. -/
theorem integral_transverse_mul_tangential (f : (ι₁ → ℝ) → ℝ) (g : (ι₂ → ℝ) → ℝ) :
    ∫ w : ι₁ ⊕ ι₂ → ℝ, f (transverse w) * g (tangential w) =
      (∫ x : ι₁ → ℝ, f x) * ∫ y : ι₂ → ℝ, g y := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ ↦ ℝ)
  have h := hmp.integral_comp' (fun p : (ι₁ → ℝ) × (ι₂ → ℝ) ↦ f p.1 * g p.2)
  calc ∫ w : ι₁ ⊕ ι₂ → ℝ, f (transverse w) * g (tangential w)
      = ∫ w : ι₁ ⊕ ι₂ → ℝ, f ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ) w).1 *
          g ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ) w).2 := rfl
    _ = ∫ y : (ι₁ → ℝ) × (ι₂ → ℝ), f y.1 * g y.2 := h
    _ = (∫ x : ι₁ → ℝ, f x) * ∫ y : ι₂ → ℝ, g y := integral_prod_mul f g

omit [Fintype ι₁] [Fintype ι₂] in
/-- The coordinate monomial of a word in transverse letters is the transverse coordinate
monomial. -/
theorem coordMonomial_inl (p : ι₁ ⊕ ι₂ → ℝ) {k : ℕ} (m : Fin k → ι₁) (w : ι₁ ⊕ ι₂ → ℝ) :
    coordMonomial p (Sum.inl ∘ m) w = coordMonomial (transverse p) m (transverse w) := by
  unfold coordMonomial
  rfl

/-- Transverse projection contracts the sup norm. -/
theorem norm_transverse_sub_le (w p : ι₁ ⊕ ι₂ → ℝ) :
    ‖transverse w - transverse p‖ ≤ ‖w - p‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact norm_le_pi_norm (w - p) (Sum.inl i)

/-- **Common-cylinder sufficiency of the fixed cutoff–monomial family.** Two losses
cylindrical over the same splitting, `L_j w = K_j (w ∘ inl)`, with `K_j` smooth,
nonnegative, analytic at the common zero `p₁` of the transverse variables, `K₁` coercive at
`p₁` on the transverse cutoff support, and a product cutoff `χ₁ ⊗ χ₂` with `χ₁ = 1` near
`p₁` and `∫ χ₂ > 0` (any tangential weight with positive integral): if the projective
data `∫ χ x^α e^{-tL₂} − C(t) ∫ χ x^α e^{-tL₁}` are beyond all orders for every coordinate
monomial `x^α` (in all coordinates), then `L₁ = L₂` near every `p` over `p₁`. The zero set
`{p₁} × ℝ^{ι₂}` is not isolated. -/
theorem cylinder_normalized_families_force_germ_eq_at
    {K₁ K₂ : (ι₁ → ℝ) → ℝ} {L₁ L₂ : (ι₁ ⊕ ι₂ → ℝ) → ℝ}
    (hL₁ : ∀ w, L₁ w = K₁ (transverse w)) (hL₂ : ∀ w, L₂ w = K₂ (transverse w))
    (h1 : ContDiff ℝ ∞ K₁) (h2 : ContDiff ℝ ∞ K₂)
    (hK1 : ∀ x, 0 ≤ K₁ x) (hK2 : ∀ x, 0 ≤ K₂ x) {p : ι₁ ⊕ ι₂ → ℝ}
    (hA1 : AnalyticAt ℝ K₁ (transverse p)) (hA2 : AnalyticAt ℝ K₂ (transverse p))
    (hp1 : K₁ (transverse p) = 0) (hp2 : K₂ (transverse p) = 0)
    {χ₁ : (ι₁ → ℝ) → ℝ} (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₁s : HasCompactSupport χ₁)
    (hχ₁0 : ∀ x, 0 ≤ χ₁ x) {ρ : ℝ} (hρ : 0 < ρ)
    (hχ₁1 : ∀ x ∈ Metric.ball (transverse p) ρ, χ₁ x = 1)
    {χ₂ : (ι₂ → ℝ) → ℝ} (hχ₂pos : 0 < ∫ y, χ₂ y)
    {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hcoer : ∀ x ∈ tsupport χ₁, c * ‖x - transverse p‖ ^ ν ≤ K₁ x)
    {C : ℝ → ℝ}
    (hfam : ∀ (k : ℕ) (m : Fin k → ι₁ ⊕ ι₂),
      SuperPoly (projDiff L₁ L₂ C fun w ↦ χ₁ (transverse w) * χ₂ (tangential w) *
        coordMonomial p m w)) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  -- the transverse data: tangential degree zero
  have hfam₁ : ∀ (k : ℕ) (m : Fin k → ι₁),
      SuperPoly (projDiff K₁ K₂ C fun x ↦ χ₁ x * coordMonomial (transverse p) m x) := by
    intro k m
    have h := hfam k (Sum.inl ∘ m)
    have hfactor : ∀ (K : (ι₁ → ℝ) → ℝ) (t : ℝ),
        (∫ w : ι₁ ⊕ ι₂ → ℝ, (χ₁ (transverse w) * χ₂ (tangential w) *
          coordMonomial p (Sum.inl ∘ m) w) * Real.exp (-(t * K (transverse w)))) =
        (∫ y : ι₂ → ℝ, χ₂ y) *
          ∫ x : ι₁ → ℝ, (χ₁ x * coordMonomial (transverse p) m x) * Real.exp (-(t * K x)) := by
      intro K t
      rw [mul_comm (∫ y : ι₂ → ℝ, χ₂ y), ← integral_transverse_mul_tangential
        (fun x ↦ (χ₁ x * coordMonomial (transverse p) m x) * Real.exp (-(t * K x))) χ₂]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      rw [coordMonomial_inl]
      ring
    have hC := (h.const_mul (∫ y : ι₂ → ℝ, χ₂ y)⁻¹)
    refine hC.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    unfold projDiff
    simp only [hL₁, hL₂]
    rw [hfactor K₂ t, hfactor K₁ t]
    field_simp
  -- the transverse conclusion
  have hK := normalized_families_force_germ_eq_at_of_cutoff_monomials (C := C) h1 h2 hK1 hK2 hA1
    hA2 hp1 hp2 hχ₁ hχ₁s hχ₁0 hρ hχ₁1 hc hν hcoer hfam₁
  -- lift along the transverse projection
  obtain ⟨δ, hδ, hK'⟩ := Metric.eventually_nhds_iff.mp hK
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun w hw ↦ ?_⟩
  rw [hL₁, hL₂]
  apply hK'
  rw [dist_eq_norm] at hw ⊢
  exact lt_of_le_of_lt (norm_transverse_sub_le w p) hw

end Laplace.Multi
