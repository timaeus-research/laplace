import Laplace.OneD.AnharmonicKappa3

/-!
# Shifted-affine strengthening of the anharmonic-κ₃ asymptotic

For the 1D anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴`
with `λ, γ > 0` and the discriminant condition `α² < 3λγ`, and three
**shifted** affine observables `αᵢ(x) = aᵢ·x + bᵢ`,

  `t² · κ₃(α₁, α₂, α₃) → a₁·a₂·a₃ · (-α/λ³)` as `t → ∞`.

The constants `bᵢ` drop because the joint third cumulant vanishes on
constant slots. This is a strict-improvement of the linear-affine
`kappa3_anharmonic_affine_asymptotic` (this same tide branch's earlier
landing): there `(b·x, a·x, c·x)` was proven, with the constants in
each slot deferred as a follow-up. The retrospective for the linear
case identified this shifted-affine extension as a follow-up, citing
~50 extra lines for the `gibbsExpectation_const` plumbing — and indeed
the bulk of this file is the cubic-polynomial expansion infrastructure
needed when the integrands carry constant terms.

## Tide-step provenance

Strict-improvement extension of Tide G2
(kappa3-affine-anharmonic), on the same branch
`tide/kappa3-affine-anharmonic`. The base linear case was committed
in `1b3e9bd`; this file adds the shifted-affine extension on top.

See
`sri/projects/primer/tide-log/2026-05-07-tide-kappa3-affine-anharmonic.md`
for the deliberation log. The `gibbsExpectation_const` requirement
(absent from the linear case) drives the `partitionFunction ≠ 0` and
polynomial-times-`exp(-tL)` integrability infrastructure below.
-/

open MeasureTheory Filter Topology

namespace Laplace

namespace OneD

/-! ## Integrability witnesses for `xⁿ · exp(-t · L_anh)` -/

/-- Polynomial-times-`exp(-t·L)` is integrable for the anharmonic
potential, by domination by the Gaussian `|x|ⁿ · exp(-tc·x²)` from
coercivity. -/
private lemma integrable_pow_mul_exp_neg_anharmonic
    (n : ℕ) {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  -- Coercivity gives `c > 0` with `c · x² ≤ L_anh(x)` everywhere.
  obtain ⟨c, hc_pos, hbound⟩ :=
    anharmonic_coercive lam alpha gamma hlam hgamma hdisc
  have htc_pos : 0 < t * c := mul_pos ht hc_pos
  -- Dominator: `|x|ⁿ · exp(-tc·x²)`, integrable.
  have h_dom : Integrable (fun x : ℝ => |x| ^ n *
      Real.exp (-(t * c * x ^ 2))) :=
    integrable_abs_pow_mul_exp_neg_mul_sq htc_pos n
  -- Continuity → AE strong measurability.
  have h_meas : AEStronglyMeasurable
      (fun x : ℝ => x ^ n *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) volume := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (continuous_id.pow n)
    · apply Real.continuous_exp.comp
      apply Continuous.neg
      apply Continuous.mul continuous_const
      -- anharmonicPotential is a polynomial in x.
      unfold anharmonicPotential
      fun_prop
  -- Pointwise: `|xⁿ · exp(-t·L_anh)| ≤ |x|ⁿ · exp(-tc·x²)`.
  refine h_dom.mono h_meas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg x) n)
  apply Real.exp_le_exp.mpr
  -- `-(t·L_anh) ≤ -(t·c·x²)` ↔ `t·c·x² ≤ t·L_anh` (use `hbound`, `ht > 0`).
  have h := hbound x
  have ht_le : t * (c * x ^ 2) ≤ t * anharmonicPotential lam alpha gamma x :=
    mul_le_mul_of_nonneg_left h ht.le
  linarith

/-- The partition function for the anharmonic potential is positive
(hence nonzero) for `t > 0`. Since `exp(-(t · L_anh))` is strictly
positive everywhere and integrable, `integral_exp_pos` closes. -/
private lemma partitionFunction_anharmonic_pos
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    0 < Laplace.partitionFunction (anharmonicPotential lam alpha gamma) t := by
  unfold Laplace.partitionFunction
  have h_int : Integrable
      (fun x : ℝ => Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have h := integrable_pow_mul_exp_neg_anharmonic 0 hlam hgamma hdisc ht
    simpa using h
  exact integral_exp_pos h_int

private lemma partitionFunction_anharmonic_ne_zero
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Laplace.partitionFunction (anharmonicPotential lam alpha gamma) t ≠ 0 :=
  (partitionFunction_anharmonic_pos hlam hgamma hdisc ht).ne'

/-! ## Cubic-polynomial expectation expansion

`⟨c₃·x³ + c₂·x² + c₁·x + c₀⟩ = c₃·⟨x³⟩ + c₂·⟨x²⟩ + c₁·⟨x⟩ + c₀` for the
anharmonic Gibbs measure. The four `Integrable` witnesses come from the
coercivity-domination lemma above. -/

private lemma gibbsExp_anharmonic_cubic_eq
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t)
    (c₀ c₁ c₂ c₃ : ℝ) :
    Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x : ℝ => c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀)
      = c₃ * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x ^ 3)
        + c₂ * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x ^ 2)
        + c₁ * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x)
        + c₀ := by
  have hZ := partitionFunction_anharmonic_ne_zero hlam hgamma hdisc ht
  -- Integrability of `cₖ · xᵏ · exp(-tL)` for k = 0, 1, 2, 3.
  have h0 := (integrable_pow_mul_exp_neg_anharmonic 0 hlam hgamma hdisc ht).const_mul c₀
  have h1 := (integrable_pow_mul_exp_neg_anharmonic 1 hlam hgamma hdisc ht).const_mul c₁
  have h2 := (integrable_pow_mul_exp_neg_anharmonic 2 hlam hgamma hdisc ht).const_mul c₂
  have h3 := (integrable_pow_mul_exp_neg_anharmonic 3 hlam hgamma hdisc ht).const_mul c₃
  -- Massage each into the `(fun x => cₖ * xᵏ) * exp` form for `_add` consumption.
  have h0' : Integrable (fun x : ℝ => c₀ *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    simpa using h0
  have h1' : Integrable (fun x : ℝ => c₁ * x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have : (fun x : ℝ => c₁ * (x ^ 1 *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
        = (fun x : ℝ => c₁ * x *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
      funext x; ring
    rw [← this]; exact h1
  have h2' : Integrable (fun x : ℝ => c₂ * x ^ 2 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have : (fun x : ℝ => c₂ * (x ^ 2 *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
        = (fun x : ℝ => c₂ * x ^ 2 *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
      funext x; ring
    rw [← this]; exact h2
  have h3' : Integrable (fun x : ℝ => c₃ * x ^ 3 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have : (fun x : ℝ => c₃ * (x ^ 3 *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x))))
        = (fun x : ℝ => c₃ * x ^ 3 *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
      funext x; ring
    rw [← this]; exact h3
  -- Build sums step by step (left-associative `(((a + b) + c) + d)` matches the goal).
  have h12 : Integrable (fun x : ℝ => c₁ * x *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x)) +
      c₀ * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := h1'.add h0'
  -- First-stage split: pull off `c₀` (innermost).
  have step0 :
      Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x : ℝ => c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀)
        = Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x : ℝ => c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x)
          + Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun _ : ℝ => c₀) := by
    have h_lhs_split :
        (fun x : ℝ => c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀)
          = (fun x : ℝ => (c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x) + c₀) := by
      funext x; ring
    rw [h_lhs_split]
    refine Laplace.gibbsExpectation_add (anharmonicPotential lam alpha gamma) t
      (fun x : ℝ => c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x) (fun _ : ℝ => c₀) ?_ ?_
    · -- Integrability of `(c₃ x³ + c₂ x² + c₁ x) · exp`.
      have : (fun x : ℝ => (c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x) *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
          = (fun x : ℝ => c₃ * x ^ 3 *
              Real.exp (-(t * anharmonicPotential lam alpha gamma x))
            + c₂ * x ^ 2 *
              Real.exp (-(t * anharmonicPotential lam alpha gamma x))
            + c₁ * x *
              Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
        funext x; ring
      rw [this]
      exact ((h3'.add h2').add h1')
    · exact h0'
  -- Second stage: pull off `c₁ x` from `c₃ x³ + c₂ x² + c₁ x`.
  have step1 :
      Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x : ℝ => c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x)
        = Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x : ℝ => c₃ * x ^ 3 + c₂ * x ^ 2)
          + Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x : ℝ => c₁ * x) := by
    refine Laplace.gibbsExpectation_add (anharmonicPotential lam alpha gamma) t
      (fun x : ℝ => c₃ * x ^ 3 + c₂ * x ^ 2) (fun x : ℝ => c₁ * x) ?_ h1'
    have : (fun x : ℝ => (c₃ * x ^ 3 + c₂ * x ^ 2) *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
        = (fun x : ℝ => c₃ * x ^ 3 *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x))
          + c₂ * x ^ 2 *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
      funext x; ring
    rw [this]
    exact h3'.add h2'
  -- Third stage: pull off `c₂ x²` from `c₃ x³ + c₂ x²`.
  have step2 :
      Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x : ℝ => c₃ * x ^ 3 + c₂ * x ^ 2)
        = Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x : ℝ => c₃ * x ^ 3)
          + Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x : ℝ => c₂ * x ^ 2) := by
    exact Laplace.gibbsExpectation_add (anharmonicPotential lam alpha gamma) t
      (fun x : ℝ => c₃ * x ^ 3) (fun x : ℝ => c₂ * x ^ 2) h3' h2'
  -- Now apply `_smul` to pull constants out, plus `_const` for c₀.
  rw [step0, step1, step2]
  rw [Laplace.gibbsExpectation_smul (anharmonicPotential lam alpha gamma) t c₃
        (fun x : ℝ => x ^ 3),
      Laplace.gibbsExpectation_smul (anharmonicPotential lam alpha gamma) t c₂
        (fun x : ℝ => x ^ 2),
      Laplace.gibbsExpectation_smul (anharmonicPotential lam alpha gamma) t c₁
        (fun x : ℝ => x),
      Laplace.gibbsExpectation_const (anharmonicPotential lam alpha gamma) t c₀ hZ]

/-! ## `Threepoint.gibbsExp` ↔ `Laplace.gibbsExpectation` bridge at `h = 0`

Re-derived locally because Tide 9's
`AnharmonicKappa3.threepoint_gibbsExp_volume_zero_eq` is `private`. -/

private lemma threepoint_gibbsExp_volume_zero_eq'
    (L A φ : ℝ → ℝ) (t : ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ) L A t 0 φ
      = Laplace.gibbsExpectation L t φ := by
  unfold Threepoint.gibbsExp Laplace.gibbsExpectation Laplace.partitionFunction
  simp only [zero_mul, add_zero]

/-- Unfolding of `Threepoint.kappa3` over `volume` in five
`Laplace.gibbsExpectation` terms (independent of the perturbation
direction `A`, since at `h = 0` it doesn't enter the integrand). -/
private lemma kappa3_volume_unfold
    (L A φ B : ℝ → ℝ) (t : ℝ) :
    Threepoint.kappa3 (volume : Measure ℝ) L A t φ B
      = Laplace.gibbsExpectation L t (fun x : ℝ => φ x * A x * B x)
        - Laplace.gibbsExpectation L t (fun x : ℝ => φ x * A x)
          * Laplace.gibbsExpectation L t B
        - Laplace.gibbsExpectation L t (fun x : ℝ => φ x * B x)
          * Laplace.gibbsExpectation L t A
        - Laplace.gibbsExpectation L t (fun x : ℝ => A x * B x)
          * Laplace.gibbsExpectation L t φ
        + 2 * Laplace.gibbsExpectation L t φ
            * Laplace.gibbsExpectation L t A
            * Laplace.gibbsExpectation L t B := by
  unfold Threepoint.kappa3
  rw [threepoint_gibbsExp_volume_zero_eq', threepoint_gibbsExp_volume_zero_eq',
      threepoint_gibbsExp_volume_zero_eq', threepoint_gibbsExp_volume_zero_eq',
      threepoint_gibbsExp_volume_zero_eq', threepoint_gibbsExp_volume_zero_eq',
      threepoint_gibbsExp_volume_zero_eq']

/-! ## The multilinear unfolding lemma -/

/-- The multilinear identity for the anharmonic third joint cumulant.
For three affine observables `(a₁ x + b₁, a₂ x + b₂, a₃ x + b₃)`, the
joint third cumulant rescales by `a₁ a₂ a₃` and the constants `bᵢ`
drop. This is the structural content driving the asymptotic theorem
below. -/
private theorem kappa3_anharmonic_shifted_affine_eq_smul
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
    Threepoint.kappa3 (volume : Measure ℝ)
        (anharmonicPotential lam alpha gamma)
        (fun x : ℝ => a₂ * x + b₂) t
        (fun x : ℝ => a₁ * x + b₁) (fun x : ℝ => a₃ * x + b₃)
      = a₁ * a₂ * a₃ * Threepoint.kappa3 (volume : Measure ℝ)
          (anharmonicPotential lam alpha gamma)
          (fun x : ℝ => x) t (fun x : ℝ => x) (fun x : ℝ => x) := by
  -- Unfold both kappa3 calls into five `Laplace.gibbsExpectation` terms.
  rw [kappa3_volume_unfold, kappa3_volume_unfold]
  -- Massage each integrand into cubic-polynomial form.
  have h_α1α2α3 : (fun x : ℝ => (a₁ * x + b₁) * (a₂ * x + b₂) * (a₃ * x + b₃))
      = (fun x : ℝ => a₁ * a₂ * a₃ * x ^ 3 +
            (a₁ * a₂ * b₃ + a₁ * b₂ * a₃ + b₁ * a₂ * a₃) * x ^ 2 +
            (a₁ * b₂ * b₃ + b₁ * a₂ * b₃ + b₁ * b₂ * a₃) * x +
            b₁ * b₂ * b₃) := by funext x; ring
  have h_α1α2 : (fun x : ℝ => (a₁ * x + b₁) * (a₂ * x + b₂))
      = (fun x : ℝ => 0 * x ^ 3 + a₁ * a₂ * x ^ 2 +
            (a₁ * b₂ + a₂ * b₁) * x + b₁ * b₂) := by funext x; ring
  have h_α1α3 : (fun x : ℝ => (a₁ * x + b₁) * (a₃ * x + b₃))
      = (fun x : ℝ => 0 * x ^ 3 + a₁ * a₃ * x ^ 2 +
            (a₁ * b₃ + a₃ * b₁) * x + b₁ * b₃) := by funext x; ring
  have h_α2α3 : (fun x : ℝ => (a₂ * x + b₂) * (a₃ * x + b₃))
      = (fun x : ℝ => 0 * x ^ 3 + a₂ * a₃ * x ^ 2 +
            (a₂ * b₃ + a₃ * b₂) * x + b₂ * b₃) := by funext x; ring
  have h_α1 : (fun x : ℝ => a₁ * x + b₁)
      = (fun x : ℝ => 0 * x ^ 3 + 0 * x ^ 2 + a₁ * x + b₁) := by funext x; ring
  have h_α2 : (fun x : ℝ => a₂ * x + b₂)
      = (fun x : ℝ => 0 * x ^ 3 + 0 * x ^ 2 + a₂ * x + b₂) := by funext x; ring
  have h_α3 : (fun x : ℝ => a₃ * x + b₃)
      = (fun x : ℝ => 0 * x ^ 3 + 0 * x ^ 2 + a₃ * x + b₃) := by funext x; ring
  have h_id_id_id : (fun x : ℝ => x * x * x)
      = (fun x : ℝ => 1 * x ^ 3 + 0 * x ^ 2 + 0 * x + 0) := by funext x; ring
  have h_id_id : (fun x : ℝ => x * x)
      = (fun x : ℝ => 0 * x ^ 3 + 1 * x ^ 2 + 0 * x + 0) := by funext x; ring
  have h_id : (fun x : ℝ => x)
      = (fun x : ℝ => 0 * x ^ 3 + 0 * x ^ 2 + 1 * x + 0) := by funext x; ring
  rw [h_α1α2α3, h_α1α2, h_α1α3, h_α2α3, h_α1, h_α2, h_α3]
  -- For the RHS unfolding, rewrite (fun x => x * x * x) etc. in cubic form.
  conv_rhs =>
    rw [show (fun x : ℝ => x * x * x) = (fun x : ℝ => 1 * x ^ 3 + 0 * x ^ 2 + 0 * x + 0)
          from by funext x; ring,
        show (fun x : ℝ => x * x) = (fun x : ℝ => 0 * x ^ 3 + 1 * x ^ 2 + 0 * x + 0)
          from by funext x; ring]
  -- Apply the cubic helper to all `gibbsExpectation` calls (eight on LHS, four on RHS).
  rw [gibbsExp_anharmonic_cubic_eq hlam hgamma hdisc ht (b₁ * b₂ * b₃)
        (a₁ * b₂ * b₃ + b₁ * a₂ * b₃ + b₁ * b₂ * a₃)
        (a₁ * a₂ * b₃ + a₁ * b₂ * a₃ + b₁ * a₂ * a₃) (a₁ * a₂ * a₃),
      gibbsExp_anharmonic_cubic_eq hlam hgamma hdisc ht
        (b₁ * b₂) (a₁ * b₂ + a₂ * b₁) (a₁ * a₂) 0,
      gibbsExp_anharmonic_cubic_eq hlam hgamma hdisc ht
        (b₁ * b₃) (a₁ * b₃ + a₃ * b₁) (a₁ * a₃) 0,
      gibbsExp_anharmonic_cubic_eq hlam hgamma hdisc ht
        (b₂ * b₃) (a₂ * b₃ + a₃ * b₂) (a₂ * a₃) 0,
      gibbsExp_anharmonic_cubic_eq hlam hgamma hdisc ht b₁ a₁ 0 0,
      gibbsExp_anharmonic_cubic_eq hlam hgamma hdisc ht b₂ a₂ 0 0,
      gibbsExp_anharmonic_cubic_eq hlam hgamma hdisc ht b₃ a₃ 0 0,
      gibbsExp_anharmonic_cubic_eq hlam hgamma hdisc ht 0 0 0 1,
      gibbsExp_anharmonic_cubic_eq hlam hgamma hdisc ht 0 0 1 0]
  ring

/-! ## Headline -/

/-- **Affine generalisation of the anharmonic-κ₃ asymptotic.**

For the 1D anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴`
with `λ, γ > 0` and the discriminant condition `α² < 3λγ`, and three
affine observables `(a₁ x + b₁, a₂ x + b₂, a₃ x + b₃)`,

  `t² · κ₃(α₁, α₂, α₃) → a₁ · a₂ · a₃ · (-α/λ³)`  as  `t → ∞`.

The constants `bᵢ` drop because the joint third cumulant vanishes on
constant slots; the multipliers `aᵢ` pull through by trilinearity. -/
theorem kappa3_anharmonic_shifted_affine_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => t ^ 2 * Threepoint.kappa3 (volume : Measure ℝ)
          (anharmonicPotential lam alpha gamma)
          (fun x : ℝ => a₂ * x + b₂) t
          (fun x : ℝ => a₁ * x + b₁) (fun x : ℝ => a₃ * x + b₃))
      Filter.atTop
      (nhds (a₁ * a₂ * a₃ * (-alpha / lam ^ 3))) := by
  -- Tide 9: `t² · κ₃[id, id, id] → -α/λ³`.
  have h_id := kappa3_anharmonic_id_id_id_asymptotic hlam hgamma hdisc
  -- Multiply by `a₁ * a₂ * a₃`.
  have h_scaled : Filter.Tendsto
      (fun t : ℝ => a₁ * a₂ * a₃ * (t ^ 2 *
          Threepoint.kappa3 (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma)
            (fun x : ℝ => x) t (fun x : ℝ => x) (fun x : ℝ => x)))
      Filter.atTop
      (nhds (a₁ * a₂ * a₃ * (-alpha / lam ^ 3))) :=
    h_id.const_mul (a₁ * a₂ * a₃)
  -- Use the multilinear identity (eventually for `t > 0`) to rewrite the limit.
  apply h_scaled.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  -- For `t > 0`, the affine kappa3 equals `a₁ a₂ a₃ · κ₃[id, id, id]`.
  rw [kappa3_anharmonic_shifted_affine_eq_smul hlam hgamma hdisc ht a₁ a₂ a₃ b₁ b₂ b₃]
  ring

end OneD

end Laplace
