/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.HalfspaceChernoff
import Laplace.Multi.SegmentDivergence

/-!
# Chernoff exponents are information projections onto response halfspaces

Fix a member `P_a = P_{t,a}` of the family and a response halfspace `{b | u · m_t(b) ≥ r}`. The
Chernoff exponent of the empirical feature mean sampled from `P_a`,
`D = sup_{λ ≥ 0} {λ r − Λ_a(λu)}`, `Λ_a(θ) = A_t(a − θ/t) − A_t(a)` (`famCgf`), is the information
distance from `P_a` to the halfspace: whenever a multiplier `λ ≥ 0` satisfies the
complementary-slackness conditions at `a* = a − (λ/t) u`,

* `KL(P_{a*} ‖ P_a) = λ r − Λ_a(λu)` (`famKL_proj_eq`, the attained value);
* `KL(P_b ‖ P_a) = KL(P_b ‖ P_{a*}) + λ (u · m(b) − r) + KL(P_{a*} ‖ P_a)` for every `b`
  (`famKL_halfspace_decomp`, the halfspace Pythagorean identity);
* `KL(P_{a*} ‖ P_a) ≤ KL(P_b ‖ P_a)` for every feasible `b` (`famKL_proj_le`, primal optimality);
* `μ r − Λ_a(μu) ≤ KL(P_{a*} ‖ P_a)` for every `μ ≥ 0` (`chernoff_rate_le_proj`, dual optimality).

Packaged: the projected divergence is the least feasible divergence (`isLeast_famKL_halfspace`) and
the greatest Chernoff rate (`isGreatest_chernoffRate`), and the halfspace Chernoff bound reads
`P_a^{⊗n}(u · R̄_n ≥ r) ≤ exp(−n KL(P_{a*} ‖ P_a))` (`halfspace_chernoff_eq_projection`).

The response map and the concentration of the sufficient statistic are governed by the same
divergence: the cost of a large deviation of the empirical response into a halfspace is the
information needed to move the data parameter until its response reaches that halfspace.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- `KL(P_{t,a} ‖ P_{t,b})` between members of the family. -/
noncomputable def famKL (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a b : ι → ℝ) :
    ℝ :=
  mixKL μ π (affLoss L₀ R a) (dirLoss R (b - a)) t 0 1

/-- The cumulant generating function of the features under `P_{t,a}`, as a free-energy difference:
`Λ_a(θ) = A_t(a − θ/t) − A_t(a)`. -/
noncomputable def famCgf (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a θ : ι → ℝ) :
    ℝ :=
  affLogZ μ π L₀ R t (a - t⁻¹ • θ) - affLogZ μ π L₀ R t a

omit [MeasurableSpace X] in
theorem sum_sub_smul_mul (a u m : ι → ℝ) (c : ℝ) :
    ∑ i, (a i - (a - c • u) i) * m i = c * ∑ i, u i * m i := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem famCgf_smul (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a u : ι → ℝ)
    (lam : ℝ) :
    famCgf μ π L₀ R t a (lam • u) =
      affLogZ μ π L₀ R t (a - (lam / t) • u) - affLogZ μ π L₀ R t a := by
  unfold famCgf
  rw [smul_smul, inv_mul_eq_div]

omit [MeasurableSpace X] in
theorem sum_sub_smul_sub_smul_mul (a u m : ι → ℝ) (c d : ℝ) :
    ∑ i, ((a - c • u) i - (a - d • u) i) * m i = (d - c) * ∑ i, u i * m i := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit ht in
/-- The Bregman form `KL(P_a ‖ P_b) = A(b) − A(a) + t ⟨b − a, m(a)⟩`. -/
theorem famKL_eq (a b : ι → ℝ) :
    famKL μ π L₀ R t a b = affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a +
      t * ∑ i, (b i - a i) * meanMap μ π L₀ R t a i :=
  mixKL_aff_eq hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR t a b

include ht in
theorem famKL_nonneg (a b : ι → ℝ) : 0 ≤ famKL μ π L₀ R t a b := by
  rw [famKL, mixKL_eq_integral_mul_var hπm hπi hπ hπpos hL₀m hL₀ hR ht b a]
  exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one fun s hs ↦
    mul_nonneg hs.1 (segVar_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR b (a - b) s))

omit [Nonempty X] ht in
/-- `Λ_a` is the cumulant generating function of the features under `P_{t,a}`. -/
theorem famCgf_eq_featCgf (ht : t ≠ 0) (a θ : ι → ℝ) :
    famCgf μ π L₀ R t a θ = featCgf (familyMeasure μ π L₀ R t a) R θ :=
  (featCgf_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR ht a θ).symm

include ht in
/-- **The attained value**: under complementary slackness at `a* = a − (λ/t) u`,
`KL(P_{a*} ‖ P_a) = λ r − Λ_a(λu)`. -/
theorem famKL_proj_eq (a u : ι → ℝ) (r lam : ℝ)
    (hslack : lam * (∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i - r) = 0) :
    famKL μ π L₀ R t (a - (lam / t) • u) a = lam * r - famCgf μ π L₀ R t a (lam • u) := by
  rw [famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR, famCgf_smul, sum_sub_smul_mul, ← mul_assoc,
    mul_div_cancel₀ _ ht.ne']
  linarith

include ht in
/-- **The halfspace Pythagorean identity**: for every `b`,
`KL(P_b ‖ P_a) = KL(P_b ‖ P_{a*}) + λ (u · m(b) − r) + KL(P_{a*} ‖ P_a)`. -/
theorem famKL_halfspace_decomp (a u : ι → ℝ) (r lam : ℝ)
    (hslack : lam * (∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i - r) = 0) (b : ι → ℝ) :
    famKL μ π L₀ R t b a = famKL μ π L₀ R t b (a - (lam / t) • u) +
      lam * (∑ i, u i * meanMap μ π L₀ R t b i - r) +
      famKL μ π L₀ R t (a - (lam / t) • u) a := by
  have h3 := mixKL_three_point hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) b a (a - (lam / t) • u)
  change famKL μ π L₀ R t b a - famKL μ π L₀ R t b (a - (lam / t) • u) -
    famKL μ π L₀ R t (a - (lam / t) • u) a = _ at h3
  rw [sum_sub_smul_mul, ← mul_assoc, mul_div_cancel₀ _ ht.ne'] at h3
  simp only [mul_sub, Finset.sum_sub_distrib] at h3
  linarith

include ht in
/-- **Primal optimality**: the projected divergence is at most the divergence of every member
whose response lies in the halfspace. -/
theorem famKL_proj_le (a u : ι → ℝ) (r lam : ℝ) (hlam : 0 ≤ lam)
    (hslack : lam * (∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i - r) = 0) {b : ι → ℝ}
    (hb : r ≤ ∑ i, u i * meanMap μ π L₀ R t b i) :
    famKL μ π L₀ R t (a - (lam / t) • u) a ≤ famKL μ π L₀ R t b a := by
  rw [famKL_halfspace_decomp hπm hπi hπ hπpos hL₀m hL₀ hR ht a u r lam hslack b]
  have h1 := famKL_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR ht b (a - (lam / t) • u)
  have h2 := mul_nonneg hlam (sub_nonneg.2 hb)
  linarith

include ht in
/-- **Dual optimality**: every Chernoff rate `μ r − Λ_a(μu)`, `μ ≥ 0`, is at most the projected
divergence. -/
theorem chernoff_rate_le_proj (a u : ι → ℝ) (r lam : ℝ)
    (hfeas : r ≤ ∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i)
    (hslack : lam * (∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i - r) = 0) {mu : ℝ}
    (hmu : 0 ≤ mu) :
    mu * r - famCgf μ π L₀ R t a (mu • u) ≤ famKL μ π L₀ R t (a - (lam / t) • u) a := by
  rw [famKL_proj_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht a u r lam hslack, famCgf_smul, famCgf_smul]
  have h0 := famKL_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR ht (a - (lam / t) • u) (a - (mu / t) • u)
  rw [famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR, sum_sub_smul_sub_smul_mul, ← mul_assoc,
    show t * (lam / t - mu / t) = lam - mu by field_simp] at h0
  have h1 := mul_nonneg hmu (sub_nonneg.2 hfeas)
  nlinarith [h0, h1, hslack]

include ht in
/-- The projected divergence is the **least divergence to the halfspace**. -/
theorem isLeast_famKL_halfspace (a u : ι → ℝ) (r lam : ℝ) (hlam : 0 ≤ lam)
    (hfeas : r ≤ ∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i)
    (hslack : lam * (∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i - r) = 0) :
    IsLeast {k | ∃ b, r ≤ ∑ i, u i * meanMap μ π L₀ R t b i ∧ k = famKL μ π L₀ R t b a}
      (famKL μ π L₀ R t (a - (lam / t) • u) a) :=
  ⟨⟨_, hfeas, rfl⟩, by
    rintro k ⟨b, hb, rfl⟩
    exact famKL_proj_le hπm hπi hπ hπpos hL₀m hL₀ hR ht a u r lam hlam hslack hb⟩

include ht in
/-- The projected divergence is the **greatest Chernoff rate**. -/
theorem isGreatest_chernoffRate (a u : ι → ℝ) (r lam : ℝ) (hlam : 0 ≤ lam)
    (hfeas : r ≤ ∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i)
    (hslack : lam * (∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i - r) = 0) :
    IsGreatest {d | ∃ mu, 0 ≤ mu ∧ d = mu * r - famCgf μ π L₀ R t a (mu • u)}
      (famKL μ π L₀ R t (a - (lam / t) • u) a) :=
  ⟨⟨lam, hlam, (famKL_proj_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht a u r lam hslack)⟩, by
    rintro d ⟨mu, hmu, rfl⟩
    exact chernoff_rate_le_proj hπm hπi hπ hπpos hL₀m hL₀ hR ht a u r lam hfeas hslack hmu⟩

include ht in
/-- **The Chernoff bound with the projected divergence as exponent**: sampling from `P_a`,
`P_a^{⊗n}(u · R̄_n ≥ r) ≤ exp(−n KL(P_{a*} ‖ P_a))`. -/
theorem halfspace_chernoff_eq_projection (a u : ι → ℝ) (r lam : ℝ) (hlam : 0 ≤ lam)
    (hslack : lam * (∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i - r) = 0) {n : ℕ}
    (hn : 0 < n) :
    (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t a).real
        {x | r ≤ ∑ i, u i * empMean R n x i} ≤
      Real.exp (-(n * famKL μ π L₀ R t (a - (lam / t) • u) a)) := by
  rw [famKL_proj_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht a u r lam hslack, famCgf]
  exact halfspace_chernoff_family hπm hπi hπ hπpos hL₀m hL₀ hR ht.ne' a u r hn hlam

end

end Laplace.Multi
