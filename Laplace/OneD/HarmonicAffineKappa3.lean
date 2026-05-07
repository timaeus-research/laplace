import Threepoint.Harmonic
import Laplace.Gibbs
import Laplace.OneD.Harmonic
import Laplace.OneD.HarmonicGibbsRegularity
import Laplace.OneD.IntegralRemainder

/-!
# κ₃ vanishes for affine observables under the harmonic Gibbs measure

For the 1D harmonic potential `L(x) = (λ/2) x²` with `λ > 0`, `t > 0`,
the third cumulant of any triple of *affine* observables vanishes:
$$
  \kappa_3\bigl(b_1 x + c_1,\; b_2 x + c_2,\; b_3 x + c_3\bigr) = 0.
$$

This is a multilinearity strict-improvement of Tide 5's
`Threepoint.kappa3_harmonic_id_id_id_eq_zero` (the identity-observable
case): every term in the κ₃ expansion expands into combinations of the
moments `m_k = ⟨x^k⟩` for `k ∈ {1, 2, 3}` against the harmonic Gibbs
weight, and the cumulant structure ensures the constant and `m_2`-only
terms cancel; under harmonic parity `m_1 = m_3 = 0`, leaving zero.

## Headline

* `Laplace.OneD.kappa3_harmonic_affine_eq_zero`:
    For `λ, t > 0` and any affine coefficients `(b_i, c_i)`,
    `kappa3 (volume) ((λ/2)·²) (b₂·+c₂) t (b₁·+c₁) (b₃·+c₃) = 0`.

## Strategy (moment-expansion, per GPT-5.5 Pro consult)

1. *Bridge.* Specialise `Threepoint.gibbsExp ... 0` (which carries the
   perturbation parameter $A$) to `Laplace.gibbsExpectation` (which
   does not), so that I2's algebra applies. Same private bridge used
   in `AnharmonicKappa3.lean`.
2. *κ₃ unfold.* Convert
   `Threepoint.kappa3 vol L A t φ B` to a polynomial in seven
   `Laplace.gibbsExpectation L t (...)` calls via the bridge.
3. *Moment expansion.* Expand each `Laplace.gibbsExpectation L t (...)`
   for `(...)` an affine product, into a polynomial in
   `(b_i, c_i, m_k)` using I2's
   `gibbsExpectation_smul/add/const/zero`. The constant case needs
   `Z ≠ 0` (`harmonic_partition_pos`); the additivity case needs
   integrability of each weighted summand
   (`integrable_pow_mul_exp_neg_mul_sq`).
4. *Substitute.* Use the harmonic moment lemmas
   `gibbsExpectation_harmonic_pow_even` (`m_2 = 1/(λt)`) and
   `gibbsExpectation_harmonic_pow_odd` (`m_1 = m_3 = 0`).
5. *Ring.* Both sides reduce to a scalar polynomial in `(b_i, c_i, λ, t)`.

## Tide-step provenance

Tide step C1, formalised on `tide/kappa3-affine-harmonic` (laplace,
branched off `tide/gibbscov-algebra` at commit `b844d7a` to inherit
I2's `Laplace.gibbsExpectation_smul/add/const` algebra). Tide log:
`projects/primer/tide-log/2026-05-07-tide-kappa3-affine-harmonic.md`.
-/

open MeasureTheory Real

namespace Laplace.OneD

/-! ## Bridge: `Threepoint.gibbsExp ... 0` to `Laplace.gibbsExpectation`

Mirrors the private helper of the same name in
`Laplace/OneD/AnharmonicKappa3.lean`. Restated here to keep the file
self-contained. -/

/-- For any potential `L` and observable `A`, the unperturbed
`Threepoint.gibbsExp ... 0 φ` against the Lebesgue measure on `ℝ`
reduces to `Laplace.gibbsExpectation L t φ`. -/
private lemma threepoint_gibbsExp_volume_zero_eq
    (L A φ : ℝ → ℝ) (t : ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ) L A t 0 φ
      = Laplace.gibbsExpectation L t φ := by
  unfold Threepoint.gibbsExp Laplace.gibbsExpectation Laplace.partitionFunction
  simp only [zero_mul, add_zero]

/-! ## Integrability of polynomials against the harmonic Gibbs weight -/

/-- For the harmonic potential and any natural-number power `n`,
`x ↦ x^n · exp(-(t · L(x)))` is integrable on `ℝ`. Direct from
`integrable_pow_mul_exp_neg_mul_sq`. -/
private lemma harmonic_integrable_pow
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n *
      Real.exp (-(t * harmonicPotential lam x))) := by
  have hint :=
    integrable_pow_mul_exp_neg_mul_sq (c := lam * t / 2) (by positivity) n
  -- `harmonic_integrand_eq` rewrites `exp(-(t·(λ/2)·x²))` to
  -- `exp(-((λt)·x²)/2)`; align via `funext`.
  apply hint.congr
  filter_upwards with x
  unfold harmonicPotential
  congr 1; congr 1; ring

/-! ## Moment closed forms under the harmonic Gibbs

The three values `m_1, m_2, m_3 = ⟨x^k⟩_t` we use in the expansion,
obtained from the existing `gibbsExpectation_harmonic_pow_*` lemmas. -/

/-- `⟨x⟩_t = 0` under the harmonic Gibbs (parity). -/
private lemma gibbsExp_x_harmonic
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Laplace.gibbsExpectation (harmonicPotential lam) t (fun x : ℝ => x) = 0 := by
  have h := gibbsExpectation_harmonic_pow_odd hlam ht 0
  simpa using h

/-- `⟨x²⟩_t = 1 / (λ t)` under the harmonic Gibbs (Gaussian variance). -/
private lemma gibbsExp_x_sq_harmonic
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Laplace.gibbsExpectation (harmonicPotential lam) t (fun x : ℝ => x ^ 2)
      = 1 / (lam * t) := by
  have h := gibbsExpectation_harmonic_pow_even hlam ht 1
  -- h : gibbsExp L t (fun x => x ^ (2*1)) = (2*1-1)‼ / (λt)^1
  simp only [Nat.mul_one, Nat.doubleFactorial, Nat.cast_one, pow_one] at h
  exact h

/-- `⟨x³⟩_t = 0` under the harmonic Gibbs (parity). -/
private lemma gibbsExp_x_cube_harmonic
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Laplace.gibbsExpectation (harmonicPotential lam) t (fun x : ℝ => x ^ 3) = 0 := by
  have h := gibbsExpectation_harmonic_pow_odd hlam ht 1
  -- h : gibbsExp L t (fun x => x ^ (2*1+1)) = 0
  simpa using h

/-! ## Affine moment expansions

For affine observables `(b·x + c)` against the harmonic Gibbs, the
expectations of products factor cleanly. We compute the
single-affine, double-affine-product, and triple-affine-product cases
using I2's `gibbsExpectation_smul/add/const` algebra. -/

/-- Strict positivity of the harmonic partition (so we can divide). -/
private lemma harmonic_Z_ne_zero
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Laplace.partitionFunction (harmonicPotential lam) t ≠ 0 := by
  unfold Laplace.partitionFunction harmonicPotential
  exact ne_of_gt (harmonic_partition_pos hlam ht)

/-- Convenience: `b * x` integrand is integrable against the harmonic weight. -/
private lemma integrable_smul_x
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (b : ℝ) :
    Integrable (fun x : ℝ => b * x *
      Real.exp (-(t * harmonicPotential lam x))) := by
  have h := harmonic_integrable_pow hlam ht 1
  -- h : Integrable (fun x => x^1 * exp(-(t·L))).
  -- Want: Integrable (fun x => b·x · exp(-(t·L))).
  have h' : Integrable (fun x : ℝ => b * (x ^ 1 *
      Real.exp (-(t * harmonicPotential lam x)))) := h.const_mul b
  apply h'.congr
  filter_upwards with x
  ring

/-- Convenience: a constant integrand is integrable against the harmonic weight. -/
private lemma integrable_const_harmonic
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (c : ℝ) :
    Integrable (fun x : ℝ => c *
      Real.exp (-(t * harmonicPotential lam x))) := by
  have h := harmonic_integrable_pow hlam ht 0
  have h' : Integrable (fun x : ℝ => c * (x ^ 0 *
      Real.exp (-(t * harmonicPotential lam x)))) := h.const_mul c
  apply h'.congr
  filter_upwards with x
  simp [pow_zero]

/-- `⟨b·x + c⟩_t = c` under the harmonic Gibbs (since `⟨x⟩_t = 0`). -/
private lemma gibbsExp_affine_harmonic
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (b c : ℝ) :
    Laplace.gibbsExpectation (harmonicPotential lam) t
        (fun x : ℝ => b * x + c) = c := by
  have hZ := harmonic_Z_ne_zero hlam ht
  have h_bx := integrable_smul_x hlam ht b
  have h_c := integrable_const_harmonic hlam ht c
  rw [show (fun x : ℝ => b * x + c)
        = (fun x : ℝ => (fun y => b * y) x + (fun _ : ℝ => c) x) from rfl,
      Laplace.gibbsExpectation_add (harmonicPotential lam) t
        (fun y => b * y) (fun _ => c) h_bx h_c,
      Laplace.gibbsExpectation_smul (harmonicPotential lam) t b (fun x => x),
      Laplace.gibbsExpectation_const (harmonicPotential lam) t c hZ,
      gibbsExp_x_harmonic hlam ht]
  ring

/-- Polynomial gibbsExpectation under the harmonic Gibbs at degree ≤ 3:
`⟨a₃·x³ + a₂·x² + a₁·x + a₀⟩_t = a₂/(λt) + a₀` (since `m₁ = m₃ = 0`).

The path goes through the `gibbsExpectation` linearity from I2 plus the
individual harmonic moment closed forms (`m_k = ⟨x^k⟩_t` from the
existing `gibbsExpectation_harmonic_pow_*` lemmas). -/
private lemma gibbsExp_poly_le3_harmonic
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (a₃ a₂ a₁ a₀ : ℝ) :
    Laplace.gibbsExpectation (harmonicPotential lam) t
        (fun x : ℝ => a₃ * x^3 + a₂ * x^2 + a₁ * x + a₀)
      = a₂ * (1 / (lam * t)) + a₀ := by
  have hZ := harmonic_Z_ne_zero hlam ht
  -- Linearity of `gibbsExpectation` over polynomial integrands.
  -- Step 1: split the 4-term polynomial via `gibbsExpectation_add` 3 times.
  --
  -- We need integrability of every "tail" of the polynomial against the
  -- harmonic weight. Each follows from `harmonic_integrable_pow`
  -- (Gaussian decay × polynomial = integrable).
  have h_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n *
      Real.exp (-(t * harmonicPotential lam x))) := harmonic_integrable_pow hlam ht n
  -- Each `aₖ·xᵏ` weighted summand is integrable.
  have h_a₃ : Integrable (fun x : ℝ => a₃ * x ^ 3 *
      Real.exp (-(t * harmonicPotential lam x))) := by
    have := (h_pow 3).const_mul a₃
    apply this.congr; filter_upwards with x; ring
  have h_a₂ : Integrable (fun x : ℝ => a₂ * x ^ 2 *
      Real.exp (-(t * harmonicPotential lam x))) := by
    have := (h_pow 2).const_mul a₂
    apply this.congr; filter_upwards with x; ring
  have h_a₁ : Integrable (fun x : ℝ => a₁ * x *
      Real.exp (-(t * harmonicPotential lam x))) := integrable_smul_x hlam ht a₁
  have h_a₀ : Integrable (fun x : ℝ => a₀ *
      Real.exp (-(t * harmonicPotential lam x))) := integrable_const_harmonic hlam ht a₀
  -- Tail integrabilities (after grouping `(a₂·x² + a₁·x + a₀)` etc.).
  have h_a₂a₁a₀ : Integrable (fun x : ℝ =>
      (a₂ * x ^ 2 + a₁ * x + a₀) *
      Real.exp (-(t * harmonicPotential lam x))) := by
    have := h_a₂.add (h_a₁.add h_a₀)
    apply this.congr; filter_upwards with x
    simp only [Pi.add_apply]; ring
  have h_a₁a₀ : Integrable (fun x : ℝ => (a₁ * x + a₀) *
      Real.exp (-(t * harmonicPotential lam x))) := by
    have := h_a₁.add h_a₀
    apply this.congr; filter_upwards with x
    simp only [Pi.add_apply]; ring
  -- Step 1a: factor `a₃·x³ + (a₂·x² + a₁·x + a₀)`.
  rw [show (fun x : ℝ => a₃ * x ^ 3 + a₂ * x ^ 2 + a₁ * x + a₀)
        = (fun x : ℝ => (fun y => a₃ * y ^ 3) x +
                        (fun y : ℝ => a₂ * y ^ 2 + a₁ * y + a₀) x) from by
        funext x; ring]
  rw [Laplace.gibbsExpectation_add (harmonicPotential lam) t
        (fun y => a₃ * y ^ 3) (fun y => a₂ * y ^ 2 + a₁ * y + a₀) h_a₃ h_a₂a₁a₀]
  -- Step 1b: factor the tail `(a₂·x² + a₁·x + a₀)` = `a₂·x² + (a₁·x + a₀)`.
  rw [show (fun y : ℝ => a₂ * y ^ 2 + a₁ * y + a₀)
        = (fun y : ℝ => (fun z => a₂ * z ^ 2) y + (fun z : ℝ => a₁ * z + a₀) y) from by
        funext y; ring]
  rw [Laplace.gibbsExpectation_add (harmonicPotential lam) t
        (fun z => a₂ * z ^ 2) (fun z => a₁ * z + a₀) h_a₂ h_a₁a₀]
  -- Step 1c: factor the tail `(a₁·x + a₀)` = `a₁·x + a₀`.
  rw [show (fun z : ℝ => a₁ * z + a₀)
        = (fun z : ℝ => (fun w => a₁ * w) z + (fun _ : ℝ => a₀) z) from rfl]
  rw [Laplace.gibbsExpectation_add (harmonicPotential lam) t
        (fun w => a₁ * w) (fun _ => a₀) h_a₁ h_a₀]
  -- Step 2: pull scalars out of each `aₖ·xᵏ` summand via `_smul`.
  rw [Laplace.gibbsExpectation_smul (harmonicPotential lam) t a₃ (fun x => x ^ 3),
      Laplace.gibbsExpectation_smul (harmonicPotential lam) t a₂ (fun x => x ^ 2),
      Laplace.gibbsExpectation_smul (harmonicPotential lam) t a₁ (fun x => x),
      Laplace.gibbsExpectation_const (harmonicPotential lam) t a₀ hZ]
  -- Step 3: substitute the closed-form moments.
  rw [gibbsExp_x_cube_harmonic hlam ht,
      gibbsExp_x_sq_harmonic hlam ht,
      gibbsExp_x_harmonic hlam ht]
  ring

/-! ## The headline -/

/-- **κ₃ vanishes for affine observables under the harmonic Gibbs measure.**

For the 1D harmonic potential `L(x) = (λ/2) x²` with `λ > 0`, `t > 0`,
on `ℝ` against the Lebesgue measure, the third cumulant of any triple
of affine observables `(b_i x + c_i)_{i = 1, 2, 3}` is zero. This is
the multilinearity strict-improvement of Tide 5's
`kappa3_harmonic_id_id_id_eq_zero`.

The proof goes by moment expansion: each of the seven Gibbs
expectations in the κ₃ formula reduces to a polynomial in
`(b_i, c_i, m_1, m_2, m_3)` by I2's algebra, where `m_k = ⟨x^k⟩`
under the harmonic Gibbs measure. Plugging in the closed forms
`m_1 = m_3 = 0`, `m_2 = 1/(λt)`, the constant and `m_2`-coefficient
terms cancel by the cumulant structure (verified numerically and
algebraically, see the tide log), leaving zero. -/
theorem kappa3_harmonic_affine_eq_zero
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (b₁ c₁ b₂ c₂ b₃ c₃ : ℝ) :
    Threepoint.kappa3 (volume : Measure ℝ)
        (harmonicPotential lam)
        (fun x : ℝ => b₂ * x + c₂)
        t
        (fun x : ℝ => b₁ * x + c₁)
        (fun x : ℝ => b₃ * x + c₃) = 0 := by
  -- Step 1: Unfold `Threepoint.kappa3` and bridge `Threepoint.gibbsExp ... 0`
  --   to `Laplace.gibbsExpectation`.
  unfold Threepoint.kappa3
  simp only [threepoint_gibbsExp_volume_zero_eq]
  -- Step 2: Rewrite each affine-product integrand as a degree-3 polynomial,
  --   then apply `gibbsExp_poly_le3_harmonic`. Single affines use
  --   `gibbsExp_affine_harmonic`.
  -- The triple `(b₁x+c₁)(b₂x+c₂)(b₃x+c₃)`:
  rw [show (fun w : ℝ => (b₁ * w + c₁) * (b₂ * w + c₂) * (b₃ * w + c₃))
        = (fun w : ℝ => (b₁*b₂*b₃) * w^3 +
                        (b₁*b₂*c₃ + b₁*c₂*b₃ + c₁*b₂*b₃) * w^2 +
                        (b₁*c₂*c₃ + c₁*b₂*c₃ + c₁*c₂*b₃) * w +
                        c₁*c₂*c₃) from by funext w; ring]
  rw [gibbsExp_poly_le3_harmonic hlam ht
        (b₁*b₂*b₃) (b₁*b₂*c₃ + b₁*c₂*b₃ + c₁*b₂*b₃)
        (b₁*c₂*c₃ + c₁*b₂*c₃ + c₁*c₂*b₃) (c₁*c₂*c₃)]
  -- The pair `(b₁x+c₁)(b₂x+c₂)`:
  rw [show (fun w : ℝ => (b₁ * w + c₁) * (b₂ * w + c₂))
        = (fun w : ℝ => 0 * w^3 + (b₁*b₂) * w^2 + (b₁*c₂ + c₁*b₂) * w + c₁*c₂) from by
        funext w; ring]
  rw [gibbsExp_poly_le3_harmonic hlam ht 0 (b₁*b₂) (b₁*c₂ + c₁*b₂) (c₁*c₂)]
  -- The pair `(b₁x+c₁)(b₃x+c₃)`:
  rw [show (fun w : ℝ => (b₁ * w + c₁) * (b₃ * w + c₃))
        = (fun w : ℝ => 0 * w^3 + (b₁*b₃) * w^2 + (b₁*c₃ + c₁*b₃) * w + c₁*c₃) from by
        funext w; ring]
  rw [gibbsExp_poly_le3_harmonic hlam ht 0 (b₁*b₃) (b₁*c₃ + c₁*b₃) (c₁*c₃)]
  -- The pair `(b₂x+c₂)(b₃x+c₃)`:
  rw [show (fun w : ℝ => (b₂ * w + c₂) * (b₃ * w + c₃))
        = (fun w : ℝ => 0 * w^3 + (b₂*b₃) * w^2 + (b₂*c₃ + c₂*b₃) * w + c₂*c₃) from by
        funext w; ring]
  rw [gibbsExp_poly_le3_harmonic hlam ht 0 (b₂*b₃) (b₂*c₃ + c₂*b₃) (c₂*c₃)]
  -- The three single affines `(b₁x+c₁)`, `(b₂x+c₂)`, `(b₃x+c₃)`:
  rw [gibbsExp_affine_harmonic hlam ht b₁ c₁,
      gibbsExp_affine_harmonic hlam ht b₂ c₂,
      gibbsExp_affine_harmonic hlam ht b₃ c₃]
  -- Step 3: All seven gibbsExpectations are now closed-form polynomials in
  --   `(b_i, c_i, lam, t)`. The cumulant cancels by `ring`.
  ring

end Laplace.OneD
