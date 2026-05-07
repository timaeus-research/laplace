import Laplace.OneD.IntegralRemainder
import Threepoint.CrossSusceptibility

/-!
# Leading-order asymptotic of κ₃(x, x, x) for the anharmonic Gibbs measure

For the 1D anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x^4`
with `λ, γ > 0` and the discriminant condition `α² < 3λγ`, the third
cumulant of the linear observable in all three slots admits the leading
asymptotic
  `t² · κ₃(x, x, x) → -α/λ³`  as  `t → ∞`.

This is the cross-repo bridge between the abstract `kappa3` framework
(`timaeus-research/threepoint`) and the concrete anharmonic asymptotic
machinery (`timaeus-research/laplace`). The harmonic case (no cubic
term) was proven in `Threepoint.Harmonic` by parity, giving κ₃ = 0
identically; here the cubic term breaks parity and κ₃ becomes nonzero
at leading order.

## Strategy

Direct calculation factors through three asymptotics already in
`IntegralRemainder.lean`:
  - `cov_anharmonic_asymptotic`:    `t² · Cov[x², x] → -2α/λ³`
  - `mean_anharmonic_asymptotic`:   `t · ⟨x⟩ → -α/(2λ²)`
  - `cov_self_anharmonic_asymptotic`: `t · Var[x] → 1/λ`

via the algebraic identity (a polynomial identity in the three moments
`⟨x⟩`, `⟨x²⟩`, `⟨x³⟩`)
  `κ₃(x, x, x) = Cov[x², x] - 2⟨x²⟩⟨x⟩ + 2⟨x⟩³`.

The `Tendsto` algebra then gives
  `t² · κ₃ = t² · Cov[x², x] - 2 · (t · ⟨x²⟩) · (t · ⟨x⟩) + 2t² · ⟨x⟩³`
       `→ -2α/λ³ - 2 · (1/λ) · (-α/(2λ²)) + 0 = -α/λ³`.

## Headline

* `kappa3_anharmonic_id_id_id_asymptotic`:
    `Tendsto (fun t => t² · kappa3 (volume) anharmonicPotential x t x x)
       atTop (nhds (-α/λ³))`.

## Tide-step provenance

Tide step 9 (Tide C2/F1, the cross-repo bridge), formalised on
`tide/anharmonic-kappa3` in laplace, branched off `main` (commit
`815b569`). See
`sri/projects/patterning/tide-log/2026-05-06-tide-anharmonic-kappa3.md`.
-/

open MeasureTheory Filter Topology

namespace Laplace

namespace OneD

/-! ## The κ₃ unfolding lemma

`Threepoint.kappa3` is defined at `h = 0` of a `(W, μ, L, A)`-perturbed
Gibbs expectation. Specialising to `μ = volume`, the unperturbed Gibbs
expectation matches `Laplace.gibbsExpectation` exactly, and the
perturbation factor `0 · A w` simplifies away. -/

/-- For any `μ`-measurable potential `L` and any observable `A`, the
unperturbed `Threepoint.gibbsExp ... 0 φ` reduces to the standard
ratio of integrals (i.e., to `Laplace.gibbsExpectation L t φ` when
`μ = volume` on `ℝ`). -/
private lemma threepoint_gibbsExp_volume_zero_eq
    (L A φ : ℝ → ℝ) (t : ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ) L A t 0 φ
      = Laplace.gibbsExpectation L t φ := by
  unfold Threepoint.gibbsExp Laplace.gibbsExpectation Laplace.partitionFunction
  simp only [zero_mul, add_zero]

/-- κ₃ at `(A, φ, B) = (id, id, id)` with `μ = volume` unfolds to a
polynomial in the first three Gibbs moments. The perturbation observable
`A` and the two cumulant slots `φ, B` are *all three* set to the
identity, paralleling the harmonic statement
`Threepoint.kappa3_harmonic_id_id_id_eq_zero`. -/
private lemma kappa3_id_id_id_unfold (L : ℝ → ℝ) (t : ℝ) :
    Threepoint.kappa3 (volume : Measure ℝ) L (fun x : ℝ => x) t
        (fun x : ℝ => x) (fun x : ℝ => x)
      = Laplace.gibbsExpectation L t (fun x : ℝ => x ^ 3)
        - 3 * Laplace.gibbsExpectation L t (fun x : ℝ => x ^ 2)
          * Laplace.gibbsExpectation L t (fun x : ℝ => x)
        + 2 * Laplace.gibbsExpectation L t (fun x : ℝ => x) ^ 3 := by
  -- Unfold `Threepoint.kappa3` to its `Threepoint.gibbsExp ... 0` form
  -- without unfolding `Laplace.gibbsExpectation`. Then convert each
  -- `Threepoint.gibbsExp ... 0 φ` to `Laplace.gibbsExpectation L t φ` via
  -- our bridging lemma, applied under all integrand lambdas.
  unfold Threepoint.kappa3
  simp only [threepoint_gibbsExp_volume_zero_eq]
  -- Reduce integrand lambdas like `(fun x => x) w` to `w`, then collapse
  -- `w * w * w → w^3` and `w * w → w^2` inside the `gibbsExpectation`
  -- arguments using function extensionality.
  have h_cube : (fun w : ℝ => (fun x : ℝ => x) w * (fun x : ℝ => x) w
        * (fun x : ℝ => x) w) = (fun w : ℝ => w ^ 3) := by
    funext w; ring
  have h_sq : (fun w : ℝ => (fun x : ℝ => x) w * (fun x : ℝ => x) w)
      = (fun w : ℝ => w ^ 2) := by
    funext w; ring
  rw [h_cube, h_sq]
  ring

/-! ## The algebraic identity

`κ₃(x, x, x) = Cov[x², x] - 2⟨x²⟩⟨x⟩ + 2⟨x⟩³`. Pure ring identity in
the moments, after expanding `gibbsCov`. -/

/-- Polynomial identity rewriting the three-moment expansion of
`κ₃(x, x, x)` in terms of the covariance `Cov[x², x]`. -/
private lemma kappa3_id_id_id_eq_cov_form (L : ℝ → ℝ) (t : ℝ) :
    Laplace.gibbsExpectation L t (fun x : ℝ => x ^ 3)
        - 3 * Laplace.gibbsExpectation L t (fun x : ℝ => x ^ 2)
          * Laplace.gibbsExpectation L t (fun x : ℝ => x)
        + 2 * Laplace.gibbsExpectation L t (fun x : ℝ => x) ^ 3
      = Laplace.gibbsCov L t (fun x : ℝ => x ^ 2) (fun x : ℝ => x)
        - 2 * Laplace.gibbsExpectation L t (fun x : ℝ => x ^ 2)
          * Laplace.gibbsExpectation L t (fun x : ℝ => x)
        + 2 * Laplace.gibbsExpectation L t (fun x : ℝ => x) ^ 3 := by
  unfold Laplace.gibbsCov
  have h_x2_x : (fun x : ℝ => x ^ 2 * x) = (fun x : ℝ => x ^ 3) := by
    funext x; ring
  rw [h_x2_x]
  ring

/-! ## Second-moment asymptotic helper

`t · ⟨x²⟩ → 1/λ` for the anharmonic Gibbs. Derived from
`cov_self_anharmonic_asymptotic` (`t · Var[x] → 1/λ`) plus
`mean_anharmonic_asymptotic` (`t · ⟨x⟩ → -α/(2λ²)`) via
`⟨x²⟩ = Var[x] + ⟨x⟩²` and the observation that `t · ⟨x⟩² → 0`
(because `t · ⟨x⟩` is bounded and `⟨x⟩ → 0` follows). -/

/-- `t · ⟨x²⟩_t → 1/λ` for the anharmonic Gibbs. -/
theorem secondMoment_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ => t * Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x ^ 2)) Filter.atTop
      (nhds (1 / lam)) := by
  have hVar := cov_self_anharmonic_asymptotic hlam hgamma hdisc
  have hMean := mean_anharmonic_asymptotic hlam hgamma hdisc
  -- Strategy: t·⟨x²⟩ = t·Var[x] + t·⟨x⟩².
  -- t·Var[x] → 1/λ (given). t·⟨x⟩² → 0 (since t·⟨x⟩ → C and ⟨x⟩ → 0).
  -- ⟨x⟩ = (1/t) · (t · ⟨x⟩) → 0 · (-α/(2λ²)) = 0 by Tendsto.mul
  -- (using 1/t → 0 as t → ∞).
  have h_inv_t : Filter.Tendsto (fun t : ℝ => 1 / t) Filter.atTop (nhds 0) := by
    simp only [one_div]; exact tendsto_inv_atTop_zero
  -- Build ⟨x⟩ → 0 as (1/t) * (t·⟨x⟩) using Tendsto.mul:
  have hMeanZero :
      Filter.Tendsto
        (fun t : ℝ => Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x))
        Filter.atTop (nhds 0) := by
    have h_prod : Filter.Tendsto
        (fun t : ℝ => (1 / t) * (t * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x)))
        Filter.atTop (nhds (0 * (-alpha / (2 * lam ^ 2)))) :=
      h_inv_t.mul hMean
    have h_lim_zero : (0 : ℝ) * (-alpha / (2 * lam ^ 2)) = 0 := by ring
    rw [h_lim_zero] at h_prod
    apply h_prod.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
  -- Now t·⟨x⟩² = (t·⟨x⟩) · ⟨x⟩ → (-α/(2λ²)) · 0 = 0.
  have h_t_mean_sq :
      Filter.Tendsto
        (fun t : ℝ => t * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x) ^ 2)
        Filter.atTop (nhds 0) := by
    have h_prod : Filter.Tendsto
        (fun t : ℝ => (t * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x))
          * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x))
        Filter.atTop (nhds ((-alpha / (2 * lam ^ 2)) * 0)) :=
      hMean.mul hMeanZero
    have h_lim_zero : (-alpha / (2 * lam ^ 2)) * (0 : ℝ) = 0 := by ring
    rw [h_lim_zero] at h_prod
    apply h_prod.congr'
    filter_upwards with t
    ring
  -- t·⟨x²⟩ = t·Var + t·⟨x⟩² → 1/λ + 0 = 1/λ.
  have h_sum :
      Filter.Tendsto
        (fun t : ℝ => t * Laplace.gibbsCov
            (anharmonicPotential lam alpha gamma) t
            (fun x : ℝ => x) (fun x : ℝ => x)
          + t * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x) ^ 2)
        Filter.atTop (nhds (1 / lam + 0)) :=
    hVar.add h_t_mean_sq
  have h_lim_eq : (1 / lam : ℝ) + 0 = 1 / lam := by ring
  rw [h_lim_eq] at h_sum
  apply h_sum.congr'
  filter_upwards with t
  -- t · ⟨x²⟩ = t · (gibbsCov L t x x + ⟨x⟩²) since gibbsCov L t x x = ⟨x²⟩ - ⟨x⟩².
  unfold Laplace.gibbsCov
  have h_x_x : (fun x : ℝ => x * x) = (fun x : ℝ => x ^ 2) := by
    funext x; ring
  rw [h_x_x]
  ring

/-! ## Headline -/

/-- **Leading-order asymptotic of κ₃(x, x, x) for the anharmonic Gibbs.**

For the 1D anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x^4`
with `λ, γ > 0` and the discriminant condition `α² < 3λγ`, and the linear
observable `(fun x => x)` in all three slots of `Threepoint.kappa3`,
  `t² · κ₃(x, x, x) → -α/λ³` as `t → ∞`.

The proof factors through the algebraic identity
  `κ₃(x, x, x) = Cov[x², x] - 2⟨x²⟩⟨x⟩ + 2⟨x⟩³`
combined with three asymptotics already in `IntegralRemainder.lean`:
  - `cov_anharmonic_asymptotic`:      `t² · Cov[x², x] → -2α/λ³`
  - `secondMoment_anharmonic_asymptotic`: `t · ⟨x²⟩ → 1/λ`
  - `mean_anharmonic_asymptotic`:     `t · ⟨x⟩ → -α/(2λ²)`

The `2⟨x⟩³` term is `O(1/t³)`, so `t² · 2⟨x⟩³ → 0`. Combining:
  `t² · κ₃ → -2α/λ³ - 2 · (1/λ) · (-α/(2λ²)) + 0 = -α/λ³`. -/
theorem kappa3_anharmonic_id_id_id_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto
      (fun t : ℝ => t ^ 2 * Threepoint.kappa3 (volume : Measure ℝ)
          (anharmonicPotential lam alpha gamma)
          (fun x : ℝ => x) t (fun x : ℝ => x) (fun x : ℝ => x))
      Filter.atTop
      (nhds (-alpha / lam ^ 3)) := by
  have hCov := cov_anharmonic_asymptotic hlam hgamma hdisc
  have hM2 := secondMoment_anharmonic_asymptotic hlam hgamma hdisc
  have hM1 := mean_anharmonic_asymptotic hlam hgamma hdisc
  -- t² · κ₃(x,x,x) = t² · Cov[x²,x] - 2 · (t·⟨x²⟩) · (t·⟨x⟩) + 2 · t² · ⟨x⟩³.
  -- The last term is t² · ⟨x⟩³ = (t·⟨x⟩)² · ⟨x⟩ / 1 ... actually
  --   t² · ⟨x⟩³ = (t·⟨x⟩) · (t·⟨x⟩) · ⟨x⟩ → C·C·0 = 0
  -- where ⟨x⟩ → 0 (proven inside secondMoment helper). We re-derive it
  -- here for clarity.
  have h_inv_t : Filter.Tendsto (fun t : ℝ => 1 / t) Filter.atTop (nhds 0) := by
    simp only [one_div]; exact tendsto_inv_atTop_zero
  have hMeanZero :
      Filter.Tendsto
        (fun t : ℝ => Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x))
        Filter.atTop (nhds 0) := by
    have h_prod : Filter.Tendsto
        (fun t : ℝ => (1 / t) * (t * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x)))
        Filter.atTop (nhds (0 * (-alpha / (2 * lam ^ 2)))) :=
      h_inv_t.mul hM1
    have h_lim_zero : (0 : ℝ) * (-alpha / (2 * lam ^ 2)) = 0 := by ring
    rw [h_lim_zero] at h_prod
    apply h_prod.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
  -- Build the three components of the limit:
  -- (1) t² · Cov[x²,x] → -2α/λ³.
  -- (2) -2 · (t·⟨x²⟩) · (t·⟨x⟩) → -2 · (1/λ) · (-α/(2λ²)) = α/λ³.
  -- (3) 2 · t² · ⟨x⟩³ → 0.
  have hPart2 :
      Filter.Tendsto
        (fun t : ℝ => -2 *
          ((t * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x ^ 2))
          * (t * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x))))
        Filter.atTop (nhds (-2 * ((1 / lam) * (-alpha / (2 * lam ^ 2))))) :=
    (tendsto_const_nhds.mul (hM2.mul hM1))
  have hPart3 :
      Filter.Tendsto
        (fun t : ℝ => 2 * (t ^ 2 * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x) ^ 3))
        Filter.atTop (nhds 0) := by
    -- 2·t²·⟨x⟩³ = 2 · (t·⟨x⟩) · (t·⟨x⟩) · ⟨x⟩ → 2·C·C·0 = 0.
    have h_prod : Filter.Tendsto
        (fun t : ℝ => 2 * ((t * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x))
          * (t * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x))
          * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x)))
        Filter.atTop
        (nhds (2 * ((-alpha / (2 * lam ^ 2)) * (-alpha / (2 * lam ^ 2)) * 0))) :=
      tendsto_const_nhds.mul ((hM1.mul hM1).mul hMeanZero)
    have h_lim_zero :
        2 * ((-alpha / (2 * lam ^ 2)) * (-alpha / (2 * lam ^ 2)) * 0) = 0 := by ring
    rw [h_lim_zero] at h_prod
    apply h_prod.congr'
    filter_upwards with t
    ring
  -- Combine the three parts.
  have hSum :
      Filter.Tendsto
        (fun t : ℝ =>
          t ^ 2 * Laplace.gibbsCov
              (anharmonicPotential lam alpha gamma) t
              (fun x : ℝ => x ^ 2) (fun x : ℝ => x)
          + (-2 *
              ((t * Laplace.gibbsExpectation
                (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x ^ 2))
              * (t * Laplace.gibbsExpectation
                (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x))))
          + 2 * (t ^ 2 * Laplace.gibbsExpectation
              (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x) ^ 3))
        Filter.atTop
        (nhds (-2 * alpha / lam ^ 3
          + (-2 * ((1 / lam) * (-alpha / (2 * lam ^ 2))))
          + 0)) :=
    (hCov.add hPart2).add hPart3
  -- The target limit -α/λ³ matches the combined value by ring algebra.
  have h_lim_eq : -2 * alpha / lam ^ 3 + (-2 * ((1 / lam) * (-alpha / (2 * lam ^ 2))))
      + 0 = -alpha / lam ^ 3 := by
    field_simp
    ring
  rw [← h_lim_eq]
  apply hSum.congr'
  filter_upwards with t
  -- LHS: t² · κ₃; RHS: t² · Cov[x²,x] + (-2)·(t·⟨x²⟩)·(t·⟨x⟩) + 2·t²·⟨x⟩³.
  rw [kappa3_id_id_id_unfold (anharmonicPotential lam alpha gamma) t,
    kappa3_id_id_id_eq_cov_form]
  ring

/-! ## Third-moment asymptotic (corollary of Tide 9 +
`secondMoment_anharmonic_asymptotic`)

Packaging the third moment `⟨x³⟩_t` of the anharmonic Gibbs measure
as a user-facing asymptotic, deferred from Tide 9. Identity:
`⟨x³⟩ = Cov[x², x] + ⟨x²⟩·⟨x⟩` (from `gibbsCov` definition). Combined
with the existing asymptotics, the third moment falls out:
`t²·⟨x³⟩ = t²·Cov[x²,x] + (t·⟨x²⟩)·(t·⟨x⟩)
       → -2α/λ³ + (1/λ)·(-α/(2λ²)) = -5α/(2λ³)`. -/

/-- **Third-moment asymptotic of the anharmonic Gibbs measure.**

For `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` with `0 < λ, γ` and
discriminant condition `α² < 3λγ`,
`t² · ⟨x³⟩_t → -5α/(2λ³)` as `t → ∞`.

Strict-improvement strict-corollary of Tide 9: the third moment
expansion was internal to the proof of `cov_anharmonic_asymptotic`
but is here packaged as a user-facing theorem. -/
theorem thirdMoment_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto
      (fun t : ℝ => t ^ 2 * Laplace.gibbsExpectation
          (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x ^ 3))
      Filter.atTop
      (nhds (-(5 * alpha) / (2 * lam ^ 3))) := by
  have hCov := cov_anharmonic_asymptotic hlam hgamma hdisc
  have hM2 := secondMoment_anharmonic_asymptotic hlam hgamma hdisc
  have hM1 := mean_anharmonic_asymptotic hlam hgamma hdisc
  -- t² · ⟨x³⟩ = t² · Cov[x², x] + (t · ⟨x²⟩) · (t · ⟨x⟩).
  -- Cov[x², x] = ⟨x²·x⟩ - ⟨x²⟩·⟨x⟩ = ⟨x³⟩ - ⟨x²⟩·⟨x⟩, so
  -- ⟨x³⟩ = Cov[x², x] + ⟨x²⟩·⟨x⟩.
  have h_sum :
      Filter.Tendsto
        (fun t : ℝ =>
          t ^ 2 * Laplace.gibbsCov
              (anharmonicPotential lam alpha gamma) t
              (fun x : ℝ => x ^ 2) (fun x : ℝ => x)
          + (t * Laplace.gibbsExpectation
              (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x ^ 2))
            * (t * Laplace.gibbsExpectation
              (anharmonicPotential lam alpha gamma) t (fun x : ℝ => x)))
        Filter.atTop
        (nhds (-2 * alpha / lam ^ 3 + (1 / lam) * (-alpha / (2 * lam ^ 2)))) :=
    hCov.add (hM2.mul hM1)
  -- The limit value simplifies: -2α/λ³ + (1/λ)·(-α/(2λ²)) = -5α/(2λ³).
  have h_lim_eq : -2 * alpha / lam ^ 3 + (1 / lam) * (-alpha / (2 * lam ^ 2))
      = -(5 * alpha) / (2 * lam ^ 3) := by
    field_simp
    ring
  rw [h_lim_eq] at h_sum
  -- Bridge the function: t² · ⟨x³⟩ matches t² · Cov[x², x] + (t·⟨x²⟩)·(t·⟨x⟩).
  apply h_sum.congr'
  filter_upwards with t
  -- Cov[x², x] = ⟨x²·x⟩ - ⟨x²⟩·⟨x⟩ = ⟨x³⟩ - ⟨x²⟩·⟨x⟩
  unfold Laplace.gibbsCov
  have h_x2_x : (fun x : ℝ => x ^ 2 * x) = (fun x : ℝ => x ^ 3) := by
    funext x; ring
  rw [h_x2_x]
  ring

/-! ## Affine multilinearity (G2)

Tide 9's `kappa3_anharmonic_id_id_id_asymptotic` lifts to affine
observables `(b·x, a·x, c·x)` by trilinearity of `κ₃`: the scalars
`a, b, c` pull through cleanly, giving an extra factor `a·b·c` on the
asymptotic value.

Two theorems:

* `kappa3_affine_id_id_id_eq` — the static factorisation. No
  hypotheses on `L` beyond what `Threepoint.kappa3`'s definition
  consumes (i.e. none); built from `gibbsExpectation_smul` and
  `kappa3_id_id_id_unfold`. Works for any potential, not just the
  anharmonic one.

* `kappa3_anharmonic_affine_asymptotic` — the asymptotic corollary
  for the anharmonic potential. Direct `Tendsto.const_mul` on top of
  Tide 9 plus the static factorisation. -/

/-- **Affine multilinearity of κ₃ at `id`-multiples** (potential-agnostic).

For any potential `L : ℝ → ℝ` and scalars `a, b, c : ℝ`, the third
cumulant of `(b·x, a·x, c·x)` factors as the trilinear product of the
scalars times the third cumulant of `(x, x, x)`.

The proof unfolds both sides to the seven-Gibbs-expectation form via
`kappa3_id_id_id_unfold`'s sibling expansion, peels each scalar via
`gibbsExpectation_smul`, and closes by `ring`. -/
theorem kappa3_affine_id_id_id_eq (L : ℝ → ℝ) (t : ℝ) (a b c : ℝ) :
    Threepoint.kappa3 (volume : Measure ℝ) L
        (fun x : ℝ => b * x) t (fun x : ℝ => a * x) (fun x : ℝ => c * x)
      = (a * b * c) *
          Threepoint.kappa3 (volume : Measure ℝ) L
            (fun x : ℝ => x) t (fun x : ℝ => x) (fun x : ℝ => x) := by
  -- Unfold `kappa3` on both sides; route every `Threepoint.gibbsExp ... 0`
  -- through `threepoint_gibbsExp_volume_zero_eq` to `Laplace.gibbsExpectation`.
  unfold Threepoint.kappa3
  simp only [threepoint_gibbsExp_volume_zero_eq]
  -- Collapse the seven LHS integrand lambdas to the canonical scaled forms
  -- `(a*b*c) * x^3`, `(a*b) * x^2`, `(a*c) * x^2`, `(b*c) * x^2`,
  -- `a*x`, `b*x`, `c*x`, then peel scalars via `gibbsExpectation_smul`.
  have h_abc : (fun w : ℝ => (fun x : ℝ => a * x) w * (fun x : ℝ => b * x) w
        * (fun x : ℝ => c * x) w) = (fun w : ℝ => (a * b * c) * w ^ 3) := by
    funext w; ring
  have h_ab : (fun w : ℝ => (fun x : ℝ => a * x) w * (fun x : ℝ => b * x) w)
      = (fun w : ℝ => (a * b) * w ^ 2) := by
    funext w; ring
  have h_ac : (fun w : ℝ => (fun x : ℝ => a * x) w * (fun x : ℝ => c * x) w)
      = (fun w : ℝ => (a * c) * w ^ 2) := by
    funext w; ring
  have h_bc : (fun w : ℝ => (fun x : ℝ => b * x) w * (fun x : ℝ => c * x) w)
      = (fun w : ℝ => (b * c) * w ^ 2) := by
    funext w; ring
  -- Same simplifications for the RHS at `(id, id, id)`.
  have h_x3 : (fun w : ℝ => (fun x : ℝ => x) w * (fun x : ℝ => x) w
        * (fun x : ℝ => x) w) = (fun w : ℝ => w ^ 3) := by
    funext w; ring
  have h_x2 : (fun w : ℝ => (fun x : ℝ => x) w * (fun x : ℝ => x) w)
      = (fun w : ℝ => w ^ 2) := by
    funext w; ring
  rw [h_abc, h_ab, h_ac, h_bc, h_x3, h_x2]
  -- Peel scalars from each scaled `gibbsExpectation` via `gibbsExpectation_smul`.
  rw [Laplace.gibbsExpectation_smul L t (a * b * c) (fun w : ℝ => w ^ 3),
      Laplace.gibbsExpectation_smul L t (a * b)     (fun w : ℝ => w ^ 2),
      Laplace.gibbsExpectation_smul L t (a * c)     (fun w : ℝ => w ^ 2),
      Laplace.gibbsExpectation_smul L t (b * c)     (fun w : ℝ => w ^ 2),
      Laplace.gibbsExpectation_smul L t a           (fun w : ℝ => w),
      Laplace.gibbsExpectation_smul L t b           (fun w : ℝ => w),
      Laplace.gibbsExpectation_smul L t c           (fun w : ℝ => w)]
  ring

/-- **Affine third-cumulant asymptotic for the anharmonic Gibbs.**

For `L = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` with `0 < λ`, `0 < γ`,
`α² < 3λγ`, and any scalars `a, b, c : ℝ`,
`t² · κ₃(volume, L, b·x, t, a·x, c·x) → -(a·b·c)·α/λ³` as `t → ∞`.

Strict-improvement of Tide 9: that tide proved the case `(a, b, c) = (1, 1, 1)`;
this multiplies by trilinearity of `κ₃` to handle arbitrary `id`-multiples. -/
theorem kappa3_anharmonic_affine_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    (a b c : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => t ^ 2 * Threepoint.kappa3 (volume : Measure ℝ)
          (anharmonicPotential lam alpha gamma)
          (fun x : ℝ => b * x) t (fun x : ℝ => a * x) (fun x : ℝ => c * x))
      Filter.atTop
      (nhds (-(a * b * c) * alpha / lam ^ 3)) := by
  have hBase := kappa3_anharmonic_id_id_id_asymptotic hlam hgamma hdisc
  -- Replace the limit constant by the trilinearly-scaled form: abc · (-α/λ³).
  have h_lim_eq : -(a * b * c) * alpha / lam ^ 3 = (a * b * c) * (-alpha / lam ^ 3) := by
    ring
  rw [h_lim_eq]
  -- t² · κ₃(b·x, a·x, c·x) = abc · (t² · κ₃(x, x, x)), so the limit is abc · (-α/λ³).
  have h_const := hBase.const_mul (a * b * c)
  apply h_const.congr'
  filter_upwards with t
  rw [kappa3_affine_id_id_id_eq (anharmonicPotential lam alpha gamma) t a b c]
  ring

end OneD

end Laplace
