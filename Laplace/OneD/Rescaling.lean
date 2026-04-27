import Laplace.OneD.Anharmonic

/-!
# Rescaling identity for the anharmonic Laplace expansion

After the substitution `x = u / √(λ t)` (which makes the harmonic part of
`tL(x)` exactly `u²/2`), the anharmonic potential has the form

  `t · L(u/√(λ t)) = u²/2 + s_t(u)`

where the perturbation is

  `s_t(u) = (α / (6 λ^{3/2})) · u³/√t + (γ / (24 λ²)) · u⁴ / t`.

This file:
* Defines the rescaled-coordinate perturbation `rescaledPerturbation`.
* Proves the rescaling identity `anharmonic_rescaling_identity`.
-/

open Real

namespace Laplace.OneD

/-- The cubic coefficient `A = α / (6 λ^{3/2})` of the rescaled perturbation
(written without fractional powers as `α / (6 λ √λ)`). -/
noncomputable def cubicScale (lam alpha : ℝ) : ℝ :=
  alpha / (6 * lam * Real.sqrt lam)

/-- The quartic coefficient `B = γ / (24 λ²)` of the rescaled perturbation. -/
noncomputable def quarticScale (lam gamma : ℝ) : ℝ :=
  gamma / (24 * lam ^ 2)

/-- The rescaled perturbation `s_t(u) = A · u³/√t + B · u⁴/t`. -/
noncomputable def rescaledPerturbation (lam alpha gamma t u : ℝ) : ℝ :=
  cubicScale lam alpha * u ^ 3 / Real.sqrt t +
    quarticScale lam gamma * u ^ 4 / t

/-- **Rescaling identity**: under the substitution `x = u/√(λt)`,
`tL(x) = u²/2 + s_t(u)`. -/
theorem anharmonic_rescaling_identity {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (alpha gamma u : ℝ) :
    t * anharmonicPotential lam alpha gamma (u / Real.sqrt (lam * t)) =
      u ^ 2 / 2 + rescaledPerturbation lam alpha gamma t u := by
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_lamt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  -- Compute powers of (u / √(λt)).
  have hd2 : (u / Real.sqrt (lam * t)) ^ 2 = u ^ 2 / (lam * t) := by
    rw [div_pow, Real.sq_sqrt hlamt.le]
  have hd3 : (u / Real.sqrt (lam * t)) ^ 3 =
      u ^ 3 / ((lam * t) * Real.sqrt (lam * t)) := by
    rw [div_pow]
    congr 1
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, Real.sq_sqrt hlamt.le]
  have hd4 : (u / Real.sqrt (lam * t)) ^ 4 = u ^ 4 / (lam * t) ^ 2 := by
    rw [div_pow]
    congr 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hlamt.le]
  -- √(λt) = √λ · √t.
  have hsqrt_split : Real.sqrt (lam * t) = Real.sqrt lam * Real.sqrt t :=
    Real.sqrt_mul hlam.le t
  unfold anharmonicPotential rescaledPerturbation cubicScale quarticScale
  rw [hd2, hd3, hd4, hsqrt_split]
  -- Now goal is purely algebraic in lam, t, alpha, gamma, u, √lam, √t.
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  have hsqrt_lam_ne : Real.sqrt lam ≠ 0 := hsqrt_lam_pos.ne'
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  field_simp
  -- After field_simp, only `√lam · √lam = lam` and `√t · √t = t` remain.
  -- Use `linear_combination` to close.
  have hsl_sq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
  have hst_sq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  nlinarith [hsl_sq, hst_sq, sq_nonneg (Real.sqrt lam),
             sq_nonneg (Real.sqrt t), mul_self_nonneg (Real.sqrt lam),
             mul_self_nonneg (Real.sqrt t), hlam, ht]

/-! ## Coercivity in rescaled coordinates

Under the discriminant hypothesis `α² < 3λγ`, the rescaling identity combined
with `anharmonic_coercive` yields uniform Gaussian decay of the integrand.
-/

/-- The rescaling identity rephrased: `u²/2 + s_t(u) = tL(u/√(λt))`. -/
lemma half_sq_add_rescaled_eq {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (alpha gamma u : ℝ) :
    u ^ 2 / 2 + rescaledPerturbation lam alpha gamma t u =
      t * anharmonicPotential lam alpha gamma (u / Real.sqrt (lam * t)) :=
  (anharmonic_rescaling_identity hlam ht alpha gamma u).symm

/-- Under coercivity, the Gibbs Boltzmann factor `exp(-tL)` in rescaled
coordinates is bounded by a Gaussian: there exists `c₀ > 0` such that

  `exp(-u²/2 - s_t(u)) ≤ exp(-c₀ · u²)`  for all `u`, `t > 0`. -/
theorem rescaled_boltzmann_decay {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ c₀ > 0, ∀ {t : ℝ}, 0 < t → ∀ u : ℝ,
      Real.exp (-(u ^ 2 / 2 + rescaledPerturbation lam alpha gamma t u)) ≤
        Real.exp (-(c₀ * u ^ 2)) := by
  obtain ⟨c, hc_pos, hcoer⟩ := anharmonic_coercive lam alpha gamma hlam hgamma hdisc
  refine ⟨c / lam, div_pos hc_pos hlam, ?_⟩
  intro t ht u
  rw [half_sq_add_rescaled_eq hlam ht]
  apply Real.exp_le_exp.mpr
  -- Want: -(t · L(u/√(λt))) ≤ -((c/λ) · u²), i.e., (c/λ) · u² ≤ t · L(u/√(λt)).
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hL := hcoer (u / Real.sqrt (lam * t))
  -- hL : c · (u/√(λt))² ≤ L(u/√(λt))
  have hsq_div : (u / Real.sqrt (lam * t)) ^ 2 = u ^ 2 / (lam * t) := by
    rw [div_pow, Real.sq_sqrt hlamt.le]
  rw [hsq_div] at hL
  -- hL : c · u² / (λt) ≤ L(u/√(λt))
  -- Multiply both sides by `t`:
  have hkey : c / lam * u ^ 2 = t * (c * (u ^ 2 / (lam * t))) := by
    field_simp
  have hgoal : c / lam * u ^ 2 ≤ t * anharmonicPotential lam alpha gamma
        (u / Real.sqrt (lam * t)) := by
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hL ht.le
  linarith

/-- Under coercivity, the integrand factor `e^{-u²/2} · max(1, e^{-s_t(u)})`
is bounded by `e^{-c₀ u²}` for some `c₀ > 0`. This is the key uniform
Gaussian-decay estimate that powers the global remainder argument. -/
theorem rescaled_max_decay {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ c₀ > 0, ∀ {t : ℝ}, 0 < t → ∀ u : ℝ,
      Real.exp (-(u ^ 2) / 2) *
          max 1 (Real.exp (-rescaledPerturbation lam alpha gamma t u)) ≤
        Real.exp (-(c₀ * u ^ 2)) := by
  obtain ⟨c, hc_pos, hboltz⟩ :=
    rescaled_boltzmann_decay hlam hgamma hdisc
  refine ⟨min (1 / 2) c, lt_min (by norm_num) hc_pos, ?_⟩
  intro t ht u
  -- LHS = max(exp(-u²/2), exp(-u²/2 - s_t(u))) by `mul_max_eq_max_mul`-style algebra.
  have hLHS : Real.exp (-(u ^ 2) / 2) *
        max 1 (Real.exp (-rescaledPerturbation lam alpha gamma t u)) =
      max (Real.exp (-(u ^ 2) / 2))
          (Real.exp (-(u ^ 2 / 2 + rescaledPerturbation lam alpha gamma t u))) := by
    rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le]
    congr 1
    · ring_nf
    · rw [show (-(u ^ 2 / 2 + rescaledPerturbation lam alpha gamma t u) : ℝ) =
            -(u ^ 2) / 2 + (-rescaledPerturbation lam alpha gamma t u) by ring]
      rw [Real.exp_add]
  rw [hLHS]
  -- Bound each side of the max by exp(-c₀ u²).
  apply max_le
  · -- exp(-u²/2) ≤ exp(-c₀ · u²) for c₀ ≤ 1/2.
    apply Real.exp_le_exp.mpr
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    have hmin_le : min (1 / 2) c ≤ 1 / 2 := min_le_left _ _
    have : min (1 / 2) c * u ^ 2 ≤ 1 / 2 * u ^ 2 :=
      mul_le_mul_of_nonneg_right hmin_le hu2
    linarith
  · -- exp(-u²/2 - s_t(u)) ≤ exp(-c · u²) ≤ exp(-c₀ · u²).
    have h := hboltz ht u
    apply le_trans h
    apply Real.exp_le_exp.mpr
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    have hmin_le : min (1 / 2) c ≤ c := min_le_right _ _
    have : min (1 / 2) c * u ^ 2 ≤ c * u ^ 2 :=
      mul_le_mul_of_nonneg_right hmin_le hu2
    linarith

/-! ## Polynomial bound on the squared perturbation

We need `s_t(u)² ≤ C · (u^6 + u^8)/t` for `t ≥ 1` to control the integral
remainder by Gaussian moments. We use the loose-but-clean bound
`(a+b)² ≤ 2a² + 2b²` to avoid handling the cross term.
-/

/-- `(a + b)² ≤ 2 a² + 2 b²` for any reals. -/
private lemma sq_add_le_two_mul_sq_add (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have := sq_nonneg (a - b)
  nlinarith

/-- **Polynomial bound on `s_t(u)²`**: for `t ≥ 1`,

  `s_t(u)² ≤ 2 (A² + B²) · (u^6 + u^8) / t`,

where `A = cubicScale lam alpha` and `B = quarticScale lam gamma`. -/
theorem rescaledPerturbation_sq_le (lam alpha gamma : ℝ)
    {t : ℝ} (ht : 1 ≤ t) (u : ℝ) :
    rescaledPerturbation lam alpha gamma t u ^ 2 ≤
      2 * (cubicScale lam alpha ^ 2 + quarticScale lam gamma ^ 2)
        * (u ^ 6 + u ^ 8) / t := by
  set A := cubicScale lam alpha
  set B := quarticScale lam gamma
  have ht_pos : 0 < t := by linarith
  have ht_ne : t ≠ 0 := ht_pos.ne'
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  have hsqrt_t_sq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht_pos.le
  -- (s_t(u))² ≤ 2·(A·u³/√t)² + 2·(B·u⁴/t)² = 2A²u⁶/t + 2B²u⁸/t².
  have hs_sq_le : rescaledPerturbation lam alpha gamma t u ^ 2 ≤
      2 * (A * u ^ 3 / Real.sqrt t) ^ 2
        + 2 * (B * u ^ 4 / t) ^ 2 := by
    unfold rescaledPerturbation
    exact sq_add_le_two_mul_sq_add _ _
  -- Simplify each square.
  have hsq_first : (A * u ^ 3 / Real.sqrt t) ^ 2 = A ^ 2 * u ^ 6 / t := by
    rw [div_pow, mul_pow, hsqrt_t_sq]
    congr 1
    rw [show (u ^ 3 : ℝ) ^ 2 = u ^ 6 by ring]
  have hsq_second : (B * u ^ 4 / t) ^ 2 = B ^ 2 * u ^ 8 / t ^ 2 := by
    rw [div_pow, mul_pow]
    congr 1
    rw [show (u ^ 4 : ℝ) ^ 2 = u ^ 8 by ring]
  rw [hsq_first, hsq_second] at hs_sq_le
  -- For t ≥ 1: 1/t² ≤ 1/t, so B²u⁸/t² ≤ B²u⁸/t.
  have ht_sq_ge : t ≤ t ^ 2 := by nlinarith [ht_pos]
  have h_last : B ^ 2 * u ^ 8 / t ^ 2 ≤ B ^ 2 * u ^ 8 / t := by
    have hnum : 0 ≤ B ^ 2 * u ^ 8 := by positivity
    exact div_le_div_of_nonneg_left hnum ht_pos ht_sq_ge
  -- So the RHS is bounded by `2(A²u⁶ + B²u⁸)/t ≤ 2(A²+B²)(u⁶+u⁸)/t`.
  have hu6_nn : 0 ≤ u ^ 6 := by positivity
  have hu8_nn : 0 ≤ u ^ 8 := by positivity
  have hA_nn : 0 ≤ A ^ 2 := sq_nonneg A
  have hB_nn : 0 ≤ B ^ 2 := sq_nonneg B
  calc rescaledPerturbation lam alpha gamma t u ^ 2
      ≤ 2 * (A ^ 2 * u ^ 6 / t) + 2 * (B ^ 2 * u ^ 8 / t ^ 2) := hs_sq_le
    _ ≤ 2 * (A ^ 2 * u ^ 6 / t) + 2 * (B ^ 2 * u ^ 8 / t) := by linarith
    _ = 2 * (A ^ 2 * u ^ 6 + B ^ 2 * u ^ 8) / t := by field_simp
    _ ≤ 2 * (A ^ 2 + B ^ 2) * (u ^ 6 + u ^ 8) / t := by
          apply div_le_div_of_nonneg_right _ ht_pos.le
          nlinarith [hA_nn, hB_nn, hu6_nn, hu8_nn]

end Laplace.OneD
