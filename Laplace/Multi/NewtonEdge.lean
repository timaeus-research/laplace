/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.WallCutoff

/-!
# The Newton-edge theorem: the crossover at a wall is the quasi-homogeneous initial form

Write the family near a wall point as a function `F x s` of the loss variable `x` and the truth
variable `s`. Fix weights `α, γ > 0`. `E` is **quasi-homogeneous** of degree one for these weights
if `E (l^α x) (l^γ s) = l · E x s` for `l > 0` (`QuasiHomog`): all its monomials `x^a s^b` lie on
the Newton edge `aα + bγ = 1`.

* **Exact collapse.** If the family is quasi-homogeneous, the substitution `x = t^{-α} u` gives, for
  every observable read at the scale of the wall, `∫ g(t^α x) e^{-tE(x,s)} dx = t^{-α} ∫ g(u)
  e^{-E(u, t^γ s)} du` (`integral_exp_neg_quasiHomog`); in particular the energy statistic is
  exactly a function of the combined variable `σ = s t^γ` (`energy_quasiHomog`).
* **Leading order.** If `F = E + R` with `R ≥ 0` of higher weight — `t R(t^{-α}u, σ t^{-γ}) → 0`
  pointwise, which for a monomial `x^a s^b` is `aα + bγ > 1` — then along the path `s = σ t^{-γ}`
  and with a compact prior, the rescaled partition function and energy numerator converge to those
  of the edge form `E(·, σ)` (`tendsto_rpow_mul_newtonEdge_den`, `…_num`), and the energy statistic
  converges to `E_σ[E(·,σ)]` under `e^{-E(·,σ)}` (`tendsto_newtonEdge_energy`).

So the combined variable is fixed by the two vertices of the edge (the exponent data of the two
chambers) and the shape of the crossover by the whole edge polynomial. The wall models
`σ u^{2k} + u^{2(k+m)}` (`WallCrossover`) and `u²(u − σ)²` (`MergingZeros`) are the edge forms with
weights `(1/2(k+m), m/(k+m))` and `(1/4, 1/4)` (`quasiHomog_wall`, `quasiHomog_merge`).
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- Quasi-homogeneity of degree one for the weights `(α, γ)`. -/
def QuasiHomog (E : ℝ → ℝ → ℝ) (α γ : ℝ) : Prop :=
  ∀ l : ℝ, 0 < l → ∀ x s : ℝ, E (l ^ α * x) (l ^ γ * s) = l * E x s

/-- The rescaling identity `t · E(t^{-α} u, s) = E(u, t^γ s)`. -/
theorem QuasiHomog.mul_apply_rescaled {E : ℝ → ℝ → ℝ} {α γ : ℝ} (hE : QuasiHomog E α γ) {t : ℝ}
    (ht : 0 < t) (u s : ℝ) : t * E (t ^ (-α) * u) s = E u (t ^ γ * s) := by
  have h := hE t⁻¹ (inv_pos.mpr ht) u (t ^ γ * s)
  rw [Real.inv_rpow ht.le, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, ← mul_assoc,
    ← Real.rpow_neg ht.le, ← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, one_mul] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

/-- **Exact collapse** for a quasi-homogeneous family: an observable read at the scale `t^α`. -/
theorem integral_exp_neg_quasiHomog {E : ℝ → ℝ → ℝ} {α γ : ℝ} (hE : QuasiHomog E α γ) {t : ℝ}
    (ht : 0 < t) (s : ℝ) (g : ℝ → ℝ) :
    (∫ x, g (t ^ α * x) * Real.exp (-(t * E x s))) =
      t ^ (-α) * ∫ u, g u * Real.exp (-E u (t ^ γ * s)) := by
  set c : ℝ := t ^ (-α) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hcinv : t ^ α * c = 1 := by
    rw [hc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
  have hcomp := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ g (t ^ α * x) * Real.exp (-(t * E x s))) c
  rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at hcomp
  have hpt : ∀ u : ℝ, g (t ^ α * (c * u)) * Real.exp (-(t * E (c * u) s)) =
      g u * Real.exp (-E u (t ^ γ * s)) := by
    intro u
    rw [← mul_assoc, hcinv, one_mul, hc, hE.mul_apply_rescaled ht]
  simp only [hpt] at hcomp
  rw [hc] at hcomp ⊢
  rw [hcomp, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos ht _).ne', one_mul]

/-- The energy statistic of a quasi-homogeneous family is exactly a function of `σ = s t^γ`. -/
theorem energy_quasiHomog {E : ℝ → ℝ → ℝ} {α γ : ℝ} (hE : QuasiHomog E α γ) {t : ℝ} (ht : 0 < t)
    (s : ℝ) :
    t * ((∫ x, E x s * Real.exp (-(t * E x s))) / ∫ x, Real.exp (-(t * E x s))) =
      (∫ u, E u (t ^ γ * s) * Real.exp (-E u (t ^ γ * s))) /
        ∫ u, Real.exp (-E u (t ^ γ * s)) := by
  have hnum := integral_exp_neg_quasiHomog hE ht s (fun v ↦ E v (t ^ γ * s))
  have hden := integral_exp_neg_quasiHomog hE ht s (fun _ ↦ (1 : ℝ))
  simp only [one_mul] at hden
  have hpt : ∀ x : ℝ, t * E x s = E (t ^ α * x) (t ^ γ * s) := fun x ↦ (hE t ht x s).symm
  rw [mul_div_assoc', ← integral_const_mul]
  have e0 : (fun x : ℝ ↦ t * (E x s * Real.exp (-(t * E x s)))) =
      fun x ↦ E (t ^ α * x) (t ^ γ * s) * Real.exp (-(t * E x s)) := by
    funext x
    rw [← mul_assoc, hpt x]
  rw [e0, hnum, hden, mul_div_mul_left _ _ (Real.rpow_pos_of_pos ht _).ne']

/-! ### The two one-dimensional wall models are edge forms -/

theorem quasiHomog_wall (k m : ℕ) (hn : 1 ≤ k + m) :
    QuasiHomog (fun u σ ↦ σ * u ^ (2 * k) + u ^ (2 * (k + m)))
      (1 / (2 * ((k : ℝ) + m))) ((m : ℝ) / (k + m)) := by
  intro l hl u σ
  have hn' : (0 : ℝ) < (k : ℝ) + m := by exact_mod_cast hn
  have h1 : (l ^ (1 / (2 * ((k : ℝ) + m)))) ^ (2 * (k + m)) = l := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
    push_cast
    rw [show 1 / (2 * ((k : ℝ) + m)) * (2 * (k + m)) = 1 by field_simp, Real.rpow_one]
  have h2 : l ^ ((m : ℝ) / (k + m)) * (l ^ (1 / (2 * ((k : ℝ) + m)))) ^ (2 * k) = l := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le, ← Real.rpow_add hl]
    push_cast
    rw [show (m : ℝ) / (k + m) + 1 / (2 * ((k : ℝ) + m)) * (2 * k) = 1 by field_simp; ring,
      Real.rpow_one]
  simp only
  rw [mul_pow, mul_pow, h1]
  calc l ^ ((m : ℝ) / (k + m)) * σ * ((l ^ (1 / (2 * ((k : ℝ) + m)))) ^ (2 * k) * u ^ (2 * k)) +
        l * u ^ (2 * (k + m))
      = (l ^ ((m : ℝ) / (k + m)) * (l ^ (1 / (2 * ((k : ℝ) + m)))) ^ (2 * k)) * (σ * u ^ (2 * k)) +
        l * u ^ (2 * (k + m)) := by ring
    _ = l * (σ * u ^ (2 * k) + u ^ (2 * (k + m))) := by rw [h2]; ring

theorem quasiHomog_merge : QuasiHomog (fun u σ ↦ u ^ 2 * (u - σ) ^ 2) (1 / 4) (1 / 4) := by
  intro l hl u σ
  have h4 : (l ^ (1 / 4 : ℝ)) ^ 4 = l := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
    norm_num
  simp only
  have : l ^ (1 / 4 : ℝ) * u - l ^ (1 / 4 : ℝ) * σ = l ^ (1 / 4 : ℝ) * (u - σ) := by ring
  rw [this, mul_pow, mul_pow,
    show (l ^ (1 / 4 : ℝ)) ^ 2 * u ^ 2 * ((l ^ (1 / 4 : ℝ)) ^ 2 * (u - σ) ^ 2) =
      (l ^ (1 / 4 : ℝ)) ^ 4 * (u ^ 2 * (u - σ) ^ 2) by ring, h4]

/-! ### Leading order: edge form plus a higher-weight remainder, with a compact prior -/

/-- Rescaled cutoff integrals along the wall path, for a general integrand shape. -/
theorem rpow_mul_integral_edge_eq {E R : ℝ → ℝ → ℝ} {α γ : ℝ} (hE : QuasiHomog E α γ) (χ : ℝ → ℝ)
    {t : ℝ} (ht : 0 < t) (σ : ℝ) (Φ : ℝ → ℝ) :
    t ^ α * ∫ x, χ x * Φ (t * (E x (σ * t ^ (-γ)) + R x (σ * t ^ (-γ)))) =
      ∫ u, χ (t ^ (-α) * u) * Φ (E u σ + t * R (t ^ (-α) * u) (σ * t ^ (-γ))) := by
  set c : ℝ := t ^ (-α) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hcomp := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ χ x * Φ (t * (E x (σ * t ^ (-γ)) + R x (σ * t ^ (-γ))))) c
  rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at hcomp
  have hσ : t ^ γ * (σ * t ^ (-γ)) = σ := by
    rw [mul_comm σ, ← mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, one_mul]
  have hpt : ∀ u : ℝ, χ (c * u) * Φ (t * (E (c * u) (σ * t ^ (-γ)) + R (c * u) (σ * t ^ (-γ)))) =
      χ (c * u) * Φ (E u σ + t * R (c * u) (σ * t ^ (-γ))) := by
    intro u
    rw [mul_add, hc, hE.mul_apply_rescaled ht, hσ]
  simp only [hpt] at hcomp
  rw [hc] at hcomp ⊢
  rw [hcomp, Real.rpow_neg ht.le α, inv_inv]

/-- Standing hypotheses of the Newton-edge theorem: nonnegative edge form and remainder, continuity,
the higher-weight condition along the path, and integrability of the edge density at `σ`. -/
structure EdgeData (E R : ℝ → ℝ → ℝ) (α γ σ : ℝ) : Prop where
  hα : 0 < α
  quasi : QuasiHomog E α γ
  E_cont : Continuous (Function.uncurry E)
  R_cont : Continuous (Function.uncurry R)
  E_nonneg : ∀ u s, 0 ≤ E u s
  R_nonneg : ∀ x s, 0 ≤ R x s
  R_lim : ∀ u, Tendsto (fun t ↦ t * R (t ^ (-α) * u) (σ * t ^ (-γ))) atTop (𝓝 0)
  E_int : Integrable fun u ↦ Real.exp (-E u σ)
  EE_int : Integrable fun u ↦ E u σ * Real.exp (-E u σ)

theorem EdgeData.tendsto_scaled_cutoff {E R : ℝ → ℝ → ℝ} {α γ σ : ℝ} (hd : EdgeData E R α γ σ)
    {χ : ℝ → ℝ} (hχ : Cutoff χ) (u : ℝ) :
    Tendsto (fun t : ℝ ↦ χ (t ^ (-α) * u)) atTop (𝓝 (χ 0)) := by
  have hq : Tendsto (fun t : ℝ ↦ t ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hd.hα
  have h0 : Tendsto (fun t : ℝ ↦ t ^ (-α) * u) atTop (𝓝 0) := by simpa using hq.mul_const u
  exact (hχ.cont.tendsto 0).comp h0

/-- The rescaled partition function converges to the edge partition function. -/
theorem EdgeData.tendsto_rpow_mul_den {E R : ℝ → ℝ → ℝ} {α γ σ : ℝ} (hd : EdgeData E R α γ σ)
    {χ : ℝ → ℝ} (hχ : Cutoff χ) :
    Tendsto (fun t ↦ t ^ α * ∫ x, χ x * Real.exp (-(t * (E x (σ * t ^ (-γ)) + R x (σ * t ^ (-γ))))))
      atTop (𝓝 (χ 0 * ∫ u, Real.exp (-E u σ))) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hχc := hχ.cont
  have hEc := hd.E_cont
  have hRc := hd.R_cont
  rw [← integral_const_mul]
  have key : Tendsto (fun t ↦ ∫ u, χ (t ^ (-α) * u) *
      Real.exp (-(E u σ + t * R (t ^ (-α) * u) (σ * t ^ (-γ))))) atTop
      (𝓝 (∫ u, χ 0 * Real.exp (-E u σ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u ↦ M * Real.exp (-E u σ))
      (Filter.Eventually.of_forall fun t ↦ ?_) ?_
      (hd.E_int.const_mul M) (Filter.Eventually.of_forall fun u ↦ ?_)
    · have h1 : Continuous fun u : ℝ ↦ E u σ := hEc.comp (continuous_id.prodMk continuous_const)
      have h2 : Continuous fun u : ℝ ↦ R (t ^ (-α) * u) (σ * t ^ (-γ)) :=
        hRc.comp ((continuous_const.mul continuous_id).prodMk continuous_const)
      exact (by fun_prop : Continuous fun u : ℝ ↦ χ (t ^ (-α) * u) *
        Real.exp (-(E u σ + t * R (t ^ (-α) * u) (σ * t ^ (-γ))))).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with t ht
      refine Filter.Eventually.of_forall fun u ↦ ?_
      rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      refine mul_le_mul (hM _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
        ((abs_nonneg _).trans (hM 0))
      have := mul_nonneg ht.le (hd.R_nonneg (t ^ (-α) * u) (σ * t ^ (-γ)))
      linarith
    · have hlim : Tendsto (fun t ↦ Real.exp (-(E u σ + t * R (t ^ (-α) * u) (σ * t ^ (-γ)))))
          atTop (𝓝 (Real.exp (-E u σ))) := by
        have h := ((hd.R_lim u).const_add (E u σ)).neg
        rw [add_zero] at h
        exact (Real.continuous_exp.tendsto _).comp h
      exact (hd.tendsto_scaled_cutoff hχ u).mul hlim
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [rpow_mul_integral_edge_eq hd.quasi χ ht σ (fun y ↦ Real.exp (-y))]

/-- `x e^{-x} ≤ 1`. -/
theorem mul_exp_neg_le_one (x : ℝ) : x * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hpos := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
  linarith

/-- The rescaled energy numerator converges to the edge energy numerator. -/
theorem EdgeData.tendsto_rpow_mul_num {E R : ℝ → ℝ → ℝ} {α γ σ : ℝ} (hd : EdgeData E R α γ σ)
    {χ : ℝ → ℝ} (hχ : Cutoff χ) :
    Tendsto (fun t ↦ t ^ α * ∫ x, χ x * (t * (E x (σ * t ^ (-γ)) + R x (σ * t ^ (-γ))) *
      Real.exp (-(t * (E x (σ * t ^ (-γ)) + R x (σ * t ^ (-γ))))))) atTop
      (𝓝 (χ 0 * ∫ u, E u σ * Real.exp (-E u σ))) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hχc := hχ.cont
  have hEc := hd.E_cont
  have hRc := hd.R_cont
  rw [← integral_const_mul]
  have hdom : Integrable fun u ↦ M * ((E u σ + 1) * Real.exp (-E u σ)) := by
    refine ((hd.EE_int.add hd.E_int).const_mul M).congr (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have key : Tendsto (fun t ↦ ∫ u, χ (t ^ (-α) * u) *
      ((E u σ + t * R (t ^ (-α) * u) (σ * t ^ (-γ))) *
        Real.exp (-(E u σ + t * R (t ^ (-α) * u) (σ * t ^ (-γ)))))) atTop
      (𝓝 (∫ u, χ 0 * (E u σ * Real.exp (-E u σ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u ↦ M * ((E u σ + 1) * Real.exp (-E u σ)))
      (Filter.Eventually.of_forall fun t ↦ ?_) ?_ hdom
      (Filter.Eventually.of_forall fun u ↦ ?_)
    · have h1 : Continuous fun u : ℝ ↦ E u σ := hEc.comp (continuous_id.prodMk continuous_const)
      have h2 : Continuous fun u : ℝ ↦ R (t ^ (-α) * u) (σ * t ^ (-γ)) :=
        hRc.comp ((continuous_const.mul continuous_id).prodMk continuous_const)
      exact (by fun_prop : Continuous fun u : ℝ ↦ χ (t ^ (-α) * u) *
        ((E u σ + t * R (t ^ (-α) * u) (σ * t ^ (-γ))) *
          Real.exp (-(E u σ + t * R (t ^ (-α) * u) (σ * t ^ (-γ)))))).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with t ht
      refine Filter.Eventually.of_forall fun u ↦ ?_
      have hE0 := hd.E_nonneg u σ
      have hR0 : 0 ≤ t * R (t ^ (-α) * u) (σ * t ^ (-γ)) :=
        mul_nonneg ht.le (hd.R_nonneg _ _)
      set y := t * R (t ^ (-α) * u) (σ * t ^ (-γ)) with hy
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le)]
      refine mul_le_mul (hM _) ?_ (by positivity) hM0
      -- `(E + y) e^{-(E+y)} = E e^{-E} e^{-y} + (y e^{-y}) e^{-E} ≤ E e^{-E} + e^{-E}`
      have hsplit : (E u σ + y) * Real.exp (-(E u σ + y)) =
          E u σ * Real.exp (-E u σ) * Real.exp (-y) + (y * Real.exp (-y)) * Real.exp (-E u σ) := by
        rw [neg_add, Real.exp_add]
        ring
      rw [hsplit]
      have h1 : E u σ * Real.exp (-E u σ) * Real.exp (-y) ≤ E u σ * Real.exp (-E u σ) := by
        have := Real.exp_le_one_iff.mpr (by linarith : -y ≤ 0)
        exact mul_le_of_le_one_right (mul_nonneg hE0 (Real.exp_pos _).le) this
      have h2 : (y * Real.exp (-y)) * Real.exp (-E u σ) ≤ 1 * Real.exp (-E u σ) :=
        mul_le_mul_of_nonneg_right (mul_exp_neg_le_one y) (Real.exp_pos _).le
      linarith
    · have hin : Tendsto (fun t ↦ E u σ + t * R (t ^ (-α) * u) (σ * t ^ (-γ))) atTop
          (𝓝 (E u σ)) := by
        have h := (hd.R_lim u).const_add (E u σ)
        rwa [add_zero] at h
      exact (hd.tendsto_scaled_cutoff hχ u).mul
        (hin.mul ((Real.continuous_exp.tendsto _).comp hin.neg))
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [rpow_mul_integral_edge_eq hd.quasi χ ht σ (fun y ↦ y * Real.exp (-y))]

/-- The energy statistic of the family with a compact prior. -/
noncomputable def edgeEnergy (χ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (s t : ℝ) : ℝ :=
  t * ((∫ x, χ x * (F x s * Real.exp (-(t * F x s)))) / ∫ x, χ x * Real.exp (-(t * F x s)))

/-- **The Newton-edge theorem**: along the path `s = σ t^{-γ}`, the energy statistic of the family
`E + R` converges to the energy of the edge form at `σ`, `E_σ[E(·,σ)]` under `e^{-E(·,σ)}`. -/
theorem EdgeData.tendsto_energy {E R : ℝ → ℝ → ℝ} {α γ σ : ℝ} (hd : EdgeData E R α γ σ)
    {χ : ℝ → ℝ} (hχ : Cutoff χ) :
    Tendsto (fun t ↦ edgeEnergy χ (fun x s ↦ E x s + R x s) (σ * t ^ (-γ)) t) atTop
      (𝓝 ((∫ u, E u σ * Real.exp (-E u σ)) / ∫ u, Real.exp (-E u σ))) := by
  have hN := hd.tendsto_rpow_mul_num hχ
  have hD := hd.tendsto_rpow_mul_den hχ
  have hpos : 0 < ∫ u, Real.exp (-E u σ) := by
    refine (integral_pos_iff_support_of_nonneg (fun u ↦ (Real.exp_pos _).le) hd.E_int).mpr ?_
    have : Function.support (fun u ↦ Real.exp (-E u σ)) = Set.univ := by
      ext u
      simp [(Real.exp_pos _).ne']
    rw [this]
    simp
  have hD0 : χ 0 * ∫ u, Real.exp (-E u σ) ≠ 0 := (mul_pos hχ.pos hpos).ne'
  have := hN.div hD hD0
  rw [mul_div_mul_left _ _ hχ.pos.ne'] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Pi.div_apply]
  rw [mul_div_mul_left _ _ (Real.rpow_pos_of_pos ht _).ne']
  unfold edgeEnergy
  rw [mul_div_assoc']
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  ring

end Laplace.Multi
