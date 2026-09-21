/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TiltInterpolation

/-!
# Cauchy–Schwarz for the tilted covariance and the variance-rate bound

With the interpolation identity, `|P_1(f) − P_0(f)| ≤ t · sup_u |Cov_{P_u}(f, R)|`, and
Cauchy–Schwarz `|Cov_{P_u}(f, R)| ≤ √Var_{P_u}(f) · √Var_{P_u}(R)`, uniform variance bounds
`Var_{P_u}(f) ≤ V²`, `Var_{P_u}(R) ≤ ε²` give `|P_1(f) − P_0(f)| ≤ t V ε`
(`abs_tiltExp_one_sub_zero_le_of_var`). For an empirical residual with
`Var_{P_u}(R) ≤ C² n^{-1} t^{-q}` this is `C V n^{-1/2} t^{1 − q/2}`
(`abs_tiltExp_one_sub_zero_le_of_var_rate`): `q = 0` is the sup-norm exponent of
`EmpiricalRelative`, `q = 1` a root-`n` random linear tilt near the minimizer, `q = 2` the
leading random quadratic variation after centering. The variance hypotheses are the interface
to the fluctuation theory of the empirical loss; they are not derived here.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Bounded measurable functions. -/
def Bdd (f : X → ℝ) : Prop := Measurable f ∧ ∃ M, ∀ x, |f x| ≤ M

theorem Bdd.const (c : ℝ) : Bdd (fun _ : X ↦ c) := ⟨measurable_const, |c|, fun _ ↦ le_rfl⟩

theorem Bdd.add {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun x ↦ f x + g x := by
  obtain ⟨hfm, Mf, hMf⟩ := hf
  obtain ⟨hgm, Mg, hMg⟩ := hg
  exact ⟨hfm.add hgm, Mf + Mg, fun x ↦ (abs_add_le _ _).trans (add_le_add (hMf x) (hMg x))⟩

theorem Bdd.mul {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun x ↦ f x * g x := by
  obtain ⟨hfm, Mf, hMf⟩ := hf
  obtain ⟨hgm, Mg, hMg⟩ := hg
  refine ⟨hfm.mul hgm, Mf * Mg, fun x ↦ ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hMf x) (hMg x) (abs_nonneg _) (le_trans (abs_nonneg _) (hMf x))

theorem Bdd.const_mul (c : ℝ) {f : X → ℝ} (hf : Bdd f) : Bdd fun x ↦ c * f x :=
  (Bdd.const c).mul hf

theorem TiltData.bdd_R {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) : Bdd R :=
  ⟨h.R_meas, M, h.R_bound⟩

variable [Nonempty X]

theorem TiltData.integrable_of_bdd {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f : X → ℝ}
    (hf : Bdd f) (t u : ℝ) :
    Integrable (fun x ↦ f x * Real.exp (-(t * R x * u)) * ν x) μ := by
  obtain ⟨hfm, Mf, hMf⟩ := hf
  exact h.integrable_tilt hfm hMf t u

/-! ### Linearity of the tilted expectation -/

theorem TiltData.tiltNum_add {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f g : X → ℝ}
    (hf : Bdd f) (hg : Bdd g) (t u : ℝ) :
    tiltNum μ ν (fun x ↦ f x + g x) R t u = tiltNum μ ν f R t u + tiltNum μ ν g R t u := by
  unfold tiltNum
  rw [← integral_add (h.integrable_of_bdd hf t u) (h.integrable_of_bdd hg t u)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  ring

omit [Nonempty X] in
theorem tiltNum_const_mul (ν R : X → ℝ) (c : ℝ) (f : X → ℝ) (t u : ℝ) :
    tiltNum μ ν (fun x ↦ c * f x) R t u = c * tiltNum μ ν f R t u := by
  unfold tiltNum
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  ring

omit [Nonempty X] in
theorem tiltNum_const (ν R : X → ℝ) (c : ℝ) (t u : ℝ) :
    tiltNum μ ν (fun _ ↦ c) R t u = c * tiltNum μ ν (fun _ ↦ 1) R t u := by
  unfold tiltNum
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  ring

theorem TiltData.tiltExp_add {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f g : X → ℝ}
    (hf : Bdd f) (hg : Bdd g) (t u : ℝ) :
    tiltExp μ ν (fun x ↦ f x + g x) R t u = tiltExp μ ν f R t u + tiltExp μ ν g R t u := by
  unfold tiltExp
  rw [h.tiltNum_add hf hg, add_div]

theorem tiltExp_const_mul (ν R : X → ℝ) (c : ℝ) (f : X → ℝ) (t u : ℝ) :
    tiltExp μ ν (fun x ↦ c * f x) R t u = c * tiltExp μ ν f R t u := by
  unfold tiltExp
  rw [tiltNum_const_mul, mul_div_assoc]

theorem TiltData.tiltExp_const {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) (c : ℝ)
    (t u : ℝ) : tiltExp μ ν (fun _ ↦ c) R t u = c := by
  unfold tiltExp
  rw [tiltNum_const, mul_div_assoc, div_self (h.tiltNum_one_pos t u).ne', mul_one]

theorem TiltData.tiltExp_nonneg {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {g : X → ℝ}
    (hg : ∀ x, 0 ≤ g x) (t u : ℝ) : 0 ≤ tiltExp μ ν g R t u := by
  unfold tiltExp
  refine div_nonneg (integral_nonneg fun x ↦ ?_) (h.tiltNum_one_pos t u).le
  exact mul_nonneg (mul_nonneg (hg x) (Real.exp_pos _).le) (h.ν_nonneg x)

/-- The tilted variance is nonnegative: `Var f = E[(f − E f)²]`. -/
theorem TiltData.tiltCov_self_nonneg {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f : X → ℝ}
    (hf : Bdd f) (t u : ℝ) : 0 ≤ tiltCov μ ν f f R t u := by
  set c := tiltExp μ ν f R t u with hc
  have hsq : 0 ≤ tiltExp μ ν (fun x ↦ (f x * f x + (-(2 * c)) * f x) + c * c) R t u :=
    h.tiltExp_nonneg (fun x ↦ by nlinarith [sq_nonneg (f x - c)]) t u
  rw [h.tiltExp_add ((hf.mul hf).add (hf.const_mul _)) (Bdd.const _), h.tiltExp_add (hf.mul hf)
    (hf.const_mul _), tiltExp_const_mul, h.tiltExp_const] at hsq
  unfold tiltCov
  rw [← hc]
  linarith

/-- **Cauchy–Schwarz for the tilted covariance.** -/
theorem TiltData.abs_tiltCov_le {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f g : X → ℝ}
    (hf : Bdd f) (hg : Bdd g) (t u : ℝ) :
    |tiltCov μ ν f g R t u| ≤
      Real.sqrt (tiltCov μ ν f f R t u) * Real.sqrt (tiltCov μ ν g g R t u) := by
  set A := tiltCov μ ν f f R t u with hA
  set B := tiltCov μ ν g g R t u with hB
  set C := tiltCov μ ν f g R t u with hC
  have hA0 : 0 ≤ A := h.tiltCov_self_nonneg hf t u
  have hB0 : 0 ≤ B := h.tiltCov_self_nonneg hg t u
  -- the quadratic `Var (f − λ g) = A − 2 λ C + λ² B ≥ 0`
  have hquad : ∀ l : ℝ, 0 ≤ B * (l * l) + (-2 * C) * l + A := by
    intro l
    have hbdd : Bdd fun x ↦ f x + (-l) * g x := hf.add (hg.const_mul _)
    have hvar := h.tiltCov_self_nonneg hbdd t u
    -- expand
    have hE : tiltExp μ ν (fun x ↦ f x + (-l) * g x) R t u =
        tiltExp μ ν f R t u + (-l) * tiltExp μ ν g R t u := by
      rw [h.tiltExp_add hf (hg.const_mul _), tiltExp_const_mul]
    have hsq : (fun x ↦ (f x + (-l) * g x) * (f x + (-l) * g x)) =
        fun x ↦ (f x * f x + (-(2 * l)) * (f x * g x)) + (l * l) * (g x * g x) := by
      funext x
      ring
    have hE2 : tiltExp μ ν (fun x ↦ (f x + (-l) * g x) * (f x + (-l) * g x)) R t u =
        tiltExp μ ν (fun x ↦ f x * f x) R t u +
          (-(2 * l)) * tiltExp μ ν (fun x ↦ f x * g x) R t u +
          (l * l) * tiltExp μ ν (fun x ↦ g x * g x) R t u := by
      rw [hsq, h.tiltExp_add ((hf.mul hf).add ((hf.mul hg).const_mul _)) ((hg.mul hg).const_mul _),
        h.tiltExp_add (hf.mul hf) ((hf.mul hg).const_mul _), tiltExp_const_mul, tiltExp_const_mul]
    unfold tiltCov at hvar
    rw [hE2, hE] at hvar
    unfold tiltCov at hA hB hC
    rw [hA, hB, hC]
    nlinarith [hvar]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hCsq : C ^ 2 ≤ A * B := by nlinarith [hdisc]
  calc |C| ≤ Real.sqrt (A * B) := Real.abs_le_sqrt hCsq
    _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA0 B

/-! ### The variance-rate bounds -/

/-- **Variance bound**: uniform tilted variances `Var(f) ≤ V²`, `Var(R) ≤ ε²` on `[0,1]` give
`|P_1(f) − P_0(f)| ≤ t V ε`. -/
theorem TiltData.abs_tiltExp_one_sub_zero_le_of_var {ν R : X → ℝ} {M : ℝ}
    (h : TiltData μ ν R M) {f : X → ℝ} (hf : Bdd f) {t : ℝ} (ht : 0 ≤ t) {V ε : ℝ}
    (hV0 : 0 ≤ V) (hε0 : 0 ≤ ε)
    (hV : ∀ u ∈ Set.Icc (0 : ℝ) 1, tiltCov μ ν f f R t u ≤ V ^ 2)
    (hε : ∀ u ∈ Set.Icc (0 : ℝ) 1, tiltCov μ ν R R R t u ≤ ε ^ 2) :
    |tiltExp μ ν f R t 1 - tiltExp μ ν f R t 0| ≤ t * (V * ε) := by
  obtain ⟨hfm, Mf, hMf⟩ := hf
  refine h.abs_tiltExp_one_sub_zero_le hfm hMf ht fun u hu ↦ ?_
  calc |tiltCov μ ν f R R t u|
      ≤ Real.sqrt (tiltCov μ ν f f R t u) * Real.sqrt (tiltCov μ ν R R R t u) :=
        h.abs_tiltCov_le ⟨hfm, Mf, hMf⟩ h.bdd_R t u
    _ ≤ Real.sqrt (V ^ 2) * Real.sqrt (ε ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt (hV u hu)) (Real.sqrt_le_sqrt (hε u hu))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = V * ε := by rw [Real.sqrt_sq hV0, Real.sqrt_sq hε0]

/-- **The variance-rate bound.** With `Var_{P_u}(R) ≤ C² n^{-1} t^{-q}` and `Var_{P_u}(f) ≤ V²`
uniformly on `[0,1]`, `|P_1(f) − P_0(f)| ≤ C V n^{-1/2} t^{1 − q/2}`. -/
theorem TiltData.abs_tiltExp_one_sub_zero_le_of_var_rate {ν R : X → ℝ} {M : ℝ}
    (h : TiltData μ ν R M) {f : X → ℝ} (hf : Bdd f) {t : ℝ} (ht : 0 < t) {V C q : ℝ}
    (hV0 : 0 ≤ V) (hC0 : 0 ≤ C) {n : ℕ} (hn : 0 < n)
    (hV : ∀ u ∈ Set.Icc (0 : ℝ) 1, tiltCov μ ν f f R t u ≤ V ^ 2)
    (hε : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      tiltCov μ ν R R R t u ≤ (C * (n : ℝ) ^ (-(1 / 2 : ℝ)) * t ^ (-(q / 2))) ^ 2) :
    |tiltExp μ ν f R t 1 - tiltExp μ ν f R t 0| ≤
      C * V * (n : ℝ) ^ (-(1 / 2 : ℝ)) * t ^ (1 - q / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hε0 : 0 ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)) * t ^ (-(q / 2)) := by positivity
  have hb := h.abs_tiltExp_one_sub_zero_le_of_var hf ht.le hV0 hε0 hV hε
  refine hb.trans (le_of_eq ?_)
  rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_one]
  ring

end Laplace.Multi
