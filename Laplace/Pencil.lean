/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Gibbs

/-!
# The pencil identity for pairs of potentials

For two potentials `L₁ L₂ : ℝ → ℝ` and the interpolating pencil
`Lₛ = L₁ + s • (L₂ - L₁)`, the fundamental theorem of calculus applied to
`s ↦ exp (-(t * Lₛ w))` gives the exact identity

  `exp (-(t * L₁ w)) - exp (-(t * L₂ w))
     = t * ∫ s in 0..1, (L₂ w - L₁ w) * exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))`

pointwise in `w` (`exp_pencil_identity`), and hence, integrated against an
observable `φ`, converts the difference of two Boltzmann integrals into a
pencil-averaged integral with the amplitude `(L₂ - L₁) * φ`
(`pencil_identity_integrated`). This is Lemma 7.1 of the germbij note
("What expectation values know about the loss landscape", 2026-08), the first
step of the singular identifiability theorem there.
-/

open MeasureTheory intervalIntegral Real

namespace Laplace

/-- **Scalar pencil identity.** For reals `x y`, the fundamental theorem of
calculus applied to `s ↦ exp (-(t * (x + s * (y - x))))` on `[0, 1]`. -/
theorem exp_sub_exp_pencil (t x y : ℝ) :
    Real.exp (-(t * x)) - Real.exp (-(t * y))
      = t * ∫ s in (0 : ℝ)..1,
          (y - x) * Real.exp (-(t * (x + s * (y - x)))) := by
  set a := x with ha
  set g := y - x with hg
  -- The integrand is the negative of the derivative of `F s = exp (-(t * (a + s * g)))`.
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ Real.exp (-(t * (a + s * g))))
        (-(t * g) * Real.exp (-(t * (a + s * g)))) s := by
    intro s _
    have h : HasDerivAt (fun s : ℝ ↦ a + s * g) g s := by
      simpa using ((hasDerivAt_id s).mul_const g).const_add a
    have h₁ : HasDerivAt (fun s : ℝ ↦ -(t * (a + s * g))) (-(t * g)) s :=
      (h.const_mul t).neg
    simpa [mul_comm] using h₁.exp
  have hcont : Continuous fun s : ℝ =>
      -(t * g) * Real.exp (-(t * (a + s * g))) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun s : ℝ ↦ -(t * g) * Real.exp (-(t * (a + s * g)))) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- `∫₀¹ -(t g) e^{...} = e^{-(t y)} - e^{-(t x)}`; rearrange.
  have h0 : a + (0 : ℝ) * g = x := by simp [ha]
  have h1 : a + (1 : ℝ) * g = y := by simp [ha, hg]
  rw [h0, h1] at hftc
  calc Real.exp (-(t * x)) - Real.exp (-(t * y))
      = -(∫ s in (0 : ℝ)..1, -(t * g) * Real.exp (-(t * (a + s * g)))) := by
        rw [hftc]; ring
    _ = ∫ s in (0 : ℝ)..1, (t * g) * Real.exp (-(t * (a + s * g))) := by
        rw [← intervalIntegral.integral_neg]; congr 1; ext s; ring
    _ = t * ∫ s in (0 : ℝ)..1, g * Real.exp (-(t * (a + s * g))) := by
        rw [← intervalIntegral.integral_const_mul]; congr 1; ext s; ring
    _ = t * ∫ s in (0 : ℝ)..1,
          (y - x) * Real.exp (-(t * (x + s * (y - x)))) := by
        rw [ha, hg]

/-- **Pointwise pencil identity.** The scalar identity evaluated along a pair
of potentials: for any `L₁ L₂ : ℝ → ℝ`, `t w : ℝ`, the difference of Boltzmann
factors is `t` times the pencil-averaged Boltzmann factor with amplitude
`L₂ w - L₁ w`. -/
theorem exp_pencil_identity (L₁ L₂ : ℝ → ℝ) (t w : ℝ) :
    Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))
      = t * ∫ s in (0 : ℝ)..1,
          (L₂ w - L₁ w) * Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))) :=
  exp_sub_exp_pencil t (L₁ w) (L₂ w)

/-- **Integrated pencil identity.** Integrating the pointwise identity against
an observable `φ` and exchanging the order of integration (Fubini). The
integrability hypothesis is stated for the uncurried integrand on
`[0,1] × ℝ`. -/
theorem pencil_identity_integrated (L₁ L₂ φ : ℝ → ℝ) (t : ℝ)
    (hint : Integrable (Function.uncurry fun s w =>
        φ w * ((L₂ w - L₁ w) *
          Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume)) :
    ∫ w, φ w * (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)))
      = t * ∫ s in (0 : ℝ)..1, ∫ w,
          φ w * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by
  have key : ∀ w, φ w * (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)))
      = t * ∫ s in (0 : ℝ)..1,
          φ w * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by
    intro w
    rw [exp_pencil_identity L₁ L₂ t w]
    calc φ w * (t * ∫ s in (0 : ℝ)..1,
            (L₂ w - L₁ w) * Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))))
        = t * (φ w * ∫ s in (0 : ℝ)..1,
            (L₂ w - L₁ w) * Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by
          ring
      _ = t * ∫ s in (0 : ℝ)..1,
            φ w * ((L₂ w - L₁ w) *
              Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by
          rw [← intervalIntegral.integral_const_mul]
  have hswap : Integrable (Function.uncurry fun s w ↦
      φ w * ((L₂ w - L₁ w) *
        Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
    rwa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc ∫ w, φ w * (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w)))
      = ∫ w, t * ∫ s in (0 : ℝ)..1,
          φ w * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by
        simp only [key]
    _ = t * ∫ w, ∫ s in (0 : ℝ)..1,
          φ w * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) :=
        MeasureTheory.integral_const_mul t _
    _ = t * ∫ s in (0 : ℝ)..1, ∫ w,
          φ w * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by
        rw [MeasureTheory.intervalIntegral_integral_swap hswap]

/-- **Comparison along the pencil.** For nonnegative potentials and `s ∈ [0,1]`,
the pencil potential `Lₛ = L₁ + s (L₂ - L₁)` is dominated by `L₁ + L₂`, so its
Boltzmann factor dominates that of `L₁ + L₂`. This is the positivity input of
the identifiability theorem (germbij Theorem 7.3). -/
lemma exp_pencil_ge (L₁ L₂ : ℝ → ℝ) {t s : ℝ} (w : ℝ)
    (ht : 0 ≤ t) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h₁ : 0 ≤ L₁ w) (h₂ : 0 ≤ L₂ w) :
    Real.exp (-(t * (L₁ w + L₂ w)))
      ≤ Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))) := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left _ ht
  nlinarith [mul_nonneg hs0 h₁, mul_nonneg (sub_nonneg.mpr hs1) h₂]

/-- **Pencil identity for partition functions** (the case `φ = 1` of the
integrated identity), phrased in terms of the seabed's `partitionFunction`. -/
theorem partitionFunction_pencil (L₁ L₂ : ℝ → ℝ) (t : ℝ)
    (h₁ : Integrable fun w ↦ Real.exp (-(t * L₁ w)))
    (h₂ : Integrable fun w ↦ Real.exp (-(t * L₂ w)))
    (hint : Integrable (Function.uncurry fun s w ↦
        (L₂ w - L₁ w) * Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))))
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume)) :
    partitionFunction L₁ t - partitionFunction L₂ t
      = t * ∫ s in (0 : ℝ)..1, ∫ w,
          (L₂ w - L₁ w) * Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))) := by
  have huncurry : (Function.uncurry fun s w ↦
      (fun _ : ℝ ↦ (1 : ℝ)) w * ((L₂ w - L₁ w) *
        Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
      = Function.uncurry fun s w ↦
        (L₂ w - L₁ w) * Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))) := by
    funext p
    simp [Function.uncurry]
  have h := pencil_identity_integrated L₁ L₂ (fun _ ↦ 1) t (huncurry ▸ hint)
  simp only [one_mul] at h
  rw [partitionFunction, partitionFunction, ← MeasureTheory.integral_sub h₁ h₂]
  exact h

end Laplace
