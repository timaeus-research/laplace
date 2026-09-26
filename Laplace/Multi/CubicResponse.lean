/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.QuadraticInformationBound

/-!
# The cubic response: how the susceptibility changes as the data move

The covariance is the susceptibility of the responses to the natural coordinates; its derivative
along an exponential tilt is the **cubic response tensor**, the third central mixed moment:

* `thirdCentral ρ g k f = E_ρ[(g − Eg)(k − Ek)(f − Ef)]`, symmetric in its three arguments
  (`thirdCentral_comm₁₂`, `thirdCentral_comm₂₃`), with the moment expansion `thirdCentral_eq`.
* **`hasDerivAt_lawCov_tilted`**: `d/ds Cov_{ν_{sf}}(g, k) = thirdCentral (ν_{sf}) g k f`.
* `hasDerivAt_var_tilted`: the variance moves by the third cumulant, `d/ds Var_{ν_{sf}} f = κ₃`.
* `hasDerivAt_lawCov_dataPath`: along the data path `D_s = ν.tilted (s h)`, the susceptibility
  entries `Cov_{D_s}(S_i, S_j)` move by `thirdCentral D_s (S i) (S j) h`, and the visible contrasts
  by `thirdCentral D_s ⟨u, S⟩ ⟨v, S⟩ h` (`hasDerivAt_lawCov_dirLoss_dataPath`).

In natural coordinates this is `D³A(θ)[u, v, w] = T_θ(u, v, w)`: the e-connection is flat, and the
cubic tensor is what the m-connection and the Levi-Civita connection are built from.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Def

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]

/-- The third central mixed moment `E_ρ[(g − Eg)(k − Ek)(f − Ef)]`. -/
noncomputable def thirdCentral (g k f : X → ℝ) : ℝ :=
  ∫ x, (g x - ∫ y, g y ∂ρ) * (k x - ∫ y, k y ∂ρ) * (f x - ∫ y, f y ∂ρ) ∂ρ

omit [IsProbabilityMeasure ρ] in
theorem thirdCentral_comm₁₂ (g k f : X → ℝ) : thirdCentral ρ g k f = thirdCentral ρ k g f := by
  unfold thirdCentral
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

omit [IsProbabilityMeasure ρ] in
theorem thirdCentral_comm₂₃ (g k f : X → ℝ) : thirdCentral ρ g k f = thirdCentral ρ g f k := by
  unfold thirdCentral
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- The moment expansion of the third central mixed moment. -/
theorem thirdCentral_eq {g k f : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hf : Bdd f) :
    thirdCentral ρ g k f =
      (∫ x, g x * k x * f x ∂ρ) - (∫ x, g x * k x ∂ρ) * (∫ x, f x ∂ρ) -
        (∫ x, g x * f x ∂ρ) * (∫ x, k x ∂ρ) - (∫ x, k x * f x ∂ρ) * (∫ x, g x ∂ρ) +
        2 * ((∫ x, g x ∂ρ) * (∫ x, k x ∂ρ) * ∫ x, f x ∂ρ) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ∫ y, g y ∂ρ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ∫ y, k y ∂ρ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ y, f y ∂ρ := ⟨_, rfl⟩
  have hg1 := integrable_of_bdd_prob ρ hg
  have hk1 := integrable_of_bdd_prob ρ hk
  have hf1 := integrable_of_bdd_prob ρ hf
  have hgk := integrable_of_bdd_prob ρ (hg.mul hk)
  have hgf := integrable_of_bdd_prob ρ (hg.mul hf)
  have hkf := integrable_of_bdd_prob ρ (hk.mul hf)
  have hgkf := integrable_of_bdd_prob ρ ((hg.mul hk).mul hf)
  have e : ∀ x, (g x - a) * (k x - b) * (f x - c) =
      g x * k x * f x - c * (g x * k x) - b * (g x * f x) - a * (k x * f x) +
        (b * c) * g x + (a * c) * k x + (a * b) * f x + (-(a * b * c)) := fun x ↦ by ring
  unfold thirdCentral
  rw [← ha, ← hb, ← hc]
  simp_rw [e]
  have i1 : Integrable (fun x ↦ g x * k x * f x - c * (g x * k x)) ρ := hgkf.sub (hgk.const_mul c)
  have i2 : Integrable (fun x ↦ g x * k x * f x - c * (g x * k x) - b * (g x * f x)) ρ :=
    i1.sub (hgf.const_mul b)
  have i3 : Integrable (fun x ↦ g x * k x * f x - c * (g x * k x) - b * (g x * f x) -
      a * (k x * f x)) ρ := i2.sub (hkf.const_mul a)
  have i4 : Integrable (fun x ↦ g x * k x * f x - c * (g x * k x) - b * (g x * f x) -
      a * (k x * f x) + (b * c) * g x) ρ := i3.add (hg1.const_mul _)
  have i5 : Integrable (fun x ↦ g x * k x * f x - c * (g x * k x) - b * (g x * f x) -
      a * (k x * f x) + (b * c) * g x + (a * c) * k x) ρ := i4.add (hk1.const_mul _)
  have i6 : Integrable (fun x ↦ g x * k x * f x - c * (g x * k x) - b * (g x * f x) -
      a * (k x * f x) + (b * c) * g x + (a * c) * k x + (a * b) * f x) ρ :=
    i5.add (hf1.const_mul _)
  rw [integral_add i6 (integrable_const _), integral_add i5 (hf1.const_mul _),
    integral_add i4 (hk1.const_mul _), integral_add i3 (hg1.const_mul _),
    integral_sub i2 (hkf.const_mul a), integral_sub i1 (hgf.const_mul b),
    integral_sub hgkf (hgk.const_mul c), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  rw [← ha, ← hb, ← hc]
  ring

end Def

section Tilt

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- **The cubic response**: the covariance along an exponential tilt moves by the third central
mixed moment, `d/ds Cov_{ν_{sf}}(g, k) = E_{ν_{sf}}[(g − Eg)(k − Ek)(f − Ef)]`. -/
theorem hasDerivAt_lawCov_tilted {g k f : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hf : Bdd f)
    (s₀ : ℝ) :
    HasDerivAt (fun s ↦ lawCov (ν.tilted (fun x ↦ s * f x)) g k)
      (thirdCentral (ν.tilted (fun x ↦ s₀ * f x)) g k f) s₀ := by
  have hP : IsProbabilityMeasure (ν.tilted (fun x ↦ s₀ * f x)) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (Bdd.const_mul s₀ hf))
  have h1 := hasDerivAt_integral_tilted ν hf (hg.mul hk) s₀
  have h2 := hasDerivAt_integral_tilted ν hf hg s₀
  have h3 := hasDerivAt_integral_tilted ν hf hk s₀
  have h := h1.sub (h2.mul h3)
  unfold lawCov
  refine h.congr_deriv ?_
  rw [thirdCentral_eq _ hg hk hf]
  ring

/-- **The variance moves by the third cumulant**: `d/ds Var_{ν_{sf}} f = E_{ν_{sf}}[(f − Ef)³]`. -/
theorem hasDerivAt_var_tilted {f : X → ℝ} (hf : Bdd f) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ lawCov (ν.tilted (fun x ↦ s * f x)) f f)
      (∫ x, (f x - ∫ y, f y ∂ν.tilted (fun x ↦ s₀ * f x)) ^ 3 ∂ν.tilted (fun x ↦ s₀ * f x)) s₀ := by
  have h := hasDerivAt_lawCov_tilted ν hf hf hf s₀
  refine h.congr_deriv ?_
  unfold thirdCentral
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

variable {J : Type*} [Fintype J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) {h : X → ℝ} (hh : Bdd h)
include hS hh

omit [Fintype J] in
/-- **The susceptibility along the data path moves by the cubic response**:
`d/ds Cov_{D_s}(S_i, S_j) = thirdCentral D_s (S i) (S j) h` for `D_s = ν.tilted (s h)`. -/
theorem hasDerivAt_lawCov_dataPath (i j : J) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ lawCov (ν.tilted (fun x ↦ s * h x)) (S i) (S j))
      (thirdCentral (ν.tilted (fun x ↦ s₀ * h x)) (S i) (S j) h) s₀ :=
  hasDerivAt_lawCov_tilted ν (hS i) (hS j) hh s₀

/-- The susceptibility of visible contrasts along the data path. -/
theorem hasDerivAt_lawCov_dirLoss_dataPath (u v : J → ℝ) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ lawCov (ν.tilted (fun x ↦ s * h x)) (dirLoss S u) (dirLoss S v))
      (thirdCentral (ν.tilted (fun x ↦ s₀ * h x)) (dirLoss S u) (dirLoss S v) h) s₀ :=
  hasDerivAt_lawCov_tilted ν (bdd_dirLoss hS u) (bdd_dirLoss hS v) hh s₀

end Tilt

end Laplace.Multi
