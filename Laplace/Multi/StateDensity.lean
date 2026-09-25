/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ThermoLengthAsymptotic

/-!
# The state-density reduction of the featureless line

On the featureless (loss-neutral) line everything depends only on the **law of the loss** under the
prior, `ν = L_*(π μ)` (`lossLaw`, the state density). The partition function is its Laplace
transform, the posterior expectation of any function of the loss is its expectation under the
tilted law `ν_u ∝ e^{-uℓ} ν` (`lawExp`), and the radial Fisher speed is `u² Var_{ν_u}(ℓ)`
(`lawVar`):

  `priorZ μ π L u = ∫ e^{-uℓ} dν`                       (`priorZ_eq_lossLaw`),
  `⟨f(L)⟩_u = lawExp ν f u`                              (`priorExp_comp_eq_lawExp`),
  `Var_u(L) = lawVar ν u`                                (`priorCov_self_eq_lawVar`),

so the thermodynamic length of the featureless line, the **radial response length**
`radialLength μ π L t = ∫₀ᵗ √Var_u(L) du` (`thermoLength_neutral_eq_radialLength`), is a functional
of the loss law alone (`radialLength_eq_lawLength`, `thermoLength_neutral_eq_of_lossLaw_eq`): two
models with the same state density have the same featureless-line geometry. The singularity of the
state density at the minimum loss is what carries Watanabe's `(λ, m)` (Astra, round 25, item 2).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **The state density**: the law of the loss under the prior `π·μ`. -/
noncomputable def lossLaw (μ : Measure X) (π L : X → ℝ) : Measure ℝ :=
  (μ.withDensity fun x ↦ ENNReal.ofReal (π x)).map L

/-- Expectation of `f` under the tilted loss law `e^{-uℓ} ν`. -/
noncomputable def lawExp (ν : Measure ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  (∫ ℓ, f ℓ * Real.exp (-(u * ℓ)) ∂ν) / ∫ ℓ, Real.exp (-(u * ℓ)) ∂ν

/-- The variance of the loss under the tilted loss law. -/
noncomputable def lawVar (ν : Measure ℝ) (u : ℝ) : ℝ :=
  lawExp ν (fun ℓ ↦ ℓ * ℓ) u - lawExp ν (fun ℓ ↦ ℓ) u ^ 2

/-- The radial response length of a loss law: `∫₀ᵗ √Var_{ν_u}(ℓ) du`. -/
noncomputable def lawLength (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, Real.sqrt (lawVar ν u)

/-- The radial response length of a model: the thermodynamic length of its featureless line. -/
noncomputable def radialLength (μ : Measure X) (π L : X → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, Real.sqrt (priorCov μ π L L L u)

/-- Integrals against the state density are prior integrals of functions of the loss. -/
theorem integral_lossLaw {π L : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x)
    (hL : Measurable L) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ ℓ, g ℓ ∂(lossLaw μ π L) = ∫ x, g (L x) * π x ∂μ := by
  unfold lossLaw
  rw [integral_map hL.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hπm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top) (fun x ↦ g (L x))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [ENNReal.toReal_ofReal (hπ x), smul_eq_mul]
  ring

/-- **The partition function is the Laplace transform of the state density.** -/
theorem priorZ_eq_lossLaw {π L : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x)
    (hL : Measurable L) (u : ℝ) :
    priorZ μ π L u = ∫ ℓ, Real.exp (-(u * ℓ)) ∂(lossLaw μ π L) := by
  rw [integral_lossLaw hπm hπ hL (by fun_prop)]
  rfl

/-- **Posterior expectations of functions of the loss are tilted-law expectations.** -/
theorem priorExp_comp_eq_lawExp {π L : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x)
    (hL : Measurable L) {f : ℝ → ℝ} (hf : Measurable f) (u : ℝ) :
    priorExp μ π L (fun x ↦ f (L x)) u = lawExp (lossLaw μ π L) f u := by
  unfold priorExp lawExp
  rw [priorZ_eq_lossLaw hπm hπ hL,
    integral_lossLaw hπm hπ hL (g := fun ℓ ↦ f ℓ * Real.exp (-(u * ℓ))) (hf.mul (by fun_prop))]

/-- **The radial variance is the variance of the tilted loss law.** -/
theorem priorCov_self_eq_lawVar {π L : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x)
    (hL : Measurable L) (u : ℝ) :
    priorCov μ π L L L u = lawVar (lossLaw μ π L) u := by
  unfold priorCov lawVar
  rw [← priorExp_comp_eq_lawExp hπm hπ hL (f := fun ℓ ↦ ℓ * ℓ) (by fun_prop) u,
    ← priorExp_comp_eq_lawExp hπm hπ hL (f := fun ℓ ↦ ℓ) measurable_id u, sq]

/-- Posterior expectations are invariant under adding a constant to the loss. -/
theorem priorExp_const_add (π L φ : X → ℝ) (c u : ℝ) :
    priorExp μ π (fun x ↦ c + L x) φ u = priorExp μ π L φ u := by
  unfold priorExp priorZ
  have e1 : (∫ x, φ x * Real.exp (-(u * (c + L x))) * π x ∂μ) =
      Real.exp (-(u * c)) * ∫ x, φ x * Real.exp (-(u * L x)) * π x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [show -(u * (c + L x)) = -(u * c) + -(u * L x) by ring, Real.exp_add]
    ring
  have e2 : (∫ x, Real.exp (-(u * (c + L x))) * π x ∂μ) =
      Real.exp (-(u * c)) * ∫ x, Real.exp (-(u * L x)) * π x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [show -(u * (c + L x)) = -(u * c) + -(u * L x) by ring, Real.exp_add]
    ring
  rw [e1, e2, mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- Posterior covariances are invariant under adding a constant to the loss. -/
theorem priorCov_const_add (π L φ ψ : X → ℝ) (c u : ℝ) :
    priorCov μ π (fun x ↦ c + L x) φ ψ u = priorCov μ π L φ ψ u := by
  unfold priorCov
  rw [priorExp_const_add, priorExp_const_add, priorExp_const_add]

/-- The thermodynamic length of the featureless line is the radial response length. -/
theorem thermoLength_neutral_eq_radialLength (π L : X → ℝ) (c : ℝ) {t : ℝ} (ht : 0 < t) :
    thermoLength μ π (pathLoss (fun _ ↦ c) L) (fun _ ↦ L) t = radialLength μ π L t := by
  rw [thermoLength_neutral_eq π L c ht]
  unfold radialLength
  simp only [priorCov_const_add]

/-- **The radial response length is a functional of the state density.** -/
theorem radialLength_eq_lawLength {π L : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x)
    (hL : Measurable L) (t : ℝ) :
    radialLength μ π L t = lawLength (lossLaw μ π L) t := by
  unfold radialLength lawLength
  simp only [priorCov_self_eq_lawVar hπm hπ hL]

/-- **Models with the same state density have the same featureless-line geometry.** -/
theorem thermoLength_neutral_eq_of_lossLaw_eq {Y : Type*} [MeasurableSpace Y] {μ' : Measure Y}
    {π L : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x) (hL : Measurable L)
    {π' L' : Y → ℝ} (hπm' : Measurable π') (hπ' : ∀ y, 0 ≤ π' y) (hL' : Measurable L')
    (h : lossLaw μ π L = lossLaw μ' π' L') (c c' : ℝ) {t : ℝ} (ht : 0 < t) :
    thermoLength μ π (pathLoss (fun _ ↦ c) L) (fun _ ↦ L) t =
      thermoLength μ' π' (pathLoss (fun _ ↦ c') L') (fun _ ↦ L') t := by
  rw [thermoLength_neutral_eq_radialLength π L c ht,
    thermoLength_neutral_eq_radialLength π' L' c' ht, radialLength_eq_lawLength hπm hπ hL,
    radialLength_eq_lawLength hπm' hπ' hL', h]

end Laplace.Multi
