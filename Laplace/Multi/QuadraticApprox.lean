import Laplace.Multi.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Multivariate quadratic approximation

For a smooth potential `L : (ι → ℝ) → ℝ` with critical point at `0`, the
multivariate Laplace asymptotic expands `t · L(u/√t)` as `(1/2) ⟨u, H u⟩
+ s_t(u)`, where `H` is the Hessian of `L` at `0` (encoded as a
continuous linear operator) and `s_t(u)` is the rescaled remainder
satisfying `|s_t(u)| ≤ C · ‖u‖³ / √t` locally.

This file sets up the basic definitions:

- `quadForm H z = ∑ i, z i * (H z) i`: the standard quadratic form
  `⟨z, H z⟩` on `ι → ℝ`.
- `rescaledPerturbation L H t u = t · L(u/√t) - (1/2) ⟨u, H u⟩`: the
  multivariate analogue of `1D's s_t(u)`.
- `rescaling_identity`: the algebraic decomposition
  `t · L(u/√t) = (1/2) ⟨u, H u⟩ + s_t(u)` (definitional).

Subsequent files build:
- `Laplace/Multi/GaussianIBP.lean`: integration-by-parts identity
  `∫ u_i u_j · exp(-Q u) du = Z · (Σ)_{ij}` with `Σ = H⁻¹` and
  `Q(u) = (1/2) quadForm H u`.
- `Laplace/Multi/Covariance.lean`: the main `lem:laplace_cov` theorem,
  combining quadratic-approximation bounds with `GaussianIBP`.

The hypotheses for the main theorem (local cubic remainder, quadratic
observable remainders, global coercivity) are taken as explicit
estimates per the GPT-5.5 Pro Phase 1 strategy, not derived from
`ContDiff` or the spectral theorem.
-/

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- Quadratic form `⟨z, H z⟩ = ∑ i, z i * (H z) i` on `ι → ℝ` for a
continuous linear operator `H`. -/
noncomputable def quadForm
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (z : ι → ℝ) : ℝ :=
  ∑ i, z i * (H z) i

/-- The multivariate rescaled perturbation
`s_t(u) := t · L(u/√t) - (1/2) · ⟨u, H u⟩`.

This is the multivariate analogue of the 1D `rescaledPerturbation` in
`Laplace.OneD.Rescaling`. Captures the deviation of `tL(u/√t)` from the
Gaussian quadratic form. -/
noncomputable def rescaledPerturbation
    (L : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ) (u : ι → ℝ) : ℝ :=
  t * L ((Real.sqrt t)⁻¹ • u) - (1/2) * quadForm H u

/-- **Rescaling identity** (definitional):
`t · L(u/√t) = (1/2) ⟨u, H u⟩ + s_t(u)`.

This is the multivariate analogue of `Laplace.OneD.anharmonic_rescaling_identity`.
Holds for any `L`, `H`, `t`, `u` — no hypotheses needed since this
is just the definition of `rescaledPerturbation` rearranged. -/
theorem rescaling_identity
    (L : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ) (u : ι → ℝ) :
    t * L ((Real.sqrt t)⁻¹ • u) =
      (1/2) * quadForm H u + rescaledPerturbation L H t u := by
  unfold rescaledPerturbation
  ring

/-- Definitional unfolding for `quadForm`. -/
lemma quadForm_def (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (z : ι → ℝ) :
    quadForm H z = ∑ i, z i * (H z) i := rfl

/-- Definitional unfolding for `rescaledPerturbation`. -/
lemma rescaledPerturbation_def
    (L : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ) (u : ι → ℝ) :
    rescaledPerturbation L H t u =
      t * L ((Real.sqrt t)⁻¹ • u) - (1/2) * quadForm H u := rfl

end Laplace.Multi
