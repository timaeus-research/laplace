/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Multi.CovKClosedForm

/-!
# The primer's next-to-leading covariance formula (eq. `primer_nlo`)

For a regular potential `V` with Hessian `P ≻ 0` at the minimiser and third-derivative tensor `T`,
and an observable `ψ` with gradient `g` and exact Hessian `A` at the minimiser, the seabed's
second-order covariance rate (`covV_first_order_rate_posDef`) reads

  `t² Cov_t(V, ψ) = ½ tr(A Σ) − ½ (Σ g)ᵀ (T : Σ) + O(1/t)`,   `Σ = P⁻¹`.

The note's eq. `primer_nlo` is this statement for the centred perturbation `ψ = ℓᵢ − Lₙ`, whose
Hessian is `Bᵢ − H`: with `tr(HΣ) = d` the bracket becomes `½[tr(BᵢΣ) − d] − ½ (Σgᵢ)ᵀ(T:Σ)`
(`primer_nlo_centered`). The uncentred form `Cov_t(K, ℓᵢ)` is `covV_first_order_rate_posDef`
itself, and the difference `Var_t(K) = d/2t² + O(t⁻³)` is `varV_first_order_rate_posDef`.
-/

namespace Laplace.Patterning

open Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trASig_sub (A A' Sig : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    trASig (A - A') Sig = trASig A Sig - trASig A' Sig := by
  simp [trASig, Finset.sum_sub_distrib]

/-- **Eq. `primer_nlo`.** For the centred perturbation with Hessian `B − H` and gradient `g`,
`t² Cov_t(K, ψ) → ½[tr(BΣ) − d] − ½ (Σg)ᵀ(T:Σ)` at rate `O(1/t)`. -/
theorem primer_nlo_centered [Nonempty ι] (V ψ : (ι → ℝ) → ℝ) {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (g : ι → ℝ) (hV : PotentialQuinticApprox V (matCLM P)) (hψ : ObservableTensorApprox ψ g)
    (B : (ι → ℝ) →L[ℝ] (ι → ℝ)) (hB : hψ.A = B - matCLM P) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * Multi.gibbsCov V t V ψ -
          ((1 / 2 : ℝ) * (trASig B (matCLM P⁻¹) - Fintype.card ι) -
            (1 / 2 : ℝ) * dot (matCLM P⁻¹ g) (tensorContractMatrix hV.T (matCLM P⁻¹)))| ≤
        K / t := by
  have h := covV_first_order_rate_posDef V ψ hP g hV hψ
  rwa [hB, trASig_sub, trASig_matCLM_inv hP] at h

end Laplace.Patterning
