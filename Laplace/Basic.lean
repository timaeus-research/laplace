import Mathlib

/-!
# Laplace asymptotic expansions and Wick contractions

Formalisation of Laplace asymptotic expansions of integrals against the Gibbs
measure `exp(-tL(w)) dw`, following the SLT Susceptibility Primer
(Baker et al. 2025).

## Roadmap

* `Laplace.OneD.GaussianMoments` — moments of the centred 1D Gaussian
  via integration by parts: `∫ x^(2k) e^{-x²/2}/√(2π) dx = (2k-1)!!`.
* `Laplace.OneD.Anharmonic` — for the anharmonic potential
  `L(w) = (λ/2)w² + (α/6)w³`, prove
  `Cov_t[w², w] = -2α/(λ³ t²) + o(t⁻²)`.
* `Laplace.MultiD.LaplaceCov` — multivariate `Cov_t[φ,ψ] = (1/t) ⟨∇φ, Σ ∇ψ⟩ + O(t⁻²)`.
-/

namespace Laplace

end Laplace
