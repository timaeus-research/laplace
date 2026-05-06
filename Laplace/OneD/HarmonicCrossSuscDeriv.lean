import Laplace.OneD.HarmonicGibbsRegularity
import Threepoint.Harmonic

/-!
# Cross-susceptibility derivative vanishes for the harmonic Gibbs

The Tide 10 capstone, composing two prior tides into a downstream
theorem neither delivers alone:

* **Tide 5** (`Threepoint.kappa3_harmonic_id_id_id_eq_zero`) — for the
  harmonic Gibbs `L = (λ/2) x²` with linear perturbation `A = x`,
  `kappa3 (volume) ((λ/2)·²) (id) t (id) (id) = 0`.
* **Tide 10** (`Threepoint.harmonic_id_gibbsRegularity`) — concrete
  `GibbsRegularity` instance for the same setup.
* **Cross-susceptibility identity** (Tide 6 / `gibbsCov_deriv_eq_neg_t_kappa3`)
  — `∂_h Cov_h(φ, B) = -t · κ₃(φ, A, B)` at `h = 0`.

Combined: at the harmonic + linear setup with `(φ, B) = (id, id)`,
`∂_h Cov_h(x, x) |_{h=0} = -t · κ₃(x, x, x) = 0`. The three
`GibbsObservable` hypotheses for the monomials `x`, `x*x`, `x*x*x`
remain external; closing those is candidate G4 of the May 6 survey.

The theorem is sharper than its statement suggests. By the closed form
of the perturbed partition function (square completion: the perturbed
Gibbs is a shifted Gaussian centred at `-h/λ` with variance `1/(λt)`),
`Cov_h(x, x) = 1/(λt)` is in fact independent of `h` — *not just*
locally constant at `h = 0`. The κ₃-route here delivers only the
basepoint version of this fact; a stronger global-constancy theorem is
recorded as a future tide candidate.

## Tide-step provenance

Tide step 11 (Candidate G1 from the 6 May candidates survey),
formalised on `tide/cross-susc-deriv-harmonic` in laplace, branched off
`main` (commit `1e3802a`). See
`sri/projects/patterning/tide-log/2026-05-06-tide-cross-susc-deriv-harmonic.md`.
-/

open MeasureTheory

namespace Laplace.OneD

/-- **Cross-susceptibility derivative vanishes for the harmonic Gibbs.**

For the harmonic Gibbs measure `μ_t,h(x) ∝ exp(-t((λ/2)x² + h·x))` on
`ℝ` against Lebesgue, with `λ, t > 0`, the covariance
`Cov_h(x, x)` has zero derivative at `h = 0`. Equivalently, the
cross-susceptibility derivative `∂_h Cov_h(x, x) |_{h=0}` is zero —
which is the FDT-style derivative `-t · κ₃(x, x, x)` evaluated using
Tide 5's parity-based vanishing of `κ₃` at the harmonic potential.

The three `GibbsObservable` hypotheses encode the differentiation-under-
the-integral-sign content for the three observables `x`, `x²`, and
`x³` against the perturbed Boltzmann factor. They are *external* to
this theorem: the structural composition that gives the conclusion is
self-contained, but the analytic content for the monomials is candidate
G4 from the May 6 survey and not formalised here. -/
theorem cov_h_id_id_deriv_harmonic_eq_zero
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (hx : Threepoint.GibbsObservable (volume : Measure ℝ)
            (fun x : ℝ => lam / 2 * x ^ 2) (fun x : ℝ => x) t (fun x : ℝ => x))
    (hx2 : Threepoint.GibbsObservable (volume : Measure ℝ)
            (fun x : ℝ => lam / 2 * x ^ 2) (fun x : ℝ => x) t
            (fun x : ℝ => x * x))
    (hx3 : Threepoint.GibbsObservable (volume : Measure ℝ)
            (fun x : ℝ => lam / 2 * x ^ 2) (fun x : ℝ => x) t
            (fun x : ℝ => x * x * x)) :
    HasDerivAt
        (fun h : ℝ => Threepoint.gibbsCov (volume : Measure ℝ)
                        (fun x : ℝ => lam / 2 * x ^ 2)
                        (fun x : ℝ => x) t h
                        (fun x : ℝ => x) (fun x : ℝ => x))
        0 0 := by
  have hreg := Threepoint.harmonic_id_gibbsRegularity hlam ht
  have hderiv := Threepoint.gibbsCov_deriv_eq_neg_t_kappa3
    (volume : Measure ℝ)
    (fun x : ℝ => lam / 2 * x ^ 2)  -- L
    (fun x : ℝ => x)                -- A
    (fun x : ℝ => x)                -- B
    t
    (fun x : ℝ => x)                -- φ
    hreg hx hx hx2 hx2 hx2 hx3
  -- `kappa3 ... (id) (id) = 0` by Tide 5; `(-t) * 0 = 0`.
  rw [Threepoint.kappa3_harmonic_id_id_id_eq_zero hlam ht, mul_zero] at hderiv
  exact hderiv

end Laplace.OneD
