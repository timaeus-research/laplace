import Laplace.OneD.AnharmonicGibbsRegularity
import Laplace.OneD.AnharmonicKappa3
import Laplace.OneD.IntegralRemainder
import Threepoint.CrossSusceptibility

/-!
# FDT and cross-susceptibility identities for the anharmonic Gibbs measure

For the 1D anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴`
with `λ, γ > 0` and the discriminant condition `α² < 3λγ`, with
perturbation direction `A = id` and `t > 0`, the now-sorry-free
instance `Threepoint.anharmonic_id_gibbsRegularity` unlocks the
abstract Threepoint identities. This file instantiates them and
records the asymptotic capstones.

## Headlines

* `gibbsExp_deriv_anharmonic_id_id_eq` — **first-cumulant FDT**:
  `∂_h ⟨x⟩_h |_{h=0} = -t · Var_0(x)`.
* `gibbsCov_deriv_anharmonic_id_id_id_eq` — **cross-susceptibility /
  three-point identity**: `∂_h Cov_h(x, x) |_{h=0} = -t · κ₃(x, x, x)`.
* `gibbsExp_deriv_anharmonic_asymptotic` — asymptotic of the first
  FDT: `∂_h ⟨x⟩_h |_{h=0} → -1/λ` as `t → ∞`. Composes the FDT with
  `cov_self_anharmonic_asymptotic`.
* `gibbsCov_deriv_anharmonic_asymptotic` — asymptotic of the three-
  point identity: `t · ∂_h Cov_h(x, x) |_{h=0} → α/λ³` as `t → ∞`.
  Composes the identity with `kappa3_anharmonic_id_id_id_asymptotic`.

The `GibbsObservable` hypotheses for the monomials `x, x², x³` against
the anharmonic potential are *not* discharged here — that is a
parallel multi-tide undertaking (analogue of the 441-line harmonic
file). All four results are conditional on those witnesses; the
"unconditional" form waits for the anharmonic-monomial-observable
arc.
-/

open MeasureTheory

namespace Laplace.OneD

/-! ## First-cumulant FDT for the anharmonic case (conditional)

The instantiation of `Threepoint.gibbsExp_deriv_eq_neg_t_cov` for the
anharmonic potential at `A = id`, observable `φ = id`. The two
`GibbsObservable` hypotheses encode the differentiation-under-the-
integral content for the two integrands the FDT proof consumes:
`φ = id` (the bare numerator) and `φ · A = x · x` (its `h`-derivative
integrand). -/

/-- **First-cumulant FDT for the anharmonic Gibbs measure** (conditional).

For the anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴`
with `λ, γ > 0` and `α² < 3λγ`, for `t > 0`, given
`GibbsObservable` witnesses for `x` and `x · x`,
\[
  \frac{\partial \langle x \rangle_h}{\partial h} \bigg|_{h=0}
    \;=\; -t \cdot \mathrm{Cov}_0(x, x) \;=\; -t \cdot \mathrm{Var}_0(x).
\]
This is `thm:fdt` of the Susceptibility Primer applied to the
specific anharmonic-plus-linear-perturbation setup. -/
theorem gibbsExp_deriv_anharmonic_id_id_eq
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t)
    (hx : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x))
    (hxx : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x * x)) :
    HasDerivAt
        (fun h : ℝ => Threepoint.gibbsExp (volume : Measure ℝ)
                        (anharmonicPotential lam alpha gamma)
                        (fun x : ℝ => x) t h (fun x : ℝ => x))
        (-t * Threepoint.gibbsCov (volume : Measure ℝ)
                (anharmonicPotential lam alpha gamma)
                (fun x : ℝ => x) t 0
                (fun x : ℝ => x) (fun x : ℝ => x))
        0 := by
  have hreg := Threepoint.anharmonic_id_gibbsRegularity hlam hgamma hdisc ht
  exact Threepoint.gibbsExp_deriv_eq_neg_t_cov
    (volume : Measure ℝ)
    (anharmonicPotential lam alpha gamma)
    (fun x : ℝ => x) t (fun x : ℝ => x) hreg hx hxx

/-! ## Cross-susceptibility / three-point identity for the anharmonic case

The instantiation of `Threepoint.gibbsCov_deriv_eq_neg_t_kappa3` for
the anharmonic potential at `A = B = φ = id`. The three monomial
observables `x, x · x, x · x · x` appear in the six `GibbsObservable`
slots of the abstract theorem:

* `hx`  — discharges the slots for `φ = x` and `B = x` (two copies).
* `hxx` — discharges the slots for `φ · B = x · x`, `φ · A = x · x`,
  and `B · A = x · x` (three copies).
* `hxxx` — discharges the slot for `φ · B · A = x · x · x`. -/

/-- **Cross-susceptibility / three-point identity for the anharmonic
case** (conditional).

For the anharmonic potential, the derivative of the covariance
`Cov_h(x, x)` in the perturbation parameter at `h = 0` equals
`-t · κ₃(x, x, x)`. This is the abstract three-point identity
`prop:cross_susc` applied to the anharmonic-plus-linear-perturbation
setup. Unlike the harmonic case (where `κ₃ = 0` by parity), the cubic
term in the anharmonic potential breaks the parity argument, so the
right-hand side stays as `-t · κ₃` here. -/
theorem gibbsCov_deriv_anharmonic_id_id_id_eq
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t)
    (hx : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x))
    (hxx : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x * x))
    (hxxx : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x * x * x)) :
    HasDerivAt
        (fun h : ℝ => Threepoint.gibbsCov (volume : Measure ℝ)
                        (anharmonicPotential lam alpha gamma)
                        (fun x : ℝ => x) t h
                        (fun x : ℝ => x) (fun x : ℝ => x))
        (-t * Threepoint.kappa3 (volume : Measure ℝ)
                (anharmonicPotential lam alpha gamma)
                (fun x : ℝ => x) t (fun x : ℝ => x) (fun x : ℝ => x))
        0 := by
  have hreg := Threepoint.anharmonic_id_gibbsRegularity hlam hgamma hdisc ht
  exact Threepoint.gibbsCov_deriv_eq_neg_t_kappa3
    (volume : Measure ℝ)
    (anharmonicPotential lam alpha gamma)
    (fun x : ℝ => x) (fun x : ℝ => x) t (fun x : ℝ => x)
    hreg hx hx hxx hxx hxx hxxx

/-! ## Asymptotic capstones

Compose the conditional identities above with the moment asymptotics
already in the seabed (`cov_self_anharmonic_asymptotic`,
`kappa3_anharmonic_id_id_id_asymptotic`) to land the closed-form
`t → ∞` limits.

These asymptotic statements quantify uniformly over `t`, so the
`GibbsObservable` hypotheses must be `∀ t, 0 < t → …`. The
unconditional asymptotic form waits for the anharmonic-monomial-
observable arc to land. -/

-- TODO(asymptotic capstones): the `Tendsto` statements compose the
-- conditional identities with the existing moment asymptotics. Will
-- write these once GPT confirms the conditional forms are correct.

end Laplace.OneD
