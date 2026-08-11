-- `import Mathlib` FIRST: comparator compares the *elaborated* statement
-- types structurally, and instance-search order is import-order-dependent.
-- Importing Mathlib first pins its linearization to match Statements.lean's.
import Mathlib
import Laplace

/-!
# The main theorems: proofs

The theorems of `Statements.lean`, restated verbatim together with the
definitions they use, and proved by delegation to the corresponding library
theorems.

Do not import `Statements` here: the two files declare the same names.

Coverage (transitive import closure of the delegated library theorems,
measured with the tide-distill closure report): 26 of 68 library files,
37,939 of 46,367 lines — 82% of the library by lines. The main areas not
represented: the harmonic-oscillator track (`OneD/Harmonic*`), the 1D
cumulant/log-partition ladder (`OneD/AnharmonicCumulants*`,
`OneD/AnharmonicPartition*`, `OneD/AnharmonicSusceptibilityGeneralH`), the
bounded-prior track (`OneD/QuarticBoundedPrior*`), and the fixed-instance 2D
quartic–sextic files subsumed by the generic `kth`–`kth` family.
-/

namespace Laplace.Statements

open MeasureTheory Filter Asymptotics


/-! ## One-dimensional Gibbs vocabulary

The Gibbs measure at inverse temperature `t` for a potential `L : ℝ → ℝ` is
`p_t(x) ∝ exp(-t·L(x))` against Lebesgue measure. -/

/-- Partition function `Z(t) = ∫ exp(-t · L(x)) dx` on `ℝ`. -/
noncomputable def partitionFunction (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-(t * L x))

/-- Gibbs expectation `⟨φ⟩_t = (1/Z(t)) · ∫ φ(x) exp(-t L(x)) dx` on `ℝ`. -/
noncomputable def gibbsExpectation (L : ℝ → ℝ) (t : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ, φ x * Real.exp (-(t * L x))) / partitionFunction L t

/-- Gibbs covariance `Cov_t[φ, ψ] = ⟨φψ⟩_t - ⟨φ⟩_t ⟨ψ⟩_t` on `ℝ`. -/
noncomputable def gibbsCov (L : ℝ → ℝ) (t : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  gibbsExpectation L t (fun x => φ x * ψ x)
    - gibbsExpectation L t φ * gibbsExpectation L t ψ

/-- The 1D anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴`. -/
noncomputable def anharmonicPotential (lam alpha gamma : ℝ) : ℝ → ℝ :=
  fun x => lam / 2 * x ^ 2 + alpha / 6 * x ^ 3 + gamma / 24 * x ^ 4

/-! ## Field-perturbed (three-point) vocabulary

The perturbed Gibbs measure `p^h_t(x) ∝ exp(-t·(L(x) + h·A(x)))` couples an
external field `h` to a perturbing observable `A`; susceptibilities are
`h`-derivatives at `h = 0`. The source's reference measure (a prior `φ(w)`
times Lebesgue) is specialised to Lebesgue itself (`π = 1`), matching the
primer's convention for the anharmonic model. -/

/-- Expectation of `φ` under the perturbed Gibbs measure
`p^h_t(x) ∝ exp(-t (L + h·A)(x))` on `ℝ`. -/
noncomputable def perturbedExpectation (L A : ℝ → ℝ) (t h : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ, φ x * Real.exp (-(t * (L x + h * A x))))
    / (∫ x : ℝ, Real.exp (-(t * (L x + h * A x))))

/-- Covariance under the perturbed Gibbs measure. -/
noncomputable def perturbedCov (L A : ℝ → ℝ) (t h : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  perturbedExpectation L A t h (fun x => φ x * ψ x)
    - perturbedExpectation L A t h φ * perturbedExpectation L A t h ψ

/-- Third cumulant of `(φ, A, B)` under the unperturbed (`h = 0`) Gibbs
measure:
`κ₃(φ, A, B) = ⟨φAB⟩ - ⟨φA⟩⟨B⟩ - ⟨φB⟩⟨A⟩ - ⟨AB⟩⟨φ⟩ + 2⟨φ⟩⟨A⟩⟨B⟩`. -/
noncomputable def thirdCumulant (L A : ℝ → ℝ) (t : ℝ) (φ B : ℝ → ℝ) : ℝ :=
  perturbedExpectation L A t 0 (fun x => φ x * A x * B x)
    - perturbedExpectation L A t 0 (fun x => φ x * A x)
      * perturbedExpectation L A t 0 B
    - perturbedExpectation L A t 0 (fun x => φ x * B x)
      * perturbedExpectation L A t 0 A
    - perturbedExpectation L A t 0 (fun x => A x * B x)
      * perturbedExpectation L A t 0 φ
    + 2 * perturbedExpectation L A t 0 φ * perturbedExpectation L A t 0 A
      * perturbedExpectation L A t 0 B

/-! ## Two-dimensional Gibbs vocabulary (degenerate separable potentials) -/

/-- Partition function of the 2D Gibbs measure `exp(-t · L(z)) dz` on `ℝ × ℝ`. -/
noncomputable def partitionFunction2D (L : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, Real.exp (-(t * L z))

/-- Gibbs expectation `⟨φ⟩_t = (1/Z(t)) · ∫ φ(z) exp(-t L(z)) dz` on `ℝ × ℝ`. -/
noncomputable def gibbsExpectation2D (L : ℝ × ℝ → ℝ) (t : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  (∫ z : ℝ × ℝ, φ z * Real.exp (-(t * L z))) / partitionFunction2D L t

/-- The degenerate even monomial potential `U_k(x) = x^(2k)/(2k)!` (a
non-quadratic minimum at the origin for `k ≥ 2`). -/
noncomputable def kthPotential (k : ℕ) : ℝ → ℝ :=
  fun x => x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)

/-- The additively-separable 2D potential `L(x, y) = U(x) + V(y)`. -/
noncomputable def addSeparable (U V : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun z => U z.1 + V z.2

/-- The exact constant in the 2D kth-kth mixed-even-moment power law:
`C(k₁,k₂,j₁,j₂) = ((2k₁)!)^(j₁/k₁) · ((2k₂)!)^(j₂/k₂) ·
(Γ((2j₁+1)/(2k₁))/Γ(1/(2k₁))) · (Γ((2j₂+1)/(2k₂))/Γ(1/(2k₂)))`. -/
noncomputable def kthKthMomentConst (k₁ k₂ j₁ j₂ : ℕ) : ℝ :=
  ((Nat.factorial (2 * k₁) : ℝ)) ^ ((j₁ : ℝ) / (k₁ : ℝ)) *
  ((Nat.factorial (2 * k₂) : ℝ)) ^ ((j₂ : ℝ) / (k₂ : ℝ)) *
  (Real.Gamma ((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) /
    Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ))) *
  (Real.Gamma ((2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) /
    Real.Gamma ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))

/-! ## Multivariate vocabulary

The multivariate Gibbs objects (`Multi.partitionFunction`,
`Multi.gibbsExpectation`, `Multi.gibbsCov` over `ι → ℝ`), the Gaussian data
(`Multi.quadForm`, `Multi.gaussianWeight`, `Multi.gaussianZ`, `Multi.dot`,
`Multi.trASig`, `Multi.tensorContractMatrix`) and the analytic hypothesis
packages (`Multi.PotentialJetApprox`, `Multi.ObservableJetApprox`,
`Multi.LaplaceCovHypotheses`, `Multi.PotentialQuinticApprox`,
`Multi.ObservableTensorApprox`, `Multi.LaplaceCov4MomentHypotheses`,
`Multi.LaplaceCov6MomentHypotheses`, …) are imported from
`Laplace/Multi/Defs.lean`, which has a Mathlib-only import closure. -/

/-- **The connected `t⁻²` covariance coefficient** of `lem:laplace_cov2`,
as a function of the observable Hessian `A = ∇²φ(0)`, the observable cubic
tensor `Φ = ∇³φ(0)`, the second observable's Hessian `B = ∇²ψ(0)` and
gradient `b = ∇ψ(0)`, the potential cubic tensor `T = ∇³V(0)`, and the
inverse Hessian `Σ = Hinv`:
`½·tr(AΣBΣ) + ½·(Σb)·(Φ:Σ) - ½·b^⊤ΣAΣ(T:Σ) - ½·(Σb)·(T:(ΣAΣ))`.

(`Multi.tensorContractMatrix T M` reads its matrix argument in transposed
orientation, `(T:M)ᵢ = ∑ⱼₖ Tᵢⱼₖ Mₖⱼ`; the matrices contracted here — `Σ` and
`ΣAΣ` — are symmetric under the symmetry hypotheses in force, so this agrees
with the source's `(T:M)ᵢ = ∑ⱼₖ Tᵢⱼₖ Mⱼₖ`.) -/
noncomputable def cov2Coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (B : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * Multi.trASig (A.comp ((Hinv).comp (B.comp Hinv)))
      (1 : (ι → ℝ) →L[ℝ] (ι → ℝ))
    + (1 / 2 : ℝ) * Multi.dot (Hinv b) (Multi.tensorContractMatrix Φ Hinv)
    - (1 / 2 : ℝ) * Multi.dot b (Hinv (A (Hinv (Multi.tensorContractMatrix T Hinv))))
    - (1 / 2 : ℝ) * Multi.dot (Hinv b)
        (Multi.tensorContractMatrix T (Hinv.comp (A.comp Hinv)))

/-! ## The theorems -/

/-- **1D anharmonic covariance asymptotic** (`t⁻²` order).

For the anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` with
`λ, γ > 0` and discriminant condition `α² < 3λγ` (so `L` has a unique global
minimum at `0`),
\[ t^2 \cdot \mathrm{Cov}_t[x^2, x] \longrightarrow -\tfrac{2\alpha}{\lambda^3}
   \quad (t \to \infty), \]
i.e. `Cov_t[x², x] = -2α/(λ³t²) + o(t⁻²)`.

Source: Elliott & Murfet (2026), *The Susceptibility Primer*, §4.1
("Susceptibilities probe geometry — the regular case"), the display
`eq:cov_anharmonic_1d` ((4.10) in the compiled primer) — the 1D example of
Lemma `lem:laplace_cov2`.
**Deviation from the source:** the primer asserts the rate
`Cov_t[x², x] = -2α/(λ³t²) + O(t⁻³)`; this statement pins only the limit
(`o(t⁻²)` remainder) — the `O(t⁻¹)`-rate strengthening of `t²·Cov_t[x², x]`
is not formalised for this observable pair (the library has rate forms for
`Cov_t[x, x]` and `⟨x⟩_t`). -/
theorem cov_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ => t ^ 2 * gibbsCov
        (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2) (fun x => x)) Filter.atTop
      (nhds (-2 * alpha / lam ^ 3)) :=
  Laplace.OneD.cov_anharmonic_asymptotic hlam hgamma hdisc

/-- **1D anharmonic third-cumulant asymptotic.**

For the anharmonic potential as above, perturbing observable `A = x` and
observables `φ = B = x`,
\[ t^2 \cdot \kappa_3(x, x, x) \longrightarrow -\tfrac{\alpha}{\lambda^3}
   \quad (t \to \infty). \]

Source: the three-point function of Murfet (2026), *From Clusters to
Circuits: Higher-Order Susceptibilities in Language Models* (the `κ₃` of
Corollary `prop:cross_susc`), evaluated on the anharmonic model of the Susceptibility
Primer §4.1. **The asymptotic value `-α/λ³` is this repository's
contribution** (it follows the primer's Laplace calculus but is not displayed
in either source). -/
theorem kappa3_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto
      (fun t : ℝ => t ^ 2 * thirdCumulant
          (anharmonicPotential lam alpha gamma)
          (fun x : ℝ => x) t (fun x : ℝ => x) (fun x : ℝ => x))
      Filter.atTop
      (nhds (-alpha / lam ^ 3)) :=
  Laplace.OneD.kappa3_anharmonic_id_id_id_asymptotic hlam hgamma hdisc

/-- **1D anharmonic cross-susceptibility (FDT) asymptotic.**

Perturb the anharmonic Gibbs measure by an external field `h` coupled to
`A = x`, and differentiate the self-covariance in `h` at `h = 0`:
\[ t \cdot \frac{\partial}{\partial h}\Big|_{h=0}
   \mathrm{Cov}^h_t(x, x) \longrightarrow \tfrac{\alpha}{\lambda^3}
   \quad (t \to \infty). \]

Source: the cross-susceptibility identity
`∂_h Cov_h(x,x)|₀ = -t·κ₃(x,x,x)` is Murfet (2026), *From Clusters to
Circuits: Higher-Order Susceptibilities in Language Models*, Corollary
`prop:cross_susc` (formalised in the companion `threepoint` repository);
composing it with the third-cumulant asymptotic above gives this limit.
**The asymptotic value `α/λ³` is this repository's contribution**,
validated empirically in the SRI's 1D FDT-identity experiment. -/
theorem gibbsCov_deriv_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto
      (fun t : ℝ => t * deriv
        (fun h : ℝ => perturbedCov
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t h
            (fun x : ℝ => x) (fun x : ℝ => x)) 0)
      Filter.atTop (nhds (alpha / lam ^ 3)) :=
  Laplace.OneD.gibbsCov_deriv_anharmonic_asymptotic hlam hgamma hdisc

/-- **Multivariate leading-order covariance, sharp `O(t⁻²)` rate**
(`lem:laplace_cov`).

For a potential `V : (ι → ℝ) → ℝ` with a coercive quadratic–cubic–quartic
Taylor package at its minimum `0` (Hessian `H`, right inverse `Hinv`) and
observables `φ, ψ` with quadratic-jet packages and gradients
`a = ∇φ(0)`, `b = ∇ψ(0)`,
\[ \Big| t \cdot \mathrm{Cov}_t[\varphi, \psi] - \langle a, H^{-1} b\rangle \Big|
   \le \tfrac{K}{t} \quad (t \ge T_0), \]
i.e. `Cov_t[φ, ψ] = (1/t)·⟨∇φ(0), Σ ∇ψ(0)⟩ + O(t⁻²)` with `Σ = H⁻¹`.

Source: Elliott & Murfet (2026), *The Susceptibility Primer*, §4.1,
Lemma `lem:laplace_cov` (its display `eq:laplace_cov`).
**Deviation from the source:** the minimum is placed at the origin
(`w* = 0`); "smooth observables vanishing at `w*`" is rendered as explicit
analytic hypothesis packages (local Taylor-jet bounds, global coercivity and
polynomial growth, and Gaussian-moment/Fubini-IBP integrability hypotheses,
bundled in `Multi.PotentialJetApprox` / `Multi.ObservableJetApprox` /
`Multi.LaplaceCovHypotheses`); the inverse Hessian is supplied as a
symmetric right inverse `Hinv` rather than constructed. -/
theorem gibbsCov_first_order_rate_sharp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : Multi.PotentialJetApprox V H)
    (hφ : Multi.ObservableJetApprox φ a)
    (hψ : Multi.ObservableJetApprox ψ b)
    (hGauss : Multi.LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * Multi.gibbsCov V t φ ψ - Multi.dot a (Hinv b)| ≤ K / t :=
  Laplace.Multi.gibbsCov_first_order_rate_sharp V φ ψ H Hinv a b hV hφ hψ hGauss

/-- **Multivariate explicit first-order expectation** (`lem:laplace_exp`).

For a potential `V` with a quintic-remainder tensor package (Hessian `H`,
cubic tensor `T = ∇³V(0)`) and an observable `φ` with an exact-tensor package
(gradient `a = ∇φ(0)`, Hessian `A = ∇²φ(0)`),
\[ \Big| 2t \cdot \langle\varphi\rangle_t
   - \mathrm{tr}(A\Sigma) + (\Sigma a)\cdot(T{:}\Sigma) \Big|
   \le \tfrac{K}{t} \quad (t \ge T_0), \]
i.e. `⟨φ⟩_t = (1/2t)·[tr(AΣ) - (Σ∇φ(0))·(T:Σ)] + O(t⁻²)`, where
`(T:Σ)_i = ∑_{jk} T_{ijk} Σ_{jk}`.

Source: Elliott & Murfet (2026), *The Susceptibility Primer*, §4.1,
Lemma `lem:laplace_exp` (its display `eq:laplace_phi`); cf. Kass, Tierney
& Kadane (1990),
Theorem 4.
**Deviation from the source:** as in `gibbsCov_first_order_rate_sharp`
(origin-centred minimum, explicit analytic hypothesis packages
`Multi.PotentialQuinticApprox` / `Multi.ObservableTensorApprox` /
`Multi.LaplaceCov4MomentHypotheses` in place of smoothness); the primer's
`Dφ(w*)^⊤Σ(T:Σ)` is spelled `(Σa)·(T:Σ)`, equal by symmetry of `Σ`. -/
theorem gibbsExpectation_first_order_rate_explicit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : Multi.PotentialQuinticApprox V H)
    (hφ : Multi.ObservableTensorApprox φ a)
    (hGauss : Multi.LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |2 * t * Multi.gibbsExpectation V t φ - Multi.trASig hφ.A Hinv
          + Multi.dot (Hinv a) (Multi.tensorContractMatrix hV.T Hinv)| ≤ K / t :=
  Laplace.Multi.gibbsExpectation_first_order_rate_explicit V φ H Hinv a hV hφ hGauss

/-- **Multivariate explicit next-to-leading covariance** (`lem:laplace_cov2`).

For a potential `V` with a quintic-remainder tensor package and observables
`φ, ψ` with quintic/exact-tensor packages, when `∇φ(0) = 0`:
\[ \Big| t^2 \cdot \mathrm{Cov}_t[\varphi, \psi]
   - \mathrm{cov2Coeff}(A, \Phi, B, T, \Sigma, b) \Big| \le \tfrac{K}{t}
   \quad (t \ge T_0), \]
with `A = ∇²φ(0)`, `Φ = ∇³φ(0)`, `B = ∇²ψ(0)`, `b = ∇ψ(0)`, `T = ∇³V(0)`,
`Σ = H⁻¹`, and the four-term coefficient
`cov2Coeff = ½·tr(AΣBΣ) + ½·(Σb)·(Φ:Σ) - ½·b^⊤ΣAΣ(T:Σ) - ½·(Σb)·(T:(ΣAΣ))`.

Source: Elliott & Murfet (2026), *The Susceptibility Primer*, §4.1,
Lemma `lem:laplace_cov2` (its display `eq:cov_full_t2`).
**Deviation from the source:** as in `gibbsCov_first_order_rate_sharp`
(origin-centred minimum; explicit analytic hypothesis packages
`Multi.PotentialQuinticApprox` / `Multi.ObservableQuinticApprox` /
`Multi.ObservableTensorApprox` / `Multi.LaplaceCov6MomentHypotheses`,
including odd-quintic remainder bounds, in place of smoothness). The primer's
remainder is `O(t⁻³)` for smooth observables; here the rate is `O(t⁻¹)`
relative to `t²·Cov`, i.e. `Cov_t[φ,ψ] = cov2Coeff/t² + O(t⁻³)`. -/
theorem gibbsCov_first_order_rate_explicit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : Multi.PotentialQuinticApprox V H)
    (hφ : Multi.ObservableQuinticApprox φ a)
    (hψ : Multi.ObservableTensorApprox ψ b)
    (h_phi_grad_zero : a = 0)
    (hGauss : Multi.LaplaceCov6MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * Multi.gibbsCov V t φ ψ -
          cov2Coeff hφ.A hφ.Φ hψ.A hV.T Hinv b| ≤ K / t :=
  Laplace.Multi.gibbsCov_first_order_rate_explicit V φ ψ H Hinv a b hV hφ hψ h_phi_grad_zero hGauss

/-- **2D degenerate separable moment power law.**

For the additively-separable potential
`L(x, y) = x^(2k₁)/(2k₁)! + y^(2k₂)/(2k₂)!` (`k₁, k₂ ≥ 1`; a degenerate,
non-quadratic minimum whenever `kᵢ ≥ 2`, outside the Laplace/Gaussian
regime), the mixed even moment obeys an exact power law:
\[ \big\langle x^{2j_1} y^{2j_2} \big\rangle_t \;\sim\;
   C(k_1,k_2,j_1,j_2) \cdot t^{-j_1/k_1 - j_2/k_2} \quad (t \to \infty), \]
with `C` the explicit Gamma-quotient constant `kthKthMomentConst`. The decay
exponents `jᵢ/kᵢ` interpolate the Gaussian case (`kᵢ = 1`, exponent `jᵢ`).

Source: **beyond the written source material** — the Susceptibility Primer's
§4.2 motivates the singular (degenerate-Hessian) regime but displays no
closed-form moment law; this family is the repository's exploration of that
regime in the simplest separable setting. -/
theorem gibbsExpectation_kthKth_isEquivalent_rpow
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (j₁ j₂ : ℕ) :
    (fun t : ℝ =>
        gibbsExpectation2D (addSeparable (kthPotential k₁) (kthPotential k₂)) t
          (fun z : ℝ × ℝ => z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂)))
      ~[atTop]
      (fun t : ℝ => kthKthMomentConst k₁ k₂ j₁ j₂ *
                    t ^ (-((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ)))) :=
  Laplace.TwoD.gibbsExpectation_kthKth_pow_pow_isEquivalent_rpow hk₁ hk₂ j₁ j₂

end Laplace.Statements
