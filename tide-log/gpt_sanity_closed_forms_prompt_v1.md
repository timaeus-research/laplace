# Context for a Lean 4 / Mathlib formalisation step (tide `sanity-closed-forms`, seabed `laplace`)

We formalise, in Lean 4 with current Mathlib, closed forms used by a note ("Sanity on Sampling") that
compares SGLD sampling with inverse-Hessian (Laplace) predictions on nondegenerate potentials.
Previous tide (merged): `Laplace/Sampler/Lyapunov.lean`, `Laplace/Sampler/ULA.lean` (ULA stationary
covariance `(P - (h/2)P²)⁻¹`, unique fixed point of `Σ ↦ (I-hP)Σ(I-hP) + 2hI`, eigenbasis entries via
`orthoOf hP : Matrix ι ι ℝ` orthogonal with `P = U diag(eigenvalues) Uᵀ`; minibatch entry formula; finite-time
identity `Σ_k - S = A^k (Σ_0 - S)(Aᵀ)^k`; scalar `ar1_var_iterate`), `Laplace/Multi/GaussianLLC.lean`.

Seabed infrastructure relevant here:
- 1D Gibbs objects on ℝ: `partitionFunction L t = ∫ x, exp(-(t * L x))`, `gibbsExpectation L t φ = (∫ φ x * exp(-(t L x))) / Z`.
- 2D track on `ℝ × ℝ` (`Laplace/TwoD/*.lean`): additively separable potentials `L(x,y) = U x + V y`, with
  factorisation `∫ f(x) g(y) e^{-tL} = (∫ f e^{-tU})(∫ g e^{-tV})` via `MeasureTheory.integral_prod_mul`,
  partition functions, moments of `x^m y^n` for separable quartic/sextic potentials. Nothing non-separable yet.
- 1D Gaussian moments (`Laplace/OneD/GaussianMoments.lean`): `∫ x^(2k) exp(-(t x²)/2) = (2k-1)‼ √(2π) t^{-(k+1/2)}`,
  odd moments vanish; harmonic Gibbs expectations of powers.
- Multi-D: Gaussian weight `exp(-½⟨u,Pu⟩)` on `ι → ℝ`, IBP theorem `gaussian_second_moment_eq_inverse_entry`.
- Matrices: `Matrix ι ι ℝ`, `Matrix.IsHermitian.eigenvalues`, spectral theorem packaged as
  `spectral_real : A = orthoOf hA * diagonal hA.eigenvalues * (orthoOf hA)ᵀ`.

## Candidates v1 (Claude)

### A. Exact Gibbs moments of the two-dimensional Rosenbrock potential
`L(x,y) = (a (y - x²)² + (1 - x)²) / 2`, `a > 0`, `t > 0`, weight `w = exp(-t L)` on ℝ², no localisation.
Structural lemma (A0): for `f` with the needed integrability,
`∫∫ f(x,y) w(x,y) dx dy = ∫ (∫ f(x, u + x²) e^{-(t a/2) u²} du) e^{-(t/2)(1-x)²} dx`
(the y-integral is a shifted Gaussian; for fixed x the conditional law of y is N(x², 1/(t a))).
Closed forms (A1..A5), all verified numerically (scipy dblquad, a = 100, t = 7, agreement 1e-8):
- Z = 2π/(t √a); E[x] = 1; E[x²] = 1 + 1/t; E[y] = E[x²] = 1 + 1/t; E[xy] = E[x³] = 1 + 3/t;
  E[y²] = E[x⁴] + 1/(t a) = 1 + 6/t + 3/t² + 1/(t a).
- Var x = 1/t, Cov(x,y) = 2/t, Var y = 4/t + 2/t² + 1/(t a).
- E[L] = 1/t, i.e. t⟨K⟩ = 1 = d/2 exactly at every t.
- Laplace comparison: Hessian at (1,1) is H = [[1+4a, -2a],[-2a, a]], det H = a, S = (tH)⁻¹ = (1/t)[[1,2],[2,4+1/a]],
  so exact Cov - S = (2/t²)·e_y e_yᵀ: the Laplace covariance is exact in the x-variance and the cross term and misses
  exactly 2/t² in Var y (on the stiff eigendirection of H this is the note's relative error ≈ 1 + 200/t for a = 100).
Proof route options for A0: (i) `MeasureTheory.integral_prod` (Fubini) + `integral_sub_right_eq_self` on the inner
integral, with product integrability from `MeasureTheory.integrable_prod_iff` (sections are Gaussian-polynomial;
the norm of the section integrates to a polynomial in x times a Gaussian in x); (ii) a measure-preserving shear
`(x,y) ↦ (x, y - x²)` turning the weight into a separable one so the seabed's `addSeparable` machinery applies.
Observables needed: 1, x, y, x², xy, y², L (polynomials of degree ≤ 4 in (x,y)).

### B. Finite AR(1) chain: expected pooled sample variance, in inner-product form
Let `E` be a real inner product space, `|ρ| < 1`, `v > 0`, `σ² = v/(1-ρ²)`. A chain `x : ℕ → E` with `x 0 = 0`,
`x (k+1) = ρ • x k + η (k+1)`, and white noise `⟪η j, η k⟫ = if j = k then v else 0`. (With `E = L²(Ω)` and
`⟪X,Y⟫ = E[XY]` this is the AR(1) chain of the note started at the mode; the L² instantiation is deliberately
deferred, the claims below are about the second-moment structure only.)
- (B1) `⟪x k, x l⟫ = σ² (ρ^{|k-l|} - ρ^{k+l})`; in particular `‖x k‖² = σ²(1 - ρ^{2k})` (the previous tide's `ar1_var_iterate`).
- (B2) For the draw window `k ∈ {b+1, …, b+N}`: `(1/N) Σ_k ‖x k‖² = σ² (N - Σ_k ρ^{2k}) / N` and
  `‖(1/N) Σ_k x k‖² = σ² (N + 2 Σ_{m=1}^{N-1} (N-m) ρ^m - (Σ_k ρ^k)²) / N²`.
- (B3) `C` chains `x^c` with mutually orthogonal noise families (`⟪η^c j, η^{c'} k⟫ = v` iff `c = c'` and `j = k`, else 0):
  the expected pooled sample variance `(1/(CN)) Σ_{c,k} ‖x^c k‖² - ‖(1/(CN)) Σ_{c,k} x^c k‖²`
  `= σ² (N - Σ_k ρ^{2k})/N - σ² (N + 2 Σ_{m=1}^{N-1}(N-m)ρ^m - (Σ_k ρ^k)²)/(C N²)`.
  This is exactly the note's `ar1_expected_sample_variance` (checked by Monte Carlo: 3.6332 ± 0.0035 vs 3.6362 at
  ρ = 0.9, v = 1, N = 12, b = 5, C = 3; and the second-moment table (B1) to MC precision).
Lean concerns: `|k - l|` with ℕ subtraction (state B1 as `k ≤ l → ⟪x k, x l⟫ = σ² (ρ^(l-k) - ρ^(k+l))` plus symmetry);
sums over `Finset.Ico (b+1) (b+N+1)`; the Toeplitz double sum `Σ_{k,l} ρ^{|k-l|} = N + 2 Σ_{m=1}^{N-1}(N-m)ρ^m`.

### C. ULA-corrected LLC (trace form)
With `P` symmetric positive definite, `h p_i < 2`: `trace (P * ulaCov P h) = Σ_i 1/(1 - h p_i/2)`; for `P = t • H`,
`γ = 0`: `(t/2) trace (H * ulaCov (t • H) h) = ½ Σ_i 1/(1 - h t λ_i/2)`, the note's "ULA-corrected LLC" (which is
100 instead of d/2 = 5 at h p_max = 1.9 in E1). Cheap corollary of `ulaCov_conj_apply` and `Matrix.trace_mul_comm`.

## Questions
1. Are A, B, C correct as written (formulas, hypotheses)? In particular check A's closed forms and the claim
   `exact Cov - S = (2/t²) e_y e_yᵀ`, and B3's sign/normalisation.
2. Which is the strongest coherent cluster reachable in one excursion? Our prior: A0-A5 + B1-B3 + C.
3. For A0, which Mathlib route is smoother: Fubini with `integrable_prod_iff` and the shift `integral_sub_right_eq_self`,
   or a measure-preserving shear on `ℝ × ℝ` (is there a Mathlib lemma for `(x, y) ↦ (x, y + g x)` preserving
   `volume.prod volume`, e.g. via `MeasureTheory.measurePreserving_prod_add` variants or `Measure.prod` + `map`)?
   How would you organise the integrability proofs for the seven polynomial observables (a single lemma
   `∀ m n, Integrable (fun p => p.1^m * p.2^n * w p)` and how to prove it)?
4. Is the inner-product-space formulation of B an acceptable formalisation of the note's finite-chain prediction,
   and do you see a cleaner statement (e.g. a general "second-moment table ⟹ sample-variance expectation" lemma)?
5. Better candidates near this seabed that we missed, of comparable size?
Please end with a one-line vote for a single target cluster.
