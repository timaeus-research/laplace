# Consult: sufficient sub-families of observables for jet recovery (germbij / laplace Lean seabed)

## Context
We formalise (Lean 4 + Mathlib) the germbij note "What expectation values know about the loss landscape": for a loss `L : ℝ^d → ℝ` with a nondegenerate minimum at 0 (Hessian form `H` positive definite), the posterior-type expectations `⟨φ⟩_t = ∫ φ e^{-tL} / ∫ e^{-tL}` (localized to a ball) have asymptotic expansions in `q = t^{-1/2}`, and the note's Theorem 3.1 recovers the Taylor jet of `L` at 0 from them. Formalised already (repo `laplace`, `Laplace/Multi/*`):

- `HigherLaplaceDomain k L H`: certified package (domain ball `U`, `C^k`, order-`k` Taylor remainder bound, quadratic lower bound). `A.rescaledMoment P q` = localized normalized moment of test `P` at scale `q`.
- `taylorHomogeneousTerm k L x = (k!)⁻¹ • iteratedFDeriv ℝ k L 0 (fun _ ↦ x)`.
- **Pairing limit** (proven): for `2 < k`, packages `A₁ A₂` for `L₁ L₂` with equal jets below `k`, and ANY continuous polynomially-growing test `P`:
  `(A₁.rescaledMoment P q − A₂.rescaledMoment P q) / q^(k−2) → −gaussianCovariance H P Q` as `q → 0⁺`, where `Q = taylorHomogeneousTerm k L₁ − taylorHomogeneousTerm k L₂` and `gaussianCovariance H f g = E_γ[fg] − E_γ[f]E_γ[g]`, `γ = N(0, H⁻¹)`.
- **Rigidity** (proven): `Q` homogeneous of degree `k > 0`, continuous, polynomial growth, `gaussianCovariance H Q Q = 0` ⇒ `Q = 0`. Symmetric tensors with equal diagonals are equal.
- Existing recovery theorems: all homogeneous degree-k tests suffice; the `d^k` monomial words `x ↦ ∏_j x_{m j}` suffice; per-degree monomial data up to degree N recover the N-jet; all degrees recover the whole jet.

The user's question: which sub-families `S` of observables suffice to recover the jet/germ? Is there a clean condition? What "approximation" results from taking fewer?

## Candidates (Lean-flavoured; `Q_k := taylorHomogeneousTerm k L₁ − taylorHomogeneousTerm k L₂`)

(A) General-family sufficiency at degree k (the "if"): for a family `φ : ι → ℝ^d → ℝ` of continuous polynomially-growing tests, IF the pairing `Q ↦ (gaussianCovariance H (φ i) Q)_i` is injective on continuous polynomially-growing degree-k homogeneous `Q` (hypothesis `hinj`), and the S-data are `o(q^{k−2})` for every `i`, THEN `iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0` (given equal lower jets and symmetric tensors). Proof: pairing limit + uniqueness of limits ⇒ all pairings with `Q_k` vanish ⇒ `Q_k = 0` ⇒ diagonals equal ⇒ tensors equal.

(B) Converse, pair form: if `gaussianCovariance H (φ i) Q_k = 0` for all `i`, then all S-data are `o(q^{k−2})` (limit 0). So A+B: relative to two losses, S distinguishes their k-jets at the rate iff the pairing with `Q_k` is nonzero for some `i`.

(B′) Instance: from a certified `L₁` and a nonzero homogeneous degree-k polynomial `Q` (diagonal of a symmetric k-tensor), build the package for `L₁ + Q`, with equal jets below k and `iteratedFDeriv k` differing by `k! • T`. Needs `iteratedFDeriv j (T ∘ diagonal) 0` for all `j`, the Taylor remainder bound for `L₁ + Q`, and the shrunken-ball quadratic lower bound. Estimated 200–300 Lean lines.

(C) No finite family suffices (pairing level): for `d ≥ 2`, `H` posdef, a finite family of `n` tests and any `k ≥ n` (so `k+1 > n`), there is a NONZERO continuous polynomially-growing degree-k homogeneous `Q` with `gaussianCovariance H (φ i) Q = 0` for all `i`. Proof: the `k+1` monomials `x₀^{k−j} x₁^{j}` are linearly independent as functions (restrict to `(s,1,0,…)`, real polynomial identity), the pairing is linear in `Q` (additivity/smul of `gaussianCovariance` in the second slot, from integrability under polynomial growth), and a linear map from a `(k+1)`-dimensional space to `ℝ^n` with `n < k+1` has nontrivial kernel. Combined with B (and B′ for the existence of the pair), NO finite family of observables recovers the full jet when `d ≥ 2`. (In `d = 1`, `{x², x³}` suffice.)

(D) Already formalised: monomials of degree ≤ N recover exactly the N-jet (`finite_jet_recovery_of_monomial_rates`).

## Questions
1. Are A, B, C correct as stated? In particular: (i) is the injectivity condition in A the right "clean condition" for a sufficient set, and is it correct that it is `H`-dependent unless the k-jets of the family span all of `H_k`? (ii) In C, is the count right — for a family of `n` tests, degree `k` with `k + 1 > n` already gives a kernel direction in `d ≥ 2` (so the failure sets in at degree `n`, not at `C(k+d−1,d−1) > n`)? (iii) Any subtlety in "the pairing depends only on the k-jet of φ"? (I do NOT plan to formalise that reduction; A quantifies over the actual tests.)
2. Which single coherent tide is strongest: A+B+C as one file (~250 lines), or A+B+C+B′ (~500 lines)? Is B′ worth its Lean cost, or is the relative iff (A+B) the right published statement with B′ a one-line remark in the paper ("take L₂ = L₁ + Q")? Is there a cheaper construction for B′ (e.g. avoiding computing iteratedFDeriv of a multilinear diagonal via Mathlib's `ContinuousMultilinearMap.iteratedFDeriv`/cpolynomial API, or via `HasFTaylorSeriesUpTo` for polynomials)?
3. Better or additional candidates close to this seabed on the "sufficient set / approximation from fewer observables" theme? E.g. an approximation statement: if S spans the degree-≤D jets but has a kernel at degree D+1, then two losses can differ at order D+1 while ALL S-data agree to o(q^{D−1}) — is that just B at k = D+1, or is there a stronger "all orders of S-data agree to o(q^{D-1})" statement (data beyond the leading rate)? Any pitfalls with the localisation (the moments are on a ball, not global)?
4. Vote for the single tide target.

Please answer in the numbered form, be concrete about Lean shape (statement-level), and end with a one-line vote.
