# Tide `covK-anharmonic` (seabed: laplace, off tide/moments-all-orders) — candidates v1

Context. The Sanity-on-Sampling note's fourth Laplace prediction is eq:covK,
`Cov[K, ψ] = ½ tr(HSBS) + ½ (Sb)ᵀ(T:S) − (t/2) bᵀSHS(T:S) − (t/2)(Sb)ᵀ(T:(SHS))` for a quadratic probe `ψ = ½ wᵀBw + bᵀw` (`S = P⁻¹`,
`P = tH`, `T = D³L`), "the primer's canonical experiment", which the note says "was checked against the primer's one-dimensional worked
examples and against exact quadrature before any chain was run" and whose relative error is "proportional to `1/t`" (E2). The seabed has
the general multi-dimensional *rate* theorem (`covK_closed_form_rate_posDef`, section 23), but no exact one-dimensional instance. With the
all-orders moment asymptotics just proved (`tendsto_J_n`, `√(λt)^n⟨xⁿ⟩ → E[gⁿ]`, `t²⟨x⁵⟩, t²⟨x⁶⟩ → 0`) the exact 1D covK is in reach.

Seabed (Lean 4 / Mathlib, all proved). For `ℓ = λx²/2 + αx³/6 + γx⁴/24` (`λ, γ > 0`, `α² < 3λγ`): `t⟨x⟩ → −α/(2λ²)`, `t⟨x²⟩ → 1/λ`,
`t²⟨x³⟩ → −5α/(2λ³)`, `t²⟨x⁴⟩ → 3/λ²`, `t³⟨x⁶⟩ → 15/λ³`, `t²⟨x⁵⟩ → 0`, `t²⟨x⁶⟩ → 0`, `t² Cov[x², x] → −2α/λ³` (`cov_anharmonic_asymptotic`);
1D `gibbsCov L t φ ψ = ⟨φψ⟩ − ⟨φ⟩⟨ψ⟩` with bilinearity lemmas (`gibbsCov_add_left/right`, `gibbsCov_smul_left/right`, `gibbsCov_const_*`
in `Laplace/Gibbs.lean`, hypotheses to be checked) and `gibbsExpectation_anharmonic_energy : ⟨ℓ⟩ = (λ/2)⟨x²⟩ + (α/6)⟨x³⟩ + (γ/24)⟨x⁴⟩`
with the integrability `integrable_pow_mul_exp_neg_t_anharmonic`.

Candidates.

A. **Pairwise covariance asymptotics** (`t² Cov[xᵐ, xⁿ]` for the pairs covK needs): `t² Cov[x², x²] → 2/λ²` (from `t²⟨x⁴⟩ → 3/λ²` and
   `(t⟨x²⟩)² → 1/λ²`), `t² Cov[x³, x²] → 0`, `t² Cov[x⁴, x²] → 0` (from `t²⟨x⁵⟩, t²⟨x⁶⟩ → 0` and `⟨x²⟩ → 0`), `t² Cov[x², x] → −2α/λ³`
   (existing), `t² Cov[x³, x] → 3/λ²`, `t² Cov[x⁴, x] → 0`.
B. **covK for the exact anharmonic measure** (`covK_anharmonic_sq`, `covK_anharmonic_lin`, `covK_anharmonic`): by bilinearity
   `Cov[ℓ, ψ] = (λ/2)Cov[x², ψ] + (α/6)Cov[x³, ψ] + (γ/24)Cov[x⁴, ψ]`, so `t² Cov[ℓ, x²] → 1/λ`, `t² Cov[ℓ, x] → −α/(2λ²)`, and for
   `ψ = (B/2)x² + bx`: `t² Cov[ℓ, ψ] → B/(2λ) − bα/(2λ²)`.
C. **Identification with eq:covK** (`covK_formula_oneDim`): with `H = λ`, `S = 1/(λt)`, `T = α`, the four terms of eq:covK are
   `B/(2λt²) + αb/(2λ²t²) − αb/(2λ²t²) − αb/(2λ²t²) = (B/(2λ) − αb/(2λ²))/t²`, so the exact `t² Cov[ℓ, ψ]` converges to `t²` times eq:covK's
   value: the formula is the exact leading term ("relative error `O(1/t)`", given B's convergence; a rate would need the moment rates).
   Optionally: the E2 statement that the *relative* error `t² Cov/covK − 1 → 0` when `B/(2λ) − αb/(2λ²) ≠ 0`.

Numerical check done (`numcheck48.py`, `λ = 2`, `a = ½`, `B = 3`, `b = 1.5`): `t² Cov[ℓ, x²] = 0.49998` (→ `1/λ = 0.5`), `t² Cov[ℓ, x] = −0.17674`
(→ `−α/(2λ²) = −0.1768`), `t² Cov[ℓ, ψ] = 0.48486` at `t = 10⁴` against `B/(2λ) − bα/(2λ²) = 0.48483`; eq:covK's four terms evaluate to
`0.75, 0.265, −0.265, −0.265` with the same sum.

Questions. (1) Are A–C correct — in particular the term-by-term bookkeeping `t² Cov[ℓ, x] → (λ/2)(−2α/λ³) + (α/6)(3/λ²) + 0 = −α/(2λ²)` and
the identification of eq:covK's `b`-terms (`½(Sb)(T:S) − (t/2) b S H S (T:S) − (t/2)(Sb)(T:(SHS))` in one dimension sum to `−αb/(2λ²t²)`)? (2)
The products `t²⟨x³⟩⟨x²⟩ → 0` use `⟨x²⟩ → 0` (from `t⟨x²⟩ → 1/λ`); is there a cleaner uniform way to dispatch all the cross terms, e.g. a lemma
"`t^{(m+n)/2}⟨xᵐ⟩⟨xⁿ⟩` is bounded, so `t² ⟨xᵐ⟩⟨xⁿ⟩ → 0` when `m + n ≥ 5`"? (3) Is C best stated as the limit of `t² Cov` equalling
`t² · covK(t)` (a constant), or as `Tendsto (fun t => Cov[ℓ, ψ]/covK(t)) atTop (𝓝 1)` (needs the constant nonzero), or both? Please end with a
vote on A–C.
