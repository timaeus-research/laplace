You are consulted (one round) on tide 88 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders (`∃ K T, ∀ t ≥ T, |…| ≤ K/t`). Tide 86 (your consult approved it) landed the third cumulant of the
localised energy: `t³κ₃(ℓ) → 1` per frame coordinate and, on E2, the exact `∂ₜ²⟨L∘A⟩_loc = −∂ₜVar_loc = ∑ᵢ κ₃(ℓᵢ)` with `t³∂ₜ²⟨L⟩ → d`
— the Gamma(d/2, t) cumulants `k/t, k/t², 2k/t³` through third order. Tide 87 landed the second-order variance `t²Var_loc(ℓ) = ½ + 2e₁/t + O(t⁻²)`.

## Candidates v1 (Claude)

Setting (E2, as in tides 68–87): the exact localised measure per frame coordinate, density `exp(−tℓ(x) − g(x − x₀)²/2)`,
`ℓ = λx²/2 + αx³/6 + γx⁴/24`, `λ > 0`, `γ > 0`, `α² < 3λγ`, `g ≥ 0`; on E2 the product over frame coordinates `uᵢ = (Qᵀ(w − c))ᵢ`
of a rotated separable quartic `L∘A = ∑ᵢ ℓᵢ(uᵢ)` with the isotropic localiser `g|w − w₀|²/2`. `mⱼ = ⟨xʲ⟩_loc`.

Landed 1D inputs: the Stein recursion `(tλ + g) m_{k+1} + (tα/2) m_{k+2} + (tγ/6) m_{k+3} = k m_{k−1} + g x₀ m_k` (all k ≥ 0);
rates `|t³m₆ − 15/λ³| ≤ K/t`; bounds `|t⁴m₇| ≤ K` (signed seventh via the recursion at k = 6), `|t⁴ m_{2k}| ≤ K`, `|t⁴ m_{2k+1}| ≤ K` for k ≥ 4
(the odd ones via `|x|^{2k+1} ≤ (x^{2k} + x^{2k+2})/2`), obtained from the unlocalised even-moment bounds `t^k ⟨x^{2k}⟩ ≤ C` by
`locWeight ≤ exp(gx₀²/2)` and the denominator `D ≥ ½`; leading rates `t⟨ℓ⟩ → ½`, `t²⟨ℓ²⟩ → ¾`, `t³⟨ℓ³⟩ → 15/8` (all `O(1/t)`);
`ℓ³` expanded as an explicit polynomial in `m₆..m₁₂` with an "assembly" lemma packaging the rates. Landed E2 inputs: for a continuous
probe `f` of one frame coordinate, `⟨f(uᵢ)⟩_loc` equals the 1D localised expectation, `Cov_loc(L∘A, f(uᵢ)) = Cov_loc,ᵢ(ℓᵢ, f)`, and
`HasDerivAt (s ↦ ⟨f(uᵢ)⟩_loc(s)) (−Cov_loc(L∘A, f(uᵢ))) t` given integrability of `ℓₖ(uₖ) f(uᵢ) e^{−(t/2)L}` for all k;
`Var_loc(L∘A) = ∑ᵢ Var_loc,ᵢ(ℓᵢ)`; `HasDerivAt (deriv ⟨L∘A⟩_loc) (∑ᵢ κ₃(ℓᵢ)) t` where `κ₃ = ⟨ℓ³⟩ − 3⟨ℓ²⟩⟨ℓ⟩ + 2⟨ℓ⟩³`.

**A. The eighth-moment coefficient, the signed ninth moment, and the fourth cumulant (1D).**
(A1) `|t⁵ m_{2k}| ≤ K` and `|t⁵ m_{2k+1}| ≤ K` for k ≥ 5 (same template, one power higher).
(A2) Signed ninth moment: recursion at k = 8, `t⁵m₉ = (t/(tλ + g))·(8 t⁴m₇ + g x₀ t⁴m₈ − (α/2) t⁵m₁₀ − (γ/6) t⁵m₁₁)`, so **`|t⁵m₉| ≤ K`**.
(A3) Eighth moment: recursion at k = 7, `t⁴m₈ = (t/(tλ + g))·(7 t³m₆ + g x₀ t³m₇ − (α/2) t⁴m₉ − (γ/6) t⁴m₁₀)`; with `t³m₆ → 15/λ³`,
`t³m₇ = O(1/t)`, `t⁴m₉ = O(1/t)`, `t⁴m₁₀ = O(1/t)`: **`|t⁴m₈ − 105/λ⁴| ≤ K/t`**.
(A4) `ℓ⁴` is an explicit polynomial of degree 8..16 (9 coefficients: `λ⁴/16 x⁸ + λ³α/12 x⁹ + …`); with `t⁴m₈ → 105/λ⁴` and all higher
`t⁴mⱼ = O(1/t)`: **`|t⁴⟨ℓ⁴⟩_loc − 105/16| ≤ K/t`**.
(A5) With `κ₄ = ⟨ℓ⁴⟩ − 4⟨ℓ³⟩⟨ℓ⟩ − 3⟨ℓ²⟩² + 12⟨ℓ²⟩⟨ℓ⟩² − 6⟨ℓ⟩⁴` and the leading rates:
`t⁴κ₄ → 105/16 − 4·(15/8)(½) − 3(¾)² + 12(¾)(¼) − 6/16 = 3`, i.e. **`|t⁴κ₄(ℓ) − 3| ≤ K/t`** — the Gamma(½, t) fourth cumulant `3!·½ = 3`.

**B. On E2: the third derivative of the mean energy.** Per coordinate, the 1D derivative identities (`∂ₜ⟨f⟩ = −Cov(ℓ, f)` for
`f = ℓ, ℓ², ℓ³`) give exactly `∂ₜκ₃(ℓ) = −κ₄(ℓ)` (ring identity after expanding `Cov(ℓ, ℓⁿ) = ⟨ℓⁿ⁺¹⟩ − ⟨ℓⁿ⟩⟨ℓ⟩`); summing,
**`HasDerivAt (deriv (deriv ⟨L∘A⟩_loc)) (−∑ᵢ κ₄(ℓᵢ)) t`**, i.e. `∂ₜ³⟨L∘A⟩_loc = −∑ᵢκ₄(ℓᵢ)` exactly, and with A5
**`|t⁴ ∂ₜ³⟨L∘A⟩_loc + 3d| ≤ K/t`**: the Gamma(d/2, t) cumulant hierarchy `κₙ = (n−1)!(d/2)/tⁿ` verified through n = 4 (the note's
"two regimes" Gamma law of `tK`). Needs new integrability lemmas `ℓₖ(uₖ) ℓᵢ(uᵢ)³ e^{−sL}` (product-measure factorisation, as tide 86 did
for `ℓᵢ²`).

**C. Excess kurtosis (shape statement, t-normalisation-free).** From A5 and tide 85's `|t²Var_loc(L∘A) − d/2| ≤ K/t` and additivity
(`κ₄(L∘A) = ∑κ₄(ℓᵢ)` is *not* landed as a cumulant statement; C would instead be stated for the derivative-defined quantity
`−∂ₜ³⟨L⟩ / (∂ₜ⟨L⟩)²`, which by tide 85/86 identities equals `∑κ₄ᵢ / (∑Var_i)²`): **`|(−∂ₜ³⟨L∘A⟩_loc)/(∂ₜ⟨L∘A⟩_loc)² − 12/d| ≤ K/t`** — the
Gamma(d/2) excess kurtosis `6/k = 12/d`. Numerically the convergence looks `O(t⁻²)` (the `1/t` terms cancel in the ratio), but we would
only claim `O(1/t)`.

## Numerical check (scipy quad, λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35))
`t⁴m₈`: 36.57, 158.67 at t = 640 vs 105/λ⁴ = 36.76, 160.04 (1/t convergence); `t⁵m₉` settles at ≈ −138, 840 (bounded);
`t⁴⟨ℓ⁴⟩` = 6.533, 6.518 at t = 640 vs 105/16 = 6.5625; `t⁴κ₄` = 2.987, 2.980 (→ 3); `κ₄/κ₂²` = 12.0000, 12.0001 (1D, → 12);
E2 (d = 2): finite-difference `∂ₜ³⟨L⟩` matches `−∑κ₄ᵢ` to 4 digits at t = 40, 80, 160; `t⁴∂ₜ³⟨L⟩` = −5.50, −5.74, −5.87 (→ −6 = −3d);
`κ₄(L)/κ₂(L)²` = 6.006, 6.0015, 6.0004 (→ 12/d = 6).

## Questions
1. Are A1–A5, B, C correct as stated (closed forms `105/λ⁴`, `105/16`, `3`, `−3d`, `12/d`; the identity `∂ₜκ₃ = −κ₄` for the localised
   measure whose localiser is t-independent; the rate bookkeeping in A3 — is the O(1/t) claim for `t⁴m₈` justified with the listed inputs,
   in particular is `t⁴m₉ = O(1/t)` needed and supplied by A2)?
2. Which bundle is the strongest reasonably reachable single tide (A+B, A+B+C)? Is C's derivative-defined formulation the right way to
   state the excess kurtosis without a general cumulant-additivity theorem, or is there a cleaner statement?
3. Anything missed close to this seabed — e.g. a Stein-type shortcut for `⟨ℓ⁴⟩` avoiding the 9-term polynomial expansion (as the
   Stein–covariance reduction avoided second-order moments in tide 87), or a cleaner route to the eighth-moment coefficient?
4. Wording against the note: is "the Gamma(d/2, t) law of the localised energy verified through the fourth cumulant" a fair gloss, and what
   qualifications are needed (fixed g, x₀; the localised measure is not the posterior; rates not uniform in parameters)?
Vote for one bundle at the end.
