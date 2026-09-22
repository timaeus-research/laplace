You are GPT-6 Astra consulting on a Lean 4 + Mathlib formalisation tide ("laplace" seabed: Laplace asymptotics of Gibbs
expectations for the quartic anharmonic oscillator, with the isotropic Gaussian localiser of a research note's E3). Below are the
candidate statements for the next tide, with the seabed's available lemmas. Please answer:

1. Are A, B, C correct as stated? In particular check `e₁ = (a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)` and the decomposition
   `e₁ = (λ/2)c₂' + (α/6)(c₃ + 3a/λ²) + (γ/24)(3/λ²)` with `c₂' = n₂ − d₁/λ`, `n₂ = B₂ + ac₃ + 3p₃/λ²`, `d₁ = −aα/(2λ²) + p₃/λ`,
   independently (do not just trust our sympy), and check that the listed moment-rate inputs suffice for each `K/t²` or `K/t` claim
   (in particular the signed handling of `x⁵` in the cubic and quartic expansions, and whether `|x|⁷ ≤ (x⁶ + x⁸)/2` loses nothing).
2. Which bundle is the strongest reasonably reachable target in one tide (we estimate ~700–800 Lean lines, reusing tide 72's
   expansion pattern), and is there a cleaner route (e.g. a Stein/IBP identity for the localised measure, or deriving the localised
   energy from the localised mean/variance already proven) that avoids one of the three pointwise expansions?
3. How should the result be worded against the note's E3 (which predicts the localised LLC `½tr(tH(tH + γI)⁻¹)` in the Gaussian
   approximation)? Is the reading "the trace prediction captures exactly the `−g/(2λ)` part; the residual `1/t` term is the
   unlocalised anharmonic correction plus the anchor-displacement terms `a²/(2λ) − aα/(2λ²)`" fair? Pitfalls?
4. Vote: which single candidate/bundle do you back?

## Candidates v1 (Claude)

Setting (as in tides 65–72): the one-dimensional anharmonic oscillator `ℓ(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` (`λ, γ > 0`,
`α² < 3λγ`), Gibbs weight `e^{−tℓ}`, and the isotropic localiser of the note's E3 with strength `g ≥ 0` and anchor `x₀`, i.e. the
localised measure `e^{−tℓ(x) − (g/2)(x − x₀)²} ∝ e^{−tℓ} φ` with `φ = e^{ax − (g/2)x²}`, `a = g x₀`. Write `⟨·⟩` for the
unlocalised and `⟨·⟩_loc` for the localised expectation, `D = ⟨φ⟩`.

Seabed state. Tide 69 (`LocalisedAnharmonicLLC.lean`) proved E3's localised LLC to first order:
`|t⟨ℓ⟩_loc − ½·tλ/(tλ + g)| ≤ K/t`, via `locEnergy_eq` (`⟨ℓ⟩_loc = (λ/2)⟨x²⟩_loc + (α/6)⟨x³⟩_loc + (γ/24)⟨x⁴⟩_loc`),
`locSecondMoment_eq`, `locThirdMoment_loc_rate` (`|t⟨x³⟩_loc| ≤ K/t`), `locFourthMoment_loc_le`; GPT then noted the `1/t`
coefficient was *not* identified, and gave the bracket
`t⟨ℓ⟩_loc = ½ + [(a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)]/t + o(1/t)`.
Tide 72 (`LocalisedMeanCoeff.lean`) built the machinery for second-order localised expansions: `abs_exp_sub_taylor_le`
(`|e^y − ∑_{m<n} y^m/m!| ≤ (e^M + n)|y|^n` for `y ≤ M`, `n ≥ 2`), `locWeight_taylor_le`, `abs_locExponent_pow_le`
(`|ax − bx²|^n ≤ 2^n(|a|^n|x|^n + |b|^n(x²)^n)`), the denominator to second order `locDenominator_rate2`
(`|D − 1 − d₁/t| ≤ K/t²`, `d₁ = −aα/(2λ²) + p₃/λ`, `p₃ = (a² − g)/2`), the cross-multiplied ratio identity `ratio_key`
(`t(N/D) − c − c'/t = ((tN − c − n₁/t) − c(D − 1 − d₁/t) − c'd₁/t² − (c'/t)(D − 1 − d₁/t))/D` when `n₁ = c' + c d₁`), and the
"abstract-real assembly lemma" pattern that avoids elaboration timeouts. Normalised moment inputs available:
`secondMoment_anharmonic_order3_rate` (`|t⟨x²⟩ − 1/λ − B₂/t| ≤ K/t²`, `B₂ = 5α²/(4λ⁴) − γ/(2λ³)`), `thirdMoment_lead`
(`|t²⟨x³⟩ − c₃| ≤ K/t`, `c₃ = −5α/(2λ³)`), `fourthMoment_lead` (`|t²⟨x⁴⟩ − 3/λ²| ≤ K/t`), `fifthMoment_lead`
(`|t³⟨x⁵⟩ − c₅| ≤ K/t`, `c₅ = −35α/(2λ⁴)`), `evenMoment_bound k` (`⟨x^{2k}⟩ ≤ C/t^k`), `energy_order1_coeff`
(`e₀ = 5α²/(24λ³) − γ/(8λ²)` is the unlocalised first correction, `energy_anharmonic_order1_rate`: `|t⟨ℓ⟩ − ½ − e₀/t| ≤ K/(t√t)`).
In `d` dimensions (E2's rotated separable oscillator with the isotropic localiser), tide 69 has
`localisedRotatedAnharmonic_energy_coord` (`⟨L∘A⟩_loc = ∑ᵢ ⟨ℓᵢ⟩_loc,i`) and the trace identity
`½tr(tH(tH + gI)⁻¹) = ½∑ᵢ tλᵢ/(tλᵢ + g)`.

### A. The localised energy to second order (1D)

`|t⟨ℓ⟩_loc − ½ − e₁/t| ≤ K/t²` with
`e₁ = (a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³) = e₀ + (a² − g)/(2λ) − aα/(2λ²)`.

Route. `t⟨ℓ⟩_loc = (λ/2)·t⟨x²⟩_loc + (α/6)·t⟨x³⟩_loc + (γ/24)·t⟨x⁴⟩_loc` and `⟨f⟩_loc = ⟨fφ⟩/D`.
1. Second moment to second order: `x²φ = x² + ax³ + p₃x⁴ + p₄x⁵ + R` with `p₄ = a³/6 − ag/2` (tide 72's `locP₄`) and
   `|R| ≤ E₆x⁶ + E₈x⁸ + E₁₀x¹⁰` (the degree-6,7,8 monomials of `x²·(y²/2 + y³/6)` bounded by `|x|⁷ ≤ (x⁶ + x⁸)/2`, plus
   `x²·|R₄|` with `|R₄| ≤ (e^M + 4)|y|⁴ ≤ 16(e^M + 4)(a⁴x⁴ + (g/2)⁴x⁸)`). Hence
   `t⟨x²φ⟩ = 1/λ + n₂/t + O(t⁻²)`, `n₂ = B₂ + ac₃ + 3p₃/λ²` (the `p₄x⁵` term is `O(t⁻²)` by `fifthMoment_lead`), and by
   `ratio_key` with `c = 1/λ`: `t⟨x²⟩_loc = 1/λ + (n₂ − d₁/λ)/t + O(t⁻²)`.
2. Third moment at leading order with rate: `x³φ = x³ + ax⁴ + x³y²/2 + x³R₃`; `x³y²/2 = (a²x⁵ − 2a(g/2)x⁶ + (g/2)²x⁷)/2` with
   `x⁵` *signed* (`fifthMoment_lead`), `x⁷` by `(x⁶ + x⁸)/2`, and `|x³R₃| ≤ (e^M + 3)|x|³·8(|a|³|x|³ + (g/2)³x⁶) ≤ C(x⁶ + (x⁸ + x¹⁰)/2)`.
   So `|t²⟨x³φ⟩ − (c₃ + 3a/λ²)| ≤ K/t`, and dividing by `D = 1 + O(1/t)`: `|t²⟨x³⟩_loc − (c₃ + 3a/λ²)| ≤ K/t`.
   (Tide 69's `locCubic_pointwise` used the *first*-order expansion `x³(φ − 1 − ax)` bounded by absolute powers, which gives only
   `|t⟨x³⟩_loc| ≤ K/t`; the signed `x⁵` is what upgrades it to a coefficient.)
3. Fourth moment at leading order with rate: `x⁴φ = x⁴ + ax⁵ − (g/2)x⁶ + x⁴R₂`, `|x⁴R₂| ≤ (e^M + 2)x⁴y² ≤ C(x⁶ + x⁸)`; so
   `|t²⟨x⁴φ⟩ − 3/λ²| ≤ K/t` and `|t²⟨x⁴⟩_loc − 3/λ²| ≤ K/t`.
4. Assemble: `t⟨ℓ⟩_loc − ½ − e₁/t = (λ/2)(t⟨x²⟩_loc − 1/λ − c₂'/t) + (α/6)(t²⟨x³⟩_loc − c₃ − 3a/λ²)/t + (γ/24)(t²⟨x⁴⟩_loc − 3/λ²)/t`
   with `c₂' = n₂ − d₁/λ`, and `e₁ = (λ/2)c₂' + (α/6)(c₃ + 3a/λ²) + (γ/24)(3/λ²)` — a closed-form identity (`energy_loc_coeff`)
   checked by sympy: equals GPT's bracket.

Rationale: the direct follow-up GPT asked for in tide 69 ("the coefficient is a natural follow-up, not a small algebraic corollary");
all inputs exist, the only new pointwise envelopes are the `x²φ`, `x³φ`, `x⁴φ` expansions, each a copy of tide 72's pattern.

### B. E2: the localised LLC to second order, and the residual against the trace prediction

`|t⟨L∘A⟩_loc − d/2 − (∑ᵢ e₁,ᵢ)/t| ≤ K/t²` with `e₁,ᵢ` the coefficient of A for the `i`-th frame oscillator (`aᵢ = g u₀ᵢ`, `u₀ = Qᵀ(w₀ − c)`),
by `localisedRotatedAnharmonic_energy_coord` and a finite sum (`sum_rate_div_sq`). Corollary: since
`½tr(tH(tH + gI)⁻¹) = d/2 − (g/2)∑ᵢ 1/λᵢ · 1/t + O(t⁻²)`,
`t⟨L∘A⟩_loc − ½tr(tH(tH + gI)⁻¹) = [∑ᵢ (e₀,ᵢ + aᵢ²/(2λᵢ) − aᵢαᵢ/(2λᵢ²))]/t + O(t⁻²)`:
E3's trace prediction captures exactly the `−g/(2λᵢ)` part of the localiser's effect; the rest of the `1/t` term is the
unlocalised anharmonic correction `e₀,ᵢ` plus the anchor-displacement terms `aᵢ²/(2λᵢ) − aᵢαᵢ/(2λᵢ²)`.

### C. The sign question of tide 69, at first order (1D corollary of A)

`e₁ − e₀ = (a² − g)/(2λ) − aα/(2λ²)` (pure algebra, `energy_loc_coeff_sub`). At the anchor at the minimum (`x₀ = 0`, so `a = 0`)
this is `−g/(2λ) ≤ 0`: localisation lowers the exact energy's `1/t` term by exactly the amount the Gaussian trace prediction
says (`½tλ/(tλ + g) = ½ − g/(2λt) + O(t⁻²)`), so at `x₀ = 0` the residual `t⟨ℓ⟩_loc − ½tλ/(tλ + g) = e₀/t + O(t⁻²)` is the
*unlocalised* anharmonic correction. For `a ≠ 0` the displacement adds `a²/(2λ) − aα/(2λ²)`, which is the `1/t` coefficient of
the exact Gaussian anchored energy `tλg²x₀²/(2(tλ + g)²)` (GPT, tide 69) corrected by the cubic cross term `−aα/(2λ²)`.
Statement: `∃ K T, ∀ t ≥ T, |t⟨ℓ⟩_loc − t⟨ℓ⟩ − ((a² − g)/(2λ) − aα/(2λ²))/t| ≤ K/t²` needs the *unlocalised* energy to second
order with a `K/t²` remainder — `energy_anharmonic_order1_rate` has only `K/(t√t)` (it uses `secondMoment_anharmonic_order2_rate`);
re-deriving it with `secondMoment_anharmonic_order3_rate` + `thirdMoment_lead` + `fourthMoment_lead` is ~40 lines
(`energy_anharmonic_order1_rate_sharp`) and would also sharpen the seabed's E2 `4.76` statement to `O(t⁻²)`.

Proposed bundle: A + B + C (C's sharpened unlocalised energy is cheap and independently useful). Line estimate ~700–800.

Numerical check: sympy expansion in `ε = 1/√t` with the localiser inside the perturbation gives `t⟨ℓ⟩_loc = ½ + 0·ε + e₁ε² + …`
with `e₁` exactly the formula above (both the direct bracket and the moment-route `(λ/2)c₂' + (α/6)(c₃ + 3a/λ²) + γ/(8λ²)`);
quadrature at `λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`: `t(t⟨ℓ⟩_loc − ½) = −0.3179, −0.3438, −0.3510, −0.3528, −0.3532` at
`t = 10, 40, 160, 640, 2560` vs `e₁ = −0.35338`; `t(t⟨ℓ⟩_loc − ½tλ/(tλ+g)) → −0.04561` vs predicted `e₁ + g/(2λ) = −0.04569`
(tide 69's `−0.045`); `e₀ = −0.034896`, `e₁ − e₀ = −0.318485 = (a² − g)/(2λ) − aα/(2λ²)`.
