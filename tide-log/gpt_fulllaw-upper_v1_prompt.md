# Context: laplace seabed, tide 114 (E8 full law, upper bound)

Tide 107 formalised, for the E8 full covariance law `X ↦ AXAᵀ + N + c∑ᵢDᵢXDᵢᵀ` (`A = I − hP`, `N = 2hI + h²t²C`, `Dᵢ = Hᵢ − H` the per-sample Hessian
deviations, `c = h²t²(1−m/n)/(m(n−1))`), existence/uniqueness of the fixed point `Σ_full` under the contraction hypothesis
`L := ‖A‖‖Aᵀ‖ + c∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖ < 1` in the `ℓ∞` operator norm (Banach), PSD-ness, `Σ_full ⪰ Σ^{mb}` (the additive fixed point), and the lower
bound `tr(HΣ_full) ≥ tr(HΣ^{mb}) + c·tr(HB(Σ^{mb}))`, `B(X) = ∑ᵢDᵢXDᵢᵀ` (one-step lower bound; you noted the exact first-order term is
`c·tr(H(1−T)⁻¹B(Σ^{mb}))`).

# Candidates (upper bounds)
A. `|Mᵢⱼ| ≤ ‖M‖`, `|tr M| ≤ d‖M‖`, `|tr(HX)| ≤ d‖H‖‖X‖` for the `ℓ∞` operator norm.
B. Banach a-priori estimate: `‖Σ_full − Σ^{mb}‖ ≤ dist(Σ^{mb}, f(Σ^{mb}))/(1−L) = c‖B(Σ^{mb})‖/(1−L) ≤ c(∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖)‖Σ^{mb}‖/(1−L)`, entrywise too.
C. `tr(HΣ_full) ≤ tr(HΣ^{mb}) + d‖H‖·c‖B(Σ^{mb})‖/(1−L)`, hence the two-sided LLC bound
   `LLC^{mb} + (t/2)c·tr(HB(Σ^{mb})) ≤ (t/2)tr(HΣ_full) ≤ LLC^{mb} + (t/2)d‖H‖c‖B(Σ^{mb})‖/(1−L)`.
D. The note's instance (`c = minibatchCoeff`): `‖Σ_full − Σ^{mb}‖ = O(h²t²/m)`.

Numerical check (3D, diagonal frame so that L = 0.9 < 1): `‖Σ_full − Σ^{mb}‖ = 1.7e-3 ≤ 4.6e-3 = c‖B‖/(1−L)`; LLC lower 3.81 ≤ full 3.86 ≤ upper 4.47.

# Questions
1. Are A–D correct? Is the `ℓ∞` operator norm the right (or at least a legitimate) norm here — the contraction hypothesis is norm-dependent
   and `‖A‖‖Aᵀ‖` can exceed 1 for a non-diagonal `A = I − hP` even when the iteration converges (spectral radius < 1). Should the note state the
   bound conditionally on `L < 1` and remark that a frame change (`A` diagonal in the eigenbasis of `P`, where `‖A‖ = max|1−hpᵢ| < 1`) removes the
   obstruction, i.e. apply the theorem to the conjugated law `UᵀXU`?
2. Cheaper or stronger: (i) a bound in terms of `tr` only, e.g. `tr(H(Σ_full − Σ^{mb})) ≤ ‖H‖·tr(Σ_full − Σ^{mb})` for PSD differences, avoiding `d`;
   (ii) the first-order identity `Σ_full − Σ^{mb} = c(1−T)⁻¹B(Σ_full)` and the resulting sharper `O(c²)` statement
   `‖Σ_full − Σ^{mb} − c(1−T)⁻¹B(Σ^{mb})‖ ≤ c²(…)`; (iii) the relative statement `‖Σ_full − Σ^{mb}‖/‖Σ^{mb}‖ ≤ cΣ‖Dᵢ‖²/(1−L)`.
3. Wording for the note's E8 paragraph: "the state-dependent (Hessian-fluctuation) correction to the stationary covariance is `O(h²t²/m)`,
   bounded above by `c∑ᵢ‖Hᵢ−H‖²‖Σ^{mb}‖/(1−L)` and below (in the LLC) by the one-step term" — fair, with what caveats (norm choice, finite-population
   coefficient, Gaussian identification)?
Vote please.
