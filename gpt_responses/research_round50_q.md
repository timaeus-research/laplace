# Research consult, round 50: mapping the space of responses across the data manifold

You are advising a Lean 4 / Mathlib formalisation ("seabed") of a note on posterior response maps. The
user's standing direction, verbatim:

> "Continue, but make sure we are tackling core features of the change in posterior expectation values
> with the change in the data distribution that allow us to 'map' the space of responses across the data
> manifold (ideally, all the way from the 'featureless' distribution of maximal entropy to our actual data
> distribution). What would it take to do this with maximum beauty and depth?"

## Setting (all formalised, sorry-free)

Sample space `X`, featureless posterior `ν` (probability measure), bounded measurable statistics
`S : J → X → ℝ` (`J` finite). Affine family `P_θ ∝ e^{−⟨θ,S⟩} ν`, mean map `m(θ) = E_{P_θ} S`,
cumulant `Λ(q) = log E_ν e^{⟨q,S⟩}`, rate `𝓘(M) = sup_q ⟨q,M⟩ − Λ(q)` (ℝ≥0∞-valued),
moment body `K = closure(convexHull(essRange))`, direction space `𝕍 = dir(affineSpan K)`,
`range m = relint K`, chart `θ ↦ m(θ)` is a C¹ diffeo of `𝕍` onto `relint K` with derivative the
covariance operator; `D_M 𝓘[u] = −⟨θ(M),u⟩` on `𝕍`.

Response projection `Π(M)`: for finite-rate `M`, the unique probability law with `E S = M` and
`KL(Π(M)‖ν) = 𝓘(M)`, Pythagorean: `KL(ρ‖ν) = KL(ρ‖Π(M)) + 𝓘(M)` for every `ρ ≪ ν` with mean `M`.
On the relint, `Π(M) = P_{θ(M)}`; on the boundary, `Π(M)` is the tilt of the face measure (exposed
chains).

Data law `D ≪ ν`, `M_D = E_D S`. Bridge `D_s = (1−s)ν + sD`, `E_{D_s} S = M_s = m_0 + s(M_D − m_0)`
(the straight atlas path in response space; `m_0 = m(0)`), so the projection of the bridge is the atlas
path `Π(M_s)`. Along it (relint case): `θ_s = θ(M_s)` is C¹, `𝓘(M_s) = ∫_0^s (s−u) κ(u) du` with
`κ(u) = Var_{P_{θ_u}}⟨v,S⟩`, `v = M_D − m_0`; exact tail `KL(Π(M_D)‖Π(M_s)) = ∫_s^1 (1−u) κ(u) du`;
boundary escape `‖θ_s‖ → ∞` as `s → 1` when `M_D` is on the boundary, with the normalised θ
converging into the normal cone; fixed-normal limits: `P_{θ + t u}` → tilt of the face measure.

Observables: `F_φ(s) = E_{P_{θ_s}} φ`, `F'(s) = Cov(φ, ⟨v,S⟩)`, `F''(s) = third central moment
T(r_φ, ⟨v,S⟩, ⟨v,S⟩)` where `r_φ` is the residual of `φ` after regressing on `S` (frozen residual trick);
Fréchet derivative of `M ↦ E_{Π(M)} φ` on relint = `Cov(φ,S) Σ⁻¹` (obsMapDeriv).

Invisible information: statistic lift `D↑ = ν.withDensity (x ↦ d(S_*D)/d(S_*ν)(S x))`, with
`dD↑/dν = ν[dD/dν | σ(S)]`, `S_*D↑ = S_*D`, tower law, and the three-way split
`KL(D‖ν) = KL(D‖D↑) + KL(S_*D‖S_*ν)`, and for finite rate
`KL(D‖ν) = 𝓘(M_D) + KL(D‖D↑) + KL(S_*D ‖ S_*Π(M_D))`
(fibre information L + marginal-invisible information). Along the bridge: `D_s↑ = (1−s)ν + sD↑`,
`L_s ≤ s L_1` (joint convexity of KL, `klDiv_mixture_mixture_le`), convexity of `s ↦ L_s`,
mixture compensation `a KL(P_0‖ν) + b KL(P_1‖ν) = KL(Q‖ν) + a KL(P_0‖Q) + b KL(P_1‖Q)`,
`genRate` strictly convex on finite-rate segments. Empirical: `M̂_n = (1/n)∑ S(X_i) → M_D` a.s.,
`KL(Π(M̂_n)‖Π(M_D)) → 0` a.s. (interior). Legendre closure: `Λ(q) = ⟨q,m(−q)⟩ − 𝓘(m(−q))`,
attained only at `m(−q)`. Variational Fisher: `Cov(⟨e,S⟩,⟨−v_s,S⟩) = ⟨e,v⟩` and
`κ(s) ≤ E (⟨v,S⟩ − c)²` etc.

Mathlib pieces available: `InformationTheory.klDiv`, `Measure.tilted`, `condExp`/`condExpL1`,
`rnDeriv`, `Measure.map`, `intrinsicInterior`, `ConvexOn.continuousOn_interior`, `strong_law_ae_real`,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, Gaussian measures, `MeasureTheory.Lp` with inner
product, `orthogonalProjection` in Hilbert spaces, `condExpL2`.

Remaining from your round-49 ranking: (2) nested Fisher projections in L²: `φ ↦ E[φ|σ(S)] ↦` best linear
predictor in `span{1,S}`, three-way Pythagoras `E(φ−a−⟨b,S⟩)² = E(φ−E[φ|S])² + E(E[φ|S]−a−⟨b,S⟩)²`;
(3) second-order expansions of fibre / marginal / total residual along tilt paths; (4) conditional
variational formula `L = sup_g { E_D g − log E_{D↑} e^g }` over bounded tests, restricted forms.

## Questions

1. Against the user's direction, what is the *deepest and most beautiful* formulation of "mapping the
   space of responses across the data manifold from the maximal-entropy ν to D" that this seabed can
   reach? In particular: is the bridge `D_s` (m-geodesic in the full simplex) versus the e-geodesic
   `P_{sθ_D}` versus the atlas path `Π(M_s)` the right triangle of paths, and which exact identities
   between them (Pythagorean along paths, the "information geometry of the projection of a straight line",
   area/curvature terms, the fibre information as the defect) are the core statements to formalise?
   Please give precise statements.
2. What are the core features of *change in posterior expectation values with change in data* that are
   still missing? E.g. (a) `s ↦ E_{Π(M_s)} φ` versus `s ↦ E_{D_s} φ = (1−s)E_ν φ + s E_D φ` (linear!):
   the gap between the projected and the actual observable path, its exact expression via the fibre and
   marginal residuals, its derivatives at s=0 (susceptibility) and s=1; (b) a "response Jacobian" theory:
   the map `M ↦ E_{Π(M)} φ` for all bounded φ as a map into the dual, its derivative
   `Cov_{Π(M)}(φ,S)Σ⁻¹`, second derivative, and the transport equation for expectation values along the
   atlas path (a Fokker–Planck/heat-flow type PDE in θ? the Legendre duality between θ and M?);
   (c) maximum-entropy characterisation of ν itself as s=0 endpoint and what "distance travelled"
   `𝓘(M_D)` vs `KL(D‖ν)` means: state the exact decomposition of `KL(D‖ν)` into the integral of the
   curvature along the atlas path plus the two residual terms; (d) anything else that makes the picture
   *complete* (e.g. a Hilbert-space/L² lift: the tangent space at each point of the path, the Fisher metric
   pulled back, the "process energy" ∫ κ as a length functional and its minimality/uniqueness).
3. Rank 6–8 concrete formalisable theorems (within ~150–400 Lean lines each, given the infrastructure
   above) by depth × feasibility, each with: exact statement, proof sketch, the seabed/Mathlib lemmas to
   use, and pitfalls (e.g. where relint is needed, ℝ≥0∞ vs ℝ issues, where bounded observables suffice).
4. Say explicitly which of the round-49 leftovers (2), (3), (4) are worth doing now versus dropping.

Be concrete and mathematical; Lean-flavoured statements welcome. Do not repeat the setting back.
