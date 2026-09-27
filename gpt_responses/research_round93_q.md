# Round 93 — programme C (mixture geometry and response fibres) is essentially complete; what next?

You are Astra, research advisor on the Lean formalisation (laplace seabed, `Laplace/Multi/*`) of the germbij note on
the response map over the data manifold. Since round 92 the following landed (all sorry-free; conventions unchanged:
`Pfam θ = ν.tilted(−⟨θ,S⟩)`, `responseOf g = θr(E_{ν.tilted g} S)`, `A_g = CDE (Φ g)` = the chart derivative = minus the
covariance operator, `responseVel = A⁻¹ Cov_ρ(S,k)`, `responseHess = A⁻¹(B − T(V,V))`):

- C0 `ResponseDataTaylor`: `contDiff_responseOf_add` (the response along `g + tk` is `C^∞`), **`responseOf_add_taylor_two`**
  `Φ(g+tk) − Φ(g) − tV − t²/2 H = o(t²)` (via Mathlib's `taylor_isLittleO_univ`).
- C1 `ResponseMixtureCoordinates`: `localMixTilt g k t = g + log(1 + t k̄)`, **`integral_localMixTilt`** (`E_{ρ_{g^m(t)}} f =
  E_{ρ_g} f + t Cov_{ρ_g}(f,k)` exactly for small `t`), `mean_localMixTilt`; endpoint mixture tilt `mixTilt g h t =
  log((1−t)e^g/Z_g + t e^h/Z_h)` with **`integral_mixTilt`** (law `(1−t)ρ_g + tρ_h`), `mean_mixTilt`.
- C2 `ResponseGlobalFibres`: **`responseOf_eq_iff`** (`Φ g = Φ h ↔ E_{ρ_g}S = E_{ρ_h}S`), **`responseOf_mixTilt_of_eq`**
  (fibres convex under mixing), `modelTilt θ = −⟨θ,S⟩`, **`responseOf_modelTilt`** (section), **`responseOf_mix_model`** +
  `integral_mix_model` (retraction of the fibre onto `P_{Φ(g)}` along `(1−t)ρ + tP_{Φ(ρ)}`), `responseOf_eq_iff_tiltedMean_eq_meanMap`.
- C3 `ResponseMixtureConnection`: `responseOf_localMixTilt_eq` (`Φ(g^m(t)) = θ(M(g) + tF)`), `mixResponseVel` (`A_{θ_t}⁻¹ F`),
  **`eventually_hasDerivAt_responseOf_localMixTilt`**, **`hasDerivAt_mixResponseVel`** (`v_m' = −A⁻¹T(v_m,v_m)`).
- C4 `ResponseEMAccelerationGap`: **`responseHess_sub_mixResponseAccel`** (`H_g(k,k) − a_m = A⁻¹B_g(k,k)`),
  `responseHess_add_mConnection` (bilinear), `responseHess_eq_mixResponseAccel_iff` (iff `B = 0`),
  **`eventually_responseOf_localMixTilt_of_invisible`** (invisible directions integrate to straight lines in a fibre).
- C5 `ResponseSliceSubmersion`: augmented slice `Ψ(z,u) = Φ(g + Σz_ik_i + hor_g u)` on `(ι → ℝ) × W`, `contDiff_augSlice`,
  **`fderiv_augSlice_zero`** (`DΨ(0,0)[ξ,w] = DΦ_g[⟨ξ,k⟩] + w`), `augDerivEquiv` (invertible derivative of `Ξ(z,u) = (z,Ψ)`,
  explicit inverse), **`hasStrictFDerivAt_augChart`**, `fibreSection σ` with **`eventually_augSlice_fibreSection`**
  (`Ψ(z,σ(z,θ)) = θ`), **`eventually_fibreSection_augSlice`** (`σ(z,Ψ(z,u)) = u`), `fibreSection_base`,
  **`contDiffAt_fibreSection`**, `hasStrictFDerivAt_fibreSection` (`(ξ,η) ↦ η − DΦ_g[⟨ξ,k⟩]`).
- C6 `ResponseFibreSecondJet` NOT done. Obstacle: the seabed's coefficient-journey lemmas (`hasDerivAt_responseVel_coeff`,
  `hasDerivAt_coeffVel`) require GLOBAL hypotheses `∀ t, HasDerivAt a (a' t) t`, `Continuous a'`, while the fibre section
  is only `C^∞` near the base. Planned route: extend `σ₀(z) := σ(z, Φ g)` by a smooth bump (`ContDiffBump`) to a global
  `C^∞` map agreeing near `0`, take `a(t) := (1, augCoeffL (tξ, σ̃(tξ)))`, and read off from the constancy of
  `Φ(g + ⟨a(t), k'⟩)` that `0 = DΦ_g[hor(σ₀''[ξ,ξ])] + H_g(Kξ,Kξ)`, hence `σ₀''[ξ,ξ] = −H_g(Kξ,Kξ) = −A⁻¹B_g(Kξ,Kξ)`.

Slop-note paragraphs exist for all landed modules. The user's standing directive: keep formalising, prioritising NEW
MATHEMATICS with "maximum beauty and depth" on the theme "mapping the space of responses across the data manifold, from
the featureless law to the actual data distribution". Please define the next programme (six modules).

## Candidates
D1. **Model Fisher geometry in natural coordinates** (your round-92 remark): the Levi-Civita connection of the Fisher
metric `G_θ(u,v) = Cov_{P_θ}(L_u, L_v)` on `W` in natural coordinates, Christoffel symbols `½ A⁻¹ T`-type from the third
cumulant (since `G = −D(mean)` is a Hessian metric, `Γ = ½ G⁻¹ ∂G` with `∂G` the third cumulant), and the curvature
tensor expressed quadratically in `T` and `G⁻¹` (fourth derivatives cancel); then the e-/m-/Levi-Civita triple
(dual connections, `∇^{LC} = ½(∇^e + ∇^m)`) with `∇^e` flat in natural coordinates (trivial) and `∇^m` flat in mean
coordinates (we have the mean-affine journeys). Which of this is provable without a manifold/connection API — as
statements about second derivatives of journeys and a symmetric-bilinear "Christoffel" operator on `W`?
D2. **First variation of response length** for a two-parameter family `g(t,ε)`: `L(ε) = ∫ √G_{g(t,ε)}(∂_t g, ∂_t g) dt`,
`L'(0) = ∫ (∂_ε P)/(2√P) dt` with `∂_ε P` from `pullbackVar` + the Hessian (positive-speed hypothesis; differentiation
under the integral on a compact interval).
D3. **C6 as above** (fibre graph Hessian), plus the mixed-slot version and the "no intrinsic second fundamental form"
caveat.
D4. **Topology of the fibre retraction**: continuity of `t ↦ ρ ↦ (1−t)ρ + tP_{Φ(ρ)}` in a suitable topology on bounded
tilts (sup norm? `L¹` of densities?) making the fibres strong deformation retracts and the quotient theorem topological.
D5. **Finite-range global topology**: `meanExt : Ŵ → conv V` bijective (landed) — is it a homeomorphism (compactness of
`Ŵ`)? Previously deferred; is there now a route via the face stratification + face embeddings?
D6. **Journeys from the featureless law to the data law with prescribed response trajectory**: given a `C²` path
`θ(t)` in `W` from `0` to `Φ(D)`, construct a data journey `g(t)` (bounded tilts) with `Φ(g(t)) = θ(t)` exactly —
horizontal lift of a path (ODE `g' = hor_{g}(θ')` in `bddSpace`; Picard–Lindelöf in a Banach space of bounded
functions; or the explicit choice `g(t) = modelTilt(θ(t))` which is trivial!). Is there a NON-trivial lifting theorem:
lifts through a prescribed starting law `g(0) = g₀` not in the family (the horizontal lift ODE), with existence on
`[0,1]` needing a bound on `hor`?
D7. Anything deeper you see.

## Questions
Q1. Rank D1–D7 by depth × reachability; one paragraph each.
Q2. For the top two, six modules total: name, one-line deliverable, exact Lean-flavoured statement in the seabed's
conventions, proof route, existing declarations. Flag anything you are not sure is true.
Q3. Headline theorem (one displayed formula) and how it continues the story: first order = Fisher form/submersion,
second order = Hessian/e-m gap, fibres = fixed-moment convex sets.
Be concrete; end with the ranked list of six modules to formalise next.
