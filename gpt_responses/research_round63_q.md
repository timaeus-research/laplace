# Research round 63: closing the response-map programme — what is left for depth?

## Landed since round 62 (laplace `Laplace/Multi/*`, sorry-free, pushed)
- **TangentPythagoras** (rank 2): `ψ_{F,M} = B_M F` (the influence function IS the regression part), tangent Pythagoras
  `E_Q(a−Ea)² = g_M(u,u) + E_Q(N_M a)²`, Riesz `E_Q[ψ_F ℓ_u] = lin_F(u)`, `Var_Q ψ_F = g_M(c_F,c_F)`, and the plug-in
  covariance limit in influence form `n Cov(Ĝ_F,Ĝ_G) → E_D[ψ_F ψ_G]`.
- **SecondOrderTransport** (rank 4): the seabed's `thirdCentral` second derivative along the atlas with the canonical regression
  coefficient equals the bias form, `(G_F∘M)''(s) = b_{F,M_s}(δ,δ) = E_{Q_s}[N F ℓ_δ²]`; Taylor with integral remainder
  `G_F(M_t) = G_F(m₀) + t lin_{F,m₀}(δ) + ∫₀ᵗ (t−r) b_{F,M_r}(δ,δ) dr` (integrability of the second derivative via
  `measurable_deriv` + a uniform bound, no continuity needed).
- **NaturalGradientAtlas** (rank 3): `L(M) = KL(Q_{M*}‖Q_M)` has `dL_M[u] = g_M(M − M*, u)`; the flow `M(τ) = m₀ + (1−e^{−τ})(M*−m₀)`
  solves `M' = −(M − M*)`, converges to `M*`, and `dL/dτ = −g_{M(τ)}(M−M*, M−M*)`.
- **InvisibleQuadratic** (rank 5): for `D = dν` bounded positive, `D_s = (1+s(d−1))ν`: `KL(D_s‖ν)/s² → ½E_ν(d−1)²`,
  `𝓘(m₀+sδ)/s² → ½g_{m₀}(δ,δ)`, `Cov_ν(S, d−1) = M_D − m₀`, and `R(s)/s² → ½‖N_{m₀}(d−1)‖²_{L²(ν)}`.
- Earlier this session: EmpiricalMoments, BiasForm (`N_M` self-adjoint), ReconstructionBias, ResponseTransport (chain rule/FTC,
  influence function, influence form along the affine path), InvisibleHump (three-point non-monotonicity), PlugInCovariance
  (sandwich), PlugInBias (schema), InformationTaylor + InformationBias (`n(E𝓘(M̂_n) − 𝓘(M)) → ½E_D g_M(S−M,S−M)`),
  `dataMoment_mixture_eq_atlasPath`.
- Also already in the seabed (older): `AtlasHessian`: pointwise `d²/ds² q_{M_s}(x) = atlasHess_s(x)` along the atlas,
  `∫ atlasHess dν = 0`, `∫ S atlasHess dν = 0`, `atlasHess = q · N_{M_s}(ℓ_δ²)` (`atlasHess_eq_normalProj`); `CurvatureSplit`:
  `KL(D_s‖ν) = 𝓘_s + R_s + L_s` as three accumulated curvature defects; `BridgeResidual`: `R` bridge moduli; `PathEnergy`,
  `AtlasEnergy`, `MixturePathEnergy`: the three straight paths and their weighted energies; exponential tilt paths with
  `hasDerivAt_genRate_dataPath`.

## Not landed
- Round-62 rank 1 flagship: full Fréchet `C²` of `M ↦ [q_M] ∈ L¹(ν)` with Hessian `q_M N_M(ℓ_uℓ_v)` (invisible signed measure)
  and the uniform-in-`F` signed-measure bias `n(E[q̃_n] − q_M) → ½ E_D[D²q_M[T,T]]` in `L¹`.
- Round-62 rank 6: `tR'(t) = R(t) + KL(ν‖D_t) − KL(ν‖Q_{M_t})` (we see: `t𝓘' − 𝓘 = KL(ν‖Q_{M_t})` is immediate from
  `toReal_klDiv_familyMeasure_symm` + `hasDerivAt_genRate_path`; `tA' − A = KL(ν‖D_t)` needs `d/dt ∫ klFun(1+th) = ∫ h log(1+th)`),
  and the tilt-path counterexample.

## The user's direction (verbatim, still the target)
"make sure we are tackling core features of the change in posterior expectation values with the change in the data
distribution that allow us to 'map' the space of responses across the data manifold (ideally, all the way from the
'featureless' distribution of maximal entropy to our actual data distribution). What would it take to do this with
maximum beauty and depth?"

## Questions
1. Given everything landed, what is the deepest remaining theorem for this direction? Rank ≤ 5 with precise statements and
   seabed-level routes. Our candidates: (a) the flagship `C²` — is there a cheaper "`C²` along every line through `M`"
   (directional Hessian `D²q_M[u,u]` for all `u ∈ 𝕍`, which the atlas machinery gives for `u = δ` by re-centring the atlas at
   `M`: `atlasPath` from `M` to `M + u` is a straight line inside the interior) that already yields the uniform-in-`F` signed
   bias via polarisation `D²q[u,v] = ¼(D²q[u+v,u+v] − D²q[u−v,u−v])`? (b) **transport of the whole reconstruction along a data
   path as a signed-measure curve**: `d/dt [q_{M_t}] = [q_{M_t} ℓ_{M_t,Ṁ_t}]` in `L¹` (we have the chain rule in `L¹` from
   `CurveLength`), and the "invisible acceleration" `d²/dt² [q_{M_t}] = [q N(ℓ²)]` with zero mass and zero feature moments —
   the density-level statement of "second-order bending is invisible"; (c) **a global map theorem**: the response map
   `D ↦ Π(E_D S)` restricted to bounded-density laws is `C¹` (in TV / `L¹`) with derivative `ḋ ↦ q_M ℓ_{M, E_ν[Sḋ]}`, i.e.
   the pushforward of a data tangent is its visible Fisher projection — the differential of the data→reconstruction map;
   (d) the **Fisher–Rao pullback**: `‖ḋ‖²_{pullback} = g_M(∫S dḋ, ∫S dḋ)` vs `‖ḋ‖²_{L²(D)}`, with the defect the normal part
   (the tangent Pythagoras in measure form); (e) **an all-orders statement along the atlas**: `G_F(M_s)` is smooth in `s` with
   `k`-th derivative given by cumulant-type expressions (the seabed has `thirdOp`, `cumulantVec`; is there a clean recursion
   `d/ds ℓ_δ = −g(δ,δ) − ℓ_{K(δ,δ)}` making the atlas derivatives of `q` a computable cumulant tower)?
2. For the flagship: is the polarisation route (a) sound and cheaper than the full Fréchet argument? What exactly must be
   uniform (compact-uniform Peano in the direction `u` over a neighbourhood) to conclude the `L¹` signed-measure bias
   `n(E[q̃_n] − q_M) → ½ E_D[D²q_M[T,T]]` from the scalar schema applied to every bounded `F`?
3. Is there a beautiful *closing statement* for the programme — a single theorem/picture ("response transport = visible Fisher
   projection; bending = invisible; sampling averages the bending; the atlas is the natural-gradient flow") that we could
   state and prove as a package from what is landed, to serve as the paper's main theorem? Propose its precise formulation.
Answer in ≤ 3000 words.
