# Round 57: the response of the law in total variation landed — what is the deepest next step? (germbij / laplace)

Same programme as rounds 52–56 (bounded features `S`, featureless posterior `ν`, family `P_θ = e^{−⟨θ,S⟩}ν/Z`,
reconstruction `Π(M) = P_{θ(M)}` with density `q_M`, direction subspace `𝕍`, atlas `M_s = m₀ + sΔ`, response scores
`ℓ_{M,u} = ⟨R_M u, M − S⟩` with `R_M = Dθ(M) = −Σ_M⁻¹`, normal projection `N_M`, regression `B_M`, third-cumulant
operator `T_θ`). User direction unchanged and verbatim: "make sure we are tackling core features of the change in
posterior expectation values with the change in the data distribution that allow us to 'map' the space of responses
across the data manifold (ideally, all the way from the 'featureless' distribution of maximal entropy to our actual
data distribution). What would it take to do this with maximum beauty and depth?"

## Landed since round 56 (all sorry-free, on `main`; slop paragraphs pushed)

- `ResponseStructure`: the §7 structure theorem as a five-part conjunction (global chart, differential duality /
  dual-flat, normal geometry with polarised Hessian + Peano, accounting identity, boundary obstruction).
- `InformationAlongAtlas` (your information companion): `KL(D‖Q_s) = KL(D‖Π(M)) + ∫_s^1(1−t)κ_t dt`,
  `KL(D‖ν) = KL(D‖Π(M)) + ∫₀¹(1−t)κ_t dt`, antitone in `s`, `d/ds KL(D‖Q_s) = −(1−s)κ_s`.
- `ThetaPeano`: vector-valued generic Peano lemma; `θ(M+z) = θ(M) + R z − ½ R T_θ(Rz,Rz) + o(‖z‖²)` and
  `T_θ(Rz,Rz) = Cov_Q(S, ℓ_z²)` as an element of `𝕍`.
- `DensitySecondOrder`: POINTWISE-UNIFORM second order in natural coordinates: with
  `T_θ(η) = 1 + ⟨η, m−S⟩ + ½(⟨η,m−S⟩² − Var_θ⟨η,S⟩)` and `K = |J| sup‖S_j‖_∞`,
  `|p_{θ+η} − p_θ T_θ(η)| ≤ 13 (K‖η‖)³ p_θ` whenever `K‖η‖ ≤ 1/4` (scalar core: `|e^{−w} − (1−w+w²/2)| ≤ |w|³/4`
  and an explicit ratio lemma with constant 13).
- `DensityPeanoAlgebra` + `DensityPeano` (your rank-1 flagship, by the EXPLICIT route rather than dominated
  convergence): `famDens_response_peano`: `∃ φ = o(‖z‖²), ∀ᶠ z, ∀ x, |q_{M+z}(x) − q_M(x)(1 + ℓ_{M,z}(x) +
  ½N_M(ℓ_{M,z}²)(x))| ≤ φ(z) q_M(x)`; `isLittleO_integral_famDens_response_peano`: `∫|q_{M+z} − q_M − q_Mℓ_z −
  ½q_MN_M(ℓ_z²)| dν = o(‖z‖²)`. Route: `η = Rz + ζ`, `ζ = −½R Cov_Q(S,ℓ_z²) + v`, `v = o(‖z‖²)`; the truncation
  splits exactly at `Rz + ζ`; `½(ℓ_z² − Var_Qℓ_z) − ½B_M(ℓ_z²) = ½N_M(ℓ_z²)` since the affine score of the
  covariance vector is the regression part; remainder `φ(z) = 13(K(‖R‖+1)‖z‖)³ + K₂‖v(z)‖ + C‖z‖‖ζ(z)‖ +
  C'‖ζ(z)‖²` with thresholds `‖z‖ ≤ 1/(BK₂²‖R‖³+1)` (so `‖ζ‖ ≤ ‖z‖`) and `‖z‖ ≤ 1/(4K(‖R‖+1)+1)` (so `K‖η‖ ≤ 1/4`).

Not done: compact-uniform remainders; the boundary endpoint of the accounting identity; general (unbounded)
densities; anything "global" about `M ↦ Π(M)` as a map into total variation.

## Questions

1. Sanity-check the TV Peano as stated (in particular that the second derivative of `M ↦ Π(M)` as a TV-valued map is
   the signed measure `Π(M)·N_M(ℓ_z²)` and not `Π(M)·(ℓ_z² − Var)`; and that the pointwise-uniform RELATIVE form
   `≤ φ(z) q_M(x)` is genuinely stronger than the TV form — is there a standard name for it?).
2. Now that the law itself responds to second order in TV: what is the deepest remaining statement on "mapping the
   space of responses across the data manifold from ν to D" that the seabed can reach? Rank with reasons. Candidates:
   (i) ALL ORDERS: since `q_{M+z}/q_M = exp(−⟨θ(M+z)−θ(M), S⟩) Z(θ(M))/Z(θ(M+z))` and `θ` is real-analytic on `ri K`,
   is `M ↦ Π(M)` real-analytic into TV (or into the relative-uniform norm `sup_x |·|/q_M`)? What is the cleanest
   all-orders statement, and what would its Lean cost be given we have the explicit cubic bound (can the explicit
   route be iterated: `n`-th order truncation with remainder `C_n (K‖η‖)^{n+1} p_θ`)?
   (ii) COMPACT-UNIFORM: `sup_{M∈C} ‖z‖⁻² ∫|q_{M+z} − …| → 0` for compact `C ⊂ ri K`, via uniform continuity of
   `M ↦ (R_M, T_{θ(M)})` and a uniform Peano for `θ` (C² with continuous second derivative on a compact
   neighbourhood) — is Mathlib's `Convex.taylor_approx_two_segment` or a `HasFTaylorSeriesUpToOn` statement the
   right tool, or should we again go explicit?
   (iii) THE TV CURVE `s ↦ Q_s` along the atlas: `q_s' = q_s ℓ_s`, `q_s'' = q_s(ℓ_s² − κ_s + ⟨w_s, S − M_s⟩)`
   already landed pointwise; state the atlas as a `C²` curve in TV with `‖Q_s − Q_t‖_TV ≤ ∫_t^s √κ`-type bounds
   (Pinsker) and the second-order TV expansion along the path — is this more or less valuable than (ii)?
   (iv) BOUNDARY triangular endpoint: for `M` on the relative boundary with finite rate, `E_{Q_*}φ − E_νφ =
   lim_{t↑1}[t E_ν(φℓ_0) + ∫₀ᵗ(t−s)E_{Q_s}[φN(ℓ_s²)]ds]` under TV convergence `Q_t → Q_*`. Our interior Taylor is
   stated for interior `M` on `[0,1]`; for boundary `M` I plan the reparametrisation `M' = M_t` (interior), whose atlas
   is `s ↦ M_{st}` with scores `ℓ'_s = t ℓ_{st}`, giving the identity at `t` by the change of variables `u = st` — any
   pitfall? Which endpoint-convergence theorem should supply `Q_t → Q_*` (we have `FixedNormalLimit` for exposed
   faces with diverging tilts, `EndpointTail` `KL(Π(M)‖Q_s) = ∫_s^1(1−u)κ` for INTERIOR `M`, `BoundaryEscape`
   `‖θ(M_s)‖ → ∞`)? Is your Section-C statement (`(1−s)i'(s) → 0` at finite-rate boundary points, hence
   `KL(Q_*‖Q_s) = ∫_s^1(1−t)κ_t` and TV convergence by Pinsker) within reach with `genRate` lower semicontinuous
   and the mixture `(1−s)ν + sQ_*` — sketch the Lean route.
   (v) THE RESPONSE MAP ON THE SIMPLEX: `D ↦ M_D ↦ Π(M_D)`; the accounting identity is pathwise for fixed `D`;
   is there a statement about the DEPENDENCE ON `D` (e.g. `D ↦ Π(M_D)` is TV-Lipschitz? `‖Π(M_D) − Π(M_{D'})‖_TV ≤
   C‖M_D − M_{D'}‖ ≤ C'‖D − D'‖_TV` on compacts of `ri K` by the TV derivative) — "the reconstruction is a
   TV-Lipschitz retraction of the simplex onto the family" — is that the one-line statement of the whole map?
   (vi) anything else that would make the whole picture read as ONE theorem: from the featureless `ν` to `D` via the
   atlas in `ri K`, with responses of observables, laws, and information all controlled.
3. For your top two items: precise statements in the seabed's terms, lemma-level proof sketches, line estimates,
   and the specific pitfalls you foresee.
