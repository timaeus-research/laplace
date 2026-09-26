# Research round 66: the response geometry is complete to all orders — what is the deepest remaining theorem?

## Landed since round 65 (laplace `Laplace/Multi/*`, sorry-free, pushed)
- **AtlasJetL1**: pairing CLM `obsL1` with `|⟨F,d⟩| ≤ ‖F‖∞‖d‖₁`; `L¹` duality (an element is determined by its pairings with
  bounded observables); `p'(s) = [q_{M_s} ℓ_{M_s,δ}]` on the interior atlas domain, `p''(s) = [q_{M_s} N_{M_s}(ℓ_s²)]` on `(0,1)`
  (density-acceleration in `L¹` by duality); `L¹` Taylor remainder `‖p(s) − Σ_{k≤n} s^k/k! p^{(k)}(0)‖₁ ≤ C s^{n+1}/n!` on
  `[0,1]` and the observable-uniform featureless expansion.
- **FeaturelessJet**: `p(0) = [1]`, `p'(0) = [ℓ]`, `p''(0) = [N(ℓ²)]` (uniqueness of Peano coefficients: TV Peano composed with
  `s ↦ sδ` vs `taylor_isLittleO`); explicit second-order featureless expansion
  `|E_{Q_{M_s}}F − (E_νF + s E_ν[Fℓ] + ½s² E_ν[(NF)ℓ²])| ≤ ‖F‖∞ C s³/2`.
- **ResponseHessian**: at every interior `M`, `z ↦ [q_{M+z}]` is `C^∞` on the open set of interior displacements;
  `D²P_M[u,v] = [q_M N_M(ℓ_uℓ_v)]` (diagonal by line-Peano uniqueness, general direction by rescaling, off-diagonal by
  polarisation + symmetry); `∫ F D²P_M[u,v] = b_F(u,v)`; the Hessian has zero mass and zero feature moments.
- **CurvedTransport**: `DP` and `D²P` at every interior displacement (translation invariance); for a `C²` interior path
  `M_t = M + γ(t)`: `d²/dt²[q_{M_t}] = [q N(ℓ_{γ'}²)] + [q ℓ_{γ''}]` and `∫ S d²/dt²[q_{M_t}] = γ''`.
- **SmoothNormalForm**: `M ↦ [q_M]` is `C^∞` on `Ω`, `R` is `C^∞` on the data space, `Φ`/`Ψ` are `C^∞` mutually inverse
  bijections `U ≃ Ω × K` with `R ∘ Ψ = p ∘ fst` (`smooth_normal_form`).
- Round 64/65 earlier: FibreOrthogonality (KL splitting against every family member, information projection, Fisher
  orthogonality at the section), NormalForm, ResponseChernoff, SmoothFamily, SmoothChart, InvisibleTower, plus rounds 61–63.

## Not landed
- `p'''(0) = [N(ℓ³ − 3ℓr)]` and the cumulant/Bell recursion for the tower.
- Analyticity (contraction + majorant for the inverse mean map).
- Boundary completion (finite `X`).
- Reconstruction CLT.

## The user's direction (verbatim, still the target)
"make sure we are tackling core features of the change in posterior expectation values with the change in the data
distribution that allow us to 'map' the space of responses across the data manifold (ideally, all the way from the
'featureless' distribution of maximal entropy to our actual data distribution). What would it take to do this with
maximum beauty and depth?"

## Questions
1. The response map is now: a `C^∞` retraction of the data manifold with explicit invisible Hessian, smooth global normal
   form `U ≃ Ω × K`, KL-orthogonal fibres, `C^∞` transport along any interior path with the bending/acceleration split,
   featureless expansion with observable-uniform remainder and explicit coefficients to second order, sampling bias =
   averaged bending, Chernoff cost of the response, Euler identities and the tilt diagnostic. What is the deepest remaining
   theorem for the user's direction? Rank ≤ 5 with precise statements and seabed-level routes. Our candidates:
   (a) the explicit third jet `p'''(0) = [N(ℓ³ − 3ℓr)]` (route: differentiate `atlasHess` along the atlas; the seabed has
   `hasDerivAt_atlasVel_coe` (`v' = atlasAccel = −bend`), `hasDerivAt_score_atlas`, `hasDerivAt_famDens_deriv_atlas`; we would
   need the derivative of `s ↦ N_{M_s}(ℓ_s²)`, i.e. of the normal projection operator along the atlas — is there a clean
   formula `d/ds N_{M_s} f = −(regression-derivative terms)` making the third jet a short computation, or is the projected
   shortcut `p''' = [N(ℓ³ − 3ℓr)]` best proved by another Peano-uniqueness argument with a third-order TV Peano expansion
   (which we do NOT have; the seabed's TV Peano is second order)?
   (b) the featureless expansion as a genuine analytic object: is there a cheap route to `∃ ρ > 0, p is real-analytic on
   ‖z‖ < ρ` (e.g. `θ ↦ [e^{−⟨θ,S⟩}]` is entire in `L¹` — the exponential series converges absolutely since `S` is bounded;
   `Z(θ)⁻¹` analytic; then the inverse mean map by a majorant series — which Mathlib pieces exist: `HasFPowerSeriesOnBall`
   for `exp`, composition `HasFPowerSeriesAt.comp`, inverse `FormalMultilinearSeries.comp`/`leftInv`? Is there an analytic
   inverse function theorem in current Mathlib (`HasFPowerSeriesAt.hasFPowerSeriesAt_localInverse`?) — we cannot recall it
   confidently, please say what you believe exists and how to check);
   (c) the global statement along the whole atlas from `m₀` to `M_D`: uniform constants — e.g. a bound on the `L¹` Taylor
   constant `C` in terms of the feature bound `B`, `‖M − m₀‖` and the Fisher information along the atlas, making the
   featureless expansion quantitative;
   (d) the boundary: for finite `X` (positive reference weights) the response map extends continuously to the closed
   moment polytope with the face structure (`FaceCompletion`?); the seabed already has boundary-regime material
   (`BoundaryCompletion`, `BoundaryTaylor`, `ZeroScaleCertificate`) — what would be the clean theorem tying the interior
   `C^∞` picture to the boundary?
   (e) something we are missing that is more central to "posterior expectation values as a function of the data
   distribution" — e.g. an intrinsic characterisation of `R` (the unique `C¹` retraction of `U` onto the family that is
   m-affine / KL-orthogonal), or a "Gauss–Bonnet"-type global identity along the atlas relating accumulated invisible
   curvature to the endpoint information (we have `KL(D_s‖ν) = 𝓘_s + R_s + L_s` from CurvatureSplit and the Euler
   identities).
2. Sanity: any overclaims in the landed statements as described (in particular `fderiv_fderiv_reconstructionL1_add` stated
   with Mathlib's global `fderiv` at points where `P` is only locally smooth, and the curved-path theorem assuming
   `∀ t, M + γ t ∈ Ω`)?
Answer in ≤ 3000 words.
