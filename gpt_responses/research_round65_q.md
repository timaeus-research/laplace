# Research round 65: the response calculus exists to all orders — what is the deepest remaining theorem?

## Landed since round 64 (laplace `Laplace/Multi/*`, sorry-free, pushed)
Round-64 ranks 1–4 are all landed, plus the all-orders tower in `L¹`:
- **FibreOrthogonality** (rank 2): `KL(ρ‖Q_θ) = KL(ρ‖Q_M) + KL(Q_M‖Q_θ)` for every family member (`klDiv_split_family`,
  via three tilted-reference formulas), information projection + uniqueness, `∫ ℓ_{M,u} k dν = 0` for invisible `k`,
  `DR_{q_M}[q_M φ] = [q_M B_M φ]` (the retraction differential at the section is the regression projection), orthogonal
  splitting `E_Q φ² = g(c_φ,c_φ) + E_Q(φ − B_M φ)²`.
- **NormalForm** (rank 1): `Φ(d) = (m(d), d − p(m(d)))`, `Ψ(M,k) = p(M) + k`, mutually inverse bijections
  `U ≃ Ω × K` (`U` = unit mass + interior response, `K` = zero mass + zero feature moments), both differentiable within their
  domains with the stated derivatives, `R(Ψ(M,k)) = p(M)`, `Φ(R d) = (m d, 0)`.
- **ResponseChernoff** (rank 4): `𝓘(M) = −⟨θ(M),M⟩ − Λ_ν(−θ(M))` and `ν^{⊗n}(⟨θ(M), R̄_n⟩ ≤ ⟨θ(M), M⟩) ≤ e^{−n𝓘(M)}` (the
  seabed already had `halfspace_chernoff`, `HalfspaceProjection`, `CompactCoverCramer`).
- **SmoothFamily** (rank 3, stage A): `N_g(θ) = ∫ g e^{−⟨θ,S⟩}dν` is `C^n` for all `n` by induction over bounded `g`
  (`DN_g = −⟨·,(N_{gS_j})_j⟩` is of the same form); the mean map, its Jacobian, the intrinsic chart `chartV : 𝕍 → 𝕍`, the
  chart derivative and `θ ↦ (Dm(θ)|_𝕍)⁻¹` are `C^∞`.
- **SmoothChart** (rank 3, stage B): `U = range chartV = {v : m₀ + v ∈ Ω}` is open (IFT); `fderiv chartVInv = (Dm|_𝕍)⁻¹ ∘ chartVInv`
  on `U`, so the bootstrap `C^n ⇒ C^{n+1}` gives `chartVInv ∈ C^∞(U)`; hence `z ↦ θ(m₀ + z)` is `C^∞` on the interior
  displacements, `s ↦ θ(M_s)` is `C^∞` on the open interior atlas domain, and `s ↦ E_{Q_{M_s}}F` is `C^∞` for every bounded `F`.
- **InvisibleTower**: `θ ↦ [g e^{−⟨θ,S⟩}] ∈ L¹` is `C^∞` (quadratic remainder from `|e^{−u} − 1 + u| ≤ u²`, same induction), so
  `θ ↦ [q_θ]` is `C^∞` into `L¹(ν)` and `p(s) = [q_{M_s}]` is a `C^∞` curve in `L¹` on the interior atlas domain; every derivative
  `p^{(k)}(s)`, `k ≥ 2`, has zero mass and zero feature moments (`invisible_tower`), and `∫ S p'(s) = M − m₀`.
- Earlier this session: EmpiricalMoments, BiasForm, ReconstructionBias, ResponseTransport, InvisibleHump (non-monotone invisible
  information), PlugInCovariance, PlugInBias, InformationTaylor, InformationBias, TangentPythagoras, SecondOrderTransport,
  NaturalGradientAtlas, InvisibleQuadratic, UniformBias (F-uniform = `L¹` bias), ResponseGeometry (closing theorem + exact
  invisibility identity), DataRetraction (`R(d) = [q_{m(d)}]` is a differentiable retraction, `DR = Dp ∘ π m`, `ker DR` =
  invisible directions), TransportL1 (Bochner FTC), TiltDiagnostic (Euler identities `sA'−A = KL(ν‖D_s)`, `s𝓘'−𝓘 = KL(ν‖Q_s)`,
  `d/ds(R/s) = (KL(ν‖D_s) − KL(ν‖Q_s))/s²`).

## Not landed
- The explicit recursion for the tower (`v_k = −A⁻¹ Σ_{|π|≥2} K_{|π|}[…]`, Bell polynomials `P_k`); only the abstract smoothness
  and invisibility are formal.
- Curved-path second-order transport `q̈ = H[Ṁ,Ṁ] + J M̈` (now cheap in principle: `θ ↦ [q_θ]` is `C^∞` into `L¹` and the chart
  is `C^∞`, so `t ↦ [q_{M_t}]` is `C²` for any `C²` path `M_t` in `Ω`; the identification of the second derivative with
  `H[Ṁ,Ṁ] + JM̈` needs the second Fréchet derivative of `θ ↦ [q_θ]` and of `z ↦ θ(m₀+z)`).
- Analyticity (real-analytic dependence on `θ`; the analytic inverse function theorem is not available to us).
- A CLT for the reconstruction law (Mathlib status unknown to us).

## The user's direction (verbatim, still the target)
"make sure we are tackling core features of the change in posterior expectation values with the change in the data
distribution that allow us to 'map' the space of responses across the data manifold (ideally, all the way from the
'featureless' distribution of maximal entropy to our actual data distribution). What would it take to do this with
maximum beauty and depth?"

## Questions
1. With the response calculus now smooth to all orders and the normal form/dual foliation landed, what is the deepest
   remaining theorem for this direction? Rank ≤ 5 with precise statements and seabed-level routes. Our candidates:
   (a) the second Fréchet derivative of the response map on the data manifold and the curved-path transport
   `d²/dt² p(m(d_t)) = H_{M_t}[Ṁ_t,Ṁ_t] + J_{M_t} M̈_t` with `H_M[u,v] = [q_M N_M(ℓ_uℓ_v)]` as the honest Hessian of `p` (we have
   `atlasHess` only along affine atlases, and the observable-level `b_F`); this would make `R` a `C²` (indeed `C^∞`) retraction
   with an explicit invisible Hessian;
   (b) a "global" version of the closing theorem on the whole data manifold: `R : U → U` is `C^∞` (not just `C¹`) with the
   normal form `Φ` a `C^∞` diffeomorphism `U ≃ Ω × K` — is it worth the `C^∞` upgrade of `DataRetraction`/`NormalForm`
   (they are assembly from `contDiff_densL1` + `contDiffOn_responseTheta_add`)?
   (c) the analytic upgrade: `θ ↦ [q_θ]` and the mean map are real-analytic (bounded `S` ⇒ the exponential series converges in
   `L¹`); the inverse `θ(M)` analytic needs an analytic IFT — is there a route through the power series of the inverse
   (Lagrange inversion / `HasFPowerSeriesAt` composition) that Mathlib supports, or is this a dead end?
   (d) a theorem about the featureless → data path that uses the all-orders structure: e.g. the Taylor series of
   `s ↦ E_{Q_{M_s}}F` at `s = 0` in terms of cumulants of `ν` (the "featureless expansion": every coefficient a
   polynomial in the moments of `S` and `F` under `ν`), giving the response of any observable to data as an explicit
   perturbation series from maximal entropy — this seems closest to "mapping responses across the data manifold";
   (e) something we are missing.
2. For (d): what is the cleanest formal statement (e.g. `iteratedDerivWithin k (s ↦ E_{Q_{M_s}}F) D 0` as an explicit
   expression for `k = 1, 2, 3` in the cumulants `Cov_ν`, third central moments, and the inverse covariance `C⁻¹`), and does
   the seabed's `thirdOp`/`cumulantVec`/`atlasBend` already provide `k = 3`?
3. Sanity: any errors or overclaims in the landed statements as described (in particular `invisible_tower`, stated with
   `iteratedDerivWithin` on the open interior atlas domain, and the normal-form derivative statements)?
Answer in ≤ 3000 words.
