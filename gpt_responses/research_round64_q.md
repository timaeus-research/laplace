# Research round 64: after the closing theorem — what remains for depth on the response map?

## Landed since round 63 (laplace `Laplace/Multi/*`, sorry-free, pushed)
- **UniformBias** (round-63 rank 1, dual form): the observable Taylor expansion with a modulus independent of `F`
  (`integral_response_peano_biasForm_all`), `|lin_F(u)| ≤ ‖F‖∞ ∫|ℓ_{πu}|`, `|b_F(u,v)| ≤ ‖F‖∞ ∫|N(ℓ_{πu}ℓ_{πv})|`, and
  `sup_{‖F‖∞≤1} |n(EĜ_{F,n} − G_F(M)) − ½ΣΓ_ab b_F(e_a,e_b)| → 0` (`reconstruction_bias_uniform_of_nhd`) = the `L¹`
  signed-measure bias `n(E q̃_n − q_M) → ½E_D[H_M[S−M,S−M]]`.
- **ResponseGeometry**: the exact non-asymptotic invisibility identity `∫ (1,S)(q_{M+h} − q_M − q_M ℓ_{M,h}) dν = 0`
  (`deviation_invisible`) and the five-part closing theorem `response_geometry` exactly in your round-63 form
  (projection/idempotence/`L¹`-differential/moment inverse; whole-law transport; invisible bending + exact invisibility;
  `F`-uniform averaged bending; natural-gradient atlas).
- **DataRetraction** (round-63 rank 2): `m : L¹(ν) → ℝ^J`, `d ↦ ∫ S d dν` as a CLM (`momentL1`); `R(d) = [q_{m(d)}]`
  (`dataRecon`); `m∘R = m`, `R∘R = R`; zero-mass directions have `∫ S h dν ∈ 𝕍` (`momentL1_sub_mem_dirSpan`, via the a.e.
  membership `S(x) − m₀ ∈ 𝕍` and `∫ f = ι P ∫ f`); on the fixed-mass affine subspace `R` is Fréchet differentiable with
  `DR_d[h] = Dp_{m(d)}(π ∫ S h dν)` (`hasFDerivWithinAt_dataRecon`); `DR∘DR = DR`; `ker DR = {∫ S h = 0}`; visible/invisible
  splitting `∫ S (h − DR h) = 0`; `‖DR h‖₁ ≤ √g(πh, πh)`; chain rule along any differentiable constant-mass `L¹` path.
- **TransportL1** (rank 3, Bochner): `[q_{M+γ(1)}] − [q_{M+γ(0)}] = ∫₀¹ Dp γ' dt` in `L¹` along `C¹` curves;
  `[q_M] − [q_{m₀}] = ∫₀¹ [q_{M_s}ℓ_{M_s,δ}] ds` along the atlas.
- **TiltDiagnostic** (round-62 rank 6): `A'(s) = ∫(d−1)log(1+s(d−1))` by differentiation under the integral;
  `sA' − A = KL(ν‖D_s)`, `s𝓘' − 𝓘 = KL(ν‖Q_{M_s})`, `sR' − R = KL(ν‖D_s) − KL(ν‖Q_{M_s})`, and
  `d/ds (R/s) = (KL(ν‖D_s) − KL(ν‖Q_{M_s}))/s²`.
- Earlier (rounds 61–62): EmpiricalMoments, BiasForm (`N_M` self-adjoint), ReconstructionBias, ResponseTransport (chain
  rule, influence function), InvisibleHump (three-point non-monotonicity), PlugInCovariance, PlugInBias, InformationTaylor,
  InformationBias, TangentPythagoras, SecondOrderTransport (`(G_F∘M)'' = b_F(δ,δ)`), NaturalGradientAtlas, InvisibleQuadratic
  (`R(s)/s² → ½‖N_{m₀}(d−1)‖²`), `dataMoment_mixture_eq_atlasPath` (the m-projection of the mixture geodesic is the atlas).
- Older seabed: AtlasHessian (`∫(1,S) q̈ = 0` along the atlas, `q̈ = q N(ℓ_δ²)`), CurvatureSplit (`KL(D_s‖ν) = 𝓘 + R + L`),
  PathEnergy (two-sided family identity), MixturePathEnergy, exponential tilt paths, `thirdOp`/`cumulantVec`, dually-flat
  facts: `natLoss_eq` (Bregman form of `KL(Q_{M*}‖Q_M)`), KL Pythagoras (`responseProjection_spec`).

## Not landed
- Round-63 rank 4: the all-orders invisible tower `d^k q_{M_s}/ds^k = q_{M_s}P_k`, `E_{Q_s}[(1,S)P_k] = 0` for `k ≥ 2`. Note that
  invisibility to all orders is immediate from the exact identity + smoothness (`∫(1,S)q_{M_s} = (1, M_s)` is affine in `s`);
  the content is smoothness of `s ↦ θ(M_s)` to all orders (we have `C¹` via the inverse function theorem on the mean map;
  `ContDiff`/analytic inverse would need the smooth inverse function theorem `ContDiffAt.to_localInverse` or an analytic one).
- The second-order transport along CURVED data paths (`q̈ = H[Ṁ,Ṁ] + J M̈`).
- Anything CLT-shaped (no CLT for the reconstruction law; Mathlib's CLT status unknown to us).

## The user's direction (verbatim, still the target)
"make sure we are tackling core features of the change in posterior expectation values with the change in the data
distribution that allow us to 'map' the space of responses across the data manifold (ideally, all the way from the
'featureless' distribution of maximal entropy to our actual data distribution). What would it take to do this with
maximum beauty and depth?"

## Questions
1. With the closing theorem and the retraction landed, what is the deepest remaining theorem for this direction? Rank ≤ 5
   with precise statements and seabed-level routes. Candidates we see:
   (a) the all-orders tower (needs smooth/analytic inverse of the mean map; is there a cheaper route via the exponential
   family's analyticity in `θ` plus the implicit function theorem, or via a recursion that avoids higher inverse-function
   derivatives entirely — e.g. differentiating the identity `m(θ(M_s)) = M_s` to get `θ^{(k)}` from `θ^{(<k)}` and the
   cumulants of `Q_s`?);
   (b) the dually-flat picture: the atlas is the m-geodesic, the tilt path `ν·e^{sh}` the e-geodesic, the response map is
   m-affine (`dataMoment_mixture_eq_atlasPath`), the KL Pythagoras is the generalized Pythagorean theorem; is there a
   single clean theorem ("the response map is the m-projection; it commutes with mixture geodesics and is the e-nearest
   point; the invisible information is the Bregman residual") worth stating as a package, and what beyond what we have
   would it need (e.g. `KL(D‖Q) = KL(D‖Q_M) + KL(Q_M‖Q)` for every family member `Q` — the full Pythagoras with two-sided
   Bregman, or the dual foliation: fibres `{d : m(d) = M}` are m-flat, the family is e-flat, they meet orthogonally in the
   Fisher sense — the "Riemannian submersion" reading of `DR`)?
   (c) large deviations: `𝓘(M)` is the Cramér rate of the empirical response from ν (Chernoff upper bound for half-spaces
   `P(⟨θ, M̂_n⟩ ≥ ⟨θ, M⟩) ≤ e^{−n(…)}` is elementary from `mgf`); "the visible information is the exponential cost of
   hallucinating the data's response from the featureless law" — a beautiful bridge between sampling and information, but
   is it core to the response map?
   (d) the fluctuation law of the reconstruction: `n·Cov` we have; the Gaussian limit we do not — skip unless Mathlib has CLT.
   (e) something we are missing that is more central to "posterior expectation values as a function of the data
   distribution" — e.g. an intrinsic characterisation of the response map among all maps data → family (the unique
   idempotent map that is m-affine and Fisher-orthogonal?), or a global statement on the whole data manifold (not just
   near one base point): `R` is `C¹` on the open set of `L¹` densities with interior response, with `DR` continuous
   (we have `continuousWithinAt_reconstructionDeriv`).
2. For (a): give the exact recursion for `θ^{(k)}` along an affine moment path and for `P_k`, and say which seabed objects
   (`thirdOp`, `cumulantVec`, `chartDerivEquiv`, `atlasVel`, `atlasBend`, `atlasHess`) already are its first rungs.
3. Sanity: any errors or overclaims in the landed statements as described above (in particular the retraction theorem's
   domain — the fixed-mass affine subspace of `L¹`, with `d₀` only required to have interior response, not to be a
   density)?
Answer in ≤ 3000 words.
