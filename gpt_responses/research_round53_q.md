# Round 53: re-ranking after the round-52 landings (germbij / laplace seabed)

Context: we are formalising in Lean 4 + Mathlib (repo `laplace`, modules `Laplace/Multi/*`) the "response map over
the data manifold" programme: a finite family of bounded features `S : J → X → ℝ`, a featureless (max-entropy)
posterior `ν` (probability on `X`), the exponential family `P_θ = e^{−⟨θ,S⟩}ν/Z(θ)`, the mean map / atlas
`M ↦ Π(M) = P_{θ(M)}` (entropy projection of a response `M = E_D S`), the information `𝓘(M) = KL(Π(M)‖ν)`,
the decomposition `KL(D‖ν) = 𝓘(M_D) + R + L` (atlas / marginal residual / fibre information `L = KL(D‖D↑)`,
`D↑ = E_ν[dD/dν|σ(S)]ν`), the straight response path `M_s = (1−s)m₀ + sM` with atlas curvature `κ(s)`, and the
bridge `D_s = (1−s)ν + sD`.

The user's standing direction: "tackle core features of the change in posterior expectation values with the
change in the data distribution that allow us to map the space of responses across the data manifold, ideally all
the way from the featureless distribution of maximal entropy to our actual data distribution. What would it take
to do this with maximum beauty and depth?"

## Landed since round 52 (all sorry-free, on `main`)

Round-52 items landed: 1 (simultaneous curvature formulas), 2 (retraction theorem), 3 (L¹ derivative),
4 (Pythagoras iff Fisher orthogonality), 5 (conditional variational formula), 8 (asymmetry), 9 (conditional
Fisher loss), 12 (length–energy). Remaining from round 52: 6 (observable-defect second order), 7 (mixed Hessian
`D²q = q(I − C − B)(ℓ_u ℓ_z)`), 10 (skewness `κ' = −E ℓ³`, asymmetry = accumulated skewness).

Precise statements now available (names are Lean theorems):
- `CurvatureSplit`: `KL(D_s‖ν) = ∫₀ˢ (s−w) k_d(w) dw`, `L_s = ∫₀ˢ (s−w)(k_d − k_a)`, `R_s = ∫₀ˢ (s−w)(k_a − κ)`,
  `a = E_ν[d|σ(S)]`, the lift of the bridge is the bridge of `a` (`statisticLift_densLaw_bridge`), the response
  of `D_s` is `M_s` (`mean_densLaw_bridge`); `k_d(w) = ∫ (d−1)²/(1+w(d−1)) dν`.
- `ConditionalFisherLoss`: `k_d(w) − k_a(w) = ∫ (d−a)²/(d_w a_w²) dν` (conditional variance of the mixture score),
  `k_a ≤ k_d`; `L_s = ∫₀ˢ (s−w) · condVar`. (We did NOT claim `k_a ≥ κ`, per your warning.)
- `BregmanGeometry`: three-point identity `KL(Π(A)‖Π(C)) = KL(Π(A)‖Π(B)) + KL(Π(B)‖Π(C)) + ⟨θ(C)−θ(B), A−B⟩`;
  Pythagoras iff the mixed pairing vanishes; `KL(Π(M)‖ν) − KL(ν‖Π(M)) = ∫₀¹ (1−2s)κ`.
- `DensityDerivative` / `ReconstructionDerivative`: `|p_{θ+η} − p_θ − p_θ(⟨η,m(θ)⟩ − ⟨η,S⟩)| ≤ 10(K‖η‖)² p_θ`
  pointwise for `K‖η‖ ≤ 1/4`; `L¹` remainder `O(‖η‖²)`; in response coordinates
  `∫|q_{M+z} − q_M − q_M(⟨Dθ z, M⟩ − ⟨Dθ z, S⟩)| = o(‖z‖)` for interior `M`, `z ∈ 𝕍` (direction subspace).
- `RetractionDerivative`: along `D_t = e^{th}Π(M)/Z`, `∫ |q_{M_t} − q_M − t q_M ⟨a, S − M⟩| = o(t)` with
  `Σ_M a = Cov_{Π(M)}(S,h)` (regression coefficient); i.e. `d(dΠ(M_t)/dΠ(M))/dt|₀ = B_M h` in `L¹(Π(M))`.
- `AtlasLength`: `(∫₀¹ √κ)² ≤ KL(Π(M)‖ν) + KL(ν‖Π(M))`.
- `ConditionalVariational`: `KL(D‖T_g) = L − E_D g + E_D log E_ν[e^g|σ(S)]` for the conditional tilt
  `T_g = e^g aν/E_ν[e^g|σ(S)]`; conditional Donsker–Varadhan `≤`; attained at `g = log(d/a)`;
  `L = max_{g bounded} {E_D g − E_D log E_ν[e^g|σ(S)]}` (`IsGreatest`). All under bounded positive densities
  `0 < c ≤ d ≤ C` (so no clipping was needed).
- Earlier (rounds 47–51): `KL(D‖ν) = ∫₀¹ (1−s)κ + L + R` for every finite-information `D`; equal energies of atlas
  and exponential paths; endpoint tails; variational Fisher (`κ = min` cost); Legendre closure; observable
  transport to second order `F''(s₀) = T(r₀, ⟨v,S⟩, ⟨v,S⟩)` (frozen residual); statistic lift, residual split,
  information tower, bridge residual moduli, joint convexity of KL; nested `L²` projections
  (`‖h‖² = ‖Bh‖² + ‖Ch − Bh‖² + ‖h − Ch‖²`); regression projection; quadratic shadow of `KL = 𝓘 + R + L` along
  bounded tilts (all three limits); atlas refinement tower; empirical projection consistency (SLLN); Cramér.

## Questions

1. Given the user's direction (map the responses from the max-entropy posterior to the data law, with maximum
   beauty and depth), what are now the deepest remaining targets, and how would you rank them by depth ×
   feasibility in Lean/Mathlib? Please consider at least: (a) skewness `κ'(s) = −E_{Q_s} ℓ_{m_s,v}³` and
   `KL(Q₁‖ν) − KL(ν‖Q₁) = ∫₀¹ s(1−s) E ℓ³` (we have `hasDerivAt_lawCov_familyMeasure_path` for covariances along
   paths and a variational characterisation of `κ`; is an envelope-theorem route to `κ'` cleaner than
   differentiating the inverse covariance?); (b) the observable-defect second-order term; (c) the mixed Hessian;
   (d) a global structure theorem for the response map (diffeomorphism of the natural-parameter space onto the
   relative interior of the moment body; the full simplex as a fibration over the moment body with fibres the
   sets `{D : E_D S = M}`, `Π` the fibre-wise entropy minimiser; what is the cleanest formal statement?);
   (e) the "three paths from ν to D": mixture bridge `D_s`, its lift `(D_s)↑`, and the atlas `Π(M_s)` — we have
   all three curvatures; is there a canonical fourth (e.g. the e-path in the full simplex `e^{s log d}ν/Z`) with a
   comparison theorem (energies, lengths, Pythagoras)?; (f) unbounded densities (clipping) for the conditional
   variational formula and the curvature split; (g) anything you consider the "missing geometric heart".
2. For your top-ranked item, give the precise statement (with hypotheses that match the seabed: bounded features,
   `ν` probability, interior responses), a proof sketch at the level of Lean lemmas, and an estimate in lines
   (not time).
3. Which of the remaining round-52 items (6, 7, 10) would you drop as not worth the Lean cost?
