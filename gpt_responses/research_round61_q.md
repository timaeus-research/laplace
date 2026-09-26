# Research round 61: after the reconstruction-bias theorem — what next for the response map across the data manifold?

## Standing programme (Lean, laplace seabed, all sorry-free)
Affine exponential family `P_θ ∝ e^{⟨θ,S⟩} ν` with bounded features `S : J → X → ℝ`, moment body `K`, direction space `𝕍`,
response reconstruction `Π(M) = P_{θ(M)}` for `M ∈ ri K` (and defined on the finite-rate domain `{𝓘(M) < ∞}`),
`𝓘(M) = KL(Π(M)‖ν)` the visible information (genRate, lsc, dual representation), scores `ℓ_{M,u}`, regression/normal
projections `B_M, N_M`, Fisher form `g_M`, third cumulant, atlas path from the featureless response `m₀` to `M`.

## Landed since round 60 (all in laplace `Laplace/Multi/*`)
- Round-60 low-cost items: `L²(Q)` orthogonality/Pythagoras of `B_M,N_M`; TV length ≤ Fisher–Rao length along interior `C¹` curves.
- `C¹` of `M ↦ [q_M] ∈ L¹(ν)` on `ri K`, with explicit operator-norm modulus.
- **EmpiricalMoments**: `E M̂_n = M_D`, `E[(M̂_n−M)_a(M̂_n−M)_b] = Γ_ab/n` (`Γ = Cov_D S`), Hoeffding tails in the sup norm.
- **BiasForm**: `N_M` is self-adjoint in `L²(Q_M)`; bias form `b_F(u,v) = ∫ N_M F · ℓ_{πu} ℓ_{πv} dQ_M` bilinear on `ℝ^J`
  via a linear projection `π` onto `𝕍`; the compact-uniform Peano expansion `G_F(M+z) = G_F(M) + lin_F(z) + ½ b_F(z,z) + O(ε‖z‖²)`.
- **ReconstructionBias** (THE round-60 target): for iid data `D ≪ ν`, `M = E_D S ∈ ri K`, `∃ C` compact convex interior
  neighbourhood of `M` such that the truncated plug-in `Ĝ_n = G_F(M̂_n)` (fallback `G_F(M)` off `C`) has
  `n (E Ĝ_n − G_F(M)) → ½ Σ_ab Γ_ab b_F(e_a,e_b) = ½ E_D b_F(S(x)−M, S(x)−M)`. No CLT (Hoeffding + Γ/n + uniform Peano).

## Not landed
- `C²` of `M ↦ [q_M]` in `L¹` (differentiate the score); all-orders prototype `ContDiff ℝ ⊤ (θ ↦ ∫ φ e^{⟨θ,S⟩} dν)`.
- Mathlib still has no CLT; no Banach analytic IFT.

## The user's direction (verbatim)
"make sure we are tackling core features of the change in posterior expectation values with the change in the data
distribution that allow us to 'map' the space of responses across the data manifold (ideally, all the way from the
'featureless' distribution of maximal entropy to our actual data distribution). What would it take to do this with
maximum beauty and depth?"

## Questions
1. Rank (≤6) the next theorems that best serve this direction, given what is landed. For each: precise statement,
   hypotheses, proof route in the seabed's terms, expected line count, and what is new mathematically. Candidates we see:
   (a) the *variance* of the plug-in `n Var(Ĝ_n) → g-dual form = E_D[(lin_F(S−M))²] = Σ Γ_ab lin_F(e_a) lin_F(e_b)` (delta method
   without CLT); (b) mean-squared error `E(Ĝ_n − G_F(M))² = (1/n) Σ Γ_ab lin_F(e_a) lin_F(e_b) + o(1/n)`; (c) the bias of the
   visible information `𝓘(M̂_n)` itself (`F`-free: `n(E 𝓘(M̂_n) − 𝓘(M)) → ½ tr(Γ g_M^{-1})`-type formula — is the coefficient
   `½ Σ Γ_ab (g_M^{-1})_{ab}` on `𝕍`? note `𝓘` has Hessian `g_M^{-1}` in response coordinates); (d) the same for the atlas path:
   bias/variance of the *whole reconstructed path* `s ↦ Π((1−s)m₀ + sM̂_n)` in TV, uniformly in `s`; (e) the data-manifold
   picture: for a *curve of data distributions* `t ↦ D_t` (e.g. a mixture `(1−t)ν + tD`, or an exponential tilt), the
   response `M(D_t)` and the reconstruction `Π(M(D_t))` — derivatives, and the identity of the mixture path's responses with
   the straight atlas path `(1−t)m₀ + tM` when `E_ν S = m₀` (is that exactly the atlas? yes if `m₀ = E_ν S`); then the
   *visible information along the data path* `t ↦ 𝓘(M(D_t))` is convex? monotone? with derivative `⟨θ(M_t), M − m₀⟩`;
   (f) the projection/Pythagoras along the data path: `KL(D_t‖ν) = 𝓘(M_t) + KL(D_t‖Π(M_t))` and the monotonicity of the
   invisible part in `t`.
2. For (e): is the mixture path `D_t = (1−t)ν + tD` the canonical "path from maximal entropy to the data"? Its response path IS
   the straight atlas path. Which quantities along it have closed forms in the seabed's terms, and which have beautiful
   inequalities (e.g. `𝓘(M_t) ≤ t 𝓘(M)` by convexity of `𝓘`; `KL(D_t‖ν) ≤ t KL(D‖ν)`; hence `KL(D_t‖Π(M_t)) ≤ t KL(D‖ν) − 𝓘(M_t)`)?
   What is the sharpest statement about "invisible information decreases toward the featureless end"?
3. Is there a Mathlib-only lemma we should extract (e.g. bilinear-form expectation of iid averages, or the truncated-plug-in
   bias schema) that would be reusable beyond this seabed?
4. Anything in the ReconstructionBias statement that a referee would object to (truncation to `C`, dependence on `π`,
   the sup norm, the `DecidablePred` instance)? Suggest the cleanest paper-level statement.
Answer in ≤ 3000 words; be concrete about statements and proof routes.
