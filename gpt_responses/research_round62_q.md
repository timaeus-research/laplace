# Research round 62: the response map across the data manifold — after ranks 1, 2, 4, 5 of round 61

## Landed since round 61 (laplace `Laplace/Multi/*`, all sorry-free)
- **ResponseTransport** (rank 1): chain rule `d/ds G_F(M(s)) = lin_{F,M(s)}(M'(s))` along any differentiable curve of interior
  responses; continuity of the velocity field; FTC `G_F(M(1)) − G_F(M(0)) = ∫₀¹ lin(M') ds`; covariance representation
  `lin_{F,M}(u) = −⟨R_M u, Cov_{Q_M}(S,F)⟩`; `R_M` is `dotJ`-symmetric; the influence function
  `ψ_{F,M}(x) = −⟨R_M Cov_{Q_M}(S,F), S(x) − M⟩`; `lin_{F,M}(E_D S − m₀) = ∫ψ dD − ∫ψ dν`; along the affine data path
  `D_t = (1−t)ν + tD` (response path = straight atlas, `dataMoment_mixture_eq_atlasPath`) `d/dt G_F(M_t) = ∫ψ_{F,M_t} d(D − ν)`.
- **InvisibleHump** (rank 2): envelopes `R(s) ≤ s KL(D‖ν) − 𝓘(M_s)` and `R(s) ≤ s R(1) + s 𝓘(M) − 𝓘(M_s)`; the THREE-POINT
  COUNTEREXAMPLE formalised: uniform ν on Fin 3, S(x)=x, D ∝ e^x; `R(0)=R(1)=0`, `R(t)>0` inside (`p₀p₂ = p₁²` for family
  members vs the strict hump for mixtures); `¬Antitone R ∧ ¬Monotone R`.
- **PlugInCovariance** (rank 5): `n Cov(Ĝ_F, Ĝ_G) → Σ Γ_ab lin_F(e_a) lin_G(e_b) = E_D[lin_F(S−M) lin_G(S−M)]` (sandwich).
- **PlugInBias** (generic schema): any `Φ` continuous on the compact convex interior neighbourhood `C` with a uniform
  second-order expansion has `n(EΦ̃_n − Φ(M)) → ½ Σ Γ_ab b(e_a,e_b)`.
- **InformationTaylor + InformationBias** (rank 4): compact-uniform `𝓘(M+h) = 𝓘(M) − ⟨h,θ(M)⟩ + ½ g_M(h,h) + o(‖h‖²)` (from the
  generic uniform Peano lemma with `A z = pairLin(θ(m₀+z))`, `B z = pairLin ∘ R_z`), ambient Fisher form `fisherAmb`
  through the direction projection, and `n(E 𝓘(M̂_n) − 𝓘(M)) → ½ E_D[g_M(S−M,S−M)] = ½ tr(Γ H_M)`.
- Earlier this session: EmpiricalMoments (unbiased, Γ/n, Hoeffding), BiasForm (`N_M` self-adjoint, bilinear `b_F`),
  ReconstructionBias (`n(EĜ_n − G_F(M)) → ½ E_D b_F(S−M,S−M)`), and all of rounds 56–60.

## Not landed
- Rank 3: `C²` of `M ↦ [q_M] ∈ L¹(ν)` (we have `C¹` with an explicit operator-norm modulus, and the L¹ derivative `Dp_M u = [q_M ℓ_{M,u}]`).
- The `L²` local expansion of the invisible information `R(t) = ½ t² ‖N_{m₀} h‖²_{L²(ν)} + o(t²)` for `h = dD/dν − 1 ∈ L²(ν)`.
- The diagnostic identity `t R'(t) = R(t) + KL(ν‖D_t) − KL(ν‖Q_{M_t})`.
- Mathlib still has no CLT and no Banach analytic IFT; `genRate` is lsc and convex, differentiable on `ri K`.

## The user's direction (verbatim, still the target)
"make sure we are tackling core features of the change in posterior expectation values with the change in the data
distribution that allow us to 'map' the space of responses across the data manifold (ideally, all the way from the
'featureless' distribution of maximal entropy to our actual data distribution). What would it take to do this with
maximum beauty and depth?"

## Questions
1. With ranks 1, 2, 4, 5 landed, what is the *next* theorem that most deepens the map `D ↦ Π(E_D S) ↦ (posterior expectations)`
   across the data manifold? Rank ≤ 6 candidates with precise statements, seabed-level proof routes, expected LOC, and what is
   new. Our own candidates: (a) the **second-order transport**: `d²/dt² G_F(M_t)` along the affine data path in terms of
   `b_F` and the third cumulant (we have `dual_curve_comparison`, `cubicScore`, `thirdOp`); (b) the **transport of the whole
   reconstruction** as a measure-valued curve: `d/dt [q_{M_t}] = [q_{M_t} ℓ_{M_t,δ}]` in `L¹` (have it) and its `C²` version
   (rank 3) giving a uniform-in-`F` version of the bias theorem (the bias as a signed measure `½ Σ Γ_ab ∂²q/∂M_a∂M_b`);
   (c) **data-manifold geometry**: the pullback of the Fisher–Rao metric of the family along `D ↦ Π(E_D S)` is the
   sandwich form `E_D[lin·lin]`-type object — is there a clean theorem that the *visible* part of a data tangent `ḋ` has
   Fisher–Rao length `‖ḋ‖_{vis} = g_M(Ṁ,Ṁ)^{1/2}` with `Ṁ = ∫ S dḋ`, and the *invisible* part is orthogonal (a Pythagoras
   for tangents, complementing the KL Pythagoras)? (d) the **influence-function calculus**: `ψ_{F,M}` is the `L²(Q_M)`-Riesz
   representer of `dG_F` restricted to tangent scores; prove `E_{Q_M}[ψ_{F,M} ℓ_{M,u}] = lin_F(u)` and
   `Var_{Q_M}(ψ_{F,M}) = g_M^{-1}(c_F, c_F)` — the "Fisher-dual norm" appearing when `Γ = C_M`; (e) **mixture vs.
   exponential path**: compare the affine data path with the exponential tilt path `ν.tilted(t log r)` (both landed as objects:
   `hasDerivAt_genRate_dataPath` for tilts) — the exponential path has `R ≡ 0` iff `log r ∈ span(S)`; a theorem
   "the invisible information along the tilt path is `KL(D‖Π(M))`-monotone?" (or a counterexample); (f) **the atlas as a
   gradient flow**: is `s ↦ Π(M_s)` the KL-gradient flow / geodesic of some structure, and `𝓘(M_s)` its action
   (`𝓘(M_s) = ∫₀ˢ (s−r) κ(r) dr` is landed — is `κ` the squared speed, making `𝓘` an energy)?
2. Which of the three non-landed items is worth landing now versus deferring, given the direction?
3. Sanity-check the information-bias coefficient: is `½ E_D[g_M(S−M,S−M)]` right, and equal to `½ dim 𝕍 / n` when `Γ = C_M`?
   (We claim `g_M(u,v) = ⟨u, C_M^{-1} v⟩` on `𝕍`; so `E_D g_M(S−M,S−M) = tr(C_M^{-1} Γ|_𝕍)`, `= dim 𝕍` if `Γ = C_M`.)
4. Referee-level restatements: the bias/covariance/information theorems currently express the linear/bilinear terms through a
   projection `π` onto `𝕍` (scaffolding). We proved `π`-independence of the coefficients (`Σ Γ b(e_a,e_b) = E_D b(S−M,S−M)`).
   Is there a cleaner intrinsic formulation you'd recommend (e.g. state everything on `𝕍` with `Γ|_𝕍`)?
Answer in ≤ 3000 words.
