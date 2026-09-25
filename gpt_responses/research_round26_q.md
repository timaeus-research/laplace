# Research round 26: after the round-25 plan — the crowning statements of the response-map programme

## Landed since round 25 (all sorry-free, pushed; laplace `Laplace/Multi/*`)

1. `MeanMapEmbedding`: the mean map is an open embedding; global inverse strictly differentiable with
   derivative `(Dm)⁻¹` on the open response space (your item 1).
2. `StateDensity`: `lossLaw ν = L_*(πμ)`; `Z` = Laplace transform of `ν`; `⟨f(L)⟩_u`, `Var_u(L)` and the
   radial length `D_t(L) = ∫₀ᵗ √Var_u(L)` are functionals of `ν` alone; same state density ⇒ same
   featureless-line geometry (your item 2, reduction).
3. `TauberianVariance`: **regular variation `Z(cu)/Z(u) → c^{-λ}` ⇒ `u² Var_u(ℓ) → λ`** with no derivative
   control (monotone-density squeeze on the integrals via `x e^{-x} ≤ 1 − e^{-x} ≤ x`); `Z ~ C u^{-λ}(log u)^k`
   ⇒ regular variation; `FeaturelessLawFromPartition`: `(∫_{u₀}^t √Var_u)/log t → √λ` from the free-energy
   asymptotic alone (your item 2, Tauberian).
4. `LogGammaTails` + `RenormalisedLength` + `MultiplicityModel`: **the multiplicity law for `k = 1`**: for the
   state density `(−log ℓ) 1_{(0,1)} dℓ`, `|u² Var_u − (1 − 1/log u)| ≤ C/log² u` with explicit `C`, and
   `∫_{u₀}^t √Var_u = log t − ½ log log t + K + o(1)` (your item 3, first landing). Tails by the `(s/u)² ≥ 1`
   trick, the only special-function input `Λ_{j+1}(∞) = (j+1)Λ_j(∞) + j!` by IBP; numerics confirm the residual
   `→ −(1−γ)`.
5. `FisherInformation`: `affScore = −t(R_v − ⟨R_v⟩_a) = ∂_v log p_a`, mean zero, and
   **`E_a[score_v score_w] = t² Cov_a(R_v, R_w) = G_a(v,w)`**: the response form is the Fisher information of the
   posterior family (your item 5 in intrinsic form; the `L²` square-root embedding itself not formalised).
6. `RadialLaws`: `D_t(aL+b) = D_{at}(L)`, constant invariance, the two-sided window identity (your item 6).

## Not yet done

- Negative-profile matching `h(−b) ~ K_{p,q} b^{β−1}` and the chamber law `ℓ_t(−A,0)/√t → K₋(A)` (your item 4).
  The seabed's Laplace machinery (`LaplaceCovHypotheses`, `movingMinimizer`) is for smooth potentials on ℝ^d with
  global jet hypotheses; the half-line potential `z^p − z^q` with real exponents needs a new localisation
  (smooth only on `(0,∞)`, complement exponentially small). Cost estimate ≥ 400 lines.
- General integer `k = m − 1`: `(T − log s)^k` binomially, tails of `∫ s^j e^{-s} (log s)^r` for `r ≤ k`, and
  an IBP recursion in `r`. ~300 lines beyond `k = 1`.
- Product-prior inequality `√(D₁² + D₂²) ≤ D(L₁+L₂) ≤ D₁ + D₂` (Fubini on a product measure, ~150 lines).

## Questions

1. **What is now the crowning statement?** Given the exact layer (global chart, Fisher information = response
   form, Legendre/entropy duality), the radial layer (state density, Tauberian `λ`, multiplicity `log log t`),
   and the singular layer (wall window isometry, receding wall, singular chart), what single theorem or small
   cluster would best express "the map of responses across the data manifold from featureless to data" —
   e.g. (i) a *comparison theorem* bounding the thermodynamic length of ANY path of data distributions from the
   featureless point to `q` below by a function of the state density of `L_q` (is the temperature line
   length-minimising among mixture paths with the same endpoints? among all paths?); (ii) a *Pythagorean /
   projection* statement (the featureless line as the radial geodesic of the exponential connection, with the
   Legendre dual coordinates); (iii) the *Fisher–Rao distance to the featureless posterior* `d_FR(P_0, P_t) =
   2 arccos ∫ √(p_0 p_t)` expressed through the state density (`∫ √(p_0 p_t) = Z(t/2)/√(Z(0)Z(t))`!) and its
   asymptotic `→ π` versus the diverging length `√λ log t` — a clean "length versus distance" theorem that is
   essentially free given the state-density reduction: is `Z(t/2)²/(Z(0) Z(t)) → 0` at rate `t^{-λ}` the right
   statement (`2^{λ}`-type constants)? Please give the precise theorem statements you would formalise for the
   best two of these, with proofs at the level of identities.

2. **The Bhattacharyya / Hellinger affinity along the featureless line.** With `ρ(t) := ∫ √(p_0 p_t) dπ =
   Z(t/2)/√(Z(t))` (taking `Z(0) = 1`), regular variation gives `ρ(t)² = Z(t/2)²/Z(t) ~ C 2^{2λ} (t/2)^{-2λ}/(C t^{-λ})
   · (log ratio)` — i.e. the affinity decays like `t^{-λ/2}`, so `−log ρ(t) ~ (λ/2) log t`, and Fisher–Rao distance
   → π. Meanwhile the length is `√λ log t`. Is there a sharp general inequality between `−log ρ(t)` and the
   thermodynamic length (a "Bhattacharyya bound" `−log ρ ≤ ℓ²/8`? or `ℓ ≥ 2 arccos ρ`?) that we can state and
   prove in the state-density setting? Which direction is clean?

3. **Negative-profile matching, cheapest rigorous route.** Given the exact profile variance
   `Var_c(y^q) = N₂(c)/N₀(c) − (N₁/N₀)²` with `N_k(c) = ∫₀^∞ y^{kq} e^{-(y^p + c y^q)} dy`, is there a route to
   `h(−b) ~ K b^{β−1}` that avoids a general Laplace localisation — e.g. a differential identity in `c`
   (`N₀' = −N₁`, `N₀'' = N₂`, so `Var_c = (log N₀)''`) plus a *convexity/Tauberian* argument like the one we used
   for `Z` (regular variation of `N₀(−b)` as `b → ∞`: `N₀(−b) ~ e^{B V(z₀)}·…` is exponential, not regularly
   varying — so what replaces it)? Or a moment-generating/Laplace-method-free route via the exact
   `ρ_c` being a *tilted* family in `c` (exponential family in the parameter `c` with sufficient statistic `y^q`):
   then `Var_c(y^q)` is the second derivative of the log-normaliser, convex in `c`, and the question is the
   asymptotic of a one-dimensional exponential family's variance as the parameter goes to `−∞`. Is there a
   general theorem "if the sufficient statistic has density with a specific tail, the variance at parameter
   `−b` ~ …"? Please give the sharpest practical route and its hypotheses.

4. **Ranked plan** (at most six items) for what to formalise next, weighting beauty and depth over cost, now
   that the round-25 list is largely done.
