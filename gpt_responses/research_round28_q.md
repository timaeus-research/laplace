# Research consult, round 28 (germbij / laplace `Laplace/Multi/*`)

Same programme as round 27 (PI direction: map the space of posterior responses across the data manifold,
featureless → data, with maximum beauty and depth). Everything below is formal, sorry-free, on main.

## Landed since round 27 (all six items you ranked were attacked; here is what exists)

1. Data-to-posterior quotient (your #1) — `DataQuotient`: on the affine family `L_a = L₀ + ∑ aᵢRᵢ` (finite data
   alphabet, bounded `Rᵢ`, positive prior): `G_a(v,v) = 0 ↔ ∃ c, R_v =ᵐ c` (kernel independent of `a`);
   `P_a = P_b ↔ ∃ c, ∀x, L_b x − L_a x = c`; `obsMapDeriv`: `D_a⟨φ⟩[v] = −t Cov_a(φ,R_v)` for bounded `φ` (Fréchet,
   continuous in `a`); `|D_a⟨φ⟩[v]| ≤ √Var_a(φ)√G_a(v,v)`; path inequality
   `|⟨φ⟩_{γ(1)} − ⟨φ⟩_{γ(0)}| ≤ ∫₀¹ √Var_{γ(s)}(φ) |γ'(s)|_{G_{γ(s)}} ds` for C¹ data paths.
   (No quotient-manifold API; the a.e.-constant kernel statement stands in for it.)
2. Square-root immersion (your #2) — `TwoValuedGeodesic`: the computable core only. `X² − Var = cX` a.e. ⟺ `X`
   two-valued a.e.; for the two-atom state density `pδ_α + qδ_β`: `Var_u = (β−α)²w_u(1−w_u)`,
   `d/du(2 arcsin√w_u) = √Var_u`, `ρ(s,t) = cos(θ_t − θ_s)`, hence `∫_s^t √Var_u du = 2 arccos ρ(s,t)` exactly
   (equality case of the angular bound). The `Lp`-valued map `Ψ = 2√p_a` and `⟨DΨ v, DΨ w⟩ = G(v,w)` were NOT built.
3. Exact affinity–KL decomposition (your #3) — `AffinityKL`: `(1−θ)KL(q‖P_a) + θKL(q‖P_b) = KL(q‖P_θ) + C_θ`;
   `½KL(P_a‖P_b) − B(a,b) = KL(P_a‖P_m)`; `B = inf_q ½(KL+KL)` attained at `P_m`; under regular variation:
   `KL(P_{cu}‖P_{du}) → λ(d/c − 1 − log(d/c))`, `−log ρ(cu,du) → λ log((c+d)/(2√(cd)))`,
   `½KL(P_u‖P_0) + log ρ(0,u) → λ(log 2 − ½)`.
4. All integer multiplicities (your #4) — `LogPowGammaTails` + `MultiplicityModelK`: your binomial route verbatim;
   `u²Var_u = 1 − k/log u + O(1/log²u)` (`c = M_{0,1}` never identified, cancels), and
   `∫_{u₀}^t √Var_u = log t − (k/2) log log t + K + o(1)` for every `k` (reusable `ratio_expansion`, `sq_expansion`).
5. Global wall chart (your #5, chart half) — `GlobalWallChart`: wall response `∂_c⟨ψ⟩_c = −Cov_c(ψ,y^q)` for every real
   `c`; `Var_c(y^q) > 0` on ℝ; `m = ⟨y^q⟩_c` strictly decreasing, `m(+∞) = 0`, `m(−∞) = +∞`;
   `profileMeanHomeomorph : ℝ ≃ₜ Ioi 0`. The two-term wall law (5b) was NOT attempted.
Also: `ProductPrior` (`Var_u(L₁+L₂) = Var_u(L₁)+Var_u(L₂)` on `π₁⊗π₂`; `√(D₁²+D₂²) ≤ D(L₁+L₂) ≤ D₁+D₂`),
`NegativeChamberLaw` (`ℓ_t(−A,0)/√t → K₋(A) = L_{p,q}A^β/β`, `β = p/(2(p−q))`), `NegativeChamber` (profile matching
`Var_{-b}(y^q)(qb/p)^{(p−2q)/(p−q)} → q²/(p(p−q))`), `HalfLineLaplace`, `TwoMonoPotential`.

## Not done from round 27
(6) Interior-minimum geometry: `t Var_{t,a}(f) → f'(x_a)²/H_a` uniformly on compact `a`-intervals, length
    `∫ √H_a |x_a'| da`, and the identification with `K₋(A)` for the two-monomial model.
(5b) The genuinely two-term wall law `ℓ_t(−A,a₁) = K₋(A)√t + (σ/√q) log t + C + o(1)` (needs
    `Var_B(√B(z^q−1)) = q²/(p(p−q)) + O(1/B)` and `h(s) = 1/(√q s) + O(s^{−1−δ})`).
(2') The `Lp` immersion itself.

## Questions
1. Re-rank what remains and add anything the landed material now makes cheap or newly attractive. Candidates we
   see beyond (6), (5b), (2'): a *global* statement tying `DataQuotient` to `MeanMapEmbedding` (the mean map
   factors through the quotient by the invisible subspace and is an open embedding of the quotient — is this a
   one-page corollary?); the phase-diagram theorem for the two-monomial wall as a single statement (rate `√t`
   for `a<0<b`, `log t` for `a=0<b`, finite for `0<a<b`, with the constants) — the pieces exist
   (`NegativeChamberLaw`, `wall_recedes`, `wall_window_length`); the Bhattacharyya/KL/length trichotomy along
   the featureless ray as one "asymptotic self-similarity" theorem; a Fisher–Rao *lower* bound for the whole affine
   family from `AffinityKL` (`B ≤ ½KL`) combined with `AngularBound`; the equality case of `ProductPrior`'s lower
   bound; entropy/Legendre duality for the state density (`F = log Z` convex, `−F'(u) = ⟨ℓ⟩_u` the mean map of the
   ray, Legendre transform = entropy of the tilted law) — the 1-parameter version of `EntropyDuality`; the
   "response map of the ray" `u ↦ ⟨ℓ⟩_u` as a global chart of `(0,∞)` onto `(ess inf ℓ, ⟨ℓ⟩_0)` (analogue of
   `GlobalWallChart`); the Cramér/large-deviation reading of the featureless ray (`log Z` as a cumulant generating
   function, `u²Var_u → λ` as the curvature of the rate function at the boundary).
2. For (6): give the cleanest Lean-ready statement of the 1D uniform Laplace theorem for a moving interior minimiser
   with hypotheses matching what a formaliser can verify (we have `MovingMinimizer` (IFT for the critical point),
   `LocalLaplaceDomain`/`HigherLaplaceDomain` (Laplace expansions at a fixed minimiser with rates), and the half-line
   lemma `tendsto_sqrt_mul_integral` with polynomially bounded observables). Which of these is the right base, and what
   is the minimal uniformity hypothesis that still yields the integrated length limit (dominated convergence in `a`
   needs a uniform bound on `t Var_{t,a}(f)`)?
3. For (5b): is there a route to `Var_B(√B(z^q−1)) = q²/(p(p−q)) + O(1/B)` that reuses `tendsto_sqrt_mul_integral`
   (e.g. apply it to the *difference* observables with an extra `√B` factor and one more Taylor term), and what is
   the exact second-order coefficient so we can check numerically before formalising?
Be concrete and Lean-aware; where you propose a theorem, spell out the hypotheses.
