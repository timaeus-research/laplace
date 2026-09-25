# Research consult, round 27 (germbij / laplace `Laplace/Multi/*`)

You are advising a Lean 4 + Mathlib formalisation programme (laplace seabed, ~250 modules, sorry-free) whose
current direction, set by the PI, is: *"tackle core features of the change in posterior expectation values with
the change in the data distribution that allow us to map the space of responses across the data manifold —
ideally all the way from the featureless distribution of maximal entropy to our actual data distribution. What
would it take to do this with maximum beauty and depth?"* Posterior `P_{t,L} ∝ e^{-tL} π`, loss `L_q(w) = E_q ℓ`,
response map `q ↦ ⟨R⟩_{t,q}`, response form `G_a(v,u) = t² Cov_a(R_v,R_u)`, thermodynamic length `∫√G`.

## Landed since your round-26 advice (all formal, sorry-free, on main)

Round-26 crown (Theorems A, B) — DONE:
- `Affinity`: `∫√(p_s p_t) = Z((s+t)/2)/√(Z_s Z_t)`; `−log ρ` = midpoint Jensen gap of `F = log Z`; under regular
  variation `Z(cu)/Z(u) → c^{-λ}`: `Z → 0`, `ρ(0,t)²/Z(t) → 2^{2λ}/Z(0)`, `d_FR(P_0,P_t) = 2 arccos ρ → π`.
- `RadialCurvature`: `N_k' = −N_{k+1}`, `F' = −⟨ℓ⟩`, `F'' = Var`, Jensen-gap integral identity
  `(F(s)+F(t))/2 − F(m) = ½(∫_s^m (u−s)Var + ∫_m^t (t−u)Var)`, `‖∂_u √p_u‖² = Var/4`.
- `AngularBound`: `2 arccos ρ(s,t) ≤ ∫_s^t √Var_u` (Cauchy–Schwarz on the L² sphere, `ρ' = (ρ/2)(⟨ℓ⟩_u − ⟨ℓ⟩_m)`).
- `InformationProjection`: KL Pythagoras `KL(q‖P_b) = KL(q‖P_a) + KL(P_a‖P_b)` under `E_q R = m(a)`.
Negative chamber — DONE (your §3 recipe, adapted to the two-monomial profile):
- `HalfLineLaplace`: abstract centred half-line Laplace lemma
  `√B ∫₀^∞ G_B(√B(z−1)) e^{-Bφ(z)} dz → ∫ G_∞(w) e^{-κw²/2} dw` (quadratic lower bound on (0,z₁], stretched
  exponential coercivity beyond, `φ(1+h)/h² → κ/2`, polynomially bounded observables).
- `TwoMonoPotential`: `ψ = z^p − (p/q)z^q`, `φ = ψ − ψ(1)`, `c₁(z−1)² ≤ φ` on (0,z₁], `½(z−1)^{min p 1} ≤ φ` beyond
  `max(2,(2p/q)^{1/(p−q)})`, `φ(1+h)/h² → p(p−q)/2`.
- `NegativeChamber`: `N_g(−b) = y_b e^{-Bψ(1)} ∫ g(y_b z) e^{-Bφ}`, `y_b = (qb/p)^{1/(p−q)}`, `B = y_b^p`, and
  `Var_{-b}(y^q)·(qb/p)^{(p−2q)/(p−q)} → q²/(p(p−q))`.
- `NegativeChamberLaw`: power-law Cesàro, continuity of the profile variance in the coupling on all of ℝ, and
  `ℓ_t(−A,0)/√t → K₋(A) = L_{p,q} A^β/β`, `β = p/(2(p−q))`, `L_{p,q} = (q/√(p(p−q)))(q/p)^{β−1}` (with
  `wall_recedes`: the two-sided law of the two-monomial wall).
- `ProductPrior`: `Var_u(L₁+L₂) = Var_u(L₁)+Var_u(L₂)` on `π₁⊗π₂`; `√(D₁²+D₂²) ≤ D(L₁+L₂) ≤ D₁+D₂`.
Earlier this session: `MeanMapChart`/`MeanMapEmbedding` (response coordinates a global chart), `StateDensity`,
`TauberianVariance` (`u²Var → λ` from regular variation of Z alone), `FeaturelessLawFromPartition`,
`FisherInformation`, `RadialLaws`, `MultiplicityModel` (k = 1: `∫_{u₀}^t √Var = log t − ½ log log t + K + o(1)`
for the state density `(−log ℓ)dℓ` on (0,1)), `RenormalisedLength`, `LogGammaTails`.

## Still open from rounds 25/26
(a) General integer `k`: state density `(−log ℓ)^k dℓ` on (0,1) (i.e. (λ,m) = (1,k+1)); want
    `∫_{u₀}^t √Var_u = log t − (k/2) log log t + K + o(1)`. Our k = 1 proof: `Z, N₁, N₂` in terms of truncated
    Gamma/log-Gamma integrals `∫₀^u s^j e^{-s} ds`, `∫₀^u s^j log s e^{-s} ds` with `O(1/u²)` tails, then
    `|u²Var − (1 − 1/log u)| ≤ C/log² u` and the renormalised-length lemma (needs exactly this second-order form).
    For general k one needs the moments `Λ_{j,r}(u) = ∫₀^u s^j (log s)^r e^{-s} ds`, r ≤ k, and a binomial
    expansion of `(log u − log s)^k`. Alternative: `Z_k(u) = (−1)^k ∂_s^k [u^{-(s+1)} γ(s+1,u)]|_{s=0}` (generating
    function in the exponent). Which route is cleanest in Lean, and is the second-order coefficient really
    `1 − k/log u + O(1/log² u)` for all k (so the Euler–Mascheroni terms cancel at this order)?
(b) Square-root Fisher immersion `Ψ(a) = 2√(p_a)` into the L² sphere, `⟨DΨ[v], DΨ[w]⟩ = G_a(v,w)`, and the
    characterisation of geodesics of the response metric through two-valued contrasts (round 25 item 5).

## Questions
1. Given the landed material, what are the 4–6 most valuable next targets for the PI's direction ("map the
   space of responses across the data manifold, featureless → data, with maximum beauty and depth")? Rank them,
   state each as a precise theorem (hypotheses, conclusion), estimate the Lean cost in lines relative to what we
   have, and say which existing modules it builds on. Candidates we see: (a), (b) above; a two-sided wall corollary
   `ℓ_t(−A,a₁) = K₋(A)√t + σ√(1/q) log t + o(log t)`; global statements about the response map on the two-monomial
   wall (homeomorphism onto its image across the wall, from `continuous_profileVar` + monotonicity of the profile
   mean); a "phase diagram" theorem: the map `a ↦ lim ℓ_t(a,·)/rate(t)` is piecewise with the rate jumping from
   `log t` to `√t` at the wall; the geometry of the affinity/KL pair (`−log ρ` vs `KL` along the featureless line,
   Bhattacharyya vs KL as Jensen gaps of `F` at the midpoint vs endpoint: `KL(P_s‖P_t) = F(t) − F(s) + (s−t)F'(s)`
   — a Bregman identity, and the ordering `−log ρ ≤ ½ KL` — is there a deeper exact statement?); a dual/entropy
   picture of the negative chamber (what is the `√t` law in terms of the state density near the interior
   minimiser — a state density with a Gaussian peak rather than a power law at 0?).
2. For (a), give the cleanest complete route, with the exact coefficient claim and how the `O(1/log² u)` remainder
   should be organised so that the existing `tendsto_renormalised_length` applies.
3. Is there a unifying statement of what we have proved about lengths versus distances — e.g. a theorem that the
   featureless line is a length-minimising path among paths in the affine family with given endpoints (it is
   straight in the natural coordinate; is it a geodesic of the Fisher metric in general? For 1-parameter families
   every path is a geodesic up to reparametrisation, so the content would be in the multi-parameter affine family
   through the mean map)? State precisely what is true and provable.
Be concrete and Lean-aware; where you propose a theorem, spell out the hypotheses you believe are needed.
