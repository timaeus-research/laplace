# Query: architecture of the general relative push-forward statement (Lean target)

## Where we are (all formalised in Lean 4 + Mathlib, laplace repo, or greybook Extras/Germbij)

Setting: loss variables `x ∈ ℝ^d` (integrated), truth variables `s ∈ ℝ^m` (parameters), `F ≥ 0`
analytic, `F(0, s) = 0` (tracked zero), compactly supported positive prior `χ`. Objects:
`Z(t,s) = ∫ χ e^{-tF(x,s)} dx`, `⟨g⟩_{t,s}`, and the energy `H_t(s) = t⟨F⟩_{t,s}`.

Done:
- **Chambers.** From Chris's relative Watanabe modification over the generic locus of truths
  (hironaka `exists_relativeWatanabeModificationOn_generic`), the type `(λ(s), θ(s))` of `F(·,s)` at
  the tracked zero is locally constant on the chambers (greybook `relative_llc_locally_constant`).
- **One-variable walls.** Newton-edge theorem (`EdgeData.tendsto_energy`): `F = E + R`, `E`
  quasi-homogeneous of weights `(α,γ)`, `R ≥ 0` of higher weight ⇒ along `s = σ t^{-γ}`,
  `H_t → ∫E(u,σ)e^{-E}/∫e^{-E}`. Residual on the weighted blow-up divisor = edge form
  (`EdgeData.tendsto_residual`). Two-layer wall `x⁶+x⁴s²+x²s⁶` (two edges, intermediate plateau),
  merging zeros, degenerating units, two-chart competition (Möbius in `c t^{e₂-e₁}`), and the
  hump `1/2 + z/(1+e^z)` for two wells with offset `z = t·F(critical point)` (algebraic assembly,
  not yet the analytic two-well theorem). Empirical (finite-n) versions along schedules.
- **Your previous verdict** (research_wall_divisors_v1): the divisor↔layer bijection is false; the
  invariant object is the *relative push-forward asymptotics*: resolve the function, the projection
  to `S`, and the density together; different compatible resolutions give the same pushed-forward
  expansion; Newton faces are models inside that frame; face-root resolutions and chart competition
  give extra scales, logs, log-shifted transitions.

## What we want now

A **general relative push-forward statement** that (i) is true, (ii) is the theorem the one-variable
wall results are instances of, (iii) can be formalised in stages in Lean with Mathlib (real analysis,
measure theory; no toric geometry library, no Melrose b-calculus; hironaka supplies resolution
*data* as structures: charts with `F∘g = a ∏u_i^{2k_i}`, Jacobian `b ∏u_i^{h_i}`, analytic units).

Candidate formulations we see:

**(P1) Toroidal-chart push-forward.** Hypothesis package: a finite family of charts on a modification
`Y → ℝ^d × ℝ^m` in which `F∘g`, the relative density, AND each truth coordinate `s_j∘g` are monomials
times units (a toroidal morphism to `S`). Conclusion: the fibre integral `Z(t,s)` equals a finite sum of
chart integrals, each of which is a Laplace integral in the fibre coordinates whose parameters are
monomials `τ_D = t · s^{q_D}` ("collapse variables"); asymptotics of each along any ray in
`(log t, log 1/s)`-space is a Boltzmann integral of the residual on the corresponding divisor.
Question: is a *relative toroidal* modification (simultaneously monomialising `F`, the density, and the
coordinate functions `s_j`) available from ordinary embedded resolution of the product ideal
`(F)·(s_1⋯s_m)·(Jac)` in `ℝ^d × ℝ^m`? Does monomialising `s_j` in the ambient coordinates suffice to make
the fibres of `Y → S` tractable (they are then unions of coordinate tori-like sets)?

**(P2) Two-parameter zeta function.** `ζ(z,w) = ∫∫ F(x,s)^z |s|^w χ(x)η(s) dx ds` (one truth variable
for simplicity). Double Mellin: `∫∫ Z(t,s) t^{z-1}s^{w-1} = Γ(z) ζ(-z, w)`. Resolution charts give
poles along the hyperplane arrangement `{2k_i z + q_i w + h_i + 1 = 0}`. The joint asymptotics of
`Z(t,s)` as `t→∞, s→0` is a polyhomogeneous expansion whose exponent lattice is read off the
arrangement; chambers of the `(log t, log 1/s)` plane where one pole dominates give plateaus
`Z ≍ t^{-λ} s^{μ} (log)^m`; rays where two poles tie give the crossovers; the crossover profile is
the Mellin inverse of the residue along the tie, which is exactly the edge Boltzmann integral.
Question: is this the cleanest true statement? Does the fibre-wise `H_t(s)` (a *ratio* of two such
functions, with `∂_t` at fixed `s`) follow from it uniformly, or does the ratio need separate control
(e.g. positivity, uniform integrability along the ray)?

**(P3) Polyhomogeneity on the blown-up corner.** `Z(t,s)` extends to a function on the manifold with
corners obtained by (weighted, iterated) blowing up the corner `{t = ∞, s = 0}` along the rays
`γ_D`, polyhomogeneous on every face; face functions = crossover profiles; corners of the blow-up =
plateaus; log terms at ties. This is Melrose's push-forward theorem for a b-fibration. Question: for
Lean, is there a way to state polyhomogeneity *without* the geometry, e.g. as "for every ray
`s = σ t^{-γ}` and every `γ` the limit exists and is given by a specific integral, uniformly on
compact `σ`-sets, plus rates"? Would that weaker "ray-wise" statement already be resolution-invariant
and imply everything statistical we want (plateaus, layer profiles, which observables jump)?

## Specific questions

1. Which of P1/P2/P3 (or what else) is the right general statement to aim at, and what exactly are
   its hypotheses in the analytic setting (real analytic `F ≥ 0`, compactly supported smooth prior,
   real coordinates with signs)? Please state it as a theorem, with the conclusion about
   `Z(t, s)` and about `⟨g⟩_{t,s}`.
2. Give the **one-chart lemma** in the form most useful for Lean: coordinates `(u, v)`, fibre variables
   `u ∈ ℝ^d`, divisor variable(s) `v`, `F∘g = v^N a(u,v) Φ(u)` with `a > 0` analytic, density
   `v^{p} b(u,v) ∏|u_i|^{h_i}`, `s = v^q`; conclusion for `∫_{fibre} e^{-tF}·density` and for the energy,
   along `t v^N → τ`. Which of these are genuinely one-chart statements and which need the sum over
   charts (competition)?
3. Chart competition: when several charts (divisors) contribute at the same ray, the energy is a
   mass-weighted average and the masses carry powers of `t` (your Test B). State the general
   assembly theorem: given chart-wise asymptotics `Z_D(t,s) ~ C_D(σ) t^{-λ_D} (log t)^{m_D}` along the
   ray, what is `H_t` to leading order, and when do log-shifted transitions occur?
4. For real coordinates: sectors (signs of `u_i`, `v`) and the failure of `s^{1/q}` for even `q` and
   `s < 0` — how do you recommend organising this (oriented blow-up, absolute values with sign
   indices)? Chris's record uses even exponents `2k_i` and `|u_i|^{h_i}`.
5. For `m ≥ 2` truth variables: the parametric linear programme you sketched (monomial constraints
   `A·a + B·γ ≥ 1`, minimise the density-weighted sum of the `a_i`) — is this literally the tropical /
   Newton-polyhedron dual of P2's pole arrangement? Could we formalise the LP statement as the
   *exponent* part of the theorem separately from the coefficient part?
6. Order of Lean targets. Our current EdgeData is: `F = E + R`, `R ≥ 0`, pointwise higher weight,
   compact prior, integrable edge density. Proposed next: (a) comparability version (`G(u,v) := F(v^αu,
   σv^γ)/v → Φ₀(u)` pointwise with `G ≥ cΦ₀`, `Φ₀` coercive), covering units and densities; (b) the
   analytic two-well theorem (Test A) as the first competition statement; (c) the one-chart lemma of Q2
   with `d` fibre variables; (d) the finite-chart sum. Is this the right order, and what would you
   drop or add? Where is the first genuinely new analytic difficulty?

Please be concrete; where you assert a theorem, give the hypotheses you would actually need and the
mechanism of proof (DCT, Mellin, Laplace method), and flag what is folklore vs. what you are deriving.
