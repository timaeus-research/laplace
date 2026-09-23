# Query: is the Newton edge at a chamber wall a resolution invariant?

## Setting (established, formalised in Lean)

Tempered posterior on the loss variable `x ∈ ℝ` (later `ℝ^d`) with a "truth" parameter
`s ∈ ℝ` (later `ℝ^m`): weight `χ(x) exp(-t F(x, s))`, `F ≥ 0` analytic, `F(0, s) = 0` for all `s`
(tracked zero). We study the *energy statistic* `E_t(s) = ⟨F⟩_{t,s}` and more generally
expectation values `⟨g⟩_{t,s}`, as `t → ∞` along paths `s = s(t) → 0`.

Away from `s = 0` the local type `(λ(s), θ(s))` (RLCT + multiplicity of `x ↦ F(x, s)` at `x = 0`)
is locally constant ("chamber"); at `s = 0` it jumps ("wall"). We proved (Lean, `NewtonEdge.lean`):

**Newton-edge theorem.** Suppose `F = E + R` with `E` quasi-homogeneous of weights `(α, γ)` in
`(x, s)`: `E(l^α x, l^γ s) = l E(x, s)` for `l > 0`, `E, R ≥ 0` continuous, and `R` of higher weight
along the collapse: `t R(t^{-α} u, σ t^{-γ}) → 0` for each `u`. Then for `s = σ t^{-γ}`,
`⟨F⟩_{t, σ t^{-γ}} → ∫ E(u, σ) e^{-E(u,σ)} du / ∫ e^{-E(u,σ)} du`. So the collapse variable is
`σ = s t^{γ}` and the crossover profile is the Boltzmann energy of the *edge form* `E(·, σ)`.

Examples: degenerating unit `F = (s + x^{2m}) x^{2k}`, edge `E = s x^{2k} + x^{2k+2m}`, weights
`(1/(2k+2m), m/(k+m))`. Merging zeros `F = x²(x−s)²`, `E = F`, weights `(1/4, 1/4)`.

**Two-layer wall (Lean, `TwoLayerWall.lean`, numerically confirmed).** `F = x⁶ + x⁴s² + x²s⁶`.
The Newton polygon (in the exponents `(a, b)` of `x^a s^b`) has two lower edges: `(6,0)–(4,2)`
with weights `(1/6, 1/6)` and `(4,2)–(2,6)` with weights `(1/5, 1/10)`. Both are edges in the
sense of the theorem (the third monomial is the higher-weight remainder). So there are two
layers: along `s = σ t^{-1/6}` the energy goes `1/6 → 1/4` (edge-1 profile is the wall model
`G_{2,1,0}(σ²)`), along `s = σ t^{-1/10}` it goes `1/4 → 1/2` (edge-2 profile is the toy
crossover `G(σ⁵)` of `y⁴ + σ⁵ y²`). The intermediate plateau `1/4` is the type of the shared
vertex `x⁴s²`: a geometry that is neither the wall's (`x⁶`, `1/6`) nor the chamber's
(`x²s⁶`, Morse, `1/2`). Numerics at `t = 10^{30}` show all three plateaus cleanly.

**Resolution check (sympy).** For each example, take the weighted blow-up of the `(x, s)` plane
at the origin with weights `(p, q)` = the primitive integer vector proportional to the edge
weights `(α, γ)`: chart `x = u v^p, s = v^q`. Then `F ∘ g = v^N · Φ(u, v)` with `N` the weighted
order, and the *residual* `Φ(u, 0)` restricted to the exceptional divisor `{v = 0}` equals the
edge polynomial `E(u, 1)` (i.e. the edge form at `σ = 1`). For the two-layer example the two
edges give two weighted blow-ups `(1,1)/6` and `(2,1)/10`, and the residual on each exceptional
divisor is the corresponding edge polynomial, while for weights off the edges (e.g. `(1,1)` on a
single-monomial edge) the residual is a monomial (no crossover, no non-trivial profile).

## The conjecture (please stress-test)

*The wall structure is a resolution invariant.* Concretely, for a log resolution
`g : Y → ℝ × ℝ^m` (or the relative modification of the pair `(x, s)` over the truth space) of
`F` at the wall point `(0, 0)`:

1. The **exceptional divisors `D_i` lying over the wall point** correspond to the layers of the
   wall. Each gives a collapse exponent `γ_i` = ratio `ν_{D_i}(s) / ν_{D_i}(F)` of divisorial
   valuations (and `α_i = ν_{D_i}(x)/ν_{D_i}(F)`), and a collapse variable `σ_i = s t^{γ_i}`.
2. The **residual function** `Φ_i = (F ∘ g) / v^{N_i}` restricted to `D_i` is the edge form at
   `σ = 1`, and the crossover profile along the `i`-th layer is the Boltzmann energy of that
   residual (with the appropriate density from the Jacobian, i.e. the `θ`/`h` data).
3. The **plateaus between layers** are the types read off at the intersection points `D_i ∩
   D_{i+1}` (the vertices of the Newton polygon), giving intermediate `(λ, θ)` values that are
   neither chamber's.
4. Divisors over the wall point on which the residual is a *monomial* contribute no crossover
   (they are the "non-edge" weights); a layer is exactly a divisor with a non-monomial residual.
5. Chris's relative-resolution record (hironaka `Statements.exists_relativeWatanabeModificationOn_*`)
   gives a relative Watanabe modification over the *generic* / *equiresoluble* locus of truths;
   the wall is its non-submersive locus, and the wall structure above should be read off the
   fibres of the modification over the wall point (the special fibre), not from the chambers.

## Questions

(a) Is the identification "edge of the Newton polygon relative to the projection to `s`
    ↔ exceptional divisor of a (toric / weighted) resolution over the wall point ↔ layer of the
    wall" correct in general for `F` non-degenerate with respect to its Newton polygon
    (Kouchnirenko / Varchenko sense, relative to the projection)? What is the right notion of
    non-degeneracy here (in the *relative* setting: `s` is a parameter, `x` is integrated)?
    Where does it fail, and what replaces the Newton polygon when `F` is degenerate (e.g. the
    merging-zeros example `x²(x−s)²` whose edge is the whole `F`)?

(b) In the intrinsic language: the collapse exponent `γ_D = ν_D(s)/ν_D(F)` is a log-canonical-
    threshold-like ratio for the pair `(F, s)`. Is the set of `(α_D, γ_D)` over the exceptional
    divisors above the wall point exactly the set of (inverse) slopes of the Newton polygon in the
    non-degenerate case? Does the *minimal* `γ` (the outermost layer, earliest departure from the
    wall type as `s` grows) have an intrinsic characterisation, e.g. as a jumping number or
    as an lct of `s` relative to the ideal `(F)`?

(c) Multi-variable version: `x ∈ ℝ^d`, `s ∈ ℝ^m`. The distance-to-the-wall quasi-norm on `s`
    (e.g. `s₁² + s₂⁴`) should be `|s|_D := ` the weighted norm with weights `ν_D(s_j)`. Is the
    right general statement "for each divisor `D` over the wall point, the collapse variable is
    the point `[s]` in the weighted projective space `P(ν_D(s_1), …, ν_D(s_m))` together with the
    scale `t^{γ_D}|s|_D`"? Is there a standard name/reference for the Newton polyhedron of a
    function relative to a projection (`(x, s) ↦ s`), i.e. the Newton polyhedron of the family
    `F_s` in the `x`-variables with `s`-weights?

(d) Literature pointers: Varchenko's asymptotics of oscillatory integrals via Newton polyhedra;
    Denef–Loeser / Igusa for zeta functions in families; "relative" or "equisingular" Newton
    polygons; Teissier's polar invariants; Lê–Ramanujam / Zariski equisingularity for the
    constancy of the type along chambers. Which of these is the right frame for "type constant
    along a chamber, Newton edges at the wall"?

(e) A concrete second test case we can formalise next: what is the simplest example where the
    Newton polygon is *degenerate* (so the edge form has a non-isolated zero on the divisor) and
    the layer profile is NOT the Boltzmann energy of a polynomial but requires a further blow-up
    (a "layer within a layer")? Predict its plateau/profile structure so we can check numerically.

Please be concrete and, where you assert something, give the argument or a counterexample.
