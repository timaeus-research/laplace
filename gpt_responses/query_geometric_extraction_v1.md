# Query: item F — the geometric interface, from Chris's relative modification to the chart data

## What is now formalised (laplace, Lean 4 + Mathlib), so the target is precise

Analytic interface (any measure space `(X, μ)` on the fibre): `RescaledData μ G w Φ₀ w₀ W c` —
rescaled phases `G_t → Φ₀` pointwise, weights `w_t → w₀` with `|w_t| ≤ W`, comparability
`c Φ₀ ≤ G_t` where `w_t ≠ 0`, integrability of `W e^{-cΦ₀}`, `W Φ₀ e^{-cΦ₀}`; conclusions: rescaled
partition function, energy numerator, every bounded observable converge (dominated convergence).
Instances: `DivisorData` (one fibre variable, `x = t^{-α}u`, density `|x|^h`), `MultiDivisorData`
(fibre `ℝ^ι`, anisotropic `x_i = t^{-α_i}u_i`, density `∏|x_i|^{h_i}`, Jacobian `t^{-∑α_i}`),
`GaussianWellData` (a `C²` well from a Taylor bound). Assembly: `ChartAssembly` (finite sum of charts
with positive normalisations `L_i(t)`, remainders `o(∑ L_i)`), two-well theorem with gap. Exponent:
one-variable LP along rays; the general LP (primal-dual certificate) is being formalised now.

Geometric input available (hironaka, Chris, record `a8897879f`): `RelativeWatanabeModificationOn f V S'`:
for `f : ℝ^d × ℝ^m → ℝ` analytic ≥ 0, `V` open with compact closure, `S' ⊆ S` open dense (the
"generic locus"), a proper surjective `g : U → V × S'`, iso off the zero set, with charts `φ` fibred
over `S'` (`(φ P).2 = s`), in which `f ∘ g = a(z) ∏ z_j^{2k_j}` and the RELATIVE (fibrewise) Jacobian is
`b(z) ∏ z_j^{h_j}`, `a > 0`, `b ≠ 0` analytic on a closed box. Three existence theorems: generic
(via Sard on strata of a total-space resolution), `of_zero_at_origin`, `of_equiresoluble`. What it gives
us: chamber theorem (type constant on `S'`). What it does NOT give: anything over the wall `S ∖ S'`.

## What the geometric interface must deliver (Lean-facing)

For a wall point `s₀ ∈ S ∖ S'` and a ray/schedule `s(t) → s₀`, a finite family of charts, each supplying
`MultiDivisorData`-type hypotheses for its fibre integral along the schedule, plus a remainder region
that is `o(∑ L_i)`. Concretely per chart: coordinates `(u, v)` with `u ∈ ℝ^d` (fibre), `v` (divisor
variable(s) transverse), `F ∘ g = v^N a(u,v) Φ(u)`-type expression, `s_j ∘ g = v^{q_j} ε_j(u,v)`, and
the fibrewise density `v^p b(u,v) ∏|u_i|^{h_i} du` — and the identity
`∫_{fibre over s} χ e^{-tF} = ∑_charts ∫_{u} (chart integrand) du + remainder`, pointwise in `s`.

## Questions

1. **What object should hironaka construct?** Options: (a) an embedded resolution of the product
   ideal `(F)·(s_1 ⋯ s_m)` (or of `F · ∏ s_j`) on `V × S`, which monomialises `F` and each `s_j` but
   (as you said) does not by itself give fibre coordinates; (b) a *relative* or *toroidal* resolution:
   a modification `Y → V × S` together with a modification `S̃ → S` such that `Y → S̃` is a toroidal
   (log smooth) morphism in adapted charts — then fibres over points of `S̃` are unions of coordinate
   subspaces intersected with the chart and the relative density is monomial; (c) a "weak" version:
   for each wall point `s₀` and each *ray* direction, a weighted blow-up of `V × S` at `(0, s₀)` with
   weights determined by the Newton polyhedron of `F` in `(x, s)`, iterated at face roots (Astra Tests
   A/B), i.e. resolution *of the ray*, not of the family. Which is (i) provable with the hironaka
   toolkit that exists (embedded resolution of real analytic functions with monomial×unit charts,
   Jacobians, closed-box control), and (ii) sufficient for the analytic interface? Be specific about
   what the statement of record should say.

2. **Pointwise-in-`s` fibre identities.** Change of variables under `g` gives `∫_{V×S'} … dx ds =
   ∫_U …`; disintegrating over `s` yields fibre identities for a.e. `s`. We need them for the
   specific `s(t)` on the schedule (a null set). How do we get pointwise identities: continuity in `s`
   of both sides (both are continuous in `s` for fixed `t` when `χ` has compact support and `F` is
   continuous — is that enough, given the chart integrands may be defined only over `S'`?), or an
   honest fibrewise change of variables in each chart (the chart is fibred over `S'`, so on the fibre
   over `s ∈ S'` the map `z ↦ (chartRep z).1` is a change of variables on `ℝ^d` with Jacobian
   `relJacobian` — is that already pointwise? it seems so for `s ∈ S'`; the problem is `s₀ ∉ S'`).
   Since the schedule `s(t)` lies in `S'` for `t < ∞` (approaching the wall), do we even need
   charts *over* `s₀`? What we need is uniformity of the chart data as `s → s₀`, i.e. charts of the
   generic modification that extend continuously to the closed box over `s₀`. Is "the relative
   modification over `S'` extends to a modification over a neighbourhood of `s₀` after a
   modification of the base" the right statement, and is it true/provable?

3. **From chart data to `MultiDivisorData`.** Given a chart over (a neighbourhood of) the wall point
   with `F∘g = a(z) ∏ z_j^{2k_j}` where now some `z_j` are fibre variables and the truth coordinates
   are `s_j∘g = ε_j ∏ z^{q_j}`: along the ray `s = σ t^{-γ}` the fibre over `s(t)` in the chart is
   `{z : ∏ z^{q_j} ε_j(z) = σ_j t^{-γ_j}}`. The natural parametrisation solves for the "divisor"
   coordinates in terms of the fibre coordinates `u`. Please write the general formula for the
   rescaled fibre integrand and identify `Φ₀` (residual), `α_i` (fibre scaling exponents), the
   collapse exponents, and the relative density exponent `p` in terms of `(k, h, q)` and the
   Jacobian of the implicit solve; and the domination hypothesis (`c Φ₀ ≤ G_t`) — where does it come
   from (positivity of the unit `a` on the closed box gives comparability with the monomial;
   is that enough?).

4. **Remainder region.** Outside the charts contributing at a given ray, the other charts have
   `F ∘ g ≥ t^{-1+ε}`-type lower bounds along the schedule (they sit at other plateaus). The assembly
   needs `R = o(∑ L_i)`. Is the right organising principle the LP: charts whose rate vector is
   feasible-but-not-optimal contribute `t^{-λ' }` with `λ' > λ`, and the remainder is controlled by the
   exponent theorem applied chart by chart? Then the "finite chart family" of the assembly is the set
   of LP-optimal faces. Please state the theorem that packages this.

5. **Minimal spec for Chris.** Given the above, what is the smallest hironaka-side statement (in the
   style of the existing record: a structure with fields, plus an existence theorem) that would let
   us prove, on the laplace side, the layered wall theorem for a general analytic `F` at an isolated
   wall point in one truth variable (`m = 1`), with the two-layer wall and Tests A/B as instances?
   Please write the structure's fields and the existence statement, with the hypotheses you believe
   are actually provable from embedded resolution (and flag those that are not).

Be concrete; where you assert, give the mechanism; distinguish folklore from what you are deriving.
