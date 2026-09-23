# Spec: a wall-adapted monomial atlas for one truth variable (`OneParameterWallMonomialAtlas`)

**Purpose (laplace side).** The relative push-forward programme (germbij_slop S14) is now
formalised down to the geometric interface: `RescaledData` (dominated rescaling on any measure
space), `MultiDivisorData` (fibre `ℝ^ι`, anisotropic scaling, monomial density), `ChartAssembly`
(finite sum with positive normalisations and `o(∑ L)` remainders), the two-well theorem, and the
exponent LP (`LPData.tendsto_lpExponent`, primal–dual certificate). What is missing is the object that
turns an analytic family `F(x, s) ≥ 0` near a wall point `s₀` into exact fibre integrals in
monomial form, uniformly for `0 < |s − s₀| < ε`. This spec (following the Astra consult
`gpt_responses/research_geometric_extraction_v1.md`) asks for that object and nothing more.

## What is NOT being asked

- No extension of the previously chosen generic modification (`exists_relativeWatanabeModificationOn_*`)
  over the wall; a **new** modification near the wall is fine.
- No smooth central fibre, no fibrewise change of variables **at** `s = s₀`.
- No toroidalisation of the projection, no claim about fibres being unions of coordinate subspaces.
- No analytic fields (`MultiDivisorData`, integrable residuals, power gaps between sectors, absence of
  logarithms). These are false in general (example: `F = x²y² + s²(x² + y²)` has `Z ≍ t^{-1/2} log t`
  along `s = t^{-γ}`, `γ > 1/2`) and belong to the laplace side.

## Inputs

- `Ω ⊆ ℝ^d × ℝ` open, `F : Ω → ℝ` real analytic, `F ≥ 0`; wall parameter `s₀ = 0`.
- A compact `K ⊆ ℝ^d` (support of the prior).
- Non-degeneracy: for all sufficiently small `s ≠ 0`, `F(·, s)` is not identically zero on the
  relevant connected components of the fibre (so the fibre zero set is null).

## The record (fields, schematically)

Geometric part (embedded resolution of `F · s` with closed-box control):

```
space                  -- real analytic (d+1)-manifold Y
map                    -- g : Y → Ω, proper, surjective, iso off {F · s = 0}
finite_charts          -- ι finite; φ_ν : chart maps with closed boxes inside open chart domains
phase_exponents        -- K_ν : Fin (d+1) → ℕ   (even: K_ν = 2 k_ν, from F ≥ 0)
base_exponents         -- q_ν : Fin (d+1) → ℕ, q_ν ≠ 0 on charts meeting the central fibre
jacobian_exponents     -- H_ν : Fin (d+1) → ℕ   (TOTAL-space Jacobian, not relative)
phase_unit  A_ν, jacobian_unit B_ν : analytic on a neighbourhood of the closed box,
  A_ν > 0, B_ν ≠ 0, with uniform upper/lower bounds on the box
phase_normal_form      -- F ∘ g = A_ν(z) ∏ |z_i|^{K_ν,i}
base_normal_form       -- s ∘ g = η_ν ∏ z_i^{q_ν,i},   η_ν ∈ {+1, −1}   (unit ABSORBED, see below)
total_jacobian_form    -- |det Dg| = B_ν(z) ∏ |z_i|^{H_ν,i}
partition_weights      -- ρ_ν ≥ 0 smooth, supported in the charts, ∑ ρ_ν = 1 on g⁻¹(K × [−ε, ε])
small_parameter_cover  -- the same finite atlas covers g⁻¹(K × {s}) for all |s| < ε
```

The base unit can be absorbed: with `s ∘ g = E(z) z^q`, `E ≠ 0`, pick `ℓ` with `q_ℓ > 0` and set
`z_ℓ' = z_ℓ |E(z)|^{1/q_ℓ}`; this is a local analytic coordinate change preserving the monomial ×
unit form of `F ∘ g` and `|det Dg|`. This is why `m = 1` is much easier than `m ≥ 2`.

Derived (fibre) part — may be a companion record proved from the above plus change-of-variables and
partition-of-unity lemmas:

```
sign_branches, solve_index ℓ (q_ν,ℓ > 0)
fibre_parameterisation    -- v = v_ν(u, s) := (|s| ∏_i |u_i|^{-q_i})^{1/q_ℓ} on each sign branch
fibre_domain D_ν(s)       -- {u : (u, v_ν(u,s)) in the closed box}
fibre_phase_formula       -- F∘g(u, v_ν(u,s)) = A_ν(u, v_ν) |s|^{ν} ∏_i |u_i|^{κ_i},
                              ν = K_ℓ/q_ℓ,  κ_i = K_i − q_i K_ℓ/q_ℓ
fibre_density_formula     -- D_{ν,s}(u) = (B_ν(u, v_ν)/q_ℓ) |s|^{p} ∏_i |u_i|^{r_i},
                              p = (H_ℓ+1)/q_ℓ − 1,  r_i = H_i − q_i (H_ℓ+1)/q_ℓ
pointwise_fibre_integral_identity :
  ∀ 0 < |s| < ε, ∀ ψ ≥ 0 measurable (then integrable signed ψ),
    ∫_{ℝ^d} ψ(x, s) dx = ∑_{ν, branches} ∫_{D_ν(s)} (ρ_ν ψ)(g(u, v_ν(u,s))) D_{ν,s}(u) du
```

Mechanism for the density: `dx ds = |det Dg| du dv` and `du ds = |∂s/∂v| du dv` with
`∂s/∂v = q_ℓ s / v`, so the relative determinant is `|det Dg| · |v| / (q_ℓ |s|)`; substituting
`|v| = |s|^{1/q_ℓ} ∏ |u_i|^{-q_i/q_ℓ}` gives the exponents above. The algebraic identities
(phase and density in terms of `(K, H, q)`) are formalised on the laplace side
(`Laplace/Multi/WallFibreFormulas.lean`); the identity itself is what the record must supply.

## Existence statement

> Under the inputs above, there exist `ε > 0` and a `OneParameterWallMonomialAtlas` whose fibre
> identity holds for every `0 < |s| < ε`.

Mechanism: (1) embedded resolution of `F · s` over a neighbourhood of `K × {0}`; (2) properness for
compact control of the preimage; (3) finitely many normal-crossing charts covering the central
preimage; (4) absorb the base unit; (5) shrink boxes for uniform unit bounds; (6) compactness: the
charts cover the preimage of `K × {s}` for all small `|s|`; (7) subordinate partition of unity;
(8) solve the base monomial on sign branches; (9) fibrewise change of variables off the analytic
null set. Steps 1–5 are resolution content; 6–9 are supporting topology/integration lemmas.

## What laplace does with it

`RaySectorCertificate` (laplace): along a schedule `s(t)`, subdivide the fibre decomposition into
finitely many sectors; each retained sector gets a normalisation `L_ν(t) = t^{-λ_ν} (log t)^{r_ν}`
and a `RescaledData`/`MultiDivisorData` limit; discarded sectors get bounds of the same form or
superpolynomial bounds; then `ChartAssembly` with the dominance rule "smaller `λ` wins, then larger
`r`" (`Laplace/Multi/PowerLogDominance.lean`). The restricted version (isolated coercive residual
sectors) is available now; the general one-parameter version needs constrained-monomial integration
with logarithmic sectors, which is the remaining analytic work on our side.
