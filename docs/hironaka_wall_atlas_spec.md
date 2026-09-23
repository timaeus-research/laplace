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

## Status (2026-09-24): the geometric core is proven on a local hironaka branch

Branch `wall-atlas` of the local hironaka worktree (`lean/hironaka-upstream`, based on `a8897879f`;
not pushed), commit `435b6a7`, `Monomialize/Relative/Wall/`:

- `FactorSeparation.lean`: `exists_factor_monomial` — if `F₁ F₂ = S ∏ u_i^{k_i}` near `0` with
  `S ≠ 0`, each factor is a unit times a monomial with exponents adding to `k` (primality of the
  coordinate germs `IsSmoothAt.dvd_or_dvd`, cancellation of a coordinate by density
  `eventuallyEq_of_coord_mul`, induction on the total degree).
- `AbsorbPair.lean`: `exists_chart_absorbing_unit_pair` — the unit-absorbing coordinate change
  `v_j = (S a)^{1/k_j} u_j` transports a second monomial × unit function to the same form.
- `WallChart.lean`: `WallChartAt F ℓ g P` and `exists_wallResolution_of_bo` — the total-space
  Watanabe resolution of `F · z_ℓ` (`watanabe_thm_2_3_of_isConnected_of_bo`) has, at every point
  over the wall `{z_ℓ = 0}`, a centred chart with `F ∘ g ∘ φ⁻¹ = a · u^k` (`a` a unit),
  `z_ℓ ∘ g ∘ φ⁻¹ = S · u^q` exactly (`S = ±1`, `q ≠ 0`), `det D(g ∘ φ⁻¹) = b · u^h`; `g` proper,
  surjective, an analytic isomorphism off `{F · z_ℓ = 0}`.
- `Record.lean`: `exists_wallResolution`, the unconditional instance at the fully Monomialize
  order-reduction family; axioms `propext`, `Classical.choice`, `Quot.sound` only.

So items 1–4 of the mechanism (resolve `F s`, proper, cover the central preimage, absorb the base
unit) are done at the level of "a chart at every point"; the remaining geometric work is the
FINITE atlas with closed boxes and uniform bounds (5–6), the partition of unity (7), and the
fibre identity (8–9). For the fibre identity the intended route reuses the total-space transport
certificates of the existing read-out (`Monomialize/Manifold/Watanabe/Readout.lean`): with
`s ∘ g ∘ φ⁻¹` an exact monomial, the one-dimensional substitution `v ↦ s` inside each box gives the
fibre density `|v|/(q_ℓ |s|)`, and equality of the `s`-integrals against every test function `η(s)`
plus continuity in `s` (compactly supported partition weights) gives the pointwise fibre identity.

Update (2026-09-24, later): steps 5–7 are also proven on the branch (`ebf18d7`, `7cd7abb`):
`WallAtlas`/`exists_wallAtlas` (finite atlas over a compact wall set `C`: closed boxes in the
targets, two-sided unit bounds on the boxes, open cores covering `g⁻¹(C)`),
`eventually_preimage_subset_of_isCompact` (small-parameter cover, Cantor intersection),
`exists_partitionOfUnity_cores`/`exists_partitionOfUnity_smallParameter` (continuous partition of
unity subordinate to the cores on `g⁻¹(L ∩ {|z_ℓ| ≤ ε})`, compactly supported pieces). Remaining:
the fibre identity (steps 8–9); consult `gpt_responses/research_fibre_identity_v1.md`.

## The fibre identity: plan of record (Astra, `gpt_responses/research_fibre_identity_v1.md`)

Route (A), in this order: (1) **weighted total-space transport interface** — hironaka exports, for
the finite atlas, the identity `∫ Ψ(y) dy = ∑_i ∫ w_i(u) Ψ(rep_i u) |det D rep_i(u)| du` for tests
supported in the covered region, with upstairs weights `w_i = ρ_i ∘ φ_i⁻¹` compactly supported in
the CERTIFIED boxes (certify transport on the atlas boxes before the finite subcover, or shrink
consistently); (2) **two-branch substitution** (Euclidean, laplace): split `u = (w, v)` at the solve
index, `s = c(w) v^{q_k}` with `c(w) = S ∏_{j≠k} w_j^{q_j}`, on `v > 0` and `v < 0` separately,
`|ds/dv| = q_k |s|/|v|`; the exceptional set `c(w) = 0` is null; (3) **continuous compact tests**:
for `Ψ = f(x) η(s)`, equality of the `s`-integrals for all `η` gives a.e. equality in `s`; both
sides are continuous in `s ≠ 0` (parameter-local domination: on the effective support the active
coordinates satisfy `|u_j| ≥ (a / ∏ R_m^{q_m})^{1/q_j}`, so the apparently singular powers are
harmless; moving domains handled by proving continuity of the weighted zero extension, never of a
raw indicator), hence equality for every `s ≠ 0` small; (4) **fibre-measure equality** from the
continuous tests, then (5) the **indicator-kernel corollary** for nonnegative/bounded measurable
tests and a compact physical region `K`. Branches: sum over the sign `σ = ±1` of the solved
coordinate only, with the compatibility condition `s · S σ^{q_k} ∏_{j≠k} w_j^{q_j} > 0`; keep `w`
signed. Library boundary: hironaka exports Euclidean representatives, certified boxes, monomial
identities, unit bounds, compactly supported weights and the weighted transport identity; a
Euclidean fibre-transport layer (laplace) proves substitution, continuity, and the fibre-measure
equality; laplace's asymptotics consume only the explicit kernels
`J_{i,σ}(s, w) = w_i(u) |b_i(u)| / q_k · |s|^{α−1} ∏_{j≠k} |w_j|^{h_j − q_j α}` on the solved
domain, zero outside (piecewise definitions, never totalised inverses). Route (B) (fibrewise change
of variables) is the reusable alternative; its new lemma is the Euclidean determinant identity
`|det D(w ↦ X(w, V(w)))| = |det DR| / |∂_v T|`, proved by multiplying `DR` by the unit-determinant
shear `[[I, 0], [DV, 1]]` to make it block triangular.

## Status (2026-09-24, later): steps 8 (weighted transport) and the Euclidean substitution are done

hironaka branch `wall-atlas`, commits `653413d3c` (`WallWeighted.lean`) and `748cefb58`
(`WallIntegral.lean`), all axioms `propext`/`Classical.choice`/`Quot.sound`:

- `WallAtlas.lintegral_eq_sum_charts_box`: for a measurable `L' ⊆ W`, a partition of unity `f` on
  `g⁻¹(L')` subordinate to the cores, and measurable `Ψ ≥ 0`,
  `∫⁻_{L'} Ψ = ∑_i ∫⁻_{box_i ∩ rep_i⁻¹ L'} Ψ(rep_i u) · ofReal(f i (φ_i⁻¹ u)) · ofReal |b_i u ∏ u^{h_i}|`.
  Mechanism: `L' ∖ {F z_ℓ ≠ 0}` is null (`volume_diff_offWall`: it lies in the images under the
  analytic `rep_i` of the coordinate hyperplanes of the boxes, by the partition of unity and the
  exact monomial form of `F z_ℓ ∘ rep_i`); the weights push down to `wallWeight` on the model (the
  value of `f i` at the unique preimage, `g` being injective off the wall), measurable because
  `rep_i` is continuous and injective on the off-wall box (`MeasurableSet.image_of_continuousOn_injOn`);
  then `transportsToOn_of_injOn_of_hasFDerivWithinAt` on `box_i ∩ rep_i⁻¹(L' ∩ off-wall)` with the
  clamped representative `repClamp` (globally continuous) and the Jacobian identity `jac`.
- `WallAtlas.integral_eq_sum_charts` (Bochner): for measurable `Ψ` integrable on `L'`,
  `∫_{L'} Ψ = ∑_i ∫_{chartSet i L'} Ψ(rep_i u) · chartDensity f i u` with
  `chartDensity f i u = f i (φ_i⁻¹ u) · |b_i u ∏ u^{h_i}|`, every chart integrand integrable
  (`integrableOn_chart`); the density is continuous on the closed box
  (`chartDensity_continuousOn`), and the weight vanishes on the target off the open ball
  (`weight_eq_zero_of_notMem_ball`), so the effective support of each chart integrand is inside the
  open ball of the box.

laplace `Laplace/Multi/FibreSubstitution.lean` (`dcdb9e5`, Mathlib only): the two-branch
substitution `s = c v^q` — `solvedCoord c q s = (|s|/|c|)^{1/q}`, `integral_branch_pos/neg`
(`∫_{v>0} Φ = ∫_{s ∈ c·(0,∞)^q} Φ(V(s)) V(s)/(q|s|) ds`, and the `v<0` branch with `−V`), the image
identifications `image_pow_Ioi` (`(0,∞)` or `(−∞,0)` by the sign of `c`) and `image_pow_Iio_eq`,
and `integral_two_branch` (full line, integrable `Φ`).

Remaining for the fibre identity: the Euclidean fibre-transport layer (laplace) — Fubini in the
solved coordinate on each chart box, `integral_two_branch` fibrewise (`c(w) = S ∏_{j≠k} w_j^{q_j}`,
null exceptional set `c(w) = 0`), continuity in `s ≠ 0` of the weighted kernel, and the
fibre-measure equality / indicator-kernel corollary.

## Status (2026-09-24, evening): the Euclidean fibre-transport layer

laplace, Mathlib only:

- `Laplace/Multi/FibreKernel.lean` (`970aa00`): `truthMono S q u = S ∏ u^q`, `solvedCoeff k S q w`
  (`truthMono (insertNth k v w) = solvedCoeff · v^{q k}`), the `lintegral` two-branch substitution
  `lintegral_two_branch` (sign sets `{0 < c(−1)^q s}`, `{0 < c s}`; `solvedCoord_pos/neg_spec`),
  the null exceptional set `volume {c(w) = 0} = 0`, the branch and fibre kernels
  `branchKernel`, `fibreKernel k S q Φ s = ∫⁻ w, branchKernel … w s`, and
  **Fubini in the solved coordinate** `lintegral_mul_comp_truthMono`:
  `∫⁻ u, Φ u · η (truthMono S q u) = ∫⁻ s, η s · fibreKernel k S q Φ s` (measurable `Φ η ≥ 0`,
  `S ≠ 0`, `q k > 0`).
- `Laplace/Multi/WallChartsData.lean` (`35ab2c0`): the Euclidean export interface
  `WallChartsData m ℓ L'` (finite charts, measurable `rep i`, `dom i`, `dens i ≥ 0`, `S i ≠ 0`,
  solve index `k i` with `q i (k i) > 0`, `rep i u ℓ = truthMono (S i) (q i) u` on `dom i`, and the
  `lintegral` transport identity); `chartFun θ i = 1_{dom i} · θ ∘ rep i · dens i`,
  `totalKernel θ s = ∑ i fibreKernel …`; the push-forward identity `lintegral_mul_comp_coord`
  (`∫⁻_{L'} θ(z) η(z ℓ) = ∫⁻ η(s) K_θ(s)`) and the **fibre identity a.e.** `fibre_ae`: for
  `L' = splitAt⁻¹(B ×ˢ A)`, `s ↦ ∫⁻_{z' ∈ A} θ(insertNth ℓ s z')` equals `totalKernel θ` a.e. on
  `B` (uniqueness of densities, `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀`).

Remaining: pointwise identity for `s ≠ 0` by continuity of both sides (route A step 3), the
real-valued kernel for signed integrands, and the instantiation of `WallChartsData` from the
hironaka export (a bridge workspace importing both, as for greybook).

## Status (2026-09-24, night): the fibre identity is closed (pointwise off the wall)

- hironaka `wall-atlas` `dfb72cb2f` (`WallExport.lean`): `WallAtlas.euclidean_export` — for an atlas
  over a measurable `L' ⊆ W` with a partition of unity `f` on `g⁻¹(L')` subordinate to the cores:
  `repClamp i` continuous, `chartSet i L'` measurable, `chartDensityClamp f i` continuous,
  nonnegative, vanishing off the open ball of radius `ρ i > 0`, `S i = ±1`, `∃ k, 0 < qs i k`,
  `repClamp i u ℓ = S i ∏ u^{qs i}` on `chartSet i L'`, and the `lintegral` transport identity with
  these data. This is exactly the field list of laplace's `WallChartsData` (instantiation needs a
  bridge workspace importing both libraries; not done here).
- laplace `FibreContinuity.lean` (`69f14d5`): `continuousAt_fibreKernel` — for continuous `Φ ≤ M < ∞`
  supported in `‖u‖ < ρ`, the fibre kernel is continuous at every `s₀ ≠ 0` (branch kernels are
  continuous off the wall; domination `2M · ofReal(2ρ/(q|s₀|)) · 1_{‖w‖ ≤ ρ}` from
  `branchKernel_le`).
- laplace `FibrePointwise.lean` (`e1f022b`): `WallChartsData.fibre_eq` — for
  `L' = splitAt⁻¹(B ×ˢ A)`, continuous bounded `θ` supported in `L'` and in a ball,
  `∫⁻_{z' ∈ A} θ(insertNth ℓ s z') = totalKernel θ s` for EVERY `s ∈ interior B`, `s ≠ 0`
  (`Measure.eqOn_open_of_ae_eq` from `fibre_ae` and the two continuity statements;
  `WallChartsData` now carries `rep_cont`, `ρ`, `ρ_pos`, `dom_eq`, `dens_cont`, `dens_supp`).

What the germbij consumer gets: the fibre partition function / fibre expectation numerators at a
fixed truth `s ≠ 0` near the wall are finite sums of chart kernels
`∫_w Φ_i(w, ±V_w(s)) · V_w(s)/(q_k |s|) dw` with `V_w(s) = (|s|/|c_i(w)|)^{1/q_k}`, exactly the
inputs of the `RescaledData`/`ChartAssembly` asymptotics. Open: the bridge instantiation, and the
explicit monomial form of the kernels (`WallFibreFormulas` parametrisation) for the exponent
bookkeeping.

## Status (2026-09-24, late): `wall_fibre_identity` — the end-to-end theorem on the hironaka branch

hironaka `wall-atlas` `a1b78e8a7`. Since laplace (Lean 4.33.0) and hironaka (4.33.1) cannot share a
bridge workspace, the Mathlib-only Euclidean layer was mirrored onto the branch verbatim
(`Monomialize/Relative/Wall/Euclid/{FibreSubstitution, FibreKernel, WallChartsData,
FibreContinuity, FibrePointwise}.lean`, namespace `Monomialize.Wall`; it built unchanged) and
instantiated:

- `WallAtlas.toWallChartsData` (`Instance.lean`): the `WallChartsData` of an atlas over `L'` from
  `euclidean_export`'s ingredients; `WallAtlas.fibre_eq`.
- `wall_fibre_identity` (`Theorem.lean`): for `F` analytic on an open `U₀ ⊆ ℝ^{m+1}`, not
  identically zero near `0`, a connected open `W ∋ 0` in `U₀`, compact `B₀ ⊆ ℝ`, `A' ⊆ ℝ^m` with
  `splitAt⁻¹(B₀ ×ˢ A') ⊆ W`: there are `ε > 0` and Euclidean wall data
  `D : WallChartsData m ℓ (splitAt⁻¹((B₀ ∩ [−ε, ε]) ×ˢ A'))` such that for every continuous
  bounded `θ ≥ 0` supported in that region and in a ball, and every `s ≠ 0` interior to
  `B₀ ∩ [−ε, ε]`, `∫⁻_{z' ∈ A'} θ(insertNth ℓ s z') = D.totalKernel θ s`. Axioms: `propext`,
  `Classical.choice`, `Quot.sound`.

So Interface F (the wall atlas with its fibre identity) is a theorem, modulo reading the kernels:
`D.totalKernel θ s = ∑_i ∫⁻_w [Φ_i(w, −V) + Φ_i(w, V)] · V/(q_k |s|)` on the sign branches, with
`Φ_i = θ ∘ rep_i · dens_i`, `V = (|s|/|c_i(w)|)^{1/q_k}`, `c_i(w) = S_i ∏_{j≠k} w_j^{q_ij}`, and
`dens_i = f_i ∘ φ_i⁻¹ · |b_i ∏ u^{h_i}|`. What the asymptotics still need from here is the exponent
bookkeeping of these kernels (the `WallFibreFormulas` parametrisation `ν, κ_i, p, r_i`) and their
`RescaledData` packaging.
