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

## The analytic layer: Astra's plan of record (`gpt_responses/research_kernel_asymptotics_v1.md`)

Verdicts on the sketch: (1) the moving cutoff `V < ρ` (i.e. `∏|w_j|^{q_j} > |s|/ρ^q`) is NOT harmless —
it is the LP constraint `Q·α ≤ γ`, and it changes the exponent (`∫_{t^{-γ}}^1 e^{-tx²}` is
`t^{-1/2}`-order only for `γ > 1/2`); (2) the atlas bounds `|a|`, not a positive phase — positivity
of `F ∘ rep` on each sign sector must be an explicit hypothesis; (3) the unit may never be frozen
at `0`: it is evaluated at the limiting FACE point (`∫∫ e^{-t(1+y)x²}`, or `a(0, σ/u)` on a moving
fibre); (4) with merely continuous weights no LP constant is guaranteed (weights like `x^β`,
`e^{-1/x²}`, `1/log(e/x)` change the order) — the safe output is a rescaled limit, possibly `0`, and
`ChartAssembly` needs strict positivity of the constants; (5) `WallChartsData` must be enriched with
the phase data (`kF`, `a`, unit bounds) to connect to asymptotics; (6) `θ = e^{-tF} φ` needs a truth
cutoff and support bookkeeping; (7) `γ = 0` is a separate entry point (positive minimum ⇒
`e^{-t F_min}` factor). The existing `LPData.tendsto_lpExponent` is the log-exponent statement, so
it is compatible with log sectors (Astra's worry about a finite-limit form does not apply).

Two theorems: a **constrained monomial comparison** (`K(t) ≍ t^{-λ}(log t)^m`,
`λ = γp + min_{P_γ} b·α`, `P_γ = {α ≥ 0, Q·α ≤ γ, κ·α ≥ 1 − γν}`, `m = dim` of the optimal face) and
a **certified rescaling** (profile certificate = exact rescaled integral identities + `RescaledData`
hypotheses ⇒ `K/L → C`, numerators `Q/L → J`). Single-monomial log theorem:
`∫_{(0,1)^d} e^{-t ∏ x^{A}} ∏ x^{h} ~ Γ(λ)/(k−1)! · ∏_{i∈M} 1/A_i · ∏_{i∉M} 1/(b_i − λA_i) · t^{-λ}(log t)^{k−1}`
with `b = h+1`, `λ = min b_i/A_i`, `k = #argmin` (`∫∫ e^{-tx²y²} ~ (√π/4) t^{-1/2} log t`); proof by
`y_i = −A_i log x_i`, the simplex volume `z^{k−1}/(k−1)!`, `u = t e^{-Y-z}`, Gamma + dominated
convergence. Chart ties: constants add, no extra log. Recommended order: (1) normalise signed
branch kernels (orthants, explicit cutoff), (2) moving-unit comparison (sandwich by constant-unit
models), (3) certified moving-kernel limit from `RescaledData`, (4) single-monomial power–log
theorem, (5) LP/profile compatibility (a new constrained certificate, not `LPData` unchanged),
(6) finite dominant-cluster assembly generalising `dominated_chart_limit` (`Fin 2` only).

## Status (2026-09-25): the analytic layer, first two lemmas of Astra's plan

laplace, Mathlib only, standard axioms:

- `ChartCluster.lean` (`657c960`): `ChartAssembly.cluster_limit` — with a reference chart `i₀` and
  `L i / L i₀ → d i ≥ 0`, the assembled ratio converges to `(∑ d i J i)/(∑ d i C i)`;
  `ChartAssembly.powLog_cluster_limit` — for `L i = k i · powLog (λ i) (r i)` the weights are
  `k i / k i₀` on the charts sharing the winning pair (smallest `λ`, then largest `r`) and `0`
  elsewhere (Astra's lemma 6; ties add constants, no extra log).
- `LogSectorCore.lean` (`657c960`): `tendsto_logSector_core`:
  `t^λ (log t)^{-n} ∫₀^∞ e^{-t e^{-z}} e^{-λ z} z^n dz → Γ(λ)` (substitution `u = t e^{-z}`,
  dominated convergence with the envelope `u^{λ-1} e^{-u} (1+|log u|)^n`, integrable by comparison
  with three Gamma integrands `integrableOn_gammaLog`).
- `LogSubstitution.lean`, `LogSubstitutionPi.lean` (`ff33ded`, `c9a5f88`): the coordinatewise
  logarithmic substitution `x_i = e^{-y_i/A_i}` on `(0,1)`, and on a tied block
  `(h_i+1)/A_i = λ`: `∫⁻_{(0,1)^{k+1}} ∏ x^h G(∏ x^A) = ∏(1/A_i) ∫⁻_{(0,∞)^{k+1}} e^{-λ∑y} G(e^{-∑y})`
  (induction through the coordinate splitting).
- `SimplexReduction.lean` (`ff33ded`): `lintegral_pi_Ioi_comp_sum`:
  `∫⁻_{(0,∞)^{k+1}} G(∑ y) = ∫⁻_{(0,∞)} G(z) z^k/k!` (power convolution + Tonelli over `{0<z<w}`).
- `LogSectorTied.lean` (`f28f899`, `635b488`): **the tied-block power–log theorem**
  `tendsto_tiedBlock`: `t^λ (log t)^{-k} ∫_{(0,1)^{k+1}} e^{-t∏x^{A}} ∏x^{h} → Γ(λ)/k! ∏ (1/A_i)`
  (Astra's (10)–(11) with all coordinates tied), and `tendsto_x2y2`:
  `∫₀¹∫₀¹ e^{-t x² y²} ~ (√π/4) t^{-1/2} log t` (numerics: the ratio to `√π/4` is `1 + 1.96/log t` at
  `t = 10³, 10⁵, 10⁷`, the `1/log t` relative correction expected from the subleading `t^{-1/2}` term).

Remaining in Astra's plan: untied factors in the single-monomial theorem (`∏_{i∉M} 1/(b_i − λA_i)`),
normalisation of the signed branch kernels with the explicit moving cutoff (lemma 1), the
moving-unit comparison (lemma 2), the certified moving-kernel limit through `RescaledData`
(lemma 3), and the LP/profile compatibility (lemma 5).

## Status (2026-09-25, later): the single-monomial power–log theorem in full

laplace, Mathlib only, standard axioms:

- `LogSubstitutionPiGeneral.lean` (`cdae7ed`): the logarithmic substitution on a block with
  arbitrary exponents, including the empty block (`lintegral_pi_Ioo_log`).
- `LogSectorGeneral.lean` (`0d3b5db`, `2e234fb`): `coreIntegral lam k s = ∫₀^∞ e^{-s e^{-z}} e^{-λz} z^k`,
  measurable in `s` (`StronglyMeasurable.integral_prod_right'`), `lintegral_tiedBlock_ofReal`
  (`s ≥ 0`), and the exact reduction `generalIntegral_eq`: the tied × untied monomial integral is
  `∏(1/A_i)(1/k!)∏(1/A'_j) ∫_{(0,∞)^m} ∏ e^{-(h'_j+1)/A'_j y_j} · J(t e^{-∑ y})`.
- `LogSectorGeneralAux.lean` (`8bb0abe`): `1 + ∑ y ≤ ∏ (1+y)`, `e^{-εy}(1+y)^k` integrable,
  `∫₀^∞ e^{-εy} = 1/ε`, the rescaled core identity `t^λ J(t e^{-Y}) = e^{λY} ∫₀^{te^{-Y}} …`,
  the uniform bound `(1+Y)^k C_k` on the rescaled inner integral and its limit `Γ(λ)`.
- `LogSectorGeneralLimit.lean` (`6e6c14f`): **`tendsto_general`** —
  `t^λ (log t)^{-k} ∫_{(0,1)^{k+1}×(0,1)^m} e^{-t∏x^A ∏x'^{A'}} ∏x^h ∏x'^{h'}
   → Γ(λ)/k! · ∏ 1/A_i · ∏ 1/(h'_j + 1 − λ A'_j)`
  for a tied block `(h_i+1)/A_i = λ > 0` and an untied block `(h'_j+1)/A'_j > λ` (Astra's
  (10)–(11)). Numerics for `A = (2,2)`, `h = 0`, one untied coordinate `x'^1`: `√t I(t)/log t`
  agrees with the predicted `√π/2` to within 0.3% at `t = 10³…10⁷`.

Astra's lemma 4 is therefore complete (both blocks), lemma 6 (`ChartCluster`) too. Remaining:
lemma 1 (normalised signed branch kernels with the explicit moving cutoff), lemma 2 (moving-unit
comparison), lemma 3 (certified moving-kernel limit through `RescaledData`), lemma 5 (LP/profile
compatibility), and the enrichment of `WallChartsData` with the phase data.

## Status (2026-09-25, night): lemma 3, the phase enrichment, and lemmas 1–2

laplace, Mathlib only, standard axioms (`27e35d0`, `52d3db7`, `7260672`); mirrored on the
hironaka branch `wall-atlas` (`2460ed363`, `ab47d8aad`, local only):

- `ProfileCertificate.lean`: `RescaledData.tendsto_den_moving` (the observable may move with `t`,
  uniformly bounded and converging pointwise), and the structure
  `ProfileCertificate l K L X μ G w Φ₀ w₀ W c`: a finite family of `RescaledData` pieces plus
  `∀ᶠ t, K t = L t · ∑ e ∫ w e t e^{-G e t}`. Theorems: `tendsto_K_div_L` (`K/L → ∑ ∫ w₀ e^{-Φ₀}`),
  `tendsto_Q_div_L` (same with a moving observable), `tendsto_energy_div_L`, and `tendsto_ratio`:
  the expectation `Q/K` converges to the ratio of the limiting integrals when the limit is nonzero
  (`limit_pos` gives it from positivity of one piece). This is Astra's lemma 3 — the certified
  moving-kernel limit — as a reusable record; a wall kernel is treated by exhibiting a certificate.
- `WallPhaseData.lean`: `WallChartsData.Phase D F` — the phase data of a chart record: exponents
  `kF`, `hJ`, continuous units `a`, `b` with bounds `0 < m_a ≤ |a| ≤ M_a`, `0 < m_b ≤ |b| ≤ M_b` on
  the closed ball, a continuous weight `0 ≤ wt ≤ 1`, and the identities `F (rep u) = a u ∏ u^kF`,
  `dens u = wt u |b u ∏ u^hJ|` on the closed ball. Lemmas `abs_loss`, `abs_loss_bounds`, `dens_le`.
  On the hironaka branch `WallAtlas.toPhase` builds it from the atlas (`aClamp`, `bClamp`, `wtClamp`
  are the clamped units and pushed-down partition weight), so the enriched record is a theorem.
- `WallKernelNormalised.lean`: **lemmas 1 and 2.** `WallChartsData.solvedPt i σ s w` is the branch
  point `(w, σ V)`; with `|S| = 1`, `s ≠ 0`, `w_j ≠ 0`, `|σ| = 1` and the point in the closed ball,
  `loss_solvedPt`: `F (rep u) = |a u| · |s|^ν ∏|w_j|^{κ_j}` (`ν = k_k/q_k`, `κ_j = k_j − q_j ν`),
  `dens_mul_solvedPt`: `dens u · V/(q_k|s|) = wt u |b u| (1/q_k) |s|^p ∏|w_j|^{r_j}`
  (`p = (h_k+1)/q_k − 1`, `r_j = h_j − q_j (p+1)`), hence `branch_integrand_eq` for the Boltzmann
  integrand `e^{-tF} φ · dens · V/(q_k|s|)`, and the sandwich `branch_integrand_ge ≤ · ≤
  branch_integrand_le` replacing `|a|` by `m_a`/`M_a` and `|b|` by `M_b`/`m_b` (needs `t ≥ 0`,
  `φ ≥ 0`, `F ≥ 0` at the point). The moving cutoff is the closed-ball hypothesis; the density
  vanishes off the open ball (`dens_supp`).

Remaining in Astra's plan: lemma 5 (LP/profile compatibility with the constrained LP), and the
construction of profile certificates for the wall kernels from the sandwich: unique dominant scale,
truth-boundary critical scale, and the tied block via `tendsto_general`.

## Status (2026-09-25, late): lemma 5, the dominant-scale certificate, and the bridge to the model

laplace, Mathlib only, standard axioms (`bd655c9`, `182cb72`, `bf8ac31`, `2aacc97`, `ada83b8`,
`d62af64`); not yet mirrored on the hironaka branch (the bridge imports the seabed's linear change
of variables `integral_comp_mulVec` from `GaussianMomentsPosDef`).

- `ConstrainedLP.lean` (Astra's lemma 5): the polyhedron `P_γ = {α ≥ 0, Q·α ≤ γ, κ·α ≥ δ}`
  (`ConstrainedFeasible`), optimality certificates by dual multipliers with weak duality
  (`ConstrainedLPCert.le`), the exponent `λ = γp + b·α` (`lpExponent`), and the compatibility
  theorem `modelKernel_eq_rescaled`: the constrained model kernel on the box of radius `ρ`,
  `K(t) = A t^{-γp} ∫_{(0,ρ)^d, v_t<ρ} W(x, v_t) ∏x^r e^{-B t^δ a(x, v_t) ∏x^κ}`, equals
  `A t^{-λ}` (with `b_j = r_j + 1`) times the rescaled integral over `∏(0, ρ t^{α_j})` with cutoff
  `D t^{-(γ − Q·α)/q} ∏u^{-Q/q} < ρ` and phase `B t^{δ − κ·α} a ∏u^κ` (Lebesgue change of variables
  `x = t^{-α} u`). Feasibility makes the two remaining `t`-powers `≤ 1` for `t ≥ 1`, and `→ 0`
  when strict.
- `DominantScale.lean` (Astra's certificates (1), (2)): `DominantScaleHyp` (feasible `α`, bounded
  measurable weight and unit converging along the rescaling, unit bounded below by `a₋ > 0` where
  the weight is nonzero, integrable limiting profile) gives a `RescaledData`
  (`DominantScaleHyp.rescaledData`) and hence `t^λ K(t) → A ∫ w₀ e^{-Φ₀}`
  (`DominantScaleHyp.tendsto_modelKernel`). The limiting domain is `(0,ρ)` in the unscaled and
  `(0,∞)` in the scaled coordinates, cut by the tied cutoff when `Q·α = γ`; the limiting phase is
  `B a₀(u) ∏u^κ` when `κ·α = δ` and `0` otherwise (the unit is evaluated at the face point through
  `a₀`, never frozen). Integrability of the profile is the hypothesis encoding uniqueness of the
  dominant scale.
- `OrthantSplit.lean`: `∫ f = ∑_ε ∫_{(0,∞)^ι} f(ε·x)` for measurable `f` on `ι → ℝ`
  (`lintegral_eq_sum_orthants`).
- `WallModelBridge.lean`, `WallModelKernel.lean` (Astra's step 1.1, completed): along
  `s = σ t^{-γ}`, the branch kernel on the orthant `ε·x` is the sum over the admissible branches
  `±V` (`0 < S ∏(±1)^{q_j} (±1)^{q_k} σ`, constant on the orthant) of the real branch integrands,
  each equal to `A t^{-γp}` times the constrained model integrand with `A = |σ|^p/q_k`,
  `B = |σ|^ν`, `D = |σ|^{1/q_k}`, `δ = 1 − γν`, `Q_j = q_j`, weight `1_{rep u ∈ L'} φ(rep u) wt |b|`
  and unit `|a|` at the branch point (`branchKernel_orth_eq`, `branchReal_eq_model`; the solved
  coordinate is the model cutoff variable and the chart ball is the model domain). Integrated:
  `fibreKernel_eq_sum_modelKernel`, `totalKernel_eq_sum_modelKernel`, `totalKernel_toReal` — the
  ambient fibre integral of `e^{-tF} φ` over the truth fibre (through `fibre_eq`) is a finite sum
  of constrained model kernels, one per chart, orthant and admissible branch.

What remains for the end-to-end statement: for each model kernel, a `DominantScaleHyp` (the
scale `α` from the constrained LP of the chart, the convergence of `wt |b| φ` and `|a|` along the
rescaling from continuity, positivity of the unit on the support of the weight, and the
integrability of the profile), then `ChartAssembly`/`cluster_limit` over the finitely many terms;
the tied (logarithmic) faces go through `tendsto_general` instead of a single dominant scale.

## Status (2026-09-25, later still): the certificate of a wall model kernel

laplace `WallCertificate.lean` (`d77984a`), Mathlib only, standard axioms. For one term of
`fibreKernel_eq_sum_modelKernel` (chart `i` with phase data and `|S| = 1`, orthant `ε`, admissible
branch `b`) and a feasible scale `α` of the chart's constrained LP, `wallDominantScaleHyp` produces
the `DominantScaleHyp` of `DominantScale.lean`, hence (`tendsto_modelKernelOf`)
`t^λ K_{i,ε,b}(t) → A ∫ w₀ e^{-Φ₀}` with `λ = γp + ∑ (r_j + 1) α_j`. The branch point converges
to the limiting branch point `(ε·facePt(u), ± limitCut(u))` (`tendsto_bridgePt`), which lies in the
open chart ball for `u` in the limiting domain (`limitBranchPt_mem_ball`); the unit `|a|` and the
weight `φ(rep) wt |b|` converge by continuity, and the chart-domain indicator is eventually `1`
where `φ ≠ 0` because the branch point solves the truth equation (`truthMono_bridgePt`,
admissibility) and, by hypothesis `hLφ`, the truth fibre where `φ ≠ 0` eventually lies in `L'` (the
slab of the fibre identity gives this when `0` is interior to the truth set and `φ` is supported in
the cylinder over `A'`). Extra hypothesis on the record: `rep u ℓ = truthMono S q u` on the closed
ball (true for the hironaka instance: `repClamp_apply_truth`). The remaining hypothesis is the
integrability of the limiting profile (twice), which encodes the uniqueness of the dominant scale.

## Status (2026-09-25, end of day): the expectation along the truth fibre

laplace `PowerAssembly.lean`, `WallFibreExpectation.lean` (`db71f23`), Mathlib only, standard
axioms. `tendsto_sum_ratio`: for finitely many kernels with `t^{λ_i} K_i → C_i`, the ratio of two
such finite sums converges to the ratio of the constants at the minimal scale `λ₀` (nonzero
dominant denominator); the non-dominant terms are absorbed automatically (no positivity of every
constant, unlike `ChartAssembly`). `tendsto_fibre_expectation`: for a chart record with phase data
and `|S_i| = 1`, a nonnegative measurable loss, the truth coordinate of `rep` monomial on the closed
balls, two localised observables `ψ, χ` (continuous, nonnegative, bounded, supported in `L'`), a
certified scale `α(i, ε, b)` for every admissible term (`ConstrainedFeasible` for the chart's LP and
`ProfileIntegrableOf`, the integrability of the limiting profile with envelope constant `1`), and a
nonzero dominant denominator constant,
`K^ψ(t) / K^χ(t) → ∑_{λ_p = λ₀} C^ψ_p / ∑_{λ_p = λ₀} C^χ_p` along `s = σ t^{-γ}`,
where `K^φ(t) = (totalKernel (e^{-tF} φ) s_t).toReal` is, through the fibre identity, the ambient
integral of `e^{-tF} φ` over the truth fibre, `λ_p = γ p_i + ∑ (r_j + 1) α_j(p)` and
`C^φ_p = A_i ∫ w₀ e^{-Φ₀}` (`termConst'`). This is the Euclidean half of the general relative
push-forward statement of S14 for pure-power (non-logarithmic) dominant faces; the geometric half
(`wall_fibre_identity`, `WallAtlas.toPhase`) lives on the hironaka branch, and the two halves are
mirrored rather than combined because of the toolchain difference.

Next: a concrete instance exercising the chain (a trivial chart with `F = (1 + x²) s² x²`), the
logarithmic faces (tied blocks through `tendsto_general`), and the hironaka mirror of the analytic
layer (`integral_comp_mulVec` must be copied into the Euclid namespace).

## Status (2026-09-25, night): the chain closes on an instance

laplace `ToyWallRecord.lean`, `ToyWallLimit.lean` (`ad6f574`), Mathlib only, standard axioms.
The identity chart on the sup-norm unit ball of `Fin 2 → ℝ` for `F = (1 + x²) s² x²` (truth
monomial `s`: `S = 1`, `q = (1, 0)`, solve index `0`; density `1` on the half ball and vanishing
off the open unit ball; slab `L' = [-1/2, 1/2] × closedBall(1/2)`) is a `WallChartsData` with phase
data (`kF = (2, 2)`, `hJ = 0`, unit `1 + x² ∈ [1, 2]`, `b = 1`, weight the density). Its model
constants are `q_k = 1`, `Q = 0`, `ν = κ = 2`, `p = r = 0`, `δ = 1 − 2γ`, `A = 1`, `B = σ²`,
`D = |σ|`; the scale `α = (1 − 2γ)/2` is feasible (phase constraint tied, truth strict), the
limiting branch point is the origin, the limiting profile is `σ² u²` on `(0, ∞)`
(`ProfileIntegrableOf` holds), and each admissible term has `termConst = φ(0) √(π/σ²)/2`. Hence
`toy_tendsto_fibre_expectation`: for `0 < γ < 1/2`, `σ > 0` and localised observables `ψ, χ` with
`χ(0) > 0`, the ratio of the total kernels along `s = σ t^{-γ}` converges to `ψ(0)/χ(0)` — every
hypothesis of `tendsto_fibre_expectation` is discharged on an instance ("instances, not names").
The predicted kernel asymptotic `∫ e^{-tF} φ ~ φ(0) √π/|σ| · t^{-(1−2γ)/2}` over the fibre is the
sum of the two admissible terms (two orthants, the `+V` branch).

## Status (2026-09-25, close): the ambient theorem on the hironaka branch

hironaka `wall-atlas` (local only), standard axioms:

- `Monomialize/Relative/Wall/Euclid/*` (`f0b503d80`): the analytic layer mirrored (`LinearChange`
  = the two change-of-variables lemmas of `GaussianMomentsPosDef`; the core of `RescaledData`
  without the `DivisorData` instance, with the two exponential inequalities it uses copied in;
  `OrthantSplit`, `ConstrainedLP`, `DominantScale`, `WallModelBridge`, `WallModelKernel`,
  `WallCertificate`, `PowerAssembly`, `WallFibreExpectation`, `ToyWallRecord`, `ToyWallLimit`).
  The mirror is built with `warningAsError`; the only edits were `omit [l.IsCountablyGenerated] in`
  on four `RescaledData` lemmas and one wrapped line.
- `Monomialize/Relative/Wall/TheoremPhase.lean` (`d72140369`, `28cd700d1`):
  `wall_fibre_identity_phase` — the record of `wall_fibre_identity` with its `Phase`
  (`WallAtlas.toPhase`), `|S_i| = 1` (`WallAtlas.sign`) and the truth coordinate on the closed
  chart balls (`repClamp_apply_truth`), transported across the slab identity by a `PSigma`;
  **`wall_fibre_expectation`** — for an analytic loss `F` near a wall (the hypotheses of
  `wall_fibre_identity`, plus `Continuous F`, `F ≥ 0`, `0 ∈ interior B₀`), the resolution produces
  `D`, `P` such that along `s = σ t^{-γ}` (`σ ≠ 0`, `γ > 0`), for localised observables `ψ, χ`
  supported in the slab and certified scales for every admissible term of `D`,
  `∫_{A'} e^{-tF} ψ(·, s_t) / ∫_{A'} e^{-tF} χ(·, s_t) → ∑_{λ_p = λ₀} C^ψ_p / ∑_{λ_p = λ₀} C^χ_p`.
  This is the general relative push-forward statement of S14 for pure-power dominant faces, end to
  end: geometric half (resolution, atlas, fibre identity) and analytic half (constrained LP,
  dominant-scale certificates, assembly) in one theorem, with the per-chart certificates as its
  hypotheses.

Numerics for the toy (`F = (1 + x²) s² x²`, `σ = 1.3`, `γ = 0.2`): `t^{(1−2γ)/2} K_φ(t)` is
`1.575, 1.451, 1.399, 1.377` at `t = 10³, 10⁵, 10⁷, 10⁹` against the predicted `√π/σ = 1.363`, and
the ratio `K_ψ/K_φ` is `1.72, 1.88, 1.95, 1.98` against the predicted `ψ(0)/φ(0) = 2`.

Open: the logarithmic (tied) faces, where the single dominant scale is replaced by the
single-monomial power–log theorem; certificates for concrete resolved charts beyond the toy.

## Status (2026-09-26): Astra's review of the end-to-end theorem; the logarithmic endpoint

Astra's adversarial review (`gpt_responses/review_endtoend_v1.md`): the combined statement is sound
as a *conditional* pure-power theorem. Confirmed: the mixed scaled/unscaled limiting domain with the
tied cutoff, the unit at the face point `a₀(u) = |a(u∞)|` (not `a(0)`), the non-circularity of the
denominator condition, the pointwise (not a.e.) fibre identity we use. Limitations to document:
`ProfileIntegrableOf` is an *unweighted* test (it can fail for a chart whose weighted kernel is
harmless or identically zero), every admissible term is currently required to be certified at its
own scale (a subleading logarithmic chart blocks the theorem although negligible), `hmin` is
imposed on inadmissible terms too. In the toy, `γ = 1/2` (`α = 0`, bounded profile with the
nonconstant unit) and `γ > 1/2` (`α = 0`, zero phase, `I_φ → ∫_{A'} φ(0, x) dx`) are covered by the
theorem, not vacuous. For logarithmic faces the exact constant is `A ρ^{∑c} Vol_k(F) ∫_Y W∞ e^{-c·y}
e^{-H(y)}` (face volume times a transverse profile integral; the unit does not average over the
face; the Gamma product is the separable special case), and its general certificate is a research
project (tube/boundary estimates). Recommended next: (5) power–log assembly with lexicographic
dominance and negligible terms; (4) a two-sided sandwich for a tied block with `Q = 0`.

Landed accordingly (laplace, Mathlib only, standard axioms):

- `LogModel.lean` (`dd9a2bb`): `modelKernel_const_eq` — the constant-unit, constant-weight model
  kernel with `Q = 0` is `A t^{-γp} w₀ ρ^{∑(r+1)} tiedBlockIntegral κ r (B a₀ ρ^{∑κ} t^δ)` past
  the cutoff (box scaling `x = ρ y`); `tendsto_modelKernel_const` — for a fully tied face
  (`(r_i+1)/κ_i = λ`), `t^{γp+δλ} (log t)^{-k} K(t) → A w₀ ρ^{∑(r+1)} (B a₀ ρ^{∑κ})^{-λ} δ^k
  Γ(λ)/k! ∏ 1/κ_i` (the `B^{-λ} δ^k` factors Astra insists on).
- `PowerLogAssembly.lean` (`2c341fd`): `tendsto_negligible_of_certified` (a term certified at
  `(λ, k)` is `o(1)` at a lexicographically smaller `(λ₀, k₀)`), `tendsto_sum_ratio_powLog`
  (dominant set with limits, all other terms `o(1)` at the dominant normalisation),
  `tendsto_sum_ratio_lex` (every term certified at its own pair; dominant set = the lexicographic
  minimum). This is the assembly that accepts `tendsto_general` terms and does not require
  certifying irrelevant charts.

Next: the two-sided sandwich for a fully tied model kernel with moving unit and weight (Astra §4),
then the `WallFibreExpectation` variant built on `tendsto_sum_ratio_powLog`.

- `LogSandwich.lean` (`adc0715`): Astra's short logarithmic theorem for `Q = 0`. A fully tied model
  kernel with moving unit `aL ≤ a ≤ aU` on the box and moving weight `0 ≤ W ≤ wU`, bounded below by
  `wL` on a smaller box `(0, RL)^{k+1}`, is squeezed between two constant-unit model kernels
  (`modelIntegrand_le_const`, `const_le_modelIntegrand`; the model integrand is integrable because
  `r_i > −1` on a tied face, `integrable_box_prod_rpow`), so with `Λ = γp + δλ` and `C = tiedConst`,
  `C(RL, aU, wL) − ε ≤ t^Λ (log t)^{-k} K(t) ≤ C(ρ, aL, wU) + ε` eventually
  (`modelKernel_sandwich`). The two constants differ by `(aU/aL)^λ`, `wU/wL` and the box ratio; the
  exact constant of a fully tied face is the constant-unit one with the unit at the origin (the face
  point), which needs the localisation argument of Astra §3.
- `WallFibreExpectationDominant.lean` (`7b7a96e`): `tendsto_fibre_expectation_dominant` — only a
  set `S` of terms is certified (admissible, common exponent `λ₀`, feasible scale, integrable
  profile); every other term is assumed `o(1)` at `t^{λ₀}` for both observables (supplied by a
  certificate at a larger exponent through `tendsto_negligible_of_certified`, by a logarithmic
  sandwich, or by a vanishing weight); the ratio converges to `∑_S C^ψ / ∑_S C^χ`. This removes the
  need to certify irrelevant charts at their own scales (Astra §1.1, §5).

hironaka `wall-atlas` (local): the logarithmic modules and the dominant-set variant are mirrored
(`253278276`: `LogSubstitution`, `LogSubstitutionPi`, `SimplexReduction`, `LogSectorCore`,
`LogSectorTied`, `PowerLogDominance`, `LogModel`, `PowerLogAssembly`, `LogSandwich`,
`WallFibreExpectationDominant`; one wrapped line), and `TheoremPhase.lean` carries the ambient
`wall_fibre_expectation_dominant` (`64ea01529`): the resolution's record with certificates for a
dominant set of terms only, the rest assumed negligible at the dominant normalisation.
- `WallTermPositivity.lean`: `termConst_pos` — the term constant is positive when the limiting
  weight is positive on the limiting domain and that domain has positive measure (integrand
  nonnegative, integrable by the certificate's envelope, positive on the domain); with the
  measurability of `facePt`, `limitCut`, `limitBranchPt`, `limitWeight`, `limitUnit` and
  `dsProfile`. This supplies the nonzero-denominator hypothesis of both fibre-expectation theorems.
- `LimitDomainMeasure.lean`: the limiting domain is open (`isOpen_limitDomain`; the cutoff function is
  continuous on the positive orthant), hence of positive measure when nonempty
  (`volume_limitDomain_pos`), and nonempty when the truth constraint is strict
  (`limitDomain_nonempty_of_strict`). With `termConst_pos` this discharges the denominator
  hypothesis from positivity of the limiting weight alone in the strict-truth case.

## How the pieces fit (reading guide, 2026-09-26)

Geometric half (hironaka `wall-atlas`, local): `exists_wallResolution` → `WallAtlas`
(`exists_wallAtlas`, partition of unity `exists_partitionOfUnity_smallParameter`) → weighted
transport (`WallWeighted`, `WallIntegral`, `WallExport`) → the Euclidean record
`WallAtlas.toWallChartsData` with phase `WallAtlas.toPhase` (`Instance.lean`) → the pointwise
fibre identity `wall_fibre_identity` / `wall_fibre_identity_phase` (`Theorem.lean`,
`TheoremPhase.lean`).

Euclidean half (laplace `Laplace/Multi`, mirrored to `Monomialize/Relative/Wall/Euclid`):

1. Fibre transport: `FibreSubstitution` (two-branch `s = c v^q`), `FibreKernel`
   (`branchKernel`, `fibreKernel`, Fubini in the solved coordinate), `WallChartsData`
   (record, `chartFun`, `totalKernel`, a.e. identity), `FibreContinuity`, `FibrePointwise`
   (`fibre_eq`, pointwise for `s ≠ 0` interior).
2. Phase data and normalisation: `WallFibreFormulas`, `WallKernelExplicit` (`ν, κ, p, r`),
   `WallPhaseData` (`Phase`), `WallKernelNormalised` (`branch_integrand_eq`, moving-unit sandwich).
3. Constrained model: `ConstrainedLP` (`P_γ`, `ConstrainedLPCert`, `modelKernel`,
   `modelKernel_eq_rescaled`), `OrthantSplit`, `WallModelBridge` + `WallModelKernel`
   (`fibreKernel_eq_sum_modelKernel`, `totalKernel_toReal`: chart kernel = sum of model kernels
   over orthants and admissible branches).
4. Certificates: `RescaledData` (dominated rescaling), `ProfileCertificate`, `DominantScale`
   (`DominantScaleHyp`, `tendsto_modelKernel`), `WallCertificate` (`wallDominantScaleHyp`,
   `tendsto_modelKernelOf`), `WallTermPositivity` (`termConst_pos`), `LimitDomainMeasure`.
5. Assembly and the theorem: `PowerAssembly` (`tendsto_sum_ratio`), `PowerLogAssembly`
   (`tendsto_sum_ratio_powLog`, `tendsto_sum_ratio_lex`), `WallFibreExpectation`
   (`tendsto_fibre_expectation`), `WallFibreExpectationDominant`; ambient versions
   `wall_fibre_expectation`, `wall_fibre_expectation_dominant` (hironaka `TheoremPhase.lean`).
6. Logarithmic faces: `LogSectorCore`, `LogSubstitution(Pi)`, `SimplexReduction`,
   `LogSectorTied` (`tendsto_tiedBlock`), `LogSectorGeneral(Aux/Limit)` (`tendsto_general`),
   `LogModel` (`tendsto_modelKernel_const`), `LogSandwich` (`modelKernel_sandwich`),
   `ChartCluster` (`powLog_cluster_limit`).
7. Instances: `ToyWallRecord`, `ToyWallLimit` (`toy_tendsto_fibre_expectation`, identity chart,
   `Q = 0`); `BlowupSectorRecord`, `BlowupSectorLimit` (`bs_tendsto_fibre_expectation`): the
   blow-up chart `(x, y) ↦ (xy, y)` for `F = z₀² + z₁²`, truth coordinate `z₀`, over the sector
   `|z₀| ≤ |z₁| ≤ 1`. Mixed truth monomial `q = (1, 1)` so `Q = 1 ≠ 0`; the transport identity is
   the change of variables with Jacobian `|y|` (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
   the null line `z₁ = 0` by `addHaar_submodule`). Constants (solving for `y`): `ν = 2`, `κ = −2`,
   `p = 1`, `r = −2`, `δ = 1 − 2γ`, `A = |σ|`, `B = σ²`; LP vertex `α = γ − 1/2` for `γ > 1/2`,
   `λ = 1/2`, tied phase, strict truth; certificate from `ProfileIntegrableOf.of_vertex` in its
   `κ_j < 0` case (`η = 1/2`); term constant `φ(0)√π/2` (Gamma integral in `1/u`); limit
   `ψ(0)/χ(0)`, matching the direct `∫ e^{-t(s² + z₁²)} ψ dz₁ ~ √(π/t) ψ(0)`.
   `BlowupAtlasRecord`, `BlowupAtlasLimit` (`at_tendsto_fibre_expectation`): the genuine two-chart
   atlas — charts `A : (x, y) ↦ (x, xy)` and `B : (xy, y)` over the unit box, glued by the
   partition of unity `ω_A = clamp((4z₀² − z₁²)/(z₀² + z₁²))`, `ω_B = 1 − ω_A`, whose chart
   pullbacks `clamp((4 − y²)/(1 + y²))`, `1 − clamp((4x² − 1)/(x² + 1))` are continuous (the
   blow-up resolves the angular discontinuity at the origin). Transport identity `at_transport` =
   two changes of variables off null lines. Chart `A` (`q = (1, 0)`, `Q = 0`, `κ = 0`, `p = 1`,
   `r = 0`) has LP optimum `α = 0`, `λ_A = γ`, phase slack (trivial certificate); chart `B` is the
   sector chart with `λ_B = 1/2`; for `γ > 1/2` chart `A` is subdominant and the ratio limit is
   `ψ(0)/χ(0)` from the two-chart transport. Chart indices are `iA`, `iB : atData.ι` with
   `forall_index`; a `Fin 2` numeral in an `atData.ι` slot breaks every `rw` (motive not
   type-correct at implicit transparency).
   `BlowupAtlasHalf` (`at_tendsto_fibre_expectation_half`): the same atlas at `γ = 1/2`, where
   both charts have exponent `1/2` (chart A tied at `α = 0` with profile `σ²(1+y²)`, chart B's
   vertex collapsed to `α = 0` with profile `σ²(1+x²)x^{-2}`), all four admissible terms are
   dominant without closed-form constants, every face map is the origin, and the point theorem
   of `LimitingMeasure` gives `ψ(0)/χ(0)` — the "two genuinely leading charts" test. Uses
   `termConst_pos_of_subset` (positivity on a positive-measure subset), `termMeasure_univ`
   (mass = term constant of `1`) and `termMeasure_le_limitMeasure`.

Consult record: `gpt_responses/research_fibre_identity_v1.md`, `research_kernel_asymptotics_v1.md`,
`review_endtoend_v1.md`, `research_logconst_v1.md`.
- `LogExactConstant.lean`: the exact constant of a fully tied logarithmic face (`Q = 0`). The box
  radius cancels from `tiedConst` on a tied face (`tiedConst_eq`, since `r_i + 1 = λ κ_i`), so the
  constant-unit kernels over nested boxes share their power–log constant and the integral away
  from the face point is negligible; for `W`, `a` continuous at the face point `(0, 0)` (box and
  cut variable), with the global bounds `0 ≤ W ≤ wU`, `a ≥ aL > 0`,
  `t^{γp+δλ}/(log t)^k K(t) → A W(0,0) (B a(0,0))^{-λ} δ^k Γ(λ)/k! ∏ 1/κ_i`
  (`tendsto_modelKernel_tied`), by a three-kernel sandwich (no Fubini, no dimension induction).
  Astra's `research_logconst_v1` confirms the route and the hypotheses (local continuity plus
  global unit/weight bounds), and ranks the next targets: a two-chart atlas-level ratio example,
  then the limiting measure on the dominant strata, then the degenerate-LP classification
  (integrable ⇔ isolated optimum in the polyhedral monomial model, `h·d < 0` on the recession
  cone with `κ·d ≤ 0`).
- `LimitingMeasure.lean` (Astra's candidate (iii)): each dominant admissible term `p` carries the
  finite measure `termMeasure p = (rep ∘ limitBranchPt)_* (A 1_L wt|b| ∏u^r e^{-Φ₀} du)` on the
  ambient space and `termConst p φ = ∫ φ dμ_p` (`termConst_eq_integral`); `limitMeasure` is the
  sum over `dominantTerms`; `tendsto_fibre_expectation_measure` restates the main theorem as
  `⟨ψ⟩_χ → ∫ψ dμ / ∫χ dμ` — the expectations retain the normalised measure `μ/μ(1)` and nothing
  else (not `λ₀`, not the amplitude); `limitMeasure_eq_zero` (vanishes off the face images) and
  `tendsto_fibre_expectation_point` (constant face maps ⇒ `ψ(z₀)/χ(z₀)`, the toy/blow-up case).
- `WallLogTerm.lean`: the log constant at the chart level. `bridgePt 0 0 = 0`; the chart weight
  (observable supported in `L'`) and the unit are jointly continuous at the face point
  (`tendsto_weightFn_face`, `tendsto_unitFn_face`); the unit is `≥ m_a` on the box for small cut
  values (`ma_le_unitFn`, the cut-local form now used by `tendsto_modelKernel_tied`); hence
  `tendsto_modelKernelOf_tied`: for a chart with `Q = 0` and a fully tied transverse face,
  `t^{γp+δλ}/(log t)^k K_{i,ε,b}(t) → tiedConst A B δ κ r λ ρ |a(0)| (φ(rep 0) wt(0) |b(0)|)`.
- `WallFibreExpectationLog.lean`: `tendsto_fibre_expectation_lex` assembles wall terms certified
  at their own pairs `(λ_p, k_p)` into the ratio limit over the lexicographically dominant terms
  (`tendsto_sum_ratio_lex` + `totalKernel_toReal_eq_sum_terms`); the three certifications in
  `termKernel` form: `tendsto_termKernel_of_not_admissible` (vanishing branch),
  `tendsto_termKernel_vertex` (`(λ_p, 0)` via `tendsto_term`), `tendsto_termKernel_tied`
  (`(γp + δλ, k)` via `tendsto_modelKernelOf_tied`, record `WallChartsData (k+1)`).
Open problems: a term theorem for partially tied faces (some `κ_j α_j` tied, others scaled), the
equivalence "profile integrable ⇔ isolated LP optimum" at degenerate (non-vertex) optima — the
"only if" half is now general (`RecessionDirection`), the "if" half is the vertex case — and
certificates for concrete resolved charts beyond the identity chart.
- `RecessionObstruction.lean`: the coordinate case of Astra's recession-cone characterisation
  (§1.2). If a scaled coordinate `j` is invisible to the limiting phase (`κ_j ≤ 0`) while its
  density does not decay (`r_j ≥ −1`), the unweighted profile is not integrable
  (`not_integrable_of_coordinate_recession`: the shells `u_j ∈ [eⁿ, eⁿ⁺¹)` each carry a fixed
  positive mass), so `ProfileIntegrableOf` fails (`not_integrable_envelope_of_recession`, strict
  truth constraint). This is the "only if" half for coordinate directions.
- `RecessionDirection.lean`: the same obstruction along an arbitrary direction `d ≠ 0`, without
  shells. If the domain is invariant under the flow `u ↦ e^{s d} ⊙ u` (`flow`), contains a box,
  the phase is bounded by `K ∏ u^κ` with `d·κ ≤ 0`, and `d·(r+1) ≥ 0`, then `1_L ∏u^r e^{-Φ}` is
  not integrable (`not_integrable_of_recession_direction`): the tails
  `A_n = L ∩ {n|d|² + m₀ ≤ ⟨d, log u⟩}` (`logHeight`) decrease to `∅`, so by
  `tendsto_setIntegral_of_antitone` their integrals tend to `0`, while the transported box
  `e^{nd} ⊙ K₀ ⊆ A_n` carries mass `≥ e^{n d·(r+1)} J₀ ≥ J₀ > 0` by the change of variables
  `integral_comp_rescale` (`flow_eq_rescale`, `prod_flow_rpow`). For the limiting domain,
  `not_integrable_envelope_of_recession_direction`: any `d ≠ 0` supported on the scaled
  coordinates with `d·κ ≤ 0`, `d·(r+1) ≥ 0` forbids the certificate (strict truth). This is the
  full "only if" direction of the recession-cone reading for the unweighted profile. Corollary
  `not_integrable_envelope_of_two_scaled`: two scaled coordinates (strict truth) always forbid
  the certificate, via `d = ±(κ_j e_i − κ_i e_j)` (or `±e_i`) — an isolated optimum has at most
  one scaled coordinate, so the vertex certificate covers every isolated strict-truth optimum.
- `VertexCertificate.lean`: the converse in the generic case. At a *strictly optimal vertex* of
  the constrained LP — one scaled coordinate `j`, `α = (δ/κ_j) e_j > 0` (tied phase), strict truth
  constraint, `η = (r_j+1)/κ_j > 0` (either sign of `κ_j`; for `κ_j < 0` the Gamma integral comes
  from the `p > 0` one by `x ↦ 1/x`, `integral_comp_rpow_Ioi` at `p = −1`), and
  `κ_i η < r_i + 1` for `i ≠ j` — the profile certificate holds:
  `integrable_vertexDom` integrates out `u_j` (a Gamma integral, `integral_rpow_mul_exp_neg_mul_rpow`
  after `volume_preserving_piFinSuccAbove` + `integrable_prod_iff'`) and is left with the box
  integral of `∏ u_i^{r_i − κ_i (r_j+1)/κ_j}`, whose exponents exceed `−1` exactly by strict
  optimality. `integrable_envelope_of_vertex` and `integrable_envelope_mul_profile_of_vertex`
  (via `x e^{-cx} ≤ (2/c) e^{-cx/2}`) are the two `ProfileIntegrableOf` integrabilities for a unit
  bounded below on the limiting domain, and `ProfileIntegrableOf.of_vertex` packages them for a
  wall chart term `(i, ε, b)` from LP data alone (`hκj`, `hη`, `hδκ`, `hα`, `hstrict`, `hgap`).
  So in the generic (vertex) case the certificate is decided by the LP: isolated vertex optimum
  ⇒ certificate, coordinate recession direction ⇒ no certificate.
- `TiedBlockBound.lean`: an all-scale bound for the tied-block integral. Writing the tied-block
  integral through the core integral `coreJ λ n s = ∫_{z>0} e^{-s e^{-z}} e^{-λz} z^n`
  (`tiedBlockIntegral_eq_coreJ`), `coreJ_le_bound` gives `coreJ λ n s ≤ M s^{-λ} (1 + log⁺ s)^n`
  for every `s > 0` (constant for `s ≤ e`, the growth bound `coreJ_le_growth` beyond), hence
  `tiedBlockIntegral_le_bound`: the power–log envelope `M s^{-λ}(1 + log⁺ s)^k` holds at every
  scale, not only asymptotically — the dominated-convergence majorant for slicing arguments.
- `PartialTiedModel.lean`: the partially tied constant-unit model. Index `Fin (k+1) ⊕ ν`: the
  tied block `T` (`(r_i+1)/κ_i = λ`) and a strictly worse block `N` (`λκ_j < r_j + 1`). Fubini
  along `MeasurableEquiv.sumPiEquivProdPi` integrates the tied block first at the effective
  constant `a₀ ∏_N z^κ`, where the fully tied theorem (`tendsto_modelKernel_const` +
  `tiedConst_eq`) gives the slice limit `(B a₀ ∏_N z^κ)^{-λ} δ^k Γ(λ)/k! ∏_T κ^{-1}`; the all-scale
  bound supplies the majorant `C ∏_N z^{r_j − λκ_j}`, integrable on the box exactly because the
  gaps are strict; dominated convergence gives (`tendsto_modelKernel_partial`)
  `t^{γp+δλ}/(log t)^k K(t) → A w₀ (B a₀)^{-λ} δ^k Γ(λ)/k! ∏_T κ_i^{-1} ∫_{(0,ρ)^N} ∏_N z^{r_j − λκ_j}`.
  The logarithmic degree is the dimension of the tied face; the strictly worse coordinates
  contribute a finite transverse integral — the constant-unit half of Astra's partially tied
  face-measure target (`research_partial_v1.md`). Open: the variable-unit version (slice-wise
  `tendsto_modelKernel_tied` + the same majorant), then the chart-level and assembly connection.
- `PartialTiedVariable.lean`: the variable-unit partially tied model (Astra's target (1), model
  level). Weight `W` and unit `a` depend on the box point and the cutoff variable, with `0 ≤ W ≤
  wU`, `aL ≤ a` on the box, `0 < a` at the face points and joint continuity of `W`, `a` at every
  face point `(0_T, z_N, 0)`. Each slice in `z_N` is a fully tied kernel with weight
  `W(y, z, v)` and unit `a(y, z, v) ∏_N z^κ`, so `tendsto_modelKernel_tied` gives the slice limit
  `tiedConst 1 B δ κ_T r_T λ ρ (a(0,z,0) ∏_N z^κ) W(0,z,0)`; after freezing the cutoff variable
  (`modelIntegrand_Q_zero_freeze`) the slice is dominated by the constant-unit slice at
  `(wU, aL ∏_N z^κ)`, whose all-scale bound `slice_const_bound` (the Stage C bound, general
  weight) is the DCT majorant. `tendsto_modelKernel_partial_var`:
  `t^{γp+δλ}/(log t)^k K(t) → A δ^k Γ(λ)/k! ∏_T κ_i^{-1} ∫_{(0,ρ)^N} W(0_T,z,0) (B a(0_T,z,0))^{-λ} ∏_N z^{r_j−λκ_j} dz`
  — a partially tied face carries the *face density* `W (B a)^{-λ} ∏_N z^{r−λκ}` on the worse
  block, not a point mass. Open: the chart-level identification (reindexing `Fin m ≃ Fin (k+1) ⊕ ν`
  of `modelKernel`, continuity of the chart weight/unit at general face points) and the
  lexicographic assembly of partially tied terms.
- `WallPartialTerm.lean`: the partially tied term at the chart level. `modelKernel_reindex e`
  (the model kernel is invariant under reindexing the coordinates along `e : ι ≃ ι'`, from
  `volume_measurePreserving_piCongrLeft`); `continuousAt_weightFn` (joint continuity of the chart
  weight at any point whose bridge point lies in the open ball, generalising
  `tendsto_weightFn_face`), `continuousAt_unitFn`, `ma_le_unitFn_of_mem_ball`,
  `bridgePt_mem_ball_of_abs_lt`; `partialFace e z` (tied coordinates `0`, worse coordinates `z`).
  `tendsto_modelKernelOf_partial`: for a chart with `Q = 0` whose transverse coordinates split
  along `e : Fin (k+1) ⊕ ν ≃ Fin m` into a tied block and a strictly worse block,
  `t^{γp+δλ}/(log t)^k K_{i,ε,b}(t) → A δ^k Γ(λ)/k! ∏_T κ^{-1} ∫_{(0,ρ)^N} φ(ρ_i(pt_z)) wt|b|(pt_z) (B|a(pt_z)|)^{-λ} ∏_N z^{r−λκ} dz`
  with `pt_z = bridgePt (partialFace e z) 0` (solved coordinate `0`, tied coordinates `0`, worse
  coordinates `±z`). `tendsto_termKernel_partial` is the `termKernel` form: the certificate of an
  admissible partially tied branch at the pair `(γp + δλ, k)` for `tendsto_fibre_expectation_lex`.
  Astra's target (1) is closed at every level (model, chart, assembly input). Open: (2) the
  two-scaled tied-truth certificate, (3) distinguishability.
- `TwoScaledInner.lean` (Astra's target (2), the analytic core): the substitution `y = e^v` on the
  whole line (`integral_comp_exp_univ`) and coordinatewise on the positive orthant
  (`integral_posOrthant_comp_exp`, diagonal Jacobian `∏ e^{v_i}`), the two-constraint matrix
  `twoMat κ Q = [κ; Q]` with the linear change `(w, s) = (κ·v, Q·v)` (`integral_comp_mulVec`),
  and the product structure on `Fin 2`. Under the dual decomposition `a = ηκ − θQ` (`η, θ > 0`,
  `Δ = κ₀Q₁ − κ₁Q₀ ≠ 0`) the quadrant integral with the cutoff in logarithmic form is exact:
  `∫_{y>0, h<Q·log y} ∏ y^{a−1} e^{−c∏y^κ} dy = Γ(η) c^{−η} e^{−θh}/(θ|Δ|)`
  (`integral_twoScaledInner`, `integrable_twoScaledInner`).
- `TiedTruthCertificate.lean`: `tiedDom` (the dominating profile `1_{limitDomain} ∏u^r e^{−c₀∏u^κ}`,
  general index) with the generic envelope integrabilities `integrable_envelope_of_tiedDom`,
  `integrable_envelope_mul_profile_of_tiedDom` (the vertex argument, from `Integrable tiedDom`
  under a tied phase constraint alone); the box monomial integral `integral_box_prod_rpow`; on
  `Fin 2 ⊕ ν` with `α = (αS, 0)`, `αS > 0` and tied truth `Q·α = γ`, the limiting domain is
  `{y > 0} × (0,ρ)^ν ∩ {D ∏u^{−Q/q} < ρ}` (`elim_mem_limitDomain`), the cutoff on a slice reads
  `q log(D ∏_ν z^{−Q/q}/ρ) < Q_S·log y` (`cut_iff_log`), each slice is `∏_ν z^r · twoScaledInner` at
  the effective constants (`tiedDom_elim`) with value `twoScaledConst · ∏_ν z^{resExp}`
  (`integral_tiedDom_elim`, `resExp_j = r_j − ηκ_j + θQ_j`). Fubini gives the **two-scaled
  tied-truth certificate** `integrable_tiedDom_twoScaled` (hypotheses `η, θ > 0`, `Δ ≠ 0`,
  `−1 < resExp_j`) and the exact value `integral_tiedDom_twoScaled`:
  `Γ(η) c₀^{−η} (D/ρ)^{−θq}/(θ|Δ|) · ∏_ν ρ^{β_j}/β_j` with `β_j = resExp_j + 1`.
- `WallTiedTruth.lean`: `limitDomain_reindex`, `tiedDom_reindex`, `integrable_tiedDom_of_reindex`
  (transport along `e : ι ≃ ι'`), and the chart-level certificate
  `ProfileIntegrableOf.of_twoScaled`: a wall chart term at a scale `α` supported on two transverse
  coordinates `e (inl 0), e (inl 1)` (positive there), tied phase `κ·α = δ`, tied truth `Q·α = γ`,
  dual decomposition `r_S + 1 = ηκ_S − θQ_S`, `Δ ≠ 0`, `β_j > 0` on the boxed coordinates. With
  `of_vertex` (strict truth, one scaled coordinate) the two isolated-optimum shapes of the LP are
  certified: one active constraint isolates one scaled coordinate, two isolate two; the
  obstruction moves to three scaled coordinates (Astra, `research_partial_v1.md` §(b)). Open: the
  three-scaled obstruction under tied truth; Astra's (3) distinguishability.
- `TiedTruthObstruction.lean`: the recession obstruction with a surviving cutoff.
  `exists_box_subset_of_isOpen` (a positive closed box inside an open set around any of its
  points); `not_integrable_envelope_of_recession_direction_tied`: for a nonempty limiting domain,
  any `d ≠ 0` supported on the scaled coordinates with `d·κ ≤ 0`, `d·Q = 0` when the truth
  constraint is tied, and `d·(r+1) ≥ 0` forbids the certificate (the unit bound is needed on the
  limiting domain only). `exists_direction_of_three_scaled`: with `3 ≤ #{l | α_l ≠ 0}` the two
  linear constraints `d·κ = d·Q = 0` have a nonzero solution on the scaled block (rank–nullity for
  `v ↦ (κ·v, Q·v)`), and one orientation has `d·(r+1) ≥ 0`. Hence
  `not_integrable_envelope_of_three_scaled` and, at the chart level,
  `not_profileIntegrableOf_of_three_scaled` (unit bounded by `Ma` on the limiting domain via
  `limitBranchPt_mem_ball`). Per Astra's round-3 audit (`research_round3_v1.md`): the certificate
  obstruction excludes three or more scaled coordinates, and the nondegenerate one- and
  two-coordinate cases have explicit certificates (`of_vertex`, `of_twoScaled`); a full
  classification still needs the converses and the degenerate two-constraint cases (round-3
  target 3). Failure of the envelope certificate does not exclude a logarithmically renormalised
  asymptotic — that is exactly the positive-dimensional-face regime.
- `NormalisedMeasure.lean` (Mathlib only): `normaliseMeasure μ = μ(1)⁻¹ • μ`;
  `ratio_eq_of_normalise_eq` (equal normalisations give equal ratios `∫ψ/∫χ`);
  `normalise_eq_iff_forall_ratio` (two nonzero finite Borel measures on a space with outer
  approximation of closed sets have the same normalised integrals of all bounded continuous
  functions iff their normalisations agree, `ext_of_forall_integral_eq_of_IsFiniteMeasure`);
  `restrict_ext_of_forall_integral_eq` (bounded continuous functions supported in an open `U`
  determine the restrictions to `U`: the cutoffs `min 1 (n·dist(x,Uᶜ))` increase to `1_U`,
  dominated convergence); `normalise_restrict_eq_of_forall_ratio(_nonneg)` (ratios against a fixed
  positive reference observable, for all (nonnegative) bounded continuous test functions supported
  in `U`, determine the normalised restriction to `U`; the nonnegative version by the
  `ψ = ψ⁺ − ψ⁻` split).
- `WallDistinguishability.lean` (Astra's target (3)): `fibreRatio D F ψ χ σ γ t` (the ratio of
  total kernels at `σt^{-γ}`); `tendsto_fibreRatio_sub_of_normalise_eq` — two phases whose
  limiting measures have the same normalisation have the same leading expectation for every
  certified pair `(ψ, χ)`; `normalise_restrict_limitMeasure_eq_of_forall_tendsto` — for open `L'`,
  if the two fibre expectations against a fixed positive reference `χ` have the same limit for
  every nonnegative bounded continuous `ψ` supported in `L'`, the normalised restrictions to `L'`
  of the two limiting measures agree. **The leading expectations know exactly the normalised
  limiting measure on `L'`**: not the mass, not the dominant power or log scale, not what the face
  maps erase. (`IsOpen L'` does genuine work: with test functions whose nonzero set lies in `L'`
  only the interior of `L'` is observable; Astra advises keeping it a theorem-level hypothesis, not
  a record field.) Astra's three ranked targets of `research_partial_v1.md` are all closed.
- `PartialFaceMeasure.lean` (round-3 target 1): `partialPt` (chart face point), `partialFacePt`
  (its image `ρ_i(pt_z)` in the ambient space), `partialConst = A δ^k Γ(λ)/k! ∏_T κ^{-1}`,
  `partialDensity` (the constant times `wt|b| (B|a|)^{-λ} ∏_N z^{r−λκ}` on `(0,ρ)^N`),
  `partialMeasure` (the push-forward of the density under the ambient face point; finite by the
  strict gaps and the bounds `wt ≤ 1`, `|b| ≤ Mb`, `|a| ≥ ma`), `integral_partialMeasure`,
  `tendsto_modelKernelOf_partial_measure` / `tendsto_termKernel_partial_measure`
  (`t^{γp+δλ}/(log t)^k K_{i,ε,b}(t) → ∫ φ dμ_{i,ε,b}`), and
  `tendsto_fibre_expectation_lex_measure`: with a finite measure `μ_p` per term certified at
  `(λ_p, k_p)`, the fibre expectation converges to `∫ψ dμ_*/∫χ dμ_*` for the lexicographic
  coefficient measure `μ_* = ∑_{(λ_p,k_p)=(λ_*,k_*)} μ_p`. The distinguishability theorems of
  `NormalisedMeasure` apply verbatim to `μ_*`. Caveat (Astra): `μ_{i,ε,b}` is a parameter-space
  density before push-forward, not a density on the represented face, and a chart contribution
  before atlas weights and dominance selection. Round-3 ranking still open: (2) the canonical
  mixed-truth log endpoint `xy = s` (`J_f(t,σ)/log t → f(0,0)`), (3) the nondegenerate
  certificate–LP equivalence in the constant-unit model, (4) local uniformity in `σ`.
- `MixedTruthLog.lean` (round-3 target 2, the core lemma; Mathlib only): the mixed truth monomial
  `xy = s` at the logarithmic endpoint, where the bridge map does not extend continuously to the
  face point. `mixedScale ρ σ t = log(ρ²t/σ)`; the substitution `x = ρe^{−Lu}` maps `(0,1)` onto
  the fibre range `(σ/(ρt), ρ)` (`image_mixed`) and turns `∫ g(x) dx/x` into `L ∫_0^1 g(ρe^{−Lu}) du`
  (`integral_fibre_eq_scale`); the second coordinate is `σ/(tx) = ρe^{−L(1−u)}`
  (`fibre_second_coord`). `tendsto_mixedLog`: for `f` continuous on the closed box,
  `(1/log t) ∫_{σ/(ρt)}^{ρ} f(x, σ/(tx)) dx/x → f(0,0)` (dominated convergence on `(0,1)`, both
  coordinates → 0 for `0 < u < 1`, `L/log t → 1`). `tendsto_mixedLog_ratio`: for `F = xy·a(x,y)`
  with continuous unit, weight and observables, the fibre expectation on `{xy = σ/t}` (measure
  `dx/x`) converges to `ψ(0,0)/χ(0,0)` when `w(0,0)χ(0,0) ≠ 0` — concentration at the corner after
  logarithmic averaging. Open: the bookkeeping into the `totalKernel`/`fibreKernel` conventions
  (Jacobians, branches, atlas weights).
- `CertificateNecessity.lean` (round-3 target 3, analytic half): `not_integrable_tiedDom_of_recession`
  (recession directions of the constant-unit profile may decrease the boxed coordinates and
  increase the cutoff monomial: `d_j ≤ 0` on boxed `j`, `d·κ ≤ 0`, `d·Q ≥ 0` when the truth is
  tied, `d·(r+1) ≥ 0`); `vertex_conditions_of_integrable` / `integrable_vertexDom_iff` (strict
  truth, one scaled coordinate `s`: the profile is integrable **iff** `η = (r_s+1)/κ_s > 0` and
  `κ_j η < r_j + 1` for all `j ≠ s`; the directions `−e_s` and `κ_j e_s − κ_s e_j`);
  `twoScaled_conditions_of_integrable` / `integrable_tiedDom_twoScaled_iff` (nondegenerate tied
  truth on a nonempty limiting domain: integrable **iff** `η > 0`, `θ > 0` and every residual
  exponent `r_j − ηκ_j + θQ_j > −1`; the scaled-plane directions with `(κ·d, Q·d) = (−1,0)`,
  `(0,1)` and `−e_j + v` with `(κ·v, Q·v) = (κ_j, Q_j)`). So the certificate hypotheses are
  exact in the constant-unit model. Open: the LP half (unique minimiser ⇔ the same conditions).
- `CertificateLP.lean` (round-3 target 3, LP half): `UniqueLPMin Q κ γ δ a α` (feasible and
  strictly better than every other feasible point). `vertex_identity`
  `a·β − a·α = η(κ·β − δ) + ∑ (a_i − ηκ_i)β_i` and `uniqueLPMin_vertex_iff` (strict truth,
  `α = (δ/κ_s) e_s`: unique minimiser **iff** `η = a_s/κ_s > 0` and `κ_j η < a_j`, `j ≠ s`; the
  perturbations `α + ε e_s`, `α + ε(e_j − (κ_j/κ_s) e_s)` with explicit `ε`); `tied_identity`
  `a·β − a·α = η(κ·β − δ) + θ(γ − Q·β) + ∑_N (a_j − ηκ_j + θQ_j)β_j`, `eq_of_two_eqs` (Cramer) and
  `uniqueLPMin_twoScaled_iff` (tied truth, `α` supported on two scaled coordinates, `Δ ≠ 0`,
  `a_S = ηκ_S − θQ_S`: unique minimiser **iff** `η > 0`, `θ > 0` and positive residual reduced costs;
  the scaled-plane directions `(κ·d, Q·d) = (1,0)`, `(0,−1)` and `e_j − v`). Together with
  `CertificateNecessity`: in the constant-unit model, **profile certificate ⇔ unique LP
  minimiser** in both nondegenerate shapes (`integrable_vertexDom_iff` + `uniqueLPMin_vertex_iff`
  with `a = r + 1`; `integrable_tiedDom_twoScaled_iff` + `uniqueLPMin_twoScaled_iff`). Degenerate
  cases (a tied one-coordinate vertex, `Δ = 0`, zero reduced costs) remain outside, as Astra
  advised. Round-3 target 4 (local uniformity in `σ`) and the `totalKernel` bookkeeping of the
  mixed-truth endpoint are the remaining items of the ranking.
- `WallDistinguishabilityLex.lean`: `lexMeasure lam kk μ lam₀ k₀ = ∑_{(λ_p,k_p)=(λ₀,k₀)} μ_p`;
  `tendsto_fibreRatio_sub_of_normalise_eq_lex` and `normalise_restrict_lexMeasure_eq_of_forall_tendsto`
  lift the two distinguishability statements to the lexicographic coefficient measure: the leading
  expectations know exactly the normalised coefficient measure on the open `L'`, whether the
  dominant terms are isolated vertices, fully tied point masses or partially tied face densities.
- Round-4 consult (`gpt_responses/research_round4_v1.md`): audit clean; `Q ≥ 0` dropped from
  `uniqueLPMin_vertex_iff`; wrappers `integrable_vertexDom_iff_uniqueLPMin`,
  `integrable_tiedDom_twoScaled_iff_uniqueLPMin` (certificate ⇔ unique LP minimiser, both
  nondegenerate shapes, `a = r + 1`). Ranking: (1) record-level mixed-truth coefficient measure
  (a 2D instance with truth monomial `xy`; `branchKernel` with `q = (1,1)`, `k = 0` gives
  `Φ(s/w, w)/w` on the positive branch, coarea convention, `γ = 1`); (2) product-chart LP face
  classification (`Opt = conv{(δ/κ_i) e_i : i ∈ T}`, `dim = |T| − 1 = k`, three coefficient-measure
  shapes; a unique LP vertex is not a point mass in general); (3) local σ-uniformity and
  `σ(t) → σ₀`; (4) a scoped degeneracy theorem (optimal set = feasible points with vanishing gap
  terms); plus atlas-independence of the normalised coefficient measure on the hironaka side.
  Numerical check `docs/numerics/partial_face_ratio.py` (Astra's example
  `∫ xyz³ e^{−txyz} φ` on `(0,1)³`, `λ = 2`, `T = {x,y}`, `k = 1`): `I(z)/I(1) → 2/3`,
  `I(z²)/I(1) → 1/2`, `t²/log t · I(1) → 1/2`, observed 0.675 / 0.510 / 0.467 at `t = 10⁶` with
  monotone logarithmic approach.
- `MixedTruthRecord.lean` (round-4 target 1, resolved with a correction; mirrored as
  `Monomialize/Relative/Wall/Euclid/MixedTruthRecord.lean`). **Coordinate truths carry no
  logarithm**: for `D : WallChartsData m ℓ L'` with `L' ⊆ closedBall 0 R` and `θ ≤ M`,
  `totalKernel θ s ≤ M (2R)^m` for a.e. `s` (`WallChartsData.totalKernel_ae_le`: the push-forward
  identity bounds `∫⁻_E K_θ` by `M · vol(L' ∩ {z ℓ ∈ E}) ≤ M (2R)^m |E|`, via the splitting
  `piFinSuccAbove` and `Real.volume_pi_closedBall`; the bound is a.e. in `s` and excludes a growing
  `log t` mass for bounded observables, not the decaying `t^{-λ}(log t)^k` terms of the loss). So
  the record-level target as first posed — a wall chart with `q = (1,1)` whose fibre kernel grows
  like `log t` — cannot exist: a genuinely
  mixed truth monomial in a chart of a Euclidean wall atlas comes with a Jacobian vanishing at the
  corner (`z₀ = u₀u₁` has zero differential there), and that Jacobian cancels the coarea `1/w`
  (`BlowupSectorRecord`: `dens = |u₁|`, fibre kernel `∫_{|s|≤|x|≤1} θ(s, x) dx`, no log). The log
  endpoint of `MixedTruthLog` is the **general-truth** situation, truth function `T = z₀z₁` on the
  Lebesgue square, which is now a record too: `TruthChartsData m T L'` (the `WallChartsData` fields
  with `T (rep i u) = truthMono (S i) (q i) u`; `WallChartsData.toTruth` is the case `T = (· ℓ)`)
  has the same push-forward identity `∫⁻_{L'} θ η(T z) = ∫⁻ η K_θ` (`lintegral_mul_comp_truth`,
  proof verbatim). `mixData : TruthChartsData 1 (z₀z₁) (0,1/2]²` is the identity chart (density
  `toyDens`, `= 1` on the square; `q = (1,1)`, `k = 0`, `S = 1`); its branch kernel at `s > 0` is
  supported on the branch `x > 0` with fibre point `(s/x, x)` and Jacobian `1/x`
  (`mixData_branchKernel`: `solvedCoeff = x`, `solvedCoord x 1 s = s/|x|`,
  `insertNth 0 v (fun _ ↦ x) = ![v, x]` by `fin_cases; rfl`), so
  `K_θ(s) = ∫_{2s}^{1/2} θ(s/x, x) dx/x` (`mixData_totalKernel`; the `Fin 1 → ℝ` integral is
  transferred by `volume_preserving_funUnique` through `Eq.trans`, since `rw` fails on the
  `Fin (0+1)` instance). For `F = z₀z₁·a(z)`, `s = σ/t`: `K(σ/t)/log t → e^{-σ a(0)} ψ(0)`
  (`mix_tendsto_totalKernel`, from `tendsto_mixedLog` with `f(x,y) = e^{-σ a(y,x)} ψ(y,x)`, `ρ = 1/2`)
  and the fibre expectation `→ ψ(0)/χ(0)` (`mix_tendsto_fibre_expectation`): the coefficient measure
  at the logarithmic scale is `e^{-σ a(0)} δ_0`, with the positive-branch multiplicity one on the
  square (the other sign branch leaves the region).
- `ProductChartLP.lean` (round-4 target 2; mirrored as `Euclid/ProductChartLP.lean`): the LP of a
  product chart in closed form. `LPOptimal Q κ γ δ a α` (feasible and minimal);
  `uniqueLPMin_iff_lpOptimal_unique`. With `Q = 0`, `0 ≤ γ`, `κ > 0`, `δ > 0`, `λ > 0`,
  `a_i = λκ_i` on the tied set `T ≠ ∅` and `λκ_i < a_i` off it: `lpOptimal_product_iff`
  (optimal **iff** `α ≥ 0`, `α_N = 0`, `κ·α = δ`; proof: `λ κ·β ≤ a·β` termwise, the tied vertex
  `(δ/κ_s) e_s` has value `λδ`, and the excess `∑ (a_i − λκ_i) α_i` vanishes termwise),
  `lpOptimal_value` (`a·α = λδ`), `lpOptimal_single`, `lpOptimal_iff_exists_weights`
  (`Opt = conv{(δ/κ_i) e_i : i ∈ T}`, weights `w_i = κ_i α_i/δ`), `uniqueLPMin_iff_card_eq_one`
  (unique minimiser **iff** `|T| = 1`, and then `α` is the tied vertex; two tied coordinates give
  two distinct optimal vertices). In the index shape of `tendsto_modelKernel_partial`
  (`Fin (k+1) ⊕ ν`, `htied`, `hgap`, `a = r + 1`): `lpOptimal_partial_iff` (optimal iff `α ≥ 0`,
  `α ∘ inr = 0`, `κ·α = δ`) and `card_image_inl` (`|T| = k + 1`), so the LP face dimension
  `|T| − 1 = k` is the logarithmic exponent of the coefficient. The three shapes: `T = univ` gives
  the fully tied point mass (`tendsto_modelKernel_tied`), `|T| = 1` a unique LP vertex whose
  coefficient is still a face density in the `ν` variables, intermediate `T` the partial face
  density — "the LP tells which faces carry the measure", with a unique vertex not a point mass.
- `KernelAtlasIndependence.lean`: `TruthChartsData.totalKernel_ae_eq` / `WallChartsData.totalKernel_ae_eq`
  — two chart systems over the same truth and region have a.e. equal total fibre kernels (both are
  densities of the same push-forward; `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`). Astra
  round 5 (`research_round5_v1.md`): the correction of target 1 is right (a.e. bound, growing mass
  only), `TruthChartsData` should become the observable-facing interface with `WallChartsData` the
  coordinate specialisation, and the hironaka export must supply simultaneous monomialisation of
  `(T, F)` (not "Hironaka on `(T)`"); the weighted family `y^h dx dy` is NOT a Lebesgue
  `TruthChartsData` with the identity chart (the transport identity would represent the weighted
  measure) — its trichotomy is `h > 0`: finite axis measure `∫ x^{h-1} e^{-σa(0,x)} ψ(0,x) dx`,
  `h = 0`: log corner mass, `h < 0`: `t^h K → σ^h ∫ u^{-h-1} e^{-σ a(u,0)} ψ(u,0) du`. Ranking:
  (1) local σ-uniformity (constant-unit tied model first, then partial faces; corollary
  `σ(t) → σ₀`), (2) the certificate-based assembly theorem (convergence against a class of
  observables), (3) general-truth Hironaka export, (4) one explicit `Q ≠ 0` degenerate face with
  its log exponent, (5) the `h > 0` weighted theorem, (6) atlas independence (done, a.e. form).
- `ParameterStability.lean` + `WallLogTermParam.lean` (round-5 target 1; mirrored): the fully tied
  power–log law along a moving parameter. `tendsto_tiedConst_param` (constant-unit kernel with
  `A t → A₀`, `B t → B₀ > 0`, cutoff `D t · t^{-γ/q} → 0`; proof: the scale `c t = B t a₀ ρ^{∑κ}
  → c₀`, `tendsto_tiedBlock ∘ (c t · t^δ)`, `log(c t · t^δ)/log t → δ`, `(c t)^{-λ} → c₀^{-λ}`);
  `tendsto_modelKernel_tied_param` (the `LogExactConstant` sandwich verbatim with `A t, B t, D t`
  per `t` — generated by substitution from the fixed proof, no new analysis: the constants enter
  the sandwich only pointwise in `t`, and the four constant-kernel limits are the `_param`
  theorem). Chart level: `tendsto_constA/B/D` (continuity of `|σ|^e` at `σ₀ ≠ 0`),
  `tendsto_constD_cut`, `admissible_eventually_iff` (a sign branch is eventually admissible iff it
  is at `σ₀`, since `admissible = 0 < c σ` with `c ≠ 0`), `tendsto_modelKernelOf_tied_param`,
  `tendsto_termKernel_tied_param` / `_of_not_admissible_param`, and the assembly
  `tendsto_fibre_expectation_lex_param` (every `σ` replaced by `σ t`, `hσ.eventually_ne hσ₀` for the
  term identity): along `σ(t) → σ₀ ≠ 0` the leading expectations converge to the ratio of the
  limiting coefficients at `σ₀`. Not done: the locally uniform (`sup_{σ ∈ C}`) form, which follows
  abstractly from the moving-parameter form by a compactness argument, and the partial-face
  (`tendsto_modelKernel_partial`) moving version.
- `PartialTiedParam.lean` (round-5 target 1, partial faces; mirrored): the constant-unit `Q = 0`
  model kernel is linear in `A` (`modelKernel_eq_A_mul`), independent of `D` past the cutoff
  (`modelKernel_const_of_cut`, both cuts `< ρ`, via `modelDomain_eq_of_Q_zero'`) and antitone in
  the scale `B` (`modelIntegrand_const_anti`, `modelKernel_const_anti`, with the integrability
  `integrable_modelIntegrand_const` from `integrable_box_prod_rpow'` and `exp ≤ 1`). The abstract
  squeeze `tendsto_of_antitone_param` (a family antitone in a parameter, fixed-parameter limits
  `L b` continuous at `B₀`, `B t → B₀ > 0` ⇒ convergence to `L B₀`; ε–η with `d = min(η/2, B₀/2)`)
  then lifts `tendsto_modelKernel_partial` to `tendsto_modelKernel_partial_param` (`A t → A₀`,
  `B t → B₀`, `D t · t^{-γ/q} → 0`) with the fixed theorem as a black box (`A := 1`, `D := 1`),
  `L b` continuous by `ContinuousAt.rpow_const`. This route would also have given the fully tied
  `_param` theorem; it does not give the variable-unit versions, whose `W(x, v_t)`, `a(x, v_t)` see
  `D`.
- `TermMeasureCertificate.lean` (round-5 target 2, interface form; mirrored):
  `WallChartsData.Phase.TermMeasureCertificate P σ γ` = `(lam, kk, μ, finite, lam₀, k₀, hmin,
  tendsto)` with `tendsto` quantified over every continuous nonnegative bounded observable;
  `leadingMeasure C = lexMeasure C.lam C.kk C.μ C.lam₀ C.k₀` (finite);
  `TermMeasureCertificate.tendsto_fibre_expectation` (`fibreRatio → ∫ψ dμ_*/∫χ dμ_*` when
  `∫χ dμ_* ≠ 0`, from `tendsto_fibre_expectation_lex_measure`) and
  `TermMeasureCertificate.normalise_eq_of_forall_tendsto` (two certified phases with the same
  leading expectations on an open `L'` have the same normalised leading measure, from
  `normalise_restrict_lexMeasure_eq_of_forall_tendsto`). The certificate is the common interface
  for the established asymptotics (vertex, fully tied, partially tied terms certify their
  `(λ_p, k_p, μ_p)`), not a claim that every chart has one. Remaining on the assembly side: a
  constructor of the certificate from per-chart LP/face data (vertex ⇒ `(λ, 0, termMeasure)`,
  tied ⇒ `(γp+δλ, k, point mass)`, partial ⇒ `(γp+δλ, k, partialMeasure)`) — the per-term
  `tendsto` facts exist (`tendsto_termKernel_vertex/tied/partial_measure`) but their observable
  hypotheses (`hφL : φ ≠ 0 → z ∈ L'`) differ from the certificate's class.
- Certificate class corrected (c19b6c8): `TermMeasureCertificate.tendsto` is quantified over
  continuous nonnegative bounded observables **supported in `L'`** (`hφL`), the class the term
  theorems actually certify (`tendsto_termKernel_vertex/tied/partial_measure` all carry `hφL`,
  since the domain indicator at the wall point is invisible only for such observables);
  `TermMeasureCertificate.ofTerms [Nonempty D.ι] lam kk μ finite tendsto` computes the leading
  order (`Finset.univ.inf'` of the powers, `sup` of the log orders on the minimal power; `hmin`
  from `Finset.inf'_le` and `Finset.le_sup`); the normalised-measure theorem is reproved with the
  supported class (`hχL`, same proof body as `normalise_restrict_lexMeasure_eq_of_forall_tendsto`).
- `MixedTruthWeighted.lean` (round-5 item 5, case `h > 0`; Mathlib only; mirrored):
  `tendsto_weightedMixed` — for `b, σ, h > 0` and `f` continuous on `ℝ²`,
  `∫_{σ/(bt)}^{b} x^{h−1} f(x, σ/(tx)) dx → ∫_0^b x^{h−1} f(x, 0) dx` (dominated convergence on
  `Ioo 0 b` with the indicator of `Ioi (σ/(bt))`, bound `C x^{h−1}` from the compact box, pointwise
  `σ/(tx) → 0`; `Ioi_inter_Ioo_eq` for the range). Every positive weight exponent removes the
  logarithm; `h = 0` is the threshold (`MixedTruthLog`). Not a Lebesgue `TruthChartsData` with the
  identity chart (Astra): a model statement.
- `TermData.lean` (round-5 target 2, the constructor; mirrored): `TermData P σ γ p` (power, log
  order, finite coefficient measure of one term, certified against observables supported in `L'`);
  `TermData.ofNotAdmissible` (zero measure), `TermData.vertex` (`(termLam, 0, termMeasure)`, from
  `tendsto_termKernel_vertex` + `termConst' = termConst` on admissible + `termConst_eq_integral`),
  `TermData.tied` (`(γp + δλ, k, ofReal c • dirac (rep 0))` with
  `c = tiedConst A B δ κ r λ ρ |a 0| (wt 0 |b 0|)`, `tiedConst_nonneg`, the linearity
  `tiedConst … (φ(rep 0) · w) = tiedConst … w · φ(rep 0)` by `unfold tiedConst; ring`),
  `TermData.partial` (`(γp + δλ, k, partialMeasure)`); `TermMeasureCertificate.ofTermData`
  assembles certified data for every term into the certificate. So the principal theorem now reads:
  classify every term of a phase into one of the four shapes ⇒ certificate ⇒ fibre expectation of
  every supported observable converges to `∫ψ dμ_*/∫χ dμ_*` (`ofTermData` +
  `TermMeasureCertificate.tendsto_fibre_expectation`).
- Hironaka contract for a general truth (Astra round 5, item 3; NOT done): the wall atlas resolves
  the product `F · z_ℓ` (`WallChart.lean` docstring: "Resolving `F · z_ℓ` … with a wall chart at
  every point over the wall"), and `WallChartAt F ℓ g P` asks for `F ∘ rep = a ∏ u^k`,
  `rep u ℓ = S ∏ u^q` and the Jacobian monomial simultaneously — unique factorisation in the local
  ring gives both factors from the normal crossings of the product. The general-truth version is the
  same statement with an analytic `T` in place of the coordinate: resolve `F · T`, `T ∘ rep =
  S ∏ u^q`, wall set `C ⊆ {T = 0}`, export `TruthChartsData m T L'` in place of `WallChartsData`.
  It is a threading of `ℓ ↦ T` through `WallChart`, `WallAtlas`, `WallExport`, `WallIntegral`,
  `Theorem*` on the branch (hundreds of lines, mechanical), plus the resolution provider applied to
  `F · T`; the fibre identity `fibre_ae` (product regions) does not transfer and is not needed for
  the push-forward statement.
- Round-6 consult (`gpt_responses/research_round6_v1.md`, 1d7275f): audit of the parameter
  theorems, squeeze, certificate, TermData, weighted theorem — consistent; the observable class
  "vanishes off `L'`" determines the measure **restricted to `L'`** only (a Dirac mass outside
  `L'` is invisible), and the certificate's `normalise_eq_of_forall_tendsto` indeed concludes about
  restrictions; honest headline: classifying constructs a certificate, any supported denominator
  with nonzero leading integral gives the ratio limit. Ranking: (1) package "what expectation
  values know" [DONE, `ExpectationValuesKnow.lean` 6fc9744, hironaka 450d2c81e:
  `normalise_restrict_eq_iff_forall_tendsto` — for two certified phases and a supported reference
  `χ` with positive leading integrals, equal leading expectations of every supported observable
  **iff** equal normalised leading measures on `L'`; converse direction via
  `integral_eq_integral_restrict_of_vanish` + `ratio_eq_of_normalise_eq` on the restrictions],
  (2) the three-coordinate degenerate example [IN PROGRESS, `DegenerateFace.lean`:
  `I(t) = ∫_{(0,1)³} 1_{xyz > t^{-2}} z² e^{-t³xyz²}`, LP `min α+β+3ζ` s.t. `α+β+ζ ≤ 2`,
  `α+β+2ζ ≥ 3`, optimal face the segment `ζ = 1, α+β = 1` (both constraints active, `k = 1`),
  claim `t⁴ I(t)/log t → 1` (numerics `docs/numerics/degenerate_face.py`: 0.70, 0.78, 0.83, 0.86
  at `t = 10²..10⁵`, i.e. `1 − c/log t` with `c ≈ 1.56`); landed step 1: `lintegral_unitSquare_mul`
  (`∫_0^1∫_0^1 G(xy) = ∫_0^1 (−log s) G(s) ds`, Tonelli on the triangle `0 < s < y < 1`,
  `lintegral_Ioo_comp_mul_left`, `lintegral_inv_Ioo`); remaining: scale `u = ts, v = tz`,
  substitute `w = uv²`, dominated convergence with the bound `1_{v<w}(1 + |log w| + 2|log v|)e^{-w}`
  (log moments via `|log v| ≤ v + 2/√v`), limit `∫_0^∞ e^{-v} dv = 1`], (3) general-truth hironaka
  export, (4) variable-unit partial moving version (try a frozen-unit perturbation squeeze before
  the 436-line substitution), (5) compact-uniform packaging (state as `∀ ε, ∀ᶠ t, ∀ σ ∈ C, …`).
- `DegenerateFace.lean` COMPLETE (b0416e5; hironaka da4b12a85): `tendsto_degI` —
  `t⁴/log t · I(t) → 1` for `I(t) = ∫_{(0,1)³} 1_{xyz > t^{-2}} z² e^{-t³xyz²}` (iterated
  `lintegral`, `degIntegrand`/`degI`). Chain: `degI_eq_collapse` (the `xy` collapse with density
  `−log s`), `degG_scale` + `lintegral_Ioo_one_eq_scale` ⇒ `degI_eq_scale : I = t^{-4} J` with
  `J = ∫_{(0,t)²} (log t − log u) 1_{uv>1} v² e^{-uv²}`; `degK_eq` + `lintegral_Ioo_comp_mul_left'`
  ⇒ `degJ_eq_subst` (inner integrand `degM v w = 1_{w>v} e^{-w}` on `w ∈ (0, v²t)`);
  `degJ_div_log` (normalise, `ENNReal.ofReal_div_of_pos`); the planar form `degN_eq_lintegral_prod`
  (`lintegral_prod` + indicator/restrict bookkeeping with `degDom t = {0<v<t, 0<w<v²t}`);
  domination `degΦ_le_degΨ` for `t ≥ e` by `1_{0<v<w}(1 + 3w + 2w^{-1/2} + 4v^{-1/2})e^{-w}` (from
  `|log v| ≤ v + 2/√v`, `abs_log_le_add_two_div_sqrt`, and `v < w`), finiteness
  `lintegral_degΨ_ne_top` (inner integral computed exactly, `lintegral_degΨ_inner =
  ofReal((w + 3w² + 10√w)e^{-w})`, then `Real.GammaIntegral_convergent` at `s = 2, 3, 3/2`),
  limit `lintegral_degΦlim = 1` (`integral_exp_neg_Ioi`), `tendsto_degN` by
  `tendsto_lintegral_filter_of_dominated_convergence` (pointwise `(log t − log w + 2 log v)/log t →
  1`, the domain indicator eventually on), and `tendsto_degI` (`ENNReal.tendsto_toReal`,
  `ENNReal.eq_div_iff`). Gotchas: identifiers cannot contain `∞`; `lt_mem_nhds`/`gt_mem_nhds`
  orientation; `lintegral_lintegral_swap` needs `(μ := volume) (ν := volume)` and the
  `aemeasurable (μ := volume.prod volume)`; `rw [← hsq]` on `√w * √w = w` also rewrites the `w`
  under the root — use `eq_mul_inv_iff_mul_eq₀`. The LP: `min α+β+3ζ`, `α+β+ζ ≤ 2`, `α+β+2ζ ≥ 3`,
  optimal segment `ζ = 1, α+β = 1`, `k = 1` — a log from a positive-dimensional face with the
  truth constraint active, which the `Q = 0` theorems do not cover. Not done: the general theorem
  behind it (an active-truth partial-face theorem in the model-kernel conventions).
- Round-7 consult (`gpt_responses/research_round7_v1.md`, 0c845c6): audit of the example (chain and
  constant correct; the next constant is `1 + γ_E ≈ 1.577`, consistent with the numerics) and of the
  iff (record: identifies restricted measures up to scale; "vanishes off `L'`" is the right class,
  not `tsupport ⊆ L'`). **The transverse active-truth face theorem** (the general statement behind
  the example, to formalise): dual certificate `(β, η)`, `β, η > 0`, `c = r + 1`, coordinates
  `J ⊔ I` with `c_j = βκ_j − ηQ_j` (`j ∈ J`) and `d_i = c_i − βκ_i + ηQ_i > 0` (`i ∈ I`); `κ_J, Q_J`
  independent and `F_J = {α_J ≥ 0 | κ_J·α_J = δ, Q_J·α_J = γ}` with a strictly positive point;
  `k = |J| − 2`, `m = βδ − ηγ`, `λ = γp + m`; then `Opt = {α_I = 0, α_J ∈ F_J}`, `dim = k`, and
  `t^λ/(log t)^k · K(t) → A q D^{-qη} Γ(β)/(𝒥 B^β) · H^k(F_J) · ∫_{(0,1)^I} ∏ y^{d_i−1} ∫_0^ρ
  v^{qη−1} W₀(y,v)/a₀(y,v)^β dv dy` with `𝒥 = √(|κ_J|²|Q_J|² − ⟨κ_J,Q_J⟩²)` (coarea factor); the
  limiting unnormalised measure `A q D^{-qη}/𝒥 · dH^k_{F_J}(α) ∏ y^{d_i−1} dy v^{qη−1} dv w^{β−1}
  W₀ e^{-Ba₀w} dw`. Mechanism: log coordinates `z_J = −log x_J`, transverse coordinates
  `s = κ_J·z_J − δ log t`, `h = γ log t − Q_J·z_J`; the remaining `k` directions have scale `log t`;
  the strict truth truncation is the fixed interval `0 < v < ρ` (weight `v^{qη−1}`), no lost log.
  Dominating factor `(1 + |log w| + |log v| + ∑|log y_i|)^k ∏ y^{d_i−1} v^{qη−1} w^{β−1} e^{-Ba_-w}`.
  No universal reduction to the `Q = 0` partial theorem (the monomial substitution moves the box
  into coupled inequalities). Example check: `J = all`, `β = 2, η = 1`, `H¹(F) = √2 = 𝒥`, limit
  `Γ(2)∫_0^1 v^0 dv = 1`. Ranking: (1) this theorem — first with `W, a` independent of `x_J`
  (polytope-fibre asymptotic + log-moment bound), then face traces by localisation; package the dual
  data `(J, I, β, η, d)` as a certificate [LP half DONE: `ActiveTruthLP.lean` b800bea, hironaka
  2d305f085 — `dual_identity`, `lpOptimal_activeTruth_iff` (optimal iff `α ≥ 0`, `κ·α = δ`,
  `Q·α = γ`, `α_i = 0` where `d_i > 0`, given a nonempty face), `lpOptimal_deg_iff` (the example:
  the segment `α₂ = 1, α₀ + α₁ = 1`)]; (2) general-truth hironaka export (with the caveat that not
  every active-truth chart is transverse); (3) variable-unit partial faces with moving parameters
  only under joint continuity in the parameter (pointwise face continuity is NOT enough — shrinking
  spikes); (4) compact-uniform packaging after the hypotheses stabilise. Skip: a universal
  active-truth-to-`Q = 0` reduction, dependent-normal faces, second-order asymptotics.
- `PolytopeFibre.lean` (1428ca9; hironaka eeb2f69be): the core of the transverse active-truth
  face theorem, in the projected coordinates. `dotLin c` (the functional `c ⬝ᵥ ·`),
  `volume_hyperplane (hc : c ≠ 0) a : volume {x | c ⬝ᵥ x = a} = 0` (translate the kernel
  submodule: `measure_preimage_add_right` + `Measure.addHaar_submodule`, `c ∉ ker` from
  `dotProduct_self_eq_zero`), `volume_coordHyperplane`; `poly2 c₁ c₂ a₁ a₂ = {α ≥ 0 | c₁·α ≤ a₁,
  c₂·α ≤ a₂}` (measurable, monotone in `a`); the fibre at scale `L`,
  `fibre2 c₁ c₂ a₁ a₂ b₁ b₂ L = {z ≥ 0 | c₁·z ≤ a₁L + b₁, c₂·z ≤ a₂L + b₂} = L • poly2 c₁ c₂
  (a₁ + b₁/L) (a₂ + b₂/L)` (`fibre2_eq_smul`, `Set.mem_smul_set_iff_inv_smul_mem₀`), so
  `volume (fibre2 …) = ofReal (L^k) · volume (poly2 … (a + b/L))` (`volume_fibre2`,
  `Measure.addHaar_smul`, `Module.finrank_fin_fun`); and `tendsto_volume_poly2 (hc₁ hc₂ b₁ b₂)
  (hbdd : IsBounded (poly2 c₁ c₂ (a₁+1) (a₂+1)))`: `volume (poly2 (a + b/L)) → volume (poly2 a)`
  (dominated convergence of indicators, `tendsto_lintegral_filter_of_dominated_convergence` with the
  enlarged polytope as bound, finite by `IsBounded.measure_lt_top`; pointwise convergence off the
  null set `{c₁·x = a₁} ∪ {c₂·x = a₂} ∪ ⋃ {x_i = 0}`, by `compl_mem_ae_iff`). Reading: in the log
  coordinates `z_J = −log x_J` with the two transverse coordinates solved, the fibre of the
  constraints is `fibre2` with `L = log t` and `b_i = b_i(s, h, y)` bounded, so its volume is
  `(log t)^k (vol F' + o(1))`, `F'` the projected face; `vol F'/|det R| = H^k(F_J)/𝒥`. Remaining for
  the theorem (constant units first): the log substitution `x = e^{-z}` of the model kernel on the
  box with the truth cut (`integral_posOrthant_comp_exp` style, orthant `z ≥ 0`), the linear change
  to `(s, h, z')` with `|det R|`, Fubini separating `(s, h)` from the fibre, and DCT in `(s, h)`
  with `volume_fibre2`/`tendsto_volume_poly2` and the bound `(1 + |s| + |h|)^k e^{-βs} e^{-ηh}
  e^{-Ba₀e^{-s}}` (needs a polynomial bound on `vol(poly2(a + b/L))` for large `|b|/L`, i.e.
  `poly2 c₁ c₂ (a₁ + u) (a₂ + u') ⊆ ball 0 (C(1 + |u| + |u'|))` when the constraints bound the orthant).
- `LogCoordinates.lean` (1b0db08; hironaka f5bf08ee0): `negExpMap ρ z = ρ e^{-z}` from the open
  orthant onto the open box, `negExpDeriv` (diagonal `−ρe^{-z_i}`), `abs_det_negExpDeriv`,
  `negExpMap_injective`, `image_negExpMap_orthant`, `integral_box_eq_orthant`
  (`∫_{(0,ρ)^ι} F = ∫_{z>0} (∏ ρe^{-z_i}) F(ρe^{-z})`, via
  `integral_image_eq_integral_abs_det_fderiv_smul`), `integrableOn_box_iff_orthant`.
- `ActiveTruthModel.lean` (8584cce; hironaka 4435c426a): step 1 of the active-truth theorem.
  `logCut ρ D γ q t Q = {z | Q·z < q log(ρ/D) + γ log t + (∑Q) log ρ}`; `cutVar_negExp`,
  `cutVar_negExp_lt_iff` (the cut `D t^{-γ/q} ∏x^{-Q/q} < ρ` at `x = ρe^{-z}` is `z ∈ logCut`);
  `modelIntegrand_const_negExp` (with the Jacobian: `w₀ ρ^{∑(r+1)} e^{-(r+1)·z} e^{-B t^δ a₀ ρ^{∑κ}
  e^{-κ·z}}` on the cut); `modelKernel_const_eq_log` (the constant-unit kernel with arbitrary `Q`
  as `A t^{-γp} w₀ ρ^{∑(r+1)} ∫_{z>0} 1_{logCut} e^{-c·z} e^{-B'e^{-κ·z}}`). Gotchas: `Real.rpow_sum_of_pos`
  folds with `←`; `ring` cannot reassociate inside `exp` (rewrite the argument first);
  `MeasurableSet.univ_pi` needs the interval's type ascribed; put `← integral_const_mul` after
  `congr 1` so it only hits the intended side. Plan for step 2 (lintegral form, index
  `Fin k ⊕ Fin 2`, the two solved coordinates last): Fubini via `sumPiEquivProdPi`; for fixed `z'`
  the 2D affine change `y ↦ (s, h) = M y + shift(z')` with `M = [[κ_a, κ_b], [−Q_a, −Q_b]]`,
  `|det M| = |Δ|`, by `Real.map_linearMap_volume_pi_eq_smul_volume_pi` + translation +
  `lintegral_map`; then `c·z = βs + ηh + mL`, `κ·z = s + δL` (the `t`-dependence cancels in the
  Boltzmann factor: `B t^δ ρ^{∑κ} e^{-κ·z} = Bρ^{∑κ} e^{-s}`), the cut `h > h₀'`; Tonelli to put
  `(s, h)` outside with the fibre volume `vol{z' ≥ 0 | y(z', s, h) ≥ 0}` inside; the fibre is
  contained in `‖z'‖ ≤ (s + δL)/κ_min` (from `κ·z = s + δL`, `z ≥ 0`, `κ > 0`), giving the
  polynomial bound `(|s| + δ)^k/κ_min^k` after dividing by `L^k`; DCT with `volume_fibre2` +
  `tendsto_volume_poly2` and the bound `e^{-βs−ηh} e^{-ce^{-s}} (|s|+δ)^k` (finite via
  `(|s|+δ)^k ≤ C(e^{βs/2} + e^{-βs/2})` and `integral_exp_mul_exp_neg_exp`); limit
  `Γ(β) c^{-β} e^{-ηh₀'}/η · vol F'`.
- `LintegralChange.lean` (8f8a3c1; hironaka 4d078c752): `lintegral_sum_split` (Fubini on
  `ι₁ ⊕ ι₂` via `sumPiEquivProdPi`), `lintegral_comp_mulVec_add` (`∫⁻ G(My + b) = |det M|⁻¹ ∫⁻ G`).
- `ActiveTruthAssembly.lean` (5d51f2a; hironaka 8e37e25d0): step 2. On `Fin k ⊕ Fin 2` (solved
  pair last): `transMat κ Q = [[κ_a, κ_b], [−Q_a, −Q_b]]` (`transMat_det = −Δ`), `transShift =
  (κ'·z' − δL, γL − Q'·z')`, `transMat_mulVec_add_shift : My + shift = (κ·z − δL, γL − Q·z)`;
  `injective_mulVec_add`, `image_mulVec_add_orthant` (the image of the orthant under `y ↦ My + b`
  is the preimage of the orthant under `v ↦ M⁻¹(v − b)`, hence measurable); `innerKv` (the
  integrand in `v = (s, h)`: `1_{z'>0} · 1_{v ∈ image(z')} · 1_{h > h₀} · ofReal(e^{-βs−ηh−mL}
  e^{-c₀e^{-s}})`), `logIntegrand`, and `lintegral_inner_subst`: `∫⁻ y, logIntegrand(z', y) =
  ofReal |det M|⁻¹ · ∫⁻ v, innerKv z' v` with `c = βκ − ηQ`, `B' = c₀ e^{δ log t}`, `mL =
  (βδ − ηγ) log t`, `h₀ = −(q log(ρ/D) + (∑Q) log ρ)`. The orthant condition on the solved pair
  is carried as an image set (no explicit inverse in the substitution); the `t`-dependence is now
  only in `e^{-mL}` and in the fibre set. Gotchas: `Sum.forall` splits `∀ i, P (Sum.elim z' y i)`
  by defeq; `Function.Injective.mem_set_image`; `Matrix.det_fin_two` (not `det_fin_two_of`) for
  `Matrix.of ![f, g]`; `ring` in `ℝ≥0∞` closes reassociations of indicator products.
- `ActiveTruthAssembly.lean` step 3 (a970b6b; hironaka ac6d2400b): Tonelli. `fibreSet κ Q δ γ L v`
  (free coordinates `z' > 0` whose solved pair lands in the orthant, as an image-set condition),
  `vWeight β η mL c₀ h₀ v = 1_{h > h₀} · ofReal(e^{-βs − ηh − mL} e^{-c₀ e^{-s}})`, `innerKv_eq`
  (`innerKv = 1_{fibreSet v}(z') · vWeight v`), `measurableSet_fibreSet_prod` (joint measurability
  through the inverse affine map), `lintegral_innerKv_swap : ∫⁻ z', ∫⁻ v, innerKv = ∫⁻ v, vWeight v ·
  volume (fibreSet v)`. Gotcha: `lintegral_indicator_one` wants the Pi `1`; with `fun _ ↦ 1` use
  `lintegral_indicator` + `setLIntegral_const` + `one_mul`.
- `ActiveTruthFibre.lean` (79b29c8; hironaka c56aa98fe): step 4, the fibre is a polytope. With
  `N = M⁻¹`: `fibreCoef j = N_{j0} κ' − N_{j1} Q'`, `fibreA j = N_{j0} δ − N_{j1} γ`,
  `fibreB v j = (N v)_j`; `inv_mulVec_sub_shift` (the solved pair is affine in `z'`),
  `mem_fibreSet_iff : z' ∈ fibreSet ↔ z' > 0 ∧ ∀ j, c_j·z' < a_j L + b_j`, `mem_fibre2_iff`,
  `fibreSet_subset_fibre2`, `fibre2_subset_box` (`κ'_i z'_i ≤ s + δL`, the `κ_min` bound),
  `volume_fibreSet_eq` (open = closed volume; needs `fibreCoef j ≠ 0` for the null hyperplanes),
  `volume_fibreSet_le ≤ ∏ ofReal((s + δL)/κ'_i)` (`Real.volume_pi_Ioc`), `poly2_eq_fibre2_one`,
  `isBounded_poly2_fibre` (via `Metric.isBounded_Icc` + `Set.pi_univ_Icc`),
  `tendsto_volume_fibreSet_div : volume (fibreSet v)/L^k → volume (poly2 c a)`.
- `ActiveTruthLimit.lean` (7800f59; hironaka 09931ab1f): step 5, DCT in `v`. `sWeight β c₀ s =
  e^{-βs} e^{-c₀ e^{-s}}`, `hWeight η h₀ = 1_{Ioi h₀} e^{-ηh}`, `vWeight_zero_eq`, `vWeight_eq_mul`
  (`vWeight mL = ofReal(e^{-mL}) · vWeight 0`), `integral_sWeight = Γ(β) c₀^{-β}` (via
  `integral_exp_mul_exp_neg_exp` and `integral_neg_eq_self`), `integral_hWeight = e^{-ηh₀}/η`,
  `lintegral_vWeight_zero`, `pow_abs_add_le_exp : (|s|+δ)^k ≤ (k/a + δ)^k e^{a|s|}`,
  `exp_abs_le_add`, `integrable_sWeight_mul_pow` (rates `β/2`, `3β/2`), `volume_fibreSet_div_le`
  (`L ≥ 1`: `volume/L^k ≤ (|s|+δ)^k/∏κ'`), `measurable_volume_fibreSet`
  (`measurable_measure_prodMk_right`), `tendsto_lintegral_vWeight_fibre`. Gotchas: `rw [h3]` with
  `h3 : |s| = …` rewrites the `|s|` inside the exponential too (use a `calc`);
  `← Real.exp_add (-(β*s))` with the first argument pinned so the rewrite hits the intended product;
  after `set C := … with hC`, later `have`s contain the expanded form — `rw [← hC] at h1`.
- `ActiveTruthTheorem.lean` (68b3d17; hironaka ba92c45e5): **the transverse active-truth face
  theorem, constant units.** `measurableSet_logCut`, `measurable_logIntegrand`,
  `modelKernel_const_eq_lintegral` (`integral_eq_lintegral_of_nonneg_ae`: no integrability needed),
  `lintegral_logIntegrand_eq` (steps 2–3: `∫⁻ logIntegrand = ofReal|det M|⁻¹ · ofReal(e^{-mL}) ·
  ∫⁻ v, vWeight 0 · volume(fibreSet)`), `facePolytope κ Q δ γ := poly2 (fibreCoef 0) (fibreCoef 1)
  (fibreA 0) (fibreA 1)`, `volume_facePolytope_ne_top`, `tendsto_modelKernel_activeTruth` (raw
  constant), `activeTruth_const_eq` (`ρ^{∑(r+1)} c₀^{-β} e^{-ηh₀} = (Ba₀)^{-β} (ρ/D)^{qη}` from
  `r + 1 = βκ − ηQ`), `tendsto_modelKernel_activeTruth'`:
  `t^{γp + βδ − ηγ}/(log t)^k · K(t) → A w₀ Γ(β) (Ba₀)^{-β} (ρ/D)^{qη}/η · vol(F')/|det M|`
  under `ρ, D, q, B, a₀, β, η > 0`, `δ ≥ 0`, `κ > 0`, `det M ≠ 0`, `fibreCoef j ≠ 0`,
  `r + 1 = βκ − ηQ`. Gotchas: `Tendsto.congr'` compares the association of the limit
  (`← mul_assoc` at the hypothesis first); `ring` cannot commute inside `exp` (`mul_comm (log t) δ`
  before `ring`); `convert h using 2` + `linear_combination coef * e` for a constant identity
  whose factors are not adjacent.
- Nondegeneracy weakened + `ActiveTruthExample.lean` (c86a8f5, 471b5a6; hironaka 69f7cc141):
  `volume_hyperplane' (h : c ≠ 0 ∨ a ≠ 0)` (the hyperplane is empty when `c = 0`), and
  `tendsto_volume_poly2`, `volume_fibreSet_eq` (`fibreCoef j ≠ 0 ∨ fibreA j * L + fibreB v j ≠ 0`),
  `tendsto_volume_fibreSet_div`, `tendsto_lintegral_vWeight_fibre`,
  `tendsto_modelKernel_activeTruth(')` now assume `fibreCoef j ≠ 0 ∨ fibreA j ≠ 0` per constraint:
  a vacuous constraint `0 < a_j L + b_j` (`a_j > 0`) is allowed. This is forced by the degenerate
  example: on `Fin 1 ⊕ Fin 2` with `κ = (1,1,2)`, `Q = (1,1,1)`, `r = (0,0,2)`, `(β, η) = (2, 1)`,
  `transMat = [[1, 2], [−1, −1]]` (det `1`), `fibreCoef = (1, 0)`, `fibreA = (1, 1)`,
  `facePolytope = [0, 1]`; `tendsto_modelKernel_degExample : t⁴/log t · K(t) → 1` reproduces the
  constant of `DegenerateFace.tendsto_degI` from the general theorem (`Real.Gamma_two`). Gotchas:
  `simp [fibreCoef, degTransMat_inv, degκ]` unfolds `degκ` inside `transMat` before the inverse
  lemma fires — `simp only [fibreCoef, degTransMat_inv]` first; `norm_num at h` turns
  `t ^ (2*0 + (2*3 − 1*2))` into the ℕ-power `t ^ 4`, so state the instance with `t ^ 4`.
- Astra round 8 (`gpt_responses/research_round8_{q,v1}.md`, 4074050): audit of the face theorem
  clean; `fibreCoef j ≠ 0 ∨ fibreA j ≠ 0` is strictly weaker than "the face has a positive point"
  (it says the `j`-th solved coordinate is not identically zero on the equality plane; the face may
  still be a point of zero projected volume); `δ ≥ 0` not analytically necessary; certificate +
  nonempty face ⇒ the face is the LP-optimal set (no separate optimality hypothesis at the analytic
  layer). Ranking: (1) identify the example's kernel with `degI`, (2) spectators, (3) face traces,
  (4) chart-level leading-measure theorem (the truth coordinate `u_t` stays of order one — the
  limit is NOT Dirac at the wall point), (5) `TermData.activeTruth` scalar wrapper, (6) export.
  Also suggested: coordinate independence of `vol(F')/|det M|` by an affine change of the solved
  pair; the `c_j = a_j = 0` case by keeping the transverse half-plane indicator.
- `ActiveTruthUniform.lean` (7e13b4d; hironaka e471f98c3): the face theorem in `lintegral` form.
  `lintegral_box_eq_orthant` (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`),
  `lintegral_modelIntegrand_const` (`∫⁻ ofReal(modelIntegrand(1, a₀)) = ofReal(ρ^{∑(r+1)}) ·
  ∫⁻ logIntegrand`), `normalised_lintegral_eq`, `tendsto_normalised_lintegral` (ENNReal limit),
  `sWeight_add_log`, `integral_sWeight_mul_pow_le` (`∫ e^{-βs} e^{-ce^{-s}} (|s|+δ)^k ≤ c^{-β}
  (1 + δ + |log c|)^k C_k`, by the shift `s ↦ s + log c`), `lintegral_vWeight_mul_pow`,
  `normalised_lintegral_le` (`t ≥ e`). Gotcha: `/ ∏ i, κ (Sum.inl i) * (…)` parses the `* (…)`
  INTO the product body — parenthesise `(∏ i, κ (Sum.inl i))` in statements; when `rw` reports an
  identical-looking pattern not found, look for this.
- `SpectatorEnvelope.lean` (e16bf00; hironaka 93f84768a): `integrable_indicator_Iio_exp`
  (`e^{cv}` on `(−∞, b)` via `comp_neg` of the `Ioi` fact), `integrable_indicator_Iio_exp_mul_pow`,
  `integrableOn_rpow_mul_log_pow` (`x^{d−1}(C + a|log x|)^k` on `(0,ρ)`, `d > 0`, through
  `integrable_comp_exp_univ_iff`), `add_sum_le_prod : C + ∑ aᵢ ≤ C ∏ (1 + aᵢ)` (`C ≥ 1`),
  `integral_Ioo_rpow_sub_one` (`integral_Ioo_rpow` already existed in `TiedTruthCertificate` —
  the root build caught the clash). Gotcha: `Finset.one_le_prod'` needs `MulLeftMono`; over `ℝ`
  use `Finset.prod_le_prod` against the constant-one product.
- `ActiveTruthSpectator.lean` (83b9f6b; hironaka 73c4ef726): **the face theorem with spectators.**
  Index `Fin m ⊕ (Fin k ⊕ Fin 2)`, spectators first. `specB B κ ξ = B ∏ ξ^{κ_I}`,
  `specD D q Q ξ = D ∏ ξ^{−Q_I/q}`, `cutVar_sum_elim`, `modelIntegrand_sum_elim`
  (`= 1_{(0,ρ)^m}(ξ) ∏ ξ^{r_I} · modelIntegrand(B_ξ, D_ξ)`), `lintegral_modelIntegrand_spectator`
  (Fubini via `lintegral_sum_split` with `F` given explicitly), `spec_const_factor`
  (`∏ξ^{r} c₀(ξ)^{-β} e^{-ηh₀(ξ)} = c_J^{-β} e^{-ηh₀J} ∏ ξ^{d−1}`), `abs_log_specC_le`,
  `specInner`/`specF`/`specFlim`, `measurable_specF` (`Measurable.lintegral_prod_right` with the
  uncurried integrand written as `(ofReal ∘ modelIntegrand) ∘ (sumPiEquivProdPi).symm`),
  `specd` (reduced costs), `specK`/`specG` (dominating function
  `K ∏ 1_{(0,ρ)}(ξᵢ) ξᵢ^{dᵢ−1}(1 + |κᵢ||log ξᵢ|)^k`), `specF_le`, `specF_tendsto`,
  `integrable_specG`, `tendsto_lintegral_specF` (DCT), `lintegral_specFlim`,
  `modelKernel_const_eq_toReal`, `tendsto_modelKernel_activeTruth_spectator`:
  `t^{γp+βδ−ηγ}/(log t)^k · K(t) → A w₀ Γ(β)(Ba₀)^{-β}(ρ/D)^{qη}/η · vol(F')/|det M| · ∏ ρ^{dᵢ}/dᵢ`
  under the J-hypotheses of the face theorem and `dᵢ > 0`. Gotchas: `Real.log_prod` takes only
  `hf` explicitly; `Real.finset_prod_rpow` is deprecated for `Real.finsetProd_rpow`;
  `simp_rw [foo_eq]` makes no progress on an unapplied `Measurable (f t)` — `rw [show f t = fun ξ ↦ _
  from funext …]`; `Set.indicator_of_mem hξ` rewrites all copies at once (a second call fails);
  `rw [hval] at h` fails on association — `rw [← mul_assoc, hval] at h`.
- Astra round 9 (`gpt_responses/research_round9_{q,v1}.md`, c0f5e33): the trace formula is
  correct; hypotheses for the exact trace model: `w, a` measurable on `(0,ρ)`, `0 ≤ w ≤ W_*`,
  `a ≥ a_- > 0` (no continuity, no upper bound on `a`); signed `w` by linearity. Chart observables
  `φ(x)`: the limit IS Dirac at `x = 0` for `I = ∅` (the "not Dirac" warning was about observables
  that see `u`); with spectators the density is `∏ y^{d−1} ∫_0^ρ u^{qη−1} W₀(y,0,u) a₀(y,0,u)^{-β}`.
  Trace replacement needs, for a.e. `w ∈ F'`, all reconstructed coordinates `α_j(w) > 0` — NOT
  implied by relative-boundary nullity (a face may lie in `{α_j = 0}`); apply the scaled-fibre DCT
  to the whole amplitude `W e^{-C a e^{-s}}`. Order: (1) exact trace model, (2) weighted fibre
  lemma, (3) general trace replacement, (4) no-spectator chart wrapper, (5) spectators.
- `ActiveTruthTraceModel.lean` + `ActiveTruthTraceAssembly.lean` (28849dc; hironaka 76b37a5e0):
  `logTruth` (`u_t(z)`), `modelIntegrand_trace_negExp`, `logIntegrandT`,
  `lintegral_modelIntegrand_trace`; `truthOf ρ D q Q h = D ρ^{-∑Q/q} e^{-h/q}`,
  `logTruth_sum_elim` (`u_t = u(h)` on the affine change — the `t`-dependence cancels),
  `innerKvT`, `lintegral_inner_substT`, `vWeightT`, `innerKvT_eq`, `lintegral_innerKvT_swap`
  (the fibre set is unchanged). Gotcha: after `set v := … with hvdef`, hypotheses obtained
  BEFORE the `set` are folded automatically — a later `rw [← hvdef] at hu` then fails.
- `ActiveTruthTraceLimit.lean` + `ActiveTruthTraceTheorem.lean` (32db66d; hironaka 4c04d8a92):
  **the face theorem for the trace model.** `truthOf_mem_Ioo` (`h > h₀ ⇒ u(h) ∈ (0,ρ)`),
  `vWeightT_le` (domination by `W_*` × the constant-unit weight at `c₀ a_-`),
  `tendsto_lintegral_vWeightT_fibre`, `lintegral_vWeightT_zero` (Fubini via
  `volume_preserving_finTwoArrow` + `lintegral_prod_symm'`, the `s`-integral first),
  `integral_Ioi_truthOf : ∫_{h>h₀} e^{-ηh} f(u(h)) = q C^{-qη} ∫_0^ρ u^{qη−1} f(u)` (any `f`, by
  `Measure.integral_comp_mul_left`, `integral_sub_right_eq_self`, `integral_comp_exp_univ`),
  `trace_const_eq`, `tendsto_modelKernel_trace`:
  `t^{γp+βδ−ηγ}/(log t)^k · K(t) → A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ∫_0^ρ u^{qη−1} w a^{-β}`.
  Gotchas: `0 ≤ᵐ[μ.restrict s] f` is `EventuallyLE` — `refine (ae_restrict_iff' hs).mpr …` then
  `change (0 : ℝ) ≤ _`; `linarith` sees `-h₀ / q` and `h₀ / q` as different atoms (`neg_div`);
  `measurable_modelIntegrand` wants `Measurable (uncurry W)` — give it as
  `show Measurable (Function.uncurry fun _ u ↦ w u) from hwm.comp measurable_snd`.
- `ActiveTruthFibreWeighted.lean` (9944c59; hironaka 268a70ffb): the weighted fibre limit (Astra
  round 9 item 2). `fibreLift κ Q δ γ L v z' = Sum.elim z' (N(v − shift z'))` (the reconstructed
  log coordinate over `v`; `fibreLift_inr : … = a_j L + b_j(v) − c_j·z'`), `lintegral_comp_smul_fin`
  (scaling `∫⁻ F(L•y) = L^{-k} ∫⁻ F` from `lintegral_comp_mulVec_add` with `M = L•1`),
  `negExpMap_mem_box_iff`, `tendsto_lintegral_fibre_weighted`: for measurable `Φ` with
  `0 ≤ Φ ≤ M` and `Tendsto Φ (𝓝[(0,ρ)^n] 0) (𝓝 Φ₀)`,
  `L^{-k} ∫_{fibreSet_L(v)} Φ(ρe^{-z(z')}) dz' → Φ₀ · vol(F')`. Proof: scale `z' = Lw`; off the
  null hyperplanes `{c_j·w = a_j} ∪ {w_i = 0}`, every reconstructed coordinate `L(a_j − c_j·w) + b_j`
  and `L w_i` tends to `+∞` (so `x → 0` inside the box) or the point leaves the fibre; dominated by
  `M 1_{F'(a+1)}`. The a.e. positivity Astra asked for is exactly the existing nondegeneracy
  `(c_j, a_j) ≠ (0,0)` (through `volume_hyperplane'`). Gotchas: `measurable_const_smul L` needs its
  type ascribed (`: Measurable fun x : Fin k → ℝ ↦ L • x`); `mul_lt_mul_left` over `ℝ` asks for
  `MulRightStrictMono` — go through `lt_div_iff₀`; `Tendsto.atTop_mul_const_of_neg` (not
  `atTop_mul_neg_const`); a `Function.comp` redex left by `Tendsto.comp` needs a final `rfl`.
- `ActiveTruthGeneral.lean` (3aefca6; hironaka 61a948d82): **the face theorem with general units**
  (Astra round 9 item 3, trace replacement). `modelIntegrand_general_negExp`, `logIntegrandG`,
  `lintegral_modelIntegrand_general`, `innerKvG` (the amplitude at the reconstructed chart point
  `ρe^{-z(z')}` and truth coordinate `u(h)`), `fibreLift_mulVec_add` (`fibreLift (My + shift) z' =
  Sum.elim z' y`), `measurable_innerKvG_uncurry`, `lintegral_inner_substG`,
  `lintegral_innerKvG_swap` (Tonelli without factoring), `lintegral_innerKvG_eq` (the transverse
  weight times the fibre integral of the amplitude), `ampG` with `ampG_nonneg_le`/`ampG_le`/
  `measurable_ampG`/`ampG_tendsto`, `innerKvG_eq_mul`, `tendsto_lintegral_innerKvG` (DCT in `v`
  with `tendsto_lintegral_fibre_weighted` inside, bound `W_*` × the constant-unit bound at
  `c₀ a_-`), `tendsto_modelKernel_general`: for jointly measurable `W(x,u)`, `a(x,u)`,
  `0 ≤ W ≤ W_*`, `a ≥ a_- > 0`, traces `W_tr, a_tr` (measurable, same bounds on `(0,ρ)`) as
  `x → 0` inside the box for each `u ∈ (0,ρ)`:
  `t^{γp+βδ−ηγ}/(log t)^k · K(t) → A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ∫_0^ρ u^{qη−1} W_tr a_tr^{-β}`.
  The `x`-dependence of the units is handled at fixed `v` by the weighted fibre limit; the
  `u`-dependence exactly as in the trace model. Gotcha: the DCT function is best written as
  `(∫⁻ z', innerKvG … z' v)/ofReal(L^k)` (measurable via `Measurable.lintegral_prod_right'` of
  the uncurried integrand composed with `measurable_swap`) and unfolded pointwise with
  `lintegral_innerKvG_eq`.
- `ActiveTruthChart.lean` (912b97e; hironaka 50fe902e3): **the chart-level active-truth term**
  (Astra round 9 item 4). `modelKernel_congr_unit` (the kernel only sees the unit on the model
  domain), `continuous_reindex`, `faceConst i γ e = vol(F')/|det M|` for the solved pair chosen by
  `e : Fin k ⊕ Fin 2 ≃ Fin m`, `activeTruthDensityFn`/`activeTruthDensity` (`(0,ρ)`-indicator of
  `A Γ(β) B^{-β} q D^{-qη} faceConst · u^{qη−1} (wt|b|)(bridgePt 0 u) |a(bridgePt 0 u)|^{-β}`),
  `activeTruthMeasure` (push-forward of the density along the truth segment
  `u ↦ rep(bridgePt 0 u)`), `integral_activeTruthMeasure`, `integrable_activeTruthDensity`,
  `isFiniteMeasure_activeTruthMeasure`, `tendsto_modelKernelOf_activeTruth` (the general-unit face
  theorem on the reindexed chart kernel; the unit is replaced by `max(unit, m_a)` off the domain
  — `modelKernel_congr_unit` — so the global lower bound holds; traces by `continuousAt_weightFn`
  / `continuousAt_unitFn` at `(0, u)`, `bridgePt 0 u ∈ ball` by `bridgePt_mem_ball_of_abs_lt`),
  `TermData.activeTruth : (γp + βδ − ηγ, k, activeTruthMeasure)`. **The leading measure of an
  active-truth chart is supported on the truth segment `{rep(0,…,±u,…,0) : u ∈ (0,ρ)}`, not at
  the wall point** — the chart coordinate `u_{k}` IS the truth coordinate, so observables see it
  (Astra round 8 was right; my round-9 framing "φ of the active coordinates only" was wrong).
  Gotchas: in `facePolytope`/`transMat` the exponent vectors are over the FULL `Fin k ⊕ Fin 2`
  (`P.kappa i ∘ e`), not the `inr` part; a lemma in `namespace WallChartsData.Phase` not
  mentioning `P` cannot be called as `P.foo`; `set C := …` before `unfold` does not fold the
  unfolded body — use `obtain ⟨C, hC⟩ : ∃ C, C = … := ⟨_, rfl⟩` and `rw [hC]`; `if_pos hadm` under
  a `fun t ↦ … t` redex needs `simp only`, not `rw`; ascribe the type of a `Tendsto.max` result
  before rewriting its limit (`uncurry f (0,u)` vs `f 0 u`).
- Astra round 10 (`gpt_responses/research_round10_{q,v1}.md`, d23b753): audit of the chart term
  clean — the power is `β + γ(p − νβ − η)`, the constants collapse to `|σ|^{p−νβ−η}` (no leftover
  `q`), the measure is (LM) for `I = ∅`, supported in the closure of the truth segment. A zero
  measure at a wrong `(lam, k)` gives a valid but zero global limit and misidentifies the leading
  order — hence the positive-face lemma and a nonvanishing wrapper (which also needs
  `(wt|b|)(bridgePt 0 u) > 0` on positive `u`-measure). Ranking: (a) spectators with traces +
  `TermData.activeTruthSpectator`, (b) LP-to-chart interface, (d) example identification,
  (f) moving parameter, (e) `c_j = a_j = 0`, (c) solved-pair independence, (g) export. For (a):
  no continuity in `y`; a.e.-`y` traces; the frozen-`y` domination must include the
  `y`-dependence of the scale parameters (reuse the spectator majorant); the certificate density
  must stay `φ`-free.
- `ActiveTruthFacePositive.lean` (2039ae1; hironaka 09823c8ed): `continuous_dotProduct_left`,
  `isOpen_poly2_interior`, `volume_poly2_pos_iff` (under `(c_j, a_j) ≠ (0,0)`:
  `0 < vol(poly2) ↔ ∃ w > 0, c_j·w < a_j` — the boundary lies in the null hyperplanes, the
  interior is a nonempty open set: `IsOpen.measure_pos`).
- `ActiveTruthGeneralUniform.lean` (88c1b79; hironaka 079e141de): `normalised_lintegral_eqG`
  (the normalised general-unit model integral in transverse form, ENNReal),
  `tendsto_normalised_lintegralG` (limit `ofReal(ρ^Σ|det|⁻¹) · ∫⁻ vWeightT(traces) · vol(F')`),
  `lintegral_innerKvG_div_le` (pointwise, `L ≥ 1`), `normalised_lintegral_leG` (`t ≥ e`: `W_*`
  times the constant-unit bound at `c₀ a_-`) — the frozen-spectator ingredients for general units.
- `ActiveTruthSpectatorGeneral.lean` (efe45b9; hironaka 7a0aef068): **the face theorem with
  spectators and general units** — `specW` (units with the spectators frozen),
  `modelIntegrand_sum_elim_general` (`1_{(0,ρ)^m}(ξ) ∏ ξ^{r_I}` times the active integrand at
  `B_ξ, D_ξ, W(ξ,·,·), a(ξ,·,·)`), `lintegral_modelIntegrand_spectator_general` (Fubini),
  `specInnerG`/`specFG`/`specFG_eq`/`measurable_specFG`, `modelIntegrand_le_const_units`
  (pointwise: general integrand `≤ W_*` × constant-unit integrand at `a₀ = a_-`, any index type),
  `specFG_le` (`≤ ofReal W_* · ofReal (specG … a_- …)`: the constant-unit majorant is reused
  verbatim), `specFGlim`, `specFG_tendsto` (via `tendsto_normalised_lintegralG` at `B_ξ, D_ξ`),
  `spec_const_factor'` (`∏ ξ^{r_I} · B_ξ^{-β} D_ξ^{-qη} = B^{-β} D^{-qη} ∏ ξ^{d_i−1}`),
  `lintegral_specFGlim` (limit integral `= ofReal(|det M|⁻¹ Γ(β) B^{-β} q D^{-qη} ·
  ∫_{(0,ρ)^m} ∏ ξ^{d−1} ∫_0^ρ u^{qη−1} W_tr(ξ,u) a_tr(ξ,u)^{-β}) · vol(F')`; the inner integral is
  measurable in `ξ` by `StronglyMeasurable.integral_prod_right` against `volume.restrict (Ioo 0 ρ)`
  and bounded by `W_* a_-^{-β} ρ^{qη}/(qη)`, so `Integrable.bdd_mul` against the product density),
  `tendsto_lintegral_specFG` (outer DCT; the traces are only assumed for a.e. `ξ`),
  **`tendsto_modelKernel_general_spectator`**: `t^{γp+βδ−ηγ}/(log t)^k · K(t) →
  A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| · ∫_{(0,ρ)^m} ∏ ξ_i^{d_i−1} ∫_0^ρ u^{qη−1}
  W_tr(ξ,u) a_tr(ξ,u)^{-β} du dξ` under `d_i > 0`, the active certificate `r_j+1 = βκ_j−ηQ_j`,
  bounded jointly measurable units with a.e.-spectator traces (jointly measurable, same bounds on
  `(0,ρ)`). Astra round-10 item (a), abstract half. (64d8ae9: the trace hypotheses are only asked
  for spectators in the box, `∀ᵐ ξ, ξ ∈ specBox → …`, which is what the chart wrapper can supply.)
- `ActiveTruthChartSpectator.lean` (64d8ae9; hironaka 4f6bde84c): **`TermData.activeTruthSpectator`**
  — the chart-level active-truth term for a chart whose coordinates split through
  `e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ Fin m` into `n` spectators, `k` free and two solved active
  coordinates. `specPt e ξ = fun j ↦ Sum.elim ξ 0 (e.symm j)` (spectators `ξ`, active coordinates
  `0`), `continuous_specPt`, `continuous_elim_reindex`, `faceConstSpec` (`vol(F')/|det M|` of the
  active pair), `activeTruthSpecDensityFn ξ u = A Γ(β) B^{-β} q D^{-qη} faceConstSpec ·
  ∏ ξ_l^{d_l−1} u^{qη−1} (wt|b|)(bridgePt (specPt e ξ) u) |a(bridgePt (specPt e ξ) u)|^{-β}`,
  `activeTruthSpecDensity` (cut to `specBox n ρ ×ˢ Ioo 0 ρ`), `activeTruthSpecMeasure` (push-forward
  of the density on `(Fin n → ℝ) × ℝ` along `(ξ,u) ↦ rep(bridgePt (specPt e ξ) u)`),
  `specTruthPt_mem_ball`, measurability/nonnegativity, `integral_activeTruthSpecMeasure`,
  `integrable_activeTruthSpecDensity` (product density `∏ 1_{Ioo} ξ^{d−1} ⊗ 1_{Ioo} u^{qη−1}` via
  `Integrable.mul_prod` after `Measure.volume_eq_prod`, times the bounded chart factors),
  `isFiniteMeasure_activeTruthSpecMeasure`, `tendsto_modelKernelOf_activeTruthSpectator` (kernel
  reindexed along `e`, unit replaced by `max(unitFn, ma)` off the domain, traces
  `W_tr(ξ,u) = weightFn (specPt e ξ) u`, `a_tr(ξ,u) = max(unitFn (specPt e ξ) u, ma)` from the
  joint continuity at the spectator truth points, which lie in the ball for `ξ` in the box; the
  limit is identified with `∫ φ dμ` through `integral_prod` and the indicator bookkeeping in `ξ`
  then `u`), `TermData.activeTruthSpectator : (γp + βδ − ηγ, k, activeTruthSpecMeasure)` under
  `d_l > 0` and the active certificate. Astra round-10 item (a) CLOSED.
- `ActiveTruthLPChart.lean` (f7f4e41; hironaka 8a3e0b5bd): **the LP-to-chart interface and the
  nonvanishing wrappers** (Astra round-10 item (b)). `exists_face_point_of_volume_pos` (a positive
  face polytope yields a face point `Sum.elim w y` with `w > 0` and the solved pair
  `y = M⁻¹(−transShift … 1 w)`, i.e. `y_j = fibreA j − fibreCoef j ⬝ w`, via
  `transMat_mulVec_add_shift`), `sum_cost_eq_of_face` (`∑ c_i α_i = βδ − ηγ` on the face),
  `reducedCost_eq` (reduced costs along `e`: `specd` on the spectators, `0` on the active
  coordinates), `lpOptimal_activeTruth_spectator_iff` (over any finite index with
  `e : Fin n ⊕ (Fin k ⊕ Fin 2) ≃ ι`: `LPOptimal Q κ γ δ (r + 1) α ↔ α ≥ 0 ∧ κ·α = δ ∧ Q·α = γ ∧
  α ∘ e ∘ inl = 0` under `hr`, `hd` and a face point — a wrapper of `lpOptimal_activeTruth_iff`),
  `activeTruth_lam_eq_lpExponent` (`γp + βδ − ηγ = lpExponent γ p (r+1) α` for every face point,
  so the active-truth power is the LP value of the face, the same power as the vertex terms of
  that face), the chart form `lpOptimal_iff_activeFace` (with `hvol` in place of the face point),
  `faceConst_pos`/`faceConstSpec_pos`/`constA_pos`, and **`activeTruthMeasure_ne_zero`**,
  **`activeTruthSpecMeasure_ne_zero`**: a positive face polytope and one truth point
  (`u₀ ∈ (0,ρ)`, resp. `(ξ₀, u₀)` with `ξ₀` in the box) where `wt |b| > 0` make the coefficient
  measure nonzero (`integral_pos_iff_support_of_nonneg`; the open set `{wt|b| > 0} ∩ (0,ρ)` lies in
  the support of the density, `IsOpen.measure_pos`). This is the guard Astra asked for: a term
  certified at `(λ, k)` with a zero measure would misidentify the leading order.
- Astra round 11 (`gpt_responses/research_round11_v1.md`, e47fce9): audit of (a), (b) clean (no
  Jacobian for the push-forward, a.e.-in-the-box traces sufficient, global trace bounds harmless);
  strong duality (deriving `(β,η)` from LP optimality) is a separate project — scope the result to
  faces admitting the displayed certificate; the `c_j = a_j = 0` case is a different boundary
  regime (the solved coordinate does not collapse, so the general-unit trace must retain it):
  DEFERRED as a scoped exclusion; solved-pair independence via the augmented linear map
  `H_e(α) = (α_free, κ·α, Q·α)` with `|det H_e| = |det M_e|` (Jacobian ratio
  `|det M_{e₂}|/|det M_{e₁}|`); moving parameters by SQUEEZING between fixed-parameter corner
  kernels (monotone in `B`, monotone in `D` through the cut) rather than a parameter-uniform DCT.
  Ranking: (d) example identification, (g) export, (f) moving parameters, (c) solved-pair
  independence, (h) one mixed vertex/tied/active example, (e) deferred.
- `ActiveTruthExampleBridge.lean` (97b89e7; hironaka f219e5b77): **the three-coordinate example is
  an instance** — `lintegral_indicator_one_mul`, `deg_cutVar_lt_iff`
  (`t^{-2}(xyz)^{-1} < 1 ↔ xyz > t^{-2}`), `degIntegrand_eq` (the example's `ofReal ∘ modelIntegrand`
  is the three `(0,1)` indicators times `degIntegrand`), `lintegral_degExample`
  (`∫⁻ ofReal (modelIntegrand …) = degI t`: `lintegral_sum_split`, `volume_preserving_funUnique`
  for `Fin 1 → ℝ`, `volume_preserving_finTwoArrow` for `Fin 2 → ℝ`, `lintegral_lintegral_swap`,
  `lintegral_prod_symm'`, then the indicators to set integrals), `modelKernel_degExample_eq`
  (`modelKernel 1 1 1 1 2 0 1 3 degQ degκ degr 1 1 t = (degI t).toReal`), and
  **`tendsto_degI_of_face`** (`t⁴ I(t)/log t → 1` from the general theorem, the regression test
  against `DegenerateFace.tendsto_degI`). Astra round-11 item (d) CLOSED.
- `ActiveTruthFaceInvariance.lean` (3dcf449; hironaka d4e736be1): **solved-pair independence of
  the face constant** (Astra round-11 item (c)). `augMat κ Q = fromBlocks 1 0 A M'`
  (`α ↦ (α_free, κ·α, Q·α)`, `augMat_mulVec`, `augMat_det = −det transMat`), `faceLift κ Q δ γ w =
  augMat⁻¹ (w, δ, γ)` (`faceLift_eq_of`: the unique constraint-set point over `w`; `faceLift_inl`,
  `faceLift_sum_κ/Q`, `faceLift_inr = fibreA − fibreCoef ⬝ w`),
  `mem_facePolytope_iff_faceLift_nonneg` (`w ∈ F' ↔ 0 ≤ faceLift w`), `transitionMat κ Q σ =
  augMat (κ∘σ) (Q∘σ) · permMatrix σ · augMat⁻¹` (`transitionMat_mulVec`: `(w, v) ↦
  ((faceLift w) ∘ σ ∘ inl, v)`, hence `transitionMat_eq_fromBlocks` with lower blocks `0, 1`,
  `transitionMat_det_eq`, `abs_det_transitionMat = |det M_σ|/|det M|`), `faceLift_transition_eq`
  (the transition map is affine with linear part the top-left block), `image_facePolytope_transition`
  (`F'_σ` is the affine image of `F'`), **`volume_facePolytope_div_det_perm`** (`vol(F'_σ)/|det M_σ| =
  vol(F')/|det M|` by `addHaar_image_linearMap` + `measure_preimage_add_right`),
  `volume_facePolytope_div_det_eq` (two splittings `e₁ e₂ : Fin k ⊕ Fin 2 ≃ ι`, via
  `σ = e₂.trans e₁.symm`), **`faceConst_eq`** (`P.faceConst i γ e₂ = P.faceConst i γ e₁`). No LP
  or nondegeneracy hypotheses beyond `det ≠ 0` and `κ > 0` (finiteness of the volume).
- `ActiveTruthParam.lean` (d061e6a; hironaka 366149be5): **the face theorem with moving constants**
  (Astra round-11 item (f), by squeezing). `tendsto_of_antitone_param2` (a kernel antitone in two
  positive parameters, fixed-parameter limits `L b d` continuous at `(B₀, D₀)`: the moving kernel
  is trapped between the corner kernels at `(B₀ ∓ d, D₀ ∓ d)`), `modelIntegrand_const_anti_of_le`
  (the constant-unit integrand is antitone in `B` — the exponential — and in `D` — the cut
  shrinks the domain — pointwise, any index type), `one_lt_of_exp_one_le`,
  `lintegral_modelIntegrand_const_ne_top` / `_spectator_ne_top` (finiteness from
  `normalised_lintegral_le`, resp. `specF_le` + `lintegral_specG_ne_top`),
  `modelKernel_const_anti_active` / `_spectator` (the Bochner kernels with `A = 1` compared through
  `lintegral` and `ENNReal.toReal_mono`), **`tendsto_modelKernel_activeTruth_param`** and
  **`tendsto_modelKernel_activeTruth_spectator_param`**: with `A(t) → A₀` (no sign condition),
  `B(t) → B₀ > 0`, `D(t) → D₀ > 0`, constant units `w₀ ≥ 0`, `a₀ > 0`, the normalised moving
  kernel converges to the fixed-constant limit at `(A₀, B₀, D₀)`. Constant units only: with
  `u`-dependent units `D` enters the unit argument `u = cutVar` and the monotonicity in `D` fails
  (Astra: the squeeze needs the units fixed); the general-unit moving version would need the
  parametrised DCT chain.
- `ActiveTruthGeneralParam.lean` (e418f23; hironaka 52948f46a): **the general-unit face theorem
  with moving constants**, by a TIME CHANGE instead of the parametrised DCT. `cutTime D₀ γ q D t =
  t (D₀/D)^{q/γ}`, `rpow_cutTime`, `cutVar_cutTime` (the cut at `(D, t)` is the cut at `(D₀, τ)`),
  **`modelKernel_cutTime`** (exact: the kernel at `(A, B, D, t)` is the kernel at
  `(A (D₀/D)^{qp}, B (D₀/D)^{-qδ/γ}, D₀, τ)`, any index type, any units), so a moving `D` is a
  moving `A, B` along the reparametrised time; `modelIntegrand_anti_B` (the general integrand is
  antitone in `B` for nonnegative units — `B` enters only through the exponential),
  `modelKernel_eq_toReal_of_nonneg`, `lintegral_modelIntegrand_general_ne_top` (from
  `normalised_lintegral_leG`), `modelKernel_anti_B_general`, `tendsto_normaliser_ratio`
  (`N(t)/N(t c(t)) → 1` for `c → 1`, `N(t) = t^λ/(log t)^k`: `c^{-λ}(1 + log c/log t)^k`), and
  **`tendsto_modelKernel_general_param`**: `A(t) → A₀`, `B(t) → B₀ > 0`, `D(t) → D₀ > 0`, `γ > 0`,
  bounded jointly measurable units with traces, the fixed-parameter limit
  `A₀ Γ(β) B₀^{-β} q D₀^{-qη} vol(F')/|det M| ∫_0^ρ u^{qη−1} W_tr a_tr^{-β}`. Proof: the
  one-parameter squeeze `tendsto_of_antitone_param` at fixed `D₀` along `τ` (fixed-`b` limits from
  `tendsto_modelKernel_general` composed with `τ → ∞`), times the normaliser ratio.
- `ActiveTruthChartParam.lean` (3fd2c59; hironaka d3876ceb3): **the chart-level active-truth term
  along a moving parameter** — `tendsto_modelKernelOf_activeTruth_param` and
  `tendsto_termKernel_activeTruth_param`: for `σ(t) → σ₀ ≠ 0`, `γ > 0`, the normalised chart kernel
  (resp. the admissible-at-`σ₀` term kernel) converges to `∫ φ d(activeTruthMeasure … σ₀ …)`. The
  chart constants are continuous in `σ` (`tendsto_constA/B/D`), the reindexed weight and unit are
  `σ`-free, the unit modification `max(unitFn, ma)` off the domain is done at each `t` with `σ(t)`
  (`σ(t) ≠ 0` eventually by `Tendsto.eventually_ne`), and `tendsto_modelKernel_general_param` does
  the rest; the value identification `hval` is the fixed-`σ₀` one. The analogue of
  `tendsto_termKernel_tied_param` for the active-truth term (parameter stability, Astra round 5
  item 1, now for all three term shapes).
- Astra round 12 (`gpt_responses/research_round12_v1.md`, f96245f): time-change audit clean
  (exponents `qp`, `−qδ/γ` right; keep `γ > 0`: at `γ = 0` a moving `D` changes the unit
  evaluation with no compensating time change). Closure verdict: the Euclidean analytic
  active-truth claim is closed for the nondegenerate strictly-positive-exponent regime; the
  hypothesis-discharge checklist for charts from a resolution: (1) the strict LP regime
  (`β, η > 0`, `κ > 0`, spectators separated) must be supplied by the classification, endpoints
  `β = 0`/`η = 0` not covered; (2) `hc₀, hc₁` are substantive (else (e)); (3) unit positivity on the
  branch (analytic ≠ positive) and the global measurable extension must preserve the kernel; (4)
  traces from continuity (with spectators retained); (5) `hWb` is a nonnegative-weight theorem —
  signed tests need the ± decomposition; (6) all admissible `(ε, b)` branches, Jacobians, cutoffs
  exactly once. Ranking: (1) compact-σ uniformity [DONE below], (2) export, (3) `xy = s` total-kernel
  bookkeeping on `mixData`, (4) mixed example, (5) the `c_j = a_j = 0` constant-unit boundary
  theorem with the explicit formula `A q D^{-qη} vol(F')/|det M| ∫_0^ρ u^{qη−1} ∫_0^∞ v^{β−1} e^{-Bv}
  ∏_{j∈J} 1_{(0,ρ)}(z_j(v,u)) dv du` (frozen solved coordinates `z_j(v,u) = exp[M⁻¹(log v,
  q log(D/u))]_j`; general units then need a partial trace retaining `z_J`), (6) `h < 0` weighted
  mixed truth, (7) support-separated distinguishability.
- `ActiveTruthChartUniform.lean` (c0ff89a; hironaka 58bf50473): **uniformity in the parameter on
  compact sets**. `eventually_uniform_of_moving` (generic: if `F t (σ t) → L σ₀` along every path
  `σ` in a compact `C` with `σ → σ₀`, and `L` is continuous on `C`, then `∀ ε > 0, ∀ᶠ t, ∀ σ ∈ C,
  |F t σ − L σ| < ε`; proof by contradiction with strictly increasing escaping times built by
  `Nat.rec` from `Filter.frequently_atTop`, a convergent subsequence of the bad parameters by
  `IsCompact.tendsto_subseq`, and the interpolating path `σpath t = if ∃ k, tₖ = t then σₖ else σ₀`
  — well defined by injectivity of the times), `integral_activeTruthMeasure_eq` (the explicit
  coefficient formula, extracted from the chart proof), `continuousOn_integral_activeTruthMeasure`
  (on `σ ≠ 0`), **`tendsto_termKernel_activeTruth_uniform`** (compact `C ∌ 0` on which the branch
  is admissible, `γ > 0`: the normalised term kernel converges uniformly in `σ ∈ C` for each fixed
  admissible test function; not uniform over test functions).
- Correction to the round-12 query: the "`xy = s` total-kernel bookkeeping" was already closed by
  `MixedTruthRecord.lean` (`mixData_totalKernel`, `mix_tendsto_totalKernel`,
  `mix_tendsto_fibre_expectation`); item 3 of the round-12 ranking is void.
- `ActiveTruthDegenerate.lean` (00baf1f; hironaka 7d864c216): **the boundary regime `c_j = a_j = 0`,
  constant units** (Astra round-12 item 5; second constraint vacuous WLOG). With
  `fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0` the second fibre constraint reads `0 < (M⁻¹v)_1`
  (strict, from `mem_fibreSet_iff`), independent of the free coordinates and the scale:
  `volume_fibreSet_eq_degenerate` (`vol(fibreSet L v) = 1_{(M⁻¹v)_1 > 0} · vol(fibre2 c₀ 0 a₀ 1 b₀
  0 L)`, null boundary of the remaining constraint only), `facePolytope_eq_of_degenerate`
  (`F' = poly2 c₀ 0 a₀ 1`, the one-constraint polytope), `poly2_zero_right_subset`,
  `tendsto_volume_fibreSet_div_degenerate` (the existing `tendsto_volume_poly2` applied with the
  vacuous constraint written as `0 ⬝ w ≤ 1`, nondegenerate through `a₂ = 1`),
  `measurable_indicator_fibreB`, `tendsto_lintegral_vWeight_fibre_degenerate` (same majorant),
  **`tendsto_modelKernel_activeTruth_degenerate`**: `t^{γp+βδ−ηγ}/(log t)^k · K(t) →
  A w₀ ρ^{Σ(r+1)}/|det M| · (∫⁻ v, vWeight β η 0 c₀ h₀ v · 1_{(M⁻¹v)_1 > 0}).toReal · vol(F')` — the
  old transverse `(s,h)`-integral restricted to a half-plane (Astra: "a half-space in the linear
  transverse variables"), no Gamma value in general; the strict inequality makes the indicator
  exact for every `v` (no a.e. exceptional set). Not done: the general-unit version (needs a partial
  trace retaining the frozen solved coordinate `z_1(v)`, per Astra), the `j = 0` mirror (swap the
  solved pair), the chart wrapper.
- `MixedTruthWeightedNeg.lean` (a174683; hironaka 320887224): **the weighted mixed truth with a
  negative exponent** (Astra round-12 item 6; the third case of the round-5 trichotomy).
  `image_fibreInv` (`x ↦ σ/(tx)` is an involution of the fibre interval `(σ/(bt), b)`),
  `weightedMixed_change_of_variables` (`∫ x^{h−1} f(x, σ/(tx)) dx = (σ/t)^h ∫ u^{−h−1} f(σ/(tu), u) du`
  on that interval, by `integral_image_eq_integral_abs_deriv_smul`), **`tendsto_weightedMixed_neg`**:
  for `h < 0`, `t^h ∫_{σ/(bt)}^b x^{h−1} f(x, σ/(tx)) dx → σ^h ∫_0^b u^{−h−1} f(0, u) du` — the mass
  moves to the other axis with the finite density `σ^h u^{−h−1}`; the proof is the change of
  variables plus `tendsto_weightedMixed` at `−h` with the coordinates exchanged. Trichotomy
  complete: `h > 0` finite axis measure `x^{h−1} dx` (`tendsto_weightedMixed`), `h = 0` the
  logarithm (`MixedTruthLog`), `h < 0` the other axis at the scale `t^h`.
- **The general-truth hironaka export** (hironaka `wall-atlas` 70ac670cb, local; Astra round-11 item
  (g) / round-12 item 2; no laplace code). New files `Monomialize/Relative/Wall/Truth{Chart,Atlas,
  Partition,Weighted,Integral,Export,Record,Instance,Theorem}.lean` (1446 lines, all zero-warning,
  standard axioms): the wall layer with the coordinate `z ℓ` replaced by a function
  `T : (Fin n → ℝ) → ℝ` throughout. `WallChartAtT F T g P`, `exists_wallResolutionT_of_bo` /
  `exists_wallResolutionT` (hypotheses `hT : AnalyticOnNhd ℝ T U₀`, `hT0 : T 0 = 0`,
  `hne : ¬ ∀ᶠ z in 𝓝 0, F z * T z = 0` taken directly; the resolution of `G = F * T`, factor
  separation, `exists_chart_absorbing_unit_pair … (f := T)`), `WallAtlasT F T g C` (field `base :
  T (watanabeRep g (φ i) u) = S i * ∏ u^qs`), `isCompact_inter_abs_le` (`L ∩ {|T| ≤ c}` compact for
  `T` continuous on `L`, via `ContinuousOn.preimage_isClosed_of_isClosed`), `exists_wallAtlasT`,
  `eventually_preimage_subset_of_isCompactT` (needs `hT : ContinuousOn T W`),
  `exists_partitionOfUnity_smallParameterT`, `offWallT F T = {F z * T z ≠ 0}`, the weighted transport
  `WallAtlasT.lintegral_eq_sum_charts(_box/_clamp)`, Bochner forms, `euclidean_export`,
  `WallAtlasT.toTruthChartsData : TruthChartsData m T L'` (fields as `toWallChartsData`, `truth :=
  repClamp_apply_truth`), `aClamp`/`phase_repClamp` (the monomial form of `F` on the boxes), and
  **`exists_truthChartsData(_phase)`**: for `F, T` analytic on `U₀ ∋ 0`, `T 0 = 0`, `F·T ≢ 0` near
  `0`, `W ⊆ U₀` connected open `∋ 0`, `L ⊆ W` compact: `∃ ε > 0, Nonempty (TruthChartsData m T (L ∩
  {z | |T z| ≤ ε}))`, the `_phase` version adding `kF, a` with `a i` continuous nonvanishing and
  `F (D.rep i u) = a i u * ∏ u^(kF i)` on the boxes. Mechanically generated from the ℓ-files by a
  regex transform (`z ℓ → T z`, `watanabeRep … u ℓ → T (watanabeRep … u)`, `(hF) → (hF) (hT)`);
  hand patches: the `hGne`/`hG0`/`hF₂` lines of the resolution, the two closedness proofs (helper
  above), and two local names `T` (a set and a sequence) that shadowed the truth function. The
  fibre identity (`fibre_eq`) does not transfer (the fibre `{T = s}` is a hypersurface); the
  push-forward identity `lintegral_mul_comp_truth` of the record is the replacement. Not done: a
  Phase-like record for general truths on the laplace side (the `_phase` conjunct is the raw
  material), and a mixed instance produced through this export rather than by hand (`mixData`).
- `ActiveTruthDistinguish.lean` (cd8f38c; hironaka 76a2c5699): **support-separated
  distinguishability** (Astra round-12 item 7). `normalise_restrict_ne_of_separated` (measurable `O`
  with `0 < μ₁ (O ∩ L')`, `μ₂ (O ∩ L') = 0`, `μ₁ L' ≠ ⊤` ⇒ the normalised restrictions to `L'`
  differ; evaluate both at `O`), `exists_observable_of_separated` (two certified phases whose
  leading measures are so separated: some continuous nonnegative bounded `ψ` supported in `L'` has
  `fibreRatio₁ ψ χ − fibreRatio₂ ψ χ ↛ 0`; contrapositive of `normalise_restrict_eq_iff_forall_tendsto`),
  `le_leadingMeasure_of_leading` (`C.μ p s ≤ C.leadingMeasure s` for a leading term `p`;
  `Measure.finsetSum_apply` + `Finset.single_le_sum`), `continuous_truthSegment`,
  `activeTruthMeasure_apply` (`= ∫⁻ u in segment⁻¹' O, ofReal(dens)`), **`activeTruthMeasure_pos_of_open`**
  (an open `O` containing a truth-segment point `rep(bridgePt 0 u₀)` of positive weight `wt|b|`,
  positive face polytope: `0 < activeTruthMeasure O`; `setLIntegral_pos_iff` and the open set
  `{wt|b| > 0} ∩ (0,ρ) ∩ segment⁻¹' O`), `activeTruthMeasure_eq_zero_of_disjoint` (segment misses
  `O` ⇒ mass `0`), **`exists_observable_of_activeTruth_separated`**: a leading term of `C₁` whose
  measure is an active-truth measure with a positive-weight segment point in an open `O ⊆ L'` with
  `C₂.leadingMeasure O = 0` gives the distinguishing observable. Astra's caveat (round 11) is built
  in: distinguishability needs the explicit support separation (`rep` may identify images, weights
  may create coincidences); nothing is claimed for different faces per se.
- Astra round 13 (b59b87f, `research_round13_{q,v1}.md`): export audit positive (`T 0 = 0` and
  `F·T ≢ 0` are the right non-degeneracy; no `F 0 = 0`, no positivity in the transport theorem;
  `TruthChartsData` is sufficient for the EXACT push-forward theorem, an asymptotic consumer needs a
  density factorisation `dens = ∏|u_j|^{r_j} J(u)` and an explicit fibre-kernel representative — the
  push-forward identity fixes `K_θ` only a.e.); the general-unit boundary statement (partial trace
  in `update y (inr 1) z`-form, unit inside the transverse exponential, `x_b = ρ e^{-(M⁻¹v)_1}`
  with one factor `ρ`, same domination); (h) = a certificate-level assembly example only; ranking:
  (1) general-unit boundary, (2) laplace-side bridge consuming the export, (3) `j = 0` mirror +
  chart wrapper, (4) positivity/localisation corollaries, (5) certificate-level mixed example.
- `ActiveTruthDegenerateGeneral.lean` (d3fe6c9; hironaka 229c09ba5): **the boundary regime with
  general units** (Astra round-13 item 1). `survCoord ρ κ Q v = ρ e^{-fibreB κ Q v 1}` (in `(0,ρ)`
  iff `fibreB … 1 > 0`), `fibreSet_eq_empty_of_degenerate` (`(M⁻¹v)_1 ≤ 0` ⇒ empty fibre),
  `negExpMap_fibreLift_eq_update` (the fibre path is `update (negExpMap (update lift (inr 1) L))
  (inr 1) (survCoord)`), **`tendsto_lintegral_fibre_weighted_degenerate`** (the weighted fibre limit
  with trace hypothesis `Tendsto (fun y ↦ Φ (Function.update y (Sum.inr 1) (survCoord ρ κ Q v)))
  (𝓝[box] 0) (𝓝 Φ₀)`: the nondegenerate proof with the second hyperplane dropped from the null set,
  the collapsing coordinates `inl ⊔ inr 0` tending to `+∞` in log coordinates and the surviving
  one replaced by `L` on the auxiliary path), `ampG_tendsto_degenerate`, `vWeightTD ρ D q κ Q β η c₀
  h₀ Wtr atr v = 1_{h>h₀} 1_{(M⁻¹v)_1>0} ofReal(Wtr(z(v),u(v)) e^{-(βs+ηh)} e^{-c₀ atr(z(v),u(v))
  e^{-s}})` (measurable, `≠ ⊤`, `vWeightTD_le`: `≤ ofReal W_* · vWeight β η 0 (c₀ a_-) h₀`),
  `tendsto_lintegral_innerKvG_degenerate` (DCT with the same majorant; `by_cases` on `h > h₀` and
  on `(M⁻¹v)_1 > 0`, the empty-fibre case giving `0`), **`tendsto_modelKernel_general_degenerate`**:
  hypotheses as `tendsto_modelKernel_general` with `hc₁` replaced by `hdeg`, traces
  `Wtr atr : ℝ → ℝ → ℝ` jointly measurable with bounds on `(0,ρ)²` and the partial-trace
  convergence `∀ z u ∈ (0,ρ), Tendsto (fun y ↦ W (update y (inr 1) z) u) (𝓝[box] 0) (𝓝 (Wtr z u))`;
  limit `A ρ^{Σ(r+1)} |det M|⁻¹ (∫⁻ vWeightTD … (B ρ^{Σκ}) h₀ Wtr atr).toReal vol(F')` — no Gamma
  value, the unit inside the exponential (Astra: it cannot be pulled out as `a_tr^{-β}` since the
  surviving coordinate depends on `v`). Constant traces recover the constant-unit theorem
  (`vWeightTD = w₀ · vWeight β η 0 (c₀ a₀) h₀ · 1_{(M⁻¹v)_1>0}`). Not done: the `j = 0` mirror
  (swap the solved pair), the chart wrapper, a laplace-side bridge consuming the hironaka export.
- `TruthPushforward.lean` (hironaka `wall-atlas` f81e1f2d5, local): **the exact push-forward
  theorem for an analytic truth** (Astra round-13 item 2, first half). `exists_truth_pushforward`:
  under the hypotheses of the export (`F, T` analytic on `U₀ ∋ 0`, `T 0 = 0`, `T` measurable,
  `F·T ≢ 0`, `W ⊆ U₀` connected open `∋ 0`, `L ⊆ W` compact), `∃ ε > 0, ∃ D : TruthChartsData m T
  (L ∩ {|T| ≤ ε}), ∀ θ measurable, Measurable (D.totalKernel θ) ∧ ∀ η measurable, ∫⁻_{L ∩ {|T| ≤ ε}}
  θ(z) η(T z) = ∫⁻ η(s) D.totalKernel θ s` — the composite of `exists_truthChartsData` with the
  mirrored `TruthChartsData.lintegral_mul_comp_truth`; the total fibre kernel of the exported data
  is the explicit representative (fixed only a.e. by the identity, per Astra).
- `ActiveTruthChartDegenerate.lean` (96ec189; hironaka 9b2ea0c71): **the chart wrapper of the
  boundary regime** (Astra round-13 item 3; the `j = 0` labelling is absorbed by the splitting
  `e`, so no abstract mirror). `survPt e z = fun j ↦ update 0 (inr 1) z (e.symm j)` (continuous,
  `|survPt e z j| < ρ` for `z ∈ (0,ρ)`), `degPt i ε b σ e v = bridgePt (survPt e (survCoord ρ κe Qe
  v)) (truthOf ρ D q Qe (v 1))` (continuous; in the open ball on `degSet = {h > h₀} ∩ {fibreB v 1 >
  0}`), `activeTruthDegDensity` (indicator of `degSet` of `wt|b|(degPt v) e^{-(βs+ηh+0)}
  e^{-c₀ |a(degPt v)| e^{-s}}`; measurable, nonnegative, `ofReal dens ≤ ofReal M_b · vWeight β η 0
  (c₀ m_a) h₀`), `degConst = A ρ^{Σ(r+1)} |det M|⁻¹ vol(F')`, **`activeTruthDegMeasure`** = map of
  `withDensity (ofReal (degConst · dens))` along `v ↦ rep(degPt v)` (finite), `integral_
  activeTruthDegMeasure`, `vWeightTD_chart_eq` (`vWeightTD … (weightFn (survPt z) u) (unitFn (survPt
  z) u) v = ofReal (φ(rep(degPt v)) · dens v)` pointwise, via `weightFn_eq_of_mem_closedBall`),
  **`tendsto_modelKernelOf_activeTruth_degenerate`** (hypotheses as `tendsto_modelKernelOf_
  activeTruth` with `hc₁` replaced by `hdeg`; the reindexed kernel `hK` verbatim, partial traces
  `We (update y (inr 1) z) u → weightFn (survPt e z) u` through `continuousAt_weightFn` at the ball
  point `bridgePt (survPt z) u`, `Continuous.update`, the general-unit boundary theorem, and
  `integral_eq_lintegral_of_nonneg_ae` to identify the limit), `TermData.activeTruthDegenerate`.
  The measure lives on the two-dimensional surface `(z, u) ↦ rep(bridgePt (survPt z) u)` (the
  nondegenerate one on the one-dimensional truth segment). Gotcha: the push-forward map must go
  through `D.rep i` (the model point `degPt` is in chart coordinates). Not done: positivity of the
  degenerate measure (`activeTruthDegMeasure_ne_zero`), the certificate-level mixed example.
- Round-13 closure (laplace 68c136e; hironaka abdef59af, fb7fd025d, local): **the density
  certificate of the export** — hironaka `TruthInstance.lean` gains `WallAtlasT.bClamp`, `wtClamp`
  (continuous; `bClamp ≠ 0`, `wt ∈ [0,1]`) and `chartDensityClamp_eq` (`dens i u = wt i u *
  |bClamp i u * ∏ u^(hJ i)|` on the box), `TruthTheorem.lean` gains
  **`exists_truthChartsData_certified`** (the phase data of `F` and the density factorisation with
  a continuous nonvanishing Jacobian unit and a `[0,1]` partition weight — Astra's "density
  structure" for asymptotic consumers, exported without changing `TruthChartsData`);
  **positivity of the degenerate measure** (`ActiveTruthDegeneratePositive.lean`: `isOpen_degSet`,
  `degConst_pos` (positive face polytope), `activeTruthDegMeasure_apply`,
  `activeTruthDegMeasure_pos_of_open` (an open set containing `rep(degPt v₀)` for `v₀ ∈ degSet`
  with `wt|b|(degPt v₀) > 0` is charged), `activeTruthDegMeasure_ne_zero`,
  `activeTruthDegMeasure_eq_zero_of_disjoint` — the distinguishability ingredients for the boundary
  regime); **the certificate-level dominant term** (`ActiveTruthLeadingTerm.lean`:
  `leadingMeasure_eq_sum_filter` (the definition), `leadingMeasure_eq_of_unique`,
  `ofTermData_leadingMeasure_eq_of_lt`: in `ofTermData T`, a term `p` with `(T p).lam < (T q).lam`
  for all `q ≠ p` has `leadingMeasure = (T p).μ` — `lam₀ = (T p).lam` by `Finset.le_inf'
  univ_nonempty`, `k₀ = (T p).kk` by `Finset.sup_le` on the singleton filter; this is the
  "which shape leads" assembly statement Astra asked for in place of a hand-built mixed atlas).
  With these, every item of the round-13 ranking is closed; the Euclidean programme of the
  active-truth and mixed-truth claims is complete at this layer per Astra's closure criterion
  (exact transport supported by the export; asymptotic consumers have the certified data).
- Astra round 14 (db67154, `research_round14_{q,v1}.md`): closure confirmed at the round-13
  criterion (with two qualifications: the general-truth consumer interface was still missing, and
  push-forward identifies densities a.e. only); a `TruthChartsData.Phase` is the right consumer
  interface (no obstruction: `bridgePt`/`solvedCoord` only use the monomial form `T ∘ rep = S ∏ u^q`
  with a scalar sign `S`); the exported `xy` regression is the acceptance test (the identity chart of
  `xy` is the two-way TIED logarithmic regime, ratios `(h_j+1)/q_j = 1` twice, not the degenerate
  boundary regime; the resolved sector charts `(u,v) ↦ (u,uv)`, `(uv,u)` each contribute
  `½ log(1/t)`); the anchored unquotiented profile `Ψ_{p*}` is the right object for "LP uniqueness ⇔
  integrability" (the quotiented transverse profile version is FALSE); the exact log-face constant is
  `vol_d(F) ∫_N 1_{z_j ≥ 0, j ∈ J₀} e^{-c·z} exp(-∑_{i∈A₀} a_i e^{-α_i·z}) dz`. Ranking: (1) the
  general-truth Phase interface, (2) exported `xy` regression, (3) an a.e.-transport/limit
  identification lemma, (4) anchored-profile statement, (5) exact log-face constant.
- **The term layer generalised to an arbitrary truth function** (laplace 9c4c1ff, 39 files;
  hironaka a3877ad74, ca845cfdc): `WallChartsData m ℓ L'` is now `abbrev … := TruthChartsData m
  (fun z ↦ z ℓ) L'` (the general record and its kernel API `chartFun`, `totalKernel`,
  `measurable_fibreKernel`, `lintegral_mul_comp_truth` live in `WallChartsData.lean`,
  namespace `TruthChartsData`; the coordinate push-forward `lintegral_mul_comp_coord` is its
  instance; `fibre_ae`, `fibre_eqOn`, `fibre_eq`, `totalKernel_ae_le/_eq`, `toTruth` (now `:= D`)
  stay in namespace `WallChartsData`; `FibrePointwise` split into a generic `TruthChartsData` block
  and the coordinate fibre identities). `TruthChartsData.Phase {T} (D : TruthChartsData m T L') F`
  and the whole term layer (`bridgePt`, `modelKernelOf`, `termKernel`, `TermData.vertex/tied/
  partial/activeTruth/activeTruthDegenerate`, `TermMeasureCertificate`, `fibreRatio`, the
  distinguishability and expectation theorems, the LP interface) are stated for
  `{T : (Fin (m + 1) → ℝ) → ℝ} {D : TruthChartsData m T L'}`, namespaces `TruthChartsData` /
  `TruthChartsData.Phase`; the truth hypotheses `D.rep i u ℓ = truthMono …` became `T (D.rep i u) =
  truthMono …`, `z ℓ = σ t^{-γ}` became `T z = …`. No statement changed for coordinate truths (the
  records `toyData`, `atData`, `bsData : WallChartsData 1 0 _` are untouched; dot notation resolves
  through the abbrev). Mechanics: `abbrev` + regex rename of namespaces/binders + rename of explicit
  `WallChartsData.<moved name>` references (`Qexp` was the one missed on the first pass); only
  `FibrePointwise` needed a hand split. Mirror-chain gotcha: the import rule `Laplace.Multi.` →
  `Monomialize.Relative.Wall.Euclid.` also hits nested `namespace Laplace.Multi.ToyWall` and `open …
  Laplace.Multi.ToyWall` lines, which must become `Monomialize.Wall.ToyWall` (four files). **The
  consumer**: hironaka `WallAtlasT.toPhase` (`TruthInstance.lean`; fields `kF hJ aClamp bClamp
  wtClamp` with the bounds `ma Ma mb Mb` of the atlas, `phase`, `dens_eq`) and
  **`exists_truthChartsData_withPhase`** (`TruthTheorem.lean`): `∃ ε > 0, ∃ D : TruthChartsData m T
  (L ∩ {|T| ≤ ε}), Nonempty (D.Phase F)` — the resolution of `F · T` for an analytic `T` with
  `T 0 = 0` now feeds the term theorems directly (Astra round-14 item 1). Standard axioms.
- `MixedTruthExport.lean` (2b39256; hironaka 412e9cefb) and hironaka `TruthMixedRegression.lean`:
  **limit identification through transport and the exported `xy` regression** (Astra round-14
  items 2–3). `TruthChartsData.totalKernel_ae_eq_of_support` (two chart systems for the same `T`
  over measurable regions `L₁`, `L₂`: kernels a.e. equal for `θ` supported in `L₁ ∩ L₂`; both set
  integrals equal the full-space integral of `θ · 1_E(T)`), **`totalKernel_mul_comp_truth`**
  (`D.totalKernel (θ · η∘T) s = η s · D.totalKernel θ s` for `η s ≠ ⊤`: on each branch the solved
  point has `truthMono = s` by `solvedCoord_pos/neg_spec`, so `T (rep u) = s` on the domain),
  `eq_of_ae_eq_of_continuousAt` (a.e. equal + both continuous at `s₀` ⇒ equal at `s₀`, via
  `isClosed_diagonal.isOpen_compl` and `Measure.measure_pos_of_mem_nhds`), the truth cutoff
  `truthCutoff ε s = min 1 (max 0 (2 − 2|s|/ε))` (`= 1` on `|s| ≤ ε/2`, `= 0` off `|s| < ε`), the
  closed square `mixLc = [0,1/2]²` (compact) and its identity-chart record `mixDataC` with the same
  logarithmic kernel `∫_{2s}^{1/2} θ(s/x, x) dx/x` as `mixData` (`mixDataC_totalKernel_eq`),
  `mixThin ε = closedBall 0 (1/2) ∩ {|z₀z₁| ≤ ε}`, and **`exported_mix_tendsto_totalKernel`**: for
  ANY `D : TruthChartsData 1 (z₀z₁) (mixThin ε)`, `(D.totalKernel (e^{-t z₀z₁ a} ψ) (σ/t)).toReal /
  log t → e^{-σ a(0)} ψ(0)` (`a` continuous, `ψ ≥ 0` continuous supported in `mixLc`). Proof: cut
  off with `θ_ε = θ · ofReal(truthCutoff ε (z₀z₁))` (supported in `mixLc ∩ mixThin ε`, bounded by the
  sup of `θ` on the compact square), a.e. equality of the `mixDataC`- and `D`-kernels of `θ_ε`,
  continuity of both at `σ/t ≠ 0` (`continuousAt_totalKernel`), pointwise equality, the cutoff
  factor `= 1` at `σ/t ≤ ε/2` (eventually), and `mix_tendsto_totalKernel`. Hironaka
  **`exists_mixed_export_regression`** (`a` analytic on `univ`, `a 0 ≠ 0`): `∃ ε > 0, ∃ D :
  TruthChartsData 1 (z₀z₁) (mixThin ε), Nonempty (D.Phase (z₀z₁ a)) ∧ ∀ σ > 0, ∀ ψ …, Tendsto …` —
  the export (`W = ⊤`, `L = closedBall 0 (1/2)`, `hne` from `a 0 ≠ 0` at the point `(r/2, r/2)`)
  composed with the regression: the coefficient of the mixed truth is reproduced by whatever charts
  the resolution produces. Gotchas: `Continuous.mul` is unavailable on `ℝ≥0∞` (no `ContinuousMul`)
  — write the product as one `ofReal` of a real product; `simp` turns `|r/2|` into `|r|/2` (use
  `abs_of_pos hr`); `continuousOn_univ.mp` for continuity from analyticity on `univ`.
- `ProfileIntegrability.lean` (388acda; hironaka af5fdfe95): **the recession-cone criterion for the
  single-scale profile** (Astra round-14 item 4: "LP uniqueness ⇔ profile integrability" for the
  anchored unquotiented profile; under a strict truth constraint an integrable profile has one
  scaled coordinate by `not_integrable_envelope_of_two_scaled`). `singleScaleDomain ρ j` (`u_j >
  0`, `0 < u_i < ρ` otherwise), `singleScaleProfile ρ c j r κ = 1_{dom} ∏ u^r e^{-c ∏ u^κ}`,
  `singleScaleProfile_insertNth` (the split `(v, w)` form through `Fin.prod_univ_succAbove`),
  `integral_singleScale_inner` (`∫ v = (c ∏_{i≠j} w^κ)^{-(r_j+1)/κ_j} Γ((r_j+1)/κ_j)/κ_j ∏ w^r`,
  from `integral_rpow_mul_exp_neg_mul_rpow`), `integrable_singleScaleProfile` (transfer along
  `piFinSuccAbove`, `integrable_prod_iff'`, inner integrability by
  `integrableOn_rpow_mul_exp_neg_mul_rpow`, outer product of powers by `Integrable.fintype_prod`
  and `intervalIntegral.integrableOn_Ioo_rpow_iff`), `not_integrable_singleScaleProfile_of_le`
  (direction `−e_j`) and `_of_effective_le` (direction `κ_i e_j − κ_j e_i`), both through
  `not_integrable_of_recession_direction` with `Φ := c ∏ u^κ`, and
  **`integrable_singleScaleProfile_iff`**: `Integrable Ψ ↔ −1 < r_j ∧ ∀ i ≠ j, −1 < r_i − κ_i
  (r_j+1)/κ_j` (`c > 0`, `κ_j > 0`) — the ratio of the scaled coordinate strictly below every other
  ratio with `κ_i > 0` (the unique vertex optimum of `min ∑(r+1)α, α ≥ 0, κ·α ≥ δ`), coordinates
  with `κ_i ≤ 0` needing only their phase-improved effective exponent above `−1` (NOT `r_i > −1`:
  a negative `κ_i` makes the phase kill the small-`u_i` region). Gotchas: big-operator bodies
  swallow a trailing `* exp …` — parenthesise `(∏ i, …) *`; `Real.finsetProd_rpow` is stated
  `∏ f^r = (∏ f)^r` (use `←`); `intervalIntegral.integrableOn_Ioo_rpow_iff` needs
  `Mathlib.Analysis.SpecialFunctions.Integrability.Basic`; pass `(Φ := …)` to the recession theorem
  or `le_rfl` sticks on `Preorder ?m`; `-0 ≤ 0` after `split_ifs` is `simp`, not `le_rfl`.
- **Round-15 note-to-Lean audit** (consult bfeaf99, `gpt_responses/research_round15_*`): Astra ranked
  (1) a statement audit of the note against the inventory plus an end-to-end analytic-input
  theorem, (2) a certificate-coverage audit, (3) the boundary regression `T = xy`, `F = ax`,
  `θ = x^p y^q` (`t^p K_t(σ/t) → σ^q ∫_σ^∞ u^{p−q−1} e^{-au} du`), (4) constructive-recovery export
  or the smooth counterexample, (5) asymptotic-scale cleanup. Audit of the singular, identifiability
  and summary sections: every displayed claim of `lem:pencil`, `lem:sector`, `thm:singular`,
  `rem:singular-scope` (c), `prop:one-point`, constructive recovery (a) and the retained fragment
  of (b) carries a `\leanref`; the Morse–Bott and SQH-induction items are commented out in the note
  (not formalised, by design). The one untagged proof is the "No" answer to `q:proportional`
  (integration by parts + sector bound). It IS formalised: `NormalizedSingular.lean`
  (`normalized_families_force_germ_eq_at`, `normalized_families_force_eq_near`,
  `normalized_expectations_force_eq_near`; hypotheses: global `C^∞`, both losses `≥ 0`, the
  derivative difference vanishing at `p` because `p` is a minimum) and the test-class variants in
  `SingularSufficientTests`, `LocalizedSingular`, `PositiveWeightFamily`, `CutoffMonomialFamily`
  — but no `\leanref` points at it. Tag suggestion for the note (the main tex is not edited from
  here): `normalized_expectations_force_eq_near` at the end of the proof of `q:proportional`.
- `ProportionalFamilies.lean` (dc95fcb, 0910141; NOT mirrored to hironaka — it sits on the
  singular-pencil chain `Anchoring/Decay/Sector/LeadingPart/SingularPrep/SingularPoint`, outside the
  wall-atlas scope): the same theorem under the hypotheses of the unnormalised pencil theorem.
  **`proportional_families_force_eq_near`**: `L₁, L₂` continuous, `L₂ ≥ 0`, both analytic at each
  point of a set `W₀` of common zeros, ANY `C : ℝ → ℝ` with `SuperPoly (∫ φ e^{-tL₂} − C t ∫ φ
  e^{-tL₁})` for all `φ ∈ C_c^∞` ⇒ `L₁ = L₂` on an open neighbourhood of `W₀` (no global
  smoothness, no `L₁ ≥ 0`, no structure on `C`). Pieces: `SuperPoly.id_mul` / `of_id_mul`,
  `continuous/contDiff_mul_of_*On_tsupport_subset` (a test function glues regularity from an open
  set), `exists_least_nonzero_diagonal'` (no `g 0 = 0`: degree `0` with the vector `fun _ ↦ 3/2`,
  `[Nonempty ι]`; the empty case is trivial since then `v = 0`),
  `analytic_square_not_superpolynomial` (quantitative: `∫ ψ a² e^{-tK} ≥ vol(S) c² e^{-4C₀}
  t^{-m-d/2}` via `leading_part_scaled_set` + `sector_lower_bound_multi`),
  `integral_fderiv_mul_exp_neg` (IBP with `L` analytic on an open `V ⊇ tsupport φ`; Mathlib's
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` needs `f` differentiable only on
  `tsupport g`), `proportional_families_superPoly_derivative` (`t ∫ φ ∂_v(L₂−L₁) e^{-tL₂}` beyond
  all orders), `proportional_families_fderiv_apply_eventually_eq` (`ContDiffBump p` with radii
  `min R (ε/3)`, `2 min R (ε/3)` inside the analyticity ball, integrability shifted by
  `measurePreserving_add_left`), then `IsOpen.is_const_of_fderiv_eq_zero` on the ball. Gotchas:
  `HasCompactSupport.fderiv` has an implicit field — write `hφs.fderiv (𝕜 := ℝ)`, otherwise the
  error is a stuck `NontriviallyNormedField 𝕜✝` reported at an unrelated line; `open scoped
  ENNReal` together with `open scoped ContDiff` makes `∞` ambiguous (write `ENNReal`); `u • S` for
  sets needs `open scoped Pointwise`; `contDiff_mul_of_tsupport_subset` already exists in
  `SingularSmooth` (different hypotheses) — the umbrella build is the only place the clash shows.
  LESSON: grep the seabed (`normalized_`, `proportional`, the claim's key words) for an existing
  formalisation of a note claim BEFORE building from a missing `\leanref`; the tag audit is not an
  inventory audit.
- hironaka `TruthTheoremPhase.lean` (d7e5a9124, LOCAL): **the end-to-end theorem for a general
  analytic truth function** (Astra round-15 item 1b). `exists_truthChartsData_phaseData` = the
  export with phase data, `|S_i| = 1` (from `WallAtlasT.sign`) and the exact truth monomial on the
  closed balls (`repClamp_apply_truth`) — the record-level hypotheses of the Euclidean term
  theorems; then `truth_fibre_expectation` (+ `_dominant`, `_measure`, `_point`,
  `_certificate`): for `F, T` analytic near `0`, `T 0 = 0`, `F·T ≢ 0`, `F` continuous `≥ 0`, `L`
  compact in a connected `W`, the resolution gives `D : TruthChartsData m T (L ∩ {|T| ≤ ε})`,
  `P : D.Phase F`, and along `s = σ t^{-γ}` the fibre-kernel ratio `D.fibreRatio F ψ χ σ γ t`
  converges to the certified leading ratio (constants / limiting measure / point evaluation /
  leading measure of any `TermMeasureCertificate`). `truth_fibre_expectation_pushforward`
  packages, for the SAME `D`, the push-forward identity `∫_{L ∩ {|T| ≤ ε}} θ · η(T) = ∫ η ·
  D.totalKernel θ` (so the kernel whose ratio converges is the conditional density along `T = s`)
  with the certificate-form limit. Pure composition (no new analysis); for a general `T` the fibre
  identity of the coordinate case is replaced by the push-forward characterisation. The remaining
  gap to a hypothesis-free statement is the certificate: `α`/`TermMeasureCertificate` are still
  inputs (constructed by `ProfileIntegrableOf.of_vertex`, the tied/active/degenerate `TermData`
  constructors, from the exponent data of the phase record).
- `MixedTruthBoundary.lean` (1507293; hironaka c58c724af): **the critical-boundary regression**
  (Astra round-15 item 3): `T = z₀z₁`, `F = a z₁` (`a > 0`, vanishing on the whole axis `z₁ = 0`
  of the wall), `θ = z₀^q z₁^p ψ` with `ψ ≥ 0` continuous supported in the closed square.
  `mix_tendsto_totalKernel_boundary`: `t^p · K_t(σ/t) → σ^q ∫_{2σ}^∞ u^{p−q−1} e^{-au} ψ(σ/u, 0)
  du` — the mass sits on the whole segment `{z₁ = 0}` weighted by `ψ(σ/u, 0)` (fibre parametrised
  by `z₁ = u/t`, `z₀ = σ/u`; `e^{-t a z₁} = e^{-au}` is scale-free); with `ψ ≡ 1` on the square and
  `p = q + 1` the coefficient is `σ^q e^{-2aσ}/a` (lower limit `2σ` = box size `1/2`). Proof: the
  explicit kernel `∫_{2s}^{1/2} g(s/x, x) dx/x` (`mixData_totalKernel_toReal`), the substitution
  `x = u/t` (`intervalIntegral.integral_comp_div`, `eq_inv_mul_iff_mul_eq₀`), pointwise algebra
  (`Real.rpow_sub`, `rpow_natCast`, `div_pow`, `field_simp`), then dominated convergence on
  `(2σ, ∞)` with `F t = 1_{Iic (t/2)} · G t`, bound `C u^e e^{-au}`
  (`integrableOn_rpow_mul_exp_neg_mul_Ioi`: any real `e`, `c > 0` — case split `e ≤ 0` via
  `antitoneOn_rpow_Ioi_of_exponent_nonpos` + `exp_neg_integrableOn_Ioi`, `e > 0` via
  `integrableOn_rpow_mul_exp_neg_mul_rpow` at `p = 1`), and `integral_indicator` +
  `Measure.restrict_restrict` + `Ioi_inter_Iic` to identify `∫ F t` with the interval integral.
  `exported_mix_totalKernel_eq` factors the transport step of `exported_mix_tendsto_totalKernel`
  (any `θr ≥ 0` continuous supported in `mixLc`, `0 < s`, `|s| ≤ ε/2`);
  `exported_mix_tendsto_totalKernel_boundary` is the regression for every chart system over
  `mixThin ε`. Gotchas: `ring` cannot cancel `u^q * u⁻¹^q` — expand `(σ/u)^q` with `div_pow`
  BEFORE `field_simp` (which then closes the goal; a trailing `ring` errors "no goals"); the
  substitution identity must be stated as a pure substitution (`∫ f = t⁻¹ ∫ f(u/t)`) and the
  `t^p` bookkeeping done afterwards under `integral_const_mul`; `∞`/`ℝ≥0∞` need `open scoped
  ENNReal` (not opened in `Real`-heavy files). In a chained shell command a `$R` that came back
  EMPTY made `grep … $R` read stdin and hang the whole gate — check variables before use.
- `CertificateFromLP.lean` (7b22892; hironaka 11ad4063d): **certificates from the chart's LP**
  (Astra round-15 item 2, the coverage audit). Inventory: the profile certificate
  `ProfileIntegrableOf` had constructors from explicit dual conditions at the two nondegenerate
  shapes (`of_vertex`, `of_twoScaled`) and `CertificateLP` had the equivalences with unique LP
  minimality (`uniqueLPMin_vertex_iff`, `uniqueLPMin_twoScaled_iff`); the missing link was the
  composition. `UniqueLPMin.comp_equiv` (reindexing along `e : ι' ≃ ι`; `Equiv.sum_comp` with the
  summand `fun i ↦ f i * g i`, the reverse direction via `β' ∘ e.symm`),
  `ProfileIntegrableOf.of_uniqueLPMin_vertex` (all `κ > 0`, `α = (δ/κ_j) e_j`, `δ > 0`, strict
  truth, `UniqueLPMin (Qexp) (kappa) γ (phaseExp) (r + 1) α` ⇒ certificate),
  `ProfileIntegrableOf.of_uniqueLPMin_twoScaled` (two scaled coordinates, `Δ ≠ 0`, the dual
  decomposition `r_S + 1 = ηκ_S − θQ_S` as data, `UniqueLPMin` ⇒ certificate — `η, θ > 0` and the
  residual gaps come out of the equivalence), `TermData.vertexOfUniqueLPMin` /
  `twoScaledOfUniqueLPMin` (term data from LP uniqueness alone; feasibility = `hmin.1`). Verdict
  of the audit: at both nondegenerate shapes the certificate is read off the chart exponents; the
  degenerate shapes (a face of minimisers) are the log regimes with their own constructors
  (`TermData.tied/partial/activeTruth(Spectator)/activeTruthDegenerate`); what is NOT there is a
  decision procedure "given exponent data, which shape" (LP theory: existence of an optimal vertex
  of the polytope), so `truth_fibre_expectation` still takes `α` as input. Gotchas: theorems in
  `namespace TruthChartsData.Phase` with the section variable `(P)` explicit are called
  `TruthChartsData.Phase.foo P …`, never `P.ProfileIntegrableOf.foo` (the dot resolves into
  `Function.…`); `TermData.vertex` takes `P` explicitly too.
- **Astra round 16** (b4a9590, `gpt_responses/research_round16_*`): statement audit + ranking.
  (1a) `proportional_families_force_eq_near` is the right general form (no `L₁ ≥ 0`, nothing on
  `C`; do not strengthen to `C = 1`). (1b) `truth_fibre_expectation_pushforward` is correct but is
  "analytic input ⇒ charts + phase; a certificate ⇒ the limit", not an unconditional theorem;
  four checks: pointwise (not a.e.) kernel semantics for chart-independence, `toReal` of `∞`,
  integrability against the leading measure (finite measure ✓), and `0 < γ` for the note-facing
  reading. (3) **STATEMENT ERROR FOUND**: the landed boundary regression assumed `ψ` globally
  continuous AND supported in the closed square, which forces the trace `ψ(v, 0) = 0` (approach
  from `z₁ < 0`), so the theorem always had limit `0`. REPAIRED (0394638; hironaka mirror):
  `mixData_totalKernel_toReal'` (nonnegativity only on the positive quadrant `mixL'`, since the
  kernel only evaluates the observable there), `mix_tendsto_totalKernel_boundary` with NO support
  hypothesis and a unit `a(z)` continuous positive on the square (`isCompact.exists_isMinOn` for
  `a_min`; the DCT bound `C u^e e^{-a_min u}` on the indicator region, where the fibre points
  `(σ/u, u/t)` lie in the square), limit `σ^q ∫_{2σ}^∞ u^{p−q−1} e^{-u a(σ/u,0)} ψ(σ/u,0) du`, and
  the acceptance value `mix_tendsto_totalKernel_boundary_const` (`a` constant, `ψ ≡ 1`,
  `p = q+1`): `σ^q e^{-2aσ}/a` (`integral_comp_mul_left_Ioi (fun x ↦ exp (-x)) (2σ) ha` — pass
  the integrand explicitly, `?g (a * x)` is not a higher-order pattern — and
  `integral_exp_neg_Ioi`). The exported version is WITHDRAWN: a continuous observable supported
  in the region has zero boundary trace, and pointwise identification of two chart kernels at
  `s = σ/t` for an observable not supported in the region is not available (the a.e. equality
  from the push-forward identity does not control a sequence `s_n`). Classification: the boundary
  example has `κ = 0` on the unsolved coordinate (the phase `a z₁` depends only on the solved
  coordinate) with `phaseExp = 1 − γ·pExp = 0` at `γ = 1`: EVERY landed term constructor assumes
  `κ > 0` (`vertex`, `twoScaled`, `tied`, `partial`, `activeTruth*`, `activeTruthDegenerate`), so
  the regime is uncovered — a unique LP optimum with a positive-dimensional support (segment), not
  a face of minimisers. Ranking: (1) repair [DONE] then the boundary `TermData` (a new
  "solved-coordinate phase" term theorem: `κ ≡ 0`, `pExp > 0`, `γ = 1/pExp`, `Q > 0`; limit
  `∫_{box} W(x,0) x^r e^{-c a(x,0) ∏x^{-Q·pExp}} dx` = the segment integral), (2) a bounded
  constructive-recovery export — 1D: `L = x^{2k} + b x^{2k+r} + O(x^{2k+r+1})`, `j ≡ r mod 2`,
  `t^{r/2k}[t^{(j+1)/2k} ∫ χ x^j e^{-tL} − A_j] → −b A_{j+2k+r}` (recovers `b`), (3) LP existence
  + classification (`exists_optimal_vertex`, then `exists_termMeasureCertificate`; "vertex /
  two-scaled / face" are not disjoint; unique minimisers with dependent active constraints need
  coverage too), (4) a minimal scale API `S_{λ,m} = t^{-λ}(log t)^m` (positivity, product,
  dominance, ratio-of-scaled-limits), (5) the smooth singular counterexample
  (`L₂ = x^{2k} + e^{-1/x²}`) only if `prop:flat` does not already export it. In "What remains"
  keep three claims separate: certificate existence, pointwise chart-independence of fibre
  evaluations, constructive recovery from specified coefficients.
- `ZeroScaleCertificate.lean` (964befc; hironaka e511103e5): **the solved-coordinate phase regime**
  (Astra round-16 item 1, the boundary `TermData`). Observation: the boundary example `F = a z₁`
  on the `xy` chart has effective exponent `κ = k − Q·pExp/q = −1 < 0` on the unsolved coordinate
  and `phaseExp = 1 − γ·pExp = 0` at `γ = 1`, and the dominant-scale theorem `tendsto_modelKernel`
  applies verbatim at the scale `α = 0` (limiting domain = the whole box since `γ ≠ 0`, tied
  phase since `κ·0 = 0 = δ`, profile `B a₀(u) ∏u^κ`, face map the UNRESCALED branch point — the
  segment of the wall). Only the profile certificate was missing.
  `integrable_box_rpow_mul_exp_neg_prod` (`1_{(0,ρ)^k} ∏u^r e^{-c∏u^κ}` integrable when every
  `κ_j < 0` or (`κ_j = 0` and `r_j > −1`): choose `N` with `r_j − κ_j N > −1` via
  `exists_nat_gt (∑ max 0 ((−1−r_j)/(−κ_j)))`, bound `e^{-cP} ≤ N!/(cP)^N` from
  `Real.pow_div_factorial_le_exp _ hx N` (x explicit), `(cP)^N = c^N ∏ (u^κ)^N` by `mul_pow`,
  `Finset.prod_pow`, `Real.rpow_mul`, `rpow_natCast`, then `integrable_box_prod_rpow'`),
  `limitDomain_zero (hγ : γ ≠ 0)`, `integrable_envelope_of_zeroScale`,
  `integrable_envelope_mul_profile_of_zeroScale` (the vertex proofs with the box in place of
  `vertexDom`), `ProfileIntegrableOf.of_zeroScale (hσ) (hγ : γ ≠ 0) (hδ : phaseExp = 0) (hκ)`,
  `TermData.zeroScale` (= `TermData.vertex` at `α := fun _ _ _ ↦ 0`, feasibility `⟨le_rfl, γ ≥ 0,
  δ = 0⟩`; power `γ·pExp`, no log, measure `termMeasure … 0`). CAVEAT: the coordinatewise
  condition is only sufficient; with mixed signs (`κ = (−1, 1)`) `u₁^{r₁}u₂^{r₂}e^{-cu₂/u₁}` needs
  `r₁ + r₂ > −2` — the recession-cone criterion at `α = 0`, not formalised. Gotchas:
  `limitDomain_zero hγ ▸ hu` leaves `Fintype ?ι` stuck — `rwa [limitDomain_zero (ρ := ρ) (D := D)
  (q := q) (Q := Q) hγ] at hu`; `dsProfile_of_tied` wants `(a₀ := a₀) (B := B)` named when the
  tied hypothesis is a `have`; `MeasurableSet.pi countable_univ` needs `[Finite ι]` (state the box
  lemma with `omit [Fintype ι] in … [Finite ι]`). NEXT (Astra steps 2–4): a `Phase` record for
  `mixData` with `F = a z₁`, the leading functional of `TermData.zeroScale` on it, and its
  identification with `σ^q ∫_{2σ}^∞ u^{p−q−1} e^{-au} ψ(σ/u,0) du` (acceptance `σ^q e^{-2aσ}/a`).
- `MixedTruthBoundary.lean` (f8b86dd; hironaka 1f358ba6b): `mix_tendsto_totalKernel_boundary_pow`
  — the regression for the phase `a(z) z₁^n` along `s = σ/τ`, `t = τ^n`:
  `τ^p K_{τ^n}(σ/τ) → σ^q ∫_{2σ}^∞ u^{p−q−1} e^{-u^n a(σ/u,0)} ψ(σ/u,0) du` (substitution
  `x = u/τ`; `integrableOn_rpow_mul_exp_neg_mul_rpow_Ioi`/`_pow_Ioi` for the DCT bound); the linear
  theorem is the case `n = 1` (`simpa only [pow_one]`).
- **Acceptance test through the certificate route — analysis (not landed).** Astra's steps 2–4
  (boundary `TermData` on the mixed record, leading functional = segment integral, recover
  `σ^q e^{-2aσ}/a`) hit three API facts worth recording. (i) In `mixData` the solved coordinate is
  `z₀` (`k = 0`), so the phase `a z₁` is a phase on the UNSOLVED coordinate: `κ = 1`, `δ = 1`,
  scale `α = 1` with tied truth (`Q·α = γ = 1`) and tied phase — a single-scaled vertex with tied
  cut, covered by NO landed constructor (`of_vertex` needs strict truth, `of_twoScaled` two scaled
  coordinates); it would be the zero-scale regime only in the chart solving `z₁`. (ii) The term
  theorems require `F ≥ 0` GLOBALLY (`branchReal_le` bounds `e^{-tF} ≤ 1` at every chart point),
  and a phase record `F ∘ rep = a(u) ∏u^{kF}` with `kF = (0,1)` and a continuous nonvanishing unit
  forces `F` to change sign — the linear phase `a z₁` is not admissible as a `Phase`; the squared
  phase `a z₁²` (`γ = 1/2`) is. (iii) The term theorems take observables supported in `L'`
  (`hφL`); for `mixData` (`L' = (0,1/2]²`) such observables vanish on the segment, so the
  certified leading constant of `z₀^q z₁^p ψ` is `0` for every `p ≥ 1` — the `t^{-p}` decay is a
  SUBLEADING order invisible to the leading-term certificate; the certificate route sees only
  `p = 0`, and only for a record whose region contains the wall segment in its interior (the
  exported thin region, two branches `±`). So the honest acceptance test is: exported record over
  the full thin region, `F = a z₁²`, observable `z₀^q ψ`, tied-cut single-scaled certificate,
  and `tendsto_nhds_unique` against the by-hand limit; ~400 lines, deferred. Constructive recovery
  (round-16 item 2) is already covered in 1D (`Laplace/OneD/*Recovery*.lean`: `jet_recovery`,
  `polynomialJet_recovery`, `smooth_full_jet_recovery`, `base_recovery`, …); the scale API exists
  as `PowerLogDominance.powLog` (positivity, dominance).
- `Laplace/OneD/FlatInvisibleSingular.lean` (d0450d6; NOT mirrored — identifiability chain):
  **flat perturbations are invisible at singular minima** (Astra round-16 item 5).
  `singular_flat_perturbation_invisible`: `L₁` continuous with `c x^{2k} ≤ L₁` for `|x| ≤ δ₀` and
  `c₁ ≤ L₁` for `|x| > δ₀`, `f` continuous, `0 ≤ f ≤ M`, flat at `0` ⇒ `|∫ φ e^{-tL₁} − ∫ φ
  e^{-t(L₁+f)}| ≤ K/t^N` for all `N`; `_superpolynomial` (the `SuperPoly` form) and the witness
  `singular_flat_witness_superpolynomial k`: `x^{2k}` vs `x^{2k} + e^{-1/x²}`. Proof: pointwise
  `e^{-tL₁}(1 − e^{-tf})` with `0 ≤ 1 − e^{-tf} ≤ tf` (`Real.add_one_le_exp`), flatness at order
  `2k(N+1)` near `0` where `t C (x^{2k})^{N+1} e^{-tcx^{2k}} ≤ C (N+1)! c^{-(N+1)} t^{-N}`
  (`y^m e^{-y} ≤ m!` from `Real.pow_div_factorial_le_exp`), the floor `c₂ = min c₁ (c δ'^{2k})`
  away from `0` with `t e^{-c₂ t} ≤ t^{-N}` eventually (`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`),
  everything dominated by `1_{tsupport φ} · Mφ A / t^N` (`norm_integral_le_of_norm_le`,
  `integral_indicator_const`) — no closed-form integral. Gotchas: `rw [← Even.pow_abs h]` rewrites
  the FIRST power it sees — pass the base (`Even.pow_abs h x`); `set y := … with hy` then
  `clear_value y` before `field_simp; ring`, or the let-value is unfolded and `ring` faces
  `c * c^N * c⁻¹ * c⁻¹^N`; `norm_integral_le_of_norm_le` needs `(f := …)` when the bound is
  given by a `fun x ↦ by …` block.
- **Astra round 17** (d2c6626, `gpt_responses/research_round17_*`): (a) API weakening — do
  BOTH, separately: observables continuous on a neighbourhood of `closure L'` with no support
  condition (restrict the measure, not the observable; zero-extension is the WRONG replacement
  since it kills boundary traces; audit `tendsto_weightFn` = `1_{A_t} · J_t · θ(rep_t)` — the
  observable needs continuity at the limiting chart image, the indicator limit is a separate
  geometric argument), and phase nonnegativity only on `L'`/`rep_i(dom_i)` (enforced at the
  domain-indicated integrand; keep the global theorems as wrappers; note `modelG_nonneg` may not
  need `F ≥ 0` at all); the linear phase stays inadmissible on a two-branch region even then.
  (b) Pointwise chart-independence: NO theorem for arbitrary bounded continuous `θ` from
  "both regions contain a neighbourhood of the wall point" (`T = xy`, `θ = 1`, `L_R = (−R,R)²`:
  `K_R(s) = 2 log(R²/|s|)`, difference `4 log(R₂/R₁)` — REGION dependence); the sharp statement is
  "same localised push-forward measure + continuous versions ⇒ pointwise equal", and the cheap
  route is the truth cutoff (a.e. equality for `θ·χ(T)`, continuity at `s₀`, `χ(s₀) = 1`).
  (c) CORRECTION of my mixed-sign example: `u₁^{r₁}u₂^{r₂}e^{-cu₂/u₁}` on the box is integrable
  iff `r₂ > −1 ∧ r₁ + r₂ > −2` (fixed in the docstring, f7dd8a3 / hironaka 0aa3b50f3); the
  general single-monomial criterion: `b = r + 1`, `C = {v ≥ 0 | κ·v ≥ 0}`, integrable iff
  `b·v > 0` on `C ∖ 0`. (d) Ranking: (1) version-selection helper + cutoff pointwise theorem
  [DONE below], then support-free observables, then local `F ≥ 0`; (2) the tied-cut
  single-scaled certificate (state the tail lemma with `κ > 0` for "every `r`"; the outer
  domination is a separate hypothesis when the cut depends on unscaled coordinates); (3) the
  quadratic exported two-branch acceptance test (not a zero-valued supported one); (4) LP
  optimal-vertex existence (finite attained optimum on a pointed polyhedron has an optimal vertex;
  this does NOT give `UniqueLPMin` nor handle optimal faces); (5) the recession-cone criterion at
  `α = 0` after landing the corrected 2D example; (6) closure discipline: a certified zero
  coefficient is not a certified leading term; LP classification must cover tied constraints and
  optimal faces before the atlas is "exhaustive".
- `KernelPointwise.lean` (4a69762; hironaka e821d3562): **pointwise chart-independence through a
  truth cutoff** (round-17 item 1). `eqOn_of_ae_eq_restrict_of_continuousOn` (continuous
  versions of an a.e.-specified `ℝ≥0∞`-valued function agree on an open `U`; proof =
  `eq_of_ae_eq_of_continuousAt`'s Hausdorff argument with `Measure.measure_pos_of_mem_nhds` and
  `Measure.restrict_apply'`), `totalKernel_eq_of_truthCutoff` (`D₁ : … L₁`, `D₂ : … L₂`, same
  `T` continuous, `θ` bounded continuous with NO support condition, `χ ≤ 1` continuous with
  `χ(s₀) = 1`, `θ z ≠ 0 → χ(T z) ≠ 0 → z ∈ L₁ ∩ L₂`, `s₀ ≠ 0` ⇒ `D₁.totalKernel θ s₀ =
  D₂.totalKernel θ s₀`; products in `ℝ≥0∞` are continuous via `ENNReal.Tendsto.mul` with the
  `Or.inr` side conditions), `totalKernel_eq_of_thin` / `_eqOn_of_thin` (standard cutoff,
  `0 < |s₀| ≤ ε/2`, `θ` supported in `L₁ ∩ L₂` on `{|T| < ε}`). This is the general form of the
  transport step of the mixed regressions.
- `TiedCutCertificate.lean` (39456ee; hironaka 40b9b23e6): **the tied-cut single-scaled
  certificate** (round-17 item 2) — the regime of the boundary example in its own chart
  (`mixData` solves `z₀`; the phase `a z₁` has `κ₀ = 1`, `δ = 1`, scale `α₀ = 1`, tied truth
  `Q₀α₀ = γ` and tied phase). `limitDomain_single_subset`: for `Fin 1`, `α = (α₀)`, `α₀ > 0`,
  `Q₀ > 0`, `Q₀α₀ = γ`, the limiting domain lies in `{u₀ > (ρ/D)^{-q/Q₀}}` (the cut
  `D u₀^{-Q₀/q} < ρ` with the antitone rpow `antitoneOn_rpow_Ioi_of_exponent_nonpos` and
  `Real.rpow_mul` for `((ρ/D)^{-q/Q₀})^{-Q₀/q} = ρ/D`); `integrable_tiedDom_single`: the
  tied-cut profile `1_{limitDomain} u₀^r e^{-c₀ u₀^{κ₀}}` is integrable for EVERY `r` (`κ₀ > 0`;
  dominate by `1_{Ioi c} x^r e^{-c₀x^κ}` transported to `Fin 1 → ℝ` by
  `volume_preserving_funUnique`/`integrable_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ)`
  from `integrableOn_rpow_mul_exp_neg_mul_rpow_Ioi`), `ProfileIntegrableOf.of_tiedCut₁` (through
  `integrable_envelope_of_tiedDom` / `_mul_profile_of_tiedDom`, which only need
  `Integrable tiedDom` + tied phase), `TermData.tiedCut₁` (= `TermData.vertex` at
  `α := fun _ _ _ _ ↦ α₀`; feasibility from the two ties). Restricted to one unsolved coordinate
  on purpose (Astra: with further unscaled coordinates the cut depends on them and the lower end
  can reach `0`; the outer domination is a separate hypothesis). Gotcha: `positivity` cannot see
  `hc : 0 < ma/Ma`, `hB`, `P.ma_pos i` — give `mul_pos (mul_pos hc hB) (P.ma_pos i)` explicitly.
- `InteriorObservable.lean` (55079dc; hironaka 06504af86): **support-free observables, the interior form of
  the term chain** (round-17 item 1, stage 2). The support hypothesis `hφL : φ z ≠ 0 → z ∈ L'`
  enters the term chain ONLY in `tendsto_weightFn` (to put the moving branch point into
  `dom_i = closedBall ∩ rep_i⁻¹ L'` where `φ ≠ 0`). Replaced by the geometric hypothesis
  `hface : ∀ u ∈ limitDomain, D.rep i (D.limitBranchPt i ε b σ γ α u) ∈ interior L'` (the limiting
  face point in the interior of the region): the branch point converges to it, so it is eventually
  in the region by `Tendsto.eventually_mem (isOpen_interior.mem_nhds …)` — no `hS`, `hadm`,
  `htruth` are needed for this step. Chain: `tendsto_weightFn_of_interior`,
  `wallDominantScaleHyp_of_interior`, `tendsto_modelKernelOf_of_interior`,
  `tendsto_term`-equivalent inside it, `tendsto_termKernel_of_interior` (per admissible term
  `faceMap … u ∈ interior L'`), `tendsto_fibre_expectation_of_interior` (bounded continuous
  nonnegative `ψ, χ`, no support). The restriction to `L'` is internal to the kernel (the
  chart-domain indicator), never a property of the observable — the interface under which a
  boundary trace is visible to the certificate route. Not done: a support-free `TermData`
  structure (its `tendsto` field quantifies over supported observables) and the local `F ≥ 0`
  weakening. Gotcha: `⟨…, interior_subset hr⟩` against a `rep⁻¹ L'` membership makes Lean look
  for `interior (rep⁻¹ L')` — write `Set.mem_preimage.mpr (interior_subset hr)`; `faceMap` lives
  in `LimitingMeasure`, not `WallFibreExpectation`.
- `InteriorObservable.lean` amended (a8296ba; hironaka c8ed52aa6): the face hypothesis is now the
  DISJUNCTION `faceMap u ∈ interior L' ∨ φ =ᶠ[𝓝 (faceMap u)] 0`. Reason: the limiting domain is
  cut by the CHART radius `ρ` (`D ∏u^{-Q/q} < ρ`) while the region has its own radius (the
  density must vanish off `ball ρ` but be `1` on the region, so the region is strictly inside),
  and the face points in between carry no weight only because the observable is supported inside
  the region's radius — the interior-only hypothesis was unsatisfiable for exactly the records
  the acceptance test needs. In the second case the moving weight is eventually `0`
  (`Tendsto.eventually hvan` through `rep ∘ bridgePt`) and the limiting weight is `0`
  (`Filter.Eventually.self_of_nhds`). `tendsto_fibre_expectation_of_interior` takes one such
  hypothesis per observable (`hfaceψ`, `hfaceχ`).
- `ResponseMap.lean` + `MixtureRigidity.lean` (70e5ba5; NOT mirrored — outside the wall-atlas
  scope): **the response map over the data manifold, exact layer** (new direction, Astra round 18
  `gpt_responses/research_round18_v1.md`). With a prior density `π` and the base weight
  `baseWeight π L₀ t = e^{-tL₀} π`, the mixture posteriors `mixExp μ π L₀ Δ φ t s` (loss
  `pathLoss L₀ Δ s = L₀ + sΔ`) are the exponential tilts of `TiltInterpolation`
  (`mixExp_eq_tiltExp`, `mixExp_eq_base_ratio`); a loss-neutral base `L₀ = c` gives the temperature
  path (`priorExp_neutral`, `mixExp_neutral`, `priorZ_neutral`); `TiltData.hasDerivAt_mixExp`
  (`−t Cov_s(φ, Δ)`), `hasDerivAt_neg_mul_mixCov` (`t² κ₃`), `mixExp_antitone` (`⟨Δ⟩_s` descends),
  `hasDerivAt_mixLogZ` (`A' = −t⟨Δ⟩`), `hasDerivAt_deriv_mixLogZ` (`A'' = t² Var`),
  `mixLogZ_convexOn` / `mixFreeEnergy_concaveOn` (Mathlib `convexOn_univ_of_deriv2_nonneg`),
  `mixKL_eq` (KL of normalised densities = Bregman divergence of `A`; pointwise where `π > 0`);
  affine chart `affLoss L₀ R a = L₀ + ∑ aᵢ Rᵢ`, `dirLoss R v = ∑ vᵢ Rᵢ`,
  `TiltData.hasDerivAt_affExp` (differential `−t Cov_a(φ, R_v)`), `responseForm μ π L₀ R a t v u =
  t² Cov_a(R_v, R_u)` with `_comm`, `_add_left`, `_smul_left`, `_self_nonneg`,
  `hasDerivAt_deriv_mixLogZ_dir` (= D²A[v,v]), `sq_response_le` (Cauchy–Schwarz). Hypotheses:
  `TiltData μ (baseWeight π L₀ t) Δ M` from `tiltData_baseWeight_of_bounded` (integrable prior,
  bounded measurable losses); `TiltData.changeR` swaps the residual. `MixtureRigidity`:
  `attZ_family_sandwich` (`Z_G(Ct) ≤ Z_{L_a}(t) ≤ Z_G(ct)` for `aᵢ ∈ [c, C]`, `fᵢ ≥ 0`),
  `family_isTheta` (Θ-rigidity of `(λ, m)` on `[c, C]^ι`, `0 < c`; generalises `mixture_isTheta`).
  Gotchas: `open Real` makes `π` the constant — a prior named `π` needs `Real.exp` etc. spelled
  out and no `open Real`; a theorem named `Bdd.dirLoss` shadows `dirLoss` inside its own proof
  (`unfold dirLoss` fails) — name it `bdd_dirLoss`; a def after `variable {μ}` takes `μ`
  implicitly (`responseForm` re-binds `(μ : Measure X)` explicitly); `mixLoss` already exists in
  `TruthVariation` (hence `pathLoss`); `rw [← priorExp_neutral]` needs `(c := c)` (the constant is
  not determined by the RHS).
- `PathResponse.lean` (80098f5; NOT mirrored): **the master fluctuation–response identity along
  any `C¹` path of losses** and the e-geodesic data path. `PathData μ π L L' S ML M'` (prior
  data; `L s` measurable, `|L s x| ≤ ML`, `|L' s x| ≤ M'` and `HasDerivAt (L · x) (L' s x) s` for
  `s ∈ (−S, S)`); `PathData.hasDerivAt_num` (dominated differentiation on `Ioo (−S) S`),
  `PathData.hasDerivAt_priorExp` (`d/ds ⟨φ⟩_{L_s} = −t Cov_{L_s}(φ, L̇_s)`), `PathData.priorZ_pos`,
  `PathData.mixture` (the affine path is an instance on every interval, bound `M₀ + S MΔ`).
  E-geodesic: `eLoss ν q₀ a ℓ s w = tiltExp ν q₀ (ℓ w) a (−1) s` (`q_s ∝ e^{sa} q₀` IS the
  data-side tilt at temperature `−1`), `eLoss' = tiltCov ν q₀ (ℓ w) a a (−1) s`,
  `eLoss_hasDerivAt` (`L̇_s(w) = Cov_{q_s}(ℓ(w,·), a)`), bounds `Mℓ` and `2 Mℓ Ma`
  (`abs_eLoss_le`, `abs_eLoss'_le` via the new `TiltData.abs_tiltExp_le_of_bound`),
  `PathData.eGeodesic` (parameter-measurability of the data-averaged losses is a hypothesis),
  `hasDerivAt_priorExp_eGeodesic` (`d/ds ⟨φ⟩_{q_s} = −t Cov_{L_s}(φ, Cov_{q_s}(ℓ, a))`).
  Gotchas: `measurable_const` leaves the constant undetermined — pass `(f := fun _ ↦ (1 : ℝ))`
  with `(Mf := 1)`; `((hasDerivAt_id s).mul_const c).const_add b` lands in the `RCLike` module
  instance and `simpa` rejects it against `pathLoss` — prove `HasDerivAt (fun s ↦ s * c) c s` by
  `simpa using` first and finish with `.congr_deriv rfl`; the set `s` of
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` can be `Ioo (−S) S` with
  `Ioo_mem_nhds hs₀.1 hs₀.2`.
- `ResponseMetric.lean` (NOT mirrored): **the asymptotic response metric at a regular minimum**.
  `priorExp_volume_one` / `priorCov_volume_one` / `responseForm_volume_one` (prior density `1` on
  `ι → ℝ` = the seabed's `gibbsExpectation`/`gibbsCov`), `responseForm_asymptotic`:
  `|g_a(v,u)/t − ⟨∇R_v, P⁻¹ ∇R_u⟩| ≤ K/t` from `gibbsCov_first_order_rate_sharp_posDef` with
  `PotentialJetApprox (affLoss L₀ R a) (matCLM P)` and `ObservableJetApprox (dirLoss R ·) g`: the
  response metric grows linearly in `t` with limiting shape the pull-back of the inverse Hessian
  under the Jacobian of `q ↦ L_q` at the minimiser.
- `CoupledPhaseDiagram.lean` (NOT mirrored): **a phase diagram over the data manifold** — the
  coupled limit `s = t^{-σ}` of the mixture `w⁴ + s w²` (`w⁴` → `w⁴ + w²`, common minimiser).
  `quartZ t s = ∫ e^{-t(w⁴ + s w²)}`, `quartProfile c = ∫ e^{-(y⁴ + c y²)}`,
  `gaussProfile c = ∫ e^{-(y² + c y⁴)}`, `coupledExponent σ = max (1/4) ((1−σ)/2)`,
  `coupledConstant σ` (= `√π` for `σ < 1/2`, `quartProfile 1` at the tie, `quartProfile 0` beyond);
  scalings `quartZ_eq_quartProfile` (`Z = t^{-1/4} quartProfile (t^{1/2} s)`) and
  `quartZ_eq_gaussProfile` (`Z(t, t^{-σ}) = t^{-(1−σ)/2} gaussProfile (t^{2σ−1})`) by
  `Measure.integral_comp_mul_left`; DCT continuity `tendsto_quartProfile` / `tendsto_gaussProfile`
  (bounds `e^{-y⁴}`, `e^{-y²}`; `integrable_exp_neg_quartic` from the Gaussian via
  `y⁴ ≥ y² − 1/4`); regimes `coupled_quartic_regime`, `coupled_gaussian_regime`, `coupled_tie`;
  **`coupled_phase_diagram`**: `t^{λ(σ)} Z(t, t^{-σ}) → C(σ)`. The exponent is continuous
  piecewise affine with a slope change at the tie `σ = 1/2`; the constant jumps there; the
  crossover variable is `s t^{1/2}` (Astra round 18: ties change slopes, not values).
  Gotcha: after `norm_num` an exponent `1/2 − σ` may come back as `1/2 + −σ`; close with
  `rw [sub_eq_add_neg]`. `linear_combination (s * w²) * hh` closes the substitution identities
  once the rpow powers are rewritten by `h4`, `h2`.
- `ResponseNullspace.lean` (NOT mirrored): **the nullspace of the response form**.
  `TiltData.tiltCov_self_eq_tiltExp_sq` (`Var f = E[(f − E f)²]`),
  `TiltData.tiltCov_self_eq_zero_iff` (`Var f = 0 ↔ ∀ᵐ x, ν x ≠ 0 → f x = E f`, via
  `integral_eq_zero_iff_of_nonneg` and `Filter.eventually_congr`),
  `TiltData.responseForm_self_eq_zero_iff` (`t ≠ 0`: `g_a(v,v) = 0 ↔ ∀ᵐ x, π x ≠ 0 → R_v x =
  ⟨R_v⟩_a`): the invisible data directions are those whose loss is a.e. constant on the support
  of the prior; the response form is a metric on the identifiable quotient.
- `GibbsVariational.lean` (NOT mirrored; round-19 package 4a): **the Gibbs variational principle**.
  `relEnt μ ρ π = ∫ ρ log(ρ/π)`, `gibbsDensity μ π L t = e^{-tL}π/Z`, `integral_gibbsDensity`,
  `log_div_gibbsDensity` (pointwise `log(ρ/ρ_t) = log(ρ/π) + tL + log Z` where `ρ, π ≠ 0`),
  **`gibbs_gap`** (`t E_ρL + KL(ρ‖π) = −log Z + KL(ρ‖ρ_t)` for a probability density `ρ` with
  `ρ ≠ 0 → π ≠ 0`), `relEnt_gibbsDensity_nonneg` (Gibbs' inequality via
  `Real.log_le_sub_one_of_pos`; pointwise `ρ − ρ_t ≤ ρ log(ρ/ρ_t)`), **`gibbs_variational`**
  (`−log Z ≤ t E_ρ L + KL(ρ‖π)`), `gibbs_variational_eq` (equality at `ρ_t`). Integrability of
  `ρL`, `ρ log(ρ/π)` are hypotheses.
- `CoefficientResponse.lean` (NOT mirrored; round-19 package 1, first step): **the coefficient-
  response calculus**. Face formula model `faceCoef ν φ h lam a = ∫ φ U_a^{-λ} dν` with the
  affine unit `faceUnit h a = ∑ aᵢ hᵢ` (principalised mixture), `facePosterior = faceCoef φ /
  faceCoef 1`, `faceCov`; `FaceData ν h a c Mh` (finite face measure, bounded measurable `hᵢ`,
  `U_a ≥ c > 0`), `radius`, `unit_perturbed_ge` (`U_{a+εv} ≥ c/2` for `|ε| ≤ radius`),
  **`FaceData.hasDerivAt_faceCoef`** (`d/dε μ_{a+εv}(φ) = −λ ∫ φ U_a^{-λ-1} R_v dν`; dominated
  differentiation on a closed ball, `HasDerivAt.rpow_const`), **`FaceData.hasDerivAt_facePosterior`**
  (the SINGULAR fluctuation–response identity: `d/dε [μ(φ)/μ(1)] = −λ Cov_{ν_a}(φ, R_v/U_a)`,
  `Real.rpow_sub_one` + quotient rule). Gotchas: `(hd.measurable_faceUnit _).pow_const _` with
  the weight left as `_` makes the unifier unfold `faceUnit` (whnf timeout at the theorem's first
  line — bisected with truncated scratch copies); pass `(a + ε • v)` and `(-lam)` explicitly, and
  annotate `∀ ε : ℝ` (otherwise `HSMul ?m (ι → ℝ)` is stuck); `gcongr` on a product of four
  factors leaves a positivity goal in place of the intended one — spell `mul_le_mul` out.
- `ValuationLP.lean` (NOT mirrored; round-19 package 2, first step): **the valuation LP**.
  `offsetFeasible α σ = {r ≥ 0 : α_j·r + σ_j ≥ 1}`, `offsetLP α b σ = sInf (b·r '' offsetFeasible)`
  (named to avoid the clash with `LPExponent.lpValue`, which broke the umbrella build);
  `offsetFeasible_convex_combo` (joint affinity), `offsetLP_le`/`le_offsetLP`,
  **`offsetLP_antitone`**, **`offsetLP_convexOn`** (no LP duality: the value function of a jointly
  affine parametric LP is convex — a two-step `le_offsetLP` argument dividing by the positive
  weights, with the degenerate weights handled by `subst` + `simp`), **`offsetLP_quartic`**
  (`d = 1`, `α = (4,2)`, `b = 1`, `σ = (0, σ)`: image set `= Ici (coupledExponent σ)`, `csInf_Ici`)
  — the LP value equals the analytic exponent of `CoupledPhaseDiagram`. Not done: piecewise
  affinity via the dual polytope's vertices, and log multiplicity = dim of the optimal face.
- `PathHessian.lean` (NOT mirrored; round-19 package 4b) + `CoupledPhaseDiagram` wall-profile
  section (package 3 first step): `TiltData.abs_tiltCov_le_of_bound` (`|Cov(f,g)| ≤ 2 Mf Mg`),
  `PathData2` (`: Prop extends PathData`, new syntax order), `PathData.hasDerivAt_num'`
  (`d/ds ∫ f_s e^{-tL_s} π = ∫ (ḟ_s − t f_s L̇_s) e^{-tL_s} π`, s-dependent observable),
  `PathData.hasDerivAt_pathFreeEnergy` (`F' = t E_s[L̇]`), `PathData2.hasDerivAt_pathMean`
  (`d/ds E_s[L̇] = E_s[L̈] − t Var_s(L̇)`), **`PathData2.hasDerivAt_deriv_pathFreeEnergy`**
  (`F'' = t E[L̈] − t² Var(L̇)`), **`PathData2.hasDerivAt_neg_mul_pathCov`** (second derivative of
  the response along any C² path: `t² κ₃(φ,L̇,L̇) − t Cov(φ, L̈)`), `eLoss''` (= `κ₃^{q_s}(ℓ,a,a)`),
  `eLoss'_hasDerivAt`, `abs_eLoss''_le` (`6 Mℓ Ma²`), `PathData2.eGeodesic`. Wall profile:
  `quartZ_wall_variable` (`t^{1/4} Z(t, c/√t) = quartProfile c` EXACTLY), `quartProfile_eq_gaussProfile`
  (`quartProfile c = c^{-1/2} gaussProfile (c^{-2})`), `tendsto_sqrt_mul_quartProfile`
  (`√c · quartProfile c → √π`: the wall profile matches the Gaussian regime). Gotchas: `hfm.mul hgm`
  is Pi-form — type the measurability of a product with a `have … : Measurable fun x ↦ f x * g x`
  before passing it where the observable is inferred from it (else goals show `|(f * g) x|` and
  `integral_sub` patterns fail); `rw [Real.abs_exp]` rewrites all copies at once.
- `ThermoLength.lean` (NOT mirrored; round-19 package 4c, exact part): `fisherSpeed μ π L L' t s =
  t² Var_s(L̇_s)`, `PathData.tiltData_base` (the path's base weight as a `TiltData` with zero
  residual), `PathData.abs_deriv_le_sqrt_fisherSpeed` (`|t Cov_s(φ, L̇)| ≤ √Var_s(φ) √g_s`),
  **`PathData.abs_priorExp_sub_le`** (`|⟨φ⟩_{s₁} − ⟨φ⟩_{s₀}| ≤ C (s₁ − s₀)` with `C ≥ √Var √g` on
  the segment; mean value `norm_image_sub_le_of_norm_deriv_le_segment'` with the bound on `Ico`).
  Not done: the `√t` degeneration of the length at regular points (needs uniform Laplace along
  the path).
- `TraceMixtureResponse.lean` (NOT mirrored; round-19 package 1, the bridge to the atlas):
  `traceFaceMeasure ρ e = (volume.restrict (Ioo 0 ρ)).withDensity (ofReal u^e)` (finite for
  `e > −1`, `integrableOn_rpow_Ioo` via `intervalIntegrable_rpow'`; `integral_traceFaceMeasure`
  via `integral_withDensity_eq_integral_toReal_smul₀` with `(f := …)` named — otherwise `f` is
  inferred as an `ℝ≥0∞`-rpow; `traceFaceMeasure_univ_pos` via `lintegral_pos_iff_support` +
  `Measure.restrict_apply'`), **`trace_integral_eq_faceCoef`** (`∫_0^ρ u^e w U_a^{-β} = faceCoef`),
  `faceData_trace`, `faceCoef_one_trace_pos` (`integral_pos_iff_support_of_nonneg_ae`),
  **`tendsto_modelKernel_trace_mixture`** (the trace-regime constant of a mixture with affine
  unit `U_a = ∑ aᵢ hᵢ` is `C₀ · faceCoef (traceFaceMeasure ρ (qη−1)) w h β a`; the implicit `A`,
  `p` of `tendsto_modelKernel_trace` must be passed), **`hasDerivAt_traceConstant`**,
  **`hasDerivAt_tracePosterior`** (singular fluctuation–response on the truth segment:
  `−β Cov_{ν_a}(w, R_v/U_a)`). First instance of the coefficient-response calculus on an actual
  atlas term. Remaining for the full representation theorem: the general `TermData` term (the
  unit sits inside `dsProfile`'s exponential; integrating the scaled coordinate produces the
  `Γ(β) (B a)^{-β}` factor), spectators, and the degenerate regimes.
- `WallLogMultiplicity.lean` (NOT mirrored; Astra round-19 warning example): `wallZ t s =
  ∫₀¹∫₀¹ e^{-tx(y+s)}`, `expInt a = ∫₀^a (1−e^{-u})/u`, `wallRem t s = ∫_{ts}^{t(1+s)} e^{-u}/u`;
  `integral_exp_inner`, `mul_wallZ_eq_expInt` (`tZ = G(t(1+s)) − G(ts)`; the inner formula carries
  a `1/t` — the first draft lost it), `integral_one_sub_exp_div_eq_log` (`integral_one_div`),
  **`wallZ_eq`** (`tZ = log((1+s)/s) − wallRem`), `wallRem_nonneg`, `wallRem_le`
  (`≤ e^{-ts}/(ts)`), `tendsto_wallRem`, **`tendsto_wallZ_wall`** (`σ = 0`: `tZ → log 2`),
  **`tendsto_wallZ_fixed`** (`0 < σ < 1`: `tZ/log t → σ`), **`tendsto_wallZ_moving`**
  (`s = e^{-√log t}`: `tZ/√log t → 1`) — the log multiplicity interpolates across the wall; the
  wall variable is `σ log t`. Gotchas: `integral_const_mul`/`integral_div`/`integral_congr_ae` are
  ambiguous between `intervalIntegral` and `MeasureTheory` under both opens — qualify;
  `IntervalIntegrable.comp_mul_left` takes `{c}` implicit with `finiteness` autoParams — use
  `(c := a)`; `simp_rw [e]` with `e : ∀ y, …` also rewrites the `y = 1` instance on the RHS;
  `Ι` needs `open scoped Interval`.
- `TermScoreResponse.lean` (NOT mirrored; round-20 package 1): **the score response of an
  exponential-form term** `dμ_a = H e^{-B U_a(u∞) P} dm`: `termCoef m H P uw h B φ a`,
  `termScore P uw h B v = B R_v(u∞) P`, `termPosterior`, `termCov`, `ScoreData` (nonneg
  measurable `H, P`, measurable face map `uw`, bounded `hᵢ`, `B > 0`, `U_a ≥ c > 0`),
  `envelope φ = |φ| H (1 + P) e^{-B(c/2)P}`; **`ScoreData.hasDerivAt_termCoef`**
  (`D_v ∫φ dμ_a = −∫ φ S_v dμ_a`, dominated differentiation with the polynomial factor absorbed
  by halving the decay), **`ScoreData.hasDerivAt_termPosterior`** (`−Cov_{μ̄_a}(φ, S_v)`). The unit
  bounds are borrowed from `FaceData` on the zero measure (`toFaceData`). Instantiation on an
  actual `termDensity` (unit = a field of `Phase`) still needs a Phase family affine in the
  weight.
- `GammaFaceMarginal.lean` (NOT mirrored; round-20 package 2): `integral_rpow_mul_exp_neg_mul`
  (`∫₀^∞ z^{β−1}e^{-bz} = b^{-β}Γ(β)` from `integral_rpow_mul_exp_neg_mul_rpow` at `p = 1`),
  `integrableOn_rpow_mul_exp_neg_mul` (arguments of the Mathlib lemma are `(hs) (hp) (hb)` with
  `s` the exponent), **`gamma_score`** (`E[B R z | u] = β R/U`), `prodMeasure ν = ν.prod
  (volume.restrict (Ioi 0))`, `ae_snd_pos` (`Measure.ae_prod_mem_iff_ae_ae_mem` with the set
  given), **`termCoef_prod_eq_faceCoef`** (Fubini `integral_prod` [needs `SFinite ν`]: the
  product-domain term integral is `Γ(β)B^{-β} · faceCoef (φ w)`), **`termScoreCoef_prod_eq`** (the
  score-weighted term integral is `Γ(β)B^{-β} · β ∫ φ w U^{-β-1} R_v`) — the exponential score
  `B R_v z` marginalises to the face score `β R_v/U_a`, so the two singular fluctuation–response
  identities agree. Gotchas: `Integrable.mono'` bounds need the integrable majorant NONNEGATIVE
  (use `hint.norm`); for a.e. positivity of the second coordinate under a product with a
  restricted factor use `ae_prod_mem_iff_ae_ae_mem`; `simp only [abs_mul, …]` beats a hand `rw`
  chain for nested absolute values, and start the `calc` with `_`.
- `AssembledResponse.lean` (NOT mirrored; Astra round-20 "single most valuable"): `assembledCoef m
  H P uw h B φ a = ∑_k termCoef_k`, `assembledPosterior`, `assembledScoreCoef` (piecewise score
  `S_v|_k = B_k R_v(u∞_k) P_k`); **`hasDerivAt_assembledCoef`** (`HasDerivAt.fun_sum` over the
  terms), **`hasDerivAt_assembledPosterior`** (`D_v⟨φ⟩_a = −(∑_k∫φS_k dμ_k − ⟨φ⟩_a ∑_k∫S_k dμ_k)/∑_k
  μ_k(X)` = `−Cov_{μ̄_a}(φ, S_v)` on the disjoint union, relative masses of the chart terms
  included). Terms live on a common base `(X, m)` with a common unit family `h`.
- `HigherResponse.lean` (NOT mirrored; round-20 package 3, unnormalised layer):
  `TiltData.bdd_mul_pow`, `TiltData.iteratedDeriv_const_mul_tiltNum` (induction with the constant
  carried, avoiding `iteratedDeriv_const_mul`'s `ContDiffAt` hypothesis), **`iteratedDeriv_tiltNum`**
  (`(d/du)^n ∫ f e^{-tuR}ν = (−t)^n ∫ f R^n e^{-tuR} ν`), `mixNum_eq_tiltNum`,
  **`iteratedDeriv_mixNum`**, **`iteratedDeriv_priorZ_pathLoss`** (`Z^{(n)} = (−t)^n ∫ Δ^n e^{-tL_s}π`),
  `priorExp_const` (neutral base ⇒ posterior = prior: the map starts at the prior mean).
- `WallSecondCrossover.lean` (NOT mirrored; Astra round-20 correction): `expIntE1 c = ∫_c^∞ e^{-u}/u`,
  `integrableOn_exp_neg_div_Ioi` (from `exp_neg_integrableOn_Ioi`), **`tendsto_wallZ_second`**
  (`tZ(t, c/t) − log t → −log c − E₁(c)`; `intervalIntegral_tendsto_integral_Ioi` with
  `b t = t + c`): the log coefficient saturates at `1` for `σ ≥ 1`, i.e. the coupled-limit log
  multiplicity is `min(σ, 1)` with a second wall at `σ = 1`.
- `ThermoLengthIntegral.lean` (NOT mirrored; Astra round-20 side landing): `PathData2.differentiableAt_priorExp_sq`
  (via `hasDerivAt_num'` with `f = L'L'`), `continuousAt_fisherSpeed`, `continuousAt_priorCov_self`,
  **`abs_priorExp_sub_le_integral`** (`|⟨φ⟩_{s₁} − ⟨φ⟩_{s₀}| ≤ ∫_{s₀}^{s₁} √Var_s(φ) √g_s ds`; FTC
  `integral_eq_sub_of_hasDerivAt` + `norm_integral_le_integral_norm` + `integral_mono_on`; the C²
  hypothesis gives continuity of the speed). Gotcha: `ContinuousOn.intervalIntegrable` leaves the
  measure stuck unless the result is ascribed with `volume`.
- `GibbsUniqueness.lean` (NOT mirrored): `defect_eq_zero_iff` (pointwise, via
  `Real.log_lt_sub_one_of_pos`), **`ae_eq_gibbsDensity_of_relEnt_eq_zero`** (`KL(ρ‖ρ_t) = 0 ⇒ ρ = ρ_t`
  a.e., through `integral_eq_zero_iff_of_nonneg` on the nonnegative defect),
  **`ae_eq_gibbsDensity_of_variational_eq`** (the variational bound is attained only at the
  posterior). Gotcha: `Integrable.sub` is Pi-form — ascribe the lambda before `integral_sub`.
- `MixtureSeries.lean` (NOT mirrored; round-20 package 5, concrete form): `hasSum_exp_series`
  (`Real.exp_eq_exp_ℝ` + `NormedSpace.expSeries_div_hasSum_exp x`), **`TiltData.hasSum_tiltNum`**
  (`∫ f e^{-tuR}ν = ∑ (−tu)^n/n! ∫ f R^n ν` for every `u`, by
  `hasSum_integral_of_dominated_convergence` with bound `(|tu|M)^n/n! · Mf ν` and
  `Real.summable_pow_div_factorial`), **`hasSum_mixNum`**, **`hasSum_priorZ_pathLoss`** (the
  partition function along the mixture path is the exponential generating function of the base
  moments of `Δ`: entire in the weight).
- `TwoMonomialWall.lean` (NOT mirrored; round-21 package 3, first step): `twoZ p q t s =
  ∫₀^∞ e^{-t(w^p + s w^q)}`, `twoProfile p q c = ∫₀^∞ e^{-(y^p + c y^q)}`, `twoProfileQ`,
  `twoExponent = max(1/p, (1−σ)/q)`; `integrableOn_exp_neg_rpow`; scalings `twoZ_eq_twoProfile`
  (`Z = t^{-1/p} F(t^{1−q/p} s)`) and `twoZ_eq_twoProfileQ` (`Z = (ts)^{-1/q} F_q(t (ts)^{-p/q})`)
  by `integral_comp_mul_left_Ioi`; **`twoZ_wall_variable`** (exact profile in `c = s t^{1−q/p}`),
  **`two_p_regime`**, **`two_q_regime`** (DCT). The general real-exponent two-monomial wall.
- `ScoreBridge.lean` (NOT mirrored; round-21 package 1, interface): **`tendsto_scaled_cov_of_four`**
  (quotient-limit algebra: four normalised limits ⇒ the scaled covariance converges),
  **`tendsto_response_of_four`** (for Gibbs laws `e^{-tL}π` with physical score `Q_t = t D_vL`:
  `−t Cov_t(φ_t, D_vL) → −Cov_{limit}`), `regular_scaled_integral`, **`regular_scaled_cov_eq`**
  (the regular model `L_a = a w^p` on `(0,∞)`: the bridge is an IDENTITY under `y = t^{1/p} w`,
  the physical score `t v w^p` is exactly `v y^p`). Gotcha: `field_simp` rewrites inside
  integrands — `set` the four integrals and `clear_value` before `field_simp`.
- `ProfileResponse.lean` (NOT mirrored; round-21 package 3, response part; NB the name `WallResponse`
  was already taken by the 2026-09-22 low-resolution wall module): `profileNum p q ψ c =
  ∫₀^∞ ψ e^{-(y^p + c y^q)}`, `profilePosterior`; `integrableOn_rpow_mul_exp_neg_rpow_nonneg`;
  **`hasDerivAt_profileNum`** (`d/dc N_ψ = −∫ ψ y^q e^{…}` for `c > 0`; dominated differentiation
  with the UNBOUNDED score `y^q` dominated by the profile decay `e^{-y^p}`),
  **`hasDerivAt_profilePosterior`** (`∂_c⟨ψ⟩_c = −Cov_c(ψ, y^q)`), `wall_numerator_scaled`,
  **`wall_posterior_eq_profile`** (the finite-`t` posterior of `ψ(t^{1/p} w)` at `s = c t^{-σ*}` IS
  the profile law, for every `t`), **`hasDerivAt_wall_posterior`** (the renormalised wall response
  `∂_c` at finite `t` equals the profile response). Gotchas: `rw [show q/p = 1 + -(1 - q/p) …]`
  rewrites the `q/p` inside `-(1 - q/p)` too — prove the exponent identity by a `calc` through
  `Real.rpow_add`; a new module name must be grepped against `Laplace/Multi/` first — creating a
  file with an existing name silently OVERWRITES the landed module (git shows ` M`, not `??`).
- `ProfileFamily.lean` (NOT mirrored; the wall profile as an EXPONENTIAL FAMILY in the wall variable):
  `integrableOn_profile` (polynomial-growth observables), **`hasDerivAt_profileNum_poly`** /
  `hasDerivAt_profilePosterior_poly` (response for `|ψ| ≤ M y^r`), **`iteratedDeriv_profileNum`**
  (`∂_c^n N_ψ = (−1)^n N_{ψ y^{nq}}`, all orders, by induction with `EventuallyEq.deriv_eq`),
  `profileNum_one_pos`, `profileLogZ := log Z(c)`, **`profile_expFamily`**
  (`ρ_c = e^{-y^p} exp(−c y^q − A(c))`), `hasDerivAt_profileLogZ` (`A' = −⟨y^q⟩`),
  `profileVar_eq/nonneg`, **`profileVar_pos`** (`q > 0`; support argument beyond `max(m^{1/q},0)+1`),
  `hasDerivAt_deriv_profileLogZ` (`A'' = Var_c(y^q)`), **`profileLogZ_convexOn`** (on `Ioi 0`, via
  `convexOn_of_deriv2_nonneg` + `interior_Ioi` + `change 0 ≤ deriv (deriv _) c`),
  **`profileMean_strictAntiOn`** / `profileMean_injOn` (the mean map `c ↦ ⟨y^q⟩_c` is strictly
  decreasing: the wall is traversed monotonically by one sufficient statistic).
- `ThermoLengthAsymptotic.lean` (NOT mirrored; THE RLCT AS THE GROWTH RATE OF THERMODYNAMIC LENGTH):
  `thermoLength μ π L L' t := ∫₀¹ √fisherSpeed`, **`fisherSpeed_neutral`** (on the neutral line
  `g = t² Var_{ts}(Δ)`), **`thermoLength_neutral_eq`** (`ℓ(t) = ∫₀^t √Var_u(Δ) du`, substitution
  `u = ts`), **`tendsto_intervalIntegral_div_log`** (Cesàro: `u g(u) → c ⇒ (∫₀^t g)/log t → c`;
  ε/4 bookkeeping with threshold `max U₀ (exp(4A/ε + 1))`), **`thermoLength_neutral_div_log_tendsto`**
  (`u² Var_u(Δ) → λ ⇒ ℓ(t)/log t → √λ`), `continuous_neutral_var` (from `PathData.mixture` at
  `S = |u|+1` and `PathData2.continuousAt_priorCov_self`), `thermoLength_neutral_div_log_tendsto'`
  (bounded contrast, only the fluctuation law assumed). Gotchas: `intervalIntegrable_inv` lives in
  `intervalIntegral`; `continuousAt_priorCov_self` is `PathData2.…` although stated for `PathData`.
- `IntegratedSusceptibility.lean` (NOT mirrored; Astra round-22 bundle items 2+3):
  `sq_intervalIntegral_le_intervalIntegral_sq` (Cauchy–Schwarz on `[0,1]` via `Var ≥ 0`),
  **`TiltData.integrated_susceptibility`** (`∫₀¹ t Var_{t,s}(Δ) ds = ⟨Δ⟩_{t,0} − ⟨Δ⟩_{t,1}`, FTC on the
  master identity), `fisherSpeed_mixture` (rfl), `TiltData.continuous_mixCov`,
  **`TiltData.thermoLength_sq_le`** (`ℓ² ≤ t(⟨Δ⟩_0 − ⟨Δ⟩_1)`), **`TiltData.thermoLength_le_sqrt_osc`**
  (`ℓ ≤ √(2Mt)`: the `√t` scale), **`TiltData.mixCov_self_pos`** (non-degenerate contrast ⇒ `Var > 0`
  everywhere, from the nullspace theorem), **`TiltData.mixExp_strictAnti`** / `mixExp_injective`
  (strict identifiability along the line). Needs `import ResponseNullspace` and `[Nonempty X]`.
- `AffineConvexity.lean` (NOT mirrored; round-22 item 1): `affLogZ μ π L₀ R t a = log Z_t(L₀ + ∑ aᵢRᵢ)`,
  `affFreeEnergy = −A/t`, `affLogZ_line` (line restriction = `mixLogZ`), `bdd_affLoss`, `tiltData_aff`,
  **`affLogZ_convexOn`** (`ConvexOn ℝ univ`, by restriction to mixture lines through `affLoss_add_smul`;
  the segment point `a•x + b•y = x + b•(y−x)` by `module`), **`affFreeEnergy_concaveOn`**,
  **`TiltData.hasDerivAt_affLogZ_dir`** (`D_v A = −t⟨R_v⟩_a`), **`TiltData.hasDerivAt_deriv_affLogZ_dir`**
  (`D_v² A = responseForm a v v`). Gotcha: `tiltData_baseWeight_of_bounded` takes `μ` EXPLICITLY;
  `omit [MeasurableSpace X]` is refused when the statement mentions `μ`.
- `WallWindowLength.lean` (NOT mirrored; round-22 item 5): `priorExp_const_mul`, `priorExp_congr_ae`,
  `twoMonoPath p q a w = w^p + a w^q`, `twoMonoVel q _ w = w^q` (NB `wallPath` is taken by `WallCutoff`),
  `scaled_rpow` (`(t^{1/p} w)^q = t^{q/p} w^q`), `priorExp_twoMonoPath_score(_sq)` (window moments
  `= t^{-q/p}⟨y^q⟩_c`, `t^{-2q/p}⟨y^q y^q⟩_c`), **`fisherSpeed_twoMonoPath`**
  (`g_t(c t^{-σ*}) = t^{2σ*} Var_c(y^q)`), **`wall_window_length`**
  (`∫_{c₀t^{-σ*}}^{c₁t^{-σ*}} √g_t da = ∫_{c₀}^{c₁} √Var_c(y^q) dc`, exact for every `t`; substitution via
  `intervalIntegral.integral_comp_mul_right`). Gotcha: an unapplied `twoMonoVel q a` inside `priorExp`
  is not unfolded by `simp only [twoMonoVel]` — `rw [show twoMonoVel q a = fun w ↦ w^q from rfl]`.
- `SqrtIntegralConvergence.lean` (NOT mirrored; round-22 item 4): `sqrt_sub_min_le` (`√y − min(√y,M) ≤ y/M`),
  `sqrt_le_one_add`, `integrable_sqrt_of_integrable`, **`tendsto_integral_sqrt_of_mass_bound`** (finite
  measure, countably generated filter, eventual hypotheses `Integrable`, `≥ 0`, `∫ ≤ C`; a.e. limit `f`
  with `∫ f ≤ C` ⇒ `∫√F_n → ∫√f`; truncation at `M = 4(|C|+1)/ε` + dominated convergence, no Vitali),
  **`thermoLength_div_sqrt_tendsto`** (bounded contrast, `t Var_{t,s}(Δ) → κ(s)` a.e. on `(0,1]` with
  `κ` integrable, `∫κ ≤ 2M` ⇒ `ℓ(t)/√t → ∫₀¹ √κ`; mass bound from `integrated_susceptibility`).
  Gotchas: `IsFiniteMeasure (volume.restrict (Ioc 0 1))` via `isFiniteMeasure_restrict.mpr
  measure_Ioc_lt_top.ne` (use `have`, not `haveI`); Bochner `integral_mono` is a `lemma` taking
  `(hf) (hg) (h : f ≤ g)`; `div_div_eq_mul_div : a/(b/c) = a*c/b`.
- `GaussianShapeMetric.lean` (NOT mirrored; Astra round-22 "order-one shape metric", EXACT for Gaussians):
  `gaussLoss H = ½ wᵀHw`, `priorExp_gaussLoss_eq_tilted` (flat-prior posterior of a Gaussian loss at
  temperature `t` = tilted Gaussian of precision `tH`, zero tilt), `isHermitian_sum_smul`,
  **`sq_mul_priorCov_gaussLoss`** (`t² Var_t(½wᵀBw) = ½ tr((BH⁻¹)²)` for EVERY `t > 0`, from
  `Laplace.Sampler.tiltedVar_quadForm` with `tiltMean _ 0 = 0` and `(t•H)⁻¹ = t⁻¹•H⁻¹` proved inline —
  the seabed's `smul_inv_of_isUnit` is `Fin d`-specific and produced a universe-mismatch whnf timeout),
  `affLoss_gaussLoss`, `dirLoss_gaussLoss`, **`responseForm_gaussian_self`** (`g_a(v,v) = ½ tr((B_v H_a⁻¹)²)`:
  the response form of a Gaussian family is Fisher–Rao on covariances, `t`-independent),
  **`fisherSpeed_gaussian`** (`½ tr((H_s⁻¹Ḣ_s)²)`). Instance hygiene: only the theorems mentioning `⁻¹`
  take `[DecidableEq ι]`; `isHermitian_sum_smul` needs neither `Fintype ι` nor `DecidableEq`.
- `RegularGeometricLimit.lean` (NOT mirrored; Astra's "regular geometric limit", pointwise):
  `dot_inv_eq_hessian_form` (`⟨g, H⁻¹g'⟩ = ⟨−H⁻¹g, H(−H⁻¹g')⟩`; `Pᵀ = P` from `hP.1.eq` via
  `conjTranspose_eq_transpose_of_trivial`), **`responseForm_asymptotic_minimizer`**
  (`g_a(v,u)/t → H(mv, mu)` given `mv = −H⁻¹∇R_v`), **`responseForm_asymptotic_movingMinimizer`**
  (velocities supplied by `Laplace.Patterning.movingMinimizer_deriv`: the stationarity equation of a
  differentiable curve of critical points). Imports `Laplace.Patterning.MovingMinimizer`.
- `MomentDetermination.lean` (NOT mirrored; round-22 item 7): **`priorZ_pathLoss_eq_of_moments_eq`**
  (same base moments ⇒ same partition function along the line), **`mixExp_eq_of_moments_eq`** (same
  mixed moments `∫φΔⁿ…` ⇒ same response `s ↦ ⟨φ⟩_s`); via `HasSum.tsum_eq` on `hasSum_priorZ_pathLoss`
  / `hasSum_mixNum`.
- `MeanMapInjective.lean` (NOT mirrored; multivariate strict identifiability / Legendre duality):
  `meanMap μ π L₀ R t a = (⟨Rᵢ⟩_{t,a})ᵢ`, `priorExp_dirLoss` (linearity in the observable via
  `Integrable.bdd_mul` + `integral_finsetSum`), **`TiltData.hasDerivAt_affLogZ_dir'`**
  (`D_v log Z = −t ∑ vᵢ mᵢ(a)`), **`meanMap_injective`** (no nonzero direction with a.s.-constant
  contrast on the prior support ⇒ the mean map is injective; proof: `mixExp_strictAnti` on the line
  from `a` to `b` with contrast `R_{b−a}` and the endpoint identifications `pathLoss _ _ 0 = L`,
  `affLoss_add_smul` at `ε = 1`).
- `ShapeMetricLimit.lean` (NOT mirrored; Astra's "next scale: common-minimiser shape geometry" for general
  regular families): `cov2Coefficient_grad_zero` (with `a = b = 0` the three cubic terms vanish:
  `simp [cov2Coefficient, dot]`), **`responseForm_shape_asymptotic`**
  (`g_a(v,u) → ½ trASig(A_v Σ A_u Σ)` at rate `O(1/t)` when both direction gradients vanish, from
  `gibbsCov_first_order_rate_explicit`), `trASig_matCLM_eq_trace` (`= tr(AΣBΣ)` for matrix data;
  `one_apply_eq_self` replaces the deprecated `ContinuousLinearMap.one_apply`; `Matrix.mulVec_single_one`).
  Matches the exact Gaussian value of `GaussianShapeMetric`.
- `BoundedDistance.lean` (NOT mirrored; Astra A(i)): `thermoLength_le_sqrt_of_fisherSpeed_le` (`g ≤ C` on
  `[0,1]` ⇒ `ℓ ≤ √C`, via `intervalIntegral.integral_mono_on`), `TiltData.thermoLength_le_sqrt_of_var_le`
  (mixture line, `t² Var ≤ C`).
- `ProfileTailLength.lean` (NOT mirrored; round-23 item 1, weak form): **`tendsto_integral_div_log_scaled`**
  (`c h(c) → L` ⇒ `(∫_{c₀}^{a₁ t^σ} h)/log t → σ L`; Cesàro lemma composed with the moving endpoint
  `T = a₁ t^σ`, `log T = log a₁ + σ log t`; `Tendsto.eventually_gt_atTop` for `0 < log T` — restate the
  composed-function hypothesis with a typed `have` before `rw`; `integral_interval_sub_left`).
- `ProfileGammaTail.lean` (NOT mirrored; the Gamma tail of the wall profile): `profileMoment p q k c`,
  `tailIntegral`, `profileMoment_subst` (`x = y^q` via `integral_comp_rpow_Ioi_of_pos` with exponent `1/q`),
  `tail_scale` (`x = z/c` via `integral_comp_mul_left_Ioi`), **`profileMoment_eq_tail`**
  (`N_k(c) = (1/q) c^{-(k+1/q)} I_k(c)`), `integral_rpow_mul_exp_neg_eq_Gamma`, **`tendsto_tailIntegral`**
  (`I_k(c) → Γ(k + 1/q)`, dominated convergence), `profileNum_*_eq_moment`, **`tendsto_mul_profileMean`**
  (`c⟨y^q⟩_c → 1/q`), **`tendsto_sq_mul_profileSecond`**, **`tendsto_sq_mul_profileVar`**
  (`c² Var_c(y^q) → 1/q` — the response-active exponent). Gotchas: `Tendsto.neg` lands in `𝓝 (-0)`
  (`rw [neg_zero] at`); pass `(x := z)` to `tendsto_const_nhds` in `div_atTop`; state the ratio identities
  as `c * (A / B)` (matching `c * profilePosterior`), not `c * A / B`.
- `WallRecedes.lean` (NOT mirrored; THE RECEDING-WALL LAW, round-23 item 1 weak form):
  `continuousOn_profileNum` (on `Ici 0`, `continuousOn_of_dominated`), `continuousOn_profileVar`,
  **`wall_recedes`**: `ℓ_t(c₀t^{-σ*}, a₁)/log t → σ*·√(1/q)` for the two-monomial family — assembled from
  `wall_window_length` (exact), `tendsto_sq_mul_profileVar` (Gamma tail) and
  `tendsto_integral_div_log_scaled` (Cesàro along the moving endpoint). The Cesàro lemmas now take
  `∀ a b, 0 ≤ a → 0 ≤ b → IntervalIntegrable …` (continuity only needed on `[0,∞)`).
- `EntropyDuality.lean` (NOT mirrored; Astra round-23 item E): `priorExp_eq_integral_gibbsDensity`,
  `priorExp_add_of_integrable`, **`meanMap_legendre`** (`F_t(a) − a·m(a) = ⟨L₀⟩_a + KL(P_a‖π)/t`, from
  `gibbs_variational_eq`; the log-density term is `ρ·(−tL − log Z)` pointwise, bounded × integrable),
  `mixExp_zero_eq_dot`, **`affFreeEnergy_le_tangent`** (`F(b) ≤ F(a) + (b−a)·m(a)`: FTC on `mixLogZ` along
  the line + `mixExp_antitone`), **`affFreeEnergy_sub_dot_le`** (Legendre sup attained at `a`),
  **`mixKL_aff_eq`** (KL = Bregman divergence of `log Z`, multivariate). Gotchas:
  `Continuous.intervalIntegrable` needs `(μ := volume)` when the measure is otherwise undetermined;
  `Integrable.congr` goals carry beta-redexes — `beta_reduce` before `by_cases`/`rw`.
- `SpectatorWall.lean` (NOT mirrored; Astra's spectator example): `spectatorPath a (x,y) = x² + y⁴ + a y²`,
  `spectatorVel = y²`, `spectator_num` (Fubini: the `x`-Gaussian factors out; `Measure.volume_eq_prod`
  + `integral_prod_mul`, no integrability needed), `integral_even_eq_two_Ioi` (`integral_comp_abs`),
  `spectator_weight_even`, `twoMono_num_eq`/`twoMono_den_eq` (rpow → npow on `Ioi 0`),
  **`spectator_priorExp`** (2D posterior of an even function of `y` = half-line two-monomial posterior),
  **`spectator_fisherSpeed`**, **`spectator_wall_recedes`** (`ℓ_t/log t → (1/2)·√(1/2) = 1/(2√2)`, not
  `σ*√λ = 1/2`). Gotchas: `integral_gaussian t` is stated with `-t * x^2` (`simp only [neg_mul] at`);
  bare numerals in a real exponent `t ^ (-(1 - 2/4))` elaborate as ℕ (`Neg ℕ` error) — annotate `(2:ℝ)`;
  rewrite the product observable `fun x ↦ V a x * V a x` BEFORE the linear one.
- `WallRecedes.lean` addendum: `recession_coefficient_eq` (`σ*√(1/q) = √(σ*(λ₊ − λ_wall))`, `λ₊ = 1/q`,
  `λ_wall = 1/p`), `wall_recedes_exponent_form` (Astra's LP consistency relation `σκ = λ₊ − λ_wall`).
- `WallChart.lean` (NOT mirrored; Astra round-24 "singular response-chart theorem", exact homogeneous case):
  `chartNum/chartPosterior p q r ψ c d` (two-parameter profile `∝ e^{-(y^p + cy^q + dy^r)}`),
  `chartPath p q r a b`, `chart_numerator_scaled`, **`chart_posterior_eq_profile`** (finite-t posterior in
  the window `a = ct^{-σ_q}, b = dt^{-σ_r}` = profile law), `priorExp_chart_rpow(_mul)`, **`chart_cov`**
  (`t^{-σ_{e₁}} t^{-σ_{e₂}} · t² Cov_t(w^{e₁}, w^{e₂}) = Cov_{c,d}(y^{e₁}, y^{e₂})`, any exponents),
  `affLoss_chart`, `dirLoss_single`, **`responseForm_chart`** (the response form of the affine family
  `w^p + a w^q + b w^r` pulled back by the chart Jacobian is the profile Fisher matrix, 2×2 with `E = ![q,r]`,
  `fin_cases` for the contrast identification).
- `ThermoLengthFromBase.lean` (NOT mirrored; Astra round-24 item 1, abstract part):
  **`tendsto_intervalIntegral_div_log_from`** (Cesàro from any base point `u₀`, no sign hypothesis),
  `continuousOn_priorNum_Ici` (dominated continuity of `u ↦ ∫ φ e^{-uL} π` on `Ici u₀` for `L ≥ 0`, dominant
  `|φ| e^{-u₀L} π`), **`continuousOn_priorCov_self_Ici`** (variance of a nonnegative loss continuous on
  `[u₀,∞)` given `Z ≠ 0` there and integrability of `L^k e^{-u₀L}π`, `k ≤ 2`),
  **`thermoLength_from_div_log_tendsto`** (`u²Var_u(L) → λ ⇒ (∫_{u₀}^t √Var_u)/log t → √λ`). The concrete
  Gaussian-prior anharmonic instance (λ = d/2) remains to be assembled from `localisedVar_energy_leading`.
- `AnharmonicFeaturelessLaw.lean` (NOT mirrored; Astra round-24 item B, the concrete instance):
  `tendsto_of_rate_div`, `gaussPrior g m = e^{-(g/2)|u−m|²}`, `rotatedAnharmonic_one_zero`,
  **`exp_gaussPrior_eq_localised`** (Gaussian-prior temperature weight = the seabed's localised weight
  `localisedRotatedAnharmonic 1 0 … t`), `priorExp_gaussPrior`, `priorCov_gaussPrior`,
  **`tendsto_sq_mul_priorCov_gaussPrior`** (`u² Var_u(L) → d/2` from `localisedVar_energy_leading`),
  `integrable_energy_pow_gaussPrior` (`L^k e^{-sL}π`, `k ≤ 2`, via `integrable_localised_of_integrable`,
  `integrable_coord_energy_separableAnharmonic`, `integrable_energy_energy_coord`),
  **`anharmonic_thermoLength_div_log_tendsto`** (`(∫_{s₀}^t √Var_u)/log t → √(d/2)`: the RLCT `d/2` of a
  regular model is the growth rate of the thermodynamic length, proper prior, unbounded loss).
  Gotchas: `ᵀ` needs `open scoped Matrix`; `anharmonicPotential` is `Laplace.OneD.`; `conv_lhs => rw [h]`
  rewrites every occurrence on the LHS (also inside `exp`) — isolate the product with a `show`.
- `WallRecedesStrong.lean` (NOT mirrored; Astra round-24 items 2/3, THE STRONG-FORM RECEDING WALL):
  `one_sub_exp_neg_le`, `tailIntegrand_le`, `integrableOn_tailIntegrand`, **`tailIntegral_sub_le`**
  (`0 ≤ Γ(k+1/q) − I_k(c) ≤ c^{-p/q} Γ(k+1/q+p/q)`), `mul_profileMean_eq` / `sq_mul_profileSecond_eq`
  (exact ratio identities), `abs_sqrt_sub_sqrt_le`, `ratio_perturb_bound`, `tailThreshold`,
  `tail_deficit_half`, **`tailRatio_sub_le`**, `tailRateConst`, `gamma_ratio_one/two`, `varRateConst`,
  **`sq_mul_profileVar_sub_le`** (`|c²Var_c(y^q) − 1/q| ≤ C_V c^{-p/q}`), **`profileSpeed_defect_le`**,
  `profileSpeed`, `speedThreshold`, **`integrableOn_profileSpeed_defect`**, **`profileLength_renormalised`**
  (`∫_{c₀}^T h − √(1/q) log T → K`), **`wall_recedes_strong`** (`∃ K, ℓ_t − σ*√(1/q) log t → K`).
  Gotchas: `field_simp` rewrites exponents inside `rpow` — isolate with `show` + `mul_div_mul_left`; real
  powers of a possibly negative base need `0 < c`; state `hc₂ : 0 < c₂` AFTER the `set` (else terms built
  from it mention the unfolded name); `Tendsto.add tendsto_const_nhds` needs `(x := …)`; a "No goals"
  error's line number may point at an `exact` after a `congr 1` that already closed the goal.
- `MeanMapFDeriv.lean` (NOT mirrored; Astra item D, stage 1): `dirCLM R x = ∑ⱼ Rⱼ(x) • proj j` (the direction
  functional as a CLM), `dirCLM_apply`, `norm_dirCLM_le` (`≤ ∑|Rⱼ(x)|`, sup norm via `norm_le_pi_norm`),
  `aestronglyMeasurable_dirCLM` (`Finset.aestronglyMeasurable_sum` + `.congr` with `Finset.sum_apply`),
  `affLoss_eq_dirCLM`, `hasFDerivAt_affWeight` (pointwise Fréchet derivative via `(dirCLM).hasFDerivAt`,
  `.const_add/.const_mul/.neg/.exp/.mul_const`, then `congr_fderiv` + `ext v; simp [smul_apply, neg_apply]`),
  **`hasFDerivAt_affNum`** (`Integrable F' ∧ HasFDerivAt (a ↦ ∫ φ e^{-tL_a} π) (∫ F' a₀) a₀` by
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` on the unit ball with bound
  `t Mφ S e^{tS} e^{-tL_{a₀}} π`), **`affNum_fderiv_apply`** (`(∫ F') v = −t ∫ φ R_v e π` via
  `ContinuousLinearMap.integral_apply`). Gotchas: the Fréchet parametric theorem is
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` (no `_loc_`), hypotheses `(hs : s ∈ 𝓝 x₀)` and
  `∀ᵐ a, ∀ x ∈ s, …`; `Integrable.bdd_mul` needs `(c := …)` when the bound is proved by `nlinarith`;
  `ContinuousLinearMap.smul_apply/neg_apply` are deprecated for root `smul_apply/neg_apply`.
- `MeanMapJacobian.lean` (NOT mirrored; Astra item D, stage 2): `affNumDeriv` (derivative CLM of a
  numerator), `meanMapDeriv` (`ContinuousLinearMap.pi` of the quotient-rule combinations),
  **`hasFDerivAt_meanMap`** (`HasFDerivAt (meanMap) (meanMapDeriv a₀) a₀`; inverse via
  `(hasDerivAt_inv hZ).comp_hasFDerivAt`, `HasFDerivAt.mul`, `hasFDerivAt_pi`; ascribe the numerator
  derivative with its `affNumDeriv` name BEFORE `.mul`, else `ring` sees two atoms), **`meanMapDeriv_apply`**
  (`Dm(a₀)[v]ᵢ = −t Cov_{a₀}(Rᵢ, R_v)`), `sum_mul_priorCov_eq` (`∑ vᵢ Cov(Rᵢ,ψ) = Cov(R_v,ψ)` via
  `priorExp_dirLoss` on the family `Rᵢψ`), **`meanMapDeriv_injective`** (non-degenerate contrasts ⇒ the
  Jacobian is injective: the mean map is an injective immersion). Remaining for the full IFT: continuity
  of `a ↦ meanMapDeriv a` ⇒ `HasStrictFDerivAt` ⇒ local diffeomorphism.
- `MeanMapChart.lean` (NOT mirrored; Astra item D, stage 3 — CLOSES D): `continuousAt_affNumDeriv`
  (`continuousAt_of_dominated` with the same unit-ball majorant `t Mφ S e^{tS} e^{-tL_{a₀}} π` as the
  derivative; `bound`, `hF_meas` eventually, `h_bound` via `Filter.eventually_of_mem (ball_mem_nhds …)`,
  pointwise continuity from `(hasFDerivAt_affWeight …).continuousAt.const_mul t |>.neg.smul continuousAt_const`),
  **`hasStrictFDerivAt_meanMap`** (`hasStrictFDerivAt_pi''` + `ContinuousLinearMap.proj_pi` per component, then
  `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` with `f'` the explicit quotient-rule entry; `hZ a` for ALL
  `a` from `tiltData_aff … |>.choose_spec.ν_pos`), `meanMapDerivEquiv` (`LinearEquiv.ofInjectiveEndo` +
  `LinearEquiv.toContinuousLinearEquiv`; `coe_meanMapDerivEquiv` by `ext` + the three coe simp lemmas),
  `hasStrictFDerivAt_meanMap_equiv`, **`meanMapInverse`** (`HasStrictFDerivAt.localInverse`) with
  `meanMapInverse_meanMap` (left inverse near `a₀`), `meanMap_meanMapInverse` (right inverse near `m a₀`),
  `meanMapInverse_apply_meanMap`, `meanMapInverse_continuousAt`, **`hasStrictFDerivAt_meanMapInverse`**
  (derivative `(meanMapDerivEquiv …).symm`), **`map_nhds_meanMap`** (`map m (𝓝 a₀) = 𝓝 (m a₀)`),
  `meanMapInverse_deriv_comp` (`ContinuousLinearEquiv.coe_symm_comp_coe`; pass the equivalence explicitly and pin
  `(μ := μ)` in `coe_meanMapDerivEquiv`, else "Module ?m ?m stuck"). The response coordinates are a local chart of
  the data manifold: Astra round-24 item D is closed.
- `MeanMapEmbedding.lean` (NOT mirrored; Astra round 25, item 1): `continuous_meanMap`,
  `isOpenMap_meanMap` (`isOpenMap_iff_nhds_le` + `map_nhds_meanMap`), **`isOpenEmbedding_meanMap`**
  (`IsOpenEmbedding.of_continuous_injective_isOpenMap`), `isOpen_range_meanMap`, `meanMapHomeomorph`
  (`IsEmbedding.toHomeomorph`), `invFun_meanMap`/`meanMap_invFun` (`Function.leftInverse_invFun`,
  `invFun_eq`), **`hasStrictFDerivAt_invFun_meanMap`** (`HasStrictFDerivAt.to_local_left_inverse` with the
  global left inverse), `continuousOn_invFun_meanMap`, `meanMapInverse_eventuallyEq_invFun`. The response
  coordinates are a GLOBAL chart of the affine data manifold.
- `StateDensity.lean` (NOT mirrored; Astra round 25, item 2): `lossLaw μ π L := (μ.withDensity (ofReal ∘ π)).map L`
  (the state density), `lawExp ν f u`, `lawVar ν u`, `lawLength ν t`, `radialLength μ π L t := ∫₀ᵗ √Var_u(L)`;
  `integral_lossLaw` (`integral_map` + `integral_withDensity_eq_integral_toReal_smul₀`), **`priorZ_eq_lossLaw`**
  (Z = Laplace transform of the state density), **`priorExp_comp_eq_lawExp`**, `priorCov_self_eq_lawVar`,
  `priorExp_const_add`/`priorCov_const_add`, `thermoLength_neutral_eq_radialLength`, `radialLength_eq_lawLength`,
  **`thermoLength_neutral_eq_of_lossLaw_eq`** (same state density ⇒ same featureless-line geometry). Pass
  `(g := …)`/`(f := …)` explicitly when rewriting with `integral_lossLaw`/`priorExp_comp_eq_lawExp` (beta-redex
  integrands).
- `RenormalisedLength.lean` (Mathlib-only; mirrorable): `hasDerivAt_log_sub_loglog` (`d/du[A log u − B log log u]`),
  `integrableOn_inv_mul_log_sq` (`C/(u log² u)` on `(u₀,∞)` via `integrableOn_Ioi_deriv_of_nonneg'` with `−C/log u`),
  **`tendsto_renormalised_length`**: `ContinuousOn f (Ici u₀)`, `|f u − (A − B/log u)| ≤ C/log² u` ⇒
  `∃ K, ∫_{u₀}^t f/u − (A log t − B log log t) → K` (split off the remainder, `intervalIntegral_tendsto_integral_Ioi`,
  FTC `integral_eq_sub_of_hasDerivAt`).
- `LogGammaTails.lean` (Mathlib-only; mirrorable): `gammaTrunc j u = ∫₀ᵘ s^j e^{-s}`, `logGammaTrunc j u`,
  `logGammaFull j`; `integrableOn_pow_mul_exp_neg_Ioi` (`Real.GammaIntegral_convergent`),
  `integral_pow_mul_exp_neg_Ioi = j!` (`Real.Gamma_eq_integral` + `Gamma_nat_eq_factorial`),
  `integrableOn_log_Ioc_zero_one` (`intervalIntegrable_log'`), `integrableOn_pow_mul_exp_neg_mul_log_Ioi`
  (split at 1: `|log| ≤ |log|` on `(0,1]`, `log s ≤ s` beyond), **`gammaTail_le`** (`∫_u^∞ s^j e^{-s} ≤ (j+2)!/u²`
  by inserting `(s/u)² ≥ 1` — no exponential asymptotics), `logGammaTail_abs_le` (`(j+3)!/u²`),
  `gammaTrunc_eq`/`logGammaTrunc_eq` (`Ioc_union_Ioi_eq_Ioi` + `setIntegral_union`), `abs_gammaTrunc_sub_le`,
  `abs_logGammaTrunc_sub_le`, the boundary limits `tendsto_pow_mul_exp_neg_mul_log_nhdsGT_zero`
  (`tendsto_log_mul_rpow_nhdsGT_zero`) / `_atTop` (`Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`, squeeze),
  **`logGammaFull_succ`** (`Λ_{j+1}(∞) = (j+1)Λ_j(∞) + j!` by `integral_Ioi_mul_deriv_eq_deriv_mul` with
  `u = log`, `v = s^{j+1}e^{-s}`; state the `IntegrableOn` of the Pi-products with typed `have`s).
- `MultiplicityModel.lean` (NOT mirrored; Astra round 25, item 3, `k = 1`): the state density `(−log ℓ)dℓ` on
  `(0,1)` as `priorExp (volume.restrict (Ioo 0 1)) (fun ℓ ↦ |log ℓ|) id`; `logModelMoment j u`, `logModelJ j u =
  log u · Γ_j(u) − Λ_j(u)`; **`logModelMoment_eq`** (`M_j(u) = u^{-(j+1)} J_j(u)`, substitution `s = uℓ` via
  `integral_comp_mul_left (f := G)` — the integrand MUST be named, the beta-redex is not a higher-order pattern),
  `logModel_sq_mul_var` (`u²Var = (J₂J₀ − J₁²)/J₀²`), `abs_mul_le_of_abs_le`, **`var_ratio_numerator_bound`**
  (pure algebra: `x_j = g_j − l_j τ + O(τ²)`, `g = (1,1,2)`, `l = (l₀, l₀+1, 2l₀+3)` ⇒ `(x₂x₀ − x₁²) − (1−τ)x₀² =
  O(τ²)` with explicit constant; `obtain ⟨d, rfl⟩ : ∃ d, x = y + d` then one `ring` identity `P + Q`),
  `logGammaFull_one/two`, `logModelC`, **`logModel_var_bound`** (`log u ≥ 481 + 2|Λ₀(∞)|` ⇒ `J₀ ≥ log u/2` and
  `|u²Var_u − (1 − 1/log u)| ≤ C/log² u`; tails `≤ 120/u² ≤ 120/log² u` since `log u ≤ u`),
  `abs_sqrt_sub_le_of_abs_sub_sq_le`, `logModel_speed_bound` (`u√Var = 1 − 1/(2 log u) + O(1/log² u)`),
  `continuous_gammaTrunc/logGammaTrunc` (`continuous_primitive`), `continuousOn_logModelJ`,
  **`logModel_length_renormalised`**: `∃ u₀ > 1, ∃ K, ∫_{u₀}^t √Var_u − (log t − ½ log log t) → K`.
  THERMODYNAMIC LENGTH DETECTS MULTIPLICITY (numerically: residual·log²u → −(1−γ) ≈ −0.423).
- `TauberianVariance.lean` (NOT mirrored; Astra round 25, item 2 second half): `exp_neg_sandwich`
  (`x e^{-x} ≤ 1 − e^{-x} ≤ x`, all `x`), `lawMoment ν k u := ∫ ℓ^k e^{-uℓ} dν`, **`sandwich_tilt`** (nonneg weight
  `w`: `(c−1)u ∫ w ℓ e^{-cuℓ} ≤ ∫ w e^{-uℓ} − ∫ w e^{-cuℓ} ≤ (c−1)u ∫ w ℓ e^{-uℓ}` by `integral_mono_ae`),
  `tendsto_regVar_lower/upper` (`(1 − c^{-λ})/(c−1) → λ` and `c^{λ+1}(…) → λ` as `c ↓ 1`, from
  `Real.hasDerivAt_rpow_const` + `hasDerivAt_iff_tendsto_slope`), **`tendsto_ratio_of_regVar`** (the
  monotone-density squeeze with EVENTUAL hypotheses `∀ᶠ u, 0 < F u`, `∀ c > 1, ∀ᶠ u, sandwich`; ε-argument:
  pick `c` near 1 via `(hA.and hB).and self_mem_nhdsWithin |>.exists` with `NeBot (𝓝[>] 1)`, transport the
  `cu`-bound to `u` by `eventually_atTop` and `v/c`), `RegVar ν λ`, `tendsto_mul_lawMoment_one_div_of_regVar`
  (`u N₁/Z → λ`), `tendsto_mul_lawMoment_two_div_of_regVar` (`u N₂/N₁ → λ+1`; `N₁` regularly varying with index
  `−(λ+1)` via `hR.comp hcu` and `Real.rpow_neg_one`), **`tendsto_sq_mul_lawVar_of_regVar`**
  (`u² Var → λ(λ+1) − λ² = λ`), `regVar_of_asymptotic` (`Z ~ C u^{-λ}(log u)^k` ⇒ `RegVar`; `log(cu)/log u → 1`),
  `integrable_lossLaw_iff` (`integrable_map_measure` + `integrable_withDensity_iff`),
  **`tendsto_sq_mul_priorCov_of_partition_asymptotic`**: the partition-function asymptotic alone gives
  `u² Var_u(L) → λ` (feeds `thermoLength_neutral_div_log_tendsto`: the RLCT is the featureless-length coefficient).
  Gotchas: `Tendsto.div`/`.comp` produce Pi-division/`∘` forms — `simp only [Pi.div_apply, Function.comp_apply]`
  before `field_simp`; `Filter.Eventually` has no `.comp` — use `hcu.eventually hF`; `field_simp` closed several
  goals outright (drop the trailing `ring`).
- `FeaturelessLawFromPartition.lean` (NOT mirrored): **`featureless_law_of_partition_asymptotic`** —
  `Z(u) ~ C u^{-λ}(log u)^k` (`hasym`), `L ≥ 0`, moments `L^k e^{-uL} π` integrable, `Z > 0` ⇒
  `(∫_{u₀}^t √Var_u(L))/log t → √λ` for every base `u₀ > 0` (`continuousOn_priorCov_self_Ici` +
  `thermoLength_from_div_log_tendsto` + the Tauberian theorem). THE RLCT IS THE FEATURELESS-LENGTH COEFFICIENT
  under the free-energy asymptotic alone.
- `FisherInformation.lean` (NOT mirrored; Astra round 25 item 5, intrinsic form): `affLogDensity` (`−t L_a − log Z(a)`),
  `affScore μ π L₀ R t a v x := −t (R_v x − ⟨R_v⟩_a)`, **`hasDerivAt_affLogDensity`** (score = directional
  derivative of the log-density along `a + εv`; `affLoss_add_smul` + `TiltData.hasDerivAt_affLogZ_dir` with the
  `R`-slot changed to `fun _ ↦ 0` via `TiltData.changeR`), `priorExp_affScore` (mean zero),
  **`fisherInformation_eq_responseForm`** (`E_a[score_v score_w] = t² Cov_a(R_v, R_w) = responseForm`): expand
  the product into four bounded×base-weight terms with lambda-typed `Integrable` facts (`I3 I2 I1 I0`, `I32`,
  `I321`), `integral_add/sub/const_mul`, then substitute `mv`, `mw` (forward `rw [hmv, hmw]`) and `field_simp; ring`.
  The response form is the Fisher–Rao metric of the posterior family pulled back to the data manifold.
- `RadialLaws.lean` (NOT mirrored; Astra round 25 item 6): `priorExp_smul_add` (`⟨φ⟩_u^{aL+b} = ⟨φ⟩_{au}^L`),
  `priorCov_self_smul_add` (`Var_u(aL+b) = a² Var_{au}(L)`; fold the three integral values with `set … ;
  clear_value` BEFORE `field_simp`, else it rewrites inside the integrands and `ring` sees different atoms),
  **`radialLength_smul_add`** (`D_t(aL+b) = D_{at}(L)`, `a > 0`, via `integral_comp_mul_left (f := …)`),
  `radialLength_const_add` (from scaling with `a = 1`), `wall_window_length_two_sided` (instance of
  `wall_window_length` at `−c₋`; subscript `₋` is not an identifier character — use `cm`/`cp`).
- `Affinity.lean` (NOT mirrored; Astra round 26 Theorem A, affinity + asymptotics): `lawDensity ν u ℓ`,
  `lawAffinity ν s t := Z((s+t)/2)/√(Z s · Z t)`, **`integral_sqrt_lawDensity_mul`** and
  **`integral_sqrt_posterior_mul`** (`∫√(p_s p_t) = ρ(s,t)`; `div_mul_div_comm`, `Real.sqrt_div'`, `← Real.exp_add`,
  `← Real.exp_half`, `Real.sqrt_mul_self (hπ x)`), `log_lawAffinity` (Bhattacharyya divergence = midpoint Jensen gap of
  `log Z`), `tendsto_lawMoment_zero_of_regVar` (doubling: `Z(2u) ≤ r Z(u)` eventually with `r < 1`, induction
  `Z(2^n U) ≤ r^n Z(U)`, antitone `Z`), `tendsto_lawAffinity_sq_div` (`ρ(0,t)²/Z(t) → 2^{2λ}/Z(0)` from `RegVar` at
  `c = 1/2`; `Real.inv_rpow`, `Real.rpow_neg`; `simp only [div_pow]` BEFORE `Real.sq_sqrt`), `tendsto_lawAffinity_zero`,
  **`tendsto_fisherRao_pi`** (`2 arccos ρ(0,t) → π`). Gotcha: `gt_mem_nhds (h : a < b) : ∀ᶠ x in 𝓝 a, x < b`
  (`lt_mem_nhds` is the other side).
- `RadialCurvature.lean` (NOT mirrored; Astra round 26 Theorem A, curvature): **`hasDerivAt_lawMoment`** (`N_k' =
  −N_{k+1}` on `(0,∞)` via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `s = Ioi (u/2)` with bound
  `ℓ^{k+1} e^{-(u/2)ℓ}`; the pointwise derivative MUST be built from a lambda-typed `have hneg : HasDerivAt (fun x ↦
  -(x*ℓ)) (-ℓ) v := (hasDerivAt_mul_const ℓ).neg` — the bare `.neg.exp` carries a Pi-negation `(-fun x ↦ …) v` that
  `ring` cannot see through), `hasDerivAt_lawLogZ` (`F' = −⟨ℓ⟩`), `hasDerivAt_lawMean` (`⟨ℓ⟩' = −Var`),
  `continuousOn_lawVar`, **`bhattacharyya_eq_integral_var`** (`(F s + F t)/2 − F m = ½(∫_s^m (u−s)Var + ∫_m^t (t−u)Var)`
  by `intervalIntegral.integral_mul_deriv_eq_deriv_mul` — QUALIFY it, the root `integral_mul_deriv_eq_deriv_mul` has
  `tsupport` hypotheses — with `u = x − s`/`t − x`, `v = mean`, and the FTC for `F`; `set m` then `rw [hm]` before the
  final `ring`), `hasDerivAt_sqrt_lawDensity` (`HasDerivAt.sqrt` then `div_eq_iff` + `linear_combination (ℓ − m) * hsq`),
  `integral_sq_sqrt_speed` (`= Var/4`). Under `open intervalIntegral`, `integral_neg`/`integral_const_mul` are ambiguous:
  write `MeasureTheory.`/`intervalIntegral.` explicitly.
- `InformationProjection.lean` (NOT mirrored; Astra round 26 Theorem B): `log_gibbsDensity_sub` (`log p_a − log p_b =
  t R_{b−a} + A(b) − A(a)`, needs `π > 0` pointwise), **`relEnt_pythagoras`**: `q ≥ 0`, `∫ q = 1`, `E_q[R] = m(a)`
  (moment matching), the two KL integrands integrable ⇒ `relEnt μ q (gibbsDensity … b) = relEnt μ q (gibbsDensity … a) +
  mixKL … a (dirLoss R (b−a)) t 0 1` (= `KL(P_a‖P_b)` by `mixKL_aff_eq`). Pointwise identity by cases on `q x = 0`;
  `gibbsDensity_pos hπ' hZ (hx : π x ≠ 0)` takes the point implicitly. Response coordinates = dual affine coordinates.
- `AngularBound.lean` (NOT mirrored; Astra round 26 Theorem A, the inequality): `integral_mul_sq_le` (Cauchy–Schwarz for
  integrals by `discrim_le_zero`; qualify `MeasureTheory.integral_mul_const/const_mul` under `open intervalIntegral`),
  `affinityExp ν s u := exp(F(m) − (F s + F u)/2)` (= `lawAffinity`, `affinityExp_eq`; `_pos`, `_self = 1`),
  `affinityExp_lt_one` (`s < u`, non-degenerate `lawVar > 0` ⇒ `ρ < 1`, from the Jensen-gap identity and
  `intervalIntegral_pos_of_pos_on`; `Real.exp_lt_one` does not exist — `rw [← Real.exp_zero, Real.exp_lt_exp]`),
  **`hasDerivAt_affinityExp`** (`ρ' = (ρ/2)(⟨ℓ⟩_u − ⟨ℓ⟩_m)` via `HasDerivAt.exp` of the Jensen gap; `simp only
  [Function.comp_apply, Pi.sub_apply, Pi.add_apply]` before `ring`), **`affinity_cauchy_schwarz`** (moment form
  `Z(m)²(⟨ℓ⟩_m − ⟨ℓ⟩_u)² ≤ Z_u Var_u (Z_s − Z_m²/Z_u)`, with `f = (ℓ−a)e^{-uℓ/2}`, `g = e^{-sℓ/2} − c e^{-uℓ/2}`; all
  integrability facts lambda-typed, and the integral values converted to `lawMoment` atoms by `rfl` BEFORE `field_simp`
  — never `simp only [lawMoment]` there), `affinityExp_sq`, `hasDerivAt_arccos_affinityExp` (`θ' ≤ ½√Var`; `change`
  not `show` for goal rewriting), **`two_arccos_affinityExp_le`** (`monotoneOn_of_deriv_nonneg` on
  `Φ = ½∫_s^v √Var − arccos ρ`, `interior_Icc`, `integral_hasDerivAt_right` with
  `ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi`). THE LENGTH–DISTANCE THEOREM: `2 arccos ρ(s,t) ≤ ∫_s^t √Var`,
  with `2 arccos ρ(0,t) → π` (Affinity) and `∫ √Var ~ √λ log t`.
- `HalfLineLaplace.lean` (NOT mirrored; Astra round 26 §3, the centred saddle lemma in abstract form):
  `integrable_dominating n hc₁ hc₂ hα` (the majorant `(1+|w|)^n (e^{-c₁w²} + 𝟙_{w>0} e^{-c₂ w^α})`), and
  **`tendsto_sqrt_mul_integral`**: for a measurable potential `φ` with `φ 1 = 0`, quadratic below `c₁(z−1)²` on `(0, z₁]`,
  coercive `c₂(z−1)^α` (`0 < α ≤ 1`) beyond `z₁`, and `φ(1+h)/h² → κ/2`, and observables `G B w` measurable, polynomially
  bounded `|G B w| ≤ C(1+|w|)^n` for `B ≥ 1`, `w > −√B`, converging pointwise to `Ginf`:
  `√B ∫₀^∞ G B (√B(z−1)) e^{-Bφ(z)} dz → ∫ Ginf w e^{-κw²/2} dw`. Proof: substitute `w = √B(z−1)`
  (`Measure.integral_comp_mul_left`, `integral_add_right_eq_self F 1`), dominated convergence with the majorant (local
  Gaussian bound from `hquad` on `z ≤ z₁`, stretched-exponential tail from `hlin`, `Real.exp_le_exp`,
  `Real.rpow_le_rpow_left_iff`). Gaussian moments `integral_exp_neg_half_mul_sq (hκ) : ∫ e^{-κw²/2} = √2√π/√κ`,
  `integral_mul_exp_neg_half_mul_sq κ = 0`, `integral_sq_mul_exp_neg_half_mul_sq (hκ) : ∫ w² e = (1/κ) ∫ e`.
  Gotchas: `integral_comp_mul_left` (interval) needs `(f := G)` when the integrand is a beta-redex; `Integrable.sub/add`
  give Pi-form functions — state combined integrability with lambda-typed `have`s; `.congr_fun` fails on `Integrable` (an
  `And`) — ascribe `IntegrableOn`.
- `TwoMonoPotential.lean` (NOT mirrored): the rescaled two-monomial potential `twoMonoPsi p q z := z^p − (p/q) z^q`,
  `twoMonoPhi := ψ z − ψ 1` (so `φ 1 = 0`, `φ' 1 = 0`, `φ''(1) = p(p−q)`): `hasDerivAt_twoMonoPsi/Phi/Psi'`,
  `twoMonoPhi_div_sq_tendsto (hq) : φ(1+h)/h² → p(p−q)/2` (`HasDerivAt.lhopital_zero_nhdsNE`; pass `(p := p)` to
  `hasDerivAt_twoMonoPhi` inside `have :=`; `simpa` on `HasDerivAt` gives instance-path mismatches — use
  `exact this.congr_deriv (mul_one _)`; state continuity limits as `𝓝 (twoMonoPhi p q 1)` not `1 + 0`),
  `rpow_sub_one_ge (hr) (hv : 1 ≤ v) : r(v−1)/v ≤ v^r − 1`, `one_sub_rpow_ge`, `rpow_antitone_of_nonpos`,
  `twoMonoPhi_sub_eq_integral` (FTC), `twoMonoPsi'_nonpos` on `(0,1]`, **`twoMonoPhi_quad_bound (hq hqp) (hz₁ : 1 ≤ z₁) :
  ∃ c₁ > 0, ∀ z ∈ (0, z₁], c₁(z−1)² ≤ φ z`** (left: `ψ'(v) ≤ −p(1−v)` … via `one_sub_rpow_ge`; right: `ψ'(v) ≥ p(v−1)/v ·
  min`), **`twoMonoPhi_coercive (hq hqp) (hz : max 2 ((2p/q)^{1/(p−q)}) ≤ z) : ½(z−1)^{min p 1} ≤ φ z`**,
  `abs_rpow_sub_one_le (hq) (hn : q ≤ n) (hz : 0 < z) : |z^q − 1| ≤ max q 1 · |z−1| · (1+z)^n` (Bernoulli lemmas are
  root-namespace: `one_add_mul_self_le_rpow_one_add`, `rpow_one_add_le_one_add_mul_self`; `Real.rpow_sub_one hv0.ne'
  (q−1)` needs the explicit exponent), `tendsto_sqrt_mul_rpow_sub_one q w : √B((1 + w/√B)^q − 1) → q w`.
  `gcongr` side goals with nonnegativity from hypotheses need explicit `mul_le_mul_of_nonneg_left`; goal-changing `show`
  is linted — use `change`.
- `NegativeChamber.lean` (NOT mirrored; Astra round 25 item 4 / round 26 §3, **profile matching**): `negScale p q b :=
  (qb/p)^{1/(p−q)}` (= `y_b`, the interior minimiser of `y^p − b y^q`), `negB := y_b^p`, `zNum p q g B := ∫₀^∞ g(z)
  e^{-Bφ(z)} dz`, `negVar p q b := ⟨y^q y^q⟩_{-b} − ⟨y^q⟩_{-b}²` (profile variance at `c = −b`). `negScale_rpow_sub`
  (`y_b^{p−q} = qb/p`), `mul_negScale_rpow` (`b y_b^q = (p/q) B`), **`profileNum_neg_eq`** (the rescaling identity
  `N_g(−b) = y_b e^{-Bψ(1)} ∫₀^∞ g(y_b z) e^{-Bφ(z)} dz`, from `integral_comp_mul_left_Ioi`),
  `integrableOn_rpow_mul_exp_neg_twoMonoPhi` (`z^s e^{-Bφ}` integrable for `s > −1`, `B > 0`, via `φ ≥ ½z^p − ½z₁^p`
  and `integrableOn_rpow_mul_exp_neg_mul_rpow`), `zNum_one_pos`, `profilePosterior_neg_eq` (the prefactor cancels:
  `mul_div_mul_left`), `zNum_rpow_scale`/`zNum_rpow_sq_scale` (`Real.mul_rpow`), **`negVar_mul_eq`**
  (`Var_{-b}(y^q) · y_b^{p−2q} = B · Var_B(z^q)`, by `linear_combination (N₂/N₀ − (N₁/N₀)²) * hyp` with `hyp : y^q y^q
  y^{p−2q} = y^p`), `negA p q j B := √B ∫ (√B(z^q−1))^j e^{-Bφ}`, `negA_eq`, `zNum_sub_one`, `zNum_sub_one_sq`,
  `mul_zVar_eq_negA` (`B·Var_B(z^q) = A₂/A₀ − (A₁/A₀)²`; `set s := √B`, `subst` of `s*s = B`, `field_simp; ring`),
  `abs_sqrt_mul_rpow_sub_one_pow_le` (the polynomial envelope `|(√B((1+w/√B)^q−1))^j| ≤ (max q 1 · 2^{⌈q⌉})^j
  (1+|w|)^{j(⌈q⌉+1)}` for `B ≥ 1`, `w > −√B`; `pow_mul'` then `← mul_pow` then `pow_le_pow_left₀`),
  **`tendsto_negA j`** (three applications of `tendsto_sqrt_mul_integral` with `z₁ = max 2 ((2p/q)^{1/(p−q)})`,
  `c₂ = ½`, `α = min p 1`, `κ = p(p−q)`; the integrand identity `1 + √B(z−1)/√B = z` by `field_simp; ring`),
  **`tendsto_mul_zVar`** (`B·Var_B(z^q) → q²/(p(p−q))`), `tendsto_negB`, **`tendsto_negVar_mul_rpow`**
  (`Var_{-b}(y^q) · y_b^{p−2q} → q²/(p(p−q))`) and **`tendsto_negVar_mul_rpow'`** (`Var_{-b}(y^q) · (qb/p)^{(p−2q)/(p−q)}
  → q²/(p(p−q))`, i.e. `h(−b) ~ K_{p,q} b^{β−1}` with `β = p/(2(p−q))`, `K_{p,q} = (q²/(p(p−q))) (q/p)^{(2q−p)/(p−q)}`).
  Gotchas: `← MeasureTheory.integral_const_mul` without arguments leaves the integrand's type a metavariable and the
  following `setIntegral_congr_fun` is stuck (`NormedSpace ℝ ?m`) — pass `(r) (f)` explicitly, then
  `apply setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ)))`; `intro z hz`; `dsimp only` before `rw`;
  `rw [pow_one]` hits `√B ^ 1` first, so state `zNum (fun z ↦ (z^q−1)^1) = zNum (fun z ↦ z^q−1)` separately;
  `fun_prop` has no theorems for `twoMonoPhi` — use `measurable_twoMonoPhi` explicitly.
- `NegativeChamberLaw.lean` (NOT mirrored; the `√t` chamber law): **`tendsto_intervalIntegral_div_rpow`** (power-law
  Cesàro: `g(u) u^{-γ} → L`, `γ > −1` ⇒ `(∫₀ᵗ g)/t^{γ+1} → L/(γ+1)`; mirror of `tendsto_intervalIntegral_div_log` with
  `integral_rpow (Or.inl hγ)`, `intervalIntegral.intervalIntegrable_rpow'`; take the tolerance `δ = ε(γ+1)/4` so that the
  remainder bound `δ (T−U)/(γ+1) ≤ ε T/4` does not depend on whether `γ+1 ≶ 1`; threshold `t ≥ (A·4/ε+1)^{1/(γ+1)}` via
  `Real.rpow_le_rpow` + `← Real.rpow_mul`), `mul_rpow_le_half_rpow_add` (`b y^q ≤ ½y^p + b(2b)^{q/(p−q)}`, case split at
  `Y₀ = (2b)^{1/(p−q)}`), `abs_profile_integrand_le` (uniform majorant on `c ≥ −b₁`), `integrableOn_profile'` (every
  coupling), **`continuous_profileNum`** (on all of `ℝ`, via `continuousOn_of_dominated` on `Ici (−(|c₀|+1))` and
  `ContinuousOn.continuousAt (Ici_mem_nhds …)`), `profileNum_one_pos'`, **`continuous_profileVar`**, `negBeta := p/(2(p−q))`,
  `negGamma := (2q−p)/(2(p−q))`, `negSpeedCoeff := (q/√(p(p−q)))(q/p)^γ`, `negChamberConst A := L A^β/β`,
  `negGamma_add_one`, `sigma_mul_negBeta` (`σβ = ½`), **`tendsto_sqrt_negVar_mul_rpow`** (`√Var_{-b}(y^q) b^{-γ} → L`),
  **`negative_chamber_law`**: `(∫_{−A}^{0} √fisherSpeed(twoMonoPath) t a da)/√t → K₋(A)` (window isometry with
  `c₀ = −A t^σ`, `c₁ = 0`; reflection `intervalIntegral.integral_comp_neg (f) (a := 0) (b := A t^σ)` then `rfl` for
  `√(V(−b)) = √(negVar b)`; `(A t^σ)^β = A^β √t` by `Real.mul_rpow`, `← Real.rpow_mul`, `Real.sqrt_eq_rpow`).
  Gotchas: `integrableOn_rpow_mul_exp_neg_mul_rpow` needs `(s := r) (b := 1/2)` when fed to `.mono'` (nothing else fixes
  them); `field_simp` closes `σβ = ½` outright once BOTH `p − q ≠ 0` and `−q + p ≠ 0` are in context; `div_add_one hc`
  for `a/c + 1`; a lemma `omit hq in` must be called without `hq`.
- `ProductPrior.lean` (NOT mirrored; Astra round 25 item 6): `sqrt_add_le_sqrt_add_sqrt` (all reals; `Real.sqrt_eq_zero'`
  for the negative cases, `Real.sqrt_le_left` + `nlinarith` otherwise), `mul_sqrt_add_mul_sqrt_le` (2D Cauchy–Schwarz
  `a√x + b√y ≤ √(a²+b²)√(x+y)`, via `Real.abs_le_sqrt` and `nlinarith [sq_nonneg (a√y − b√x)]`),
  `integral_sqrt_add_le` (`∫₀ᵗ√(V₁+V₂) ≤ ∫√V₁ + ∫√V₂`, `intervalIntegral.integral_mono_on ht hf hg` with
  `Continuous.comp_continuousOn` + `intervalIntegrable_of_Icc`), **`sqrt_sq_add_sq_le_integral_sqrt_add`** (Minkowski
  by scalar CS: `S := D₁² + D₂²`, `S = ∫(D₁√V₁ + D₂√V₂) ≤ √S ∫√(V₁+V₂)`, then divide by `√S`; a `rw [e]` with
  `e : S = ∫…` also rewrites the `S` under `√S` — use a `calc`), `prodPrior`, `sumLoss`, `prod_weight_eq`,
  `priorZ_prod` (`integral_prod_mul (f) (g)` — pass the factor functions explicitly, the pattern `?f z.1 * ?g z.2` is
  not a higher-order pattern), `prod_num_add`, `prod_num_sq` (integrability of the product integrands via
  `Integrable.mul_prod`; `[SFinite μ₁] [SFinite μ₂]`), `mean_ratio_alg`/`var_ratio_alg` (the ratio algebra on abstract
  reals — `field_simp` on the goal itself rewrites `exp(−(u L x))` into `exp(−(L x u))` inside ONE integrand and `ring`
  then sees two atoms), `priorExp_prod_add`, **`priorCov_self_prod`** (`Var_u(L₁+L₂) = Var_u(L₁) + Var_u(L₂)`),
  `radialLength_prod_eq`, **`radialLength_prod_le`** (`D ≤ D₁ + D₂`), **`sqrt_sq_add_sq_le_radialLength_prod`**
  (`√(D₁²+D₂²) ≤ D`, needs `0 ≤ Var_u(L_i)` on `[0,t]`). `priorCov` is stated with a product `φ*ψ`, not a square:
  match the algebra lemma's shape to `n/z * (n/z)`.
- `AffinityKL.lean` (NOT mirrored; Astra round 27 item 3): `relEnt_self` (`KL(p‖p) = 0`), `log_gibbsDensity_eq`,
  `affLoss_convex_comb` (affine in the parameter; prove the sum identity by `Finset.mul_sum` twice +
  `← Finset.sum_add_distrib` + termwise `ring`, then `ring` — a bare `simp only [add_mul, Finset.sum_add_distrib, …]; ring`
  leaves mismatched normal forms), `affJensenGap μ π L₀ R t θ a b := (1−θ)A(a) + θA(b) − A((1−θ)•a + θ•b)`,
  `affBhat … a b := (A a + A b)/2 − A((1/2)•(a+b))`, `convex_comb_half`, `affJensenGap_half`,
  `relEnt_integrand_convex_comb` (pointwise identity, `by_cases q x = 0`), `integrable_relEnt_integrand_convex_comb`,
  **`relEnt_convex_comb`** (`(1−θ)KL(q‖P_a) + θKL(q‖P_b) = KL(q‖P_θ) + C_θ`; lambda-typed `have h1` for the
  `integral_sub`), **`relEnt_midpoint`**, **`half_relEnt_sub_affBhat`** (`½KL(P_a‖P_b) − B = KL(P_a‖P_m)`; the
  `p_a log(p_a/p_a)` integrand is `(integrable_zero _ _ _).congr` with `Pi.zero_apply`), **`affBhat_le_half_add`**
  (via `relEnt_gibbsDensity_nonneg`), **`affBhat_eq_at_mid`**. Part B: `lawKL ν s u := (u−s)N₁(s)/Z(s) + log(Z u/Z s)`,
  `relEnt_lawDensity_eq_lawKL`, `tendsto_lawMoment_ratio_dilation` (`Z(du)/Z(cu) → (d/c)^{-λ}`, `Real.div_rpow`,
  `div_div_div_cancel_right₀`), **`tendsto_lawKL_dilation`** (`generalize` the two moment values before `field_simp`),
  **`tendsto_neg_log_lawAffinity_dilation`** (log identities: `Real.log_sqrt`, explicit `≠ 0` facts — `Real.log_mul (by
  norm_num) _` with a metavariable base fails), **`tendsto_endpoint_identity`** (`½KL(P_u‖P_0) + log ρ(0,u) → λ(log 2 − ½)`;
  do NOT `rw [one_div]` on a hypothesis whose function also contains `1/2` — rewrite `log (1/2)` with a `show`).
  Gotcha: `Filter.Tendsto.log` needs the limit `≠ 0`.
- `GlobalWallChart.lean` (NOT mirrored; Astra round 27 item 5, chart half): **`hasDerivAt_profileNum_all`** /
  **`hasDerivAt_profilePosterior_all`** (the wall response `∂_c⟨ψ⟩_c = −Cov_c(ψ, y^q)` for EVERY real `c`, via
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `Metric.ball c₀ 1` with the negative-side majorant
  `abs_profile_integrand_le` applied to `ψ y^q` (growth `r + q`) and `b₁ = |c₀| + 2`), **`profileVar_pos'`**
  (`Var_c(y^q) > 0` on all of `ℝ`; the variance-as-centred-second-moment identity needs the integrals folded to atoms
  BEFORE `field_simp`, and `simp only [one_mul] at hm ⊢` after `unfold profilePosterior profileNum at hm ⊢`),
  **`profileMean_strictAnti`** (`strictAnti_of_deriv_neg`), `continuous_profileMean`, `profileMean_pos`
  (`setIntegral_pos_iff_support_of_nonneg_ae` with the nonnegativity stated through `ae_restrict_iff'` — `y^q` is NOT
  nonnegative for `y < 0`), `tendsto_profileMean_atTop` (`m → 0`, from `tendsto_mul_profileMean`),
  `tendsto_profileMean_neg_div` (`⟨y^q⟩_{-b}/y_b^q → 1`, from `negA_eq` at `j = 0, 1`: `⟨z^q⟩_B − 1 = A₁/(√B A₀)`),
  `tendsto_profileMean_atBot` (`m → +∞`; `hy.atTop_mul_pos one_pos hlim`, `tendsto_neg_atBot_atTop`, `neg_neg` in
  the final simp), **`profileMean_bijOn`** (surjectivity onto `Ioi 0` through `log ∘ m` and `Continuous.surjective'`
  with `Real.tendsto_log_nhdsGT_zero` + `tendsto_nhdsWithin_iff`), `profileMeanPos`, **`profileMeanOrderIso : ℝ ≃o
  (Ioi 0)ᵒᵈ`** (`StrictMono.orderIsoOfSurjective`; `OrderDual.toDual_lt_toDual`, `Subtype.mk_lt_mk`,
  `OrderDual.ofDual.injective (Subtype.ext hc)`), **`profileMeanHomeomorph : ℝ ≃ₜ Ioi 0`** (`OrderIso.toHomeomorph` then
  `.trans ⟨OrderDual.ofDual, continuous_ofDual, continuous_toDual⟩`), `profileMeanHomeomorph_apply` (rfl),
  `continuous_profileMeanHomeomorph_symm`.
- `DataQuotient.lean` (NOT mirrored; Astra round 27 item 1): `priorExp_congr_ae'`, **`priorCov_self_eq_integral_sq`**
  (`Var = ∫(φ−m)² e^{-tL}π / Z`; fold the three integrals into atoms and `unfold priorZ at hZ` separately — `unfold
  priorCov … at hZ` fails when `hZ` has no `priorCov`), **`ae_eq_const_of_priorCov_self_eq_zero`**
  (`integral_eq_zero_iff_of_nonneg` + `mul_eq_zero`), `priorExp_const_fun`, `priorCov_self_eq_zero_of_ae_const`,
  `integrable_mul_affWeight_of_bdd` (from `tiltData_aff … a a t` + `TiltData.integrable_of_bdd hf t 0`, then
  `simp only [baseWeight, mul_zero, neg_zero, Real.exp_zero, mul_one]; ring`), `affZ_pos` (`.choose_spec.ν_pos`),
  **`responseForm_self_eq_zero_iff`** (`G_a(v,v) = 0 ↔ ∃ c, R_v =ᵐ c`), `responseForm_self_eq_zero_iff_of_ne`,
  **`gibbsDensity_eq_iff`** (`P_a = P_b ↔ ∃ c, ∀ x, R_{b−a} x = c`; `Real.log_injOn_pos (mem_Ioi.mpr hpa)
  (mem_Ioi.mpr hpb)`; the `priorZ` shift needs `dsimp only` before `rw [hL y]` under `integral_congr_ae`),
  `obsMapDeriv` (mirror of `meanMapDeriv` for one observable), **`hasFDerivAt_obsMap`**, **`obsMapDeriv_apply`**
  (`D_a⟨φ⟩[v] = −t Cov_a(φ, R_v)`), **`abs_obsMapDeriv_le`** (`≤ √Var_a(φ) √G_a(v,v)` via
  `TiltData.abs_tiltCov_le` and `← priorCov_eq_tiltCov_zero` three times), `continuous_obsMap`,
  `continuous_obsMapDeriv` (`ContinuousAt.inv₀`, `.smul`, `continuousAt_affNumDeriv`),
  **`abs_priorExp_sub_le_integral`** (path inequality; FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt`; the
  response form along the path as `t² ∑ᵢ γ'ᵢ ∑ⱼ γ'ⱼ Cov(Rⱼ, Rᵢ)` via `sum_mul_priorCov_eq` twice with the symmetry
  `Cov(R_i, R_v) = Cov(R_v, R_i)`; `Continuous.clm_apply`; `Continuous.intervalIntegrable (μ := volume) 0 1` — the bare
  `_ _` leaves `IsLocallyFiniteMeasure ?μ` stuck; state the FTC identity with the beta-reduced endpoints as a typed
  `have … := hftc` before `rw`, since `set F := fun s ↦ …` does not fold `F 1`).
- `LogPowGammaTails.lean` (NOT mirrored): `logPowGammaTrunc j r u := ∫₀ᵘ s^j e^{-s} (log s)^r`, `logPowGammaFull j r`,
  `log_le_rpow_div' (hy : 1 ≤ y) (ha : 0 < a) : log y ≤ y^a/a`, `abs_log_pow_le_rpow (hr : 1 ≤ r) : |log s|^r ≤ (2r)^r
  s^{-1/2}` on `(0,1]` (via `log s⁻¹ ≤ (s⁻¹)^{1/(2r)}·2r`, `Real.inv_rpow`, `← Real.rpow_natCast`, `← Real.rpow_mul`),
  `integrableOn_pow_mul_exp_neg_mul_log_pow_Ioc/Ioi` (dominate by `(2r)^r s^{-1/2}` near 0 — `intervalIntegrable_rpow'`
  — and by `s^{j+r}e^{-s}` beyond 1 via `log s ≤ s`), `intervalIntegrable_log_pow'` (all intervals, through
  `intervalIntegrable_of_even (fun x ↦ by simp [Real.log_neg_eq_log])` and the majorant `(2r)^r s^{-1/2} + x^r` on
  `Ioc 0 x`; `integrableOn_const measure_Ioc_lt_top.ne`), `intervalIntegrable_pow_mul_exp_neg_mul_log_pow`
  (`.continuousOn_mul`), **`logPowGammaTail_abs_le`** (`≤ (j+r+2)!/u²` from `gammaTail_le (j+r)`),
  `logPowGammaTrunc_eq`, **`abs_logPowGammaTrunc_sub_le`**, `logPowGammaFull_zero (= j!)`, `logPowGammaFull_one (=
  logGammaFull j)`, `continuous_logPowGammaTrunc`. Gotcha: a `(by fun_prop : Measurable …)` followed by
  `.aestronglyMeasurable` on the NEXT line parses as a separate term — write `Measurable.aestronglyMeasurable (by fun_prop …)`.
- `MultiplicityModelK.lean` (NOT mirrored; Astra round 27 item 4): `logModelMomentK k j u := ∫₀¹ ℓ^j e^{-uℓ} |log ℓ|^k`,
  `logModelJK k j u := ∑_{r ≤ k} C(k,r)(−1)^r (log u)^{k−r} Λ_{j,r}(u)`, **`logModelMomentK_eq`** (`N = u^{-(j+1)} J`;
  substitution `s = uℓ`, `|log ℓ|^k = (log u − log s)^k`, binomial `add_pow` after `sub_eq_add_neg, add_comm`, then
  `neg_pow` and `intervalIntegral.integral_finsetSum`), `priorZ_logModelK`, `priorExp_logModelK_one/two`,
  `logModelK_sq_mul_var` (`u²Var = J₂/J₀ − (J₁/J₀)²`), `logModelJK_div_pow` (`A_j = ∑ C(k,r)(−1)^r Λ_{j,r} τ^r`, `τ = 1/log u`;
  `x^k = x^{k−r} x^r` by `← pow_add, Nat.sub_add_cancel`), `logModelJK_div_pow'` (extended to `range (k+2)` by
  `Nat.choose_succ_self`), **`abs_sum_sub_linear_le`** (a polynomial in `τ ∈ [0,1]` minus its linear part is `≤ (∑|g_r|)τ²`;
  two `Finset.sum_range_succ'` peelings), `ratioConst`, **`ratio_expansion`** (`A/B = a₀/b₀ + ((a₁b₀ − a₀b₁)/b₀²)τ +
  O(τ²)` for `B ≥ b₀/2`; `obtain ⟨eA, rfl⟩ : ∃ e, A = a₀ + a₁τ + e`, the key identity by `eq_div_iff` + `field_simp` with
  BOTH spellings `b₀ + b₁*τ + eB ≠ 0` and `b₀ + τ*b₁ + eB ≠ 0` in context, then `abs_sub` chains and `div_le_div₀`),
  `sqConst`, **`sq_expansion`**, `logModelD`, **`logModelA_expansion`** (`|A_j − (j! − k M_{j,1} τ)| ≤ D_{j,k} τ²`; the
  instantiated `abs_sum_sub_linear_le` is already beta-reduced, so rewrite `↑(k.choose 0) * (-1)^0 * Λ₀` and
  `↑(k.choose 1) * (-1)^1 * Λ₁` with explicit equations, not the lambda forms), `logModelKT` (threshold),
  `logModelKC`, **`logModelK_var_bound`** (`log u ≥ 4·KT` ⇒ `x^k/2 ≤ J₀ ∧ |u²Var − (1 − k/log u)| ≤ KC/log² u`; the three
  expansions with common constant `D`, `A₀ ≥ ½`, two `ratio_expansion`s with `b₀ = 1`, `sq_expansion`, and the
  identity `(2 − 3kτ) − (1 − 2kτ) = 1 − kτ`), `logModelKC_nonneg` (from the bound at one admissible `u`),
  `logModelKS`, **`logModelK_speed_bound`** (`abs_of_nonneg (by positivity : (0:ℝ) ≤ …)` — a bare `by positivity`
  inside `rw` runs on a metavariable), `continuousOn_logModelJK` (`continuousOn_finsetSum`; `continuousOn_finset_sum`
  is deprecated), **`logModelK_length_renormalised`**: `∃ u₀ > 1, ∃ K, ∫_{u₀}^t √Var_u − (log t − (k/2) log log t) → K`.
  Numerics: residual × log²u ∈ [−0.8, 0.6] for k = 1,2,3 up to u = 10¹².
- `TwoValuedGeodesic.lean` (NOT mirrored; Astra round 27 item 2, computable core): `twoValued_of_quadratic` (`X² − v = cX`
  a.e., `v ≥ 0` ⇒ `X ∈ {(c ± √(c²+4v))/2}` a.e.; `quadratic_eq_zero_iff one_ne_zero hd` with `discrim` unfolded),
  `quadratic_of_twoValued`, `twoAtom p q α β := ofReal p • dirac α + ofReal q • dirac β`, `integral_twoAtom`
  (`integral_add_measure` with `(integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top`, `integral_smul_measure`,
  `integral_dirac`, `ENNReal.toReal_ofReal`), `atomWeight` (`w_u`), `twoAtomZ`, `lawMoment_twoAtom_zero`,
  `lawExp_twoAtom`, `atomWeight_pos/lt_one`, **`lawVar_twoAtom`** (`(β−α)² w(1−w)`), **`hasDerivAt_atomWeight`**
  (`w' = (β−α)w(1−w)`; state `hZ'`/`hdiv` with lambda types — `hN.div (hN.add hM)` is Pi-form and `field_simp` then sees
  `((fun …) + fun …) u` atoms), `continuous_atomWeight`, `atomWeight_monotone` (`monotone_of_deriv_nonneg`), `atomAngle :=
  arcsin √w` (`omit hp hq in` for the range lemmas), `sin_atomAngle`, `cos_atomAngle` (`Real.cos_arcsin` + `Real.sq_sqrt`),
  **`hasDerivAt_two_atomAngle`** (`d(2θ)/du = √Var`; `Real.hasDerivAt_arcsin (hx1 : x ≠ −1) (hx2 : x ≠ 1)` composed with
  `HasDerivAt.sqrt`; `Real.sqrt_eq_one`; then `set a := √w, b := √(1−w)`, `rw [← ha2] at hb2 ⊢; rw [← hb2]; field_simp`),
  `continuous_sqrt_lawVar_twoAtom`, **`twoAtom_length_eq`** (`∫_s^t √Var = 2θ_t − 2θ_s`, FTC), **`lawAffinity_twoAtom`**
  (`ρ = √(w_s w_t) + √((1−w_s)(1−w_t))`; rewrite `atomWeight` by `show … from rfl` so `Real.sqrt_div' _ hZst.le` sees the
  folded `twoAtomZ`; `unfold … at *` inside a `have` MUTATES the outer hypotheses — use `at this ⊢`),
  `lawAffinity_twoAtom_eq_cos` (`Real.cos_sub`), **`twoAtom_length_eq_two_arccos`** (`Real.arccos_cos` with
  `0 ≤ θ_t − θ_s ≤ π` from `Real.monotone_arcsin` and the range lemmas), `twoAtom_two_arccos_affinityExp_eq` (equality case
  of `two_arccos_affinityExp_le`).
- `WallPhaseDiagram.lean` (NOT mirrored; Astra round 28 §1.3 synthesis): **`tendsto_intervalIntegral_dilation`** (`c h(c) → L`,
  `h` continuous on `(0,∞)` ⇒ `∫_{aT}^{bT} h → L log(b/a)`; substitution `integral_comp_mul_left (f := h)`, then
  `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` with the constant bound `(|L|+1)/a` on
  `Ι a b = uIoc a b` (`uIoc_of_le`, `ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc`), and `integral_inv_of_pos`
  — do NOT `simp_rw [div_eq_mul_inv]` on the goal, it also rewrites `log (b/a)`; use a `funext` equation),
  `continuous_sqrt_fisherSpeed_twoMono` (via the identity `√g_t(a) = t^σ √Var(a t^σ)` of `wall_window_length`'s proof),
  **`wall_phase_positive`** (`0 < a ≤ b`: `ℓ_t(a,b) → √(1/q) log(b/a)`), **`wall_phase_wall`** (`wall_recedes` at `c₀ = 0`,
  `simpa only [zero_mul]`), **`wall_phase_negative`** (`a < 0 < b`: `ℓ_t(a,b)/√t → K₋(−a)`; split at `0` with
  `integral_add_adjacent_intervals`, `log t/√t → 0` from `isLittleO_log_rpow_atTop (1/2)` + `Real.sqrt_eq_rpow`),
  **`tendsto_ray_length_dilation`** (`∫_{cu}^{du} √Var_v → √λ log(d/c)`; `continuousOn_lawVar` needs `K ≥ 3`).
- `QuotientMeanMap.lean` (NOT mirrored; Astra round 28 item 1, core): `invisibleSet μ R := {v | ∃ c, R_v =ᵐ c}`,
  `dirLoss_zero`, `hasDerivAt_affineLine (a v s) : HasDerivAt (fun s ↦ a + s • v) v s` (`simpa using ((hasDerivAt_id (s :
  ℝ)).smul_const v).const_add a`; needs `set_option linter.unusedFintypeInType false in` — the Pi norm needs `Fintype`),
  **`invisibleSubmodule`** (`Submodule ℝ (ι → ℝ)` with `dirLoss_add`/`dirLoss_smul`), `priorExp_congr_loss_ae`,
  `priorExp_const_add'`, **`priorExp_affLoss_add_of_invisible`** / **`meanMap_add_of_invisible`** (`M(a+k) = M(a)`),
  `sum_mul_meanMap_of_invisible` (`⟨k, M(a)⟩ = c`, via `priorExp_dirLoss` + `priorExp_congr_ae'` + `priorExp_const_fun`),
  **`dot_meanMap_sub_of_invisible`**, **`meanMap_eq_iff_invisible`** (`M a = M b ↔ b − a ∈ K`; `⇒` is the
  `meanMap_injective` argument with `hnd` derived from `π > 0`, `⇐` invariance), `priorCov_self_nonneg'`,
  **`dot_meanMap_sub_eq_integral`** (`⟨M(b)−M(a), b−a⟩ = −t∫₀¹ Var_{a+s(b−a)}(R_{b−a})`; chain rule
  `HasFDerivAt.comp_hasDerivAt` needs the `HasFDerivAt` fact named first and then `exact h` — inline it fails to unify
  `?l ∘ f` with the lambda; every `fun s ↦ … s • v` binder must be typed `s : ℝ` or `HSMul` is stuck; add `Pi.sub_apply`
  to the final simp), **`dot_meanMap_sub_neg`** (`< 0` off `K`; `intervalIntegral_pos_of_pos_on`). NOT built: the
  `K^⊥`-restricted open embedding (Lean plumbing over `MeanMapChart`).
- `InteriorMinimumTwoMono.lean` (NOT mirrored; Astra round 28 item 2, two-monomial instance): `interiorMin p q a := negScale p q
  (−a)` (`x_a = (q|a|/p)^{1/(p−q)}`), `interiorHess := p(p−q) x_a^{p−2}`, `interiorMin_rpow` (`x_a^r = (q(−a)/p)^{r/(p−q)}`),
  `hasDerivAt_interiorMin` (`x_a' = −q x_a^{q−1}/H_a`, from `Real.hasDerivAt_rpow_const` composed with the affine inner map),
  **`sqrt_interiorHess_mul_abs_deriv`** (`√H_a |x_a'| = k₋ (−a)^{negGamma}`; the `(p−2)/2`-power bookkeeping goes through
  `x^{(p−2)/2} x^{q−1} = x^{(2q−p)/2} x^{p−2}` and `x^{(2q−p)/2} = (q/p)^γ (−a)^γ`; fold `√(p(p−q))` into an opaque `s` with
  `set … clear_value` and rewrite `p(p−q) = s²` BEFORE `field_simp`, never `← hsq` which also rewrites inside the radical),
  `negChamberConst_eq_integral` (`K₋(A) = ∫₀ᴬ k₋ s^γ ds`, `integral_rpow` + `negGamma_add_one`),
  **`integral_sqrt_interiorHess_mul_abs_deriv`** (`∫_{a₀}^{a₁} √H_a|x_a'| = K₋(−a₀) − K₋(−a₁)`, via `integral_comp_neg` and
  `integral_interval_sub_left`), **`tendsto_fisherSpeed_div_interior`** (`fisherSpeed t a / t → (q x_a^{q−1})²/H_a` for `a < 0`:
  rescaling `fisherSpeed t a = (t^σ)² negVar(−a t^σ)`, `(q b/p)^e` with `b = −a t^σ` splits by `Real.mul_rpow`, and the exponent
  identity `(t^σ)^e = (t^σ)²/t` (`σ e = 2σ − 1`, `e = (p−2q)/(p−q)`) closes with `mul_div_cancel_left₀`, NOT `field_simp`),
  `wall_phase_negative_pair` (`ℓ_t(a₀,a₁)/√t → K₋(−a₀) − K₋(−a₁)` for `a₀ ≤ a₁ < 0`), **`interior_minimum_length`**
  (`ℓ_t(a₀,a₁)/√t → ∫_{a₀}^{a₁} √H_a |x_a'| da`). One-liner `have hX : … := by have : … := by linarith; positivity` nests the
  `positivity` inside the inner `by` — split into two `have`s. Astra's second-order wall coefficient
  `Var_B(√B(z^q−1)) = q²/(p(p−q)) + q²(p−2)/(2p²(p−q))/B + O(B⁻²)` was CONFIRMED numerically for (4,2), (3,1), (5,2) (not yet
  formalised; it is the input of the two-term wall law).
- `RayChart.lean` (NOT mirrored; Astra round 28 items 5 and 6, algebraic core): `lawMean ν u := N₁/Z`, `lawFree ν u := log Z(u)`,
  **`lawVar_eq_integral_sq`** (`Var_u = Z⁻¹∫(ℓ−m)²e^{−uℓ}`; from `integral_sq_sqrt_speed` after rewriting the integrand by
  `mul_pow, Real.sq_sqrt` and `integral_const_mul, integral_div`), `integrable_sq_sub_mul_exp`, `lawVar_nonneg`,
  **`lawVar_pos`** (hypothesis `¬ ∃ c, ∀ᵐ ℓ ∂ν, ℓ = c`; `integral_pos_iff_support_of_nonneg_ae` + `pos_iff_ne_zero` +
  `ae_iff` + `measure_mono_null` into `Function.mem_support`), `hasDerivAt_lawMean'`/`hasDerivAt_lawFree` (wrappers of
  `RadialCurvature` at `K = 2`), `lawMoments_at` (`omit hpos hZ in`), `lawMean_antitoneOn` (`antitoneOn_of_deriv_nonpos
  (convex_Ioi 0)`, `interior_Ioi`, `HasDerivAt.deriv`), **`lawMean_strictAntiOn`** (`strictAntiOn_of_deriv_neg`),
  `ordConnected_image_lawMean` (`isPreconnected_Ioi.image` + `isPreconnected_iff_ordConnected`), **`exists_rayChart`**
  (`∃ e : Ioi 0 ≃ₜ (lawMean ν '' Ioi 0), e u = m u`: `StrictMonoOn.orderIso` of `−m`, `.toHomeomorph` once the image is
  `OrdConnected` (instance `orderTopology_of_ordConnected` fires from a plain `have`), then `(Homeomorph.neg ℝ).image _` and
  `Homeomorph.setCongr` with `Set.image_image`; the final coercion goal is `change -(-(m u)) = m u`), **`lawFree_convexOn`**
  (`MonotoneOn.convexOn_of_deriv`), **`lawFree_ge_tangent`** (`ConvexOn.le_slope_of_hasDerivAt`/`slope_le_of_hasDerivAt` +
  `slope_def_field` + `le_div_iff₀`), **`lawKL_zero_eq_legendre`** (`KL(P_u‖P_0) = −u m(u) − F(u) + F(0)`; `omit hpos hint in`),
  **`legendre_isMaxOn`** (`IsMaxOn (fun v ↦ −m(u)v − F v) (Ioi 0) u`), `lawKL_zero_ge_legendre`.
- `NaturalCoordinates.lean` (NOT mirrored; Astra round 29 item 1): `jointStat L₀ R : Option ι → X → ℝ` (`none ↦ L₀`),
  `natCoord t a = (t, t a)`, `natTangent t a s v = (s, a s + t v)`, `dataDir v = (0, v)`;
  `dirLoss_jointStat_natCoord` (`Fintype.sum_option`, `Option.elim`, `Finset.mul_sum`), `affLoss_zero_jointStat_natCoord`
  (`affLoss 0 S (Θ t a) = fun x ↦ t L_a x + 0`, the shape `priorExp_smul_add` wants), `dirLoss_jointStat_dataDir`,
  `dirLoss_jointStat_natTangent`, `natCoord_eq_smul` (`omit [MeasurableSpace X] [Fintype ι] in`), `bdd_jointStat`
  (`omit [Fintype ι]` only — `Bdd` references the measurable structure), **`dataDir_mem_invisibleSet_iff`**,
  **`invisible_temperature_dir`** (joint invisible `(s,v)` with `s ≠ 0` ⇒ `L₀ =ᵐ c − R_{v/s}`), **`priorExp_natCoord`**,
  `priorZ_natCoord`, `priorCov_natCoord`, `affLogZ_natCoord`, `meanMap_natCoord_some/none`,
  **`responseForm_natTangent`** (`g_{Θ}(DΘ(s,v), DΘ(s,v)) = Var_{t,a}(s L_a + t R_v)`), `lawMean_lossLaw_eq`
  (`m(u) = ⟨L_a⟩_{u,a}` via `priorExp_comp_eq_lawExp` at `f = id`; measurability of `affLoss` is `hL₀m.add (bdd_dirLoss hR a).1`),
  **`natKL_eq`** (Bregman in natural coordinates: `mixKL_aff_eq` at `L₀ = 0`, `t = 1`; pass `h0 : ∀ x, |(fun _ ↦ 0) x| ≤ 0`
  as a named `have`, or the `M₀` metavariable is never solved), **`natKL_natCoord`** (slice KL = joint KL),
  **`hasDerivAt_affLogZ_line`** (line derivative of `A_t` at EVERY point: `TiltData.hasDerivAt_affLogZ_dir` at base
  `a + s•v` built with `tiltData_baseWeight_of_bounded … measurable_const (fun _ ↦ by simp)`, shifted by
  `HasDerivAt.comp_sub_const s s` after `rw [sub_self]`, then `congr_of_eventuallyEq` + `change` + `congr 1` + `module`),
  `priorExp_dirLoss_eq_dot`, **`natKL_zero_eq_integral`** (`KL(P_θ‖P_0) = ∫₀¹ s Var_{sθ}(S_θ) ds`: primitive
  `g(s) = ψ(0) − ψ(sθ) − s D(s)`, `hasDerivAt_const s (explicit constant)` — an underscore is not inferred —,
  integrand continuity through `continuous_obsMapDeriv` + `clm_apply`, FTC `integral_eq_sub_of_hasDerivAt`, and the
  final bookkeeping needs `Pi.zero_apply` for `(0 : Option ι → ℝ) j`), **`lawMean_eq_dot_meanMap`**
  (`⟨L_a⟩_{u,a} = η₀ + a·M` as the joint mean map on the ray). Astra round 29 (`gpt_responses/research_round29_{q,v1}.md`):
  ranking (1) joint family [DONE here], (2) `N^⊥` open-embedding packaging + featureless anchor [anchor DONE],
  (3) ray Cramér curvature `I(x) = −x u(x) − F(u(x))`, `I' = −u`, `I'' = 1/Var`, (4) ess-inf endpoint without regular
  variation (`m(u) → α` from `ν{ℓ < α+ε} > 0`, lemma `sup_{y≥ε} y e^{−ry} = ε e^{−rε}`) + finite-alphabet endpoint
  distribution, (5) moment-polytope image theorem, (6) two-term wall law (full coefficient derivation §4: `c₁ = n₂ − h₁²`,
  odd orders vanish by parity, `O(B⁻²)` needs the order-3 weight polynomial), (7) abstract moving-minimum theorem.
  Warnings: the joint kernel `N ⊋ {0}×K` unless `L₀ ∉ span{1,R}`; the `t > 0` mean image need NOT be convex (three-atom
  counterexample); the dual coordinate is `(⟨L₀⟩, M)`, not `(⟨L_a⟩, M)`; Bregman parameter order is reversed.
- `RayCramer.lean` (NOT mirrored; Astra round 29 item 3): `rayInv ν := Function.invFunOn (lawMean ν) (Ioi 0)`,
  `rayRate ν x := −x u(x) − F(u(x))`; section `(hint : ∀ v > 0, ∀ k ≤ 3, …)` with `hint2` (`omit hpos hZ hnd in`) for the `K = 2`
  lemmas, `continuousOn_lawVar'`; `rayInv_lawMean` (`StrictAntiOn.injOn.leftInvOn_invFunOn`), `rayInv_pos`/`lawMean_rayInv`
  (`Function.invFunOn_mem/_eq`; `omit hpos hint hZ hnd in`), **`isOpen_image_lawMean`** (`isOpen_iff_mem_nhds`; window
  `Ioo (m(2u)) (m(u/2))` via `intermediate_value_Ioo'` on `Icc (u/2) (2u)`), `rayInv_antitoneOn` (contrapositive of strict
  antitonicity; `absurd this (not_lt.2 hxy)`), **`continuousAt_rayInv`** (`continuousAt_of_monotoneOn_of_image_mem_nhds` applied
  to `−u`, image ⊇ `Iio 0`; there is NO antitone variant; convert back with `ContinuousAt.congr` + `Eventually.of_forall … simp`,
  since `simp only [neg_neg] at h` does not see through the Pi negation), **`hasDerivAt_rayInv`**
  (`HasDerivAt.of_local_left_inverse`, `u' = (−Var)⁻¹`), `continuousOn_rayInv`, `rayRate_lawMean`, **`rayRate_lawMean_eq_lawKL`**
  (`I(m(u)) = KL(P_u‖P_0) − F(0)`), **`rayRate_isMaxOn`** (Cramér sup attained at `u(x)`), **`hasDerivAt_rayRate`** (`I' = −u`;
  the product/chain-rule derivative carries `(-id) x` — `simp only [Pi.neg_apply, id_eq]` before `ring`),
  **`hasDerivAt_deriv_rayRate`** (`I'' = 1/Var_{u(x)}`, via `deriv` eventually equal to `−u` on the open image),
  `rayRate_convexOn` (`MonotoneOn.convexOn_of_deriv` on the `OrdConnected` image, `.convex`, `IsOpen.interior_eq`),
  **`lawLength_eq_integral_sqrt_curvature`** (`∫_{u₀}^{u₁} √Var = ∫_{m u₁}^{m u₀} √(1/Var(u(x))) dx`:
  `intervalIntegral.integral_comp_mul_deriv'` with `f = m`, `f' = −Var`, `g = √(1/Var∘u)`; pass
  `intervalIntegral.integral_symm (m u₀) (m u₁)` with explicit arguments or it rewrites the LEFT integral; pointwise
  `√(V⁻¹)·V = √V` by `Real.sqrt_inv, mul_neg, inv_mul_eq_div, eq_div_iff, Real.mul_self_sqrt`).
- `RayEndpoint.lean` (NOT mirrored; Astra round 29 item 4): **`mul_exp_le_of_le`** (`y e^{−ry} ≤ ε e^{−rε}` for `ε ≤ y`,
  `1/ε ≤ r`, from `Real.add_one_le_exp (r(y−ε))`), section `(hint : ∀ v > 0, ∀ k ≤ 1, …) (hα : ∀ᵐ ℓ, α ≤ ℓ)
  (hmass : ∀ ε > 0, 0 < ν {ℓ | ℓ < α + ε})`; `integrable_exp_tilt`, `integrable_mul_exp_tilt`, `lawMoment_zero_pos'`
  (positivity of `Z` from mass: `integral_pos_iff_support_of_nonneg_ae`, `support = univ` by `ext ℓ; simp [(exp_pos _).ne']`
  — `Function.support_eq_univ` does NOT exist), `lawMean_sub_eq` (`m(u) − α = ∫(ℓ−α)e^{−uℓ}/Z`; `omit hα hmass in`, and the
  implicit `α` must be passed `(α := α)` at call sites), `le_lawMean` (`α ≤ m(u)`), **`lawMean_sub_le`** (the tilt estimate
  `m(u) − α ≤ ε + (εW/c_ε) e^{−(u−1)ε/2}` for `u ≥ 1 + 1/ε`: pointwise a.e. bound by cases `ℓ − α ≤ ε` / `> ε` with
  `mul_exp_le_of_le` and the factorisation `e^{−uℓ} = e^{−r(ℓ−α)} e^{−rα} e^{−ℓ}`, `integral_mono_ae`; denominator
  `Z ≥ e^{−r(α+ε/2)} c_ε` by `setIntegral_mono_on` + `setIntegral_le_integral`; `c_ε > 0` via
  `setIntegral_pos_iff_support_of_nonneg_ae` and `measure_mono` from `hmass (ε/2)` — the membership needs
  `show ℓ < α + ε/2 from hℓ`; a one-line `have … := by rw [hr]; have : … := by positivity; linarith` nests the `linarith`
  in the inner `by` — split it; after `unfold lawMoment; simp only [pow_zero, one_mul]` the `set` variable `W` is folded by
  `rfl`), **`tendsto_lawMean_atTop`** (`tendsto_order`; `ε := (b−α)/3`; `Tendsto.atTop_div_const (r := 2)` — without the
  named `r` the unifier picks `ε`; `simp only [id_eq]` before `ring` in the `congr`).
- `FiniteEndpoint.lean` (NOT mirrored; Astra round 29 §5 "finite-alphabet face endpoints"): finite `X` with
  `Measure.count` (needs `[MeasurableSingletonClass X]` for `integral_count`, which is `@[simp]`); `groundAvg π L φ m₀ :=
  (∑_{L = m₀} φ π)/(∑_{L = m₀} π)`; hypotheses `(hπ : ∀ x, 0 < π x) (hm₀ : ∀ x, m₀ ≤ L x) (hex : ∃ x, L x = m₀)` (the ground
  level is a hypothesis — `Finset.inf'`/`exists_mem_eq_inf'` were not worth the plumbing); `ground_filter_nonempty`,
  `ground_sum_pos` (`Finset.sum_pos`), `tendsto_tilt_weight` (`c x e^{−r(L x − m₀)} → if L x = m₀ then c x else 0`;
  `omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] hπ hex in`), `tendsto_tilt_sum` (`Finset.sum_filter` +
  `tendsto_finsetSum`), `priorExp_count_eq` (ratio of tilted sums; `mul_div_mul_left` with `c = e^{r m₀}` and the per-term
  identity `e^{rm₀} e^{−rL} = e^{−r(L−m₀)}` — pass `(m₀ := m₀)` at call sites), **`tendsto_priorExp_atTop_finite`**
  (`⟨φ⟩_r → E_π[φ | L = min]`; `Tendsto.div` + `congr'` with `Pi.div_apply`), **`tendsto_gibbsDensity_atTop_finite`**
  (`φ = 1_{x}`, `Finset.sum_eq_single`), `priorExp_natural_ray` (`affLoss 0 S (r•h) = r · S_h`, `priorExp_smul_add`; the
  ray parameter MUST be typed `fun r : ℝ ↦ …` or `atTop` has a stuck `Preorder ?m`), **`tendsto_priorExp_natural_ray`**,
  **`tendsto_meanMap_natural_ray_finite`** (`M(rh) → E_π[S | S_h = min S_h]`: natural directions select faces of the moment
  polytope, the prior resolves ties on the face).
- `MomentPolytope.lean` (NOT mirrored; Astra round 29 item 5): finite alphabet, `Measure.count`, `[Nonempty X] [Nonempty J]`,
  `set_option linter.unusedFintypeInType false` file-wide (count/integral_count need `Fintype X` invisibly); `statPoint S x :=
  fun j ↦ S j x`, `dotJ θ y := ∑ θ_j y_j` (`isLinearMap_dotJ`, `dotJ_add_left`, `dotJ_smul_left`, `dotJ_single_left`),
  `piMin π := univ.inf' … π` (`piMin_le` = `Finset.inf'_le`, `piMin_pos` = `(Finset.lt_inf'_iff _).2`), finite-alphabet
  instances of the affine hypotheses (`count_hπpos`, `bdd_finite` via `Finset.exists_max_image`, `zero_bdd`, `hnd_count` via
  `Measure.ae_count_iff`), `meanMap_eq_sum_weights`, `priorZ_count_pos`, **`meanMap_mem_convexHull`** (`Convex.sum_mem`),
  **`affLogZ_ge_of_mem_convexHull`** (`ψ(θ) ≥ log π_min − ⟨θ,y⟩` on the polytope: `convexHull_min` into the half-space
  `convex_halfSpace_ge (isLinearMap_dotJ θ)`; atoms via `Finset.single_le_sum` + `Real.log_le_log`), **`coercive_bound`**
  (`ψ(θ) + ⟨θ,x⟩ ≥ log π_min + (δ/2)‖θ‖` when `ball x δ ⊆ conv`: test point `y = x − (δ/2) sgn(θ_{j₀}) e_{j₀}` with the
  max-modulus coordinate; `sgn` as an `if`, NOT `SignType`; the test point via `obtain ⟨y, hy⟩ : ∃ y, y = …` not `set`),
  `continuous_affLogZ_count`, `continuous_dotJ_left`, **`exists_min_variational`** (`Continuous.exists_forall_le` +
  `tendsto_atTop_mono` + `tendsto_norm_cocompact_atTop.const_mul_atTop`), **`meanMap_eq_of_min`** (first-order condition:
  `IsLocalMin.hasDerivAt_eq_zero` along `e_j` with `TiltData.hasDerivAt_affLogZ_dir'`),
  **`range_meanMap_eq_interior_convexHull`** (`interior_maximal` + `isOpen_range_meanMap` for `⊆`; variational argument
  for `⊇`). GOTCHA (cost a bisection): `pi_norm_le_iff_of_nonneg'`, `tendsto_norm_cocompact_atTop'` and the other PRIMED
  norm lemmas are the MULTIPLICATIVE (`SeminormedGroup`) versions — using them on `J → ℝ` produces `(deterministic) timeout
  at whnf/isDefEq` with no other symptom; the additive names are the unprimed ones.
- `SegmentDivergence.lean` (NOT mirrored; Astra round 30 item 3): `sq_integral_sqrt_le_integral` (`(∫₀¹√f)² ≤ ∫₀¹ f`
  by AM–GM with a free weight `λ = √(∫f + ε)` and `le_of_forall_pos_le_add`), `segVar μ π L₀ R t a v s :=
  Var_{a+sv}(R_v)`, `hasDerivAt_segMean` (`d/ds ⟨R_v⟩_{a+sv} = −t V(s)`; NOT `omit ht` — the obsMap lemmas need `0 < t`),
  `continuous_segVar` (through `continuous_obsMapDeriv`), `segVar_nonneg`, **`mixKL_eq_integral_mul_var`**
  (`KL(P_b‖P_a) = t²∫₀¹ s V`; primitive `A(a) − A(a+sv) − t s D(s)`), **`mixKL_eq_integral_one_sub_mul_var`**
  (`KL(P_a‖P_b) = t²∫₀¹(1−s)V`; primitive `A(a+sv) − A(a) − t(1−s)D(s) + tD(0)` — the sign of the last two terms was
  wrong on the first attempt; finish by `simp only [one_smul, zero_smul, …, hv]` FIRST, then
  `rw [priorExp_dirLoss_eq_dot … a (b − a)]`), `segmentLength := t∫₀¹√V`, **`sq_segmentLength_le_jeffreys`**
  (`Length² ≤ KL(a‖b) + KL(b‖a)`; typed `IntervalIntegrable (fun s ↦ …)` facts for `integral_add`),
  **`mixKL_three_point`** (`KL(a‖b) − KL(a‖c) − KL(c‖b) = t⟨b−c, m(a)−m(c)⟩`, pure algebra on `mixKL_aff_eq`),
  **`mixKL_pythagoras`**, `hasDerivAt_mixKL_line` (`d/ds KL(P_a‖P_{c+sv}) = t⟨v, m(a) − m(c+sv)⟩`; lambdas must be typed
  `fun s : ℝ ↦` or `s • v` picks `ℕ`; `neg_mul` + `Finset.sum_neg_distrib` in the final simp),
  **`orthogonal_of_isMinOn_line`** (first-order condition of an information projection onto a line gives
  `⟨v, m(a) − m(c)⟩ = 0`). Astra round 30 (`gpt_responses/research_round30_{q,v1}.md`): CORRECTIONS — the wall family
  `(x^p, x^q)` on `(0,∞)` is NON-STEEP: natural domain `{θ₁ > 0} ∪ {θ₁ = 0, θ₂ > 0}`, mean image the curved band
  `{v^r < u ≤ C_Γ v^r}` (r = p/q, `C_Γ = Γ(k+r)/(Γ(k)k^r)`, k = 1/q), a PROPER subset of the convex support
  `{u ≥ v^r}`; the wall is the homogeneous curve `u = C_W v^r` splitting the band; temperature rays have `√κ_a log T`
  Fisher length in ALL three chambers (`κ_a = 1/q, 1/p, 1/2`), the three-regime law concerns data segments at fixed `t`;
  `L² ≤ 2KL` is FALSE (Bernoulli tilt: `L → π/2`, `KL → log 2`), the correct bound is Jeffreys. Ranking: (1) bounded-
  statistic moment-body theorem `range η = int cl conv (essRange S)` via a uniform positive-mass cap lemma, (2) full
  mean-coordinate potential (inverse chart, `I = ψ*(−m)`, `∇I = −θ`, `D²I = G⁻¹`, dual Bregman, path-length transport),
  (3) segment identities [DONE here], (4) fixed-temperature image as the graph `η₀ = h_t(M)` = level set `∂_{η₀}I = −t`,
  reduced potential `J_t(M) = inf_e (I(e,M) + te) + ψ(t,0)`, (5) `N^⊥`, (6) the wall mean band, (7) two-term wall law
  (little-`o` variance lemma suffices; `c₁ = (h₂²/2 + h₁h₃)/λ² − (2h₁h₂μ₃ + h₁²μ₄/2)/λ³ + h₁²μ₃²/λ⁴`), (8) abstract
  moving minimum.
- `EssentialRange.lean` + `MomentBody.lean` (NOT mirrored; Astra round 30 item 1): `priorMeasure μ π := μ.withDensity (ofReal π)`,
  `essRange μ π S := ((priorMeasure μ π).map (statPoint S)).support` (Mathlib `Measure.support`), `momentBody := closure
  (convexHull ℝ essRange)`; `priorMeasure_eq_zero_iff` (`withDensity_apply_eq_zero'`, positive density),
  **`ae_statPoint_mem_essRange`** (`Measure.measure_compl_support` — needs `HereditarilyLindelofSpace (J → ℝ)`, hence
  `[Fintype J]` stays although the type does not mention it: `set_option linter.unusedFintypeInType false in`; `unfold essRange
  at h0 ⊢` before `Measure.map_apply`), `mem_essRange_iff` (`Metric.nhds_basis_ball.mem_measureSupport`), `setIntegral_pi_pos`,
  `continuous_dotJ_right`, `abs_dotJ_le` (`|⟨e,y⟩| ≤ (∑|e_j|)‖y‖` via `norm_le_pi_norm`), `one_le_sum_abs_of_norm_eq_one`,
  `sum_abs_le_card_of_norm_le_one`, **`exists_far_point`** (for `ball x δ ⊆ body` and `‖e‖ = 1`: `∃ y₀ ∈ essRange, δ/2 ≤ ⟨e, x − y₀⟩`;
  contrapositive through the closed half-space `{⟨e,x⟩ − δ/2 ≤ ⟨e,y⟩}` and the test point `x − (3δ/4) sgn(e)`),
  **`cap_lemma`** (`∃ c > 0, ∃ m > 0, ∀ ‖e‖ = 1, m ≤ ∫_{⟨e, x − S⟩ ≥ c} π`: far point + ball of radius `δ/(4n)` + perturbation
  radius `δ/(8n(‖x‖+K+1))` + `isCompact_sphere` with `IsCompact.elim_nhds_subcover'` + `Finset.inf'` over the finite subcover;
  the mass function must be typed `(J → ℝ) → ℝ` and the subcover elements coerced `(e : J → ℝ)`); `affLoss_zero_eq_dotJ`,
  **`mean_mem_momentBody`** (`geometric_hahn_banach_point_closed`, `pi_eq_sum_univ'` + `map_sum`/`map_smul` for the functional in
  coordinates, `priorExp_dirLoss`, `integral_mono_ae`), `measurable_cap`, **`coercive_bound_general`** (`c‖θ‖ + log m ≤ ψ(θ) +
  ⟨θ,x⟩`; direction `e = ‖θ‖⁻¹ • θ` or `Pi.single j₀ 1` when `θ = 0`, `setIntegral_mono_on` + `setIntegral_le_integral`),
  `continuous_affLogZ_general` (from `hasFDerivAt_affNum` at `φ = 1`), `exists_min_variational_general`
  (`tendsto_norm_cocompact_atTop.const_mul_atTop`), `meanMap_eq_of_min_general`,
  **`range_meanMap_eq_interior_momentBody`** (`hnd` in the a.e. form of `MeanMapEmbedding`).
- `DualPotential.lean` (NOT mirrored; Astra round 30 item 2): `dotCLM y := ∑ y_j • proj j` (`dotCLM_apply : dotCLM y v = dotJ v y`),
  **`hasFDerivAt_affLogZ`** (`DA(a₀) = −t • dotCLM (m a₀)`: `hasFDerivAt_affNum` at `φ = 1`, `.log`, `congr_fderiv`, `ext v`,
  `affNum_fderiv_apply`; identify `dotJ v (m a₀)` with `priorExp (dirLoss R v)` by `change` + `priorExp_dirLoss` + `rfl`),
  `dualPotential μ π L₀ R t y := −t⟨θ(y), y⟩ − A(θ(y))` with `θ = Function.invFun (meanMap …)`, `dualPotential_meanMap`,
  **`mixKL_eq_bregman_dual`** (`KL(P_b‖P_a) = I(m_b) − I(m_a) + t⟨a, m_b − m_a⟩`; finish with a SECOND `simp only [neg_mul,
  Finset.sum_neg_distrib]` pass — inside one simp set the lemma never fires), `invJac` (`(meanMapDerivEquiv …).symm` as a CLM),
  `invJac_meanMapDeriv` (from `meanMapInverse_deriv_comp`), **`hasFDerivAt_dualPotential`** (`DI(m a) = −t • dotCLM a`; chain
  rule on `hasStrictFDerivAt_invFun_meanMap`, `HasFDerivAt.fun_sum` + `HasFDerivAt.mul` for `⟨θ(y), y⟩` with
  `hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι ↦ ℝ) j` — without `F'` the instance search is stuck; deprecated
  `ContinuousLinearMap.smul_apply/sub_apply/sum_apply/add_apply` → `_root_.…`), `dualHessian a := −t • invJac a`,
  `hasFDerivAt_dualGradient`, **`dualHessian_apply_cov`** (`D²I (Cov(R_i,R_v))_i = v`, via `meanMapDeriv_apply`),
  **`dualHessian_quadratic_form`** (`⟨Dm v, D²I (Dm v)⟩ = G_a(v,v)`, `sum_mul_priorCov_eq`).
- `TemperatureSlice.lean` (NOT mirrored; Astra round 30 item 4, coverage half): `tiltedPrior π L₀ t := e^{−tL₀}π`,
  `tiltedPrior_pos`, `measurable_tiltedPrior`, `integrable_tiltedPrior` (`Integrable.bdd_mul` with `c = e^{tM₀}`),
  `integral_tiltedPrior_pos` (the `ν_pos` field of `tiltData_aff` is about `baseWeight`, so finish with `simp [baseWeight,
  affLoss, tiltedPrior]`), **`meanMap_eq_tilted`** (`m(t,a) = m^{π_t}(1, t•a)` with base loss `0`; pointwise
  `rw [← mul_assoc, ← Real.exp_add]; congr 2; simp only [Pi.smul_apply, smul_eq_mul, zero_add, Finset.mul_sum, mul_add,
  mul_assoc]; ring`), `essRange_tilted` (both sides via `mem_essRange_iff`, which is prior-independent),
  `momentBody_tilted`, **`range_meanMap_slice`** (`range (a ↦ m(t,a)) = interior (momentBody μ π R)` for EVERY `t > 0`),
  `bijOn_meanMap_slice`, **`temperature_slice_graph`** (`∃! a`, the contrast part of the joint response at `Θ(t,a)` is `y`).
  Section-level `include` with many hypotheses + per-lemma `omit` lists was unmanageable here: give each helper its
  hypotheses explicitly and reserve `variable … include` for the final three theorems.
- `ObservableRegression.lean` (NOT mirrored): `obsMean μ π L₀ φ R t y := ⟨φ⟩_{θ(y)}`, `obsMean_meanMap`,
  **`hasFDerivAt_obsMean`** (`DΦ(m a) = obsMapDeriv φ a ∘ invJac a`, chain rule on `hasStrictFDerivAt_invFun_meanMap`),
  **`obsMean_deriv_cov`** (`DΦ(m a)(Cov(R_i,R_v))_i = Cov(φ, R_v)`: the regression identity `DΦ = Cov(φ,R)Cov(R,R)⁻¹`;
  via `invJac_meanMapDeriv` and `obsMapDeriv_apply`), **`abs_obsMean_deriv_le`** (`|DΦ ṁ| ≤ √Var(φ) √⟨ṁ, D²I ṁ⟩` from
  `abs_obsMapDeriv_le` + `dualHessian_quadratic_form`).
- `LegendreMaximum.lean` (NOT mirrored; Astra round 31 item 1): **`dual_objective_le_at_mean`** (`−t⟨θ,m(a₀)⟩ − A(θ) ≤
  −t⟨a₀,m(a₀)⟩ − A(a₀)`; the 1-D tangent inequality `ConvexOn.le_slope_of_hasDerivAt` on the segment
  `s ↦ mixLogZ … s` with `TiltData.mixLogZ_convexOn`, `TiltData.hasDerivAt_mixLogZ 0`, `slope_def_field`, `mixExp_zero_eq_dot`,
  `affLogZ_line`), **`legendre_isMaxOn_aff`** (name: `legendre_isMaxOn` already exists in `RayChart`),
  **`eq_of_isMaxOn_dual_objective`** (uniqueness: `IsLocalMax.hasFDerivAt_eq_zero` on `hasFDerivAt_affLogZ` + the CLM
  `dotCLM`, evaluate on `Pi.single j 1`, cancel `−t` by `mul_eq_zero`, then `meanMap_injective`), `dualPotential_isMaxOn`,
  `affLoss_zero_eq`, `affLoss_sub_affLoss_zero`, `log_gibbsDensity_div_zero` (`log(p_a/p_0) = −tR_a − A(a) + A(0)`),
  **`relEnt_eq_relEnt_gibbs_add`** (`KL(q‖P_0) = KL(q‖P_a) + (−t⟨a,m(a)⟩ − A(a) + A(0))` for a probability density `q` with
  the contrast means of `P_a`; pointwise identity with a case split on `q x = 0`; typed `Integrable (fun x ↦ …)` facts
  for `integral_add`/`integral_sub`), **`dual_add_le_relEnt`** (`relEnt_gibbsDensity_nonneg`). Astra round 31
  (`gpt_responses/research_round31_{q,v1}.md`): corrections — the gamma-boundary means of the wall are INTERIOR points of
  the moment body (missed by the open family), the observable-segment integrand needs `Cov(φ, R_{C⁻¹d})`; ranking (1)
  Legendre + constrained entropy [DONE], (2) wall mean band (Schur-complement fixed-mean monotonicity
  `∂_α U = −(Var F − Cov(F,z)²/Var z) < 0`, endpoints by entropy competitors, IVT), (3) temperature-slice variational
  principle (`∂_e I = −t`, `J_t`, `D²J_t = C_RR⁻¹`, `∂_t h_t(M) = −(residual variance of L₀ after regression on R)`),
  (4) scoped non-steep boundary-extension theorem, (5) `N^⊥`, (6) two-term wall law, (7) mean-segment observable transport
  (`ΔE φ = ∫ Cov_{m_s}(φ, R_{C_s⁻¹ d}) ds`, `|ΔEφ|² ≤ (∫Var φ)(KL + KL)`), (8) Cramér (not cheap).
- `SliceVariational.lean` (NOT mirrored; Astra round 31 item 3, variational core): **`dualPotential_ge_tangent`**
  (`I(m b) ≥ I(m a) − t⟨a, m b − m a⟩`, pure algebra on `dual_objective_le_at_mean` with `θ := a` at the mean of `b`),
  **`dualPotential_convexOn`** (on `range m = interior (momentBody R)` via `range_meanMap_slice`, hence `[Nonempty ι]` and
  `hπ : ∀ x, 0 < π x`; a convex combination `l₁ m a₁ + l₂ m a₂ = m c`, expand `dotJ c` by `IsLinearMap.map_add/map_smul`,
  then `nlinarith [mul_le_mul_of_nonneg_left h1 hl₁, …]`), **`partial_base_dualPotential`** (`∂_e I = −t` at `η(Θ(t,a))`:
  `hasFDerivAt_dualPotential` for the joint family composed with `hasDerivAt_affineLine … (Pi.single none 1) 0` — the base
  point must be aligned with `have hI' : HasFDerivAt … ((fun s ↦ m + s • e) 0) := by simpa using hI`; the statement needs
  `[DecidableEq ι]` for `Pi.single none`), **`slice_variational`** (among joint responses with the same contrast part the
  slice point minimises `e ↦ I(e,M) + te`; the dot product collapses by `Fintype.sum_option` + `hb` + `rfl`).
- `MeanSegment.lean` (NOT mirrored; Astra round 31 item 7): **`continuous_meanMapDeriv`** (entry continuity copied from
  `hasStrictFDerivAt_meanMap`; the assembly `ContinuousLinearMap.pi` is a linear map between finite-dimensional spaces, so
  `LinearMap.continuous_of_finiteDimensional` — build the `LinearMap` structure with `ext v i; simp [pi_apply]`),
  `meanMapDeriv_comp_invJac` (`ContinuousLinearEquiv.coe_comp_coe_symm`), `meanMapDerivUnit` (the Jacobian as a unit of the
  endomorphism algebra; `ContinuousLinearMap.mul_def`, `one_def`), `invJac_eq_inverse` (`Ring.inverse_unit`),
  **`continuous_invJac`** (`NormedRing.inverse_continuousAt u` — state `ContinuousAt Ring.inverse (meanMapDeriv a)` as a
  typed `have` before `.comp`, otherwise the coercion `↑u` is read as `Units.val` applied), `sq_integral_sqrt_mul_le`
  (`(∫₀¹√(fg))² ≤ (∫f)(∫g)` for `ContinuousOn … (Icc 0 1)`, AM–GM with weight `λ = √((B+ε)/(A+ε))`, `(B+ε)/λ = λ(A+ε)`, no
  square roots of products), `dotJ_comm`, `meanSeg`, `dataPath := m⁻¹ ∘ meanSeg`, `meanSeg_eq_comb` (`module`),
  `meanSeg_mem_range` (convexity of `range m = interior body`), `meanMap_dataPath`, `dataPath_zero/one`,
  **`hasDerivAt_dataPath`** (velocity `(Dm(γ_s))⁻¹ d`), `continuousOn_dataPath`, `continuousOn_dataPath_velocity`,
  **`obsMean_segment_eq`** (transport `⟨φ⟩_{a₁} − ⟨φ⟩_{a₀} = ∫₀¹ D⟨φ⟩(γ_s)[(Dm)⁻¹ d]`; FTC on `uIcc 0 1` with
  `ContinuousOn.intervalIntegrable`), `dualQuad s := ⟨d, D²I(y_s) d⟩`, `dualQuad_eq`, `continuousOn_dualQuad`,
  `hasDerivAt_dualPotential_meanSeg`, `hasDerivAt_dot_dataPath` (`dotJ d y = dotCLM d y` by `dotJ_comm`),
  **`mixKL_eq_integral_dual_one_sub`** (`KL(P_{a₁}‖P_{a₀}) = ∫₀¹(1−s)Q`; NOTE the seabed's `mixKL (affLoss a) (dirLoss (b−a))`
  is `KL(P_a‖P_b)`, so `KL(P_{a₁}‖P_{a₀})` is `mixKL (affLoss a₁) (dirLoss (a₀ − a₁))` — the first draft had the two
  identities swapped), **`mixKL_eq_integral_dual_mul`**, **`integral_dualQuad_eq`** (`∫₀¹Q = KL + KL`),
  `continuousOn_var_dataPath`, **`sq_obsMean_sub_le_jeffreys`** (`|Δ⟨φ⟩|² ≤ (∫₀¹Var_{γ_s}φ)(KL + KL)`).
- `ConstrainedResponse.lean` (NOT mirrored; Astra round 31 item 2, abstract core): `priorCov_dirLoss_add_smul` /
  `_right` (bilinearity of `priorCov` in the contrast direction, from `sum_mul_priorCov_eq` three times +
  `Finset.mul_sum` + `← Finset.sum_add_distrib`; the right slot via `priorCov_comm π _ φ ψ t` — its explicit arguments are
  `(π L φ ψ : X → ℝ) (t : ℝ)`, `μ` implicit), **`schur_eq_var_residual`** (`Var R_v − Cov(R_v,R_w)²/Var R_w = Var R_{v−λw}`,
  `λ = Cov/Var`; introduce `λ` by `obtain ⟨lam, hlam⟩ : ∃ lam, lam = … := ⟨_, rfl⟩`, expand with the two bilinearity lemmas,
  `field_simp; ring`), **`schur_pos_iff`** (positive iff `R_{v−λw}` is not a.e. constant, i.e. `R_v` not a.e. affine in `R_w`;
  from `responseForm_self_eq_zero_iff` and `priorCov_self_nonneg' … (t := t)` — `t` must be named),
  **`constrained_response_deriv`** (along `a(s) = a₀ + s v + β(s) w` with `⟨R_w⟩` constant,
  `d/ds⟨R_v⟩ = −t(Var R_v − Cov²/Var R_w)`; both responses differentiate by `hasFDerivAt_obsMap … |>.comp_hasDerivAt` with
  path velocity `v + β' w`, the constant one has derivative `0` by `HasDerivAt.unique`, which identifies
  `β' = −Cov(R_v,R_w)/Var R_w`; NOTE `obsMapDeriv_apply` puts the observable in the FIRST covariance slot and the direction in
  the second, so the right-slot bilinearity is the one needed; a `set a := fun s ↦ …` does not fold the literal
  `a₀ + s • v + β s • w` in the goal — `change` the goal to the `a s` form and restate `hw` as `hw' : … (a s) … ≠ 0 := hw`
  before `field_simp`).
- `FeaturelessPoint.lean` (NOT mirrored): `segVar_pos` (response variance along a segment in a nonzero direction is positive;
  `responseForm_self_eq_zero_iff` + the `hnd` form with the vacuous `π x ≠ 0 →` premise discharged by `hc.mono`),
  **`mixKL_pos`** (`0 < KL(P_b‖P_a)` for `a ≠ b`; forward segment identity + `intervalIntegral.intervalIntegral_pos_of_pos_on`
  with `IntervalIntegrable` from `Continuous.intervalIntegrable`), `mixKL_eq_zero_iff` (`←` by the Bregman identity at `a = a`,
  `simp [dotJ]`), `dualPotential_meanMap_zero` (`I(m 0) = −A(0)`), **`dualPotential_sub_prior_eq_mixKL`**
  (`I(m b) − I(m 0) = KL(P_b‖P_0)`, from `mixKL_eq_bregman_dual 0 b`), the `y`-coordinate form `…'` (`meanMap_invFun hy`),
  `dualPotential_prior_le/lt`, **`dualPotential_isMinOn_prior`** (the prior's response is the unique minimiser of `I` on
  `range m`), `eq_zero_of_dualPotential_eq_prior`, `dualPotential_add_affLogZ_zero_nonneg` (`I(y) + A(0) ≥ 0` on the range).
  Section hypotheses use strict `hπ : ∀ x, 0 < π x` (SegmentDivergence) and pass `fun x ↦ (hπ x).le` to the DualPotential API.
- `MultiConstrainedResponse.lean` (NOT mirrored; Astra round 32 item 1, algebraic engine): `Bdd.sub`,
  `priorCov_dirLoss_add_left/right`, **`priorCov_dirLoss_sum_smul_left/right`** (`Cov(R_{∑ cₖ wₖ}, ψ) = ∑ cₖ Cov(R_{wₖ}, ψ)`;
  proof: rewrite every `Cov(R_{wₖ}, ψ)` by `(sum_mul_priorCov_eq …).symm` under the binder with `simp only [e]`, then `←
  sum_mul_priorCov_eq` on the left, `Finset.sum_apply/Pi.smul_apply/sum_mul/mul_sum`, `Finset.sum_comm`, termwise `ring`),
  `priorCov_sub_left/right` for bounded observables (from the definition with `integral_sub` on typed lambda integrability
  facts; `simp only [priorCov, priorExp]` unfolds AND beta-reduces so the `e1/e2` rewrites match), `covMat` (`Matrix.of`),
  `covVec`, `dotProduct_covMat_mulVec` (`uᵀCu = Var R_{∑ uₖwₖ}`), **`residual_var`** (`Cb = c ⇒ Var(φ − ∑ bₖR_{wₖ}) = Var φ − ∑
  bₖ Cov(R_{wₖ}, φ)`; the key step `Cov(R_{wₖ}, R_{∑ bₗ wₗ}) = (Cb)ₖ = cₖ` by `congrFun hb k` + `simp only [Matrix.mulVec,
  dotProduct, covMat, Matrix.of_apply, covVec] at this`), `residual_var_nonneg`, `residual_var_eq_zero_iff`
  (`ae_eq_const_of_priorCov_self_eq_zero`; the base integrability `h0` needs `(t := t)` pinned or `simp` faces `?t`),
  **`covMat_mulVec_injective`** (`hnd` + `LinearIndependent ℝ w`; `Fintype.linearIndependent_iff`),
  **`multi_constrained_response_deriv`** (`d/ds⟨φ⟩ = −t(Cov(φ,R_v) − ∑ bₖ Cov(φ,R_{wₖ}))` along
  `a₀ + s v + ∑ βₖ(s) wₖ` with all `⟨R_{wₖ}⟩` constant, `Cb = c`, `C` injective; the constraint derivatives vanish
  (`HasDerivAt.unique`), giving `Cβ' = −c`, so `β' = −b` by injectivity; the path derivative of `∑ βₖ(s) • wₖ` is
  `HasDerivAt.fun_sum`), `multi_constrained_response_deriv_self` (`= −t Var(residual)`).
  The `integrable_mul_affWeight_of_bdd` lemma needs `[Nonempty X]` — do not `omit` it on lemmas that use it.
- `SliceChart.lean` (NOT mirrored; Astra round 32 item 1, IFT step): `jointPoint t M := Option.elim t M`,
  `sliceMap θ := (θ none, ⟨R⟩_θ)` in the joint natural coordinates (`meanMap μ π 0 (jointStat L₀ R) 1`), `sliceMapDeriv`
  (`ContinuousLinearMap.pi` with `proj none` in the temperature slot and `proj (some i) ∘ meanMapDeriv` in the feature slots;
  the `proj`s need `(R := ℝ) (φ := fun _ : Option ι ↦ ℝ)`), **`hasStrictFDerivAt_sliceMap`** (`hasStrictFDerivAt_pi'.2`, then
  `cases j`; each slot is `hasStrictFDerivAt_apply (𝕜 := ℝ) (F' := …) j _` (composed with `hasStrictFDerivAt_meanMap`, which needs
  NO nondegeneracy) followed by `.congr_fderiv (by ext u; rfl)`), **`sliceMapDeriv_injective`** under FEATURE nondegeneracy only
  (kernel vector has `u none = 0`, so `u = dataDir u_some`; `Var(dirLoss S u) = ∑_j u_j Cov(S_j, dirLoss S u)` via
  `sum_mul_priorCov_eq` + `Fintype.sum_option` vanishes, `responseForm_self_eq_zero_iff` + `dirLoss_jointStat_dataDir` + `hnd`),
  `sliceMapEquiv` (`LinearEquiv.ofInjectiveEndo … |>.toContinuousLinearEquiv`, as `meanMapDerivEquiv`), `natCoord_of_pos`
  (`θ = natCoord (θ none) (θ_some/θ none)`), `sliceMap_natCoord`, **`sliceMap_injOn`** on `{θ none > 0}` (reduce both points to
  `natCoord` form with `obtain ⟨t, a, rfl⟩ : ∃ t a, θ = natCoord t a`, then `meanMap_injective`), `sliceMap_surj` (from
  `bijOn_meanMap_slice`), `sliceInv := Function.invFunOn sliceMap {θ none > 0}` — a `def` inside a hypothesis section takes only the
  variables it USES, so it and `tempPath` live outside the section with explicit `(μ π L₀ R)` — `sliceInv_sliceMap`
  (`InjOn.leftInvOn_invFunOn`), `sliceMap_sliceInv` (`Function.invFunOn_eq`), `sliceInv_none_pos`,
  **`hasStrictFDerivAt_sliceInv`** (`HasStrictFDerivAt.to_local_left_inverse` with the eventual left-inverse on the open half-space
  `isOpen_lt continuous_const (continuous_apply none)`), `tempPath μ π L₀ R M t := sliceInv (jointPoint t M)`, `tempPath_none`,
  `tempPath_response`, **`tempPath_eq_natCoord`** (`= natCoord t (invFun (meanMap t) M)` by `sliceMap_injOn`; needs
  `range_meanMap_slice` to get `M ∈ range`), `obsMean_eq_tempPath`, `hasDerivAt_jointPoint` (`jointPoint t M = jointPoint 0 M + t •
  Pi.single none 1`; keep `set_option linter.unusedFintypeInType false in`), **`hasDerivAt_tempPath`** (velocity
  `(sliceMapEquiv θ₀).symm (Pi.single none 1)`), `tempPath_velocity_none` (`= 1`), `velocity_decomp`.
- `LossSurface.lean` (NOT mirrored; Astra round 32 item 1): `dirLoss_pi_single` (NOTE `dirLoss_single` already exists in
  `WallChart` — the clash surfaces only at the umbrella build), `dirLoss_jointStat_single_some/none`, `featCov` (`Cov(R_k, R_l)`
  as `Matrix.of`), `featObsCov`, `sum_smul_single_eq`, `featCov_eq_covMat`, `featObsCov_eq_covVec`, `covMat_joint_eq`,
  `covVec_joint_eq` (joint-family covariances at `natCoord t a` = `a`-family covariances, by `priorCov_natCoord`),
  **`featCov_mulVec_injective`** (via `covMat_mulVec_injective` + `Pi.linearIndependent_single_one ι ℝ`; `classical`),
  `featCov_mulVec_surjective` (`Matrix.mulVec_surjective_iff_isUnit`; needs `classical` for the matrix ring),
  **`hasDerivAt_obsMean_temp`** (`∂_t⟨φ⟩|_M = −(Cov(φ,L₀) − ∑ bₖ Cov(φ,Rₖ))`, `C b = Cov(R,L₀)` at `(t₀, m_{t₀}⁻¹ M)`: apply
  `multi_constrained_response_deriv_path` in the joint family (`L₀ := 0`, `R := jointStat`, `t := 1`) along `tempPath M` with
  `v = Pi.single none 1`, `w k = Pi.single (some k) 1`, `γ k = u (some k)`; the feature constraints hold eventually
  (`lt_mem_nhds ht₀`); transfer back with `obsMean_eq_tempPath` (eventually equal functions) and `priorCov_natCoord`; a
  `set θ₀ := tempPath … t₀` does NOT fold occurrences created later by `key`, so restate `hθ₀eq'` on the unfolded term),
  **`hasDerivAt_lossSurface`** (`∂_t h = −Var(L₀ − dirLoss R b)` via `residual_var` + `sum_smul_single_eq`),
  `lossSurface_deriv_nonpos`, **`lossSurface_antitoneOn`** (`antitoneOn_of_deriv_nonpos (convex_Ioi 0)`, `interior_Ioi`, the
  regression vector at each `t` from surjectivity), `featCov_mulVec_apply` (`(Cv)_i = Cov(R_i, R_v)`),
  **`obsMean_fderiv_eq_regression`** (`D_M⟨φ⟩[d] = ∑ bₖ dₖ` for `C b = Cov(R, φ)`; write `d = Cv`, use `obsMean_deriv_cov`,
  and the symmetry `∑ₖ bₖ(Cv)ₖ = ∑ₗ vₗ(Cb)ₗ` by `Finset.sum_comm`).
- `ReducedPotential.lean` (NOT mirrored; Astra round 32 item 1, block Hessian): **`hasDerivAt_affLogZ_temp`** (`∂_t A_t(a) =
  −(⟨L₀⟩_{t,a} + ⟨a, m(t,a)⟩)`; chain rule through the joint family: `t ↦ natCoord t a = t • natCoord 1 a` composed with
  `hasFDerivAt_affLogZ` at `t = 1`, then `simp only [_root_.smul_apply, smul_eq_mul, dotCLM_apply, dotJ, Fintype.sum_option,
  natCoord, Option.elim, meanMap_natCoord_none, meanMap_natCoord_some]; ring_nf`), **`featCov_mulVec_dualHessian`** (`C (D²I d) = d`:
  write `d = C v` by surjectivity, `featCov_mulVec_apply`, `dualHessian_apply_cov`), `dualPotential_eq_tempPath`
  (`J(t,M) = −⟨θ(t,M), (0,M)⟩ − B(θ(t,M))`; `Finset.sum_neg_distrib` before the termwise `ring`), **`hasDerivAt_dualPotential_temp`**
  (`∂_t J = h`: `J(t) = G(θ(t))` with `G(θ) = −⟨θ,(0,M)⟩ − B(θ)`, `DG(θ(t)) = ⟨·, m_J(θ) − (0,M)⟩ = ⟨·, (h, 0)⟩`, `θ'(t)_none = 1`; the
  function `θ ↦ dotJ θ y` is `⇑(dotCLM y)` by `funext … (dotCLM_apply _ θ).symm`; do NOT unfold `meanMap` in the final simp —
  it destroys the `tempPath_response` pattern for the `some` slots; give the `none` slot as a separate `rfl` fact `hnone`),
  **`hasDerivAt_infoRel_temp`** (`∂_t(J + A_t(0)) = h − ⟨L₀⟩_{t,0}`), **`tempPath_velocity_some`** (`∂_t β = −b`, the mixed
  partial, via `constrained_velocity_eq` — factored out of `multi_constrained_response_deriv_path` in `MultiConstrainedResponse`;
  needs `[DecidableEq ι]` in the statement for `Pi.single`). With `hasDerivAt_lossSurface` (`∂_t² J = −σ²`),
  `obsMean_fderiv_eq_regression` (`∇_M h = b`) and `hasFDerivAt_dualPotential` (`∇_M J = −ta`) this is the whole block Hessian
  `[[−σ², bᵀ],[b, C⁻¹]]`.
- `AnnealingRay.lean` (NOT mirrored; Astra round 32 item 2, fixed-energy part): `affLoss_zero_eq_fun` (`affLoss L₀ R 0 = L₀`;
  NOTE `affLoss_zero_eq` lives in `LegendreMaximum`, outside this closure), **`hasDerivAt_priorExp_temp`** (`d/dt⟨φ⟩_{t,a} =
  −Cov_{t,a}(φ, L_a)`; chain rule through the joint family along `t ↦ natCoord t a = t • natCoord 1 a`, `hasFDerivAt_obsMap` at
  `t = 1`, `obsMapDeriv_apply`, `priorCov_natCoord`, `dirLoss_jointStat_natCoord … 1 a` + `one_mul`), `hasDerivAt_energy_temp`
  (`E' = −Var_t(L₀)`; `.congr_deriv (by rw [affLoss_zero_eq_fun L₀ R])` — a rewrite that makes both sides identical closes the
  goal), **`energy_antitone`** (on ALL of `ℝ`, `antitone_of_deriv_nonpos`), `continuous_priorCov_temp` (from differentiability of
  the three expectations; `exact h1.sub (h2.mul h3)` unifies with `priorCov` by defeq), **`integral_var_eq_energy_drop`**
  (`∫₀ᵀ Var = E(0) − E(T)`; FTC with `f := fun u ↦ −E u`, `f'` given explicitly), **`rayKL_eq`** (`mixKL μ π L₀ (fun x ↦ −L₀ x) T
  0 1 = ∫₀ᵀ u Var_u`; Bregman form from `tiltData_baseWeight_of_bounded (μ := μ) (Δ := fun x ↦ −L₀ x)` — type the direction as
  the lambda, `hL₀m.neg` alone infers the Pi-negation `−L₀` — and `TiltData.mixKL_eq`; primitive `g(u) = log∫π − A_u(0) − u E(u)`
  with `g' = u Var_u` from `hasDerivAt_affLogZ_temp` and `hasDerivAt_energy_temp`; endpoints `pathLoss L₀ (−L₀) 1 = 0`,
  `priorZ 0 T = ∫π`, `A_0(0) = log ∫π`; `unfold affLogZ` last), **`rayKL_le`** (`KL ≤ T(E(0) − E(T))`,
  `intervalIntegral.integral_mono_on`), **`sq_priorExp_sub_le_ray`** (`(⟨φ⟩_T − ⟨φ⟩_0)² ≤ (∫₀ᵀ Var φ)(E(0) − E(T))`: FTC for the
  change, pointwise Cauchy–Schwarz `TiltData.abs_tiltCov_le` via `tiltData_aff … (0 : ι → ℝ) 0 u` + `← priorCov_eq_tiltCov_zero` ×3
  + `← Real.sqrt_mul`, `intervalIntegral.abs_integral_le_integral_abs`, rescale `∫₀ᵀ k = T ∫₀¹ k(Ts)` by
  `intervalIntegral.integral_comp_mul_left k hT.ne'` (the instances `hres k` come out beta-reduced — no `simp only at`), then
  `sq_integral_sqrt_mul_le` (MeanSegment) on `[0,1]`).
- `DataMixture.lean` (NOT mirrored; Astra round 32 item 2, data-manifold bridge): `dataLoss ℓ ν x := ∫ z, ℓ x z ∂ν` (NOTE
  `popLoss` is taken by `TruthVariation`), `mixMeasure ν₀ ν₁ s := ofReal (1−s) • ν₀ + ofReal s • ν₁`, `measurable_ℓ_right`,
  `integrable_ℓ_right` (`Integrable.of_bound` on a probability measure), `measurable_dataLoss`
  (`hℓ.stronglyMeasurable.integral_prod_right' (ν := ν)` — `Measurable (uncurry ℓ)` is the hypothesis to carry),
  `abs_dataLoss_le` (`norm_integral_le_of_norm_le_const` + `simpa [dataLoss, measureReal_def]`), **`dataLoss_mixMeasure`**
  (affine in `s ∈ Icc 0 1`; `integral_add_measure` of `Integrable.smul_measure … ENNReal.ofReal_ne_top`, `integral_smul_measure`,
  `ENNReal.toReal_ofReal`), `lossContrast ℓ ν₀ ν₁ := L_{ν₁} − L_{ν₀}`, `dataLoss_mixMeasure_eq_pathLoss`,
  `dataLoss_mixMeasure_eq_affLoss` (the `ι = Unit` affine family), `bdd_lossContrast_unit`, `tiltData_dataMixture`,
  **`hasDerivAt_dataMixture_exp`** (`d/ds⟨φ⟩_{t,ν_s} = −t Cov(φ, L_{ν₁} − L_{ν₀})` for `s ∈ Ioo 0 1`; `TiltData.hasDerivAt_mixExp`
  + eventual equality on `Ioo_mem_nhds`), **`dataMixture_KL_eq`/`_eq'`** (`KL(P_{ν₁}‖P_{ν₀}) = t²∫₀¹ s Var_{ν_s}(Δ)`, reverse with
  `1 − s`; instantiate `mixKL_eq_integral_mul_var` in the Unit family at `a = 0, b = 1`, rewrite the endpoints by `funext; simp
  [affLoss]`/`[dirLoss]`, then inside `intervalIntegral.integral_congr` convert `s ∈ uIcc 0 1` with `uIcc_of_le (zero_le_one' ℝ)`
  and rewrite the direction `(fun _ ↦ 0) + s • ((fun _ ↦ 1) − fun _ ↦ 0) = fun _ ↦ s` and `dirLoss (fun _ ↦ Δ) (…) = Δ` by explicit
  `funext; simp` facts — `congr 2` bullets are fragile there). Section discipline: `variable (hℓ) (hM)` + `include hℓ hM` at the
  top, `omit hM in`/`omit [MeasurableSpace X] hℓ in` per lemma; the prior hypotheses in a nested section.
- `ThirdCumulant.lean` (NOT mirrored; Astra round 32 item 4): `priorCum3` (`κ₃(φ,ψ,χ) = ⟨φψχ⟩ − ⟨φψ⟩⟨χ⟩ − ⟨φχ⟩⟨ψ⟩ − ⟨ψχ⟩⟨φ⟩ +
  2⟨φ⟩⟨ψ⟩⟨χ⟩`, products associated `φ x * ψ x * χ x`), `priorCum3_swap₁₂/₂₃` (funext the products, `ring`),
  **`hasDerivAt_cov_of_hasDerivAt_exp`** (the algebraic engine: family `L : ℝ → X → ℝ`, temperature `τ : ℝ → ℝ`, generator `D`,
  rate `c`; from `d/ds E_s[f] = −c Cov(f, D)` for all bounded `f` to `d/ds Cov_s(φ,ψ) = −c κ₃(φ,ψ,D)`; proof `(hE (φψ)).sub ((hE
  φ).mul (hE ψ))` then `simp only [priorCov, priorCum3]; ring`), `hasDerivAt_priorExp_line`, **`hasDerivAt_priorCov_line`**
  (`−t κ₃(φ,ψ,R_v)`), **`hasDerivAt_meanMapDeriv_line`** (`D²m[u,v]ᵢ = t² κ₃(Rᵢ,R_u,R_v)`; rewrite the function with
  `meanMapDeriv_apply` under `funext` — type the lambda binder `fun s : ℝ` or `s • v` is stuck), **`hasDerivAt_responseForm_line`**
  (`−t³ κ₃(R_u,R_v,R_w)`, totally symmetric: the Amari–Chentsov tensor), `hasDerivAt_segVar_line`,
  **`hasDerivAt_priorCov_temp`** (`d/dt Cov = −κ₃(φ,ψ,L_a)`, from `hasDerivAt_priorExp_temp` with `c = 1`, `τ = id`).
- `TwoAxisResponse.lean` (NOT mirrored; Astra round 33 item 3): `affLoss_add_smul_eq` (`affLoss (a + s•v) = fun x ↦ affLoss a x +
  s * dirLoss R v x`; NOTE `affLoss_add_smul` in ResponseMap is a different statement), `priorExp_add_bdd`
  (`priorExp_add_of_integrable` + `integrable_mul_affWeight_of_bdd`), `priorExp_const_mul_bdd` (NOTE `priorExp_const_mul` is taken
  by WallWindowLength, outside this closure), `priorCov_add_right_bdd`, `priorCov_const_mul_right'`, `priorCov_affLoss_line`,
  `priorExp_affLoss_line`, `priorCum3_affLoss_line` (linearity in the moving loss `L_{a+sv} = L_a + sR_v`; ALWAYS state these with
  a separate base point `b` — `rw [affLoss_add_smul_eq L₀ R a v s]` otherwise rewrites the family loss too),
  **`hasDerivAt_exp_temp_line`** / **`hasDerivAt_exp_line_temp`** (the mixed partials of `⟨φ⟩` in both orders, common value
  `−Cov(φ,R_v) + t κ₃(φ,R_v,L_{a+sv})`; the `t`-order one is `((hasDerivAt_id t₀).neg).mul (hasDerivAt_priorCov_temp …)` and
  needs `simp only [Pi.neg_apply, id_eq]` before `ring`), **`hasDerivAt_affLogZ_temp_line`** / **`hasDerivAt_affLogZ_line_temp`**
  (mixed partials of `A`, common value `−⟨R_v⟩ + t Cov(R_v, L_{a+sv})`). The three-point identity Astra ranked 4th is already
  `mixKL_three_point`/`mixKL_pythagoras` (SegmentDivergence).
- `FaceLimit.lean` (NOT mirrored; Astra round 33 item 1, positive-mass half): `mul_exp_neg_le_exp_neg_one` (`y e^{−y} ≤ e^{−1}`,
  from `Real.add_one_le_exp (y − 1)`), `exp_mul_priorZ` (`e^{λα}Z_λ = ∫e^{−λ(V−α)}π`), `priorExp_sub_const`,
  `aestronglyMeasurable_shift_weight`, `tendsto_shift_weight` (pointwise `e^{−λ(V−α)} → 1_{V=α}`; the indicator rewrites need the
  membership spelled `show x ∈ {x | V x = α} from hxF`), `tendsto_shift_integral` (`tendsto_integral_filter_of_dominated_convergence`
  along `atTop : Filter ℝ`, bound `Mφ π`, `Real.exp_le_one_iff` + `nlinarith` for the domination), **`tendsto_shifted_priorZ`**
  (`e^{λα}Z_λ → ∫_F π`), **`tendsto_priorExp_face`** (`⟨φ⟩_λ → (∫_F φπ)/(∫_F π)`; ratio of shifted numerators via `mul_div_mul_left`),
  **`tendsto_mul_priorExp_shift`** (`λ⟨V−α⟩_λ → 0`, bound `e^{−1}π`, `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1`),
  **`tendsto_mixKL_face`** (`KL(q_λ‖π̄) → log∫π − log∫_Fπ`; `TiltData.mixKL_eq` with `L₀ := 0`, the tilted `TiltData` for
  integrability `hT'.integrable_tilt (f := …)` — pass `f` explicitly when `hfm := measurable_const`; the final assembly needs
  `tendsto_const_nhds (x := …)` pinned), `priorExp_ray_eq_tilted` (`⟨φ⟩_{t,sv} = ⟨φ⟩` under `tiltedPrior` tilted by `R_v` at rate
  `ts`), **`tendsto_priorExp_ray_face`**. Section discipline: no `[Nonempty X]` in the section; add it as an instance binder only on
  the KL theorem; `omit hπpos hV in` on the dominated-convergence lemmas.
- `FaceInfinite.lean` (NOT mirrored; Astra round 33 item 1, zero-mass half): `mul_log_ge_tangent` (`r log c + r − c ≤ r log r`
  from `Real.log_le_sub_one_of_pos (c/r)`, finish with `nlinarith [h2, h3]` where `h3 : r * (c/r) = c`), `tiltData_face`,
  `priorZ_face_pos`, `integrable_face_weight` (from `TiltData.integrable_tilt` + `.congr (… by simp [baseWeight])`; pass `(f := …)`
  when `hfm := measurable_const`), **`mixKL_face_eq_integral`** (`KL = (∫ ℓ w)/Z`, `ℓ = −λV + log Z₀ − log Z`; from
  `TiltData.mixKL_eq` with the `TiltData` TYPE-ASCRIBED so `L₀ = 0` is fixed; the last `field_simp` needs `ring` after it),
  **`tangent_weight_le`** (the weighted pointwise tangent inequality `Z⁻¹(log c + 1) w − c Z₀⁻¹ π ≤ Z⁻¹ ℓ w`, with `ℓ = log r`,
  `r = e^{−λV}Z₀/Z`; two `field_simp; ring` identities), `setIntegral_linear_form`, **`mixKL_ge_two_event`**
  (`KL ≥ q_λ(A) log(q_λ(A)/π̄(A)) − 1`: `integral_add_compl`, `setIntegral_mono_on` on `A` with `c = q_λ(A)/π̄(A)` and on `Aᶜ`
  with `c = 1`; `q_λ(A) > 0` via the lower bound `e^{−|λ|M}π ≤ w`; `setIntegral_le_integral` for `π̄(Aᶜ) ≤ 1`),
  `exp_neg_mul_le_of_le`, **`tilt_mass_compl_le`** (`q_λ({V < α+ε}ᶜ) ≤ e^{−λε/2} Z₀/∫_{V<α+ε/2}π`; `div_le_div₀` with the
  numerator/denominator bounds; split `e^{−λ(α+ε)} = e^{−λε/2}e^{−λ(α+ε/2)}`), `tendsto_tilt_mass_compl` (squeeze),
  `tilt_mass_eq_one_sub` (`rw [eq_sub_iff_add_eq, ← add_div, h, div_self]`; `div_add_div_same` no longer exists),
  **`tendsto_face_nbhd_mass`** (`∫_{V<α+1/(n+1)} π → ∫_{V=α} π = 0`, DCT on indicators along `ℕ`;
  `Set.indicator_of_mem (…) π` takes `f` explicitly; `exists_nat_one_div_lt`), **`tendsto_mixKL_zero_face`**
  (`tendsto_atTop`; neighbourhood with `π̄(A) < e^{−2(|K|+2)}`, eventually `q_λ(A) ≥ 1/2`, then the log arithmetic with
  `Real.log_le_log`, `Real.log_exp`, `log 2 ≤ 1`).
- `EffectiveFeatures.lean` (NOT mirrored; Astra round 33 item 2): `priorCov_eq_zero_of_ae_const` (`priorExp_congr_ae'` +
  `priorExp_const_mul_bdd` + `priorExp_const_fun`), `priorExp_eq_of_sub_mem` (`P_b = P_a` for `b − a ∈ N`; from
  `priorExp_affLoss_add_of_invisible` + `add_sub_cancel`), **`featCov_mulVec_eq_zero_iff`** (`C u = 0 ↔ u ∈ N`; `→` via
  `u ⬝ C u = Var(R_u)` (`featCov_mulVec_apply`, `sum_mul_priorCov_eq`) and `responseForm_self_eq_zero_iff`; `←` entrywise),
  **`injOn_meanMap_of_isCompl`** (`meanMap_eq_iff_invisible` + `IsCompl.inf_eq_bot` + `Submodule.mem_inf/mem_bot`),
  **`image_meanMap_of_isCompl`** (`Submodule.codisjoint_iff_exists_add_eq` — the `Submodule.` prefix is required),
  `bijOn_meanMap_of_isCompl`, **`responseForm_pos_of_isCompl`**, `finrank_compl_invisible`
  (`Submodule.finrank_add_eq_of_isCompl` + `Module.finrank_fintype_fun_eq_card`). No `hnd` anywhere.
- `ResidualFormDeriv.lean` (NOT mirrored; Astra round 34 item 1, layer B): `residual_form_sub` (exact difference identity
  `s(t) − s(t₀) = Δv − ⟨b(t),Δc⟩ − ⟨Δc,b(t₀)⟩ + ⟨b(t),ΔC b(t₀)⟩` from the normal equations and symmetry; `Finset.sum_comm` +
  `hsym` + `hCb'` pointwise), `slope_form_aux` (distribute `h⁻¹` through the identity), **`hasDerivAt_residual_form`**
  (`d/dt (v − ⟨c,b⟩) = v' − 2⟨b,c'⟩ + ⟨b,C'b⟩` with `b` merely CONTINUOUS: `hasDerivAt_iff_tendsto_slope`, the slope identity
  via `slope_def_field` + `div_eq_inv_mul` as a `∀ f` rewrite under binders, limits by `HasDerivAt.tendsto_slope`,
  `tendsto_finsetSum`, `tendsto_pi_nhds.1` for the components of `b`; convert the limit value BEFORE `Tendsto.congr'` — there
  is no `Tendsto.congr_nhds`).
- `LossCurvature.lean` (NOT mirrored; Astra round 34 item 1): `priorCum3_dirLoss_left` (`κ₃(R_u,ψ,χ) = ∑ uᵢ κ₃(Rᵢ,ψ,χ)`; each
  `priorExp` of a product with `dirLoss` via `priorExp_dirLoss` on the product family, then four explicit `Finset.sum_mul`/
  `mul_sum` normalisations `h2..h5` and `simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]` — a
  `congr 1` cascade is NOT robust here), `priorCum3_sub_left`, **`priorCum3_residual_expand`**
  (`κ₃(H,H,χ) = κ₃(L₀,L₀,χ) − 2∑bᵢκ₃(Rᵢ,L₀,χ) + ∑∑bᵢbⱼκ₃(Rᵢ,Rⱼ,χ)`, second slot through `priorCum3_swap₁₂`),
  `priorCum3_natCoord`, `regCoeff := (featCov …)⁻¹ *ᵥ featObsCov … L₀` (Matrix inverse; `[DecidableEq ι]`),
  `isUnit_featCov` (needs `DecidableEq` for the matrix ring — do not omit it), `featCov_mulVec_regCoeff` (normal equations, from
  `Matrix.mul_nonsing_inv` with `(Matrix.isUnit_iff_isUnit_det _).1`), `featCov_symm`, `dirLoss_jointStat_velocity`
  (`S_u = L₀ − b·R` for the temperature-path velocity), **`hasDerivAt_priorCov_tempPath`** (`d/dt Cov_{t,M}(φ,ψ) = −κ₃(φ,ψ,H)`
  via `hasDerivAt_cov_of_hasDerivAt_exp` in the joint family with `τ := fun _ ↦ 1` — write the temperature as `((fun _ ↦ 1) t)`
  in `hE` so the lemma's pattern matches), **`continuousAt_regCoeff`** (`continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv'];
  exact continuousAt_inv₀ hdet)` composed with entrywise continuity `continuousAt_pi.2`; entry of the inverse via
  `(continuous_id.matrix_elem i j).continuousAt.comp hinv`), `residual_var_eq_form` (`σ² = v − ⟨c, b⟩` from `residual_var`),
  **`hasDerivAt_residual_var`** (`(σ²)' = −κ₃(H,H,H)`; the normal equations only hold for `t > 0`, so reparametrise by
  `τ t = if 0 < t then t else t₀` (introduced with `obtain ⟨τ, hτdef⟩ : ∃ τ, τ = … := ⟨_, rfl⟩`) and transfer the derivative,
  continuity and function by `∀ᶠ t, τ t = t`; the eventual-equality proofs are `by simp only [h]` (a `rw [h]` cannot see the
  bound variable under the beta-redex)), **`hasDerivAt_deriv_lossSurface`** (`∂_t² h = κ₃(H,H,H)` — `deriv h =ᶠ −σ²` from
  `hasDerivAt_lossSurface` with `b := regCoeff`).
- `DataReachability.lean` (NOT mirrored; Astra round 34 item 2): `mixFin ν w := ∑ j, ofReal (w j) • ν j`, `reachableCoeff a :=
  (fun w ↦ ∑ j, w j • a j) '' stdSimplex ℝ J`, `reachableResponse := meanMap t '' reachableCoeff a`,
  **`reachableCoeff_eq_convexHull`** (`= convexHull ℝ (range a)`: the coefficient map as a `LinearMap` structure literal,
  `convexHull_basis_eq_stdSimplex`, `LinearMap.image_convexHull`, `Set.range_comp`, `Finset.sum_eq_single` with `Ne.symm hk`
  for the off-diagonal `if j = k`), `isCompact_reachableCoeff` (`isCompact_stdSimplex ℝ J |>.image (by fun_prop)`),
  `integrable_mixFin_partial`, `dataLoss_mixFin` (integral against a finite sum of measures by `Finset.induction_on` +
  `integral_add_measure`/`integral_smul_measure` — no `integral_finset_sum_measure` in this Mathlib; `classical` for
  `insert`), **`dataLoss_mixFin_eq_affLoss`** (`L₀ + (∑ wⱼaⱼ)·R + ∑ wⱼkⱼ`; `∑ w = 1` via `← Finset.sum_mul`, then normalise
  the inner association with an explicit `∀ y` sum identity before `ring`), **`priorExp_mixFin`**, `reachableResponse_eq_image_convexHull`,
  **`isCompact_reachableResponse`**, `reachableResponse_subset_range/_interior`, **`mem_reachableResponse_iff`**
  (`invFun_meanMap`/`meanMap_invFun`), `response_mixFin_mem`. Omit `[Fintype ι]` on the coefficient-polytope lemmas
  (`linter.unusedFintypeInType`); do NOT omit `[MeasurableSpace X]` where `hℓ : Measurable (uncurry ℓ)` is in scope.
- `JourneyPotential.lean` (NOT mirrored; Astra round 34 item 4): **`hasDerivAt_natKL_path`** (`d/ds KL(P_{η s}‖P_{η₀}) =
  Cov_{η s}(S_{η s − η₀}, S_{η'})`; rewrite the KL by `natKL_eq` (Bregman form), differentiate `A ∘ η` with
  `hasFDerivAt_affLogZ … |>.comp_hasDerivAt`, `m ∘ η` with `hasFDerivAt_meanMap` then `hasDerivAt_pi.1` per component, the
  coefficient `η₀ j − η s j` with `(hasDerivAt_pi.1 hη j).const_sub (η₀ j)` — a `simpa using … .sub` trips the instance
  diamond; the value by `← sum_mul_priorCov_eq` + `meanMapDeriv_apply` + two sum identities + `linarith`),
  **`continuous_natCov_path`** (`Cov_θ(S_u,S_v)` continuous along continuous `θ, u, v`: bilinear expansion through
  `sum_mul_priorCov_eq` twice, then `Cov_θ(S_j,S_k) = −obsMapDeriv θ (Pi.single k 1)` and `continuous_obsMapDeriv … |>.comp hθ
  |>.clm_apply continuous_const`; `continuous_finsetSum`), **`natKL_path_eq_integral`** (FTC; `KL(η 0‖η 0) = 0` by `natKL_eq`
  + `simp`; pass `(u := fun s ↦ η s − η 0) (v := η')` explicitly), `natKL_segment_eq_integral` (`s G(d,d)` via `dirLoss_smul`,
  `priorCov_const_mul_left`).
- `RayLength.lean` (NOT mirrored; Astra round 34 item 3): `rayLength μ π L₀ R T := ∫₀ᵀ √Var_u(L₀)` (the Fisher
  length of the annealing ray); **`priorExp_mono_bdd`** (monotone expectations of bounded observables, `integral_mono`
  over the nonnegative weight), **`priorCov_self_le_sq_of_bounds`** (Popoviciu: `lo ≤ φ ≤ hi ⇒ Var φ ≤ ((hi−lo)/2)²`;
  centred second moment expanded by `priorExp_add_bdd`/`priorExp_const_mul_bdd`/`priorExp_const_fun`, pointwise
  `(φ−c)² ≤ r²` by `nlinarith [mul_nonneg (φ−lo) (hi−φ)]`, then `nlinarith [sq_nonneg (⟨φ⟩ − c)]`),
  **`abs_priorExp_sub_le_ray`** (`|⟨φ⟩_T − ⟨φ⟩_0| ≤ ∫₀ᵀ √(Var φ · Var L₀)`, the intermediate step of
  `sq_priorExp_sub_le_ray` exposed), **`sq_rayLength_le`** (`Length(T)² ≤ T(E(0) − E(T))`: `sq_integral_sqrt_mul_le`
  with `g = 1` after rescaling to `[0,1]`; `simp only [mul_one, intervalIntegral.integral_const, sub_zero, one_smul]`
  kills `∫₀¹ 1`), `rayLength_le_sqrt`, **`abs_priorExp_sub_le_rayLength`** (`|Δ⟨φ⟩| ≤ ((hi−lo)/2) Length(T)`; `lo ≤ hi`
  from `Classical.arbitrary X`, `Real.sqrt_le_sqrt` + `Real.sqrt_sq`), **`rayLength_ge`**
  (`2|Δ⟨φ⟩|/(hi − lo) ≤ Length(T)`; `div_le_iff₀` + `linarith`). Imports `TwoAxisResponse` for `priorExp_add_bdd`.
- `HalfspaceChernoff.lean` (NOT mirrored; Astra round 34 item 5): `featCgf ν R θ := log ∫ e^{dirLoss R θ} dν`,
  `empMean R n x i := (∑ₖ R i (x k))/n`, `sum_mul_empMean` (`u·R̄_n = (∑ₖ R_u(xₖ))/n`, `← mul_div_assoc, ← Finset.sum_div,
  Finset.mul_sum` then `Finset.sum_comm`), `integrable_exp_mul_of_bdd` (`Integrable.of_bound` with `e^{|λ|M}`),
  **`halfspace_chernoff`** (`(Measure.pi fun _ : Fin n ↦ ν).real {r ≤ u·R̄_n} ≤ exp(−n(λr − Λ_ν(λu)))`, `λ ≥ 0`:
  coordinates independent by `iIndepFun_pi (X := fun _ ↦ dirLoss R u)`, `mgf (Xₖ) P = mgf Y ν` through
  `integral_map (μ := P) (φ := Function.eval k) (f := …)` + `(measurePreserving_eval _ k).map_eq` (pass `μ φ f`
  explicitly — the eval is otherwise inferred as `fun f ↦ f k` and the rewrite fails), `iIndepFun.mgf_sum` +
  `Finset.prod_const`, `iIndepFun.integrable_exp_mul_sum`, Mathlib's `measure_ge_le_exp_mul_mgf`, event rewritten
  by `le_div_iff₀` + `linarith`, then `conv_lhs => rw [← Real.exp_log hpos]`, `← Real.exp_nat_mul, ← Real.exp_add`),
  `halfspace_chernoff_iInf` (`le_ciInf` over `Set.Ici 0`, `⟨0, Set.mem_Ici.2 le_rfl⟩`), `familyMeasure μ π L₀ R t a :=
  μ.withDensity (ofReal (e^{−t L_a} π / Z))`, `measurable_familyDensity` (needs `hπm`; `fun_prop`),
  `integral_familyMeasure` (`integral_withDensity_eq_integral_toReal_smul₀`, no boundedness needed), 
  `isProbabilityMeasure_familyMeasure` (`withDensity_apply _ MeasurableSet.univ`, `← ofReal_integral_eq_lintegral_ofReal`;
  `integrable_mul_affWeight_of_bdd … (t := t) a (Bdd.const 1)` — the implicit `t` must be pinned or `simp` faces
  `?m = t ∨ …`), **`featCgf_familyMeasure`** (`Λ_{P_{t,a}}(θ) = A_t(a − θ/t) − A_t(a)`: `sub_eq_add_neg, ← neg_smul,
  affLoss_add_smul_eq`, `← Real.exp_add`, `field_simp; ring`, `Real.log_div`), **`halfspace_chernoff_family`**.
- `HalfspaceProjection.lean` (NOT mirrored; Astra round 35 item 1) — NOTE `InformationProjection.lean` already exists
  (KL Pythagorean theorem, imported by `DataQuotient`): writing a new file under that name creates a Lake build
  cycle and clobbers the module; grep `Laplace/Multi/<Name>.lean` before creating a file. Content: `famKL μ π L₀ R t a b
  := mixKL (affLoss a) (dirLoss (b − a)) t 0 1` (= `KL(P_a‖P_b)`), `famCgf … a θ := A_t(a − t⁻¹•θ) − A_t(a)`,
  `famKL_eq` (Bregman, from `mixKL_aff_eq`), `famKL_nonneg` (`mixKL_eq_integral_mul_var … ht b a`, `segVar_nonneg`),
  `famCgf_eq_featCgf`, `famCgf_smul` (hypothesis-free: `smul_smul, inv_mul_eq_div`), pure sum identities
  `sum_sub_smul_mul`/`sum_sub_smul_sub_smul_mul`; with `a* = a − (λ/t)•u` and slackness
  `hslack : λ (u·m(a*) − r) = 0`: **`famKL_proj_eq`** (`KL(a*‖a) = λr − Λ_a(λu)`; `mul_div_cancel₀` + `linarith`),
  **`famKL_halfspace_decomp`** (`KL(b‖a) = KL(b‖a*) + λ(u·m(b) − r) + KL(a*‖a)`; `mixKL_three_point … b a a*` then
  `change` to `famKL` form, `mul_sub, Finset.sum_sub_distrib`, `linarith`), **`famKL_proj_le`** (primal),
  **`chernoff_rate_le_proj`** (dual: `famKL_nonneg a* c` with `c = a − (μ/t)•u`, `show t * (λ/t − μ/t) = λ − μ by
  field_simp`, `nlinarith [h0, μ(u·m(a*) − r) ≥ 0, hslack]`), `isLeast_famKL_halfspace`, `isGreatest_chernoffRate`,
  **`halfspace_chernoff_eq_projection`** (`P_a^{⊗n}(u·R̄_n ≥ r) ≤ exp(−n KL(a*‖a))`).
  `DataReachability.reachableResponse_ne_range` (`[Nonempty ι]`, inside the `hnd` block): compact = range would be
  clopen nonempty in `ι → ℝ` hence `univ`, contradicting `IsCompact.ne_univ` (`RealNormedSpace.noncompactSpace`).
- `JointChartMetric.lean` (NOT mirrored; Astra round 35 item 4): `natForm μ π L₀ R θ u v := Cov_θ(S_u, S_v)` (Fisher
  form in natural coordinates), `natLength η η' := ∫₀¹ √G(η', η')`, `dirLoss_jointStat_jointPoint`
  (`S_{(τ,ω)} = τ L₀ + R_ω`), `dirLoss_neg_mul_sub` (`R_{−τb − w} = −τ R_b − R_w`; `simp only [dirLoss, Finset.mul_sum,
  ← Finset.sum_sub_distrib]` then `sum_congr; ring`), `priorCov_residual_dirLoss` (`Cov(H, R_u) = 0` when `Cb = c`:
  `sum_mul_priorCov_eq` + `featCov_mulVec_apply` + `featObsCov` unfold + `priorCov_comm`), **`sliceInv_deriv_jointPoint`**
  (`D sliceInv (τ, v) = (τ, −τ b − C⁻¹ v)`: `ContinuousLinearEquiv.symm_apply_eq`, `hcoe` from `← coe_sliceMapEquiv; rfl`,
  `cases j`, `meanMapDeriv_apply` at `t = 1`, `priorCov_natCoord`, then `simp only [dirLoss_jointStat_jointPoint,
  dirLoss_neg_mul_sub, jointPoint_some]` — a `rw` leaves a beta-redex that blocks `priorCov_add_right_bdd` — bilinearity,
  `C b = c`, `C C⁻¹ v = v`), `dirLoss_jointStat_sliceInv_deriv` (score `τ H − R_{C⁻¹v}`), **`natForm_sliceInv_deriv`**
  (`G((τ,v),(τ',v')) = ττ' Var(H) + v'·C⁻¹v`; orthogonality lemmas oriented by a typed `have` + `rw [priorCov_comm]`),
  `natForm_temp_response_orth` (`omit [DecidableEq ι]` + `classical`), `natForm_temp_temp` (`= Var(H)`),
  `natForm_response_response` (`= v'·C⁻¹v`); path section: `hasDerivAt_priorExp_natPath` (`d/ds⟨φ⟩_{η s} = −Cov(φ, S_{η'})`),
  `abs_priorCov_le_sqrt_natForm`, **`abs_priorExp_sub_le_natLength`** (`|Δ⟨φ⟩| ≤ ((hi−lo)/2) natLength`; velocity continuity
  via `(continuous_obsMapDeriv …).comp hηc |>.clm_apply hη'` + `obsMapDeriv_apply`; Popoviciu in the joint family with
  `L₀ := 0`, `R := jointStat`, `t := 1`), **`natLength_ge`** (`2|Δ⟨φ⟩|/(hi−lo) ≤ natLength`).
- `RelativeEntropyGeometry.lean` (NOT mirrored; Astra round 35 item 3): `relEntropy μ π L₀ R θ := −mixKL (affLoss 0 S θ)
  (dirLoss S (0 − θ)) 1 0 1` (= `−KL(P_θ‖π̄)`), `natCoord_none/some` (rfl; `omit [MeasurableSpace X] [Fintype ι]`),
  `affLogZ_joint_zero` (`A(0) = log ∫π`), **`relEntropy_eq`** (`𝒮(θ) = ⟨θ, m(θ)⟩ + A(θ) − A(0)` from `natKL_eq θ 0`),
  **`relEntropy_natCoord`** (`𝒮 = t⟨L₀⟩ + t⟨a, m_t(a)⟩ + A_t(a) − log∫π`; `Fintype.sum_option`, `meanMap_natCoord_none/some`,
  `simp only […, mul_assoc]` closes the sum), `relEntropy_zero`, `relEntropy_nonpos` (`famKL_nonneg` in the joint family
  with `L₀ := 0, R := jointStat, t := 1`, then `unfold famKL`), **`hasDerivAt_relEntropy_path`** (`d𝒮 = −G_θ(θ, η')`;
  `(hasDerivAt_natKL_path 0 hη).neg` + `simp only [natForm, sub_zero]`), **`relEntropy_sub_eq`**
  (`𝒮(θ) − 𝒮(ϑ) = KL(ϑ‖θ) − ⟨θ, m(ϑ) − m(θ)⟩`), **`relEntropy_featureless_sub`** / `relEntropy_le_featureless` (Gibbs
  variational principle: equal loss expectation ⇒ `𝒮(t,0) − 𝒮(ϑ) = KL(ϑ‖(t,0)) ≥ 0`), **`hasDerivAt_relEntropy_temp`**
  (`d/dt 𝒮(tempPath M t) = −t Var(H)`: `dirLoss_jointStat_velocity`, `dirLoss_jointStat_natCoord` as a funext `have`,
  `priorCov_const_mul_left`, comm, a `rfl` equation exposing `affLoss a = L₀ + R_a` ONLY in the observable slot (a global
  `rw` would also hit the measure slot), `priorCov_add_right_bdd`, `priorCov_residual_dirLoss` twice).
- `ChartPathDerivatives.lean` (NOT mirrored; Astra round 35 item 2, part 1): `aOf θ i := θ (some i)/θ none`, `natCoord_aOf`,
  `natC/natc/natb/natH` (feature covariance, feature–loss covariance, regression coefficients `C⁻¹c`, residual, at a
  natural-coordinate point; `natb`/`natH` need `[DecidableEq ι]` for the inverse), transports `natC_eq_featCov`,
  `natc_eq_featObsCov`, `natCov_eq`, `natCum3_eq` (`conv_lhs => rw [← natCoord_aOf hθ]` then `priorCov_natCoord`),
  `isUnit_natC`, `natC_mulVec_natb` (normal equations), `natC_mulVec_apply`, `natCov_natH_dirLoss` (residual ⊥ features),
  `natCov_natH_self` (`Var H = Var L₀ − c·b`; `change` to the unfolded residual, a defeq `Bdd` witness for the lambda),
  `natCum3_natH_slot` (`κ₃(R_k, H, χ) = κ₃(R_k, L₀, χ) − ∑ b_j κ₃(R_k, R_j, χ)`); path section (`hθ : HasDerivAt θ θ' s₀`):
  **`hasDerivAt_natCov_path`** (`d/ds Cov = −κ₃(φ, ψ, S_{θ'})`, `hasDerivAt_cov_of_hasDerivAt_exp` with `c := 1`,
  `τ := fun _ ↦ 1`, `hE` from `hasDerivAt_priorExp_natPath`), `hasDerivAt_natC_path`/`natc_path`,
  **`differentiableAt_natb_path`** (`open scoped Matrix.Norms.Operator in`; `DifferentiableAt.inverse` on the matrix
  function, entries via `ContinuousLinearMap.proj … |>.differentiableAt.comp`, `Matrix.nonsing_inv_eq_ringInverse` to
  pass from `Ring.inverse` to `⁻¹`, `DifferentiableAt.fun_sum`), **`hasDerivAt_natb_path`** (`d/ds b = −C⁻¹ κ₃(R, H, S_{θ'})`:
  `b' := deriv`, differentiate the normal equations with `HasDerivAt.fun_sum` + `HasDerivAt.unique`, solve with
  `nonsing_inv_mul`; final `rw [← this, hCb', ← Matrix.mulVec_neg]; congr 1` — `congr 1` closes the Pi-negation goal, a
  following `funext` errors "no goals"), **`hasDerivAt_natVarH_path`** (`d/ds Var H = −κ₃(H,H,S_{θ'})` via
  `hasDerivAt_residual_form` with `hpos : ∀ s, 0 < θ s none` so the normal equations hold everywhere — no reparametrisation;
  `conv_rhs => rw [e, natCum3_eq, priorCum3_residual_expand]` then `simp only [← natCum3_eq]`).
- `LossHessian.lean` (NOT mirrored; Astra round 35 item 2, part 2 — THE UNIFIED HESSIAN): `chartDomain` (open:
  `isOpen_lt` ∩ preimage of `isOpen_interior`), `jointPoint_eq`, `lossChart p := ⟨L₀⟩_{sliceInv p}`,
  `lossGrad θ τ v := −τ Var_θ(H_θ) + v·b_θ`, `priorCum3_const_mul_left`, `dotProduct_natC_inv_mulVec` (symmetric inverse
  across `⬝ᵥ`: `dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_nonsing_inv`;
  `ᵀ` needs `open Matrix` — use `.transpose`), `tempPath_none_pos`, `aOf_tempPath`, `natC_tempPath`, `natb_tempPath`
  (`natb (tempPath M t) = regCoeff M t`), **`chartScore_eq`** (`S_{(τ,v)} = τ H − (C⁻¹v)·R` in `natH/natC` form),
  **`exists_chartLine`** (σ-trick: `σ s := if p₀ + s•Y ∈ chartDomain then s else 0`, `∀ s, 0 < θ s none`,
  `θ 0 = tempPath`, `HasDerivAt θ (D sliceInv Y) 0`; the strict-derivative point must be rewritten through a `have hsm :
  sliceMap (tempPath M t₀) = jointPoint t₀ M` since `tempPath` is not syntactically `sliceInv (jointPoint …)`; write
  `fun s : ℝ ↦ … + s • Y` and `(0 : ℝ)` in ALL statements or `s` and `0` elaborate as `ℕ`), **`hasDerivAt_lossChart_line`**
  (`D h[(τ,v)] = −τ Var(H) + v·b`; eventual equality named with an explicit type before `congr_of_eventuallyEq`;
  `Cov(L₀,H) = Var H` via a `rfl` equation unfolding only the FIRST slot; `Cov(L₀, R_{C⁻¹v}) = v·b` via `change` to the
  unfolded `natb` then `← dotProduct_natC_inv_mulVec`), **`hasDerivAt_lossGrad_line`** (`D²h[X,Y] = κ₃(H, S_X, S_Y)`:
  `hasDerivAt_natVarH_path` + `hasDerivAt_natb_path` through `HasDerivAt.fun_sum`, trilinearity of κ₃ after `natCum3_eq`
  transport, `priorCum3_const_mul_left`, `priorCum3_dirLoss_left`).
- `InteriorThreshold.lean` (NOT mirrored; Astra round 36 item 2): `priorExp_const_mul_loss` (`⟨φ⟩_{cL, s} = ⟨φ⟩_{L, sc}`,
  pure), `priorExp_neg_obs`; face section (FaceInfinite variables): **`priorExp_face_ge`** (`α ≤ ⟨V⟩_λ`; `integral_mono_ae`),
  **`priorExp_face_sub_le`** (`⟨V⟩_λ − α ≤ ε + (M+|α|) q_λ({V<α+ε}ᶜ)`; split with `integral_add_compl₀`, `setIntegral_mono_on`,
  `setIntegral_le_integral`; Pi-subtraction congruence needs `simp only [Pi.sub_apply]; ring`; `omit hα in`, so callers pass
  `(α := α)`), **`tendsto_priorExp_face_inf`** (`⟨V⟩_λ → α` with only accessibility `∀ε>0, ∫_{V<α+ε}π > 0` — NO positive-mass
  face; `tendsto_order`, `tendsto_tilt_mass_compl`, `gt_mem_nhds`); family section: `thresholdFun a u λ := ⟨R_u⟩_{a − (λ/t)u}`,
  `thresholdFun_zero`, `thresholdFun_eq_sum` (pass the `tiltData_aff` arguments explicitly), `sub_div_smul_eq`,
  **`hasDerivAt_thresholdFun`** (`= Var_{a_λ}(R_u)` via `hasDerivAt_priorExp_line` with `v := −(1/t)•u`),
  `thresholdFun_monotone/continuous`, `thresholdFun_strictMono` (`segVar_pos`; `unfold segVar at this; rwa [zero_smul,
  add_zero]`), `affLoss_affLoss`, **`tendsto_thresholdFun`** (`→ β` = ess sup of `u·R`, hypotheses `hβ : ∀ᵐ x, u·R ≤ β`,
  `hmass : ∀ε>0, 0 < ∫_{β−ε<u·R} π`; transport to the tilt of `π' = e^{−tL_a}π` by `V' = −u·R` via `affLoss_affLoss`,
  `priorExp_ray_eq_tilted`, `dirLoss_smul`, `priorExp_const_mul_loss`; mass transfer through
  `setIntegral_pos_iff_support_of_nonneg_ae` with `support ∩ S = S` by `Set.inter_eq_right`), **`exists_threshold_tilt`**
  (`intermediate_value_Icc`), **`exists_halfspace_projection`**, **`chernoff_rate_eq_inf_KL`** (`sSup = sInf` via
  `IsGreatest.csSup_eq`/`IsLeast.csInf_eq`).
- `LossHessianBlocks.lean` (NOT mirrored; Astra round 36 audit): `dirLoss_zero_vec`, `priorCum3_neg_left`,
  **`lossHessian_symm`** (`κ₃(H,S_X,S_Y) = κ₃(H,S_Y,S_X)`, `priorCum3_swap₂₃`; no `ht`/`hM` needed), **`lossHessian_temp_temp`**
  (`κ₃(H,H,H)`; `chartScore_eq` + `simp only [Matrix.mulVec_zero, dirLoss_zero_vec, one_mul, sub_zero]`),
  **`lossHessian_temp_response`** (`−κ₃(H,H,(C⁻¹v)·R)`), **`lossHessian_response_response`** (`κ₃(H,(C⁻¹v)·R,(C⁻¹w)·R)`; signs
  moved through `priorCum3_swap₁₂/₂₃` + `priorCum3_neg_left`).
- `ChartSynthesis.lean` (NOT mirrored; Astra round 36 item 1): `continuous_sliceMap`, `continuous_jointLoss`,
  `continuous_relEntropy` (via `relEntropy_eq`, `continuous_meanMap`, `hasFDerivAt_affLogZ` — both take `∀ x, 0 ≤ π x`),
  `sliceMap_mem_chartDomain` (`range_meanMap_slice` at `t := θ none`), `sliceInv_mem_source`, `sliceMap_sliceInv'`
  (chart-domain forms via `jointPoint_eq`), **`responseChart : PartialHomeomorph`** (source `{θ | 0 < θ none}`, target
  `chartDomain`; this Mathlib's `PartialHomeomorph` has NO `open_source`/`open_target` fields — only the two `continuousOn`
  fields on top of `PartialEquiv`), simp lemmas `responseChart_apply/symm_apply/source/target`, **`responseChart_bijOn`**
  (`.toPartialEquiv.bijOn`), `continuousOn_sliceInv`, **`continuousOn_lossChart`**, **`continuousOn_relEntropy_chart`**.
- `ArcsineLength.lean` (NOT mirrored; Astra round 35/36 "arcsine"): **`arcsin_speed_bound`** (pure: `|2·(1/√(1−√(p/d)²))·((m'/d)/(2√(p/d)))| ≤ √G`
  from `|m'| ≤ √V√G`, `V ≤ pq`, `p+q = d`; `Real.sqrt_div'`, then `set st := √d` + `d = st*st` BEFORE `field_simp` — a
  `rw [← hdd]` on `√d * √d = d` also rewrites the `d` inside `√d`; `field_simp` closes the identity, no `ring`),
  **`priorCov_self_le_mul_of_bounds`** (Bhatia–Davis `Var φ ≤ (⟨φ⟩−lo)(hi−⟨φ⟩)`: `E[(φ−lo)(hi−φ)] ≥ 0` via
  `priorExp_mono_bdd` + linearity), **`natLength_ge_arcsin`** (`2|arcsin√z(1) − arcsin√z(0)| ≤ natLength`, hypothesis
  `hint : ∀ s, lo < ⟨φ⟩_{η s} < hi`; chart derivative via `Real.hasDerivAt_arcsin (hsqm1) (hsq1) |>.comp s (hz.sqrt …)`,
  `Real.sqrt_eq_one`, continuity of the chart derivative from `Continuous.div … (h ≠ 0)` and `Continuous.sqrt`; FTC + the
  pointwise bound).
- `CompactCoverCramer.lean` (NOT mirrored; Astra round 34/36 item "compact-cover Cramér"): `halfspace_chernoff_one` (`λ = 1`,
  `simpa`), **`finite_union_chernoff`** (`P(R̄_n ∈ ⋃_{k∈s} {θ_k·y ≥ c_k}) ≤ ∑ e^{−n(c_k − Λ(θ_k))}`; set identity by `ext; simp`,
  `measureReal_biUnion_finset_le`), **`compact_cover_chernoff`** (`∀ x ∈ F, ∃ θ, α < θ·x − Λ(θ)` ⇒ `∃ N, ∀ n ≥ 1,
  P(R̄_n ∈ F) ≤ N e^{−nα}`: totalise the witness (`∀ x, ∃ θ, x ∈ F → …`) so `choose` yields a plain function, strict
  halfspaces `U x` open by `isOpen_lt`, `IsCompact.elim_finite_subcover`, `measureReal_mono` (probability measure discharges
  the finiteness autoparam), `Finset.sum_const, nsmul_eq_mul`).
- `DataLocus.lean` (NOT mirrored; Astra round 37 item 1 — the data → posterior arrow): `dataCoeff a : (J → ℝ) →L[ℝ] (ι → ℝ)`
  (`∑ j, (proj j).smulRight (a j)`, `dataCoeff_apply` by `simp [dataCoeff]`), `dataCoeff_mem_reachableCoeff`, `dataResponse`,
  `dataMetric` (`responseForm` pulled back), `dataLoss'` (NOTE `dataLoss` is taken by DataMixture), `dataLossGrad`, `dataEntropy`,
  `hasDerivAt_natCoord_line` (`HasDerivAt (fun s ↦ natCoord t (b + s•v)) (natTangent t b 0 v) 0`, `hasDerivAt_pi` + `cases`),
  **`hasFDerivAt_dataResponse`** (`(hasFDerivAt_meanMap … hZ).comp w (dataCoeff a).hasFDerivAt`), `dataResponse_deriv_apply`,
  **`dataResponse_deriv_eq_zero_iff`** (kernel = `L⁻¹(N)` via `featCov_mulVec_eq_zero_iff` + `featCov_mulVec_apply`),
  `dataResponse_add_of_invisible` (`meanMap_add_of_invisible` takes NO hypotheses), **`dataMetric_self_eq_zero_iff`**,
  **`hasFDerivAt_dataLoss`**, `dataLoss_deriv_apply`, **`hasDerivAt_dataLossGrad_line`** (e-Hessian `t²κ₃(L₀, R_{Lh}, R_{Lk})`;
  pass the observable to `bdd_dirLoss` explicitly), **`hasDerivAt_dataEntropy_line`** (`−t² Cov(L_w, R_{Lk})` via
  `hasDerivAt_relEntropy_path`, `dirLoss_jointStat_natCoord/natTangent`).
- `NaturalJourney.lean` (NOT mirrored; Astra round 37 item 2): `hasDerivAt_natRay` (`fun s ↦ s • θ`; the Pi norm needs
  `Fintype (Option ι)` so keep the instance and `set_option linter.unusedFintypeInType false in`),
  **`relEntropy_natRay_eq_integral`** (`𝒮(θ) = −∫₀¹ s G_{sθ}(θ,θ)`; `natKL_segment_eq_integral 0 θ` + `simp only [zero_add]`),
  **`hasDerivAt_relEntropy_natRay`** (`−s G_{sθ}(θ,θ)`; `dirLoss_smul` + `priorCov_const_mul_left`),
  **`relEntropy_natRay_antitoneOn`** (`antitoneOn_of_deriv_nonpos (convex_Ici 0)`, `interior_Ici`), `abs_priorExp_sub_le_natRay`,
  `natRay_ge_arcsin` (instances with `simpa only [one_smul, zero_smul]`), **`relEntropy_natCoord_decomp`**
  (`𝒮(t,a) = 𝒮(t,0) − famKL a 0 + t(⟨L₀⟩_{t,a} − ⟨L₀⟩_{t,0})`; `mixKL_three_point … (t := 1) (natCoord t a) 0 (natCoord t 0)`,
  `Fintype.sum_option`, `natKL_natCoord` to `famKL`; `simp` turns `0 − x` into `−x`, so `simp only [zero_sub]` on the goal
  before `linarith`).
- `MixtureBending.lean` (NOT mirrored; Astra round 37 item 3): `centredFeat Zᵢ = Rᵢ − ⟨Rᵢ⟩`, `whitenedDir V_v = R_{C⁻¹v}`,
  `prodObs = V_vV_w`, `mixBend 𝓑(v,w) = V_vV_w − ⟨V_vV_w⟩ − dirLoss Z (C⁻¹⟨Z V_vV_w⟩)`; `prodObs_comm`, **`mixBend_comm`**
  (`unfold mixBend; rw [prodObs_comm …]` — `simp only [mixBend, prodObs_comm]` makes no progress), `bdd_centredFeat`,
  `priorExp_centredFeat` (= 0), **`priorExp_centredFeat_mul`** (`⟨Zᵢφ⟩ = Cov(Rᵢ,φ)`), `priorExp_centredFeat_mul_centredFeat`
  (`⟨ZᵢZⱼ⟩ = Cᵢⱼ`; final `rfl` through `Matrix.of_apply`), **`priorExp_mixBend_eq`** (the linear structure `⟨φ𝓑⟩ = ⟨φV_vV_w⟩ −
  ⟨V_vV_w⟩⟨φ⟩ − ∑ dᵢ⟨φZᵢ⟩`; identity proved after `rw [← hd, ← hc]` to refold the `set` variables that `unfold` re-exposes,
  `priorExp_dirLoss` for the sum), **`priorExp_mixBend`** (`⟨𝓑⟩ = 0`), **`priorExp_centredFeat_mul_mixBend`** (Fisher-normality
  `⟨Zⱼ𝓑⟩ = 0`: the sum is `(C(C⁻¹e))ⱼ = eⱼ`, `change` to the `mulVec` sum then `Finset.sum_congr … mul_comm`),
  **`priorExp_residual_mul_mixBend`** (`⟨H𝓑(v,w)⟩ = κ₃(H,V_v,V_w)`: `⟨HZᵢ⟩ = 0` by `priorCov_residual_dirLoss` at
  `Pi.single i 1` + `dirLoss_pi_single`; unapplied `prodObs` must be unfolded by a `rfl` equation — `simp only [prodObs]`
  only fires on applied occurrences; `beta_reduce at hv hw`; `linear_combination ⟨V_w⟩ * hv + ⟨V_v⟩ * hw`; needs neither
  `hnd` nor `ht`). Calls of `priorExp_mixBend_eq` in a `have` need `(t := t)` and `(φ := …)` pinned.
- `ProductDensity.lean` (NOT mirrored; infrastructure for the tilt lower bound): `indicator_pi_prod` (indicator of a box =
  product of coordinate indicators, by cases with `Set.mem_univ_pi`), **`Measure.pi_withDensity_ofReal`**
  (`(P.withDensity (ofReal ∘ r))^{⊗n} = P^{⊗n}.withDensity (ofReal ∏ r(xₖ))` for bounded nonnegative measurable `r` with the
  density measure a probability measure — NOT in Mathlib; via `Measure.pi_eq` on boxes, `ofReal_integral_eq_lintegral_ofReal`,
  and the BOCHNER finite-product Tonelli `integral_fintype_prod_eq_prod` (the `lintegral` version has no findable name),
  `ENNReal.ofReal_prod_of_nonneg`, `ENNReal.ofReal_toReal`), **`measureReal_pi_ge_of_density_ge`** (`c · P^{⊗n}(A) ≤ Q^{⊗n}(A)`
  when `∏ r ≥ c` on `A`; take finiteness from `Q^{⊗n}` BEFORE rewriting it as a density — the rewritten form has no
  `IsFiniteMeasure` instance).
- `TiltLowerBound.lean` (NOT mirrored; Astra round 37 item 5): **`familyMeasure_eq_withDensity_tilt`** (`P_a = P_b.withDensity
  (ofReal e^{−(λu·R − Λ_a(λu))})`, `b = a − (λ/t)u`: `withDensity_mul₀` backwards, pointwise `ENNReal.ofReal_mul`, exponent
  identity and the regrouping as separate `have`s proved by `field_simp; ring` / `ring` — `show … by …` inside `rw` is
  fragile — `Real.exp_log`, `field_simp`), `famKL_tilt_eq` (`KL(b‖a) = λ u·m(b) − Λ_a(λu)`), `integrable_coord_pi`,
  `integral_coord_pi` (`integral_map (φ := Function.eval k)` + `measurePreserving_eval`), `integral_empSum` (`= n⟨f⟩`),
  `memLp_two_of_bdd`, `variance_empSum` (`= n Var f` via Mathlib's `variance_sum_pi`), **`measureReal_empMean_far_le`**
  (Chebyshev `P(|f̄_n − ⟨f⟩| ≥ ρ) ≤ Var f/(nρ²)` from `meas_ge_le_variance_div_sq`; `field_simp` closes the ratio),
  `measurableSet_empMean_near` (`MeasurableSet.iInter` needs `Countable ι` from `[Fintype ι]` — keep the instance and
  `set_option linter.unusedFintypeInType false in`), **`measureReal_empMean_near_ge`** (`1 − ∑ Varᵢ/(nρ²) ≤ P_b^{⊗n}(near)`;
  `measureReal_compl` + `P.real univ = 1` via `measureReal_def, measure_univ, ENNReal.toReal_one`;
  `measureReal_iUnion_fintype_le _` takes ONE explicit argument; `omit ht`, so callers pass `(t := t)`),
  **`tilt_lower_bound`** (`∃ N, ∀ n ≥ N, e^{−n(KL(b‖a)+δ)} ≤ P_a^{⊗n}(∀ i, |R̄ᵢ − mᵢ(b)| < ε)`: radius
  `ρ = min ε (δ/(2(λS+1)))`, `S = ∑|uᵢ|`; product density `= e^{−n(λ u·R̄_n − Λ)}` via `← Real.exp_sum` and
  `∑ₖ R_u(xₖ) = n u·R̄_n`; `measureReal_pi_ge_of_density_ge`; Chebyshev with `N = max (⌈2V/ρ²⌉₊+1) (⌈2 log 2/δ⌉₊+1)`;
  `rw [← Finset.sum_div, ← hV]` to fold the variance budget).
- `MeanJourney.lean` (NOT mirrored; Astra round 38 top pick, duality capstone part 1): `meanLine y₀ d s := θ(y₀ + s d)`
  (the coefficient of a mean segment), `meanSpeed := d ⬝ᵥ (featCov (meanLine s))⁻¹ *ᵥ d` (needs `[DecidableEq ι]`),
  `meanEntropy M := −famKL (θ M) 0`; `segment_mem_interior_momentBody` (`(convex_momentBody R).interior.add_smul_sub_mem`),
  `meanMap_mem_interior`, `meanMap_meanLine` (`Function.invFun_eq` + `range_meanMap_slice`), `meanLine_zero/one`,
  **`hasDerivAt_meanLine`** (`hasStrictFDerivAt_invFun_meanMap` at `meanLine s`, point rewritten by `meanMap_meanLine`, then
  `.comp_hasDerivAt s (hasDerivAt_affineLine …)`; derivative `invJac (meanLine s) d`), `dualHessian_eq_inv_mulVec`
  (`calc` through `(C⁻¹ C) *ᵥ x`, never `rw [← h]` on a term whose RHS contains the LHS), `invJac_apply_eq`
  (`= (−t)⁻¹ • C⁻¹ d`), `hasDerivAt_dualPotential_meanLine` (`−t ⟨d, a(s)⟩`), **`hasDerivAt_meanLine_pairing`**
  (second derivative `= meanSpeed`; `hasDerivAt_pi.mp` per coordinate + `HasDerivAt.fun_sum`, close with `field_simp`
  after `rw [invJac_apply_eq]`), `meanSpeed_nonneg` (`d = C w`, `d ⬝ C⁻¹ d = Var(R_w)`; make the point and `w` opaque with
  `obtain ⟨a, ha⟩ : ∃ a, … = a := ⟨_, rfl⟩` before `conv_lhs => rw [← hd]`, or `rw` sees through `set`), `continuous_featCov`
  (`continuous_matrix` + `continuous_obsMap` on the three products), `continuousOn_meanSpeed` (`continuousAt_matrix_inv _
  (NormedRing.inverse_continuousAt (Units.mk0 _ hdet))`; compose with `ContinuousAt.comp_continuousWithinAt (g := Inv.inv)
  (f := …) (x := s)` — all three named, or the unifier takes `f := featCov`), `hasDerivAt_meanJourney_primitive`
  (`(1−s) I' + I`), **`famKL_eq_integral_meanSpeed`** (FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt` with `f`, `f'`
  named, `uIcc_of_le zero_le_one`; endpoints via `mixKL_eq_bregman_dual` and `dotJ_comm`; replace the means by opaque `y₀ y₁`
  with `rw [hy₀, hy₁]` on the goal BEFORE `rw [hFTC]`), **`famKL_e_journey_eq_m_journey`**,
  **`famKL_add_famKL_eq_integral_meanSpeed`** (Jeffreys; `linear_combination t * hs` with the sums as atoms),
  `sq_integral_sqrt_meanSpeed_le` (`sq_integral_sqrt_mul_le` with `g = 1`, `simpa`), `meanEntropy_meanMap`,
  `meanEntropy_eq_dual` (`dotJ_zero_left`), **`meanEntropy_concaveOn`** (`dualPotential_convexOn.neg.add_const` + `.congr`),
  `hasDerivAt_meanEntropy_line` (eventual equality on the open response space via `preimage_mem_nhds`),
  `hasDerivAt_meanEntropy_line_deriv` (`Pi.neg_apply` before `ring`), `meanEntropy_eq_neg_integral`,
  **`meanEntropy_line_antitoneOn`** (`antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (f := fun s : ℝ ↦ …)` — annotate `s : ℝ`
  in the STATEMENT too, else `s • v` elaborates with `s : ℕ`; `interior_Icc`, FTC on `0..s`, `dotJ_zero_right`).
- `ResponseStability.lean` (NOT mirrored; Astra round 38 item 3): `integral_one_sub_mul_const` / `integral_id_mul_const`
  (pure real lemmas BEFORE the section, else every section hypothesis is auto-included), `dotProduct_featCov_mulVec`
  (`u ⬝ C_a v = Cov(R_u,R_v)`; `omit [Nonempty X]`), **`sq_dotProduct_featCov_le`** (Cauchy–Schwarz for the covariance form
  from `TiltData.abs_tiltCov_le` + `priorCov_eq_tiltCov_zero`; pass `(t := t)` to `priorCov_self_nonneg'`),
  `dotProduct_featCov_mulVec_le_of_bounds` (`Var(R_v) ≤ (∑ Mᵢ²)‖v‖²`: `Var ≤ ⟨φ²⟩`, `priorExp_mono_bdd`, `priorExp_const_fun`,
  `Finset.sum_mul_sq_le_sq_mul_sq`), **`mul_meanSpeed_le`** (`α q ≤ ‖Δ‖²`, dot-product CS + `nlinarith`),
  **`le_mul_meanSpeed`** (`‖Δ‖² ≤ β q`: covariance-form CS with `u = Δ`, `v = C⁻¹Δ`; `rw [hd] at hcs` rewrites BOTH
  `C *ᵥ w` — restore with `dotProduct_comm w d, hqw`; the strict case needs `le_of_mul_le_mul_left` through an explicit
  `calc` — `nlinarith` fails), `sq_dist_meanMap_le_famKL` (`‖Δm‖² ≤ 2β KL`), `famKL_le_sq_dist_meanMap` (`2α KL ≤ ‖Δm‖²`)
  via `intervalIntegral.integral_mono_on zero_le_one hf hg h` (interval integrability from
  `Continuous.intervalIntegrable 0 1` — explicit endpoints, and a TYPED `have hc : Continuous fun s ↦ …` or the
  Pi-product form does not match), `segVar_eq_dotProduct`, `famKL_le_sq_dist_coeff` / `famKL_ge_sq_dist_coeff`
  (`t²α‖Δa‖² ≤ 2KL ≤ t²β‖Δa‖²`), **`sq_dist_meanMap_le`** / **`le_sq_dist_meanMap`** (bi-Lipschitz
  `(αt)²‖Δa‖² ≤ ‖Δm‖² ≤ (βt)²‖Δa‖²`), `sq_dist_meanMap_le_of_bounds` (unconditional Lipschitz with `β = ∑ Mᵢ²`).
  Theorems whose statement has no matrix inverse take `[Nonempty ι]` explicitly and `classical` in the proof.
- `FullMeanGeometry.lean` (NOT mirrored; round-38 capstone in the FULL geometry): the joint family is the affine family
  `(L₀ := 0, R := jointStat L₀ R, t := 1)`, so `DualPotential`/`MeanJourney` instantiate under the JOINT nondegeneracy
  `hjnd : ∀ v : Option ι → ℝ, v ≠ 0 → ¬∃ c, ∀ᵐ x, π x ≠ 0 → dirLoss (jointStat L₀ R) v x = c`. `fullMean θ := meanMap 0 S 1 θ`,
  `abs_zero_fun_le` (pass as the base-loss bound with `measurable_const`, `bdd_jointStat hL₀m hL₀ hR`, `one_pos`),
  `relEntropy_eq_meanEntropy` (`meanEntropy_meanMap` + `rfl`: `relEntropy θ = −famKL_joint θ 0` definitionally),
  `fullMean_mem_interior`, **`relEntropy_concaveOn_fullMean`** (`meanEntropy_concaveOn` by defeq — `exact` unfolds `fullMean`),
  **`hasDerivAt_relEntropy_fullMean_line`** (gradient `⟨Δ, θ(s)⟩`; `congr_deriv (one_mul _)`),
  **`hasDerivAt_relEntropy_fullMean_line_deriv`** (`−Δ ⬝ G⁻¹ Δ`; `congr_of_eventuallyEq (of_forall fun u ↦ (one_mul _).symm)`),
  **`natRay_cost_eq_fullMean_cost`** (`∫ s G_{sθ}(θ,θ) = ∫ (1−s) Δ·G⁻¹Δ`; from `famKL_e_journey_eq_m_journey 0 θ`,
  `one_pow, one_mul`, `simp [segVar, natForm]` under `intervalIntegral.integral_congr`),
  `relEntropy_eq_neg_integral_fullMean`, `relEntropy_fullMean_line_antitoneOn`. Everything is by instantiation — zero new
  analysis; the joint nondegeneracy is the only new hypothesis.
- `AsymptoticUpperBound.lean` (NOT mirrored; round-38 item 4, compact case): `eventually_measureReal_empMean_le`
  (`∃ N₀, ∀ n ≥ N₀, 0 < n → P(R̄_n ∈ F) ≤ e^{−n(α−ε)}`, `N₀ = ⌈log N/ε⌉₊`, `Nat.ceil_le`, `Real.log_le_iff_le_exp`,
  `N = 0` case separately), `eventually_measureReal_empMean_le'` (`∀ᶠ n in atTop`, via `max N₀ 1`),
  `eventually_log_measureReal_empMean_div_le` (`log P/n ≤ −(α−ε)` under `0 < P`; `Real.log_le_log`, `Real.log_exp`,
  `div_le_iff₀`). The `limsup ≤ −α` form is deliberately NOT stated through `Real.log 0`.
- `ContractionIdentity.lean` (NOT mirrored; Astra round 37 item 4 / round 38 item 5): **`priorCum3_dirLoss_slot`** /
  `priorCum3_dirLoss_slot₃` (κ₃ multilinear over feature combinations, generic `L`/`hν`; rewrite each product as a
  `dirLoss` of a product family and use `priorExp_dirLoss`, then `simp only [Finset.sum_mul, Finset.mul_sum,
  ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]` + termwise `ring`), **`priorCum3_eq_priorCov_centred`**
  (`κ₃(φ,ψ,χ) = Cov(φ,(ψ−⟨ψ⟩)(χ−⟨χ⟩))`; make the means opaque with `obtain ⟨b, hb⟩ : ∃ b, … = b`, expand with
  `priorExp_add_bdd`/`priorExp_const_mul_bdd`/`priorExp_const_fun`, `ring`), `cum3Mat` (`T_pq = κ₃(H,R_p,R_q)`), `respHess`
  (`K_ij` = the response block on `Pi.single`), `contractObs` (`Q = Zᵀ C⁻¹ Z`), `natC_transpose` (use `.transpose`, `ᵀ` needs
  `open Matrix`), `natC_inv_apply_symm` (`Matrix.transpose_nonsing_inv`), `lossHessian_response_apply_eq_respHess`,
  **`respHess_eq`** (`K = C⁻¹ T C⁻¹`: `Matrix.mulVec_single_one` + `Matrix.col_apply`, two slot expansions, `Finset.sum_comm`,
  symmetry, `ring`), **`trace_natC_respHess`** (`tr(CK) = tr(T C⁻¹)`), **`trace_cum3Mat_inv_eq_cov`** (`= Cov(H,Q)`: `Q` as
  `dirLoss` over `ι × ι` via `Fintype.sum_prod_type'`, `sum_mul_priorCov_eq`, `Laplace.Patterning.trace_mul_eq_double_sum`),
  `trace_natC_respHess_eq_cov`, **`hasDerivAt_log_det_natC_tempPath`** (`d/dt log det C|_M = −tr(CK)`:
  `Laplace.Patterning.hasDerivAt_log_det` on `t ↦ natC (tempPath M t)` with `hasDerivAt_natC_path (hθ := hasDerivAt_tempPath)`;
  the velocity's score is `natH` by `chartScore_eq … 1 0` after `Pi.single none 1 = jointPoint 1 0`; then two
  `trace_mul_eq_double_sum`, `Finset.sum_comm`, `priorCum3_swap₂₃, priorCum3_swap₁₂`), `hasDerivAt_log_det_natC_tempPath_cov`.
  Pin `(M₀ := 0)` when passing `(fun x ↦ by simp)` as the zero base-loss bound, else `0 ≤ ?m` is left unsolved.
- `ResponseStability.lean` LOCALISED (Astra round 39 audit: a GLOBAL covariance lower bound is impossible for bounded
  features — the global co-Lipschitz bound would map an unbounded parameter space into a bounded response body): the
  mean-side theorems now assume ellipticity only along the lifted mean segment `meanLine (m a₀) (m a₁ − m a₀) s`, the
  natural-side ones only along `a₀ + s(a₁ − a₀)`, the bi-Lipschitz theorems take both (`hm`, `hn`); global versions are
  wrappers (`le_sq_dist_meanMap_of_global`, `sq_dist_meanMap_le_of_bounds`).
- `ProfileGeometry.lean` (NOT mirrored; Astra round 39 top pick): **`profile_gap_eq_famKL`**
  (`J(μ(θ)) + t u(θ) − I_t(m_t a) = KL(P_θ ‖ P_{t,a})` when `θ` and `a` share the response; `unfold fullMean at hM ⊢`,
  `natKL_eq`, `affLogZ_natCoord`, both `dualPotential_meanMap`, then `simp only [dotJ, Fintype.sum_option, natCoord_none,
  natCoord_some, hM, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]; ring`), `profile_gap_self`
  (`meanMap_natCoord_some π L₀ R t a i` — EXPLICIT `π L₀ R t a`), `profile_le` (from `famKL_nonneg` of the joint family),
  `dualPotential_add_affLogZ_zero` (`I_t(m a) + A_t 0 = KL(P_a‖P_0)`), `profile_rate_contraction`,
  **`famKL_pythagoras_slice`** (`KL(P_θ‖P_{t,b}) = KL(P_θ‖P_{t,a}) + KL(P_{t,a}‖P_{t,b})`; pure Bregman algebra, the cross
  pairing vanishes by `hM`), **`hasFDerivAt_relEntropy_fullMean`** (gradient `dotCLM θ` in full mean coordinates; eventual
  equality on the open range, `unfold fullMean` BEFORE `meanEntropy_eq_dual`), `hasDerivAt_relEntropy_fullMean_path`
  (`d𝒮/ds = ⟨θ, μ'⟩` along any differentiable full mean path). `[Nonempty ι]` is NOT needed anywhere here.
- `FluctuationResponse.lean` (NOT mirrored; round-39 small corollary): `variance_familyMeasure` (Mathlib's
  `variance_eq_sub (hX : MemLp X 2 μ)` — `variance_def'` does not exist; `Pi.pow_apply`, `integral_familyMeasure (t := t)`),
  `sum_mul_empMean_eq` (`v·R̄_n = (1/n) ∑ₖ R_v(xₖ)`), **`variance_empMean_dir`** (`Var(v·R̄_n) = v⬝Cov v / n` via
  `variance_const_mul`, `variance_empSum`; `omit ht`), **`variance_empMean_dir_eq_meanMapDeriv`** (`= −v⬝Dm v/(nt)`).
- `WallRay.lean` (NOT mirrored; round-39 first wall theorem): `thresholdFun_le` (`omit ht`, callers pass `(t := t)`),
  **`segVar_ray_le`** (Bhatia–Davis `priorCov_self_le_mul_of_bounds` with `lo = −‖R_u‖∞`, `hi = β`:
  `Var ≤ (Mu+|β|)(β − u·m)`; `omit ht`), `tendsto_dot_meanMap_ray` (`tendsto_thresholdFun` + `thresholdFun_eq_sum (t := t)`),
  **`tendsto_segVar_ray`** (squeeze `tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup`),
  `tendsto_responseForm_ray`. Hypotheses: an EVERYWHERE bound `∀ x, R_u x ≤ β` (Bhatia–Davis is pointwise) and the mass
  condition `∀ ε > 0, 0 < ∫_{β−ε < R_u} π`.
- `LargeDeviationBounds.lean` (NOT mirrored; round-39 LDP): `abs_empMean_le` (the empirical response lies in the feature
  box; `omit [MeasurableSpace X] [Fintype ι] … hR` — then `ν` is NOT an argument), **`closed_cover_chernoff`** (closed `F`:
  `F ∩ B` compact via `isCompact_univ_pi` + `IsCompact.inter_left`; the event set equals `{R̄_n ∈ F ∩ B}` by
  `Set.mem_univ_pi`; witnesses only needed on `F ∩ B`), `eventually_measureReal_empMean_le_closed`, **`open_lower_bound`**
  (`tilt_lower_bound` with `u := t•(a−b)`, `lam := 1`; `a − (1/t)•(t•(a−b)) = b` by `smul_smul, one_div_mul_cancel,
  one_smul, sub_sub_cancel`; `Metric.isOpen_iff`, `dist_pi_lt_iff`, `Real.dist_eq`, `measureReal_mono`),
  `eventually_le_log_measureReal_empMean_div`.
- `SchurComplement.lean` (NOT mirrored; round-39 bundle item C): `jointCov_mulVec_none/some` (block rows of the joint
  `featCov` by `simp only [Matrix.mulVec, dotProduct, featCov, Matrix.of_apply, Fintype.sum_option, natc, natC, jointStat,
  Option.elim_none, Option.elim_some]`), **`natVarH_pos`** (`Var(H) > 0` under `hjnd`: `ae_eq_const_of_priorCov_self_eq_zero`
  returns `∀ᵐ x, φ x = ⟨φ⟩` — NOT `∃ c`; the witness direction is `fun j ↦ j.elim 1 (fun i ↦ −b i)`; the `.congr` for the
  weight integrability needs its TARGET TYPE annotated), **`dotProduct_jointCov_inv`** (`d ⬝ G⁻¹ d = d_R ⬝ C⁻¹ d_R +
  (d₀ − b·d_R)²/Var(H)`: exhibit `w = (τ, C⁻¹(d_R − τc))` with `τ δ = d₀ − b·d_R`, verify `G w = d` blockwise
  (`linear_combination hτ − τ * hδeq` on the base row), then `G⁻¹ d = w` by a `calc` — never `rw [← hGw]` when `d` also sits
  inside `w`'s definition), `dotProduct_natC_inv_le_jointCov_inv` (minimal lift), `dotProduct_jointCov_inv_slice_tangent`
  (equality at `d₀ = b·d_R`). Symmetry of `C⁻¹` via `Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
  Matrix.transpose_nonsing_inv, natC_transpose`.
- `JourneyEnergy.lean` (NOT mirrored; round-40 item 4): `natural_energy_eq` (`t²∫₀¹ Var_{a(s)}(R_{Δa}) = −t Δa·Δm` via FTC on
  `hasDerivAt_segMean`, `priorExp_dirLoss`, then `simp only [dotJ, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, meanMap]`
  — `meanMap` must be in the simp set), `famKL_add_famKL_eq_neg_mul_dot` (Jeffreys `= −t Δa·Δm`; `omit ht`),
  **`natural_energy_eq_mean_energy`** (`E_e = E_m`), `sq_natural_length_le_jeffreys`.
- `TemperatureCompatibility.lean` (NOT mirrored; round-40 item 2; the first law `∂_t I_t(M) = u_t(M)` was ALREADY
  `hasDerivAt_dualPotential_temp` in ReducedPotential, and the general fixed-response derivative
  `hasDerivAt_obsMean_temp` in LossSurface — grep before naming): `lossChart_eq_obsMean` (`obsMean_eq_tempPath … L₀`),
  **`hasDerivAt_lossChart_temp`** (`∂_t h(t,M) = −Var(H)` from `hasDerivAt_lossChart_line … 1 0` reparametrised by
  `s = t − t₀`: state the line derivative at the point `(fun t ↦ t − t₀) t₀` (prove by `simp only [sub_self]; exact h`)
  and call `HasDerivAt.comp (h := fun t ↦ t − t₀) t₀ h0 hh` with the inner function NAMED — otherwise higher-order
  unification of `?h t₀ = t₀ − t₀` picks `HSub.hSub t₀`; close with `zero_dotProduct, neg_one_mul, mul_one`),
  `hasDerivAt_obsMean_base_temp`, `lossChart_temp_deriv_neg` (strict concavity of `t ↦ I_t(M)` from `natVarH_pos`).
- LANDING-CHAIN GOTCHA: a `sed -i 's/^import X$/…\nimport Y/' Laplace.lean && grep -n Y Laplace.lean && lake build …`
  chain fails SILENTLY when the sed does not match (grep exits 1 and the `&&` chain stops) — always verify the
  registration line explicitly (python assert) and never gate on a chain that can skip the build without output.
- `RateFunction.lean` (NOT mirrored; round-40 top pick, parts A/B): `baseCgf q := featCgf (familyMeasure t 0) R q`,
  `chernoffScore M q := q·M − Λ(q)`, `rateFun M := ⨆ q, ENNReal.ofReal (chernoffScore M q)` (the `q = 0` score is `0`,
  so the nonnegative clipping loses nothing); `dotJ_neg_left`, `mul_sum_zero_sub_mul` (`dotJ_smul_left` and `dirLoss_smul`
  ALREADY EXIST — `dirLoss_smul` is a FUNCTION equality, `rw` works pointwise anyway), `baseCgf_eq` (`Λ(q) = A_t(−q/t) − A_t 0`
  from `featCgf_familyMeasure … 0 q`), **`chernoffScore_le_famKL`** (score at `q` = dual objective at `b = −q/t`, `≤` by
  `dual_objective_le_at_mean` (takes `hπ` NONNEG) — `field_simp` needs `t ≠ 0` as a HYPOTHESIS in context),
  `chernoffScore_neg_smul` (equality at `q = −t a`), **`rateFun_meanMap`** (`𝓘(m_t a) = ofReal (KL(P_a‖P_0))`; `le_antisymm
  (iSup_le …) (le_iSup_of_le …)`), `rateFun_meanMap_zero`, `rateFun_meanMap_toReal`, `convexOn_dualPotential_add`,
  `baseCgf_smul_le` (`Λ(λw) ≤ λc` when `w·R ≤ c` a.e.; `withDensity_absolutelyContinuous` transports the a.e. bound,
  `integral_mono_ae`, `Real.log_le_iff_le_exp (integral_exp_pos hint)`), **`rateFun_eq_top_of_not_mem`**
  (`geometric_hahn_banach_point_closed` gives `f M < u < f y` on `K`; coordinates by `pi_eq_sum_univ'`; the direction is
  `−v`; `ENNReal.eq_top_of_forall_nnreal_le` with `λ = (r+1)/(w·M + u)`; `omit ht`), `lowerSemicontinuous_rateFun`
  (`lowerSemicontinuous_iSup` + `ENNReal.continuous_ofReal.comp`; `unfold chernoffScore dotJ; fun_prop`).
- `CramerTheorem.lean` (NOT mirrored; round-40 bundle C/D): `chernoffScore_combo` (affine in `M` via `isLinearMap_dotJ`),
  **`rateFun_combo_le`** (convexity of `𝓘` along segments with finite endpoints; `ENNReal.ofReal_le_iff_le_toReal` turns
  `le_iSup` into a real bound), `radial_mem_interior` (`Convex.combo_closure_interior_mem_interior`; `omit [Fintype ι]`),
  `rateFun_radial_le` (towards `m_t(0)` where `𝓘 = 0`, `mul_le_of_le_one_left`), **`cramer_upper`** (closed `F`, `c < 𝓘` on
  `F` ⇒ eventually `≤ e^{−n(c−ε)}`; witnesses via `lt_iSup_iff` + `ENNReal.ofReal_lt_ofReal_iff'`),
  `cramer_lower_interior` (tilted mean via `range_meanMap_slice` + `open_lower_bound … 0 b` with `δ = c − KL`),
  **`cramer_lower`** (open `G`, `𝓘(M) < c` for some `M ∈ G` ⇒ eventually `≥ e^{−nc}`; `M ∈ K` since `𝓘 < ⊤`; the radial
  point enters `G` by continuity: `(hcont.tendsto 0 |>.eventually (hG.mem_nhds …)).and (eventually_lt_nhds zero_lt_one)`
  then `Filter.Eventually.exists_gt`).
- `ExposedFace.lean` (NOT mirrored; round-40 bundle E): `genRate ν R M` (generic Chernoff rate; `rateFun` is `genRate
  (familyMeasure t 0)` DEFINITIONALLY), `faceMeasure ν F := (ν F)⁻¹ • ν.restrict F` (`isProbabilityMeasure_faceMeasure`
  needs `ν F ≠ 0`; from `0 < ν.real F` via `(ENNReal.toReal_pos_iff.1 hp).1.ne'`), `integral_faceMeasure`
  (`integral_smul_measure`, `ENNReal.toReal_inv`), `integrable_exp_dirLoss`, `setIntegral_exp_dirLoss_pos` (constant lower
  bound + `setIntegral_const` + `integral_mono` on the restricted measure), `featCgf_faceMeasure`
  (`Λ_F(q) = log ∫_F e^{q·R} − log p_F`), `log_add_featCgf_face_le`, **`genRate_le_face`** (everywhere;
  `ENNReal.ofReal_add_le`, `add_le_add le_rfl …`), **`tendsto_featCgf_ray`** (`Λ(q+λu) − λβ → log p_F + Λ_F(q)`: split the
  integral with `integral_add_compl`, rewrite on the face with `setIntegral_congr_fun` and `simp only [dirLoss_add,
  dirLoss_smul, hx', ← Real.exp_add]` (beta-redexes block `rw`), DCT `tendsto_integral_filter_of_dominated_convergence` on
  `ν.restrict Fᶜ` with `ae_restrict_of_ae`, `ae_restrict_mem hF.compl`, `Real.tendsto_exp_atBot.comp
  (tendsto_id.atTop_mul_const_of_neg hlt)`; log-limit via a named `h1 : Tendsto (fun lam ↦ A + G lam) atTop (𝓝 A)`),
  `featCgf_zero'`, **`face_le_genRate`** (on `{u·M = β}`: `le_of_tendsto'` — NOT `ge_of_tendsto'` — of the scores along
  `q + λu`; `ENNReal.add_iSup`, case split `le_or_gt` with `ENNReal.ofReal_add` / `ENNReal.ofReal_of_nonpos`),
  **`genRate_face_eq`**, **`rateFun_face_eq`** (`𝓘(M) = −log p_F + 𝓘_F(M)` for the response family; a.e. bound transported
  by `withDensity_absolutelyContinuous`).
- `NullFace.lean` (NOT mirrored; round-41 F1/F2): `integrable_of_bdd_prob`, `dotJ_integral_eq` (`q·E R = E(q·R)`),
  **`genRate_mean_eq_zero`** (Jensen: `convexOn_exp.map_integral_le` needs `ContinuousOn`, `isClosed_univ`, a.e. membership,
  and integrability of `f` and `exp ∘ f`; close `ofReal … ≤ 0` by `nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero`; `zero_le`
  takes NO explicit argument), `dotJ_condMean` (`u·M_F = β`), **`genRate_condMean`** (`𝓘(M_F) = −log p_F`),
  **`genRate_eq_top_of_null_face`** (`Z_λ = E e^{λ(u·R − β)} → 0` by DCT with bound `1`; `∀ᵐ x, u·R ≠ β` from `ae_iff` on the
  null face; score at `λu` is `−log Z_λ`; `ENNReal.eq_top_of_forall_nnreal_le` with `λ` from
  `(hZlim.eventually (gt_mem_nhds (exp_pos (−r)))).exists`).
- `FaceTotalVariation.lean` (NOT mirrored; round-41 G): `familyMeasure_real_eq_priorExp` (mass = expectation of the
  indicator via `integral_indicator_one`; `omit [Nonempty X] ht`), `ray_numerator_subset_face` (`∫ 1_B e^{−t L_{sv}} π =
  e^{−tsα} ∫_B tiltedPrior` for `B ⊆ F`; `integral_indicator`, `setIntegral_congr_fun`), **`familyMeasure_real_inter_face`**
  (`P_s(A ∩ F) = P_s(F) · Q_F(A)`; call the numerator lemma at `0` and `rw [zero_smul] at h` before using it),
  **`tendsto_familyMeasure_real_face`** (`P_s(F) → 1` from `tendsto_priorExp_ray_face` with `φ = 1_F`; its section omits
  `hπpos`; give `setIntegral_congr_fun` its target `(g := …)` or the congruence proof fixes the wrong function),
  `faceLaw_real_eq` (`faceMeasure` unfolded: `Measure.smul_apply, Measure.restrict_apply, ENNReal.toReal_mul,
  ENNReal.toReal_inv`), **`abs_familyMeasure_real_sub_faceLaw_le`** (`|P_s(A) − Q_F(A)| ≤ 1 − P_s(F)`;
  `measureReal_inter_add_sdiff (s := A) hF`, `measureReal_compl`, `nlinarith` with the two product facts as hypotheses),
  **`tendsto_familyMeasure_real_ray`** (squeeze).
- `BoundaryBarrier.lean` (NOT mirrored; round-41 F3/F4): `exists_supporting_direction` (Hahn–Banach
  `geometric_hahn_banach_open_point` on `interior K`; the functional is `dotJ u` with `u j = f (Pi.single j 1)` via
  `pi_eq_sum_univ'`; closure step by `Convex.closure_interior_eq_closure_of_nonempty_interior` and
  `closure_minimal (t := {z | f z ≤ f M})`), `essRange_subset_closedBall` (`mem_essRange_iff` + `nonempty_of_measure_ne_zero`
  + `le_of_forall_pos_le_add`; sup-norm via `pi_norm_le_iff_of_nonneg`), **`isCompact_momentBody`**
  (`set_option linter.unusedFintypeInType false in`; `isCompact_closedBall … |>.of_isClosed_subset`), **`momentBody_subset_halfspace`**
  (`convexHull_min` + `convex_halfSpace_le (isLinearMap_dotJ u)`; a point of the essential range outside the half-space
  has a ball of positive prior mass inside the open complement, contradicting the a.e. bound via `measure_mono_null` and
  `ae_iff`), `familyMeasure_eq_zero_iff` (`withDensity_apply_eq_zero'` + `measurable_familyDensity`; `omit [Nonempty X] ht`),
  `familyMeasure_real_pos_of_ne_zero`, **`rateFun_eq_top_of_mem_frontier`** (needs `hnd` for a nonempty interior and
  `[Nonempty ι]`; supporting direction + `genRate_eq_top_of_null_face` with the a.e. bound transported by
  `withDensity_absolutelyContinuous _ _`), `rateFun_eq_top_of_not_mem_interior`, **`exists_frontier_rateFun_lt_top`**
  (conditional mean `M_F` has finite rate by `genRate_condMean`, lies in `K` by the contrapositive of
  `rateFun_eq_top_of_not_mem`, and is not interior because `M_F + c•u ∈ K` would violate the half-space bound;
  `c = ε/(2(‖u‖+1))`, `dotJ u u > 0` via `Finset.sum_pos'` + `Function.ne_iff`), **`rateFun_frontier_eq_top_iff`**
  (boundary infinity ⇔ all supporting faces `μ`-null), `frontier_momentBody_nonempty` (`isClopen_iff_frontier_eq_empty`,
  `isClopen_iff`, `noncompact_univ (ι → ℝ)`), `isCompact_rateFun_sublevel` (`LowerSemicontinuous.isClosed_preimage`),
  `rateFun_sublevel_subset_interior`, **`exists_pos_forall_infDist_lt_imp_lt_rateFun`** (statement `∃ δ : ℝ, 0 < δ ∧ …`
  — `∃ δ > 0` mis-elaborated; `Metric.infDist_pos_iff_notMem_closure`, `disjoint_interior_frontier`,
  `IsCompact.exists_isMinOn` + `isMinOn_iff`, empty sublevel handled separately), **`tendsto_rateFun_nhds_top`**
  (`ENNReal.tendsto_nhds_top_iff_nnreal`; general filter), `…_of_null` wrapper. `ℝ≥0` needs `open scoped NNReal`.
- `EntropyProjection.lean` (NOT mirrored; round-41 item 2/6, entropy-projection completion): `entropyProj ν R M :=
  ⨅ ρ [IsProbabilityMeasure ρ] (E_ρ R = M), klDiv ρ ν` (Mathlib `InformationTheory.klDiv`, `open InformationTheory`);
  `integrable_exp_of_bdd`; **`integral_sub_log_le_toReal_klDiv`** (Donsker–Varadhan for bounded `f`: `KL(ρ‖ν_f) ≥ 0` via
  `integral_llr_add_sub_measure_univ_nonneg` + `integral_llr_tilted_right` + `absolutelyContinuous_tilted`;
  `toReal_klDiv_of_measure_eq` needs `ρ univ = ν univ` by `simp [measure_univ]`), `ofReal_integral_sub_log_le_klDiv`
  (`klDiv_ne_top_iff`, `ENNReal.ofReal_le_iff_le_toReal`), `llr_tilted_ae` (`llr_tilted_left` with `ν ≪ ν := fun _ h ↦ h`,
  transported by `(tilted_absolutelyContinuous ν f).ae_le`; `llr_self`), `integral_llr_tilted_eq`, `integral_sub_log_nonneg`,
  **`klDiv_tilted_eq`** (`KL(ν_f‖ν) = E_{ν_f} f − log E_ν e^f`), **`genRate_le_klDiv`** (`unfold genRate featCgf` then
  `dotJ_integral_eq`), `genRate_le_entropyProj`, `entropyProj_le_klDiv` (`iInf_le_of_le ρ (iInf_le_of_le inferInstance …)`;
  omit `hR [Fintype ι] [IsProbabilityMeasure ν]`), `faceMeasure_eq_withDensity` (`withDensity_indicator`, `withDensity_const`),
  **`klDiv_faceMeasure`** (`Measure.rnDeriv_withDensity`, `Measure.ae_smul_measure (ae_restrict_mem hF)` — namespace
  `Measure`!, `change Real.log (…rnDeriv…).toReal = _` before `rw [hx, Set.indicator_of_mem, ENNReal.toReal_inv, Real.log_inv]`),
  `entropyProj_condMean`; family section: `integral_exp_neg_mul_dirLoss_familyMeasure_zero` (from `featCgf_familyMeasure … 0
  ((-t) • a)` + `dirLoss_smul` + `Real.exp_log`), **`familyMeasure_eq_tilted`** (`P_{t,a} = Q.tilted (fun x ↦ -t * dirLoss R a x)`
  from `familyMeasure_eq_withDensity_tilt … a a t` (TiltLowerBound) after `div_self, one_smul, sub_self`; `unfold Measure.tilted;
  congr 1; funext x; beta_reduce; congr 1`), **`klDiv_familyMeasure_zero`** (`= ofReal (famKL a 0)`; rewrite into the tilt, apply
  `klDiv_tilted_eq`, rewrite back, `famKL_eq … (t := t)`, `simp only [dotJ, Pi.zero_apply, zero_sub, neg_mul,
  Finset.sum_neg_distrib]; ring`), **`entropyProj_meanMap`**, **`klDiv_eq_add_of_mean`** (Pythagoras; three cases `¬ρ ≪ Q`,
  `¬Integrable llr`, finite — the non-integrable case transfers through `llr_tilted_right` with `Pi.sub_apply, Pi.add_apply`;
  finite case `← ENNReal.ofReal_add (Gibbs) (integral_sub_log_nonneg)`), **`klDiv_eq_rateFun_iff`** (`nth_rewrite 2 [← zero_add …]`
  + `ENNReal.add_left_inj` + `klDiv_eq_zero_iff`).
- `ThermalTransport.lean` (NOT mirrored; round-42 item 1): `tiltExp_one_eq_integral_tilted` (seabed `tiltExp ν 1 g f (-1) s` =
  `∫ g ∂ν.tilted (s * f)`; `integral_tilted`, `div_mul_eq_mul_div`, `integral_div`, per-point goals need `beta_reduce` before
  `rw`), **`hasDerivAt_integral_tilted`** (master transport `d/ds E_{ν_s} g = Cov_{ν_s}(g,f)` from `TiltData.hasDerivAt_tiltExp`
  with weight `fun _ ↦ 1`, `R := f`, `t := -1`; `TiltData` anonymous constructor `⟨measurable_const, integrable_const _,
  fun _ ↦ zero_le_one, by simp, hfm, hfb⟩`), `hasDerivAt_integral_exp_mul` (`d/ds ∫ e^{sf} = ∫ f e^{sf}`, from
  `hasDerivAt_tiltNum` with `f := 1`), `integral_tilted_eq_div`, **`hasDerivAt_klDiv_tilted_toReal`** (`d/ds KL(ν_s‖ν) = s Var_s f`;
  representation via `klDiv_tilted_eq` + `toReal_ofReal (integral_sub_log_nonneg)`, then `((hasDerivAt_id s₀).mul h1).sub
  (h2.log hZpos.ne')`, `congr_of_eventuallyEq`, `congr_deriv`, `simp only [id_eq]; ring`); family: `familyMeasure_natCoord`
  (`unfold familyMeasure; rw [priorZ_natCoord]; congr 1; funext; rw [affLoss_zero_jointStat_natCoord]; simp`), `natCoord_zero_eq`,
  **`klDiv_familyMeasure_prior`** (`= ofReal (−relEntropy (natCoord t a))`, via the joint family's `klDiv_familyMeasure_zero` with
  `(L₀ := 0) (R := jointStat) (t := 1)`; `unfold relEntropy famKL; rw [neg_neg]`), `familyMeasure_zero_temp`,
  `familyMeasure_eq_tilted_prior` (from the joint `familyMeasure_eq_tilted`), **`hasDerivAt_relEntropy_temp_fixed`**
  (`hasDerivAt_relEntropy_path` along `t ↦ natCoord t a` (derivative `natCoord 1 a` via `natCoord_eq_smul`); `unfold natForm;
  rw [priorCov_natCoord]`, `dirLoss_jointStat_natCoord`, `priorCov_const_mul_left`), `relEntropy_natCoord_eq_neg_integral` (FTC
  with `continuous_priorCov_temp`), **`klDiv_familyMeasure_prior_eq_integral`**, **`hasDerivAt_klDiv_familyMeasure_prior_toReal`**,
  `rateFun_toReal_eq` (interior `M` at any `t > 0` via `range_meanMap_slice`), **`hasDerivAt_rateFun_temp_toReal`**
  (`hasDerivAt_dualPotential_temp … hnd ht₀ hM` + `hasDerivAt_affLogZ_temp … 0 t₀`; `congr_of_eventuallyEq` on `Ioi_mem_nhds`),
  `hasDerivAt_entropyProj_temp_toReal`.
- `GroundState.lean` (NOT mirrored; round-42 item 4, positive-mass case): the thermal path `t ↦ P_{t,a}` is the ray of the
  one-feature family on `Unit` (`affLoss_unit`, `dirLoss_unit`, **`familyMeasure_unit`**: `familyMeasure 0 (fun _ ↦ H_a) 1
  (s • 1) = familyMeasure L₀ R s a` — `unfold familyMeasure; rw [affLoss_unit]; unfold priorZ; simp only [one_mul, add_zero]`;
  `face_unit`, `tiltedPrior_zero_one`), `priorExp_affLoss_self` (`⟨H_a⟩ = ⟨L₀⟩ + a·m`; rewrite ONLY the observable with a
  `rfl`-typed `have e : priorExp … (affLoss a) t = priorExp … (fun x ↦ L₀ x + dirLoss R a x) t` — `conv_lhs => rw` hits the loss
  slot too), **`mixKL_eq_neg_relEntropy`** (`mixKL 0 H_a t 1 0 = −𝒮(t,a)` via `TiltData.mixKL_eq` + `relEntropy_natCoord`),
  **`tendsto_energy_temp`** (`⟨H_a⟩_{t,a} → α` from `tendsto_thresholdFun` on the `Unit` family with direction `−1`; identification
  `thresholdFun … = −⟨H_a⟩` via `priorExp_smul_add`, `priorExp_const_mul`), `tendsto_priorExp_temp_face` (direct instance of
  `tendsto_priorExp_face` with `V := affLoss a`), `unit_face_pos`, `unit_face_ae`, **`tendsto_familyMeasure_real_ground`**
  (`P_{t,a}(G) → 1`), **`abs_familyMeasure_real_sub_priorFace_le`**, **`tendsto_familyMeasure_real_temp_face`** (TV convergence to
  `π̄(·|G)`; instantiate `FaceTotalVariation` with `(L₀ := 0) (R := fun _ : Unit ↦ H_a) (t := 1)` and `simp only [familyMeasure_unit,
  face_unit, hz] at h` — `simp` rewrites under the `fun s ↦` binder where `rw` cannot), **`tendsto_klDiv_prior_temp_face`**
  (`KL(P_{t,a}‖π̄) → log ∫π − log ∫_G π`, from `tendsto_mixKL_face`), `familyMeasure_zero_real_eq` (`π̄(A) = ∫_A π/∫π`; after
  `unfold priorExp priorZ` the factors are `0 * …` and `exp 0 * π`: `zero_mul`, `one_mul`; indicators by `by_cases` +
  `Set.indicator_of_mem/notMem`, `Set.indicator_apply` needs `Decidable`), **`tendsto_klDiv_prior_temp_face'`**
  (`KL(P_{t,a}‖π̄) → KL(π̄_G‖π̄)`), **`affLogZ_tangent_temp`** (Bregman tangent bound `A_t − (s − t)⟨H⟩_t ≤ A_s` from the
  joint family's `famKL_nonneg`/`famKL_eq` at `natCoord t a`, `natCoord s a`; `Fintype.sum_option`, `meanMap_natCoord_*`),
  **`tendsto_klDiv_prior_temp_null`** (null ground state ⇒ `KL → +∞`: `monotoneOn_of_deriv_nonneg (convex_Ici 0)` from
  `hasDerivAt_klDiv_familyMeasure_prior_toReal` (`interior_Ici`), unboundedness by contradiction: `simp only [not_exists,
  not_and, not_le] at hcon`, `ge_of_tendsto` along `⟨H⟩_t → α` (`tendsto_energy_temp`) gives `log∫π − C ≤ A_s + sα` for all
  `s`, while `Real.tendsto_log_nhdsNE_zero.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_shifted_priorZ, pos⟩)` sends
  `log(e^{sα} Z_s) → −∞`; `Measure.restrict_eq_zero`, `integral_zero_measure`; finish with `tendsto_atTop_atTop`).
- `RelativeInterior.lean` (NOT mirrored; round-42 item 2, geometry): **`mem_intrinsicInterior_iff_exists_ball`** (`x ∈ relint K ↔
  x ∈ K ∧ ∃ δ > 0, ∀ v ∈ (affineSpan ℝ K).direction, ‖v‖ < δ → x + v ∈ K`; `mem_intrinsicInterior` + `mem_nhds_subtype` +
  `AffineSubspace.vadd_mem_iff_mem_direction`/`vsub_mem_direction` with `simpa [vadd_eq_add, add_comm]`/`[vsub_eq_sub]`; write
  `interior_subset hy` with the preimage type, not `↑y ∈ K`), `displacements K x : Set (direction)` (convex:
  `push_cast` then `calc … (a + b) • x … := by module`), `mem_interior_displacements`
  (`set_option linter.unusedFintypeInType false in` — the metric on the direction needs `Fintype J`),
  **`mem_intrinsicInterior_iff_forall_supporting`** (`K` convex: `x ∈ relint K ↔ x ∈ K ∧ ∀ e, (∀ y ∈ K, e·y ≤ e·x) → ∀ y ∈ K,
  e·y = e·x`; converse via `geometric_hahn_banach_open_point` on the direction subspace, `intrinsicInterior_nonempty` for a
  relint point, `LinearMap.exists_extend (f : V →ₗ[ℝ] ℝ)` to extend the functional and `pi_eq_sum_univ'` to read it as `dotJ e`).
- `RelativeMomentBody.lean` (NOT mirrored; round-42 item 2): `dirSpan μ π S := (affineSpan ℝ (momentBody μ π S)).direction`
  (an `abbrev`; a `local notation` for the projection fails quotPrecheck), `one_le_dotJ_self` (`Finset.exists_max_image` +
  `pi_norm_le_iff_of_nonneg`), `exists_far_point_rel` (test point `x + (−3δ/4) • e`, `e ∈ 𝕍`), **`cap_lemma_rel`** (copy of
  `cap_lemma` over the compact `E = 𝕍 ∩ sphere` (`IsCompact.inter_left`, `Submodule.closed_of_finiteDimensional`); `E = ∅`
  handled first; omits `hπpos`), **`coercive_bound_rel`** (nonzero `θ ∈ 𝕍`, `e := ‖θ‖⁻¹ • θ`), **`exists_min_variational_rel`**
  (minimise on the subtype `𝕍`: `Continuous.exists_forall_le' hf 0 hcoer` with `tendsto_norm_cocompact_atTop`; write the
  function with binder `fun θ : dirSpan μ π S ↦ …`; `simp only [hfdef] at h1 ⊢` before `linarith` so both sides are
  beta-reduced), **`meanMap_eq_of_min_rel`** (first-order condition along `e ∈ 𝕍` gives `e·(x − m) = 0`; apply to
  `e := x − m ∈ 𝕍` and `Finset.sum_eq_zero_iff_of_nonneg`), **`range_meanMap_eq_intrinsicInterior_momentBody`** (no `hnd`; `⊆`
  via the supporting characterisation: `e·S ≤ e·m` a.e. with equal `P_θ`-expectation ⇒ `e·S = e·m` a.e.
  (`integral_eq_zero_iff_of_nonneg_ae`, transfer by `familyMeasure_eq_zero_iff`) ⇒ `K` in the hyperplane by
  `momentBody_subset_halfspace` twice).
- `ConditioningChainRule.lean` (NOT mirrored; round-42 item 3 prerequisites): `faceMeasure_rnDeriv` (density `1_F/ν(F)`),
  `ae_mem_faceMeasure` (`Measure.ae_smul_measure (ae_restrict_mem hF)`), `absolutelyContinuous_faceMeasure` (`ρ ≪ ν`, `ρ Fᶜ = 0`
  ⇒ `ρ ≪ ν_F`; `Measure.restrict_apply'`, `measure_le_inter_add_sdiff`, `ENNReal.inv_eq_zero`), **`llr_faceMeasure_ae`**
  (`Measure.rnDeriv_mul_rnDeriv hρ (κ := ν)`, `Measure.rnDeriv_pos`, `Measure.rnDeriv_lt_top`; `unfold llr` then `Real.log_mul`,
  `Real.log_inv`, `simp only [measureReal_def]; ring`), **`klDiv_eq_klDiv_faceMeasure_add`** (`KL(ρ‖ν) = KL(ρ‖ν_F) + ofReal(−log ν(F))`;
  integrable and non-integrable cases; `ν.real F ≤ 1` by `ENNReal.toReal_le_of_le_ofReal zero_le_one` + `prob_le_one`),
  **`compl_eq_zero_of_mean_face`** (mean on the face hyperplane ⇒ carried by the face; `integral_eq_zero_iff_of_nonneg_ae`,
  `measure_eq_zero_iff_ae_notMem`, `Set.notMem_compl_iff`), `essRange_faceMeasure_subset`/`momentBody_faceMeasure_subset`
  (`set_option linter.unusedFintypeInType false in`), `momentBody_faceMeasure_subset_hyperplane`,
  **`finrank_dirSpan_faceMeasure_lt`** (`W := LinearMap.ker (IsLinearMap.mk' (dotJ e) _)`; `direction_affineSpan`, `vectorSpan_def`,
  `Submodule.span_le`, `Set.mem_vsub`; `Submodule.finrank_lt_finrank_of_lt`), `familyMeasure_one_zero` (`withDensity_one`),
  `genRate_eq_rateFun` (`unfold rateFun chernoffScore baseCgf; rw [familyMeasure_one_zero]; rfl`).
- `EntropyCompletion.lean` (NOT mirrored; round-42 item 3, THE COMPLETION PRINCIPLE): **`exists_unique_entropy_minimiser`**
  (`genRate ν S M ≠ ⊤ → ∃! ρ, IsProbabilityMeasure ρ ∧ E_ρ S = M ∧ klDiv ρ ν = genRate ν S M`; `suffices` over `n` +
  `induction n using Nat.strong_induction_on with | _ n ih`, quantifying over all probability laws with
  `finrank (dirSpan ν 1 S) = n`; family hypotheses for `(ν, π := 1, L₀ := 0, t := 1)` are `measurable_const`, `integrable_const _`,
  `fun _ ↦ one_pos`, `by simp`, `h0`; interior case via `range_meanMap_eq_intrinsicInterior_momentBody`, `klDiv_familyMeasure_zero`
  rewritten with `familyMeasure_one_zero`, `rateFun_meanMap`, `klDiv_eq_rateFun_iff`; boundary case via
  `mem_intrinsicInterior_iff_forall_supporting` + `push Not`, `genRate_eq_top_of_null_face`, `genRate_face_eq`,
  `finrank_dirSpan_faceMeasure_lt`, the chain rule, `ENNReal.add_right_inj ENNReal.ofReal_ne_top`), **`entropyProj_eq_genRate`**
  (`𝓔 = 𝓘` for every `M`, infinite values included). The induction is carried by **`exists_pythagorean_minimiser`**
  (`∃ ρ_M, prob ∧ mean ∧ attains ∧ ∀ ρ prob with mean M, KL(ρ‖ν) = KL(ρ‖ρ_M) + 𝓘(M)`; boundary case: a law with the
  face mean is carried by `F`, `klDiv_eq_klDiv_faceMeasure_add`, the IH's Pythagoras, `add_assoc`/`add_comm`; a law not
  `≪ ν` has both sides `⊤` via `klDiv_of_not_ac`); uniqueness then follows from `klDiv_eq_zero_iff` — when deriving it,
  `rw [zero_add, h]` rewrites BOTH copies of `genRate`; use `rw [zero_add]; exact h`.
- `DataResponseMap.lean` (NOT mirrored; round-43 item 1): **`responseProjection hS ν M`** (instance-free: `open Classical in`,
  `if h : IsProbabilityMeasure ν ∧ genRate ν S M ≠ ⊤ then (haveI := h.1; Classical.choose (exists_pythagorean_minimiser …))
  else 0` — a def taking `[IsProbabilityMeasure ν]` cannot be applied to `faceMeasure ν F` in a statement;
  `responseProjection_spec` via `dif_pos ⟨inferInstance, hfin⟩` + `Classical.choose_spec`), `klDiv_eq_top_of_genRate_eq_top`
  (`top_le_iff.1 (h ▸ genRate_le_klDiv …)`), **`information_decomposition`** (`KL(D‖ν) = 𝓘(E_D S) + KL(D‖Π(E_D S))`, one `rw` of
  the spec's Pythagoras + `add_comm`), `essRange_eq_of_equiv`, `mean_mem_momentBody_general` (`change priorExp … = _` before
  `rw [← integral_familyMeasure …, familyMeasure_one_zero]`, which then closes the goal — no trailing `rfl`),
  **`mean_mem_intrinsicInterior_of_equiv`** (supporting characterisation + `compl_eq_zero_of_mean_face` + `ae_iff` transfer by
  `ν ≪ D`), **`mean_tilted_mem_intrinsicInterior`**, **`hasDerivAt_dataResponsePath`** (= `hasDerivAt_integral_tilted`; omit
  `[Fintype J] [Nonempty J]`), **`klDiv_tilted_eq_integral`** (FTC with `hasDerivAt_klDiv_tilted_toReal`; continuity of the integrand
  from the tilt derivatives; `ν.tilted (0 * f) = ν` via `tilted_const'`, `measure_univ`, `inv_one`, `one_smul`; `klDiv_self`),
  **`information_decomposition_path`** (`ENNReal.toReal_add`, finiteness of the residual from `ENNReal.add_ne_top`),
  **`responseProjection_faceMeasure`** (Π_ν(M) = Π_{ν_F}(M) on a positive supporting face; chain rule + uniqueness; no `_` in
  the `have` type of the cancellation step). Several statements need `set_option linter.unusedFintypeInType false in`.
- `IntrinsicChart.lean` (NOT mirrored; round-43 item 2, chart part): `eq_zero_of_invisible_of_mem_dirSpan` (an a.s.-constant
  contrast in `𝕍` is zero: `K` in the hyperplane by `momentBody_subset_halfspace` twice, `𝕍 ≤ ker (dotJ e)` via
  `direction_affineSpan`/`vectorSpan_def`/`Submodule.span_le`, then `dotJ e e = 0`), **`meanMap_injOn_dirSpan`**
  (`meanMap_eq_iff_invisible … one_pos a b` with the zero base loss), **`intrinsicChart : dirSpan μ π S ≃ intrinsicInterior ℝ K`**
  (`Equiv.ofBijective`; surjectivity from `exists_min_variational_rel` + `meanMap_eq_of_min_rel`, which give a parameter IN `𝕍`),
  `intrinsicChart_apply` (rfl), `meanMap_intrinsicChart_symm` (`congrArg Subtype.val (Equiv.apply_symm_apply …)` — a reverse `rw`
  with the apply lemma leaves the chart's hypotheses as metavariable goals).
- `ConditioningCertificate.lean` (NOT mirrored; round-43 item 3): face algebra `faceMeasure_univ`, `faceMeasure_apply`,
  `faceMeasure_real_apply` (`ν_A(B) = ν(B ∩ A)/ν(A)`), **`faceMeasure_faceMeasure`** (`(ν_A)_B = ν_{A ∩ B}`; `Measure.restrict_smul`,
  `Measure.restrict_restrict hB`, `smul_smul`, then the ENNReal scalar identity via `ENNReal.mul_inv (Or.inl …) (Or.inl …)`,
  `inv_inv`, `mul_right_comm`, `ENNReal.mul_inv_cancel`), `faceMeasure_real_le_one`, `prob_real_le_one`.
  **`inductive ExposedChain ν S M : Set X → ℕ → Prop`** (`root : univ 0`; `step` adds `A ∩ {dirLoss S e = β}` under
  `∀ᵐ x ∂ν_A, e·S ≤ β`, a point of `K_{ν_A}` off the hyperplane, positive `ν_A`-mass of the face, and `e·M = β`). The inductive
  references `[Fintype J]` (via `dotJ`/`momentBody`), so it cannot be omitted in the section; name constructor implicits with
  `| @step A n hA e β hβ hproper hpos hM ih` or the goal's `A` and the case's `A✝` diverge; `ExposedChain.castSet` (a lemma named
  `cast` collides with the root `cast` under dot notation). `ExposedChain.measurableSet`, `ExposedChain.pos`
  (`div_pos_iff_of_pos_right`), **`ExposedChain.finrank_add_le`** (`n + dim 𝕍_{ν_A} ≤ dim 𝕍_ν`; the second point for the strict
  drop is the conditional mean of the new face, `mean_mem_momentBody_general` + `momentBody_faceMeasure_subset(_hyperplane)`;
  finish by `omega`), **`ExposedChain.genRate_eq`** (`𝓘_ν(M) = ofReal(−log ν(A)) + 𝓘_{ν_A}(M)`; `genRate_face_eq` at `ν_A`,
  `← ENNReal.ofReal_add`, `Real.log_div`, `ring`), **`ExposedChain.prefix`** (prefix a chain of `ν_F` by the first face: root via
  `step root` and `faceMeasure_univ`, step via `faceMeasure_faceMeasure` rewriting the hypotheses and `Set.inter_assoc`),
  **`exists_exposedChain`** (same strong induction as the completion, now producing the chain with `M ∈ relint K_{ν_A}`),
  **`responseProjection_eq_of_exposedChain`** (`∃ θ ∈ 𝕍_{ν_A}, Π_ν(M) = familyMeasure ν_A 1 0 S 1 θ`; the tilt attains the rate by
  the chain rule + `ExposedChain.genRate_eq`, then the spec's Pythagoras and `klDiv_eq_zero_iff`).
- `MixtureBridge.lean` (NOT mirrored; round-43 item 4, minus the TV part): `mixture_absolutelyContinuous`,
  `isProbabilityMeasure_mixture` (`ℝ≥0`-scalars; normalise `•` with `simp only [ENNReal.smul_def, smul_eq_mul, mul_one]`
  then `← ENNReal.coe_add`), **`klDiv_mixture_le`** (convexity of `klDiv` in the first argument: `klDiv_eq_lintegral_klFun_of_ac`
  on all three laws, `Measure.rnDeriv_add'` + `rnDeriv_smul_left'` for the density of the mixture, pointwise
  `convexOn_klFun.2` with the points pinned by `(ENNReal.toReal_nonneg (a := …))`, `lintegral_mono_ae`, then
  `lintegral_add_left`/`lintegral_const_mul` with `Measurable.ennreal_ofReal` of `by fun_prop`), `mean_mixture`
  (`integral_add_measure` with `Integrable` facts typed for the `ℝ≥0`-smul measure, `integral_smul_nnreal_measure`,
  `NNReal.smul_def`), **`genRate_segment_le`** (`𝓘((1−s) m₀ + s M) ≤ ofReal s * 𝓘(M)`; via `entropyProj_eq_genRate`,
  `entropyProj_le_klDiv` at the mixture `a • ν + b • Π(M)`, `klDiv_mixture_le`, `klDiv_self`; infinite-rate case by
  `ENNReal.mul_top`), **`genRate_segment_mono`** (reparametrise `M_s` as the point `s/t` of the segment to `M_t`; `gcongr`
  with `ENNReal.ofReal_le_one`), **`segment_mem_intrinsicInterior`** (mixture law equivalent to `ν` for `s < 1`;
  `mean_mem_intrinsicInterior_of_equiv`), **`tendsto_genRate_segment`** (`tendsto_order`; lower half by
  `lowerSemicontinuous_rateFun` transported along the continuous path, upper half by `ENNReal.Tendsto.mul_const` and
  `Ioo_mem_nhdsLT (zero_lt_one' ℝ)`; write real numerals `(1 : ℝ)` in the `have` type or `1 - 1` elaborates in `ℕ`).
  OPEN: TV convergence of the representatives (needs Pinsker, not in Mathlib).
- `EndpointConvergence.lean` (NOT mirrored; round-44 items 1–2): **`klDiv_tilted_right_eq`** (`KL(ρ‖ν_f) = KL(ρ‖ν) − E_ρ f +
  log E_ν e^f` for `ρ ≪ ν` of finite information and bounded `f`; Mathlib `integral_llr_tilted_right`,
  `integrable_llr_tilted_right`, `klDiv_of_ac_of_integrable`; the `ν.real univ − ρ.real univ` terms are `1 − 1`, close with
  `congr 1; ring`), **`genRate_eq_zero_iff`** (`𝓘_ν(M) = 0 ↔ M = E_ν S`; via `responseProjection_spec` + `klDiv_eq_zero_iff`),
  **`responseProjection_eq_tilted`** (a relative-interior response is `ν.tilted (−dirLoss S θ)`: the root of `ExposedChain`
  in `responseProjection_eq_of_exposedChain`, `faceMeasure_univ`, `familyMeasure_eq_tilted`, `familyMeasure_one_zero`),
  **`klDiv_responseProjection_segment_le`** (`KL(Π(M)‖Π(M_s)) ≤ 𝓘(M) − 𝓘(M_s)` for `0 < s < 1`: three means of `f`
  (`dotJ_integral_eq`), the rate of the path point from `klDiv_tilted_eq`, Gibbs at `ν` from
  `integral_sub_log_le_toReal_klDiv ν ν` + `klDiv_self`, linearity of `dotJ` along the segment, then `nlinarith`/`linarith`;
  ENNReal wrap-up with `nth_rewrite 2 [hI]` (the `← ofReal_toReal` copy inside the KL formula must NOT be rewritten) and
  `← ENNReal.ofReal_sub _ hb`), **`tendsto_klDiv_responseProjection_segment`** (squeeze with `ENNReal.Tendsto.sub`,
  `tsub_self`, `Ioo_mem_nhdsLT`). GOTCHA: `obtain ⟨Q, hQ⟩ : ∃ Q, Q = responseProjection …` loses the probability instance;
  re-derive it with `have hQP' : IsProbabilityMeasure Q := by rw [hQ]; exact hQP`. `haveI` for a Prop is linted: use `have`.
  OPEN: TV convergence (Pinsker), the C¹ Legendre chart on 𝕍, the differential data response, the cubic tensor.
- `ResponseSusceptibility.lean` (NOT mirrored; round-44 item 3, first half): `mem_of_hasDerivAt_subtype` (velocity of a path in a
  closed submodule stays in it: `hasDerivAt_iff_tendsto_slope`, `IsClosed.mem_of_tendsto`, `slope_def_module`),
  `hasDerivAt_subtype_of_hasDerivAt` (`HasDerivAt` version of the subtype helper, `Submodule.coe_smul`),
  **`hasFDerivAt_famKL_zero`** (envelope identity `D_θ 𝓘(m(θ))[w] = −⟨θ, Dm(θ) w⟩`: `famKL_eq`, `hasFDerivAt_affLogZ`
  (DualPotential, `dotCLM`), `HasFDerivAt.fun_sum` + `HasFDerivAt.mul` + `hasFDerivAt_apply` + `hasFDerivAt_pi'`; close with
  `congr_fderiv`, `ext w`, simp with ROOT `add_apply/smul_apply/neg_apply` (the `ContinuousLinearMap.` forms are deprecated),
  `FunLike.coe_sum`, two `mul_comm` sum identities, `ring`), `hasStrictFDerivAt_chartV_equiv`,
  `eventually_mem_intrinsicInterior_chartV` (`eventually_right_inverse`; binder MUST be written `∀ᶠ v : dirSpan μ π S in …`
  or `v` elaborates in `J → ℝ`), `rateFun_eq_famKL_chartVInv`, **`hasFDerivAt_rateFun_chart`/`hasFDerivAt_genRate_chart`**
  (`D_M 𝓘(M)[u] = −⟨θ(M), u⟩` on `𝕍`; chain rule through `chartVInv`, `congr_of_eventuallyEq` + `congr_fderiv`; rewrites
  with `chartDeriv_apply`/`coe_chartDerivEquiv` need their explicit arguments or leave `case hπm` goals),
  `meanMap_zero_eq_mean`, `pathV` (`M(s) − m₀ ∈ 𝕍`), `dataCov` (`variable (S) in` so `S` is explicit: `dataCov S ν h s`),
  `hasDerivAt_pathV(_val)`, `dataCov_mem_dirSpan`, `dataTheta` (= `chartVInv (pathV s)`), `chartV_dataTheta`,
  **`hasDerivAt_dataTheta`** (`θ'(s) = (Dm|_𝕍)⁻¹ Cov_{D_s}(S,h)`), **`hasDerivAt_genRate_dataPath`**
  (`d/ds 𝓘(M(s)) = −⟨θ(M(s)), Cov_{D_s}(S,h)⟩`). `HasFDerivAt.comp_hasDerivAt` needs the base point passed explicitly
  (`hl.comp_hasDerivAt s₀ hf`). `include` does not apply to defs: a def includes only the variables its body uses.
  NEXT: basepoint second derivative `d²/ds² 𝓘(M(s))|₀ = ⟨b, C₀⁻¹ b⟩ ≤ Var h`, residual variance.
- `BasepointCurvature.lean` (NOT mirrored; round-44 item 3, basepoint theorem): `lawCov` (`Cov_ν(φ,ψ) = Eφψ − EφEψ`),
  `lawCov_comm`, `lawCov_neg_left`, `lawCov_self_nonneg` (write `Var φ = ∫ (φ − Eφ)²`; the `integral_add` witness must be a
  lambda-typed `have hA : Integrable (fun x ↦ …)`), `lawCov_sub_self`, `one_integral_pos ν` (the featureless `hπpos`, PINNED to
  `ν` — a bare `(by simp)` inside a `def` leaves `Measure.real ?m univ`), `tilted_zero_mul` (`tilted_const'`), `priorCov_one_zero`,
  `dirLoss_neg` (S implicit: call `dirLoss_neg (S := S) _ x`), `lawCov_dirLoss_left`, `dataCov_zero`, `pathV_zero`, `dataTheta_zero`,
  `hasDerivAt_genRate_dataPath_zero` (zero velocity at the featureless law), `basepointVelocity` (`θ'(0)`),
  `chartDeriv_basepointVelocity`, `regressor` (`⟨−θ'(0), S⟩`), **`lawCov_dirLoss_regressor`** (regression identity
  `Cov(⟨e,S⟩, g) = Cov(⟨e,S⟩, h)` ∀ e; `rw [dotJ_chartDeriv, Submodule.coe_zero, priorCov_one_zero, dataCov_zero]`),
  `hasDerivAt_dataCov` (existence form, three `hasDerivAt_integral_tilted`), **`hasDerivAt_rateVel_zero`** (product rule with
  `HasDerivAt.mul` ascribed to the lambda type, `dataTheta_zero` kills the unknown second factor),
  **`hasDerivAt_deriv_genRate_dataPath_zero`** (`deriv` of the rate along the path has derivative `Var_ν(regressor)` at `0`),
  **`residual_variance`** (`Var h − Var g = Var(h − g)`), **`regressor_variance_le`**. GOTCHA: `rw [lawCov_comm]` bare rewrites
  the FIRST `lawCov`, which is usually not the one meant — give the arguments.
- `QuadraticInformationBound.lean` (NOT mirrored; round-44 item 4): `hasDerivAt_log_integral_exp` (`HasDerivAt.log` of
  `hasDerivAt_integral_exp_mul`, `integral_tilted_eq_div`), **`log_integral_exp_le_of_var_le`** (two `antitoneOn_of_deriv_nonpos`
  integrations on `Icc 0 1` with `interior_Icc`; state the `HasDerivAt` of `f − K·s` with the LAMBDA type in a `have` — the
  `.sub (…const_mul K)` form is Pi-subtraction and `rw [….deriv]` fails; the final `simp only` at `s = 1`, `s = 0` needs
  `zero_pow`, `one_pow`, `Real.log_one`, `integral_const`), `lawCov_self_le_integral_sq` (`Var g ≤ E(g − c)²`, product form
  `(g − c) * (g − c)` because `Bdd` has no `congr`), **`lawCov_dirLoss_le_of_bdd`** (`Var_ρ⟨q,S⟩ ≤ B²‖q‖²` for every `ρ ≪ ν`
  when `‖S − m₀‖ ≤ B` a.s.; `Finset.sum_mul_sq_le_sq_mul_sq univ q w`, `hρ.ae_le hB`, `integral_mono_ae`),
  **`featCgf_le_quadratic`** (`Λ(q) ≤ ⟨q,m₀⟩ + B²‖q‖²/2`; the tilted probability instance must be supplied by
  `isProbabilityMeasure_tilted` inside the lambda), **`genRate_ge_quadratic`** (`ofReal (‖M − m₀‖²/(2B²)) ≤ 𝓘(M)` for EVERY `M`,
  via `le_iSup_of_le ((B²)⁻¹ • v)`, `dotJ_smul_left`, `dotJ_comm`, `field_simp; ring`). `‖·‖` throughout is `dotJ v v`.
- `CubicResponse.lean` (NOT mirrored; round-44 item 6): `thirdCentral ρ g k f = E[(g−Eg)(k−Ek)(f−Ef)]`, `thirdCentral_comm₁₂/₂₃`,
  `thirdCentral_eq` (moment expansion: name the three means with `obtain ⟨a, ha⟩`, one pointwise `ring` identity `e`,
  `simp_rw [e]`, then a chain of lambda-typed `Integrable` facts `i1 … i6` and `integral_add`/`integral_sub` outermost-first,
  `integral_const_mul` ×6, `integral_const`, `ring`), **`hasDerivAt_lawCov_tilted`** (`d/ds Cov_{ν_{sf}}(g,k) = thirdCentral (ν_{sf}) g k f`
  from three `hasDerivAt_integral_tilted` (g·k, g, k) and `unfold lawCov; congr_deriv; rw [thirdCentral_eq]; ring`),
  `hasDerivAt_var_tilted` (`κ₃`), `hasDerivAt_lawCov_dataPath` (`omit [Fintype J]`), `hasDerivAt_lawCov_dirLoss_dataPath`.
  Round-44 items 1–6 ALL DONE (TV/Pinsker and the local inverse-stability constant remain open).
- `InvisibleInformation.lean` (NOT mirrored): `invisible_dataPath_eq` (`KL(D_s‖Π(M s)).toReal = KL(D_s‖ν).toReal − 𝓘(M s).toReal`,
  by `linarith` from `information_decomposition_path` and `klDiv_tilted_eq_integral`), **`hasDerivAt_invisible_dataPath`**
  (`s Var_{D_s} h + ⟨θ(M(s)), Cov_{D_s}(S,h)⟩`), `hasDerivAt_invisible_dataPath_zero`,
  **`hasDerivAt_deriv_invisible_dataPath_zero`** (curvature at the featureless law = `Var_ν(h − regressor)`; product rule with
  `hasDerivAt_var_tilted`, the negation of `hasDerivAt_rateVel_zero` via `congr_of_eventuallyEq (… by simp)` — `simpa` cannot
  see through `-fun s ↦ -…`). At second order `Var h = Var(regressor) + Var(h − regressor)` is the visible/invisible split.
- `ResponsePathDifferential.lean` (NOT mirrored; round-45 item 3; consult `gpt_responses/research_round45_v1.md`, ranking:
  1 atlas package, 2 dual Fisher metric + inverse stability `κ_r = e^{−2Br} λ₀`, 3 response differential for arbitrary paths and
  observables, 4 integrated Fisher budget `𝓘(M) = ∫₀¹ (1−s)⟨Δ, C_{θ_s}⁻¹Δ⟩ ds` and `KL(D‖ν) = ∫₀¹ (1−s) 𝓕_data(s) ds`, 5 Pinsker via
  binary KL + `klDiv_map_le`, 6 strict-convexity gap identity). Contents: `toV μ π S M` (a `dite` on `M − m₀ ∈ 𝕍`; explicit
  `(μ π S)` via `variable (μ π S) in` because `include` does not reach defs; `toV_apply`, `deriv_mem_dirSpan_of_path`,
  `hasDerivAt_toV_path` take only the membership/path hypotheses), `responseTheta M = chartVInv (toV M)`, `chartV_responseTheta`,
  `meanMap_responseTheta` (`m(θ(M)) = M` on the relint), **`hasDerivAt_responseTheta_path`** (`θ' = (Dm|_𝕍)⁻¹ M'` for ANY
  differentiable response path with `M s − m₀ ∈ 𝕍` and `M s₀ ∈ relint`), **`hasDerivAt_rateFun_path`/`hasDerivAt_genRate_path`**
  (`−⟨θ(M s₀), M'⟩`), `obsV φ v = E_{P_{θ(v)}} φ`, **`hasFDerivAt_obsV`** (`hasFDerivAt_obsMap` from DataQuotient composed with
  `chartVInv`), `obsV_deriv_apply` (`= −priorCov_{θ}(φ, ⟨(Dm|_𝕍)⁻¹u, S⟩)`), **`responseProjection_eq_familyMeasure_responseTheta`**
  (via `klDiv_eq_rateFun_iff` and `responseProjection_spec`, no exposed chain needed), `integral_responseProjection_eq`,
  `priorCov_eq_lawCov_familyMeasure`, **`hasDerivAt_integral_responseProjection_path`** (`d/ds E_{Π(M s)} φ = −Cov_{Π(M s₀)}(φ, ⟨θ', S⟩)`,
  relint only eventually).
- `ChartContinuity.lean` (NOT mirrored): `norm_chartDeriv_sub_le` (restriction does not increase the operator norm;
  `ContinuousLinearMap.opNorm_le_bound`, `le_opNorm`), **`continuous_chartDeriv`** (from `continuous_meanMapDeriv`, `Metric.continuous_iff`),
  `coe_chartDerivEquiv_symm` (`= Ring.inverse (chartDeriv θ)`: `ContinuousLinearMap.ringInverse_eq_inverse` then `inverse_equiv`),
  **`continuous_chartDerivEquiv_symm`** (`NormedRing.inverse_continuousAt` at the unit `(ContinuousLinearEquiv.unitsEquiv ℝ V).symm e`).
- `StraightPathAtlas.lean` (NOT mirrored; round-45 items 1 + 4 visible half): `atlasPath S ν M s = (1−s)•m₀ + s•M` (explicit `S ν M`),
  `atlasPath_zero/one/eq/sub`, `hasDerivAt_atlasPath`, `responseProjection_absolutelyContinuous`, `atlas_mem_intrinsicInterior`
  (needs `import Laplace.Multi.EndpointConvergence` for `segment_mem_intrinsicInterior`), `mem_momentBody_of_genRate_ne_top`
  (closedness + limit along `𝓝[<] 1`; the `Tendsto` `have` must be typed or `mono_left nhdsWithin_le_nhds` leaves metavariables),
  `sub_mem_dirSpan_of_genRate_ne_top`, `atlasPath_sub_mem_dirSpan`, `atlasTheta hS ν M s` (explicit `M`), `atlasVel hS ν hfin s`
  (`(Dm|_𝕍)⁻¹ Δ`), `atlasCurv` (`−⟨atlasVel, Δ⟩`), `atlasTheta_zero`, **`hasDerivAt_atlasTheta`**, **`hasDerivAt_atlasRate`**
  (`−⟨θ_s, Δ⟩`), **`hasDerivAt_atlasVelocity`** (derivative = `atlasCurv`), **`atlasCurv_eq_priorCov`** (variance of `⟨atlasVel, S⟩`
  under `P_{θ_s}`), `atlasCurv_nonneg`, `continuousAt_atlasCurv` (`ContinuousAt.clm_apply`), `genRate_atlasPath_zero`,
  `neg_dotJ_atlasTheta_eq_integral`, **`genRate_atlasPath_eq_integral`** (`𝓘(M_r) = ∫₀ʳ (r−s) atlasCurv s`; FTC twice with `(f := …)`
  pinned, IBP `intervalIntegral.integral_deriv_mul_eq_sub` with `u s = s − r`; `intervalIntegral.integral_neg` in a `rw` list hits the
  FIRST negated integral — derive the sign flip as a separate `have` with `← integral_neg` + `integral_congr`),
  **`tendsto_integral_atlasCurv`** (`→ 𝓘(M).toReal` as `r ↑ 1`, via `ENNReal.tendsto_toReal` and `tendsto_genRate_segment`),
  **`atlas_decomposition_mixture`** (`KL(D_b‖ν) = 𝓘(M_b) + KL(D_b‖Π(M_b))` for the mixtures of a data law with response `M`).
- `PinskerEvent.lean` (NOT mirrored; round-45 item 5): **`log_integral_exp_le_of_ae_abs_sub_le`** (Hoeffding's lemma in cumulant form,
  `log E e^g ≤ E g + r²/2` when `|g − c| ≤ r` a.e.; from `log_integral_exp_le_of_var_le` + `lawCov_self_le_integral_sq`;
  `abs_mul_abs_self`, `mul_self_le_mul_self`), **`pinsker_event`** (`ofReal (2 (μ A − η A)²) ≤ klDiv μ η`: Donsker–Varadhan
  `ofReal_integral_sub_log_le_klDiv η μ hg` at `g = A.indicator (fun _ ↦ 4 d)`, `integral_indicator_const`,
  `norm_indicator_le_norm_self`; `Set.indicator_apply` needs `Decidable` — use `by_cases` + `indicator_of_mem/notMem`; feed
  `nlinarith` the substitution `μ.real A = d + η.real A`), **`sq_real_responseProjection_segment_le`**
  (`2 (Π(M) A − Π(M_s) A)² ≤ (𝓘(M) − 𝓘(M_s)).toReal`, via `ENNReal.ofReal_le_iff_le_toReal (ENNReal.sub_ne_top hfin)`),
  **`tendsto_real_responseProjection_segment`** (every event probability converges at the endpoint; squeeze, `Tendsto.sqrt`,
  `Real.sqrt_sq_eq_abs`, `(tendsto_zero_iff_abs_tendsto_zero _).2`).
- `DualFisherMetric.lean` (NOT mirrored; round-45 item 2, Hessian half): `fderiv_rateFun_chart_eventually` (`∇𝓘(m₀+v) = −θ(v)` as a
  functional, eventually near every image point: `hasFDerivAt_rateFun_chart` at `chartVInv v` + `chartV_chartVInv`),
  **`hasFDerivAt_fderiv_rateFun_chart`** (`D_v[∇𝓘(m₀+v)(w)] = −(dotCLM w) ∘ subtypeL ∘ (chartDerivEquiv θ₀).symm`; the
  `congr_of_eventuallyEq` goal needs `Function.comp_apply, Pi.neg_apply` in the simp set then one `rw [dotJ_comm]`),
  **`hessian_rateFun_chart_eq`** (= `priorCov_{θ₀}(⟨u',S⟩, ⟨w',S⟩)` with `u' = (Dm|_𝕍)⁻¹u`: rewrite `w` as `chartDeriv θ₀ w'`
  with `conv_lhs`, then `dotJ_chartDeriv` — do NOT `dotJ_comm` first, the pattern wants `chartDeriv` in the second slot),
  `hessian_rateFun_chart_symm`, **`hessian_rateFun_chart_pos`** (positive definite on `𝕍`: `ContinuousLinearEquiv.symm_apply_eq`
  + `map_zero` for `u' ≠ 0`, `priorCov_dirLoss_self_pos`). OPEN (item 2 second half): inverse-stability constant
  `κ_r = e^{−2Br} λ₀` (density bound of `P_θ` w.r.t. `ν`, variance comparison, coercivity of `C_0` on the unit sphere of `𝕍`, segment
  integration of `⟨θ−η, m(η)−m(θ)⟩`).
- `DataFisherBudget.lean` (NOT mirrored; round-45 item 4, data-side half): **`klFun_eq_integral`** (`x log x − x + 1 =
  ∫₀¹ (1−s)(x−1)²/(1−s+sx) ds` for `x ≥ 0`; `x = 0` by `intervalIntegral.integral_congr_ae'` off the null endpoint
  (`Real.volume_singleton`), `x > 0` by the FTC with antiderivative `−(x−1)s + x log(1+(x−1)s)`; for the derivative identity
  name the denominator `d` with `obtain ⟨d, hdd⟩`, `field_simp`, then `rw [hdd]; ring` — `field_simp` cannot match `1+(x−1)s`
  against its own normal form `1 + xs − s`; `add_sub_cancel : a + (b − a) = b` at the end), `dataFisher ν D s`
  (`∫⁻ ofReal ((f−1)²/(1−s+sf)) dν`, `f = (D.rnDeriv ν).toReal`), `measurable_dataFisher_integrand`,
  **`klDiv_eq_lintegral_dataFisher`** (`KL(D‖ν) = ∫⁻ s in Ioc 0 1, ofReal (1−s) * dataFisher s` in `ℝ≥0∞`, for `D ≪ ν`;
  `klDiv_eq_lintegral_klFun_of_ac`, `ofReal_integral_eq_lintegral_ofReal` with `Measure.integrableOn_of_bounded` (bound
  `(y−1)²`; pass a NAMED `Measurable` fact, the inline `(by fun_prop : …).aestronglyMeasurable` misparses), `Filter.EventuallyLE`
  must be unfolded before `ae_restrict_iff'`, Tonelli `lintegral_lintegral_swap (f := fun x s ↦ …)`, `setLIntegral_congr_fun`,
  `lintegral_const_mul` with a named measurable integrand, `ENNReal.ofReal_mul`).
- `PinskerObservable.lean` (NOT mirrored; round-45 item 5, observable form): **`pinsker_observable`** (`(E_μF − E_ηF)²/(2L²) ≤ KL(μ‖η)`
  for `|F − c| ≤ L`: Donsker–Varadhan at `g = t F`, `t = d/L²`, Hoeffding with centre `t c` and radius `|t| L`; the final
  algebra via named identities `e1/e2/e3` and `linarith`), **`sq_integral_responseProjection_segment_le`**,
  **`tendsto_integral_responseProjection_segment`** (every bounded posterior expectation converges at the endpoint of the bridge).
  Round-45 item 5 fully closed.
- `ProjectionPythagoras.lean` (NOT mirrored; round-46 item 2; consult `gpt_responses/research_round46_v1.md` — verdict: the atlas
  is defensible; ranking 1 complete information budget (visible ∫(1−s)κ as an improper integral + data budget + invisible =
  difference, and the local `KL(D_s‖Π) ~ s²/2 Var(h−g)`), 2 reference-independent Pythagoras + metric packaging, 3 inverse
  stability, 4 parameter escape at the boundary (`‖θ(M_s)‖ → ∞`, accumulation directions in the normal cone), 5 boundary
  strict-convexity gap identity, 6 C^∞ + `D_θ C_θ[w] = −T_θ(·,·,w)` (sign!)): `toReal_klDiv_tilted_right` (real form with the
  Donsker–Varadhan nonnegativity from `integral_sub_log_le_toReal_klDiv`), **`klDiv_familyMeasure_eq_add_projection`**
  (`KL(D‖P_η) = KL(D‖Π(E_D S)) + KL(Π(E_D S)‖P_η)` for finite-information `D`, every `η`, boundary responses included; equality in
  `ℝ≥0∞` via `ENNReal.toReal_eq_toReal_iff'` on finite terms).
- `VisibleBudget.lean` (NOT mirrored; round-46 item 1, visible half): `affLogZ_one_zero_eq_featCgf` (`A(θ) = Λ(−θ)`),
  `genRate_atlasPath_toReal_eq` (rate of a path point in Chernoff form at its own coordinate; `unfold atlasTheta` then
  `conv_lhs => rw [← hm]` with `hm : m(θ(M_r)) = M_r`, `rateFun_meanMap`, `famKL_eq`, `featCgf_zero' ν`),
  **`gap_ge_atlasVelocity`** (`(1−r)(−⟨θ_r,Δ⟩) ≤ 𝓘(M) − 𝓘(M_r)` from `le_iSup` in `genRate` at `q = −θ_r`),
  `integral_one_sub_mul_atlasCurv` (`∫₀ʳ (1−s)κ = 𝓘(M_r) + (1−r)(−⟨θ_r,Δ⟩)`; the `integral_add` witness must be a lambda-typed
  `have hA` from `IntervalIntegrable.continuousOn_mul (by fun_prop)`), `continuousOn_atlasCurv_weighted`,
  `lintegral_Ioc_atlasCurv_weighted`, **`genRate_eq_lintegral_atlasCurv`** (`𝓘(M) = ∫⁻ s in Ioo 0 1, ofReal ((1−s)κ s)`: `≤` by
  `le_of_tendsto` on `tendsto_genRate_segment` with `lintegral_mono_set`; `≥` by monotone convergence `lintegral_iSup'` on
  indicators of `Ioc 0 (1 − 1/(n+2))` — write the sequence as `fun n : ℕ ↦ …` and prove indicator monotonicity/sup by `by_cases`
  with `Set.indicator_of_mem/notMem`; `exists_nat_one_div_lt`; a subset used in `Set.inter_eq_left.2` must be a NAMED `have`
  or the interval unfolds to its set-builder form), `integrableOn_atlasCurv_weighted` (`integrable_toReal_of_lintegral_ne_top`),
  **`genRate_toReal_eq_integral_atlasCurv`** (`integral_eq_lintegral_of_nonneg_ae`).
- `InformationBudget.lean` (NOT mirrored; round-46 item 1, the capstone): `measurable_dataFisher` (`Measurable.lintegral_prod_right'`
  on the swapped integrand; needs `SFinite ν`, so keep `[IsProbabilityMeasure ν]`), `measurable_dataFisher_weighted`,
  `klDiv_eq_lintegral_dataFisher_Ioo` (`setLIntegral_congr Ioo_ae_eq_Ioc`), `dataFisher_ae_ne_top` (`ae_lt_top'` +
  `ENNReal.mul_lt_top_iff` case split; `ae_restrict_mem`), **`toReal_klDiv_eq_integral_dataFisher`**
  (`integral_eq_lintegral_of_nonneg_ae`, `lintegral_congr_ae` with `ENNReal.ofReal_mul`, `ofReal_toReal`),
  `integrableOn_dataFisher_weighted`, **`klDiv_projection_eq_integral_budget`** (`KL(D‖Π(M_D)).toReal = ∫_{Ioo 0 1}
  ((1−s)𝓕_D(s).toReal − (1−s)κ(s))` for finite `KL(D‖ν)`; `integral_sub` of the two `IntegrableOn` facts). GOTCHA: `Π` is a
  reserved token — an identifier `hDΠ` breaks parsing (`hDP`).
- `TiltDensityBounds.lean` (NOT mirrored; round-46 item 3, analytic half): `abs_dotJ_le_of_sq_le` (Cauchy–Schwarz in `dotJ` form),
  `exp_neg_dirLoss_bounds` (`e^{−⟨θ,m₀⟩} e^{∓Br} ≤ e^{−⟨θ,S⟩} ≤ …` a.s. for `⟨θ,θ⟩ ≤ r²`, `‖S − m₀‖ ≤ B` a.s.),
  **`integral_familyMeasure_ge`** (`E_{P_θ} φ ≥ e^{−2Br} E_ν φ` for nonneg bounded `φ`; `integral_tilted`, pointwise density bound
  via `le_div_iff₀`; the measurability of `e^{−⟨θ,S⟩}/Z` needs `(bdd_dirLoss hS θ).1` named for `fun_prop`),
  **`lawCov_familyMeasure_ge`** (`Var_{P_θ} g ≥ e^{−2Br} Var_ν g`; variance = second moment about its own mean, then
  `lawCov_self_le_integral_sq`). NEXT: coercivity constant `λ₀` on the unit sphere of `𝕍`, segment integration, `κ_r = e^{−2Br}λ₀`.
- `InverseStability.lean` (NOT mirrored; round-46 item 3): `dotJ_segment_eq`/`dotJ_segment_le` (the `dotJ`-ball is convex),
  `dotJ_smul_smul`, `sq_dotJ_le` (Cauchy–Schwarz squared), `lawCov_dirLoss_eq_neg_dotJ_chartDeriv`, `continuous_lawCov_dirLoss`
  (quadratic form through `chartDeriv 0`; `continuous_finsetSum`), `lawCov_dirLoss_smul`, **`exists_coercive_variance`**
  (`∃ λ₀ > 0, λ₀⟨u,u⟩ ≤ Var_ν⟨u,S⟩` on `𝕍`: minimise the ratio over `Metric.sphere 0 1` with `isCompact_sphere`,
  `IsCompact.exists_isMinOn`, `isMinOn_iff`, `NormedSpace.sphere_nonempty`; the `𝕍 = 0` case separately with `dirLoss_zero`;
  scale by `‖u‖⁻¹`, `dotJ_smul_smul` + `field_simp`), **`variance_familyMeasure_ge_coercive`** (`Var_{P_θ}⟨u,S⟩ ≥ e^{−2Br}λ₀⟨u,u⟩`),
  `hasDerivAt_dotJ_meanMap_segment` (`hasDerivAt_id' (x := t)` for the affine line; `hasStrictFDerivAt_meanMap` needs `hπ : 0 ≤ π`),
  **`dotJ_sub_meanMap_ge`** (strong monotonicity `κ_r⟨θ−η,θ−η⟩ ≤ ⟨θ−η, m(η)−m(θ)⟩`; FTC with `(f := …) (f' := …)`; `IsLinearMap.map_sub`
  must be given its two arguments or it expands the wrong difference; `omit [Nonempty J] hlam0 in`),
  **`sq_dotJ_sub_le_dotJ_meanMap_sub`** (`κ_r²⟨θ−η,θ−η⟩ ≤ ⟨mθ−mη, mθ−mη⟩`, needs `0 ≤ λ₀`). Subtype coercions: write
  `((θ : J → ℝ) - (η : J → ℝ))`.
- `MixtureCompensation.lean` (NOT mirrored; round-46 item 5): `klFun_mixture_identity` (pointwise real identity
  `a klFun f₀ + b klFun f₁ = klFun g + a g klFun h₀ + b g klFun h₁` for `g = a f₀ + b f₁`, `fᵢ = hᵢ g`, `a + b = 1`; the
  `f log f` splitting by `by_cases f = 0` + `Real.log_mul`, then one `linear_combination`), `ofReal_klFun_mixture_identity`
  (the `ℝ≥0∞` form; `obtain ⟨F, hF, rfl⟩ : ∃ F, 0 ≤ F ∧ f = ofReal F` for each finite density, then both sides folded to one
  `ofReal` and `congr 1`), **`klDiv_mixture_compensation`** (`a KL(P₀‖ν) + b KL(P₁‖ν) = KL(Q‖ν) + a KL(P₀‖Q) + b KL(P₁‖Q)`,
  `Q = a P₀ + b P₁`, in `ℝ≥0∞` with NO integrability hypotheses: `klDiv_eq_lintegral_klFun_of_ac` (needs `IsFiniteMeasure ν`),
  `Measure.rnDeriv_add'`/`rnDeriv_smul_left'`, chain rule `Measure.rnDeriv_mul_rnDeriv hP₀Q`, `Q = ν.withDensity (Q.rnDeriv ν)`
  via `lintegral_withDensity_eq_lintegral_mul` rewritten by `Measure.withDensity_rnDeriv_eq`; measurability facts must be
  stated in lambda form or `← lintegral_const_mul` fails on the Pi product), **`genRate_mixture_gap`** (the gap identity
  `a 𝓘(M₀) + b 𝓘(M₁) = 𝓘(aM₀+bM₁) + [a KL(P₀‖Q) + b KL(P₁‖Q) + KL(Q‖Π(aM₀+bM₁))]`; finiteness of the mixture rate from
  the identity itself + `klDiv_eq_top_of_genRate_eq_top`; `ring` closes in `ℝ≥0∞`), **`genRate_mixture_lt`** (strict convexity
  of the rate on its finite domain: `ENNReal.lt_add_right`, `add_eq_zero`, `klDiv_eq_zero_iff`, and the means).
- `BoundaryEscape.lean` (NOT mirrored; round-46 item 4, robust part): `meanMap_atlasTheta` (`m(θ_s) = M_s` for `s < 1`),
  `continuous_atlasPath`, **`tendsto_norm_atlasTheta_atTop`** (`‖θ(M_s)‖ → ∞` along `𝓝[<] 1` when the finite-rate `M` is
  not in `intrinsicInterior ℝ (momentBody …)`): negate `Filter.tendsto_atTop` (`not_forall, Filter.not_eventually, not_le`),
  `Frequently.and_eventually (Ioo_mem_nhdsLT zero_lt_one)`, `Filter.exists_seq_forall_of_frequently` (𝓝[<] 1 is countably
  generated), Bolzano–Weierstrass `tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : 𝕍)) (r := b))` in the
  proper space `𝕍`, `continuous_meanMap … (M₀ := 0) (fun _ ↦ by simp) hS one_pos`, `tendsto_nhds_unique`, and
  `range_meanMap_eq_intrinsicInterior_momentBody`. `continuous_atlasPath ν (S := S) (M := M)` needs both implicits named.
  The directional refinement (normalised parameters accumulate in the normal cone at `M`) and the fixed-normal conditioning
  limit are NOT yet formalised.
- `NormalCone.lean` (NOT mirrored; round-46 item 4, directional refinement): `dotJ_meanMap_le_neg_featCgf`
  (`⟨θ, m(θ)⟩ ≤ −featCgf ν S (−θ)` from `famKL_nonneg` + `famKL_eq` with `(π := …) (L₀ := …)` named — the `by simp` for
  `hL₀` needs `L₀` fixed), `exp_mul_real_le_integral_exp_neg` (Laplace lower bound `e^{−rc} ν(g<c) ≤ ∫ e^{−rg}`;
  `setIntegral_const`, `setIntegral_mono_on`, `setIntegral_le_integral`), `dirLoss_sub'`, `featCgf_neg_smul_ge`
  (`−rδ − rc + log ν(⟨u,S⟩<c) ≤ featCgf ν S (−(r • w))` when `⟨w,S⟩ ≤ ⟨u,S⟩ + δ`; `Real.log_le_log`, `Real.log_mul`),
  **`dotJ_le_of_escape`** (general: `‖θ_n‖ → ∞`, `m(θ_n) → M`, `θ_n/‖θ_n‖ → u` ⟹ `⟨u,M⟩ ≤ c` whenever
  `ν(⟨u,S⟩ < c+ε) > 0 ∀ε`; `le_of_forall_pos_le_add`, `inv_mul_le_iff₀`, `le_of_tendsto_of_tendsto` with `hev.mono key`,
  `tendsto_iff_norm_sub_tendsto_zero`, `tendsto_const_nhds.div_atTop`), **`dotJ_sub_nonneg_of_escape`** (`0 ≤ ⟨u, x − M⟩` on the
  moment body; contrapositive of `momentBody_subset_halfspace` via `measureReal_eq_zero_iff` + `ae_iff`),
  **`dotJ_le_of_tendsto_normalized_atlasTheta`** (the atlas instance: escape from `tendsto_norm_atlasTheta_atTop` composed
  with `tendsto_nhdsWithin_iff`, means from `meanMap_atlasTheta`). The `.congr` goals of `integrable_exp_mul_of_bdd` are
  beta-redexes: `simp only [neg_mul]`, not `rw`. `[Nonempty J]` is needed only by the atlas theorem.
- `FixedNormalLimit.lean` (NOT mirrored; round-47 item 1A): `tilted_add_const`, **`faceMeasure_tilted`** (conditioning
  commutes with tilting: `(ν.tilted f)(·|F) = (ν(·|F)).tilted f`; both sides as `ν.withDensity` of a product via
  `withDensity_mul`, pointwise `ofReal` algebra with `ENNReal.ofReal_inv_of_pos`/`ofReal_mul` and `field_simp`; rewrite the
  tilt normaliser `∫ … ∂faceMeasure` by `integral_faceMeasure` BEFORE `faceMeasure_eq_withDensity`, or the density's integral
  is rewritten too), `real_inter_add_diff` (`measure_inter_add_sdiff`), `abs_real_sub_faceMeasure_real_le`
  (`|P(A) − P(A|F)| ≤ 1 − P(F)`), `abs_integral_sub_faceMeasure_integral_le` (`≤ 2L(1 − P(F))`;
  `norm_setIntegral_le_of_norm_le_const`, `integral_add_compl`, `measureReal_compl`, `probReal_univ`),
  `familyMeasure_one_zero_eq_tilted`, **`faceMeasure_familyMeasure_fixedNormal`** (`P_{η−ta}(·|F) = Q` for every `t`;
  `tilted_congr` under `ae_mem_faceMeasure` + `tilted_add_const`), **`real_familyMeasure_fixedNormal`**
  (`p_t = exp(th + log ν(F) + Λ_F(−η) − Λ(−η + ta))`), `tendsto_real_familyMeasure_fixedNormal_face` (`p_t → 1` from
  `tendsto_featCgf_ray`), **`tendsto_real_familyMeasure_fixedNormal`**, **`tendsto_integral_familyMeasure_fixedNormal`**
  (events and bounded observables converge to the conditioned tilt), **`klDiv_familyMeasure_fixedNormal`**
  (`KL(Q‖P_{η−ta}) = ofReal(−log p_t)` via `klDiv_eq_klDiv_faceMeasure_add` + `klDiv_self`),
  `tendsto_klDiv_familyMeasure_fixedNormal`. `isProbabilityMeasure_familyMeasure` takes `(t := 1)` named and then the
  parameter, no `ht`; name `(π := …) (L₀ := …)` or the `by simp` for `hL₀` sees a metavariable.
- `EndpointTail.lean` (NOT mirrored; round-47 item 4): `atlasPath_eq_sub` (`M_s = M − (1−s)Δ`, `module`),
  **`toReal_klDiv_responseProjection_atlas`** (exact: `KL(Π(M)‖Π(M_s)) = 𝓘(M) − 𝓘(M_s) − (1−s)(−⟨θ_s,Δ⟩)` for every
  finite-rate `M`, `0 ≤ s < 1`; the certificate `klDiv_responseProjection_segment_le` is this identity minus a nonneg term;
  `klDiv_tilted_right_eq` + `genRate_atlasPath_toReal_eq` + `gap_ge_atlasVelocity` for the `toReal_ofReal` side goal;
  `change` turns `responseTheta … (atlasPath …)` into `atlasTheta`), `intervalIntegrable_atlasCurv_weighted_tail`
  (`intervalIntegrable_iff_integrableOn_Ioc_of_le`, `integrableOn_Ioc_iff_integrableOn_Ioo`),
  **`toReal_klDiv_responseProjection_atlas_eq_integral`** (`KL(Π(M)‖Π(M_s)) = ∫_s^1 (1−u) κ(u) du`;
  `integral_add_adjacent_intervals`, `intervalIntegral.integral_congr` with `change` for the integrand identity),
  **`atlasCurv_le_of_dotJ_le`** (`κ(u) ≤ ‖Δ‖²/κ_r` on the ball: `variance_familyMeasure_ge_coercive` — which does NOT take
  `hlam0` — plus `sq_dotJ_le`, `le_of_mul_le_mul_left`), **`toReal_klDiv_responseProjection_atlas_le`**
  (`KL ≤ ‖Δ‖²(1−s)²/(2κ_r)` when `θ_u` stays in the ball on `Ico s 1`; `intervalIntegral.integral_mono_on`,
  `intervalIntegral.integral_const`, root `integral_id`). Under `open intervalIntegral`, `integral_const_mul` and
  `integral_const` are ambiguous: qualify them.
- `FisherVariational.lean` (NOT mirrored; round-47 item 5): `lawCov_self_eq_integral_sq` (`Var g = ∫ (g − Eg)²`),
  **`sq_dotJ_le_lawCov_mul_integral_sq`** (Cauchy–Schwarz `⟨v,Ṁ⟩² ≤ Var⟨v,S⟩ · E h²` for score perturbations `h` with
  `E h = 0`, `E[h⟨e,S⟩] = ⟨e,Ṁ⟩`; `integral_mul_sq_le` from AngularBound with `(f := …) (g := …)` named),
  **`lawCov_le_integral_sq_of_cov_eq`** (minimal Fisher cost: `C v = Ṁ ⟹ Var⟨v,S⟩ ≤ E h²`; `le_of_mul_le_mul_left`),
  **`centred_dirLoss_attains`** (the centred score attains it), `lawCov_dirLoss_neg_atlasVel` (`C_{θ_s}(−θ_s') = Δ`: unfold
  `atlasVel`, `← coe_chartDerivEquiv`, `ContinuousLinearEquiv.apply_symm_apply`, `dotJ_chartDeriv`),
  **`atlasCurv_le_integral_sq`** (`κ(s) ≤ E_{P_{θ_s}} h²` for every score perturbation producing `Δ`: the budget integrates
  minimal Fisher costs). The variational section needs no `[Nonempty X]`.
- `LegendreClosure.lean` (NOT mirrored; round-47 item 6): `dotJ_sub_genRate_le_featCgf` (Fenchel inequality from the
  `iSup` definition via `ENNReal.ofReal_le_iff_le_toReal`), `genRate_meanMap_neg` (`𝓘(m(−q)) = ofReal(⟨q,m(−q)⟩ − Λ(q))`
  from `genRate_eq_rateFun` + `rateFun_meanMap` + `famKL_eq`), **`featCgf_eq_dotJ_sub_genRate_meanMap`** (attainment),
  **`eq_meanMap_of_dotJ_sub_genRate_eq`** (uniqueness by `genRate_mixture_lt` at `a = b = 1/2`;
  `ENNReal.toReal_strict_mono`, one `ENNReal.coe_toReal` rewrites both coercions; the only theorem needing `[Nonempty J]`),
  **`isGreatest_featCgf`** (`Λ(q) = max {⟨q,M⟩ − 𝓘(M) : 𝓘(M) < ∞}`).
- `ObservableCurvature.lean` (NOT mirrored; round-47 item 2 via Astra round-48's frozen-residual trick):
  `hasDerivAt_mul_of_eq_zero_of_continuousAt` (product of a differentiable factor vanishing at `s₀` with a merely continuous
  one; `hasDerivAt_iff_isLittleO`, `HasDerivAt.isBigO_sub`, `IsBigO.mul_isLittleO`, `Asymptotics.isLittleO_one_iff`),
  `thirdCentral_dirLoss_left` (linearity of the third central moment in a visible contrast), `integral_familyMeasure_one_zero`,
  **`hasDerivAt_integral_familyMeasure_path`** (`d/ds E_{P_{θ_s}}φ = −Cov(φ,⟨θ_s',S⟩)` along any `C¹` path via
  `hasFDerivAt_obsMap … |>.comp_hasDerivAt`, `obsMapDeriv_apply`), **`hasDerivAt_lawCov_familyMeasure_path`**
  (`d/ds Cov_{P_{θ_s}}(f,g) = −T(f,g,⟨θ_s',S⟩)`; product/sub rules + `thirdCentral_eq` + `ring`), `hasDerivAt_atlasTheta_coe`,
  `continuousAt_atlasVel`, `hasDerivAt_integral_familyMeasure_atlas` (first order along the atlas), `lawCov_dirLoss_atlasVel`
  (`Cov_{P_s}(⟨e,S⟩,⟨v_s,S⟩) = −⟨e,Δ⟩` for all `s`), **`hasDerivAt_neg_lawCov_atlasVel`** (frozen residual: for `β₀` with
  `Cov_{s₀}(S_i,⟨β₀,S⟩) = Cov_{s₀}(S_i,φ)`, `F'(s) = ⟨β₀,Δ⟩ − Σ_i Cov_{P_s}(S_i,r₀)·v_s(i)`, each summand a vanishing
  differentiable factor times a continuous one), **`hasDerivAt_deriv_integral_familyMeasure_atlas`**
  (`F''(s₀) = T_{P_{s₀}}(r₀,⟨v_{s₀},S⟩,⟨v_{s₀},S⟩)` for `s₀ ∈ (0,1)`), **`exists_regression_coefficient`** (the covariance vector
  lies in `𝕍` by the dual-annihilator argument of `meanMapDeriv_mem_dirSpan`; `β₀ := (chartDerivEquiv θ_{s₀}).symm (−c)`).
  Gotchas: `lawCov_dirLoss_left hS ν v ψ hψ` (hS explicit); `rw [← hr₀]` on the goal BEFORE working with the named residual, or
  the final `thirdCentral_dirLoss_left` rewrite sees the lambda; `rw [← hP]` on a goal stated with `familyMeasure` before
  `linarith` against facts stated with the abbreviation `P`.
- `StatisticLift.lean` (NOT mirrored; Astra round-48 item 2 + 5A): `statisticLift ν D S := ν.withDensity (d(S_*D)/d(S_*ν) ∘ S)`
  (section needs `[IsFiniteMeasure ν] [IsFiniteMeasure D]` for the Lebesgue decomposition of the pushforwards),
  `map_withDensity_comp` (`S_*(ν.withDensity (g ∘ S)) = (S_*ν).withDensity g` by `Measure.ext` + `setLIntegral_map`),
  `map_absolutelyContinuous` (`AbsolutelyContinuous.mk`), **`map_statisticLift`** (`S_*D↑ = S_*D`),
  `isProbabilityMeasure_statisticLift`, `measure_liftDensity_eq_zero` (`D{r∘S = 0} = 0`: rewrite the withDensity form of
  `S_*D` in a separate `key` and transport, never `rw [← withDensity_rnDeriv_eq]` on a goal whose set mentions `S_*D`),
  **`absolutelyContinuous_statisticLift`** (`D ≪ D↑` via `withDensity_apply_eq_zero`), **`klDiv_statisticLift_eq_map`**
  (`KL(D↑‖ν) = KL(S_*D‖S_*ν)` unconditionally, `klFun` form + `lintegral_map`), **`klDiv_eq_klDiv_statisticLift_add_map`**
  (base split `KL(D‖ν) = KL(D‖D↑) + KL(S_*D‖S_*ν)` for finite `KL(D‖ν)`: chain rule `rnDeriv_mul_rnDeriv`, `rnDeriv_pos`,
  `ae_of_ae_map`, `hD.ae_le` to transport `ν`-a.e. facts to `D`, `toReal_klDiv` + `probReal_univ`, `integral_map`,
  `ENNReal.ofReal_add`), **`klDiv_statisticLift_le`** / **`eq_statisticLift_of_klDiv_eq`** (least-informative realisation
  and uniqueness via `ENNReal.add_left_inj` + `klDiv_eq_zero_iff`), `map_tilted_comp` (`S_*(ν.tilted (f∘S)) = (S_*ν).tilted f`;
  name the measurable density first or `exact` times out), **`klDiv_tilted_comp_eq_statisticLift_add_map`** (residual split
  for bounded tilts via `klDiv_tilted_right_eq` on both spaces and `toReal_klDiv_tilted_right` for the sign). Gotchas:
  `λ`/`μ` in identifiers (`hλμ`, `hPλ`) are reserved tokens; `klDiv_map_le (μ := D) (ν := ν) hS`;
  `Measure.isProbabilityMeasure_map hS.aemeasurable`; `zero_le` has an implicit argument.
- `ResidualInformation.lean` (NOT mirrored; Astra round-48 items 2, 5B): `klDiv_tilted_comp_eq_statisticLift_add_map'`
  (residual split for tilts by `f ∘ S` with `f` bounded only along `S`: clamp `f` to `max (−L) (min L f)`),
  **`klDiv_responseProjection_eq_statisticLift_add_map`** (`KL(D‖Π(M_D)) = KL(D‖D↑) + KL(S_*D‖S_*Π(M_D))` for finite-information
  `D` with response in the relint; `responseProjection_eq_tilted`, the identification `dirLoss S θ x = dotJ θ (statPoint S x)`
  by `simp only [dirLoss, dotJ, statPoint]` — NOT `rfl` — and the tilt function passed as `(f := …)`: leaving it to
  higher-order unification `?f (statPoint S x)` is a whnf timeout), `statisticLift_congr`, `statisticLift_statisticLift`
  (`(D↑ˢ)↑ᵀ = D↑ᵀ` for `T = h ∘ S`, `Measure.map_map`), **`klDiv_statisticLift_tower`** (`KL(D‖D↑ᵀ) = KL(D‖D↑ˢ) + KL(D↑ˢ‖D↑ᵀ)`:
  three base splits and `ENNReal.add_left_inj`; `ring` closes in `ℝ≥0∞`).
- `GeneralResidualSplit.lean` (NOT mirrored; Astra round-48 general-density extension): **`klDiv_withDensity_comp_eq_statisticLift_add_map`**
  (`KL(D‖ν.withDensity (g∘S)) = KL(D‖D↑) + KL(S_*D‖S_*P)` for any probability `P` with measurable `g : Y → ℝ≥0∞`; case split on
  finiteness of the marginal term with `klDiv_map_le`, `D ≪ P` from `withDensity_apply_eq_zero` + `D{g∘S = 0} = 0`, the two
  chain rules, finiteness of `g` a.e. from `ae_lt_top` and the probability normalisation, `Pi.sub_apply` before rewriting an a.e.
  identity into an `Integrable.sub`), `ExposedChain.exists_preimage` (chain sets are `statPoint S ⁻¹' B`; after `rw [Set.preimage_inter]`
  a bare `congr 1` closes the step), **`responseProjection_eq_withDensity_comp`** (every finite-rate projection is
  `ν.withDensity (g ∘ statPoint S)` with `g = 1_B e^{−⟨θ,·⟩}/(ν(A) Z)`: `unfold familyMeasure`, `← hZ` for the normaliser BEFORE
  `faceMeasure_eq_withDensity`, `← withDensity_mul` with a hand-written measurability of the family density; the indicator of a
  preimage is `rfl` after `rw`), and **`klDiv_responseProjection_eq_statisticLift_add_map'`** (the invisible-information split with
  NO interiority hypothesis). `Π` in identifiers (`hΠ`) is a reserved token.
- `BridgeResidual.lean` (NOT mirrored; Astra round-49 item 1, without joint convexity): `binEnt a b` (binary entropy),
  **`klDiv_le_log_of_smul_le`** (`a P ≤ Q ⟹ KL(P‖Q) ≤ log(1/a)`: `rnDeriv_le_one_of_le` + `rnDeriv_smul_left'`, the pointwise
  bound `klFun x ≤ x log c + 1 − x` for `x ≤ c`, `Measure.integrable_toReal_rnDeriv`, `Measure.integral_toReal_rnDeriv`;
  integrability witnesses must be lambda-typed `have`s), `klDiv_mixture_self_le` (`KL(aν+bD‖ν) ≤ b KL(D‖ν)`),
  **`toReal_klDiv_mixture_ge`** (`b H ≤ KL(aν+bD‖ν) + h₂(a,b)` from mixture compensation + the log bounds),
  **`statisticLift_mixture`** (the lift is affine; no absolute continuity needed; `Measure.map_add`, `Measure.map_smul`,
  `rnDeriv_add'`/`rnDeriv_smul_left'` transported by `ae_of_ae_map`, split the summed density into a Pi-sum by `rfl`
  before `withDensity_add_left`, `withDensity_smul'`, closing `rfl` for `ℝ≥0` vs `ℝ≥0∞` scalar action on measures),
  `statisticLift_self` (needs `Measurable S`: for non-measurable `S` the lift is `0`), `statisticLift_bridge`
  (`(aν + bD)↑ = aν + bD↑`), `toReal_fibreInformation_bridge_eq` (`L_s = KL(D_s‖ν) − KL(D_s↑‖ν)`),
  **`fibreInformation_bridge_le`/`_ge`** (`b L₁ − h₂ ≤ L_s ≤ b L₁ + h₂`), **`invisibleInformation_bridge_modulus`**
  (`aH − δ𝓘 ≤ R₁ − R_s ≤ aH + h₂ − δ𝓘`; supply `a·H = H − b·H` before `linarith`). Joint convexity of KL (which would give
  `L_s ≤ b L₁` without slack and convexity of `s ↦ L_s`) is NOT in Mathlib and not yet landed.
- `KLJointConvexity.lean` (NOT mirrored; general measure theory, not in Mathlib): `klFun_perspective_le` (the perspective
  inequality `q klFun H ≤ a q₀ klFun H₀ + b q₁ klFun H₁` for `q = a q₀ + b q₁`, `qH = a q₀ H₀ + b q₁ H₁`, from `convexOn_klFun`
  with weights `a q₀/q, b q₁/q`; `a + b = 1` NOT needed), `ofReal_klFun_perspective_le` (`ℝ≥0∞` form with `1 = a q₀ + b q₁`;
  `ENNReal.toReal_mul` is unconditional so `⊤ · 0` never matters), **`klDiv_mixture_mixture_le`** (JOINT CONVEXITY
  `KL(aP₀+bP₁ ‖ aQ₀+bQ₁) ≤ a KL(P₀‖Q₀) + b KL(P₁‖Q₁)` for probability laws with `Pᵢ ≪ Qᵢ`, `a, b > 0`: reference measure
  `Q = aQ₀ + bQ₁` itself, `dQ/dQ = 1 = a q₀ + b q₁`, chain rule `rnDeriv_mul_rnDeriv`, all in `lintegral` form with no
  integrability; the helper quantifying over `Qi` needs `[IsFiniteMeasure Qi]` for the Lebesgue decomposition; get
  `rnDeriv_add'` for the mixture with `rw [← hQ] at h`, not `hQ ▸`), **`fibreInformation_bridge_le'`** (`L_s ≤ b L₁`, no slack).
- `LiftConditional.lean` (NOT mirrored; round-49 item 4a + convexity of the fibre information):
  **`rnDeriv_statisticLift_eq_condLExp`** (`dD↑/dν = ν⁻[dD/dν | comap S]` a.e.: Mathlib's `rnDeriv_map` (namespace
  `MeasureTheory`, not `Measure`) + `rnDeriv_withDensity`), `bridge_remix` (`aν + bD = lν + m(cν + dD)` from the linear
  relations `a + b = c + d = l + m = 1`, `b = md` — no truncated subtraction in `ℝ≥0`), **`fibreInformation_bridge_le_remix`**
  (`L_b ≤ m L_d` for `b = m d`: convexity of `s ↦ L_s` in re-mixed form, from joint convexity + the affine lift).
- `EmpiricalProjection.lean` (NOT mirrored; round-49 item 5, **the atlas under sampling**):
  `genRate_ne_top_of_mem_intrinsicInterior`, **`toReal_klDiv_responseProjection_interior`**
  (`KL(Π(M)‖Π(M')) = 𝓘(M) − 𝓘(M') + ⟨θ(M'), M − M'⟩` for finite-rate `M` and interior `M'`; the
  endpoint identity of `EndpointTail` with a general interior target), `klDiv_responseProjection_interior_ne_top`,
  `eventually_mem_intrinsicInterior_of_tendsto` (a sequence in `K` converging to a relint point is eventually in
  relint: `tendsto_subtype_rng` into the affine span), `sampleResponse S Xs n ω = (1/n) ∑_{i<n} S(Xᵢ ω)`,
  `ae_tendsto_sampleResponse` (`strong_law_ae_real` coordinatewise, `IndepFun.comp`/`IdentDistrib.comp`,
  `ae_all_iff`, `tendsto_pi_nhds`), `ae_sampleResponse_mem_momentBody` (`ae_statPoint_mem_essRange` transported
  through `D ≪ ν` and `P.map (Xs i) = D`, then `Convex.sum_mem`), **`ae_tendsto_klDiv_responseProjection_sampleResponse`**
  (`KL(Π(M̂_n)‖Π(M_D)) → 0` a.s. when `M_D ∈ relint`: continuity of `𝓘` along `𝕍` from
  `hasFDerivAt_genRate_chart` at `chartV (responseTheta M_D) = toV M_D`, plus `ENNReal.tendsto_ofReal` on the
  interior identity). Consistency of the empirical representative in information, hence in total variation.
- `TargetPythagoras.lean` (NOT mirrored; round-50 item 2): **`klDiv_responseProjection_target_eq`**
  (`KL(D‖Π(N)) = KL(D‖D↑) + KL(S_*D‖S_*Π(M_D)) + KL(Π(M_D)‖Π(N))` for finite-information `D` and interior `N`:
  the log-density of `Π(N)` is affine in `S`, so its `D`- and `Π(M_D)`-expectations agree; two `klDiv_tilted_right_eq`
  identities + the general residual split), `klDiv_bridge_responseProjection_target_eq` (the same along the bridge
  `aν + bD`, response `a m₀ + b M_D` via `mean_mixture`).
- `PathEnergy.lean` (NOT mirrored; round-50 item 5, exponential path): `mean_familyMeasure_one_zero`,
  `log_integral_exp_neg_dirLoss`, `klDiv_familyMeasure_featureless` (`KL(P_θ‖ν) = −⟨θ,m(θ)⟩ − Λ(−θ)`, via
  `klDiv_tilted_eq`), `klDiv_featureless_familyMeasure` (`KL(ν‖P_θ) = ⟨θ,m₀⟩ + Λ(−θ)`), both nonnegativity facts
  (Fenchel at `m(θ)` / at `m₀` with `genRate_mean_eq_zero`), **`toReal_klDiv_familyMeasure_symm`**
  (`KL(P_θ‖ν) + KL(ν‖P_θ) = −⟨θ, m(θ) − m₀⟩`), **`integral_var_familyMeasure_segment`** (`∫₀¹ Var_{P_{sθ}}⟨θ,S⟩ ds =
  −⟨θ, m(θ) − m₀⟩` by FTC on `hasDerivAt_dotJ_meanMap_segment`, continuity from
  `hasDerivAt_lawCov_familyMeasure_path`), `integral_var_familyMeasure_segment_eq_symm_klDiv` (energy = symmetrised KL).
- `ObservableDefect.lean` (NOT mirrored; round-50 item 3): `statSigma S = comap (statPoint S)`, `statSigma_le`,
  `integral_mul_condExp_statSigma` (bounded `σ(S)`-measurable weights pass through `condExp`:
  `condExp_stronglyMeasurable_mul_of_bound` + `integral_condExp`), `integral_tilted_dirLoss_condExp`
  (`E_{ν_f} φ = E_{ν_f} E_ν[φ|σ(S)]` for the affine tilt, via Mathlib `integral_tilted`), `integral_mixture_of_integrable`,
  `integrable_condExp_of_ac` (`ae_bdd_abs_condExp_of_ae_bdd_abs`), **`integral_responseProjection_condExp`**
  (reconstructed laws see only `ψ = E_ν[φ|σ(S)]`), **`observableDefect_eq`**
  (`E_{D_s}φ − E_{Π(M_s)}φ = b(E_Dφ − E_Dψ) + (E_{D_s}ψ − E_{Π(M_s)}ψ)` along the bridge `aν + bD`),
  **`hasDerivAt_observableDefect`** (`Δ'_φ(s) = E_Dφ − E_νφ + Cov_{Π(M_s)}(φ,⟨v_s,S⟩)` on the atlas path).
- `NestedProjections.lean` (NOT mirrored; round-50 item 1, first half): `norm_sq_eq_three_starProjection`
  (three-way Pythagoras for nested subspaces `U ≤ V` of a real inner product space:
  `norm_sq_eq_add_norm_sq_starProjection` twice + `orthogonalProjectionOnto_starProjection_of_le`),
  `memLp_two_bdd`, `statSpan hS Q = span{1, S_j} ⊆ Lp ℝ 2 Q` (finite-dimensional, complete, hence
  `HasOrthogonalProjection`), `statSpan_le_lpMeas` (`A ⊆ L²(σ(S))` via `mem_lpMeas_iff_aestronglyMeasurable`),
  **`norm_sq_eq_statSpan_add_condExpL2`** (`‖h‖² = ‖Bh‖² + ‖Ch − Bh‖² + ‖h − Ch‖²`, `B` = projection onto
  the affine span, `C = condExpL2` = projection onto `lpMeas`; `condExpL2 … h = (lpMeas …).starProjection h` is `rfl`),
  `norm_sub_statSpan_starProjection` (best affine predictor, `starProjection_minimal`), `norm_sq_eq_integral_sq`.
- `RegressionProjection.lean` (NOT mirrored; round-50 item 1, second half): `inner_toLp_toLp` (`⟪toLp f, toLp g⟫ = ∫ fg`),
  `oneLp`, `oneLp_mem_statSpan`, `toLp_stat_mem_statSpan`, `toLp_dirLoss_eq_sum` (`Lp.ext` + `Lp.coeFn_finsetSum` +
  `Lp.coeFn_smul`), `toLp_dirLoss_mem_statSpan`, `regressionLp hS Q a φ = Eφ·1 + (⟨a,S⟩ − E⟨a,S⟩)`,
  **`starProjection_statSpan_toLp`** (`B φ = regression` when `a` solves the normal equations; via
  `eq_starProjection_of_mem_of_inner_eq_zero` and `span_le` into `(ℝ ∙ (φ − reg))ᗮ`), `norm_sq_regressionLp_sub`
  (`‖Bφ − Eφ‖² = Var⟨a,S⟩`), **`norm_sq_regressionLp_sub_eq_dotJ`** (`= ⟨a, Cov(S,φ)⟩`, the Fisher energy of the
  response velocity), `starProjection_statSpan_toLp_atlas` (on the atlas path, via `exists_regression_coefficient`).
- `AtlasEnergy.lean` (NOT mirrored; round-50 item 5, mean-path half): `tendsto_one_sub_one_div_nat`, `atlasTheta_one`,
  `atlasPath_eq_add_smul`, **`hasDerivAt_genRate_atlasPath_one`** (`𝓘(M_s)` differentiable at the interior endpoint
  `s = 1`, derivative `−⟨θ(M), Δ⟩`, from `hasFDerivAt_genRate_chart` composed with the line `s ↦ s•Δ` in `𝕍`),
  `neg_dotJ_atlasTheta_le_one` (interior slopes ≤ endpoint slope: EndpointTail identity + interior Bregman identity),
  `slope_le_neg_dotJ_atlasTheta` (chord slopes ≤ right slope: Bregman identity between two atlas points),
  **`tendsto_neg_dotJ_atlasTheta`** (`−⟨θ_s,Δ⟩ → −⟨θ(M),Δ⟩` as `s → 1⁻`, by `tendsto_order` from the two bounds and the
  derivative at 1 — no continuity of the inverse chart), **`integrableOn_atlasCurv`**
  (`integrableOn_Ioc_of_intervalIntegral_norm_bounded_right` along `r_n = 1 − 1/(n+1)`),
  **`integral_atlasCurv_eq_neg_dotJ`** (`∫₀¹ κ = −⟨θ(M), Δ⟩`, `tendsto_setIntegral_of_monotone` + uniqueness of limits),
  **`toReal_klDiv_featureless_responseProjection_eq_integral`** (`KL(ν‖Π(M)) = ∫₀¹ s κ(s) ds`),
  `integral_atlasCurv_eq_symm_klDiv`, **`integral_atlasCurv_eq_integral_var_segment`** (equal Fisher energies of the
  atlas path and the exponential path).
- `SusceptibilityDefect.lean` (NOT mirrored; round-50 item 3 at `s = 0`): `lawCov_neg_right_eq`, `lawCov_sub_left_eq`,
  `lawCov_residual_dirLoss` (the regression residual is uncorrelated with every visible contrast),
  **`hasDerivAt_observableDefect_zero`** (`Δ'_φ(0) = E_D(φ − ⟨a,S⟩) − E_ν(φ − ⟨a,S⟩)` with `a ∈ 𝕍` the regression
  coefficient of `φ` under `ν`: the initial susceptibility defect is the change of the expectation of `(I − B₀)φ`;
  from `hasDerivAt_observableDefect`, `exists_regression_coefficient` at `s₀ = 0`, `lawCov_dirLoss_neg_atlasVel`).
- `TiltQuadratic.lean` (NOT mirrored; round-50 item 4, first expansion): **`tendsto_klDiv_tilted_div_sq`**
  (`KL(ν_{tf}‖ν)/t² → Var_ν f / 2`, L'Hôpital `HasDerivAt.lhopital_zero_nhdsNE` on
  `hasDerivAt_klDiv_tilted_toReal` with `hasDerivAt_var_tilted` for continuity), `klDiv_tilted_isLittleO_sq`
  (`KL = t²/2 Var + o(t²)` via `isLittleO_iff_tendsto'`), `norm_sq_toLp_sub_mean` (`Var_ν f = ‖f − Ef‖²_{L²}`).
- `TiltRateQuadratic.lean` (NOT mirrored; round-50 item 4, second expansion): `eventually_mem_intrinsicInterior_of_tendsto_filter`,
  `tiltResponse S ν f t = E_{ν_t} S`, `tiltResponse_zero`, **`hasDerivAt_tiltResponse`** (`M_t'(0) = Cov_ν(S,f)`),
  `genRate_tiltResponse_ne_top`, `familyMeasure_neg_smul_eq_tilted` (`P_{−ta} = ν_{t⟨a,S⟩}`),
  `meanMap_neg_smul_eq_tiltResponse`, `genRate_tiltResponse_dirLoss_toReal` (`𝓘(N_t) = KL(ν_{t⟨a,S⟩}‖ν)`),
  `genRate_tiltResponse_dirLoss_add_le` (Fenchel lower bound), `abs_dotJ_le_card_mul`,
  **`isBigO_responseTheta_tiltResponse`** (`θ(M_t) = O(t)` from `hasStrictFDerivAt_chartVInv.exists_lipschitzOnWith`),
  **`tendsto_genRate_tiltResponse_div_sq`** (`𝓘(M_t)/t² → ⟨a, Cov_ν(S,f)⟩/2`, sandwich between Fenchel and the Bregman
  identity with `M_t − N_t = o(t)`; asymptotics via `IsBigO.of_bound`, `IsBigO.mul_isLittleO`, `IsLittleO.add`,
  `IsLittleO.tendsto_div_nhds_zero`).
- `ResidualQuadratic.lean` (NOT mirrored; round-50 item 4, headline): `norm_sq_sub_starProjection_statSpan`
  (`‖h − B₀h‖² = Var f − ⟨a,u⟩` for the centred score, Pythagoras in `L²` + `RegressionProjection`),
  `klDiv_tilt_eq_genRate_add` (Pythagoras for the tilt), **`tendsto_klDiv_tilt_responseProjection_div_sq`**
  (`KL(ν_t‖Π(M_t))/t² → ‖h − B₀h‖²/2`: the projection defect along a tilt is the energy of the residual score).
- `MixturePathEnergy.lean` (NOT mirrored; round-51 item 7): `klKernel r s = (r−1)²/(1+s(r−1))`, `klKernel_denom_pos`,
  `continuousOn_klKernel`, **`integral_one_sub_mul_klKernel`** (`∫₀¹ (1−s) klKernel = klFun r`, FTC with antiderivative
  `r log(1+s(r−1)) − (r−1)s`), **`integral_mul_klKernel`** (`∫₀¹ s klKernel = r − 1 − log r`), `integral_klKernel`;
  `densLaw ν r = ν.withDensity (ofReal ∘ r)`, `mixSpeed ν r s = ∫ klKernel (r x) s dν`, `klKernel_le`,
  `measurable_klKernel_uncurry`, `integral_weight_mul_mixSpeed` (Tonelli via `integral_integral_swap` on
  `(volume.restrict (Ioc 0 1)).prod ν` with `Measure.prod_restrict` + `ae_restrict_iff'` for the bound),
  `isFiniteMeasure_densLaw`, `integrable_klFun_comp`, `integrable_sub_one_sub_log`, `toReal_klDiv_densLaw`
  (`KL(rν‖ν) = ∫ klFun r`), `toReal_klDiv_densLaw_symm` (`KL(ν‖rν) = ∫ (r − 1 − log r)`, via `Measure.inv_rnDeriv`,
  `withDensity_inv_same`, `lintegral_withDensity_eq_lintegral_mul`), **`toReal_klDiv_densLaw_eq_integral_mixSpeed`**,
  **`toReal_klDiv_symm_densLaw_eq_integral_mixSpeed`**, **`integral_mixSpeed_eq_symm_klDiv`** (the bridge in the full
  simplex obeys the same weighted identities as the atlas and exponential paths; bounded positive density).
- `EntropyTaylor.lean` (NOT mirrored; round-51 item 3, engine): **`abs_klFun_one_add_sub_le`**
  (`|klFun(1+u) − u²/2| ≤ 4|u|³` for `|u| ≤ 1/2`, from `Real.abs_log_sub_add_sum_range_le` at order 2),
  **`tendsto_integral_klFun_div_sq`** (for a.e. `q_t = 1 + t g + e_t`, `|e_t| ≤ K t²` on `|t| ≤ δ`, `g` bounded:
  `(∫ klFun (q_t) dν)/t² → (∫ g²)/2`; pointwise bound `C|t|³`, integrated with `norm_integral_le_of_norm_le`, limit by
  `Metric.tendsto_nhdsWithin_nhds`).
- `EntropyTaylor` generalised: the score `g` is only a.e. bounded (`hgm : AEStronglyMeasurable g ν`, `∀ᵐ x, |g x| ≤ B`).
- `LiftDensity.lean` (NOT mirrored; round-51 item 3, densities): **`condLExp_ofReal_ae_eq`** (`ν⁻[ofReal ∘ f | m] =ᵐ
  ofReal ∘ ν[f|m]` for nonnegative integrable `f`, via `ae_eq_condLExp` and `setIntegral_condExp`),
  **`statisticLift_eq_withDensity_condExp`** (the statistic lift of `pν` is `E_ν[p|σ(S)]ν`; from
  `rnDeriv_statisticLift_eq_condLExp` + `withDensity_rnDeriv_eq`), `tiltDens ν f t = e^{tf}/Z_t`,
  `tilted_eq_withDensity_tiltDens` (rfl), **`tiltDens_sub_le`** (`|p_t − 1 − t(f − Ef)| ≤ 9B²t²` for
  `|t| ≤ 1/(4(B+1))`: `Real.abs_exp_sub_one_sub_id_le`, `Z ≥ 1/2`, explicit numerator algebra),
  `toReal_klDiv_withDensity_ofReal_ae` (`KL(rν‖ν) = ∫ klFun r` under a.e. bounds).
- `LiftQuadratic.lean` (NOT mirrored; round-51 item 3, COMPLETE): `tiltErr`, `integral_condExp_mul_self`
  (`∫ g h = ∫ g²` for `g = E[h|σ(S)]`, via `condExp_stronglyMeasurable_mul_of_bound` + `integral_condExp`),
  **`condExp_tiltDens_ae_eq`** (`E[p_t|σ(S)] = 1 + t E[h|σ(S)] + E[e_t|σ(S)]`), `tiltDens_mem_Icc`
  (`1/2 ≤ p_t ≤ 2` for `|t| ≤ 1/(8(B+1))`), **`tendsto_klDiv_statisticLift_tilt_div_sq`** (`KL(ν_t↑‖ν)/t² → (∫ g²)/2`,
  from `statisticLift_eq_withDensity_condExp`, `toReal_klDiv_withDensity_ofReal_ae`, `condExp_mono` bounds and the
  entropy-Taylor engine), **`tendsto_klDiv_tilt_statisticLift_div_sq`** (fibre: `KL(ν_t‖ν_t↑)/t² → (∫ (h−g)²)/2`),
  **`tendsto_klDiv_map_tilt_div_sq`** (marginal: `KL(S_*ν_t‖S_*Π(M_t))/t² → (∫ g² − ⟨a,u⟩)/2`). With
  `TiltQuadratic`/`TiltRateQuadratic`/`ResidualQuadratic` this is the full quadratic shadow of `KL = 𝓘 + R + L`.
- `AtlasRefinement.lean` (NOT mirrored; round-51 item 6, atlas refinement): `dirLoss_affine_coarse`
  (`⟨θ,S⟩ = ⟨Tᵀθ,S'⟩ + ⟨θ,b⟩` for `S = TS' + b`), **`familyMeasure_coarse_eq_fine`** (`P^S_θ = P^{S'}_{Tᵀθ}`, via
  `tilted_add_const`), **`responseProjection_mean_familyMeasure`** (a fine family member is its own projection:
  `𝓘(m(θ)) = KL(P_θ‖ν)` + Pythagoras + `klDiv_eq_zero_iff`), **`klDiv_responseProjection_coarse_eq`**
  (`KL(D‖Π_S(M_D)) = KL(D‖Π_{S'}(M'_D)) + KL(Π_{S'}(M'_D)‖Π_S(M_D))`, from `TargetPythagoras` with the coarse
  representative as fine target), **`genRate_fine_eq_coarse_add`** (`𝓘_{S'} = 𝓘_S + KL(Π_{S'}‖Π_S)`).
  The observational tower `L_G = L_H + KL(D^H‖D^G)` is `klDiv_statisticLift_tower` (ResidualInformation).
- `InformationDistance.lean` (NOT mirrored; the one-line map): **`toReal_klDiv_eq_integral_atlasCurv_add`**
  (`KL(D‖ν) = ∫₀¹ (1−s) κ(s) ds + L + R` for every finite-information `D`, boundary responses included),
  `atlasPath_eq_mixture_mean`, **`toReal_klDiv_bridge_eq_integral_atlasCurv_add`**
  (`KL(D_s‖ν) = ∫₀ˢ (s−u) κ(u) du + L_s + R_s` along the bridge `aν + bD`, `b < 1`).
- `BregmanGeometry.lean` (NOT mirrored; round-52 items 4 and 8): **`toReal_klDiv_responseProjection_three_point`**
  (`KL(Π(A)‖Π(C)) = KL(Π(A)‖Π(B)) + KL(Π(B)‖Π(C)) + ⟨θ(C) − θ(B), A − B⟩`),
  **`klDiv_responseProjection_three_point_eq_iff`** (generalised Pythagoras iff the mixed pairing vanishes = Fisher
  orthogonality at `B`), **`toReal_klDiv_responseProjection_sub_symm`** (`KL(Π(M)‖ν) − KL(ν‖Π(M)) = ∫₀¹ (1−2s) κ`).
- `CurvatureSplit.lean` (NOT mirrored; round-52 item 1, simultaneous curvature formulas): `bridgeDens d s = 1 + s(d−1)`,
  `klKernel_bridge`/`mixSpeed_bridge` (the bridge of a bridge rescales the kernel: `k_{d_s}(u) = s² k_d(us)`),
  `bridgeDens_bounds`, **`toReal_klDiv_densLaw_bridge`** (`KL(D_s‖ν) = ∫₀ˢ (s−w) k_d(w) dw`, by the substitution
  `intervalIntegral.integral_comp_mul_left`), `isProbabilityMeasure_densLaw_bridge`, `integral_densLaw_of_bounds`,
  **`mean_densLaw_bridge`** (the response of `D_s` is the atlas point `M_s`), `klDiv_densLaw_ne_top`,
  `measurable_mixSpeed`, `abs_mixSpeed_le`, `intervalIntegrable_sub_mul_mixSpeed`,
  **`statisticLift_densLaw_bridge`** (`(D_s)↑ = (1 + s(a−1))ν` with `a = E_ν[d|σ(S)]`: the lift of the bridge is the
  bridge of the conditional density, via `statisticLift_eq_withDensity_condExp` + `condExp_add/smul/const`),
  **`fibre_eq_integral_curvature`** (`L_s = ∫₀ˢ (s−w)(k_d(w) − k_a(w)) dw`),
  **`marginal_eq_integral_curvature`** (`R_s = ∫₀ˢ (s−w)(k_a(w) − κ(w)) dw`, `s < 1`). Together with
  `genRate_atlasPath_eq_integral`: the three terms of `KL(D_s‖ν) = 𝓘(M_s) + R_s + L_s` are the accumulated curvatures
  of three nested straight paths (full simplex `k_d`, observable simplex `k_a`, atlas `κ`), and `k_d ≥ k_a ≥ κ`.
- `ConditionalFisherLoss.lean` (NOT mirrored; round-52 item 9): `kernelSlope`, **`klKernel_sub_tangent`** (tangent-line
  identity of the convex mixture kernel: `k(y) − k(z) − k'(z)(y−z) = (y−z)²/((1+w(y−1))(1+w(z−1))²)`),
  `abs_kernelSlope_le`, **`exists_condDens`** (a `σ(S)`-measurable version of `E_ν[d|σ(S)]` with the pointwise bounds
  of `d` exists: clamp), `integral_mul_sub_condDens` (`∫ g(a)(d − a) = 0` for bounded `σ(S)`-measurable `g`),
  **`mixSpeed_sub_mixSpeed_condDens`** (`k_d(w) − k_a(w) = ∫ (d−a)²/(d_w a_w²) dν` = the conditional variance of the
  mixture score `h_w = (d−1)/d_w` under `D_w`, since `E_{D_w}[h_w|σ(S)] = (a−1)/a_w`), `mixSpeed_condDens_le`
  (`k_a ≤ k_d` pointwise), **`fibre_eq_integral_condVar`** (`L_s = ∫₀ˢ (s−w) ∫ (d−a)²/(d_w a_w²) dν dw`). NOTE (Astra):
  `k_a ≥ κ` does NOT follow pointwise (different laws); `R_s ≥ 0` only in accumulated form.
- `DensityDerivative.lean` (NOT mirrored; round-52 item 3, natural chart): `famWeight S θ = e^{−⟨θ,S⟩}`, `famZ`,
  `famDens S ν θ = e^{−⟨θ,S⟩}/Z(θ)`, `famMean S ν θ = E_{P_θ} S`; `famWeight_add`, `integrable_famWeight`, `famZ_pos`,
  `integral_famDens`, `abs_dirLoss_le_card_mul` (`|⟨η,S(x)⟩| ≤ |J| B ‖η‖`), `abs_famMean_le`, `abs_dotJ_famMean_le`,
  `integral_dirLoss_mul_famWeight` (`∫ ⟨η,S⟩ e^{−⟨θ,S⟩} = Z(θ)⟨η,m(θ)⟩`), `abs_famWeight_add_sub_le` (second order in
  the weight, `Real.abs_exp_sub_one_sub_id_le`), `abs_famZ_add_sub_le` (second order in the normaliser),
  **`abs_famDens_remainder_le`** (`|p_{θ+η} − p_θ − p_θ(⟨η,m(θ)⟩ − ⟨η,S⟩)| ≤ 10 (K‖η‖)² p_θ` for `K‖η‖ ≤ 1/4`, by
  clearing both denominators with `linear_combination`), **`integral_abs_famDens_remainder_le`** (the `L¹(ν)` bound
  `≤ 10 K² ‖η‖²`, since `∫ p_θ = 1`), **`isBigO_famDens_remainder`** (`=O[𝓝 0] ‖η‖²`).
- `ReconstructionDerivative.lean` (NOT mirrored; round-52 item 3, response coordinates):
  `familyMeasure_eq_withDensity_famDens`, `famMean_eq_meanMap`, `responseProjection_eq_withDensity_famDens`
  (`Π(M) = p_{θ(M)} ν` for interior `M`), `responseTheta_add` (`θ(M + z) = chartVInv(toV M + z)` for `z ∈ 𝕍`),
  **`isLittleO_reconstruction_density_remainder`**: for interior `M` and `z ∈ 𝕍`,
  `∫ |q_{M+z} − q_M − q_M(⟨Dθ z, M⟩ − ⟨Dθ z, S⟩)| dν = o(‖z‖)`, `Dθ = (chartDerivEquiv θ(M))⁻¹` — the Fréchet
  derivative of the reconstruction density in `L¹(ν)` is `q_M ℓ_{M,z}`. Chain rule: the natural-chart remainder is
  `O(‖η‖²)`, `η(z)` is Lipschitz in `z` (`HasStrictFDerivAt.exists_lipschitzOnWith`) and `η(z) − Dθ z = o(‖z‖)`
  (`hasFDerivAt_iff_isLittleO_nhds_zero`).
- `RetractionDerivative.lean` (NOT mirrored; round-52 item 2, the retraction theorem): `abs_score_le`
  (`|⟨v,m(θ)⟩ − ⟨v,S⟩| ≤ 2K‖v‖`), `score_sub`, `integrable_famDens_mul_score`, `integral_famDens_mul_abs_score_le`
  (`∫ p_θ |score_v| ≤ 2K‖v‖`), `dotJ_single`, `tiltResponse_familyMeasure_mem_momentBody` (a bounded tilt of a family
  member has a response in the moment body: `tilted_tilted` + `klDiv_tilted_eq` + `genRate_le_klDiv`),
  **`lawCov_eq_chartDeriv_neg`** (the velocity `u = Cov_Q(S, h)` of the tilt response is `chartDeriv θ(M) (−a)` for the
  regression coefficient `a`, via `dotJ_chartDeriv` + `priorCov_eq_lawCov_familyMeasure` + `lawCov_dirLoss_left`),
  **`isLittleO_retraction_remainder`**: for interior `M`, `Q = Π(M)`, bounded `h`, `M_t = E_{Q.tilted(th)} S`:
  `∃ a ∈ 𝕍, Cov_Q(S_j, ⟨a,S⟩) = Cov_Q(S_j, h) ∧ ∫ |q_{M_t} − q_M − t q_M(⟨a,S⟩ − ⟨a,M⟩)| dν = o(t)`;
  **`tendsto_retraction_quotient`** (`(1/t) ∫ |…| → 0`). Proof: `isLittleO_reconstruction_density_remainder` composed
  with the curve `z(t) = M_t − M ∈ 𝕍` (`comp_tendsto`, `trans_isBigO` with `HasDerivAt.isBigO_sub`), the chart
  derivative sends `u` to `−a` (`ContinuousLinearEquiv.symm_apply_apply`), and the linearisation error
  `‖L(z(t) − t u)‖ ≤ ‖L‖ · o(t)` is integrated against `q_M` with the score bound.
- `AtlasLength.lean` (NOT mirrored; round-52 item 12): `atlasLength = ∫₀¹ √κ`, **`atlasLength_sq_le_integral_atlasCurv`**
  (Cauchy–Schwarz via `integral_mul_le_Lp_mul_Lq_of_nonneg` with `Real.HolderConjugate.two_two`),
  **`atlasLength_sq_le_symm_klDiv`** (`Len² ≤ KL(Π(M)‖ν) + KL(ν‖Π(M))`).
- `ConditionalVariational.lean` (NOT mirrored; round-52 item 5): `densLaw_eq_tilted_log` (a normalised positive
  density law is `ν.tilted (log p)`), `abs_log_le_of_mem`, `isProbabilityMeasure_densLaw`, `integral_condDens`
  (`∫ a = 1`), **`statisticLift_densLaw_eq_condDens`** (`(dν)↑ = aν`), `integrable_densLaw_of_abs_le`; for bounded
  `g` with a `σ(S)`-measurable version `cg` of `E_ν[e^g|σ(S)]`: `condTilt_pos`, **`integral_condTilt`** (the
  conditional tilt `T_g = e^g/cg · aν` is normalised, by `integral_mul_condExp_statSigma`), `condTilt_eq_tilted`
  (`T_g = ν.tilted (g + log a − log cg)`), **`toReal_klDiv_condTilt`** (`KL(D‖T_g) = KL(D‖aν) − E_D g + E_D log cg`,
  via `klDiv_tilted_right_eq` twice and Donsker–Varadhan for the `toReal_ofReal` side conditions),
  **`condDV_le`** (conditional Donsker–Varadhan inequality), **`condDV_attained`** (`E_ν[e^{log d − log a}|σ(S)] = 1`
  a.e. by the pull-out property, and `E_D(log d − log a) = KL(D‖aν)` since `T_{g₀} = D`),
  **`fibre_isGreatest_condDV`** (`L = max_g {E_D g − E_D log E_ν[e^g|σ(S)]}` over bounded tests, `IsGreatest`).
- `AtlasSkewness.lean` (NOT mirrored; round-52 item 10 / round-53 rank 1): `abs_thirdCentral_self_le` (`|T(f,f,f)| ≤ 8B³`),
  `neg_thirdCentral_self_eq` (`−T(f,f,f) = ∫ (Ef − f)³`), **`atlasCurv_sub_eq`** (exact increment
  `κ(t) − κ(s) = Cov_{Q_s}(f_t,f_s) − Cov_{Q_t}(f_t,f_s)`, from `lawCov_dirLoss_atlasVel`), **`hasDerivAt_atlasCurv_of`**
  (frozen-argument covariance derivative + bilinear remainder `o(t−s)` via `IsLittleO.mul_isBigO`/`IsLittleO.sum`),
  **`hasDerivAt_atlasCurv`** (`κ'(s) = T_{Q_s}(f_s,f_s,f_s)` on `[0,1)`), the primed lemmas `atlas_mem_intrinsicInterior'`,
  `hasDerivAt_atlasTheta'`, `hasDerivAt_atlasTheta_coe'`, `continuousAt_atlasVel'`, `hasDerivAt_atlasCurv'` (on `[0,1]`
  for interior targets), `exists_bound_atlasVel`, `intervalIntegrable_deriv_atlasCurv` (via `measurable_deriv` + bound),
  **`toReal_klDiv_responseProjection_sub_symm_eq_skew`**
  (`KL(Π(M)‖ν) − KL(ν‖Π(M)) = ∫₀¹ s(1−s) E_{Q_s} ℓ_s³ ds`, `ℓ_s = E f_s − f_s`, by `integral_mul_deriv_eq_deriv_mul`).
- `ExponentialPath.lean` (NOT mirrored; round-53 rank 6, four-path package): `sq_setIntegral_sqrt_le_setIntegral_Ioo`
  (generic `(∫₀¹ √g)² ≤ ∫₀¹ g`, nonnegativity only on the interval), `expPath ν f s = ν.tilted (s f)`,
  **`integral_var_expPath_eq_symm_klDiv`** (`∫₀¹ Var_{E_s} f = KL(ν.tilted f‖ν) + KL(ν‖ν.tilted f)` for bounded `f`, by
  FTC on `E_{E_s} f` and Donsker–Varadhan at `ρ = ν` for the sign), `bdd_log_of_bounds`, `expPath_log_one`
  (`E_1 = D`), **`integral_mixSpeed_eq_integral_var_expPath`** (mixture and exponential paths `ν → D` have equal
  energy), `mixSpeed_nonneg`, `integrableOn_mixSpeed_Ioo`, `sq_integral_sqrt_mixSpeed_le_symm_klDiv` (bridge length
  ≤ √energy), `integral_mixSpeed_condDens_eq_integral_var_expPath` (the same for `ν → D↑`),
  **`symm_klDiv_statisticLift_le`** (`KL(D↑‖ν) + KL(ν‖D↑) ≤ KL(D‖ν) + KL(ν‖D)`: conditioning contracts the
  symmetrised divergence, from `k_a ≤ k_d`).
- `GlobalChart.lean` (NOT mirrored; round-53 rank 3, packaging): `relintToV`, `intrinsicChart_symm_eq_chartVInv`,
  **`relintChart : 𝕍 ≃ₜ intrinsicInterior ℝ K`** (the gauge-fixed mean map is a homeomorphism onto the relative
  interior; inverse continuity from `hasStrictFDerivAt_chartVInv`), `relintChart_apply`, `relintChart_symm_apply`
  (`= responseTheta`), `responseProjection_eq_familyMeasure_relintChart_symm`, `hasStrictFDerivAt_relintChart_coe`
  (derivative `subtypeL ∘ chartDeriv θ`), `dotJ_relintChart_deriv` (`⟨e, Dm(θ)v⟩ = −Cov_{P_θ}(⟨e,S⟩,⟨v,S⟩)`),
  **`global_response_chart`** (∃ homeomorphism with: forward = mean map, strict derivative, inverse = natural
  coordinate of `Π`, `Π(M)` has response `M` and is the unique entropy minimiser in its fibre).
  (`responseChart` was already taken by `ChartSynthesis`.)
- `AtlasVelocityDerivative.lean` (NOT mirrored; round-53 rank 2, stage 1): `hasDerivAt_of_subtype_val` (a curve into a
  submodule is differentiable once its coercion is), `thirdCentral_add₂`/`thirdCentral_smul₂` (trilinearity in the
  middle slot), `chartDeriv_coe_apply` (`(Σ_θ v)_j = −Cov_{P_θ}(S_j, ⟨v,S⟩)`), `cumulantVec`/`cumulantLin`
  (`(D_s v)_j = T_{Q_s}(S_j, ⟨v,S⟩, f_s)`), `hasDerivAt_chartDeriv_coe`, `cumulantVec_mem_dirSpan` (closedness of
  `𝕍`, via `hasDerivAt_iff_tendsto_slope`), **`cumulantOp`** (`D_s : 𝕍 →L 𝕍`), **`hasDerivAt_chartDeriv_atlas`**
  (the restricted covariance operator is differentiable along the atlas, assembled from `Module.finBasis` and
  `ContinuousLinearMap.smulRightL`), `atlasVel_eq_ringInverse`, **`hasDerivAt_atlasVel`**
  (`β_s' = −Σ_s⁻¹ D_s β_s`, by `hasFDerivAt_ringInverse` composed with the operator path).
- `AtlasHessian.lean` (NOT mirrored; round-53 rank 2, stage 2 — the mixed Hessian on the atlas diagonal):
  `measurable_famDens`, `integral_famDens_mul` (`∫ f dP_θ = ∫ p_θ f dν`), **`hasFDerivAt_famZ`**
  (`DZ(θ)[η] = −Z(θ)⟨η, m(θ)⟩`, from `hasFDerivAt_affNum`), `hasDerivAt_famZ_atlas`, `hasDerivAt_dirLoss_atlas`,
  `hasDerivAt_famWeight_atlas`, **`hasDerivAt_famDens_atlas`** (`d/ds q_s = q_s ℓ_s`, `ℓ_s = ⟨β_s, M_s⟩ − ⟨β_s,S⟩`),
  `atlasAccel` (`β_s'`), `hasDerivAt_score_atlas`, `atlasBend` (`w_s = Σ_s⁻¹ D_s β_s`), **`atlasHess`**
  (`q_s(ℓ_s² − κ(s) + ⟨w_s, S − M_s⟩)`), **`hasDerivAt_famDens_deriv_atlas`** (`d²/ds² q_s = atlasHess`),
  `atlasCurv_eq_integral_score_sq`, `cumulantVec_atlasVel_eq` (`(D_s β_s)_j = E_{Q_s}[(S_j − M_j) ℓ_s²]`),
  `lawCov_stat_atlasBend` (`Cov_{Q_s}(S_j, ⟨w_s,S⟩) = −(D_s β_s)_j`), **`integral_atlasHess`** (`∫ q'' dν = 0`),
  **`integral_mul_atlasHess`** (`∫ S_j q'' dν = 0`): all second-order bending of the atlas is response-invisible.
- `BoundaryBlowup.lean` (NOT mirrored; round-54 rank 2): `lawCov_eq_integral_centred`, **`lawCov_sq_le`**
  (Cauchy–Schwarz for covariances), **`exists_supporting_normal`** (a finite-rate response on the relative
  boundary has a supporting functional `e` with `⟨e, m₀⟩ < ⟨e, M⟩`, from `mem_intrinsicInterior_iff_forall_supporting`
  at `M` and at `m₀`), `ae_dirLoss_le_of_supporting` (`⟨e,S⟩ ≤ ⟨e,M⟩` a.e.), **`atlasCurv_ge_of_supporting`**
  (`κ(s) ≥ δ/(R(1−s))`: `E_{Q_s} Y = (1−s)δ`, `Var Y ≤ R E Y`, `Cov_{Q_s}(⟨e,S⟩, f_s) = −δ`, Cauchy–Schwarz),
  **`atlasCurv_ge_boundary`**, **`tendsto_atlasCurv_nhdsLT_one`** (`κ(s) → ∞` as `s → 1⁻`),
  **`not_intervalIntegrable_atlasCurv`** (`∫₀¹ κ = ∞`, via `intervalIntegrable_sub_inv_iff`),
  **`neg_dotJ_atlasTheta_ge_log`** (`−⟨θ_s, Δ⟩ ≥ (δ/R) log(1/(1−s))`: logarithmic escape of the natural coordinates).
- `NormalGeometry.lean` (NOT mirrored; round-54 rank 3, stage 1 — the normal geometry of the response map):
  `lawCov_const_left_eq_zero`, **`responseScore`** (`ℓ_{M,u} = ⟨R u, M − S⟩`, `R = (Dm(θ(M))|_𝕍)⁻¹ = −Σ_M⁻¹`),
  `bdd_responseScore`, `respCov` (`Cov_Q(S, f)`), `chartDeriv_symm_apply`, `respCov_mem_dirSpan` (via the
  regression coefficient), **`regProj`** (`B_M f = ℓ_{M, Cov_Q(S,f)}`), **`normalProj`** (`N_M f = f − E_Q f − B_M f`),
  `integral_stat_responseTheta`, `integral_dirLoss_responseTheta`, `integral_responseScore` (`E_Q ℓ_{M,u} = 0`),
  `lawCov_stat_responseScore` (`Cov_Q(S_j, ℓ_{M,u}) = u_j`), **`integral_responseScore_mul`** (differential
  duality: `E_Q[ℓ_{M,u} ℓ_{M,z}] = −⟨R u, z⟩ = ⟨Σ_M⁻¹ u, z⟩`), **`integral_responseScore_sq_pos`** (the
  response-space Fisher metric is positive definite on `𝕍`), `respCov_responseScore`, `regProj_responseScore`,
  `normalProj_responseScore`, **`integral_normalProj`**, **`integral_stat_mul_normalProj`** (zero mass, zero
  feature moments), `atlasScore` (`ℓ_s`), `atlasScore_eq_responseScore` (rfl), `bdd_atlasScore(_sq)`,
  **`atlasBend_eq_respCov`** (`w_s = R Cov_{Q_s}(S, ℓ_s²)`), **`atlasHess_eq_normalProj`** (the density-acceleration
  theorem `q_s''/q_s = N_{M_s}(ℓ_s²)`: the second derivative of the reconstruction density is the normal projection
  of the squared score).
- `CovarianceFrechet.lean` (NOT mirrored; round-54 rank 1, stage 1 — the polarised response Hessian by the Fréchet
  route): `hasFDerivAt_of_subtypeL_comp`, `mem_of_hasFDerivAt_val` (derivatives of submodule-valued maps stay in
  the submodule), `covCLM`/`covCLM_apply` (`v ↦ −Cov_ρ(φ,⟨v,S⟩)`), `cumCLM`/`cumCLM_apply` (`v ↦ −T_ρ(f,g,⟨v,S⟩)`),
  **`hasFDerivAt_integral_family`** (`θ ↦ E_{P_θ}φ` Fréchet, derivative `covCLM`), **`hasFDerivAt_lawCov_family`**
  (`θ ↦ Cov_{P_θ}(f,g)`, derivative `cumCLM`), **`hasFDerivAt_famDens`** (`θ ↦ p_θ(x)`, derivative
  `p_θ(x)(⟨·,m(θ)⟩ − ⟨·,S(x)⟩)`, from `abs_famDens_remainder_le`), `thirdVec`, `thirdCoordCLM`,
  `hasFDerivAt_chartDeriv_coe`, `thirdVec_mem_dirSpan`, `thirdDir`, `hasFDerivAt_chartDeriv_apply`,
  **`thirdOp`** (`T_θ : 𝕍 →L (𝕍 →L 𝕍)`, the Fréchet derivative of the restricted covariance operator,
  `hasFDerivAt_chartDeriv`; `thirdOp_coe_apply` by uniqueness of derivatives), `dotCLMlin`, `dotCLM_add`,
  **`hasStrictFDerivAt_responseTheta_add`** (`z ↦ θ(M+z)` strictly differentiable with derivative
  `R = (Dm(θ)|_𝕍)⁻¹`), `hasFDerivAt_famDens_response` + `famDens_response_deriv_apply` (`D_M q_M(x)[u] = q_M(x) ℓ_{M,u}(x)`),
  `hasFDerivAt_chartDeriv_response`, **`hasFDerivAt_inverse_response`** (`D_M R_M[u] = −R T_{θ(M)}(Ru) R`, by
  `hasFDerivAt_ringInverse`), `thirdVec_eq_respCov` (`T_{θ(M)}(Ru, Rw) = Cov_Q(S, ℓ_u ℓ_w)`),
  **`hasFDerivAt_responseScore_response`** (`D_M ℓ_{M,w}(x)[u] = −E_Q[ℓ_u ℓ_w] − B_M(ℓ_u ℓ_w)(x)`),
  **`hasFDerivAt_famDens_responseScore`** (THE POLARISED HESSIAN: the derivative field `z ↦ q_{M+z} ℓ_{M+z,w}` is
  differentiable at `0` with derivative `u ↦ q_M · N_M(ℓ_{M,u} ℓ_{M,w})(x)`).
- `ObservableHessian.lean` (NOT mirrored; round-54 rank 1, stage 2 — the observable defect to second order):
  `integral_mul_dirLoss` (`∫ ψ⟨v,S⟩ = Σ vⱼ ∫ ψ Sⱼ`), `integral_mul_sub_dirLoss`, `hasFDerivAt_dotCLM_add`,
  **`hasFDerivAt_integral_response`** (`z ↦ E_{Π(M+z)} φ` differentiable in response coordinates),
  `integral_response_deriv_apply` (derivative `u ↦ E_Q[φ ℓ_{M,u}] = Cov_Q(φ, ℓ_{M,u})`),
  `hasFDerivAt_inverse_response_coord`, `hasFDerivAt_dotJ_inverse_response`,
  **`hasFDerivAt_integral_responseScore`** (the derivative field `z ↦ E_{Π(M+z)}[φ ℓ_{M+z,w}]` is differentiable at
  `0` with derivative `u ↦ E_Q[φ · N_M(ℓ_{M,u} ℓ_{M,w})]`: the second-order response of an observable is its pairing
  with the normal projection of the product of the response scores, so only the normal part of `φ` responds at
  second order).
- `FisherRaoCurvature.lean` (NOT mirrored; round-54 rank 3, stage 2 — the Fisher–Rao second fundamental form
  along the atlas): `famDens_pos`, `bdd_normalProj`, **`sqrtDens`** (`r_s = 2√q_s`), `sqrtDens_sq`,
  `integral_sqrtDens_sq` (`∫ r_s² dν = 4`: the curve lies on the sphere of radius 2 in `L²(ν)`),
  `integral_sqrtDens_sq_mul` (`∫ r_s² g dν = 4 E_{Q_s} g`), **`hasDerivAt_sqrtDens`** (`r_s' = r_s ℓ_s/2`),
  `integral_sqrtDens_velocity_sq` (`∫ (r_s')² dν = κ(s)`: the Fisher energy is the speed squared),
  **`hasDerivAt_sqrtDens_velocity`** (`r_s'' = (r_s/4) N(ℓ_s²) − (κ/4) r_s − (r_s/4) B(ℓ_s²)`),
  `integral_sqrtDens_mul_normal`, `integral_sqrtDens_mul_tangential`, `integral_normal_mul_tangential` (the
  three pieces are mutually orthogonal in `L²(ν)`: normal = second fundamental form of the family in the sphere,
  radial = curvature of the sphere, tangential = the atlas is not a geodesic of the family unless `B(ℓ²) = 0`).
- Round-55 consult (`gpt_responses/research_round55_{q,v1}.md`): the missing heart is FINITE RESPONSE — the
  accounting identity `E_D φ − E_ν φ = Cov_ν(φ, ℓ_{m₀,Δ}) + ∫₀¹ (1−s) E_{Q_s}[φ N_{M_s}(ℓ_s²)] ds + E_D[N_M φ]`
  (baseline susceptibility + accumulated nonlinear response + feature-invisible residual), plus the Peano
  expansion `F_φ(M+z) = F + A z + ½H(z,z) + o(‖z‖²)` (operator-valued assembly + generic Peano lemma), compact
  uniform remainders, the `L¹` density version; candidate (c) is FALSE: `D²_z KL(D‖Π(M+z)) = ⟨Σ_M⁻¹u,w⟩` is
  fibre-independent (Pythagoras); dual-flat package `∇𝓘 = −θ`, `D²𝓘 = G`, `DG[z](u,w) = −C(u,w,z)`.
- `FiniteResponse.lean` (NOT mirrored; round-55 rank 1, stage 1 — the accounting identity along the atlas):
  `familyMeasure_zero_eq` (`P_0 = ν`), `atlas_zero_eq` (`Q_0 = ν`), `integral_mul_atlasScore_eq`
  (`E_{Q_t}[φ ℓ_t] = ⟨β_t, M_t⟩E_{Q_t}φ − Σⱼ β_{t,j}E_{Q_t}[φ Sⱼ]`), **`hasDerivAt_integral_atlas`**
  (`d/ds E_{Q_s}φ = E_{Q_s}[φ ℓ_s]`), **`hasDerivAt_integral_atlasScore`** (`d²/ds² E_{Q_s}φ = E_{Q_s}[φ N_{M_s}(ℓ_s²)]`),
  **`integral_normalProj_eq_sub`** (the fibre identity `E_D[N_M φ] = E_D φ − E_{Π(M)} φ` for every data law with
  response `M`), `abs_lawCov_le`, `abs_integral_le_of_abs_le`, `continuousOn_ringInverse_chartDeriv_atlas`,
  `exists_bound_ringInverse_atlas` (`s ↦ Σ_s⁻¹` bounded on `[0,1]`), `norm_atlasPath_le`,
  `intervalIntegrable_integral_normalProj_atlas` (the second-derivative field is bounded on `[0,1]`),
  **`integral_atlas_taylor`** (Taylor with integral remainder: `E_{Q_1}φ − E_{Q_0}φ = E_{Q_0}[φ ℓ_0] +
  ∫₀¹(1−s)E_{Q_s}[φ N(ℓ_s²)]ds`), **`response_accounting`** (THE ACCOUNTING IDENTITY:
  `E_D φ − E_ν φ = E_ν[φ ℓ_0] + ∫₀¹ (1−s) E_{Q_s}[φ N_{M_s}(ℓ_s²)] ds + E_D[N_M φ]` — baseline susceptibility,
  accumulated nonlinear response along the atlas, feature-invisible residual).
- `FibreHessian.lean` (NOT mirrored; round-55 rank "land immediately" — the fibre-independent KL Hessian):
  **`eventually_add_mem_intrinsicInterior`** (the relative interior is open in `𝕍`: `M + z ∈ ri K` for `z` near `0`,
  from `HasStrictFDerivAt.map_nhds_eq_of_equiv` for the chart), `hasFDerivAt_responseTheta_add_at` (`z ↦ θ(M+z)`
  differentiable at every interior `z₀`), `hasFDerivAt_genRate_response_at` (`∇𝓘(M+z₀) = −θ(M+z₀)`),
  `hasFDerivAt_dotJ_responseTheta_at`, **`klDiv_fibre_eq`** (Pythagoras–Bregman: `KL(D‖Π(M+z)) = KL(D‖Π(M)) + 𝓘(M) −
  𝓘(M+z) − ⟨θ(M+z), z⟩` for `D` with response `M`), **`hasFDerivAt_klDiv_fibre`** (derivative `w ↦ −⟨R_{M+z₀}w, z₀⟩`
  at every interior `z₀`, independent of `D`), `hasFDerivAt_klDiv_fibre_zero` (critical at the reconstruction),
  **`hasFDerivAt_klDiv_fibre_field`** (the derivative field's derivative at `0` is `u ↦ E_Q[ℓ_u ℓ_w] = ⟨Σ_M⁻¹u,w⟩`:
  the transverse KL profile is the Fisher metric, the same on the whole fibre; no fibre-specific normal term).
- `ResponseTaylor.lean` (NOT mirrored; round-55 rank 1, stage 2 — the Peano expansion):
  **`isLittleO_peano_of_hasFDerivAt`** (generic: a derivative field `A` differentiable at `0` with derivative `B`
  gives `F z − F 0 − A 0 z − ½ B z z = o(‖z‖²)`, by the mean value inequality along the segment),
  **`responseDerivField`** (`A_z(w) = E_{Π(M+z)}[φ ℓ_{M+z,w}]` as a functional, defined for every `z`),
  `responseDerivField_apply`, **`hasFDerivAt_integral_response_at`** (the response of `φ` is differentiable at
  every interior point with derivative the field), **`hasFDerivAt_responseDerivField`** (the field is differentiable
  at `0` with derivative the response Hessian `B u w = E_Q[φ N_M(ℓ_u ℓ_w)]`, assembled on a basis and identified by
  uniqueness of derivatives), **`response_peano`**
  (`E_{Π(M+z)}φ = E_Qφ + E_Q[φ ℓ_{M,z}] + ½ E_Q[φ N_M(ℓ_{M,z}²)] + o(‖z‖²)`).
- `DualFlat.lean` (NOT mirrored; round-55 rank 4 — the dual-flat package): **`fisherForm`** (`G_M(u,w) =
  E_Q[ℓ_u ℓ_w]`), `fisherForm_comm`, **`cubicScore`** (`C_M(u,v,w) = E_Q[ℓ_u ℓ_v ℓ_w]`, name `cubicForm` taken by
  Patterning/GaussianFourth), `cubicScore_symm`, `fisherForm_eq_neg_dotJ`, **`hasFDerivAt_genRate_response`**
  (`∇𝓘(M) = −θ(M)`), **`hasFDerivAt_neg_dotJ_responseTheta`** (`D²𝓘 = G`), `integral_normalProj_mul_responseScore`
  (`N_M f ⊥ ℓ_w` in `L²(Q)`), `integral_regProj_mul_responseScore` (`B_M` is the `L²(Q)`-orthogonal projection onto
  tangent scores), **`hasFDerivAt_fisherForm_response`** (`DG_M[v](u,w) = −C_M(u,v,w)`), **`dual_flat_structure`**
  (potential + Hessian = Fisher + derivative of Fisher = −cubic + symmetry + Bregman canonical divergence).
- `ResponseStructure.lean` (NOT mirrored; round-55 rank 2 — the §7 packaging): **`response_structure_theorem`**, one
  statement in five parts: (1) the global chart `𝕍 ≃ₜ ri K` with strict derivatives, `Π = P_{θ}` and unique entropy
  minimiser on each fibre; (2) differential duality (`E_Q[ℓ_uℓ_z] = −⟨Ru,z⟩`, positive definite) and the dual-flat
  package (`∇𝓘 = −θ`, `D²𝓘 = G`, `DG = −C`); (3) the polarised density Hessian `q_M N_M(ℓ_uℓ_w)` and the Peano
  expansion of every bounded observable; (4) the accounting identity for every data law with interior response;
  (5) the boundary obstruction (`κ → ∞`, `∫₀¹κ = ∞`).
- `InformationAlongAtlas.lean` (NOT mirrored; round-56 "information companion"): `continuousOn_atlasCurv`,
  `intervalIntegrable_one_sub_mul_atlasCurv`, **`klDiv_data_atlas_eq_integral`** (`KL(D‖Q_s) = KL(D‖Π(M)) +
  ∫_s^1 (1−t)κ(t)dt` for a data law with response `M`), **`klDiv_data_eq_add_integral`** (the information budget
  `KL(D‖ν) = KL(D‖Π(M)) + ∫₀¹(1−t)κ`), `klDiv_data_atlas_antitone`, **`hasDerivAt_klDiv_data_atlas`**
  (`d/ds KL(D‖Q_s) = −(1−s)κ(s)` on `(0,1)`). Built on EndpointTail's
  `toReal_klDiv_responseProjection_atlas_eq_integral`.
- Round-56 consult (`gpt_responses/research_round56_{q,v1}.md`): sanity checks confirmed (geodesic claim is
  "affinely parametrised geodesic of the family iff `B(ℓ²) = 0`"; `Γ^{LC} = −½ Cov_Q(S, ℓ_uℓ_w)`, `Γ^{(m)} = 0`,
  `Γ^{(e)} = −Cov_Q(S,ℓ_uℓ_w)`; "normal part responds at second order" with two qualifications); NEXT flagship =
  the total-variation density Peano `∫|q_{M+z} − q_M − q_Mℓ_z − ½q_MN(ℓ_z²)| = o(‖z‖²)` via integrated continuity
  of the pointwise Hessian on a finite basis (no `Lp`), then compact-uniform remainders; boundary: the triangular
  endpoint `lim_{t↑1}[t E_ν(φℓ_0) + ∫₀ᵗ(t−s)…]` is the safe statement (needs TV convergence `Q_t → Q_*`); the
  information companion (done); `KL(Q_*‖Q_s) = ∫_s^1(1−t)κ` and `(1−s)i'(s) → 0` at finite-rate boundary points.
- `ThetaPeano.lean` (NOT mirrored; towards the TV density Peano): **`isLittleO_peano_of_hasFDerivAt'`** (the generic
  Peano lemma, vector-valued), **`isLittleO_responseTheta_peano`** (`θ(M+z) = θ(M) + Rz − ½R T(Rz)(Rz) + o(‖z‖²)`),
  `responseTheta_peano_quadratic` (`T(Rz)(Rz) = Cov_Q(S, ℓ_z²)` as an element of `𝕍`).
- `DensitySecondOrder.lean` (NOT mirrored): `ratio_core_identity`, `abs_ratio_core_le`,
  **`abs_ratio_sub_second_order_le`** (a ratio of two second-order truncated exponentials differs from the
  second-order truncation of the ratio by `≤ 13ε³`), `abs_exp_neg_sub_second_le` (`|e^{−w} − (1 − w + w²/2)| ≤ |w|³/4`),
  `densTrunc` (`T_θ(η) = 1 + ⟨η, m − S⟩ + ½(⟨η, m−S⟩² − Var_θ⟨η,S⟩)`), `famZ_add_div`, `integral_dirLoss_mul_famDens`,
  **`abs_famDens_second_remainder_le`** (POINTWISE-UNIFORM second order in natural coordinates:
  `|p_{θ+η} − p_θ T_θ(η)| ≤ 13 (K‖η‖)³ p_θ` for `K‖η‖ ≤ 1/4`).
- `DensityPeanoAlgebra.lean` (NOT mirrored): `affScoreAt` (`⟨v, m − S(x)⟩`), `covQ` (`Cov_{P_θ}(⟨v,S⟩,⟨w,S⟩)`),
  linearity/symmetry lemmas, `covQ_self_eq`, **`densTrunc_add`** (the exact splitting of the truncation at
  `η = v + ζ`), `abs_affScoreAt_le`, `abs_covQ_le`.
- `DensityPeano.lean` (NOT mirrored; round-56 flagship): **`famDens_response_peano`** — the POINTWISE-UNIFORM
  Peano expansion of the reconstruction density: `∃ φ = o(‖z‖²), ∀ᶠ z, ∀ x, |q_{M+z}(x) − q_M(x)(1 + ℓ_z(x) +
  ½N_M(ℓ_z²)(x))| ≤ φ(z) q_M(x)`; **`isLittleO_integral_famDens_response_peano`** — the TOTAL-VARIATION Peano
  expansion `∫|q_{M+z} − q_M − q_Mℓ_z − ½q_MN_M(ℓ_z²)| dν = o(‖z‖²)` (the score is the first derivative of the
  reconstructed law and the normalised squared score its second derivative, as signed measures). Route: explicit
  composition `η = Rz + ζ`, `ζ = −½R c_z + v`, `c_z = Cov_Q(S,ℓ_z²)`, `v = o(‖z‖²)`; `densTrunc_add` splits
  `T_θ(Rz + ζ)` into the target plus `⟨v,m−S⟩ + ℓ_z⟨ζ,m−S⟩ + ½⟨ζ,m−S⟩² − Cov(Rz,ζ) − ½Cov(ζ,ζ)`, each term
  bounded by `K₂‖v‖`, `K₂²‖R‖‖z‖‖ζ‖`, `K₃‖R‖‖z‖‖ζ‖`, `½(K₂²+K₃)‖ζ‖²`; the cubic remainder is
  `13(K(‖R‖+1)‖z‖)³` once `‖ζ z‖ ≤ ‖z‖` (threshold `δ ≤ 1/(BK₂²‖R‖³+1)`) and `K‖η‖ ≤ 1/4` (threshold
  `δ ≤ 1/(4K(‖R‖+1)+1)`).
- `BoundaryTaylor.lean` (NOT mirrored; round-56 boundary item A): scaling lemmas `responseScore_smul`,
  `respCov_congr_smul`, `regProj_congr_smul`, `normalProj_congr_smul`; the reparametrised atlas
  `atlasPath (atlasPath M t) s = atlasPath M (st)`, `atlasTheta`/`atlasVel`/`atlasScore` of the atlas point
  (`ℓ'_s = t ℓ_{st}`), `integral_normalProj_atlasPath` (`t² N(ℓ_{st}²)`); **`integral_atlas_taylor_of_lt`**: for
  a FINITE-RATE response (boundary allowed) and every `t < 1`, `E_{Q_t}φ − E_νφ = t E_ν[φℓ_0] + ∫₀ᵗ(t−u)E_{Q_u}[φN(ℓ_u²)]du`
  (change of variables `u = st` in the interior identity for `M_t`); **`tendsto_atlas_taylor_endpoint`**: if
  `E_{Q_t}φ → L` as `t ↑ 1` then the triangular accounting expression converges to `L − E_νφ`.
- `BoundaryCompletion.lean` (NOT mirrored; round-57 rank 1, mostly ASSEMBLY of existing seabed pieces):
  `atlas_eq_responseProjection` (`Q_s = Π(M_s)` for `s < 1`), **`tendsto_integral_atlas_endpoint`** (`E_{Q_t}φ →
  E_{Q_*}φ`, `Q_* = Π(M)` the information projection, via PinskerObservable's segment theorem),
  **`tendsto_atlas_taylor_responseProjection`** (triangular accounting at the endpoint with `L = E_{Q_*}φ`),
  **`tendsto_klDiv_responseProjection_atlas`** (`KL(Q_*‖Q_s) → 0`, squeeze by `𝓘(M) − 𝓘(M_s)`),
  **`sq_integral_sub_responseProjection_atlas_le`** (Pinsker at the endpoint: `(E_{Q_*}F − E_{Q_s}F)² ≤
  2L²∫_s^1(1−u)κ`), **`boundary_completion`** (eight-part package: projection spec, Pythagoras, tail identity
  `KL(Q_*‖Q_s) = ∫_s^1(1−u)κ`, KL → 0, observable convergence, triangular accounting). NB: the seabed ALREADY had
  the boundary information projection (`responseProjection_spec` needs only `hfin`), the tail identity
  (`EndpointTail`, `hfin` only) and the segment Pinsker convergence (`PinskerObservable`) — the consult's
  "TV-Cauchy construction" and "(1−s)i'(s) → 0" were unnecessary.
- `ReconstructionLipschitz.lean` (NOT mirrored; round-57 rank 2): `integral_abs_responseScore_le_sqrt`
  (`E_Q|ℓ_u| ≤ √E_Qℓ_u²`, via `variance_nonneg`), `fisherForm_self_le` (`≤ |J|‖R_M‖‖u‖²`),
  **`abs_integral_sub_le_of_segment`** (mean value inequality along an interior segment:
  `|E_{Π(M')}F − E_{Π(M)}F| ≤ √(|J|Λ)‖M'−M‖` for `|F| ≤ 1`), **`integral_abs_famDens_sub_le_of_segment`** (TV form
  via the sign test), **`exists_tv_lipschitz_of_isCompact_convex`** (compact convex `C ⊂ ri K` ⇒ TV-Lipschitz
  constant; `‖R‖` continuous on `ri K` through `relintChart`), `norm_density_response_sub_le`
  (`‖E_{d'ν}S − E_{dν}S‖ ≤ B∫|d'−d|`), **`integral_abs_famDens_density_sub_le`** (`d ↦ Π(E_{dν}S)` TV-Lipschitz on
  compact convex interior response sets), **`reconstruction_retraction`** (retraction `Π(E_{P_θ}S) = P_θ` [from
  `AtlasRefinement.responseProjection_mean_familyMeasure`] ∧ derivative has zero mass and transmits the moment
  perturbation ∧ compact-uniform TV-Lipschitz).
- `AtlasTotalVariation.lean` (NOT mirrored; round-57 rank 4): `integral_abs_le_sqrt_integral_sq` (generic Cauchy–Schwarz
  `∫|f| ≤ √∫f²` on a probability space), **`hasDerivAt_integral_atlas_of_lt`** (response derivative `E_{Q_u}[Fℓ_u]` along
  the atlas of ANY finite-rate response for `u < 1`, from the interior response derivative at the base point `m₀`),
  `atlasCurv_eq_integral_score_sq_of_lt` (`κ_u = E_{Q_u}ℓ_u²` under `hfin` only), `continuousOn_integral_mul_atlasScore`,
  **`integral_abs_famDens_atlas_sub_le`** (`∫|q_s − q_t| dν ≤ ∫_t^s √κ_u du`, `0 ≤ t ≤ s < 1`: FTC + sign test),
  `half_integral_abs_famDens_atlas_sub_le` (`d_TV(Q_s,Q_t) ≤ ½∫_t^s √κ`).
- `UniformPeano.lean` (generic, Mathlib-only): `norm_sub_deriv_le_of_uniform`, **`uniform_peano_of_hasFDerivAt`**
  (a `C²` map on a compact convex set with continuous second derivative has a uniformly `ε‖z'−z‖²`-small second-order
  Peano remainder; two mean value inequalities + uniform continuity of `B` on the compact).
- `ThetaUniformPeano.lean` (NOT mirrored): `continuous_integral_family`, **`continuous_thirdOp`** (the third-cumulant
  operator is continuous in `θ`: `continuous_clm_apply` twice + `thirdCentral_eq` + continuity of the family responses),
  `isCompact_preimage_add_mean`/`convex_preimage_add_mean` (the direction picture `{z : m₀ + z ∈ C}`),
  `hasFDerivAt_inverse_add_at` (`D R` at every interior point, by translation of `hasFDerivAt_inverse_response`),
  `continuousOn_inverse_add`, `continuousOn_responseTheta_add`, **`uniform_responseTheta_peano`** (compact-uniform
  second-order expansion of `θ`).
- `DensityPeanoUniform.lean` (NOT mirrored; round-57 rank 2b, the compact-uniform relative-uniform Peano):
  `densPeanoBound`/`densPeanoLead`/`densPeanoBound_le` (explicit remainder coefficient and its `(D r + n(Mb+B)ε) r²`
  bound), **`abs_famDens_response_remainder_le`** (QUANTITATIVE pointwise second-order bound with explicit constants:
  `B`, `Λ ≥ ‖R_M‖`, `Mb ≥ ‖M‖`, natural-coordinate remainder `≤ ε‖z‖²`, thresholds `(BK₂²Λ³+ε)‖z‖ ≤ 1`,
  `4K(Λ+1)‖z‖ ≤ 1`), `exists_bound_inverse_of_isCompact`, **`famDens_response_peano_uniform`** (∀ compact convex
  `C ⊂ ri K`, ∀ ε ∃ δ ∀ M ∈ C, M+z ∈ C, ‖z‖ ≤ δ, ∀ x: `|q_{M+z} − q_M(1+ℓ+½N(ℓ²))| ≤ ε‖z‖²q_M`),
  **`integral_abs_famDens_response_peano_uniform`** (the compact-uniform TV expansion).
- `ResponseAtlasTheorem.lean` (NOT mirrored; the CAPSTONE of the response-map programme): `klDiv_data_eq_add_integral_of_ne_top`
  (information budget `KL(D‖ν) = KL(D‖Π(M)) + ∫₀¹(1−s)κ` at EVERY finite-rate response, from Pythagoras +
  `genRate_toReal_eq_integral_atlasCurv`), **`response_atlas_reconstruction`** — the four-layer package: B (retraction,
  derivative projection, compact-uniform TV-Lipschitz), A (compact-uniform relative second-order expansion), C (accounting on
  `[0,t]`, TV speed ≤ Fisher speed, information budget), D (boundary completion, eight parts).
- `EmpiricalTotalVariation.lean` (NOT mirrored; round-58 candidate (v), done ahead of the consult): `exists_compact_convex_nhd`
  (every interior response has a compact convex interior neighbourhood catching all moment-body responses within `r`, from
  `eventually_add_mem_intrinsicInterior` and the closed ball in `𝕍`), **`ae_tendsto_integral_abs_famDens_sampleResponse`**
  (TV consistency `∫|q_{M̂_n} − q_{M_D}| → 0` a.s. for i.i.d. samples with interior data response, via the Lipschitz constant on
  the neighbourhood), **`ae_tendsto_integral_responseProjection_sampleResponse`** (`E_{Π(M̂_n)}φ → E_{Π(M_D)}φ` a.s. for bounded
  `φ`).
- `EntropyGapStability.lean` (NOT mirrored; round-58 rank 1 §4.3–4.4): **`lowerSemicontinuous_genRate`** (the rate is a
  supremum of continuous affine functions), `integral_mixture_eq`, **`ofReal_sq_sub_le_gap`** (the ENTROPY-GAP INEQUALITY
  `ab(E_{Π(A)}F − E_{Π(B)}F)²/(2L²) + 𝓘(aA+bB) ≤ a𝓘(A) + b𝓘(B)` from the mixture compensation identity + Pinsker, no
  boundary natural parameter), **`tendsto_integral_responseProjection_of_tendsto_genRate`** (NON-RADIAL boundary stability:
  finite-rate `M_i → M_*` with `𝓘(M_i) → 𝓘(M_*) < ∞` ⇒ `E_{Π(M_i)}F → E_{Π(M_*)}F` for every bounded `F`, any filter;
  the completion topology is that of `M ↦ (M, 𝓘(M))`). NB Astra's counterexample: response convergence alone does NOT
  give TV convergence at finite-rate boundary points.
- `SegmentStability.lean` (NOT mirrored; round-58 §4.2): `genRate_segment_le_of_ne_top` (convexity of the rate between any two
  finite-rate responses, from `genRate_mixture_gap` with `ℝ≥0` weights), `tendsto_segment_nhdsLT`,
  **`tendsto_genRate_segment_of_ne_top`** (`𝓘((1−t)A + tB) → 𝓘(B)` as `t ↑ 1`; lsc + convexity via `tendsto_order`),
  **`tendsto_integral_responseProjection_segment_of_ne_top`** (continuity of the reconstruction along every segment
  between finite-rate responses, boundary endpoints included).
- `ObservableTaylorUniform.lean` (NOT mirrored; round-58 "named corollary"): **`integral_response_peano_uniform`**
  (`E_{Π(M+z)}F = E_Q F + E_Q[Fℓ_z] + ½E_Q[F N(ℓ_z²)] + o(‖z‖²)B_F` uniformly on compact convex interior sets).
- `DualCurveComparison.lean` (NOT mirrored; round-58 rank 3/§3(iv) "matched-velocity comparison"): `densTrunc_smul`
  (`T_θ(tη) = 1 + ta + ½t²(a² − Var)`), `responseScore_eq_affScoreAt`, `covQ_responseScore`,
  **`abs_famDens_exponential_line_le`** (exponential curve `P_{θ+tRu}` to second order, relative-uniform, `O(t³)`),
  **`famDens_response_peano_line`** (mixture curve `Π(M+tu)` to second order, `o(t²)`), **`normalProj_sub_centred_sq`**
  (`N(ℓ²) − (ℓ² − Eℓ²) = −B(ℓ²)`), **`integral_responseScore_mul_normalProj_sub`** (pairing with the velocity = `−E_Qℓ³`),
  `dual_curve_comparison` (package). Both curves have velocity `Qℓ_u`; their second-order coefficients differ by the
  regression part of the squared score (a third-cumulant vector), whose pairing with the velocity is minus the skewness.
- `EntropyGapTotalVariation.lean` (NOT mirrored): `integral_responseProjection_eq_rnDeriv`, **`sq_integral_abs_rnDeriv_sub_le`**
  (the entropy-gap inequality in TOTAL VARIATION: `(∫|r_A − r_B|dν)² ≤ (2/(ab))[a𝓘(A) + b𝓘(B) − 𝓘(aA+bB)]` on the whole
  finite-rate domain, densities as Radon–Nikodym derivatives), `tendsto_entropy_gap_zero`,
  **`tendsto_integral_abs_rnDeriv_sub_of_tendsto_genRate`** (TV continuity of `M ↦ Π(M)` on the finite-rate domain for the
  topology of `(M, 𝓘(M))`).
- `DifferentialRetraction.lean` (NOT mirrored; round-59 rank 2): `responseScore_add`, `integrable_famDens_mul_responseScore`,
  `reconstructionL1` (`[q_M] ∈ L¹(ν)` via `Integrable.toL1`), `reconstructionDerivLin`/`reconstructionDeriv`
  (`u ↦ [q_M ℓ_{M,u}]` as a CLM, finite-dimensional domain), **`hasFDerivAt_reconstructionL1`** (`L¹`-Fréchet
  differentiability of the reconstruction density at every interior response, from
  `isLittleO_reconstruction_density_remainder` + `L1.norm_of_fun_eq_integral_norm`), **`moment_famDens_mul_responseScore`**
  (`H(q_Mℓ_u) = u`: the moment map inverts the derivative), `famDens_mul_regProj_eq` (`P_M(q_M g) = q_M B_M g` for centred
  bounded `g`), `famDens_mul_responseScore_moment_eq` (idempotence of `P_M = Dp_M ∘ H`).
- `RefinementTower.lean` (NOT mirrored; round-59 rank 3 package): **`refinement_tower`** — base splits for the coarse and
  fine statistics, refinement of the error `KL(D‖Π_c) = KL(D‖Π_f) + KL(Π_f‖Π_c)`, refinement of the visible information
  `𝓘_f = 𝓘_c + KL(Π_f‖Π_c)` (both from `AtlasRefinement`): feature refinement converts invisible information into
  visible information by exactly the divergence between the reconstructions.
- `ReconstructionC1.lean` (NOT mirrored; round-60 §2): `responseScore_sub_responseScore`, **`norm_reconstructionDeriv_sub_le`**
  (explicit operator-norm modulus of the `L¹` derivative), `continuousOn_inverse_chart` (`M ↦ R_M` continuous on `ri K`),
  **`continuousWithinAt_reconstructionDeriv`** (`p : M ↦ [q_M]` is `C¹` into `L¹(ν)` on the relative interior).
- `RegressionOrthogonality.lean` (NOT mirrored; round-60 §4 first item): `sub_integral_eq_regProj_add_normalProj`
  (`g − E_Qg = B_Mg + N_Mg`), `integral_regProj_mul_normalProj` (`⟨B_Mg, N_Mg⟩_{L²(Q)} = 0`),
  **`integral_sq_sub_eq_regProj_add_normalProj`** (Pythagoras `E_Q(g − E_Qg)² = E_Q(B_Mg)² + E_Q(N_Mg)²`): `B_M` is the
  `L²(Q)`-orthogonal projection onto the tangent scores.
- `CurveLength.lean` (NOT mirrored; round-60 §4 second item): `norm_reconstructionDeriv_apply_le` (`‖Dp_M u‖₁ ≤ √g_M(u,u)`),
  `hasDerivAt_reconstructionL1_curve` (chain rule in `L¹` along a differentiable curve of interior responses),
  **`integral_abs_famDens_curve_le`** (TV length ≤ Fisher–Rao length along every interior `C¹` curve:
  `∫|q_{M+γ(1)} − q_{M+γ(0)}| ≤ ∫₀¹ √g_{M+γ(t)}(γ',γ')`).
- `EmpiricalMoments.lean` (NOT mirrored; probabilistic inputs of the reconstruction-bias theorem): `map_Xs_eq`,
  `integral_comp_Xs`, `measurable_sampleResponse`, **`integral_sampleResponse`** (`E M̂_n = M_D`), `sampleResponse_sub_eq`,
  `integral_comp_Xs_sub`, `integrable_comp_Xs_mul`, **`integral_sampleResponse_sub_mul_sub`**
  (`E[(M̂_n − M)_a(M̂_n − M)_b] = Γ_ab/n`, `Γ = Cov_D(S)`, pairwise independence suffices),
  **`measureReal_abs_sampleResponse_sub_gt_le`** / **`measureReal_norm_sampleResponse_sub_gt_le`** (Hoeffding:
  `P(‖M̂_n − M‖ > δ) ≤ 2|J| exp(−nδ²/(8B²))` for features bounded by `B`, sup norm on `J → ℝ`, `iIndepFun`),
  `exists_tail_sampleResponse` (`∃ c > 0` with the rate `exp(−c n δ²)`).
- `BiasForm.lean` (NOT mirrored): `dirProj S ν` (linear projection `(J → ℝ) → 𝕍`, `dirProj_coe`), `linForm` (the linear
  Peano term as a linear functional on `J → ℝ`), `coordUnit`, `linearMap_eq_sum_coordUnit`, **`biasForm`**
  (`b_F(u,v) = ∫ N_M F · ℓ_{πu} ℓ_{πv} dQ_M`, a `LinearMap.mk₂` bilinear form on `J → ℝ`), `biasForm_eq_sum` (coordinate
  expansion), **`integral_mul_normalProj_comm`** (`N_M` is self-adjoint in `L²(Q_M)`: `∫ f N g = ∫ N f · g`),
  `integral_mul_normalProj_sq_eq_biasForm`, **`integral_response_peano_biasForm`** (the compact-uniform Peano expansion
  `G(M+z) = G(M) + linForm(z) + ½ b_F(z,z) + O(ε‖z‖²)`).
- `ReconstructionBias.lean` (NOT mirrored; round-60 §4 third item, the reconstruction-bias theorem): `obsResponse`
  (`G_F(M') = ∫ F dQ_{M'}`), `abs_obsResponse_le`, `continuousOn_obsResponse` (continuity on interior sets, via `dirProj`
  and `continuousOn_responseTheta_add`), `dataMoment D S = E_D S`, `plugIn` (truncated plug-in estimator, `Set.piecewise`),
  `norm_sq_le_sum_sq`, `abs_sampleResponse_le`, **`reconstruction_bias_core`** (fixed-`n` estimate:
  `|n(EĜ_n − G(M)) − ½ΣΓ_ab b_F(e_a,e_b)| ≤ BF ε Σ_a Γ_aa + n K P(‖M̂_n − M‖ > min r δ)`),
  **`reconstruction_bias`**: for iid samples of `D ≪ ν` with interior `M = E_D S`, `∃ C` compact convex interior
  neighbourhood of `M` with `n (E Ĝ_n − G_F(M)) → ½ Σ_{ab} Γ_ab b_F(e_a, e_b)`, `Γ = Cov_D(S)`. No CLT: unbiasedness +
  `Γ/n` second moments + Hoeffding tail on the exceptional set + compact-uniform Peano.
- `ReconstructionBias.lean` addendum: **`sum_dataCov_mul_biasForm_eq`** (`Σ_ab Γ_ab b_F(e_a,e_b) = E_D b_F(S(x)−M, S(x)−M)`:
  the bias coefficient is the data expectation of the bias form on the centred feature vector, independent of `π`).
- `ReconstructionBias.lean` addendum 2: **`dataMoment_mixture_eq_atlasPath`** (`E_{(1−t)ν+tD} S = atlasPath t`: the affine
  data path from the featureless law to the data has the straight atlas as its response path; round-61 rank 1 opener).
- Round-61 consult (`gpt_responses/research_round61_{q,v1}.md`): rank 1 data-path transport (`d/dt G_F(M_t) = ∫ ψ_{F,M_t} dḊ_t`,
  mixture path = straight atlas, `𝓘(M_t) = ∫_0^t (t−r) H_{M_r}(δ,δ) dr` convex nondecreasing); rank 2 information splitting
  along the atlas `KL(D_t‖ν) = 𝓘(M_t) + R(t)` with `R` NOT monotone (three-point counterexample: mixture of two family members
  leaves the family), `R(t) ≤ t KL(D‖ν)`, `tR'(t) = R(t) + KL(ν‖D_t) − KL(ν‖Q_{M_t})`; rank 3 `L¹`-`C²` + uniform whole-atlas
  response theorem; rank 4 visible-information bias `n(E𝓘(M̂_n) − 𝓘(M)) → ½ Σ Γ_ab H_M(e_a,e_b)`; rank 5 joint plug-in
  covariance (sandwich `Σ Γ_ab lin_F(e_a) lin_G(e_b)`, Fisher-dual only when `Γ = C_M`). Referee notes: localisation is
  legitimate (any bounded fallback gives the same limit), `π` is scaffolding (intrinsic coefficient proved), sup norm harmless.
- `ResponseTransport.lean` (NOT mirrored; round-61 rank 1): **`linForm_eq_neg_dotJ_respCov`** (`lin_{F,M}(u) = −⟨R_M u, Cov_{Q_M}(S,F)⟩`),
  `dotJ_inverse_chart_symm` (`R_M` is `dotJ`-symmetric), **`influence`** (`ψ_{F,M}(x) = −⟨R_M Cov(S,F), S(x) − M⟩`),
  `linForm_eq_neg_dotJ_influenceDir`, `integral_dotJ_statPoint_sub`, **`linForm_sub_featureless_eq_integral_influence`**
  (`lin_{F,M}(E_D S − m₀) = ∫ψ dD − ∫ψ dν`), **`hasDerivAt_integral_response_path`** (chain rule: `d/ds G_F(M(s)) =
  lin_{F,M(s)}(M'(s))` along any differentiable curve of interior responses), `continuousOn_responseTheta_path`,
  `continuousOn_linForm_path`, **`integral_response_sub_eq_integral_linForm`** (FTC: `G_F(M(1)) − G_F(M(0)) = ∫₀¹ lin(M') ds`
  for `C¹` paths), `integral_response_sub_featureless_eq_integral_atlas` (atlas transport from `m₀` to `M`),
  **`hasDerivAt_integral_response_atlas_influence`** (`d/dt G_F(M_t) = ∫ψ_{F,M_t} dD − ∫ψ_{F,M_t} dν` along the affine data path).
- `InvisibleHump.lean` (NOT mirrored; round-61 rank 2): `invisibleInformation_bridge_le_total` (`R_s ≤ s KL(D‖ν) − 𝓘(M_s)`),
  **`invisibleInformation_bridge_le`** (`R_s ≤ s R₁ + s 𝓘(M) − 𝓘(M_s)`, from the bridge modulus); the THREE-POINT COUNTEREXAMPLE:
  `uniform3`, `coordFeature` (`S(x) = x` on `Fin 3`), `hump3D = Pfam(−1) ∝ e^x`, `humpMix t = (1−t)ν + tD`,
  `humpResidual t = KL(humpMix t ‖ Π(E_{humpMix t} S))`, `humpResidual_zero`, `humpResidual_one`, **`humpResidual_pos`**
  (interior mixtures leave the family: the log-linear identity `p₀p₂ = p₁²` of family members, `loglinear_mul`, versus the
  strict hump `q₁² < q₀q₂` of a positive mixture, `hump_mul`), **`humpResidual_not_antitone`** (¬Antitone ∧ ¬Monotone):
  the invisible information along the affine data path is NOT monotone.
- `ReconstructionBias.lean` refactor: `reconstruction_bias_of_nhd` (explicit compact convex neighbourhood) + wrapper.
- `PlugInCovariance.lean` (NOT mirrored; round-61 rank 5): `abs_linearMap_le_norm`, `abs_bilinear_le_norm_sq`,
  `linearMap_mul_linearMap_eq_sum`, `exists_first_order_remainder` (`|G_F(M+z) − G_F(M) − lin(z)| ≤ (B_F + ½‖b_F‖)‖z‖²`),
  `integrable_plugIn_sampleResponse`, **`plugIn_product_core`** (fixed-`n` estimate of the scaled second moment of the two
  plug-in deviations), **`plugIn_product_tendsto_of_nhd`**, **`plugIn_covariance_tendsto_of_nhd`**
  (`n Cov(Ĝ_F, Ĝ_G) → Σ Γ_ab lin_F(e_a) lin_G(e_b)`, the bias product being `O(1/n²)`), `sum_dataCov_mul_linForm_eq_integral`
  (`= E_D[lin_F(S−M) lin_G(S−M)]`, the sandwich covariance of the influence functions), **`plugIn_covariance_tendsto`**
  (existential package: one `C` for all pairs of bounded observables).
- `InformationTaylor.lean` (NOT mirrored): `pairLin` (`θ ↦ (v ↦ −⟨v,θ⟩)`), `hasFDerivAt_rate_add`, `hasFDerivAt_pairLin_theta`,
  **`uniform_rate_peano`** (compact-uniform second-order expansion of `𝓘` in the direction picture, from
  `uniform_peano_of_hasFDerivAt`), `pairLin_comp_inverse_apply` (Hessian = Fisher form), **`fisherAmb`** (ambient Fisher form
  `g_M(πu, πv) = −⟨R_M πu, πv⟩`, a `LinearMap.mk₂`), `fisherAmb_coe`, **`rate_peano_at`**
  (`|𝓘(M+h) − 𝓘(M) + ⟨h,θ(M)⟩ − ½ g_M(h,h)| ≤ ε‖h‖²` uniformly on a compact convex interior neighbourhood).
- `PlugInBias.lean` (NOT mirrored): **the plug-in bias schema** `plugInGen`, `plugInGen_bias_core`,
  **`plugInGen_bias_tendsto_of_nhd`**: any functional `Φ` continuous on `C` with a uniform second-order expansion
  `Φ(M+z) = Φ(M) + Lz + ½ b(z,z) + o(‖z‖²)` has `n(EΦ̃_n − Φ(M)) → ½ Σ Γ_ab b(e_a,e_b)`.
- `InformationBias.lean` (NOT mirrored; round-61 rank 4): `continuousOn_toReal_genRate`, `rateGrad`,
  `information_bias_tendsto_of_nhd`, `sum_dataCov_mul_bilinear_eq_integral`, **`information_bias_tendsto`**
  (`n(E 𝓘(M̂_n) − 𝓘(M)) → ½ E_D[g_M(S−M, S−M)]`: the expected excess visible information of a sample is half the
  Fisher-quadratic mean of the centred features, i.e. `½ tr(Γ H_M)`).
- Round-62 consult (`gpt_responses/research_round62_{q,v1}.md`): flagship `C²` `L¹`-Hessian as an invisible signed measure;
  tangent Pythagoras; natural-gradient atlas; second-order transport; invisible `L²` expansion; tilt-path diagnostics.
- `TangentPythagoras.lean` (NOT mirrored; round-62 rank 2): `integral_regProj_sq_eq_fisherForm`, **`influence_eq_regProj`**
  (`ψ_{F,M} = B_M F`), **`tangent_pythagoras`** (`E_Q(a − E_Q a)² = g_M(u,u) + E_Q(N_M a)²`, `u = Cov_Q(S,a)`),
  **`integral_influence_mul_responseScore`** (`E_Q[ψ_F ℓ_u] = lin_F(u)`: Riesz representation on tangent scores),
  `integral_influence` (centred), **`lawCov_influence_self`** (`Var_Q ψ_F = g_M(c_F, c_F)`),
  `linForm_statPoint_sub_eq_influence`, `ae_statPoint_sub_mem_dirSpan`, **`plugIn_covariance_tendsto_influence`**
  (`n Cov(Ĝ_F, Ĝ_G) → E_D[ψ_F ψ_G]`).
- `SecondOrderTransport.lean` (NOT mirrored; round-62 rank 4): `abs_thirdCentral_le` (`|T(g,k,f)| ≤ 8 B_g B_k B_f`),
  `atlasInc`, `atlasLin` (`−Cov_{Q_s}(F, ⟨v_s, S⟩)` = the first-order transport), `atlasLin_eq_linForm`, `atlasBeta`
  (the canonical regression coefficient `−R_{M_s} Cov_{Q_s}(S,F)`), `atlasBeta_regression`, `atlasQuad`
  (`thirdCentral` second derivative), `hasDerivAt_atlasLin`, **`atlasQuad_eq_biasForm`** (the seabed's third-central
  second derivative IS the bias form `b_{F,M_s}(δ,δ) = E_{Q_s}[N F ℓ_δ²]`), `exists_bound_atlasQuad`,
  **`integral_response_atlas_taylor`** (Taylor with integral remainder, via `measurable_deriv` + a uniform bound),
  **`obsResponse_atlas_eq_second_order`** (`G_F(M_t) = G_F(m₀) + t lin_{F,m₀}(δ) + ∫₀ᵗ (t−r) b_{F,M_r}(δ,δ) dr`),
  **`hasDerivAt_deriv_obsResponse_atlas`** (`(G_F ∘ M)''(s) = b_{F,M_s}(δ,δ)` on `(0,1)`).
- `NaturalGradientAtlas.lean` (NOT mirrored; round-62 rank 3): `natLoss` (`L(M) = KL(Q_{M*}‖Q_M)`), `natLoss_eq` (Bregman
  form `A(θ(M)) − A(θ*) + ⟨θ(M) − θ*, M*⟩`), **`hasFDerivAt_natLoss`** (`dL_M[u] = ⟨R_M u, M* − M⟩`), `fisherForm_neg_right`,
  **`natLoss_deriv_eq_fisherForm`** (`dL_M[u] = g_M(M − M*, u)`: the natural gradient is the displacement), `natFlow`
  (`M(τ) = atlasPath(1 − e^{−τ})`), `natFlow_zero`, **`hasDerivAt_natFlow`** (`M' = −(M − M*)`), `tendsto_natFlow`,
  `natFlow_mem_intrinsicInterior`, **`hasDerivAt_natLoss_natFlow`** (dissipation `dL/dτ = −g_{M(τ)}(M(τ)−M*, M(τ)−M*)`).
- `InvisibleQuadratic.lean` (NOT mirrored; round-62 rank 5): `genRate_featureless_ne_top`, `featureless_mem_intrinsicInterior`,
  `responseTheta_featureless` (`θ(m₀) = 0`), `familyMeasure_responseTheta_featureless` (`Q_{m₀} = ν`),
  **`tendsto_genRate_atlas_div_sq`** (`𝓘(m₀ + sδ)/s² → ½ g_{m₀}(δ,δ)`), `bdd_sub_one`, `mean_densLaw_mem_intrinsicInterior`,
  `invisibleBridge` (`R(s) = KL(D_s‖Π(M_s))` for `D_s = (1 + s(d−1))ν`), `invisibleBridge_eq` (Pythagoras),
  **`tendsto_klDiv_bridge_div_sq`** (`KL(D_s‖ν)/s² → ½ E_ν(d−1)²`), `respCov_featureless_sub_one` (`Cov_ν(S, d−1) = M_D − m₀`),
  **`integral_sub_one_sq_eq_fisher_add_normal`** (tangent Pythagoras at `m₀`), **`tendsto_invisibleBridge_div_sq`**
  (`R(s)/s² → ½ ‖N_{m₀}(d−1)‖²_{L²(ν)}`: the invisible information is the squared normal data displacement).
- Round-63 consult (`gpt_responses/research_round63_{q,v1}.md`): flagship = uniform `L¹` second jet (already
  `integral_abs_famDens_response_peano_uniform`); `L¹` signed-measure bias = observable-uniform scalar bias; retraction
  differential; closing main theorem "Response geometry: projection, invisible bending, averaged curvature".
- `UniformBias.lean` (NOT mirrored; round-63 rank 1 in dual form): **`integral_response_peano_uniform_all`** /
  **`integral_response_peano_biasForm_all`** (the observable Taylor expansion with a modulus independent of the observable),
  `abs_linForm_le_of_bound` (`|lin_F(u)| ≤ ‖F‖∞ ∫|ℓ_{πu}|`), `abs_biasForm_le_of_bound` (`|b_F(u,v)| ≤ ‖F‖∞ ∫|N(ℓ_{πu}ℓ_{πv})|`),
  **`reconstruction_bias_uniform_of_nhd`** (`sup_{‖F‖∞≤1} |n(EĜ_{F,n} − G_F(M)) − ½ΣΓ_ab b_F(e_a,e_b)| → 0`: the dual form of
  the `L¹`-valued signed-measure bias `n(E[q̃_n] − q_M) → ½E_D[H_M[S−M,S−M]]`).
- `ResponseGeometry.lean` (NOT mirrored; round-63 closing theorem): **`integral_deviation_eq_zero`** /
  **`integral_stat_mul_deviation_eq_zero`** / **`deviation_invisible`** (the exact, non-asymptotic invisibility identity
  `∫ (1, S)(q_{M+h} − q_M − q_M ℓ_{M,h}) dν = 0` for interior `M`, `M + h`: every nonlinear deviation of the reconstruction
  from its tangent prediction is invisible to the features), and **`response_geometry`** — "Response geometry: projection,
  invisible bending, and averaged curvature", the five-part package assembled from landed pieces: (1) `Π(M*) = Q_{M*}`,
  response `M*`, idempotence `Π(E_{Q_θ}S) = Q_θ`, `L¹`-differential `u ↦ [q ℓ_u]`, moment map inverts it; (2) whole-law
  transport `G_F(M*) − G_F(m₀) = ∫₀¹ lin_{F,M_s}(δ) ds`; (3) invisible bending (second-order transport + the exact
  invisibility identity); (4) sampling averages the bending, uniformly over `‖F‖∞ ≤ 1`; (5) the atlas is the
  natural-gradient trajectory of `KL(Q_{M*}‖Q_M)` (start, ODE, convergence, Fisher dissipation).
- `DataRetraction.lean` (NOT mirrored; round-63 rank 2, the reconstruction as a retraction of the DATA manifold):
  `exists_feature_bound`, `integrable_stat_mul_L1`, `momentLin`/**`momentL1`** (the moment functional `d ↦ ∫ S d dν` as a CLM
  `L¹(ν) → (J → ℝ)`, `momentL1_apply`), `dirProjL` (`dirProj` as a CLM), **`visibleL1`** (the visible part `π ∫ S h dν ∈ 𝕍` of
  a data direction), **`dataRecon`** (`R(d) = [q_{m(d)}]` on `L¹(ν)`), `momentL1_reconstructionL1` / **`momentL1_dataRecon`**
  (`m ∘ R = m`), **`dataRecon_dataRecon`** (`R ∘ R = R`), `momentL1_reconstructionDeriv` / `visibleL1_reconstructionDeriv`
  (`π m(Dp_M u) = u`), **`momentL1_sub_mem_dirSpan`** (zero-mass data directions have visible moments in `𝕍`, via the a.e.
  membership `S(x) − m₀ ∈ 𝕍` and the projection trick `∫ f = ι P ∫ f`), `momentL1_mem_dirSpan`,
  **`hasFDerivWithinAt_dataRecon`** (on the fixed-mass affine subspace, `DR_d[h] = Dp_{m(d)}(π ∫ S h dν)`: the pushforward of a
  data tangent is the reconstruction derivative of its visible part), **`dataReconDeriv_comp_self`** (`DR ∘ DR = DR`),
  **`dataReconDeriv_eq_zero_iff`** (`ker DR = {∫ S h dν = 0}`, the invisible data directions), **`momentL1_sub_dataReconDeriv`**
  (every zero-mass direction = visible tangent score + invisible remainder), `norm_dataReconDeriv_le` (`‖DR h‖₁ ≤ √g(πh, πh)`),
  **`hasDerivAt_dataRecon_path`** (the chain rule along any differentiable constant-mass path of `L¹` densities).
- `TransportL1.lean` (NOT mirrored; round-63 rank 3 in Bochner form): **`reconstructionL1_curve_sub_eq_integral`** (the
  Bochner FTC in `L¹(ν)` along a `C¹` curve of interior responses, `[q_{M+γ(1)}] − [q_{M+γ(0)}] = ∫₀¹ Dp_{M+γ(t)} γ'(t) dt`),
  `hasDerivAt_dirProjL_atlasPath` (the atlas as a `𝕍`-valued curve via `dirProjL`),
  **`reconstructionL1_sub_featureless_eq_integral_atlas`** (`[q_M] − [q_{m₀}] = ∫₀¹ [q_{M_s} ℓ_{M_s, M−m₀}] ds` in `L¹`).
- `TiltDiagnostic.lean` (NOT mirrored; round-62 rank 6): `dotJ_smul_right`, **`atlas_rate_euler`** (`s𝓘'(s) − 𝓘(s) =
  KL(ν‖Q_{M_s})`), `abs_log_bridgeDens_le`, `toReal_klDiv_bridge_eq_integral_klFun`, **`hasDerivAt_integral_klFun_bridge`**
  (differentiation under the integral: `A'(s) = ∫ (d−1) log(1 + s(d−1)) dν`), `hasDerivAt_klDiv_bridge`,
  **`bridge_information_euler`** (`sA'(s) − A(s) = KL(ν‖D_s)`), **`hasDerivAt_invisibleBridge`**, **`invisibleBridge_euler`**
  (`sR'(s) − R(s) = KL(ν‖D_s) − KL(ν‖Q_{M_s})`), **`hasDerivAt_invisibleBridge_div`** (`d/ds (R(s)/s) = (KL(ν‖D_s) −
  KL(ν‖Q_{M_s}))/s²`: the invisible information per unit displacement grows exactly where the reverse information of the
  data exceeds that of its reconstruction — the tilt diagnostic).
- `FibreOrthogonality.lean` (NOT mirrored; round-64 rank 2, the dual foliation): `integral_dirLoss_of_response`,
  `klDiv_familyMeasure_ne_top`, **`toReal_klDiv_split_family`** / **`klDiv_split_family`** (for `ρ ≪ ν` of finite information
  with response `M` and EVERY natural parameter `θ`: `KL(ρ‖Q_θ) = KL(ρ‖Q_M) + KL(Q_M‖Q_θ)`; route: three tilted-reference
  formulas `toReal_klDiv_tilted_right` + `∫ dirLoss θ dρ = ⟨θ, M⟩ = ∫ dirLoss θ dQ_M`), `klDiv_family_ne_top`,
  **`klDiv_family_le`** (the reconstruction is the information projection onto the whole family), **`klDiv_family_eq_iff`**
  (uniqueness), **`integral_responseScore_mul_invisible`** (`∫ ℓ_{M,u} k dν = 0` for zero-mass zero-moment `k`: invisible
  directions ⟂ tangent scores), `integrable_famDens_mul_of_bdd`, **`momentL1_toL1_famDens_mul`** (the visible part of
  `q_M φ` with `E_Q φ = 0` is `Cov_Q(S, φ)`), **`dataReconDeriv_section`** (`DR_{q_M}[q_M φ] = [q_M · B_M φ]`: the retraction
  differential at the section is the regression projection), **`fisher_orthogonal_splitting`** (`E_Q φ² = g(c_φ,c_φ) +
  E_Q(φ − B_M φ)²`: the data tangent space at the section splits orthogonally into the family tangent and the fibre).
- `NormalForm.lean` (NOT mirrored; round-64 rank 1, the global visible–invisible normal form): `invisibleDirs`
  (`K = {∫k = 0, ∫Sk = 0}`), `dataSet` (`U = {∫d = 1, m(d) ∈ Ω}`), **`normalForm`** (`Φ(d) = (m(d), d − p(m(d)))`),
  **`normalFormInv`** (`Ψ(M,k) = p(M) + k`), `integral_reconstructionL1` (unit mass), `integral_L1_add/sub`,
  **`normalForm_mem`** / **`normalFormInv_mem`** / **`normalFormInv_normalForm`** / **`normalForm_normalFormInv`** (`Φ`, `Ψ`
  are mutually inverse bijections `U ≃ Ω × K`), **`dataRecon_normalFormInv`** (`R(Ψ(M,k)) = p(M)`: in normal-form
  coordinates the reconstruction is the projection onto the response), `normalForm_dataRecon` (`Φ(R d) = (m d, 0)`),
  **`hasFDerivWithinAt_normalForm`** (`DΦ_d[h] = (m(h), h − DR_d[h])` within `U`),
  `hasFDerivWithinAt_reconstructionL1_dirProjL` (`p` differentiable within `Ω` with derivative `Dp_M ∘ π`),
  **`hasFDerivWithinAt_normalFormInv`** (`DΨ_{(M,k)}[u,k'] = Dp_M(πu) + k'` within `Ω × K`): the response family is a
  global section of the data space and every datum is response coordinates plus an exactly invisible residual.
- `ResponseChernoff.lean` (NOT mirrored; round-64 rank 4): **`toReal_genRate_eq_neg_dotJ_sub_featCgf`** (`𝓘(M) = −⟨θ(M), M⟩ −
  Λ_ν(−θ(M))`: the rate is the Chernoff exponent at its own natural parameter), **`response_chernoff`**
  (`ν^{⊗n}(⟨θ(M), R̄_n⟩ ≤ ⟨θ(M), M⟩) ≤ e^{−n𝓘(M)}`: the visible information is the exponential cost of producing the
  response from the featureless law; the seabed's `halfspace_chernoff` at direction `−θ(M)`, multiplier 1).
- `SmoothFamily.lean` (NOT mirrored; round-64 rank 3, stage A): `famNum` (`N_g(θ) = ∫ g e^{−⟨θ,S⟩} dν`), `famZ_eq_famNum`,
  `integrable_mul_famWeight`, `integral_mul_dirLoss_mul_famWeight`, **`hasFDerivAt_famNum`** (`DN_g(θ) = −⟨·, (N_{gS_j}(θ))_j⟩`),
  **`contDiff_famNum`** (`C^n` for every `n` by induction — the derivative is a weighted normaliser again, so no
  differentiation under the integral beyond first order), `contDiff_infty_famNum`, **`contDiff_famZ`**, `famMean_eq_famNum_div`,
  **`contDiff_famMean`** / **`contDiff_meanMap`** (the mean map is `C^∞`), `meanMapDeriv_eq_fderiv`, **`contDiff_meanMapDeriv`**,
  **`contDiff_chartV`** (the intrinsic chart `𝕍 → 𝕍`), `chartDeriv_eq_dirProjL`, **`contDiff_chartDeriv`**,
  **`contDiff_chartDerivEquiv_symm`** (`θ ↦ (Dm(θ)|_𝕍)⁻¹` is `C^∞`, via `contDiffAt_map_inverse`).
- `SmoothChart.lean` (NOT mirrored; round-64 rank 3, stage B — the smooth bootstrap): `mem_range_chartV_iff`
  (`v ∈ range chartV ↔ m₀ + v ∈ Ω`), **`isOpen_range_chartV`** (inverse function theorem), `fderiv_chartVInv_of_mem`
  (`D chartVInv(v) = (Dm(θ)|_𝕍)⁻¹` at `θ = chartVInv v`), `differentiableOn_chartVInv`, **`contDiffOn_chartVInv`**
  (`C^n ⇒ C^{n+1}` via `contDiffOn_succ_iff_fderiv_of_isOpen` and the `C^∞` inverse covariance),
  **`contDiffOn_infty_chartVInv`**, `responseTheta_add_eq_chartVInv`, **`contDiffOn_responseTheta_add`** (`z ↦ θ(m₀ + z)` is
  `C^∞` on the interior displacements), **`contDiff_integral_familyMeasure`** (`θ ↦ E_{Q_θ} F` is `C^∞`),
  `atlasPath_eq_add_smul_atlasInc`, **`contDiffOn_atlasTheta`** (`s ↦ θ(M_s)` is `C^∞` where the atlas is interior),
  `Ioo_subset_atlas_interior`, **`contDiffOn_integral_atlasTheta`** (the response of every bounded observable is `C^∞` along
  the atlas): the response calculus exists to all orders.
- `InvisibleTower.lean` (NOT mirrored; the all-orders invisibility in `L¹` form): `weightL1` (`θ ↦ [g e^{−⟨θ,S⟩}] ∈ L¹`),
  `weightDeriv`, `weightDeriv_apply`, `exists_dirLoss_bound`, **`norm_weightL1_remainder_le`** (quadratic remainder from
  `|e^{−u} − 1 + u| ≤ u²`), **`hasFDerivAt_weightL1`**, **`contDiff_weightL1`** (`C^n` into `L¹` by induction — the derivative
  is a weighted weight again), `contDiff_infty_weightL1`, `densL1`, `densL1_eq` (`[q_θ] = Z⁻¹ • [e^{−⟨θ,S⟩}]`),
  **`contDiff_densL1`** (the reconstruction density is a `C^∞` map into `L¹(ν)`), `reconstructionL1_eq_densL1`,
  `atlasDomain` (`{s | M_s ∈ Ω}`), **`contDiffOn_reconstructionL1_atlas`** (`s ↦ [q_{M_s}]` is `C^∞` in `L¹` on the interior atlas
  domain), `isOpen_atlas_interior`, `momentL1_reconstructionL1_atlas`, `iteratedDerivWithin_affine_eq_zero`,
  `clm_iteratedDerivWithin_reconstructionL1_atlas` (CLMs commute with `iteratedDerivWithin` on the open domain),
  **`invisible_tower`** (every derivative of order `≥ 2` of the reconstruction along the atlas has zero feature moments and
  zero mass), **`momentL1_iteratedDerivWithin_one`** (the first derivative carries exactly `M − m₀`).
- `AtlasJetL1.lean` (NOT mirrored; round-65 rank 2, the `L¹` jets and the featureless expansion): `integrable_bdd_mul_L1`,
  `obsLin`/**`obsL1`** (pairing with a bounded observable as a CLM on `L¹`, `abs_obsL1_le : |⟨F, d⟩| ≤ ‖F‖∞‖d‖₁`),
  `obsL1_reconstructionL1`, **`L1_eq_zero_of_forall_integral_mul`** / **`L1_ext_of_forall_integral_mul`** (duality: an `L¹`
  element is determined by its pairings with bounded observables, via the sign observable), `hasDerivAt_reconstructionL1_atlas`,
  **`iteratedDeriv_one_reconstructionL1_atlas`** (`p'(s) = [q_{M_s} ℓ_{M_s, M−m₀}]`), `clm_iteratedDeriv_reconstructionL1_atlas`,
  **`integral_mul_atlasHess_eq_biasForm`** (`∫ F · atlasHess_s dν = b_{F,M_s}(δ,δ)`), **`iteratedDeriv_two_reconstructionL1_atlas`**
  (`p''(s) = [atlasHess_s] = [q_{M_s} N_{M_s}(ℓ_s²)]` on `(0,1)`: the density-acceleration theorem in `L¹`, by duality),
  `Icc_subset_atlasDomain`, `contDiffOn_reconstructionL1_atlas_Icc`, `contDiffAt_reconstructionL1_atlas_zero`,
  `taylorWithinEval_reconstructionL1_atlas`, **`reconstructionL1_taylor_remainder`** (`‖p(s) − Σ_{k≤n} s^k/k! p^{(k)}(0)‖₁ ≤ C s^{n+1}/n!`
  on `[0,1]`), **`obsResponse_atlas_taylor`** (the featureless expansion of the response of every bounded observable with the
  SAME constant: `|E_{Q_{M_s}}F − Σ_k s^k/k! ∫ F p^{(k)}(0)| ≤ ‖F‖∞ C s^{n+1}/n!`).
- `FeaturelessJet.lean` (NOT mirrored; round-65 rank 2, the jets at maximal entropy): **`eq_zero_of_isLittleO_sq`**
  (uniqueness of Peano coefficients: `a s + b s² = o(s²)` as `s → 0⁺` ⇒ `a = b = 0`), `famDens_featureless` (`q_{m₀} = 1`),
  **`reconstructionL1_featureless`** (`p(0) = [1]`), `integral_mul_iteratedDeriv_zero_atlas_zero`,
  **`iteratedDeriv_one_reconstructionL1_atlas_zero`** (`p'(0) = [ℓ_{m₀,M−m₀}]`), `integral_mul_iteratedDeriv_one_atlas_zero`
  (`∫ F p'(0) = lin_{F,m₀}(δ)`), **`isLittleO_obsResponse_atlas_zero`** (observable Peano at `m₀` along the atlas from the
  TV Peano `isLittleO_integral_famDens_response_peano` composed with `s ↦ s•δ`), `isLittleO_obsResponse_atlas_taylor_two`
  (`taylor_isLittleO` paired with `F`), **`integral_mul_iteratedDeriv_two_atlas_zero`** (`∫ F p''(0) = b_{F,m₀}(δ,δ)` by
  uniqueness), **`iteratedDeriv_two_reconstructionL1_atlas_zero`** (`p''(0) = [atlasHess_0] = [N_{m₀}(ℓ²)]`),
  **`obsResponse_atlas_second_order_featureless`** (the explicit second-order featureless expansion
  `|E_{Q_{M_s}}F − (E_ν F + s lin_F(δ) + ½ s² b_F(δ,δ))| ≤ ‖F‖∞ C s³/2` on `[0,1]`, `C` independent of `F`).
- `ResponseHessian.lean` (NOT mirrored; round-65 rank 1, the Hessian in all directions): `biasForm_comm`, `addDomain`
  (`{z ∈ 𝕍 | M + z ∈ Ω}`), `lineCLM`, **`isOpen_addDomain`**, **`contDiffOn_reconstructionL1_add`** /
  **`contDiffAt_reconstructionL1_add`** (`z ↦ [q_{M+z}]` is `C^∞` on the interior displacements of every interior `M`),
  `isSymmSndFDerivAt_reconstructionL1_add`, **`iteratedDeriv_two_line_eq`** (`d²/ds² P(sw)|₀ = D²P_0[w,w]`, via
  `ContinuousLinearMap.iteratedFDerivWithin_comp_right`), `hasDerivAt_reconstructionL1_line`, `contDiffOn_line_Icc`,
  `integral_mul_iteratedDeriv_zero/one_line`, `isLittleO_obsResponse_line` (TV Peano at `M` along the line, paired),
  `isLittleO_obsResponse_line_taylor_two`, **`integral_mul_fderiv_fderiv_diag_of_line`** / **`integral_mul_fderiv_fderiv_diag`**
  (the diagonal Hessian pairs to `b_F(w,w)`; general `w` by rescaling into the interior), **`integral_mul_fderiv_fderiv_eq_biasForm`**
  (polarisation + symmetry of second derivatives: `∫ F · D²P_M[u,v] = b_{F,M}(u,v)`), **`fderiv_fderiv_reconstructionL1_add`**
  (`D²P_M[u,v] = [q_M N_M(ℓ_{M,u} ℓ_{M,v})]`), **`momentL1_fderiv_fderiv_eq_zero`** (the Hessian is invisible: zero mass, zero
  feature moments).
- `CurvedTransport.lean` (NOT mirrored; round-65 rank 1, curved paths): `fderiv_comp_sub_const'` (translation invariance of
  `fderiv`), `contDiffAt_reconstructionL1_add_of_mem`, `reconstructionL1_add_eq_sub`, **`fderiv_reconstructionL1_add_of_mem`**
  (`DP_{z₀} = Dp_{M+z₀}` at every interior displacement), **`fderiv_fderiv_reconstructionL1_add_of_mem`** (the invisible Hessian
  at every interior displacement, by translation to the base point), **`hasDerivAt_reconstructionL1_path`** /
  `deriv_reconstructionL1_path` (first-order transport along any `C¹` interior path), **`hasDerivAt_deriv_reconstructionL1_path`**
  (second-order transport along any `C²` interior path: `d²/dt²[q_{M_t}] = [q N(ℓ_{Ṁ}²)] + [q ℓ_{M̈}]`),
  **`momentL1_deriv_deriv_reconstructionL1_path`** (`∫ S d²/dt²[q_{M_t}] = M̈`: the bending is invisible, the response
  acceleration is visible).
- `SmoothNormalForm.lean` (NOT mirrored; round-65 rank 1, the `C^∞` upgrade): `eq_add_dirProjL_sub_of_mem`,
  `dirProjL_sub_mem_addDomain`, **`contDiffOn_reconstructionL1_interior`** (`M ↦ [q_M]` is `C^∞` on `Ω`),
  **`contDiffOn_dataRecon`** (`R` is `C^∞` on the data space), **`contDiffOn_normalForm`** / **`contDiffOn_normalFormInv`**,
  **`smooth_normal_form`** (the package: `Φ`, `Ψ` mutually inverse `C^∞` bijections `U ≃ Ω × K`, `R ∘ Ψ = p ∘ fst`).
- `L1PointwiseDeriv.lean` (NOT mirrored; round-66 rank 3, the principle): **`coeFn_hasDerivAt_L1_ae`** (an `L¹`-differentiable
  curve `f : ℝ → L¹(ν)` with pointwise representatives `φ t` near `s₀` that are differentiable in `t` at every `x` has
  `L¹`-derivative `= [h]` a.e.: `L¹` convergence of the difference quotients ⇒ a.e.-convergent subsequence ⇒ uniqueness of limits),
  **`hasDerivAt_L1_eq_toL1`**, `integrable_of_hasDerivAt_L1`.
- `ThirdJet.lean` (NOT mirrored; round-66 rank 3, projection after differentiation): `responseScore_zero`,
  `respCov_eq_zero_of_invisible`, **`normalProj_eq_self_of_invisible`** (zero mean + zero feature moments under `Q_M` ⇒ `N_M F = F`),
  **`famDens_mul_normalProj_of_invisible`** (`q_M F` invisible ⇒ `q_M N_M F = q_M F` pointwise), `respCov_add`, **`normalProj_add`**,
  **`normalProj_const`**, `normalProj_const_mul`, `normalProj_congr`, **`contDiffOn_atlasVel`** (`s ↦ β_s` is `C^∞` on the interior
  atlas domain), `atlasVelD`/`atlasVelDD` (`β'`, `β''`), `hasDerivAt_atlasVel(D)_of_mem`, `atlasVelD_eq_atlasAccel`,
  `atlasScoreD`/`atlasScoreDD` (`ℓ' = ⟨β',M_s⟩ + ⟨β,δ⟩ − ⟨β',S⟩`, `ℓ'' = ⟨β'',M_s⟩ + 2⟨β',δ⟩ − ⟨β'',S⟩`),
  `hasDerivAt_atlasScore(D)_of_mem`, `atlasHess'` (`= atlasHess` on `[0,1]`), `atlasH3` (`ℓ³ + 3ℓℓ' + ℓ''`), `atlasThird`,
  **`hasDerivAt_atlasHess'`** (`q''' = q(ℓ³ + 3ℓℓ' + ℓ'')` pointwise), `hasDerivAt_iteratedDeriv_two_reconstructionL1_atlas`,
  **`iteratedDeriv_three_reconstructionL1_atlas`** (`p'''(s) = [q_s H₃]` in `L¹` on `(0,1)`, via the principle),
  `integral_atlasThird` / `integral_stat_mul_atlasThird` (zero mass, zero feature moments, from `invisible_tower` k = 3),
  **`atlasThird_eq_normalProj`** / **`iteratedDeriv_three_reconstructionL1_atlas_normal`** (`p''' = [q_s N_s H₃]`),
  `atlasRho` (the bending score `r_s = ⟨β'_s, S − M_s⟩`, `atlasScoreD_eq : ℓ' = −c − r`, `atlasRho_eq_responseScore`),
  `atlasCubicRho` (`ℓ³ − 3ℓr`), `atlasH3_decomp` (`H₃ = (ℓ³ − 3ℓr) + (tangent score + const)`), **`normalProj_atlasH3_eq`**,
  **`iteratedDeriv_three_reconstructionL1_atlas_cubic`** (`p'''(s) = [q_s N_{M_s}(ℓ_s³ − 3 ℓ_s r_s)]`),
  `integral_mul_iteratedDeriv_three_atlas`, **`iteratedDeriv_three_obsResponse_atlas`** (the third derivative of every observable
  response along the atlas is `E_{Q_s}[N_s F · (ℓ³ − 3ℓr)]`).
- `QuantitativeJets.lean` (NOT mirrored; round-66 rank 1 pre-theorem, explicit `L¹` jet bounds): `le_sq_div_of_coercive`
  (`λb ≤ a ≤ √b K ⇒ a ≤ K²/λ`), `dotJ_self_nonneg`, `abs_dotJ_le_sqrt_mul` (Cauchy–Schwarz), `lawCov_dirLoss_self_eq_neg_dotJ`
  (`Var_θ⟨v,S⟩ = −⟨v, Dm(θ)v⟩`), `norm_toL1_famDens_mul` (`‖[q_M g]‖₁ = E_{Q_M}|g|`), **`integral_abs_normalProj_le_sqrt`**
  (`E|N g| ≤ √(E g²)`, Cauchy–Schwarz + tangent Pythagoras); with `λ|v|² ≤ Var_{Q_s}⟨v,S⟩` on `𝕍`, `|S − M_s| ≤ L`, `|M − m₀| ≤ D`:
  `chartDerivEquiv_atlasVel`, `atlasCurv_eq_lawCov`, `lam_mul_dotJ_atlasVel_le`, `atlasCurv_le_sqrt_mul`, **`atlasCurv_le`**
  (`c_s ≤ D²/λ`), `dotJ_atlasVel_self_le` (`|β|² ≤ D²/λ²`), `atlasScore_eq_dotJ`, **`abs_atlasScore_le`** (`|ℓ_s| ≤ DL/λ`),
  `integral_atlasScore_sq`, `integral_atlasScore_sq_sq_le`, **`norm_iteratedDeriv_one_atlas_le`** (`‖p'‖₁ ≤ D/√λ`),
  **`norm_iteratedDeriv_two_atlas_le`** (`‖p''‖₁ ≤ LD²/λ^{3/2}`), `integral_atlasRho_sq_eq_lawCov`, `chartDerivEquiv_atlasVelD`
  (`Dm(θ_s)β' = −Cov(S, ℓ²)`), `dotJ_respCov_atlasScore_sq`, `abs_dotJ_respCov_atlasScore_sq_le`, `sqrt_dotJ_respCov_atlasScore_sq_le`
  (`|Cov(S,ℓ²)| ≤ Lc`), **`integral_atlasRho_sq_le`** (`E r² ≤ L²c²/λ`), **`norm_iteratedDeriv_three_atlas_le`**
  (`‖p'''‖₁ ≤ 4L²D³/λ^{5/2}`).
- `CubicRemainder.lean` (NOT mirrored): **`norm_L1_le_of_forall_integral_mul_le`** (norm duality via the sign observable),
  `norm_iteratedDeriv_three_atlas_le_uniform`, `contDiffOn_obsL1_atlas`, **`reconstructionL1_cubic_remainder`**
  (`‖p(s) − p(0) − s p'(0) − ½s² p''(0)‖₁ ≤ (4L²D³/λ^{5/2}) s³/6` on `[0,1]`: pair with `|F| ≤ 1`, real Lagrange remainder of
  `t ↦ E_{Q_{M_t}}F`, third jet bound, dualise — the sharp `1/3!` constant, not Mathlib's Banach `1/n!`).
- `AnalyticTilt.lean` (NOT mirrored; round-67 rank 1, step 1 of the analytic atlas): `featureBall J B` (compact ball, instance
  `compactSpace_featureBall`), `featureLin`/**`featureCLM`** (`θ ↦ (z ↦ −⟨θ,z⟩) ∈ C(K,ℝ)`), **`exp_apply_featureBall`** (the
  Banach-algebra exponential of `C(K,ℝ)` evaluates pointwise, via `NormedSpace.map_exp` on the evaluation ring hom), `featPt`
  (`S(x) ∈ K`), `measurable_featPt`, `integrable_pullback`, `pullbackLin`/**`pullbackCLM`** (`u ↦ [g (u ∘ S)] : C(K,ℝ) →L L¹`),
  **`weightL1_eq_pullback_exp`** (`[g e^{−⟨θ,S⟩}] = T_g(exp_A(featureCLM θ))`), **`analyticAt_weightL1`** /
  **`contDiff_omega_weightL1`** (the tilt map is real-analytic), `famNum_eq_integralCLM_weightL1`, **`analyticAt_famNum`**,
  `contDiff_omega_famNum`, **`contDiff_omega_famZ`**.
- `AnalyticChart.lean` (NOT mirrored; round-67 rank 1, THE ANALYTIC RESPONSE ATLAS): `contDiff_omega_famMean`,
  `contDiff_omega_meanMap`, `contDiff_omega_meanMapDeriv` (`fderiv_right le_top` at grade ω), `contDiff_omega_chartV`,
  `contDiff_omega_chartDeriv`, `contDiff_omega_chartDerivEquiv_symm` (`contDiffAt_map_inverse (n := ω)`),
  **`contDiffOn_omega_chartVInv`** (grade-ω `ContDiffAt.to_localInverse` at each point, the local inverse identified with
  `chartVInv` through `chartVInv ∘ chartV = id` on `eventually_right_inverse`), **`contDiffOn_omega_responseTheta_add`** /
  `isOpen_interior_displacements` / **`analyticOnNhd_responseTheta_add`** (`z ↦ θ(m₀+z)` analytic on the open interior
  displacements), **`contDiff_omega_densL1`** (`θ ↦ [q_θ]` analytic into `L¹`), **`contDiffOn_omega_reconstructionL1_add`** /
  **`analyticOnNhd_reconstructionL1_add`** / `analyticAt_reconstructionL1_add` (`z ↦ [q_{M+z}]` real-analytic on `addDomain`),
  `contDiffOn_omega_atlasTheta`, `contDiffOn_omega_reconstructionL1_atlas`, **`analyticAt_reconstructionL1_atlas`** (the atlas
  curve is real-analytic on the interior atlas domain), **`analyticAt_obsResponse_atlas`** (every bounded-observable response
  `s ↦ E_{Q_{M_s}}F` is real-analytic).
- `PointwiseJets.lean` (NOT mirrored; round-67 rank 4, structural Bell tower): `contDiffOn_iteratedDeriv_of_isOpen`,
  `hasDerivAt_iteratedDeriv_of_contDiffOn` (iterated derivatives of a `C^∞` map on an open set), `contDiff_famDens_apply`,
  `contDiffOn_famDens_atlas` (`s ↦ q_{M_s}(x)` is `C^∞` on the interior atlas domain), **`coeFn_iteratedDeriv_reconstructionL1_atlas`**
  (`p^{(k)}(s) = [x ↦ ∂_s^k q_{M_s}(x)]` for EVERY `k` at every interior atlas point — the `L¹` jets are the pointwise jets, by
  induction through the `L¹`-pointwise principle), `integrable_iteratedDeriv_famDens_atlas`, `iteratedDeriv_reconstructionL1_atlas_eq_toL1`,
  `atlasJet` (`∂_s^k q_s`), `atlasBell` (`B_k = q_s⁻¹ ∂_s^k q_s`), `atlasJet_zero`, `atlasBell_zero`, `hasDerivAt_atlasJet`,
  **`integral_atlasJet`** / **`integral_stat_mul_atlasJet`** (pointwise jets of order `≥ 2` have zero mass and zero feature moments),
  `atlasBell_one` (`B_1 = ℓ_s`), **`atlasBell_succ`** (the Bell tower `B_{k+1} = ∂_s B_k + ℓ_s B_k` on `[0,1]`).
