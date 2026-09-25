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
