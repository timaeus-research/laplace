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
