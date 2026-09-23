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
  (10)–(11)). Numerics for `A = (2,2)`, `h = 0`, one untied coordinate `x'^1`: the ratio of
  `√t I(t)/log t` to the predicted `√π/2` is `1 + c/log t` at `t = 10³…10⁷`.

Astra's lemma 4 is therefore complete (both blocks), lemma 6 (`ChartCluster`) too. Remaining:
lemma 1 (normalised signed branch kernels with the explicit moving cutoff), lemma 2 (moving-unit
comparison), lemma 3 (certified moving-kernel limit through `RescaledData`), lemma 5 (LP/profile
compatibility), and the enrichment of `WallChartsData` with the phase data.
