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
