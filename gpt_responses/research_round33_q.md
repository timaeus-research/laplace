# Research consult, round 33 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "core features of the change in posterior expectation values with the change in the data
distribution, mapping the space of responses across the data manifold, all the way from the featureless distribution of
maximal entropy to the actual data distribution, with maximum beauty and depth"). All formal, sorry-free, on `main`.
Setting as before: bounded features `R : ι → X → ℝ`, bounded `L₀`, positive prior `π·μ`, `t > 0`, feature nondegeneracy
`hnd`; `P_{t,a} ∝ e^{−t(L₀+⟨a,R⟩)}π`, `m(t,a) = ⟨R⟩`, `I_t` the dual potential on `range m = int(momentBody R)`.

## Landed since round 32 (your ranking: 1 loss surface + block Hessian, 2 annealing bridge, 3 N^⊥, 4 second-order
## response, 5 Cramér, 6 boundary, 7 wall band instance, 8 two-term wall law)

Item 1 — COMPLETE.
- `MultiConstrainedResponse`: covariance matrix `C` of constrained statistics, regression residual `Var(φ − ∑bₖR_{wₖ}) =
  Var φ − ∑ bₖ Cov(R_{wₖ}, φ)` for `Cb = c`, vanishing iff `φ` a.e. affine in the constraints, `C` invertible under `hnd` +
  linear independence; path form: velocity `v + ∑γₖwₖ`, locally constant constraints ⇒ `γ = −b` and
  `d/ds⟨φ⟩ = −t(Cov(φ,R_v) − ∑bₖCov(φ,R_{wₖ}))` for every bounded `φ`.
- `SliceChart`: in the joint natural coordinates `θ = (t, β)`, `sliceMap θ = (θ_none, ⟨R⟩_θ)` is strictly differentiable,
  its derivative injective under FEATURE nondegeneracy only (kernel vector has zero temperature component, then
  `Var(R_{u_some}) = 0`), injective on `{t > 0}` by the slice bijection; partial inverse strictly differentiable
  (`to_local_left_inverse`); `tempPath M t` differentiable with unit temperature velocity; identified with the `a`-chart.
- `LossSurface`: `∂_t⟨φ⟩|_M = −(Cov(φ,L₀) − ∑bₖCov(φ,Rₖ))`, `Cb = Cov(R,L₀)`; `∂_t h = −Var(L₀ − ∑bₖRₖ) ≤ 0`, `h` antitone
  in `t`; `D_M⟨φ⟩[d] = ∑bₖdₖ` (regression coefficients).
- `ReducedPotential`: `∂_tA_t(a) = −⟨L_a⟩`; envelope `∂_tJ(t,M) = h(t,M)` (`J = I_t`); `∂_t(J + A_t(0)) = h − ⟨L₀⟩_{t,0}`;
  `C (D²I d) = d`; mixed partial `∂_tβ = −b`. Block Hessian `[[−σ², bᵀ],[b, C⁻¹]]` assembled.

Item 2 — COMPLETE.
- `AnnealingRay` (fixed data, `t ∈ ℝ` through the prior at `0`): `d/dt⟨φ⟩ = −Cov(φ, L_a)`; `E' = −Var(L₀)`, `E` antitone
  on ℝ; `∫₀ᵀ Var_u = E(0) − E(T)`; `KL(P_T‖π̄) = ∫₀ᵀ u Var_u ≤ T(E(0) − E(T))`; `(⟨φ⟩_T − ⟨φ⟩_0)² ≤ (∫₀ᵀ Var φ)(E(0) − E(T))`.
- `DataMixture` (the data manifold): `L_ν = ∫ℓ(·,z)dν(z)` for bounded `ℓ`, probability `ν`; along `ν_s = (1−s)ν₀ + sν₁`,
  `L_{ν_s} = L_{ν₀} + s(L_{ν₁} − L_{ν₀})` (affine); `d/ds⟨φ⟩ = −t Cov(φ, L_{ν₁} − L_{ν₀})`; both KL segment identities
  between the posteriors of `ν₀, ν₁` (via the `ι = Unit` affine family).

Item 4 — COMPLETE (`ThirdCumulant`): `κ₃`; if all bounded expectations move by `−c Cov(·, D)` then all covariances move
by `−c κ₃(·,·,D)`; `d/ds Cov_{a+sv} = −t κ₃(·,·,R_v)`; `D²m[u,v] = t² κ₃(R,R_u,R_v)`; `∂_w G(u,v) = −t³ κ₃(R_u,R_v,R_w)`
(Amari–Chentsov tensor); `d/dt Cov_{t,a} = −κ₃(·,·,L_a)`.

Earlier this session: `ConstrainedResponse` (single constraint Schur), `FeaturelessPoint` (`0 < KL(P_b‖P_a)` for `a ≠ b`;
`I(m 0) = −A(0)`; `I(y) − I(m 0) = KL(P_{θ(y)}‖P_0)`; prior response = unique minimiser of `I`).

Not done: (3) `N^⊥`, (5) Cramér, (6) boundary theory, (7) wall band instance, (8) two-term wall law.

## Questions

1. **Audit** the statements above (as in rounds 30–32): anything wrong, mis-normalised, or hypotheses too strong?
   In particular: (a) `sliceMapDeriv_injective` under feature nondegeneracy only — correct? (b) the annealing identities
   hold for ALL real `t` (bounded `L₀`), including negative temperatures — any reason to restrict? (c) the data-mixture
   bridge assumes `|ℓ| ≤ M` uniformly and probability measures — is there a cleaner standing hypothesis you would use?
2. **Re-rank what remains** for the PI's goal. Candidates: (i) `N^⊥` (what is the crispest formal statement worth
   landing: descended injective mean map on the quotient? relative interior of the moment body? invariance of the geometry
   under feature reparametrisation `R ↦ AR + c`?); (ii) Cramér / large deviations of the empirical response under
   `P_{t,0}` with rate `I_t + A_t(0)` (bounded statistics, finite `ι`); (iii) boundary theory: the closure of `range m`,
   boundary values of `I`, `I → +∞`?? at the boundary (is `I_t + A_t(0)` coercive/ blowing up at `∂ momentBody`?), rays to
   the boundary and the ess-inf endpoint in several dimensions; (iv) thermodynamic length of the annealing ray
   `∫₀ᵀ √Var_u(L₀) du` and of data segments, and a "geodesic" statement (is the mean segment / natural segment length-
   minimising for the response metric? no—but what IS true?); (v) the Amari–Chentsov tensor: does the family's
   `e`-flatness in `a` and `m`-flatness in `y` give a clean formal statement the seabed lacks (e.g. the mixed-parametrisation
   Pythagoras: for `a`-segment ⟂ `m`-segment)? (vi) the "second-order loss surface": `∂_M² h`, `∂_t∂_M h` in terms of
   `κ₃` and the Schur complement; (vii) an explicit global theorem tying the two axes: the map `(t, ν) ↦ P_{t,ν}` from
   `(0,∞) × {data distributions}` with total response `d⟨φ⟩ = −Cov(φ, L_ν) dt − t Cov(φ, dL_ν)`, the exactness/integrability
   of this 1-form (mixed partials), and the resulting potential (`log Z` as the potential whose exterior derivative is
   `−⟨L⟩ dt − t⟨dL⟩`); (viii) anything else you regard as core.
3. For your top pick, give the cleanest Lean-friendly formulation and the main pitfall.
