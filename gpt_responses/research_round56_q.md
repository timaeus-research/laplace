# Round 56: finite response landed — what is left for maximum beauty and depth? (germbij / laplace)

Same programme as rounds 52–55 (bounded features `S`, featureless posterior `ν`, family `P_θ = e^{−⟨θ,S⟩}ν/Z`,
reconstruction `Π(M) = P_{θ(M)}`, direction subspace `𝕍`, atlas `M_s = m₀ + sΔ`, response scores
`ℓ_{M,u} = ⟨R u, M − S⟩`, normal projection `N_M`, regression `B_M`). User direction unchanged: map the responses
across the data manifold from the featureless posterior to the data law, with maximum beauty and depth.

## Landed since round 55 (all sorry-free, on `main`; slop paragraphs pushed)

- `FisherRaoCurvature`: `r_s = 2√q_s` lies on the sphere of radius 2 in `L²(ν)`, `∫(r')² = κ`,
  `r'' = (r/4)N(ℓ²) − (κ/4)r − (r/4)B(ℓ²)`, the three pieces mutually orthogonal (normal = second fundamental form,
  radial = sphere curvature, tangential ≠ 0 unless `B(ℓ²) = 0`).
- `FiniteResponse` (your rank 1, integrated form): `d/ds E_{Q_s}φ = E_{Q_s}[φℓ_s]`, `d²/ds² = E_{Q_s}[φ N(ℓ_s²)]`
  (finite-combination trick, no dominated differentiation), bound on `s ↦ Σ_s⁻¹` on `[0,1]` ⇒ integrability of the
  second-derivative field, Taylor with integral remainder, fibre identity `E_D[N_Mφ] = E_Dφ − E_{Π(M)}φ`, and THE
  ACCOUNTING IDENTITY `E_Dφ − E_νφ = E_ν[φℓ_0] + ∫₀¹(1−s)E_{Q_s}[φN_{M_s}(ℓ_s²)]ds + E_D[N_Mφ]` (interior `M`).
- `FibreHessian` (your "land immediately" item, corrected as you said): `ri K` is open in `𝕍`
  (`HasStrictFDerivAt.map_nhds_eq_of_equiv` on the chart), `KL(D‖Π(M+z)) = KL(D‖Π(M)) + 𝓘(M) − 𝓘(M+z) − ⟨θ(M+z),z⟩`,
  derivative field `−⟨R_{M+z}w, z⟩`, critical at `0`, Hessian `= E_Q[ℓ_uℓ_w]` — fibre-independent.
- `ResponseTaylor` (your rank 1, Peano form): generic lemma (differentiable derivative field ⇒ `o(‖z‖²)` via the mean
  value inequality on the segment), `responseDerivField` (a functional for every `z`), differentiability of the
  response at every interior point, Fréchet derivative of the field = Hessian `E_Q[φN(ℓ_uℓ_w)]` (basis assembly +
  uniqueness), `E_{Π(M+z)}φ = E_Qφ + E_Q[φℓ_z] + ½E_Q[φN(ℓ_z²)] + o(‖z‖²)`.
- `DualFlat` (your rank 4): `∇𝓘 = −θ`, `D²𝓘 = G = E_Q[ℓ_uℓ_w]`, `DG[v](u,w) = −C(u,v,w)` with `C = E_Q[ℓ_uℓ_vℓ_w]`
  totally symmetric (via `B_M` = L²(Q)-orthogonal projection onto tangent scores), Bregman canonical divergence;
  packaged as `dual_flat_structure`.

Not done: §7 structure-theorem packaging (doing now), `L¹` density Peano, compact-uniform remainders, the boundary
endpoint `t ↑ 1` of the accounting identity, general (unbounded) densities.

## Questions

1. Sanity-check three claims I put in the note: (a) in the square-root embedding the atlas is not a geodesic of the
   family unless `B_{M_s}(ℓ_s²) = 0` (the tangential component of `r''`); (b) the Levi-Civita connection of the
   Fisher form in response coordinates has Christoffel symbols `Γ^{LC}(u,w) = −½ Cov_Q(S, ℓ_uℓ_w)`, with
   `Γ^{(m)} = 0`, `Γ^{(e)}(u,w) = −Cov_Q(S, ℓ_uℓ_w)` (your round-55 remark — confirm signs/normalisation given
   `R = −Σ⁻¹`); (c) "only the normal part of `φ` responds at second order" with your two qualifications.
2. What now is the deepest remaining statement about mapping responses across the data manifold that the seabed can
   reach? Candidates: (i) the `L¹` density Peano `‖q_{M+z} − q_M − q_Mℓ_z − ½q_MN(ℓ_z²)‖_{L¹} = o(‖z‖²)` (pointwise
   Hessian exists; needs an `L¹`-valued derivative field — is there a route avoiding the `Lp` API, e.g. via the
   generic Peano lemma applied to `z ↦ ∫ g q_{M+z}` uniformly over `‖g‖_∞ ≤ 1`, using the explicit remainder bound
   `abs_famDens_remainder_le` (`|p_{θ+η} − p_θ − p_θ(⟨η,m⟩ − ⟨η,S⟩)| ≤ 10K²‖η‖²p_θ`) twice?); (ii) the boundary
   endpoint: for `M` on the relative boundary with finite rate, does `∫₀¹(1−s)E_{Q_s}[φN(ℓ_s²)]ds` converge (we
   have `κ ≥ δ/(R(1−s))`, so `(1−s)κ` is bounded below by a constant — is the integrand `(1−s)E[φN(ℓ²)]`
   integrable at `s = 1`? is there a clean statement like `E_{Π(M)}φ − E_νφ = lim_{t↑1}[…]` with the limit existing
   by monotonicity/continuity of `s ↦ E_{Q_s}φ` up to `s = 1` (we have `BoundaryEscape`, `EndpointTail`)?);
   (iii) uniform control: continuity of `M ↦ H_{M,φ}` on compacts of `ri K`; (iv) a Wasserstein/transport or
   total-variation counterpart of the accounting identity; (v) the response of the *fibre information* `L`
   itself along the atlas; (vi) anything else that would make the note read as one theorem.
3. For your top item give the precise statement in the seabed's terms, a lemma-level proof sketch, and a line
   estimate (we have `hasFDerivAt_famDens_response`, `hasFDerivAt_famDens_responseScore`,
   `integral_abs_famDens_remainder_le`, `isBigO_famDens_remainder`, `hasStrictFDerivAt_responseTheta_add`,
   `exists_bound_ringInverse_atlas`, `eventually_add_mem_intrinsicInterior`).
