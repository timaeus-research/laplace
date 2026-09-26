# Round 54: after the third-order geometry, the global chart and the four paths (germbij / laplace)

Same programme as rounds 52–53 (bounded features `S`, featureless posterior `ν`, family `P_θ = e^{−⟨θ,S⟩}ν/Z`,
reconstruction `Π(M) = P_{θ(M)}`, atlas path `M_s = (1−s)m₀ + sM`, curvature `κ`, bridge `D_s`, lift `D↑`,
`KL(D‖ν) = 𝓘 + R + L`). User direction unchanged: map the responses across the data manifold from the
max-entropy posterior to the data law, with maximum beauty and depth.

## Landed since round 53 (all sorry-free, on `main`)

- `AtlasSkewness` (rank 1): `κ'(s) = T_{Q_s}(f_s,f_s,f_s) = −E_{Q_s} ℓ_s³` via the exact increment
  `κ(t) − κ(s) = Cov_{Q_s}(f_t,f_s) − Cov_{Q_t}(f_t,f_s)` (no inverse-covariance differentiation), and
  `KL(Π(M)‖ν) − KL(ν‖Π(M)) = ∫₀¹ s(1−s) E_{Q_s} ℓ_s³ ds` (IBP with `deriv κ` integrable via `measurable_deriv`).
- `ExponentialPath` (rank 6): `E_s = ν.tilted(s log d)`; `∫₀¹ k_d = ∫₀¹ Var_{E_s}(log d) = KL(D‖ν)+KL(ν‖D)`;
  the same for `ν → D↑`; `KL(D↑‖ν)+KL(ν‖D↑) ≤ KL(D‖ν)+KL(ν‖D)` (conditioning contracts the symmetrised
  divergence, from `k_a ≤ k_d`); length ≤ √energy for every path on `(0,1)`.
- `GlobalChart` (rank 3, packaging): `relintChart : 𝕍 ≃ₜ ri K` (gauge-fixed mean map is a homeomorphism onto the
  relative interior), strict derivatives both ways, inverse = natural coordinate of `Π`, `Π(M)` has response `M`
  and is the unique entropy minimiser of its fibre (`global_response_chart`).
- `AtlasVelocityDerivative` + `AtlasHessian` (rank 2, on the atlas diagonal): `Σ_s` is differentiable along the
  atlas with derivative the third-cumulant operator `(D_s v)_j = T_{Q_s}(S_j,⟨v,S⟩,f_s)` (basis assembly +
  closedness of `𝕍`), `β_s' = −Σ_s⁻¹ D_s β_s` (`hasFDerivAt_ringInverse`), `d/ds q_s = q_s ℓ_s`,
  `d²/ds² q_s = q_s(ℓ_s² − κ(s) + ⟨w_s, S − M_s⟩)` with `w_s = Σ_s⁻¹ D_s β_s` and
  `(D_s β_s)_j = E_{Q_s}[(S_j − M_j) ℓ_s²]`; `∫ q_s'' dν = 0`, `∫ S_j q_s'' dν = 0`.
  The polarised Fréchet Hessian `D²q_M[u,z]` in response coordinates is NOT done (it needs the second Fréchet
  derivative of the inverse chart); the path version is the diagonal `u = z = Δ`.

Earlier: everything listed in the round-53 query (curvature split, conditional Fisher loss, Bregman geometry,
L¹ derivatives, retraction theorem, length–energy, conditional variational formula, etc.).

## Questions

1. Given the user's direction, re-rank the remaining targets by depth × Lean feasibility. Candidates:
   (a) the polarised mixed Hessian `D²q_M[u,z]` and its corollary, the observable-defect second-order term
       `Δ_f''(0) = E_Q[r_{f,M}(h̄² − (B_M h)²)]`; is there a route through the *path* Hessian (polarisation over
       directions `u, z` by considering the two-parameter family `M + su + tz`, or by the identity
       `D²q[u,z] = ½(D²q[u+z,u+z] − D²q[u,u] − D²q[z,z])`, which only needs the diagonal along straight paths
       through `M` in every direction — we have the diagonal for the atlas path from `m₀`, but a straight path
       from an arbitrary interior `M₀` in direction `v` is the same machinery with `m₀` replaced by `M₀`)?
   (b) unbounded densities for the bridge curvature split (interior-time identities, nonnegative kernels);
   (c) the conditional variational formula for general densities (sup; clipping of `log(d/a)`);
   (d) a genuine second-fundamental-form statement: with the Fisher metric on the full simplex (scores `h` with
       `∫h² dQ`), the tangent space of the family at `Q_M` is `{ℓ_{M,u}}`, its normal space in `L²(Q_M)` is the
       orthogonal complement, and the second derivative of the density along the atlas has a normal component
       `(I − P₀ − B_M)(ℓ²)`: what is the cleanest formal statement and does it need the polarised Hessian?
   (e) the Fisher–Rao great circle as the common length lower bound (`2 arccos ∫√d dν`);
   (f) the boundary: behaviour of `κ`, `β_s`, `q_s` as `M_s → ∂K` (we have `FixedNormalLimit`, `NormalCone`,
       `BoundaryEscape`, `EndpointTail`); is there a deep statement left (e.g. `κ(s) → ∞` or the rate of blow-up
       of `θ(M_s)` as `M → face`)?
   (g) anything else you consider the missing heart now that the second-order geometry is in place.
2. For your top-ranked item give the precise statement in the seabed's terms, a lemma-level proof sketch, and
   a line estimate.
3. Which existing statements would you strengthen or repackage (e.g. into a single "structure theorem for the
   response map") to make the programme read as one theorem?
