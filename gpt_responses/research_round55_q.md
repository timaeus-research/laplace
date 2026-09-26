# Round 55: the second-order geometry is complete — what is the missing heart? (germbij / laplace)

Same programme as rounds 52–54 (bounded features `S`, featureless posterior `ν`, family `P_θ = e^{−⟨θ,S⟩}ν/Z`,
reconstruction `Π(M) = P_{θ(M)}`, direction subspace `𝕍`, atlas path `M_s = (1−s)m₀ + sM`, curvature `κ`,
bridge `D_s`, lift `D↑`, `KL(D‖ν) = 𝓘 + R + L`). User direction unchanged and verbatim: "make sure we are
tackling core features of the change in posterior expectation values with the change in the data distribution
that allow us to map the space of responses across the data manifold (ideally, all the way from the featureless
distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum
beauty and depth?"

## Landed since round 54 (all sorry-free, on `main`)

- `BoundaryBlowup` (rank 2): `κ(s) ≥ δ/(R(1−s))` from a supporting normal at a finite-rate boundary response,
  `κ → ∞`, `∫₀¹ κ = ∞`, `−⟨θ_s, Δ⟩ ≥ (δ/R) log(1/(1−s))`.
- `NormalGeometry` (rank 3, stage 1): response scores `ℓ_{M,u} = ⟨R u, M − S⟩` with `R = (Dm(θ(M))|_𝕍)⁻¹ = −Σ_M⁻¹`;
  `E_Q ℓ_{M,u} = 0`; `Cov_Q(S_j, ℓ_{M,u}) = u_j`; **differential duality** `E_Q[ℓ_{M,u}ℓ_{M,z}] = ⟨Σ_M⁻¹u, z⟩`
  (positive definite on `𝕍`); regression projection `B_M f = ℓ_{M, Cov_Q(S,f)}` (fixes tangent scores), normal
  projection `N_M f = f − E_Q f − B_M f` (kills tangent scores, zero mass, zero feature moments);
  **density-acceleration theorem** on the atlas: `q_s''/q_s = N_{M_s}(ℓ_s²)`.
- `CovarianceFrechet` (rank 1, stage 1): Fréchet derivatives in natural coordinates of `E_{P_θ}φ`,
  `Cov_{P_θ}(f,g)`, `p_θ(x)`; the third-cumulant operator `T_θ : 𝕍 →L (𝕍 →L 𝕍)` as the Fréchet derivative of
  `Σ_θ|_𝕍` (basis assembly, identified by uniqueness of derivatives); `z ↦ θ(M+z)` strictly differentiable with
  derivative `R`; `D_M R_M[u] = −R T_{θ(M)}(Ru) R`; `T_{θ(M)}(Ru,Rw) = Cov_Q(S, ℓ_u ℓ_w)`;
  `D_M ℓ_{M,w}(x)[u] = −E_Q[ℓ_uℓ_w] − B_M(ℓ_uℓ_w)(x)`; **the polarised Hessian**
  `D²q_M[u,w](x) = q_M(x) N_M(ℓ_{M,u}ℓ_{M,w})(x)` (as: the derivative field `z ↦ q_{M+z}ℓ_{M+z,w}` is
  differentiable at 0 with that derivative).
- `ObservableHessian` (rank 1, stage 2): `D_M E_{Π(M)}φ[u] = Cov_Q(φ, ℓ_{M,u})` and
  `D²_M E_{Π(M)}φ[u,w] = E_Q[φ · N_M(ℓ_{M,u}ℓ_{M,w})]` — only the normal part of `φ` responds at second order.

Not done: rank 3 stage 2 (Fisher–Rao second fundamental form: with `r_s = 2√q_s` in `L²(ν)`, the acceleration
splits as `r'' = (r/4)N(ℓ²) − (κ/4)r − (r/4)B(ℓ²)`, radial/tangential/normal, mutually orthogonal — I intend to
land this next as `FisherRaoCurvature`), the §7 structure theorem packaging, rank 4 (general conditional
variational), rank 5 (Fisher–Rao great circle), rank 6 (unbounded bridge split).

## Questions

1. With the second-order geometry of the response map now in hand (global chart, differential duality, normal
   projection, polarised Hessian, observable second order, boundary blow-up), what is the **missing heart** of the
   user's programme? Re-rank by depth × Lean feasibility. Candidates I see:
   (a) **Second-order Taylor expansion of the response map with remainder**: `E_{Π(M+z)}φ = E_Qφ + Cov_Q(φ,ℓ_z)
       + ½E_Q[φ N_M(ℓ_z²)] + o(‖z‖²)` (and the same for `q_{M+z}` in `L¹(ν)`); what is the cleanest Mathlib route
       from "the derivative field is differentiable at 0" + strict differentiability of `θ(M+·)` (Mathlib has
       `HasFDerivAt` of `fderiv` ⇒ second-order Taylor? which lemma)?
   (b) **The data manifold as a fibre bundle over responses**: the map `Π̂ : D ↦ Π(M_D)` (I-projection onto the
       response fibre), the splitting of a score `g` at `Q` into horizontal `B_M g` and vertical `g − E g − B_M g`
       (we have `NestedProjections`, `RegressionProjection`); is there a *connection* statement (horizontal lift of
       a response direction `u` is `ℓ_{M,u}`; curvature of the horizontal distribution = ?) that is both deep and
       formalisable? What does the third cumulant `T` mean in this picture (torsion-free? Amari's e/m-connections:
       `T_{θ}` is the Amari–Chentsov tensor restricted to `𝕍` — is the cleanest statement "the response chart is
       the m-flat (mixture) affine coordinate and `θ` the e-flat one, dually flat with respect to the Fisher metric
       `⟨Σ_M⁻¹u,z⟩`, and `KL(Π(M)‖Π(M')) = 𝓘(M) − 𝓘(M') + ⟨θ(M'), M−M'⟩` is the canonical divergence" — we have the
       Bregman identity (EmpiricalProjection); is dual flatness worth stating formally, and how?
   (c) **Fibre-transverse second order**: for a law `D` in the fibre over `M` (same response), the second-order
       expansion of `KL(D‖Π(M+z))` in `z` (we have first order via the Pythagoras/Bregman identities): is
       `∂²_z KL(D‖Π(M+z))|₀[u,u] = ⟨Σ_M⁻¹u,u⟩ + E_D[N_M(ℓ_u²)]`-type formula true (the fibre sees the normal part
       of the squared score through `D`)? That would be the "response Hessian seen from a data law".
   (d) **Global control**: uniform second-order bounds on compact subsets of `ri K` (continuity of `M ↦ Σ_M⁻¹`
       we have; is the Hessian norm locally bounded — needed for (a) with uniform remainders).
   (e) the Fisher–Rao second fundamental form / great circle (ranks 3b, 5), the §7 packaging.
   (f) anything else you consider the missing heart.
2. For your top-ranked item give the precise statement in the seabed's terms, a lemma-level proof sketch, and a
   line estimate (Lean 4.33, Mathlib Sep 2026; we have `hasStrictFDerivAt_responseTheta_add`,
   `hasFDerivAt_famDens_responseScore`, `hasFDerivAt_integral_responseScore`, `thirdOp`, `normalProj`).
3. Sanity-check the claim "only the normal part of `φ` responds at second order" and the formula in (c).
