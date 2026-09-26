# Research consult, round 51: after the quadratic split — what completes the map of responses?

Same Lean seabed as round 50 (your answer there is on file). Since then ALL of the following are formalised
(sorry-free):

* Pythagoras against an arbitrary interior target: `KL(D‖Π(N)) = L + R + KL(Π(M_D)‖Π(N))`, pathwise along the bridge.
* Fisher energies: `KL(P_θ‖ν) = −⟨θ,m(θ)⟩ − Λ(−θ)`, `KL(ν‖P_θ) = ⟨θ,m₀⟩ + Λ(−θ)`, symmetrised = `−⟨θ, m(θ) − m₀⟩`;
  `∫₀¹ Var_{P_{sθ}}⟨θ,S⟩ ds = KL(P_θ‖ν) + KL(ν‖P_θ)` (exponential path); for the atlas path with interior endpoint:
  endpoint slope continuity `−⟨θ_s,Δ⟩ → −⟨θ,Δ⟩` (from the two Bregman identities + differentiability of 𝓘 at the
  endpoint, no inverse-chart continuity), `κ ∈ L¹(0,1)`, `∫₀¹ κ = −⟨θ,Δ⟩`, `KL(ν‖Π(M)) = ∫₀¹ s κ(s) ds`
  (companion of `𝓘(M) = ∫₀¹ (1−s) κ(s) ds`), equal energies of the two paths.
* Observable defect: `E_{Π(N)} φ = E_{Π(N)} E_ν[φ|σ(S)]`; exact split
  `E_{D_s}φ − E_{Π(M_s)}φ = s E_D(φ−ψ) + (E_{D_s}ψ − E_{Π(M_s)}ψ)`; `Δ'_φ(s) = E_Dφ − E_νφ + Cov_{Π(M_s)}(φ,⟨v_s,S⟩)`;
  at `s = 0`: `Δ'_φ(0) = E_D(φ − ⟨a,S⟩) − E_ν(φ − ⟨a,S⟩)` with `a ∈ 𝕍` the regression coefficient.
* L² spine: `A = span{1,S_j} ⊆ L²(σ(S)) ⊆ L²(Q)`; three-way Pythagoras `‖h‖² = ‖Bh‖² + ‖Ch−Bh‖² + ‖h−Ch‖²`
  (`condExpL2`); `B φ = Eφ + ⟨a, S − M⟩` under the normal equations; `‖Bφ − Eφ‖² = ⟨a, Cov(S,φ)⟩`; on the atlas path
  `a ∈ 𝕍` exists.
* Quadratic split along bounded tilts `ν_t ∝ e^{tf}ν`, `h = f − E_ν f`: `KL(ν_t‖ν)/t² → ‖h‖²/2` (L'Hôpital),
  `M_t' (0) = Cov_ν(S,f)`, `𝓘(M_t)/t² → ‖B₀h‖²/2` (Fenchel/Bregman sandwich around `P_{−ta}`, `θ(M_t) = O(t)` by local
  Lipschitz of the inverse chart), hence `KL(ν_t‖Π(M_t))/t² → ‖h − B₀h‖²/2`.
* Empirical consistency `KL(Π(M̂_n)‖Π(M_D)) → 0` a.s.; interior Bregman identity; conditional-expectation form of the
  lifted density; joint convexity; `HalfspaceChernoff` (Chernoff-type bounds for the empirical response).

Not yet: separate quadratic expansions of `L` and `R` (need `E_ν[e^{tf}/Z | σ(S)] = 1 + tCh + O(t²)`); the mixed
response Hessian `D²_M E_{Π(M)}φ[u,z] = E[r_φ ℓ_u ℓ_z]` (only the atlas-directional `F''` exists); the `L¹`-valued
derivative of the reconstruction density; the conditional variational formula; the Fisher metric as a
`RCLike`/inner-product structure on `𝕍`; a large-deviation reading of `𝓘`.

## Questions

1. The user's programme is "map the space of responses across the data manifold from the featureless posterior to
   the data". With the above in place, what are the 5–7 most valuable remaining theorems, ranked by depth × feasibility
   (each ≤ 400 Lean lines given the infrastructure), with exact statements and proof sketches? Candidates I see:
   (a) Cramér/large-deviation reading: under `ν`, `P(M̂_n ∈ A) ≈ exp(−n inf_A 𝓘)`; at least the sharp upper bound
       `limsup (1/n) log P_ν(M̂_n ∈ F) ≤ −inf_F 𝓘` for closed `F` (via Chernoff over finitely many halfspaces — does the
       seabed's halfspace bound suffice for compact `F`?) and the lower bound for open sets via the tilted measure and
       the SLLN under `P_θ` (which we have: `ae_tendsto_sampleResponse` for any data law). This would identify the
       information geometry of the atlas with the large-deviation geometry of empirical responses under the
       featureless posterior. Is this the right "beautiful" endpoint, and what is the cheapest rigorous route?
   (b) the separate `L`/`R` quadratic expansions (conditional-expectation of the tilt density);
   (c) the mixed Hessian / response Jacobian in `L¹`;
   (d) a coarse-graining tower: two statistics `S ⊆ S'` (σ(S) ⊆ σ(S')), nested atlases, the information split refined
       into visible-by-S, visible-by-S'-not-S, invisible; monotonicity of `𝓘_S ≤ 𝓘_{S'}` and of the residuals;
   (e) the bridge in the *full* simplex as an m-geodesic: its Fisher energy `∫₀¹ Var_{D_s}(dD/dν − 1)/(1−s+s dD/dν)…`
       vs `KL` — is there a clean identity like the ones for the two straight paths?
   (f) response-map curvature: the Hessian of `M ↦ E_{Π(M)}φ` in atlas coordinates via polarisation of the existing
       directional `F''`, given `C²` regularity — what is the cheapest way to get the Fréchet Hessian?
   (g) anything I am missing that would make the picture *complete*.
2. For your top-ranked item give the precise Lean-flavoured statement, the Mathlib lemmas to use (e.g. for LDP:
   `ProbabilityTheory` has `IdentDistrib`, `iIndepFun`, `strong_law_ae_real`; is there any Cramér theorem in Mathlib
   as of 2026? if not, what is the minimal self-contained route for bounded statistics on a finite-dimensional
   response space?), and the pitfalls.
3. Which of the items should be dropped or deferred, and why?
