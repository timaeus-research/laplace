# Research consult, round 41 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "core features of the change in posterior expectation values with the change in the data
distribution; map the space of responses across the data manifold, from the featureless distribution of maximal
entropy to the actual data distribution; maximum beauty and depth"). All formal, sorry-free, on `main`.
Conventions as before: `P_{t,a} ∝ exp(−t(L₀ + a·R)) π`, `V = Cov_{t,a}(R,R)`, `Q = P_{t,0}` the featureless member,
natural coordinates `θ = (t, ta)`, `S = (L₀,R)`, joint nondegeneracy `hjnd`, moment body `K` = closed convex hull
of the essential range of `R` (prior null sets), `int K = range m_t`.

## Landed since round 40 — your bundle A–E and items 2, 4
1. `JourneyEnergy`: `E_e = t²∫₀¹Var_{a(s)}(R_{Δa}) = −t Δa·Δm = E_m = Jeffreys`; `L_e², L_m² ≤ Jeffreys`.
2. `TemperatureCompatibility`: `∂_t² I_t(M) = ∂_t u_t(M) = −Var_{t,M}(H) < 0` (the first law was already landed).
3. `RateFunction` (A/B): `Λ(q) = log E_Q e^{q·R}`, `𝓘(M) = ⨆_q ofReal(q·M − Λ(q)) ∈ [0,∞]`;
   `𝓘(m_t(a)) = KL(P_{t,a}‖Q)` (score at `q = −tb` is the dual objective, maximal at `b = a`); on `int K` the rate is
   the convex `I_t + A_t(0)`; `𝓘 = ⊤` off `K` (Hahn–Banach separation + `Λ(λw) ≤ λ sup_K w·y`); lsc.
4. `CramerTheorem` (C/D): rate convex along segments with finite endpoints; radial interior approximation
   `(1−ε)M + ε m_t(0) ∈ int K`, along which the rate does not increase; **upper**: closed `F`, `c < 𝓘` on `F` ⇒
   eventually `Q^{⊗n}(R̄_n ∈ F) ≤ e^{−n(c−ε)}`; **lower**: open `G`, `𝓘(M) < c` for some `M ∈ G` ⇒ eventually
   `Q^{⊗n}(R̄_n ∈ G) ≥ e^{−nc}` (interior points are tilted means; boundary points by radial approximation).
5. `ExposedFace` (E): for any feature law `ν`, `u·R ≤ β` a.e., `F = {u·R = β}`, `p_F = ν(F) > 0`, `ν_F = ν(·|F)`:
   `𝓘 ≤ −log p_F + 𝓘_F` everywhere (`Λ ≥ log p_F + Λ_F`), and `𝓘 = −log p_F + 𝓘_F` on the hyperplane `{u·M = β}`
   (`Λ(q+λu) − λβ → log p_F + Λ_F(q)` by dominated convergence, `u·M = β`); specialised to `Q`.
Also: the note's overview theorem V was rewritten around the duality capstone and a seven-section dependency
catalogue was added (your consolidation request).

Not done: F (blow-up criterion), G (conditional convergence in total variation of the wall ray; the expectation form
`tendsto_priorExp_ray_face` and the KL cost `tendsto_mixKL_zero_face` were landed earlier), dual connections
(`a'' = (1/t)V⁻¹C(w,w)` along the m-journey), full-geometry stability, the a.e. interface of `WallRay`.

## Questions
1. **Audit** items 3–5. (a) In item 5 the face is defined by the sample-space event `{u·R = β}`; the identity holds
   for EVERY `M` on the hyperplane, including `M ∉ K_F` where `𝓘_F(M) = ⊤` — consistent? (b) The lower Cramér bound
   uses `M ∈ G` with `𝓘(M) < c` — is "`inf_G 𝓘 < c`" exactly equivalent (yes, by definition of inf), and is the
   eventual-exponential interface equivalent to the liminf/limsup statement with the convention `log 0 = −∞`?
   (c) Item 3's `⊤` off `K` uses the prior's essential range while `Q` is the featureless tilt — equivalent null
   sets under positive densities; anything to flag? (d) Are the constants/quantifiers in the radial step right
   (`ε ∈ (0,1]`, `M ∈ K`, endpoint `m_t(0)` with `𝓘 = 0`)?
2. **The blow-up criterion (F)** as a formal target: "`𝓘(M_n) → ⊤` whenever `M_n ∈ int K`, `dist(M_n, ∂K) → 0`, iff
   every proper exposed face has `Q`-mass zero". Which half is the clean first theorem, with what exact hypotheses
   (bounded features, nondegenerate; faces indexed by unit directions `u` with `β(u) = ess sup u·R`)? Sketch the
   Lean-friendly statement and the pitfalls (compactness of the unit sphere, uniformity, the null-face direction
   giving `𝓘 = ⊤` on the face via `Λ(λu) − λβ → −∞`?).
3. **Re-rank the rest** and propose anything of comparable depth I am missing: (i) F; (ii) G in total variation
   (we have `tendsto_priorExp_ray_face` for bounded observables — is TV convergence a short corollary via the sign
   observable, as in the seabed's `tendsto_mixKL_zero_face`?); (iii) dual connections through the cubic tensor
   (`Γ^{(m)} = −tV⁻¹C`, `a'' = (1/t)V⁻¹C(w,w)`; needs `d/ds V⁻¹` — `hasFDerivAt_ringInverse` route); (iv) full-geometry
   stability by instantiation; (v) the "conditional response chart": on a positive-mass face the conditional family
   `Q_F` tilted along the face is again an exponential family with its own chart — the wall as an exponential family
   (partly landed as `ProfileFamily`, `WallChart` in the singular setting) — is there a clean statement "the response
   atlas extends to the exposed faces by conditioning, with entry costs `−log p_F`" (a stratified atlas)? (vi) the
   entropy of the face law: `𝒮(Q_F) = 𝒮(Q) + log p_F`?? and the relative entropy of the wall limit; (vii) anything
   else. For the top pick give the theorem bundle with pitfalls, as before.
