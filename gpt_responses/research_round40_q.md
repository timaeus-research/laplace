# Research consult, round 40 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "core features of the change in posterior expectation values with the change in the data
distribution; map the space of responses across the data manifold, from the featureless distribution of maximal
entropy to the actual data distribution; maximum beauty and depth"). All formal, sorry-free, on `main`.
Conventions as before: `P_{t,a} ∝ exp(−t(L₀ + a·R)) π`, `V = featCov = Cov_{t,a}(R,R)`, natural coordinates
`θ = (t, ta)`, `S = (L₀,R)`, `G_θ = Cov_θ(S,S)`, `𝒮 = −KL(P_θ‖π̄)`, joint nondegeneracy `hjnd`.

## Landed since round 39 — the whole round-39 list
1. `ProfileGeometry` (your top pick A, B, F + entropy balance): `J(μ(θ)) + t u(θ) − I_t(m_t a) = KL(P_θ‖P_{t,a})`
   when θ and a share the response; `I_t(M) ≤ J + tu` with equality at the lift; exact Pythagoras
   `KL(P_θ‖P_{t,b}) = KL(P_θ‖P_{t,a}) + KL(P_{t,a}‖P_{t,b})`; `I_t(m a) + A_t(0) = KL(P_{t,a}‖P_{t,0})` and rate
   contraction; `∇_μ 𝒮 = θ` as a Fréchet derivative on the full mean chart and `d𝒮/ds = ⟨θ(μ(s)), μ'(s)⟩` along any
   differentiable full mean path. (D and E were already landed: `natForm_sliceInv_deriv`, `hasDerivAt_relEntropy_temp`.)
2. `SchurComplement` (C): blocks of the joint `featCov`; `Var(H) > 0` under `hjnd`;
   `d·G⁻¹d = d_R·V⁻¹d_R + (d₀ − b·d_R)²/Var(H)`; the slice metric is the minimal lift, attained at `d₀ = b·d_R`.
3. `ResponseStability` LOCALISED per your audit: ellipticity only along the lifted mean segment (mean side) / the
   natural segment (natural side); bi-Lipschitz takes both; global versions are wrappers.
4. `FluctuationResponse`: `Var(v·R̄_n) = v·V v/n = −v·Dm_t(a)v/(nt)` under `P_{t,a}^{⊗n}`.
5. `WallRay` (first wall theorem): along `a − (λ/t)u` with `β` an everywhere upper bound of `R_u` approached with
   positive prior mass: `u·m → β`, `Var(R_u) → 0`, `G(u,u) → 0`, via Bhatia–Davis `Var ≤ (‖R_u‖∞+|β|)(β − u·m)`.
6. `LargeDeviationBounds`: closed-set Chernoff bound through the feature box (no exponential tightness); open-set
   lower bound `P_a^{⊗n}(R̄_n ∈ G) ≥ e^{−n(KL(P_b‖P_a)+δ)}` for every tilted mean `m_t(b) ∈ G`, log form.
7. The note's seven-theorem overview: theorem V rewritten around the duality capstone (paired KL integrals,
   `∇𝒮 = θ`, `D²𝒮 = −G⁻¹`, profile geometry), surgical edits to I (visible quotient + bi-Lipschitz), IV (contraction
   identity at fixed response, `V` vs `tV`), VI (finite interior geometry vs asymptotic face degeneration), VII (rate =
   dual potential, lower bound, fluctuation–response).

Not done: interior approximation for boundary points of open sets (Cramér step 4); exposed-face lemma `u·M ≤ β` on
the moment body; the Legendre/extended-real conjugate for unattained means; the full-geometry stability instantiation.

## Questions
1. **Audit** items 1, 2, 5, 6 as stated (signs/normalisations; the `hjnd` witness direction `(1, −b)` for `Var(H) > 0`;
   the everywhere-bound hypothesis in the wall theorem versus an a.e. bound).
2. **Where is the remaining depth?** The programme now has: atlas, calibration, covariance metric, third-cumulant
   bending + contraction, dual geometry with two journeys (slice and full), profile geometry (Pythagoras, Schur, rate
   contraction), stability, boundary (ray concentration), LD upper/lower, fluctuation–response. Candidates: (i) the
   complete Cramér theorem for bounded features (interior approximation + convexity of the rate) — is the rate
   function `I_t(M) + A_t(0)` on int K and `+∞` off `K` the right extended object, and how would you state it without
   an extended-real conjugate API? (ii) exposed faces and the boundary behaviour of the dual potential: `I_t(M) → ∞`
   as `M → ∂K`? (true iff … ? for bounded features with zero face mass; with positive face mass `I` stays finite —
   the two boundary regimes of theorem VI); (iii) the "response geodesic" question: is the m-journey (straight in
   means) or the e-journey (straight in coefficients) shorter in the Fisher length, or neither — any exact
   comparison (e.g. both lengths² ≤ Jeffreys, with equality iff …)? (iv) second-order response along the mean
   journey: `d²m/ds²` along the e-journey is `t²κ₃`; along the m-journey `d²a/ds²` = ? (the dual cubic tensor, the
   `α = −1` connection) — a clean statement of the two dual affine connections on the response space through κ₃
   and V⁻¹; (v) the multi-temperature picture: the family of slices `t ↦ (I_t, V_t)` and `∂_t I_t(M) = u_t(M)`,
   `∂_t² I_t(M) = −δ` (your E) as a formal theorem — the entropy–temperature Legendre structure; (vi) anything of
   comparable depth I am missing. Please rank, and give the theorem bundle for the top pick with pitfalls.
3. **Note structure**: with ~50 Lean paragraphs, is a second consolidation pass warranted now (a dependency-organised
   catalogue: chart → duality → journeys → conditioning → temperature compatibility → sampling/asymptotics → walls),
   or should it wait until the next capstone lands?
