# Research consult, round 35 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "core features of the change in posterior expectation values with the change in the data
distribution; map the space of responses across the data manifold, from the featureless distribution of maximal
entropy to the actual data distribution; maximum beauty and depth"). All formal, sorry-free, on `main`.

## Landed since round 34 (your ranking: 1 second-order loss surface, 2 actual-data reachability polytopes,
## 3 lengths, 4 journey theorem, 5 halfspace Chernoff, 6 walls via polytopes)

1. Second-order loss surface — layer A/B DONE, the `tt` block only. `ResidualFormDeriv`: pure lemma
   `d/dt [v − c·b] = v' − 2 b·c' + b·C' b` whenever `C_t b_t = c_t`, `b` continuous (no inverse differentiability:
   differentiate the slope of the identity). `LossCurvature`: `regCoeff = C⁻¹c` continuous (`continuousAt_matrix_inv`),
   `d/dt Cov_{t,M}(φ,ψ) = −κ₃(φ,ψ,H)` with `H = L₀ − b·R` the residual, `d/dt Var_{t,M}(H) = −κ₃(H,H,H)`, hence
   `∂²_t h = κ₃(H,H,H)` (`hasDerivAt_deriv_lossSurface`). Mixed `tM` and `MM` blocks NOT done.
2. Reachability polytopes — DONE (`DataReachability`): `mixFin ν w = ∑ wⱼ νⱼ` on the simplex, `L_{mixFin} = L₀ + w·a`
   affine, reachable coefficients `= conv{aⱼ}`, reachable responses `= m_t '' conv{aⱼ}` compact ⊂ `int K`, membership
   criterion. The "≠ all of int K" witness is not formalised.
3. Lengths — DONE (`RayLength`): `Length(T) = ∫₀ᵀ √Var_u(L₀)`, `Length² ≤ T(E(0)−E(T))`,
   `|Δ⟨φ⟩| ≤ ∫√(Var φ·Var L₀)`, Popoviciu `Var φ ≤ ((hi−lo)/2)²` for `lo ≤ φ ≤ hi`, `Length ≥ 2|Δ⟨φ⟩|/(hi−lo)`.
4. Journey theorem — DONE (`JourneyPotential`): in natural coordinates `d/ds KL(P_{η s}‖P_{η₀}) = G_{η s}(η s − η₀, η')`;
   `KL(P_{η 1}‖P_{η 0}) = ∫₀¹ G_{η s}(η s − η 0, η' s) ds` for any C¹ path; segment corollary `∫ s G(d,d)`.
5. Halfspace Chernoff — DONE (`HalfspaceChernoff`): `ν^{⊗n}(u·R̄_n ≥ r) ≤ exp[−n(λr − Λ_ν(λu))]`, `iInf` form,
   `familyMeasure` (`P_{t,a}` as a probability measure, expectations = `priorExp`), and
   `Λ_{P_{t,a}}(θ) = A_t(a − θ/t) − A_t(a)` so the rate under a family member is the Legendre transform of `A_t`.
Earlier: constrained responses, slice chart / loss surface / reduced potential (block Hessian `E_tt`), annealing ray,
data mixtures, third cumulant / Amari–Chentsov, featureless point, boundary dichotomy (`FaceLimit`/`FaceInfinite`),
`N^⊥` by restriction, two-axis integrability, three-point identity.

Not done: mixed/MM blocks of the residual-cumulant Hessian; the reachable-set-≠-int K witness; finite-union /
compact-cover Cramér upper bound; walls.

## Questions
1. **Audit** the new statements: (a) `RayLength`: is `Length(T)` really the Fisher length of the ray (response form in
   the temperature direction = `Var_u(L₀)` — the natural coordinate is `−u` with unit speed, so `G = Var`); is the
   Popoviciu route to the lower bound the right one, or is there a sharper `Length ≥ …` in terms of `KL`?
   (b) `HalfspaceChernoff`: `Λ_{P_{t,a}}(θ) = A_t(a − θ/t) − A_t(a)`; the Chernoff rate `sup_{λ≥0}{λr − A_t(a − λu/t) + A_t(a)}`
   — identify it with the dual potential / KL: is `sup_λ {λ r − Λ(λu)} = inf {KL(P_{t,b}‖P_{t,a}) : u·m_t(b) ≥ r}`
   (Cramér rate = information projection onto the halfspace of responses)? That would close the loop "response map ⇄
   concentration" beautifully. Is it true, and what is the cleanest formalisable statement (e.g. the ≥ direction via
   the Bregman/Donsker–Varadhan inequality for each `b`, the ≤ direction via the optimiser `b = a − λ*u/t` when the sup
   is attained in the interior)?
2. **Re-rank what remains and propose new directions** for the PI's goal. Candidates: (i) the Cramér ⇄ information
   projection identity above; (ii) mixed/MM Hessian blocks (`∂_t∂_M h`, `∂²_M h`) — is `∂²_M h = −(C⁻¹)` up to sign
   (the loss surface is `−J`-conjugate)? we have `featCov_mulVec_dualHessian` and `hasDerivAt_dualPotential_temp`;
   (iii) finite unions / compact-cover Cramér upper bound with the prefactor; (iv) a *global* map theorem: the joint
   chart `(t, a) ↦ (h, M)` restricted to the reachable polytope `conv{aⱼ}`, with `KL(P_data‖π̄)` = ∫ along the journey
   (compose `JourneyPotential` with `DataReachability`); (v) Fisher length of the journey along a general path in
   the joint chart, with the lower bound from Popoviciu generalised to any path (`Length ≥ 2|Δ⟨φ⟩|/(hi−lo)` along any
   C¹ path in natural coordinates — the same proof: `|d/ds ⟨φ⟩| = |Cov(φ, S_{η'})| ≤ √Var φ √G(η',η')`); (vi) the
   entropy of `P_{t,a}` as a function on the joint chart (`H = −∫ p log p`), `dH = …`, and the "maximal entropy" reading
   of the featureless point — is `P_{t,0}` the max-entropy member subject to `⟨L₀⟩ = E(t)`? (Gibbs variational
   principle — formalisable via `mixKL_pos`.) (vii) anything else core.
3. For your top pick give the Lean-friendly formulation and pitfalls.
