# Research consult, round 36 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "core features of the change in posterior expectation values with the change in the data
distribution; map the space of responses across the data manifold, from the featureless distribution of maximal
entropy to the actual data distribution; maximum beauty and depth"). All formal, sorry-free, on `main`.

## Landed since round 35 (your ranking: 1 Chernoff ⇄ information projection, 2 unified residual-cumulant Hessian,
## 3 entropy geometry, 4 joint-chart Fisher metric, 5 compact-cover Cramér, 6 reachable-chart synthesis, 7 walls)

1. Chernoff ⇄ information projection — DONE (`HalfspaceProjection`), exactly your finite-tilt certificate: with
   `a* = a − (λ/t)u` and slackness `λ(u·m(a*) − r) = 0`: `KL(a*‖a) = λr − Λ_a(λu)`; halfspace Pythagorean identity
   `KL(b‖a) = KL(b‖a*) + λ(u·m(b) − r) + KL(a*‖a)`; primal and dual optimality; `IsLeast`/`IsGreatest` packaging;
   `P_a^{⊗n}(u·R̄_n ≥ r) ≤ exp(−n KL(a*‖a))`. Also the properness witness `reachableResponse ≠ range m_t`.
2. Unified Hessian — DONE (`ChartPathDerivatives`, `LossHessian`): along any differentiable path θ(s) in natural
   coordinates with score S: `d Cov = −κ₃(·,·,S)`, `d b = −C⁻¹κ₃(R,H,S)` (differentiating `Cb = c`, a priori
   differentiability of `b` from `DifferentiableAt.inverse` at a unit), `d Var(H) = −κ₃(H,H,S)`; on the chart:
   chart score `S_{(τ,v)} = τH − (C⁻¹v)·R`, gradient `−τ Var(H) + v·b`, and `D²h[X,Y] = κ₃(H, S_X, S_Y)`.
3. Entropy geometry — DONE (`RelativeEntropyGeometry`): `𝒮(θ) = −KL(P_θ‖π̄) = ⟨θ,m(θ)⟩ + A(θ) − A(0)`,
   `(t,a)`-form `t h + t a·M + A_t(a) − log∫π`, `𝒮 ≤ 0`, `d𝒮 = −G_θ(θ,·)`, `d/dt 𝒮|_M = −t Var(H)`,
   `𝒮(θ) − 𝒮(ϑ) = KL(ϑ‖θ) − ⟨θ, m(ϑ) − m(θ)⟩`, featureless point = max relative entropy at its loss expectation.
4. Joint-chart Fisher metric — DONE (`JointChartMetric`): `D sliceInv(τ,v) = (τ, −τb − C⁻¹v)`,
   `G((τ,v),(τ',v')) = ττ' Var(H) + v'ᵀC⁻¹v`, temperature ⊥ response, general-path observable bound
   `|Δ⟨φ⟩| ≤ ((hi−lo)/2)·Length`, `Length ≥ 2|Δ⟨φ⟩|/(hi−lo)` (Popoviciu route; arcsine not done).
Earlier: everything from rounds 29–34 (constrained responses, slice chart, loss surface, reduced potential, annealing
ray + lengths, data mixtures + reachability polytopes, third cumulant, featureless point, boundary dichotomy, N^⊥,
two-axis integrability, three-point/journey theorem, halfspace Chernoff with `Λ_{P_{t,a}}(θ) = A_t(a − θ/t) − A_t(a)`).

Not done: interior-threshold existence for the projection (`u·m(a) < r < ess sup u·R` ⇒ finite tilt);
arcsine length bound; compact-cover Cramér; reachable-chart synthesis; walls.

## Questions
1. **Audit** items 2–4 as stated. In particular: (a) the Hessian is stated as "derivative of the explicit gradient
   `−τ Var(H) + v·b` along the chart line through `Y`" — is that the full content of `D²h[X,Y] = κ₃(H,S_X,S_Y)`
   (yes if the gradient theorem holds at every chart point, which it does), and is symmetry `D²h[X,Y] = D²h[Y,X]`
   worth stating separately (it is `priorCum3_swap₂₃`)? (b) any sign/normalisation slip in
   `d/dt 𝒮|_M = −t Var(H)` and `d𝒮 = ⟨θ, dm⟩ = −G_θ(θ,·)` (natural coordinates `θ = (t, ta)`, density
   `e^{−θ·S}π/Z`)? (c) the response block `κ₃(H,V_v,V_w)`: is there a clean statement of when it is definite, or a
   nice invariant (e.g. its trace against `C`, `∑ κ₃(H, V_{e_i}, V_{Ce_i}) = κ₃(H, ·, ·) contracted with C⁻¹`)?
2. **What is now the deepest missing piece for the PI's goal?** Candidates: (i) interior-threshold existence
   (monotonicity of `λ ↦ u·m(a − λu/t)` (it is `−(1/t)·G(u,u)` decreasing? actually `d/dλ u·m(a − λu/t) = +Var(R_u)`
   — check sign) plus the large-tilt limit `u·m(a − λu/t) → ess sup_{P_{t,a}} u·R` via the boundary theorems
   (`FaceLimit`) — gives existence of the projection for every interior threshold and hence Cramér's rate as an
   honest sup/inf identity); (ii) the arcsine bound `Length ≥ 2|arcsin√z(1) − arcsin√z(0)|`; (iii) compact-cover
   Cramér with strict `α < inf_F I`; (iv) a "curvature of the response map" theorem: the second fundamental form
   of the response image / the Amari α-connections in the joint chart (we have the Amari–Chentsov tensor
   `κ₃(S_u,S_v,S_w)` — is the unified Hessian the `∇^{(1)}`-covariant Hessian of `h` in some canonical sense? e.g.
   `D²h[X,Y] = κ₃(H,S_X,S_Y)` looks like "the Hessian of `⟨L₀⟩` w.r.t. the mixture connection, restricted to the
   constrained submanifold"; a precise statement would be a beautiful capstone: dual flatness, e/m-connections,
   and the loss Hessian as an m-Hessian); (v) global reachable-chart synthesis; (vi) something else core.
3. For your top pick give the Lean-friendly formulation and pitfalls.
