# Research consult, round 37 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "core features of the change in posterior expectation values with the change in the data
distribution; map the space of responses across the data manifold, from the featureless distribution of maximal
entropy to the actual data distribution; maximum beauty and depth"). All formal, sorry-free, on `main`.

## Landed since round 36 (your ranking: 1 global chart synthesis, 2 interior-threshold existence, 3 fixed-temperature
## mixture geometry, 4 arcsine bound, 5 compact-cover Cramér, 6 walls)

1. Global chart — DONE (`ChartSynthesis`): `responseChart : PartialHomeomorph` from `{θ_none > 0}` (natural
   coordinates) onto `chartDomain = {(t,M) | t > 0, M ∈ int K}` with inverse `sliceInv`; `BijOn`; `h(t,M)` and
   `𝒮(t,M)` continuous on the chart domain. (Coercivity was not needed: the seabed already had `range m_t = int K`
   and injectivity; the packaging is the new content.)
2. Interior-threshold existence — DONE (`InteriorThreshold`): `d/dλ u·m(a − λu/t) = Var_{a_λ}(R_u)` (no `1/t`, as you
   said); `⟨V⟩_λ → ess inf V` for bounded `V` under accessibility only (no positive-mass face) — proof:
   `α ≤ ⟨V⟩_λ ≤ α + ε + (M+|α|) q_λ({V<α+ε}ᶜ)`; hence `u·m(a_λ) → ess sup u·R`; every `u·m(a) < r < ess sup` has a
   finite tilt (IVT); `sup_{μ≥0}{μr − Λ_a(μu)} = inf{KL(b‖a) : u·m(b) ≥ r}` as `sSup = sInf`.
3. Mixture geometry — recorded as interpretation in the note (full-family m-Hessian of `h` is 0; the response block
   is the intrinsic mixture Hessian of the fixed-`t` family); the block theorems are formal (`LossHessianBlocks`:
   symmetry, `κ₃(H,H,H)`, `−κ₃(H,H,V_v)`, `κ₃(H,V_v,V_w)`).
4. Arcsine bound — DONE (`ArcsineLength`): Bhatia–Davis `Var φ ≤ (⟨φ⟩−lo)(hi−⟨φ⟩)` and
   `2|arcsin√z(1) − arcsin√z(0)| ≤ Length(η)` along any C¹ natural path with interior expectations.
5. Compact-cover Cramér — DONE (`CompactCoverCramer`): finite-union Chernoff; for compact `F` with pointwise dual
   witnesses `θ·x − Λ(θ) > α`: `∃ N, ∀ n ≥ 1, P(R̄_n ∈ F) ≤ N e^{−nα}`.
Earlier (rounds 29–36): constrained responses, slice chart, loss surface, reduced potential, annealing ray and
lengths, data mixtures and reachability polytopes (+ properness), third cumulant / Amari–Chentsov, featureless point,
boundary dichotomy, N^⊥, two-axis integrability, three-point + journey theorem, halfspace Chernoff with
`Λ_{P_{t,a}}(θ) = A_t(a − θ/t) − A_t(a)`, information projection certificate, unified Hessian
`D²h[X,Y] = κ₃(H,S_X,S_Y)` with `d b = −C⁻¹κ₃(R,H,S)`, relative entropy geometry (`𝒮 = ⟨θ,m⟩ + A(θ) − A(0)`,
`d𝒮 = −G(θ,·)`, `d/dt 𝒮|_M = −t Var(H)`, Gibbs variational principle in the family), joint-chart Fisher metric
`ττ'Var(H) + v'ᵀC⁻¹v`.

Not done: contraction identity `tr(CK) = Cov(H,Q) = −∂_t log det C|_M`; asymptotic form `limsup (1/n) log P ≤ −α`;
second fundamental form `B^{(m)}`; walls; canonical parameter map on the reachable locus `d ↦ q(t, M(d))`.

## Questions
1. **Audit** items 2, 4, 5 as stated. (a) In `tendsto_priorExp_face_inf` the hypotheses are `hα : ∀ᵐ x, α ≤ V x`
   and `hmass : ∀ ε > 0, 0 < ∫_{V<α+ε} π` — is that exactly "α is the essential infimum of V under π̄"? (b) the
   arcsine theorem assumes `∀ s, lo < ⟨φ⟩_{η s} < hi` for ALL real `s` (the path is defined on all of ℝ); harmless?
   (c) the Cramér theorem's hypothesis `∀ x ∈ F, ∃ θ, α < θ·x − Λ(θ)` — is it equivalent to `α < inf_F I` with
   `I(x) = sup_θ {θ·x − Λ(θ)}` when `I` may take the value +∞ (yes, pointwise); any subtlety with `F` compact but
   `I = +∞` on part of it? (d) in `exists_halfspace_projection` the threshold hypothesis is
   `u·m(a) < r < β` with `β` an a.e. upper bound of `u·R` satisfying accessibility — i.e. `β = ess sup`; if `β` is
   merely an a.e. bound with accessibility (which forces `β = ess sup`) fine?
2. **Big picture.** After 37 rounds the seabed has ~35 modules on this programme. What is the *statement of the
   theory* — the 5–8 theorems a reader should see first, in what order, to understand "the map of responses across
   the data manifold from the featureless point to the data"? Please propose the narrative spine and say which
   landed theorems are the load-bearing ones and which are supporting lemmas. This will drive the consolidation of
   the note (`germbij_slop.tex`, currently ~35 paragraphs in landing order).
3. **Re-rank what remains and propose new directions**: (i) contraction identity + log-det corollary
   (needs Jacobi's formula for `d/dt det C`; Mathlib has no `HasDerivAt.matrix_det` — we have a seabed
   `hasDerivAt_finset_prod`; `det` via `Matrix.det_apply'` as a sum over permutations of products is doable);
   (ii) the asymptotic upper bound `limsup_n (1/n) log P(R̄_n ∈ F) ≤ −inf_F I` (from the compact-cover bound by
   letting `α ↑ inf_F I`); (iii) the second fundamental form / mixture-bending capstone as a formal theorem — what
   exactly would be stated in Lean? (iv) canonical parameter assignment on the reachable locus: for the finite
   mixture family `ν_w`, `w ↦ q(t, M(w))` is continuous/differentiable and the loss/entropy landscape restricted to
   the polytope; (v) a "response map from the featureless point to the data" theorem: the straight segment from
   `(t,0)` to `(t,a_data)` in natural coordinates with all quantities (KL, length, entropy drop, response
   displacement) computed/bounded along it — a single packaged statement; (vi) lower bounds (Cramér lower
   half / change of measure) — is there a clean finite-n *lower* bound `P(R̄_n ∈ B(m(b), ε)) ≥ e^{−n(KL(b‖a)+δ)}`
   for large n via the tilt (needs a law of large numbers under the tilt — Mathlib has the strong law
   `ProbabilityTheory.strong_law_ae` for iid real sequences; a weak law/Chebyshev suffices); (vii) anything else.
4. For your top pick give the Lean-friendly formulation and pitfalls.
