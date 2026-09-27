# Research round 82 — after the facet theory: what is the deepest next structure?

Context: germbij response-map programme in the laplace seabed (Lean 4.33). Standing direction (user): "map the space of
responses across the data manifold, from the featureless distribution of maximal entropy to the actual data
distribution; maximum beauty and depth". Since round 81 (all sorry-free):

* `FisherCompletionMeasure` (`completionLaw x = ν.withDensity Ψ̄(x)²`, probability, mean `meanExt x`, `= P_θ` at interior points);
* `FaceRootDensityLimit` (normal ray → face root density in `L²`, via the affinity `‖q_r − q_F‖² = 2 − 2√(Z_F/A_r)`);
* `FacetCompletionLaw` (`completionLaw x_M = familyMeasure (faceMeasure ν A) 1 0 S 1 v_M`; `rayTail`,
  `tendsto_ray_completion`, `dist([v_M − a u], x_M) ≤ rayTail a`);
* `CompletionSupportingFace` (a completion law is concentrated on every exposed face containing its mean);
* `DataResponseEndpoint` (`t ↦ [θ_t]` has a limit in `Ŵ_F` iff the response length is finite; the limit's law is the
  face family law);
* `NormalTiltFisherComparison` (`⟨a,S⟩ = c` on `A`, `⟨a,S⟩ ≥ c` a.e. ⇒ `Var_{P_{θ+a}}⟨w,S⟩ ≤ Var_{P_θ}⟨w,S⟩/P_θ(A)`);
* `FacetHellingerEmbedding` (`q_{θ_n} → q_F(v_M)` in `L²` ⇒ `[θ_n] → x_M`).

So for a polytope moment body with charged vertices and a FACET `F` we have the complete picture: accessibility iff
`Σ√a_k < ∞`; the completion fibre over `M ∈ ri F` is a single point; its law is the face family law; the data
response reaches it iff its length is finite; Hellinger and Fisher topologies agree there.

## Questions

**Q1 (codimension ≥ 2, honestly).** For a vertex or lower-dimensional face `F` (codim `k ≥ 2`), the normal cone `C_F`
replaces the ray. Which of the following is the right *first theorem*, and what is its proof skeleton in our language?
(a) **Uniqueness by normal translation** (your round-81 §Q2): every nonempty fibre `m̄⁻¹(M)`, `M ∈ ri F`, is a point,
using `fisherVar (θ+a) ≤ fisherVar θ / P_θ(A_F)` and a translated grid. Please spell out the translated-grid step: two
Cauchy sequences `θ_n = v_M + a_n`, `θ'_n = v_M + b_n`, `a_n, b_n ∈ C_F` (after removing tangential errors) — how exactly
does one bound `d_F(θ_n, θ'_n)`? Is it `d_F(v_M + a_n, v_M + a_n + b_m) + d_F(v_M + a_n + b_m, v_M + b_m)` with each term
a *translated Cauchy tail* (translate the short path from `θ_n` to `θ_{n'}` by `b_m`, cost multiplied by
`P^{-1/2}(A_F)`) plus the "fixed normal shift" term `d_F(v_M + a_n + b_m, v_M + b_m) → 0` as `n → ∞` for fixed `m`?
Why does the fixed shift term vanish — because along the segment `s ↦ v_M + b_m + s a_n` the Fisher speed
`√Var_{P}(⟨a_n,S⟩)` is small when the law concentrates on `A_F` where `⟨a_n,S⟩` is constant? But `a_n` grows
(`‖a_n‖ → ∞`) — the variance of `⟨a_n,S⟩` under a law with `P(A_F) → 1` is `≤ 2K‖a_n‖² P(A_F^c)`-ish, which need not
vanish. Please resolve this precisely (perhaps the concentration must be quantified: `P_{v_M + a_n}(A_F^c) ≤ e^{−gap(a_n)}`
with `gap` the normal energy gap, so `‖a_n‖² e^{−gap} → 0`?). Give the exact statement of the lemma you'd formalise.
(b) **Eventual normal-cone membership**: `m(θ_n) → M ∈ ri F` ⇒ `θ_n − proj_{T_F} θ_n ∈ C_F` eventually. In the facet
case this is `r_n → ∞`. For codim 2 with vertex `M`: `θ_n = v_M + a_n` with `⟨a_n, w − M⟩ → −∞`?? for every vertex
`w ≠ M`? (The vertex-gap criterion gives `⟨θ_n, w − M⟩ → +∞` in our sign convention `P_θ ∝ e^{−⟨θ,S⟩}`.) Is eventual
membership in the *closed* normal cone `{a : ⟨a, w − M⟩ ≥ 0 ∀ w ∈ V}` what's needed, or in the open cone? With
`a_n = θ_n − v_M` and `⟨v_M, w − M⟩` bounded, `⟨a_n, w − M⟩ → +∞` gives strict positivity eventually — fine for finitely
many vertices. But the "sign-adjusted normal" hypothesis of `NormalTiltFisherComparison` is `⟨a,S⟩ = c` on `A_F` and
`⟨a,S⟩ ≥ c` a.e.: for a vertex `M`, `A_F = statFibre M` and `⟨a, S(x)⟩ ≥ ⟨a, M⟩` a.e. iff `⟨a, S(x) − M⟩ ≥ 0` a.e. iff (S
takes values in the polytope a.e.) `a` is in the normal cone at `M`. OK. So (b) reduces to the vertex-gap criterion.
Confirm.
(c) **Accessibility in codim 2** — the multiscale problem. For the product square example the answer is clean
(product of 1-D criteria). Is there ANY general sufficient condition worth formalising now (e.g., accessibility along
the *bisector* ray `−r(u₁ + u₂)` implies accessibility; and the criterion for a fixed ray is the dyadic shell sum of
the slack `ℓ = ⟨u₁+u₂, S⟩ − β`, by `RayFisherLengthClassification` applied to that ray)? Then "accessible iff some ray
in the open normal cone has summable shell roots" would be a *characterisation* if we also show: accessible ⇒ some
ray is finite (is that true? In codim 1 yes (facet theorem). In codim 2: a finite-length path with means → M — does
it force a finite ray? Your round-79 counterexample idea (charged square) said the ray/path equivalence FAILS in
codim ≥ 2: tangential nuisance runs on different scales. So accessibility is NOT equivalent to any single ray being
finite. Then what is the right characterisation? Perhaps: accessible iff `inf over paths` … tautological. Is there a
clean two-parameter shell criterion for the product case only? Please state the product-corner theorem precisely
(what to formalise: `ProductCornerCompletion`).

**Q2 (the map across the data manifold).** The response coordinates `θ_t` of `ρ_t = ν.tilted(t h)` are a curve; the
"data manifold" more generally is `{ν.tilted(g) : g ∈ G}` for a finite-dimensional space of observables `G ∋ h` (or all
bounded `g`). The response map `Φ : ν.tilted(g) ↦ θ(g) ∈ W` (the parameter with `m(θ(g)) = E_{ν.tilted g} S`) is
defined whenever the data mean is interior. We now know: along a ray `g = t h` the curve extends to `t = ∞` in `Ŵ_F`
iff the response length is finite. What is the natural *global* statement? Candidates: (i) `Φ` is locally Lipschitz
from the Hellinger metric on the data manifold to `d_F`?? (false in general — the response can be infinitely long
while the data path has finite Hellinger length: the atomic example); (ii) the Fisher–Rao geometry of the data
manifold (Fisher metric of the family `ν.tilted(g)` in `g`) versus the pulled-back `d_F`: is `d_F(Φ(q), Φ(q')) ≤ C
d_{FR}(q, q')` locally? The data-side speed is `√Var_{ρ_t} h` and the response speed is `√(−⟨θ', Cov_{ρ_t}(S,h)⟩)`; we
have `ThreePointNotContracting` (response speed can exceed data speed) — so no contraction; (iii) the *Legendre
duality*: `Φ` factors through the mean map `m_data(g) = E_{ν.tilted g} S = m(Φ(g))`, so `Φ = m⁻¹ ∘ (g ↦ E_{ν.tilted g} S)`
and the completed response map is `m̄⁻¹` on the closure — but `m̄` is not injective in general (only on accessible
facets). Please propose THE theorem that deserves the name "the response map across the data manifold" and is
provable with our tools, e.g.: for the top-set conditional mean in a facet interior, the endpoint law is the
I-projection of `ν` onto `{Q : ∫ S dQ = M}` (a KL characterisation: `D(Q‖ν) ≥ D(Q_M‖ν)` for all `Q ≪ ν` with mean `M`,
with equality iff `Q = Q_M`) — is this provable from `ResponseBregman`/`ResponseDefectPythagoras` plus the
boundary-support argument (`CompletionSupportingFace`-style)? Give the Lean skeleton.

**Q3 (the featureless end).** The other end of the data manifold is `t = 0`: `ρ_0 = ν`, `θ_0 = 0`. Is there a
theorem about the *whole* curve `t ∈ [0, ∞]` — e.g., the response length `∫_0^∞ |θ'_t|_F dt` bounded by a data-side
quantity when the top set is charged (we showed the data-side Fisher length `∫√Var_{ρ_t} h` is `2 arccos √p₀ < π` for
indicators; the response length can be infinite). Conversely is there an *upper* bound of the response length by
`log(1/p_*)` times something in the facet case (from `DataRayReverse`'s window bound we have
`L_resp ≤ C₁∫D + C₂(∫g + 2C₃ log(1/p_*) + 2C₄∫D)` where `∫D ≤ 2B card J log(1/p_*)`)? Is the clean statement
`L_resp ≤ A · L_ray + B · log(1/p_*)` with explicit constants worth landing?

**Q4 (ranking).** Rank ≤ 300-line modules by depth with one-line statements; say which are ready now.
