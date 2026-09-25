# Research consult, round 30 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "map the space of responses across the data manifold, from the featureless distribution of
maximal entropy to the actual data distribution, with maximum beauty and depth"). All formal, sorry-free, on `main`.

## Landed since round 29 (your ranking 1–7)

1. `NaturalCoordinates` (your #1): augmented statistic `S = (L₀, R)`, `θ = Θ(t,a) = (t, ta)`; pull-backs of
   expectations / mean map / free energy / response form (`g_{(t,a)}((s,v),(s,v)) = Var_{t,a}(sL_a + tR_v)`);
   joint kernel vs slice kernel (`(0,v)` invisible ⇔ `v` invisible; a joint invisible direction with `s ≠ 0` writes
   `L₀` as an a.e. affine combination of the contrasts); KL = Bregman of `ψ` in natural coordinates, agreeing with the
   slice KL; **the featureless anchor** `KL(P_θ‖P_0) = ∫₀¹ s Var_{sθ}(S_θ) ds`; the ray chart coordinate is the joint
   mean map on the ray, `⟨L_a⟩_{u,a} = η₀ + a·M`.
3. `RayCramer` (your #3): inverse ray chart `u(x)` on the open image, `u' = −1/Var`; `I(x) = −x u(x) − F(u(x)) =
   sup_{v>0}(−xv − F(v)) = KL(P_{u(x)}‖P_0) − F(0)`; `I' = −u`, `I'' = 1/Var_{u(x)}`; `I` convex;
   `∫_{u₀}^{u₁} √Var = ∫_{m(u₁)}^{m(u₀)} √(I'')`.
4. `RayEndpoint` (your #4): `⟨ℓ⟩_u → ess inf ℓ` with no regular variation (your tilt estimate, verbatim).
   `FiniteEndpoint`: finite alphabet, `P_{rh} → π(·|S_h = min S_h)`, `η(rh) → E_π[S | S_h = min]`.
5. `MomentPolytope` (your #5): finite alphabet, positive prior, nondegenerate `S`:
   **`range η = interior (convexHull (range S))`** (open-map half from `MeanMapEmbedding`; variational half:
   `ψ(θ) ≥ log π_min − ⟨θ,y⟩` on the polytope ⇒ `ψ(θ) + ⟨θ,x⟩ ≥ log π_min + (δ/2)‖θ‖` for `ball x δ ⊆ conv`, extreme
   value theorem, first-order condition `η(θ*) = x`). ~330 lines.
Not done: the degenerate `N^⊥` packaging (2), the two-term wall law (6), the abstract moving minimum (7).

## Where this leaves the programme
In the finite-alphabet case the map is complete: natural coordinates `(t, ta)` for temperature and data as ONE
exponential family; the prior at `θ = 0`; the response coordinates `η` a global chart onto the interior of the moment
polytope; the metric = Hessian of `ψ`; KL = Bregman; the featureless anchor as an integrated response form; the ray
charted by `⟨ℓ⟩` with Cramér's rate function as potential; the faces as the endpoints of the natural rays; the invisible
directions as the joint kernel. Separately, the two-monomial wall (`x^p + a x^q` on `(0,∞)`) has its three-regime
phase diagram with constants (`√t`·interior-minimum length / `(1/√q) log t` / bounded) and its global chart `ℝ ≃ₜ (0,∞)`.

## Questions
1. **The wall as an exponential family.** The wall family `t(x^p + a x^q) dx` on `(0,∞)` IS the two-parameter
   exponential family with statistic `(x^p, x^q)` and natural parameter `θ = (t, ta)`, base measure Lebesgue, natural
   domain `{θ₁ > 0} ∪ {θ₁ = 0, θ₂ > 0}` (plus?), and mean domain `η(Θ) ⊆ conv{(x^p, x^q)} = {(u,v) : v ≥ u^{q/p}}`-ish.
   Please write down exactly: the natural domain, the mean domain (is it the interior of the convex hull of the curve,
   or a proper subset because the family is not steep at `θ₁ = 0`?), where the three regimes of the phase diagram sit
   in the mean domain (the wall `a = 0` is the ray `θ₂ = 0`; the negative chamber `θ₂ < 0`; the positive chamber
   `θ₂ > 0`), and what the `√t` / `log t` / bounded asymptotics say about the boundary behaviour of `η` near the
   corner of the mean domain. Is there a clean theorem "the response length to the boundary of the mean domain is
   finite along the positive chamber, logarithmically infinite at the wall, and `√t`-infinite in the negative chamber",
   i.e. is the phase diagram literally the Fisher–Rao geometry of the mean domain near its boundary? If so, what is the
   Lean-ready statement that reads the three regimes off `I''` (the Hessian of the rate function) in mean coordinates?
2. **Beyond finite alphabets.** For bounded `S` on a general probability space (our standing setting: bounded
   contrasts, positive prior), what is the right analogue of `range η = int conv S(X)`? Candidates: `range η =
   interior (closed convex hull of the essential range)` under minimality; or only `closure (range η) = closed conv`.
   Which is true, and which is the natural formal target (hypotheses, proof route reusing the finite proof: the
   supporting half-space inequality needs `π_min` — replace by `ess inf` over a set of positive mass?).
3. **Two-term wall law** (your §4 of round 29): confirm the sub-step order, and state precisely the abstract
   "polynomial expanding-window expansion" theorem in a form that reuses `HalfLineLaplace.tendsto_sqrt_mul_integral`
   (which gives only the leading term): is it cheaper to prove `Var_B = c₀ + c₁/B + o(1/B)` (one more term, `o` not `O`)
   and does that already give the two-term wall law with `o(1)` error? What exactly is lost with `o(1/B)`?
4. **What else is newly cheap and beautiful** with the joint family landed? Candidates we see: (a) the "featureless →
   data" path as the natural segment `s ↦ sθ` and its length `∫₀¹ √Var_{sθ}(S_θ) ds` compared with `KL = ∫ s Var`
   (is there a clean inequality `Length² ≤ 2 KL`? we have `B ≤ ½KL` warnings); (b) the dually flat structure: the
   `e`-geodesic (natural segment) and the `m`-geodesic (mean segment) and the generalised Pythagoras
   `KL(P_θ‖P_ϑ) = KL(P_θ‖P_ζ) + KL(P_ζ‖P_ϑ)` when `ζ` is the projection — we have `InformationProjection` for the ray;
   (c) the moment-polytope theorem for the augmented statistic with the temperature slice: the image of `{t} × ℝ^k` is
   the slice `{η₀ = ?}`… is it the intersection of the polytope interior with a hyperplane? (no — `η₀ = ⟨L₀⟩` is not
   fixed on a slice); (d) the response form as the second derivative of the rate function in mean coordinates on the
   whole polytope (`I = ψ*` convex conjugate, `∇I = −θ`, `D²I = G⁻¹`), i.e. the finite-dimensional Cramér picture.
Re-rank everything. Be concrete and Lean-aware; spell out hypotheses.
