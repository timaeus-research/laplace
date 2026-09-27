# Round 94 — programme D (the curved response quotient) is complete; what next?

You are Astra, research advisor on the Lean formalisation (laplace seabed, `Laplace/Multi/*`) of the germbij note on
the response map over the data manifold. Since round 93 ALL SIX modules of your programme D landed (sorry-free, in
your ranked order; conventions unchanged: `Pfam θ = ν.tilted(−⟨θ,S⟩)`, `𝕍 = W` the direction space, `A_θ = CD θ`
(chart derivative = minus covariance operator), `T_θ = thirdOp θ` (its Fréchet derivative), `fisherInner S ν θ u v =
Cov_{P_θ}(⟨u,S⟩,⟨v,S⟩) = −⟨u, A_θ v⟩`, `responseOf g = θr(E_{ν.tilted g} S)`, `responseVel = A⁻¹Cov(S,k)`,
`responseHess = A⁻¹(B − T(V,V))`):

- D01 `ResponseFisherJets`: **`hasDerivAt_fisherInner_line`** (`d/dt G_{θ+tu}(v,w) = −⟨v,T_{θ+tu}(u,w)⟩`),
  `dotJ_thirdOp_symm₁₂/₂₃` (total symmetry), `hasDerivAt_fisherInner_line_swap` (Hessian metric),
  **`mChristoffel θ u v := (CDE θ).symm (thirdOp θ u v)`** (`C = A⁻¹T`), **`fisherInner_mChristoffel`**
  (`G(C(u,v),w) = −⟨w,T(u,v)⟩`), **`hasDerivAt_fisherInner_line_mChristoffel`** (`∂_uG(v,w) = G(C(u,v),w)`),
  `mChristoffel_unique`, **`responseHess_eq_sub_mChristoffel`** (`H = A⁻¹B − C(V,V)`),
  **`mixResponseAccel_eq_neg_mChristoffel`** (mixture journeys are m-geodesics, `θ'' + C(θ',θ') = 0`).
- D02 `ResponseDualConnections`: `fisherDeriv`, **`alphaChristoffel α := ((1−α)/2) • mChristoffel`** (e-flat at
  `α=1`, m at `−1`, LC at `0`, torsion-free), **`hasDerivAt_fisherInner_line_dual`** (metric duality `∂_uG(v,w) =
  G(Γ^α(u,v),w) + G(v,Γ^{−α}(u,w))`), **`koszul_alphaChristoffel_zero`**, `chartDeriv_mChristoffel` (`AC = T`),
  **`hasDerivAt_deriv_chartV_path`** (mean path law `(m∘θ)'' = Aθ'' + T(θ',θ')` for `C²` paths in `W`),
  **`mean_accel_eq_zero_iff_mGeodesic`** (m-geodesics = mean-affine paths), `…_of_lcGeodesic` (`(m∘θ)'' = ½T(θ',θ')`).
- D03 `ResponseFisherCurvature`: `contDiff_thirdOp`, **`fourthOp θ := fderiv (θ ↦ thirdOp θ) θ`** with
  **`fourthOp_symm`** (via `isSymmSndFDerivAt` of the smooth `CD`), **`hasFDerivAt_inverse_natural`**
  (`∂_u A⁻¹ = −A⁻¹T(u)A⁻¹`), **`hasDerivAt_mChristoffel_line`** (`∂_uC(v,w) = −C(u,C(v,w)) + A⁻¹Q(u,v,w)`),
  `alphaCurvature α θ u v w := ∂_uΓ^α(v,w) − ∂_vΓ^α(u,w) + Γ^α(u,Γ^α(v,w)) − Γ^α(v,Γ^α(u,w))` (derivs along lines),
  **`alphaCurvature_eq`**: `R^α = −((1−α²)/4)(C(u,C(v,w)) − C(v,C(u,w)))` (closed by `module` after `fourthOp_symm`),
  `alphaCurvature_one/_neg_one = 0`, `alphaCurvature_zero` (Fisher curvature `= −¼[C,C]`), `alphaCurvature_neg`,
  `alphaCurvature_antisymm`.
- D04 `ResponseDensityTopology`: `lawMomentFun i p = ∫ S_i p dν` on `Lp ℝ 1 ν`, **`lipschitzWith_lawMomentFun`**,
  `lawDens ν g hg := toLp (normDens ν g)`, **`DataLaw ν := {p : Lp ℝ 1 ν // ∃ g hg, p = lawDens ν g hg}`** (L¹
  subspace topology), **`lawResponse hS ν p := θr (lawMomentL1 p)`**, `lawResponse_toDataLaw` (= `responseOf`),
  **`continuous_lawResponse`** (via `contDiffOn_infty_chartVInv`), **`modelLaw θ := toDataLaw (modelTilt θ)`**,
  `lawResponse_modelLaw`, **`continuous_modelLaw`** (dominated convergence with the uniform bound
  `p_θ ≤ exp(2R|J|B)` on `‖θ‖ ≤ R`).
- D05 `ResponseFibreDeformation`: **`normDens_mixTilt`**, **`lawDens_mixTilt`** (`= (1−t)•lawDens g + t•lawDens h`),
  **`convex_dataLawSet`**, `contractibleSpace_dataLaw`, **`deform t p := (1−t)•p + t•modelLaw(lawResponse p)`**
  (`t : unitInterval`) with `deform_zero/one/modelLaw`, **`lawResponse_deform`** (fibre-preserving),
  **`continuous_deform`** (joint), `responseFibre θ ⊆ Lp`, **`convex_responseFibre`**, **`contractibleSpace_responseFibre`**.
- D06 `ResponseTopologicalQuotient`: **`isQuotientMap_lawResponse`** (`IsQuotientMap.of_inverse`),
  `continuous_iff_comp_lawResponse`, **`responseQuotientHomeomorph : Quotient (Setoid.ker lawResponse) ≃ₜ W`**,
  `deformHomotopy`/`deformHomotopyWith` (response-preserving)/`deformHomotopyRel` (rel the family),
  **`responseHomotopyEquiv : DataLaw ν ≃ₕ W`**, `contractibleSpace_responseQuotient`.

Slop-note paragraphs exist for all of these. Standing directive from the user: keep formalising, prioritising NEW
MATHEMATICS with "maximum beauty and depth" on the theme "mapping the space of responses across the data manifold,
from the featureless law of maximal entropy to the actual data distribution"; also the user's "resolution story": the
structural coordinate shifts both when the truth varies and when one samples, and chambers are unresolvable when the
sampling variance exceeds the chamber size.

## Open threads / candidates
E1. **C6 `ResponseFibreSecondJet`** (your corrected formula `D²σ₀(0)[ξ,η] = −H_g(Jξ,Jη)`, `Jξ = Kξ − hor(DΦ Kξ)`): still
open; route via twice differentiating `Ψ(z,σ(z,Φg)) = Φg` with the `C^∞` `augSlice` and `fibreSection` (both landed).
E2. **Fisher–Rao length and distance on the quotient**: for a `C¹` path `θ` in `W`, `L(θ) = ∫ √G_{θ_t}(θ',θ') dt`
(`fisherNorm` exists: `fisherNorm_rayPath`, `integrableOn_fisherNorm_rayPath`); first variation `L'(0)` for a
two-parameter family; geodesic equation of `Γ⁰`; is the Fisher–Rao distance between `0` (featureless) and `Φ(D)` a
meaningful "thermodynamic distance" already related to the seabed's three scales (rounds 22–26: `2 arccos ρ ≤ length`,
`d_FR → π`)? What is the cleanest NEW theorem here (e.g. the m-geodesic/e-geodesic/LC-geodesic lengths between the same
endpoints compared; or the length of the mean-affine path vs the straight natural path)?
E3. **Sign structure of the Fisher curvature**: `G(R⁰(u,v)v,u) = −¼(G(C(u,C(v,v)),u) − G(C(v,C(u,v)),u))`; using total
symmetry of the lowered `T` and `C = A⁻¹T`: `G(C(u,x),y) = −⟨y,T(u,x)⟩`. Can the sectional curvature be written as a
difference of two Gram-type quantities `‖T(u,v)‖²_{G⁻¹} − ⟨T(u,u),T(v,v)⟩_{G⁻¹}` (up to sign/normalisation)? If so
that's a beautiful theorem: sectional curvature = a covariance-type inequality defect of the third cumulants
(reminiscent of the "curvature of exponential families = −(1/4) Var-type" formulas). Please give the exact formula
and its sign meaning (when is the Fisher metric of an exponential family nonpositively curved?).
E4. **Resolution/sampling layer on the quotient**: the sampling noise of the structural coordinate (rounds 22–26:
`FisherNormalisedSampling`, `effDim_eq_sum_lawCov`, `d_eff = tr(R C_D)`) lives in `W` with the Fisher metric; the
chamber/wall structure (walls = faces of the moment polytope, `FiniteRange*` modules) partitions `W`. A theorem of the
form "the Fisher-Rao ball of radius `√(d_eff/n)` around `Φ(D)` meets a wall iff …" or "the Fisher distance from `Φ(D)`
to the wall `≥ c ⇒` the chamber is resolvable at sample size `n`". What is the cleanest formalisable statement using
`fisherNorm`, `dist_rayEndpoint_le_tail`, `meanExt`, and the finite-range face stratification?
E5. **Journey lifting**: given a `C¹` path `θ(t)` in `W` and a starting law `g₀` with `Φ(g₀) = θ(0)`, the horizontal
lift `g' = hor_{g(t)}(θ'(t))` in the Banach space of bounded functions — existence via Picard–Lindelöf (`hor` is
locally Lipschitz in `g`?) — or the mixture lift `g(t) = log((1−s(t))p_{g₀} + s(t) p_{θ(t)})`-type explicit lifts. Is
there an explicit CONTINUOUS lift `DataLaw × [0,1] → DataLaw` of every path through a given point of the fibre (a
"connection" on the quotient map in the topological sense = path lifting)? With D05/D06 in place, `lawResponse` has a
continuous section; is it a Hurewicz fibration (path lifting property)? A clean statement: `lawResponse` is a
fibration with contractible fibres, hence a homotopy equivalence (we have the latter directly).
E6. **Second variation / stability of the featureless law**: the response defect `Δ(t)` and its derivatives (rounds
earlier: `deriv_deriv_responseDefect`, `Δ'''(0) = 2κ(h,h,h) + 3κ(h,h,L_v) − κ(L_v,L_v,L_v)`) now have a geometric
reading via `C`: `Δ''(0)`, `Δ'''(0)` as curvature-type invariants? Please state the cleanest identity.
E7. Anything deeper you see, especially something that turns programme D's objects (`C`, `R^α`, the quotient
homeomorphism, the deformation) into ONE theorem about the whole map from the featureless law to the data law.

## Questions
Q1. Rank E1–E7 by depth × reachability; one paragraph each; flag anything you doubt is true.
Q2. For the top items, six modules total: name, one-line deliverable, exact Lean-flavoured statement in the seabed's
conventions, proof route, existing declarations to reuse.
Q3. Headline theorem (one displayed formula) and how it continues the story: first order = Fisher form/submersion,
second order = Hessian/e-m gap, fibres = contractible fixed-moment sets, quotient = W with the curved Fisher metric.
Be concrete; end with the ranked list of six modules to formalise next.
