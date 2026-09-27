# Round 95 — programme E (information geometry of the response quotient) is complete; what next?

You are Astra, research advisor on the Lean formalisation (laplace seabed, `Laplace/Multi/*`) of the germbij note on
the response map over the data manifold. Since round 94 ALL SIX modules of your programme E landed (sorry-free, in
your ranked order; conventions unchanged: `Pfam θ = ν.tilted(−⟨θ,S⟩)`, `W = 𝕍`, `A_θ = CD θ`, `T_θ = thirdOp θ`,
`G = fisherInner`, `C_θ = mChristoffel = A⁻¹T`, `Γ^α = alphaChristoffel`, `responseOf`, `lawResponse` on `DataLaw ν ⊆ L¹`):

- E1 `ResponseFisherCurvatureSign`: `inverseFisherInner θ x y := G(A⁻¹x, A⁻¹y)` (`= −⟨x,A⁻¹y⟩`, inner product),
  **`fisherInner_mChristoffel_mChristoffel`** (`G(C(u,v),C(x,y)) = G*(T(u,v),T(x,y))`, rfl), lowered tensor
  **`fisherInner_alphaCurvature`** (`G(R^α(u,v)w,x) = −((1−α²)/4)(G*(T(u,x),T(v,w)) − G*(T(v,x),T(u,w)))`),
  **`fisherCurvature_numerator`** (`G(R⁰(u,v)v,u) = ¼(G*(T(u,v),T(u,v)) − G*(T(u,u),T(v,v)))`),
  **`fisherCurvature_numerator_nonpos_iff`**, `fisherSectional(_nonpos_iff)`, antisymmetry/pair symmetry/**Bianchi**
  for every α, `alphaCurvature_eq_zero_of_comm`.
- E2 `ResponseInformationPythagoras`: `toReal_klDiv_tilted_tilted`, **`tilted_mixTilt`** (law of the mixture tilt =
  ℝ≥0-mixture), `toReal_klDiv_tilted_model`, `toReal_klDiv_model_model` (Bregman), **`toReal_klDiv_pythagoras`**
  (`KL(ρ_g‖P_θ) = KL(ρ_g‖P_Φg) + KL(P_Φg‖P_θ)`), **`toReal_klDiv_pythagoras_featureless`** (θ = 0),
  `toReal_klDiv_model_ge`, **`toReal_klDiv_model_eq_iff`** (unique I-projection), `responseInformationDefect` (`≥ 0`,
  `= 0 ↔ ρ_g = P_Φg`, `= 0` on the family), **`responseInformationDefect_mix_le`** (`≤ (1−t)·defect` along the mixture).
- E3 = C6 `ResponseFibreSecondJet` (closed at last): `fibreGraph σ₀`, `hasFDerivAt_fibreGraph_zero` (`Dσ₀ = −V`),
  `eventually_fderiv_sl_fibreGraph`, **`fderiv_fderiv_fibreGraph_zero_eq_neg`**, `fderiv_fderiv_sl_zero` (= response
  Hessian on augmented coefficients), `fibreTangent Jξ`, **`responseVel_fibreTangent`** (`DΦ[Jξ] = 0`),
  **`fderiv_fderiv_fibreGraph_zero`** (`D²σ₀(0)[η,ξ] = −H_g(Jη,Jξ)`).
- E4 `ResponseFaceFisherSeparation`: `affinity`, `sphericalDist = 2 arccos ρ` (metric via `InnerProductGeometry.angle`
  on `rootDensL2`, `sphericalDist_triangle`), **`abs_affinity_deriv_le`** (`|∂ρ| ≤ ½√(1−ρ²)‖γ'‖`),
  **`two_arccos_affinity_le_integral`** (angle ≤ Fisher length, by the `ε`-regularised comparison `L/2 − arccos((1−ε)ρ)`),
  **`integral_rootDens_mul_sqrt_le`** (face margin `ρ(p_θ,q) ≤ √P_θ(A)` for `q` supported on `A`),
  `integral_rootDens_mul_sqrt_faceCondDens` (attained), **`two_arccos_sqrt_real_le_integral_add`** (face separation).
- E5 `ResponseSamplingBoundary` (name `ResponseSamplingResolution` was already taken by an earlier module; the
  `d_eff/n` identity `integral_samplingEnergy` and the resolution floors existed): **`measureReal_dotJ_sampleResponse_le_le`**
  (wall crossing `≤ Var_D⟨a,S⟩/(nδ²)`), **`dotJ_sampleResponse_eq_iff`** (on an exposed face iff every observation),
  **`measure(Real)_dotJ_sampleResponse_eq`** (`= P_D(face)^n` under `iIndepFun`), `_lt_one`.
- E6 `ResponseFisherEnergyVariation`: `continuous_fisherInner`, `continuous_mChristoffel`, `FisherVariation` (explicit
  `C²` package `Θ V A U W`), `fisherEnergy`, **`hasDerivAt_energyIntegrand`** (`∂_sG(V,V) = 2G(W,V) + G(C(U,V),V)`),
  **`hasDerivAt_energyPairing`**, **`hasDerivAt_fisherEnergy`** (differentiation under the integral),
  **`fisherEnergy_variation`** (`E'(0) = G(U,V)|₀¹ − ∫G(U, θ'' + ½C(θ',θ'))`), **`hasDerivAt_fisherEnergy_of_lcGeodesic(_fixed)`**.

Slop-note paragraphs exist for all of these (Overleaf). The seabed now has programmes A (finite-range stratification),
B (second-order response calculus), C (mixture geometry & fibres), D (curved response quotient: α-connections,
curvature, density topology, deformation retraction, quotient homeomorphism/homotopy equivalence), E (curvature
sign, KL Pythagoras, fibre second jet, face separation, sampling boundary, energy variation).

Standing directive from the user: keep formalising, prioritising NEW MATHEMATICS with "maximum beauty and depth" on
"mapping the space of responses across the data manifold, from the featureless law of maximal entropy to the actual
data distribution"; plus the resolution story (truth shifts vs sampling shifts; chambers unresolvable when sampling
variance exceeds chamber size). User's older open threads: negative-profile saddle lemma, general `k` multiplicity law
(k=1 landed: `log t − ½ log log t + K`), product inequality.

## Candidates I see
F1. **KL Hessian = Fisher** (`ResponseInformationHessian`): `t ↦ KL(ρ_g ‖ P_{θ+tu})` has derivative `⟨u, E_ρS − m(θ+tu)⟩`
(`hasFDerivAt_famZ` gives `∂ log Z`), vanishing exactly at `θ = Φ(g)`, second derivative `G_θ(u,u)`: the response is
the unique nondegenerate minimiser; the model-fitting objective is Fisher-convex along natural lines.
F2. **Fundamental lemma / converse of E6**: if `E'(0) = 0` for all compactly supported variations then
`θ'' + ½C(θ',θ') = 0` (needs a bump-function argument in `W`; is there a cheap Mathlib route?).
F3. **Global trivialisation `DataLaw ≅ responseFibre(0) × W`** (your round-94 E5 remark): exponential tilting of
each input law relative to `p` — the missing theorem is joint continuity of the relative moment inverse in the L¹
variable. Is there a formalisable statement with the present tools (`contDiffOn_infty_chartVInv` is for the reference
ν only)? What is the honest version (local trivialisation near the family?).
F4. **Sectional curvature examples**: the categorical (multinomial) family has `K ≡ +¼`; a Gaussian location family
has `K = 0`; can we exhibit in Lean the sign in a concrete finite-range instance via `fisherCurvature_numerator`
(e.g. `X = Fin 3`, `S` = two indicator statistics) with a closed-form `T` and `G*`? Or a general theorem: for a
finite-range family with `S` taking values in an affine basis, `K ≡ +¼`?
F5. **The Fisher completion vs the L¹ topology of `DataLaw`**: the seabed has the intrinsic Fisher completion
`FisherCompletion` with `rootDensExt`, `hellingerExt ≤ dist/2`, and now `sphericalDist ≤ fisherLength`. Is
`sphericalDist` (angle) also `≤ fisherDist` (the intrinsic distance) — yes by taking inf over paths — and does the
completion then embed isometrically-up-to-`2×` into the L² sphere? A clean statement: `sphericalDist_le_fisherDist` and
the induced continuous map from the completion to the sphere; where is the genuine new theorem?
F6. **Resolution story as one theorem**: combine `measureReal_dotJ_sampleResponse_le_le` (wall crossing) with the
truth-shift `⟨a, b_t⟩ = Cov_{ρ_t}(⟨a,S⟩,h)` along a data journey: the empirical structural coordinate resolves the
direction of the truth shift at time `t` iff `t·|⟨a,b⟩| ≫ √(Var/n)`, i.e. a theorem "for `n ≥ N(t)` the sign of the
empirical shift agrees with the truth shift with probability `≥ 1 − ε`" — the resolution floor in probabilistic form.
F7. **Journeys from the featureless law**: the mixture journey `(1−t)ν + t ρ_g` from the featureless law to the
data law and its response `Φ_t`; velocity/acceleration formulas exist locally (`ResponseMixtureConnection`); a global
statement about `t ↦ Φ((1−t)ν + tρ_g)` (C^∞ on [0,1], the m-geodesic in the mean chart, its Fisher length ≤ …, its
information defect `KL(ρ_t ‖ P_{Φ_t})` ≤ `t KL(ρ_g ‖ P_Φ)`?) — a "featureless-to-data" headline theorem.
F8. Anything deeper.

## Questions
Q1. Rank F1–F8 by depth × reachability; one paragraph each; flag anything you doubt is true.
Q2. Six modules: name, one-line deliverable, exact Lean-flavoured statements in the seabed's conventions, proof route,
existing declarations to reuse.
Q3. Headline theorem (one displayed formula) and how it continues the story.
Be concrete; end with the ranked list of six modules to formalise next.
