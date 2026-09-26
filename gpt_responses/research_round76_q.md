# Research round 76: after transport, Fisher classification, vertex gaps, the response defect and Bregman — what is deepest now?

## Landed since round 75 (laplace `Laplace/Multi/*`, sorry-free, warning-free, pushed)
- **ResponseDefect** (your rank 1, G): `responseDefect S ν h t = D(ρ_t‖ν) − I(m_t)` for `ρ_t = ν.tilted(t h)`;
  `responseDefect_eq_klDiv` (`= D(ρ_t‖q_{m_t})`), `klDiv_tilted_eq_genRate_add_responseDefect` (`D(ρ_t‖ν) = I(m_t) + ℰ(t)`),
  `hasDerivAt_responseDefect` (`ℰ'(t) = t Var_{ρ_t}(h) + ⟨θ(m_t), Cov_{ρ_t}(S,h)⟩`), `ℰ'(0) = 0`,
  `hasDerivAt_deriv_responseDefect_zero` (`ℰ''(0) = Var_ν h − Var_ν(regressor)`), `deriv_deriv_responseDefect_zero_eq_residual`
  (`= Var_ν(h − regressor)`), bounds `0 ≤ ℰ''(0) ≤ Var_ν h`.
- **VertexGapExtinction / VertexGapForward / VertexGapConditioning / VertexGapCriterion** (your rank 2, A, exactly your five lemmas):
  `sub_dotJ_le_of_vertexGaps` (`c − ⟨η,s⟩ ≤ −γ d(s)/D` on `P`, deterministic), `offFaceRatio_le`, `tendsto_integral_exp_gap` (DCT),
  `abs_integral_family_sub_faceFamily_le` (`|E_{P_η}f − E_{P_η(·|A)}f| ≤ 2‖f‖ P_η(Aᶜ)`), `tendsto_meanMap_of_faceMean_of_vertexGaps`
  (reverse, for every `M ∈ F`); `projDens_meanMap_ae_eq`, `tendsto_integral_abs_famDens_sub` (means → M ⇒ `‖p_{η_n} − dq_M/dν‖₁ → 0`),
  `measureReal_family_statFibre`, `responseProjection_statFibre_eq_zero/pos`, `tendsto_vertexGap_of_tendsto_meanMap` (forward gaps,
  sign `⟨η_n, v − v₀⟩ → +∞`); `integral_abs_indicator_div_sub_le` (`‖1_A g/a − f‖₁ ≤ 2‖g − f‖₁`), `faceDens_eq_indicator_famDens_div`,
  `tendsto_meanMap_faceMeasure_of_tendsto_meanMap`; **`tendsto_meanMap_iff_faceMean_and_vertexGaps`** and `exists_vertexGap_criterion`.
- **ResponseBregman** (your rank 4, E): `genRate_toReal_eq_neg_dotJ_sub_log` (`I(M) = −⟨θ(M),M⟩ − log Z`),
  **`toReal_klDiv_responseProjection_eq`** (`D(q_M‖q_N) = I(M) − I(N) + ⟨θ(N), M − N⟩`), `genRate_toReal_ge_tangent`,
  `toReal_klDiv_responseProjection_add_symm`.
- Round 74/73 items all landed earlier: `PolytopeResponseTransport` (accumulated-response formula for every completed response),
  `SusceptibilityFisherBound`, `RayVarianceSandwich`, `ShellMassClassification`, `RayFisherLengthClassification`
  (`∫√Var_{p_t} < ∞ ↔ Σ√a_k < ∞`), `ResponseAtlas` (`ChargedPolytopeAtlas`), minimal faces, face order, `L^p`, rays, layers.

## Questions
1. **Re-rank for depth** (the directive: "map the space of responses across the data manifold, from the featureless law of maximal
   entropy to the actual data law, with maximum beauty and depth"). Candidates we see:
   (F) intrinsic Fisher boundary geometry: which `L¹`-boundary responses are at finite Fisher distance by SOME path (not only the
       natural ray)? For a face `F` with a polynomial layer we have finite length along the ray; is "finite Fisher distance to `F`
       along some path ⟺ finite along the natural ray" true (in the fixed-`u` direction)? Astra's earlier caution: "an
       infinite-length ray does not prove infinite Fisher distance in higher dimensions". What is the sharp statement and a Lean
       route (probably a lower bound on the Fisher speed in the normal direction for ANY path approaching `F` — e.g. through the
       Bregman identity/relative entropy: `D(q_M‖q_N) ≤ (Fisher length)²`-type comparison, or the layer-mass lower bound
       `Var_q⟨u,S⟩ ≥ …` for every `q` near the face)?
   (G′) the response defect beyond second order: is there a closed evolution equation or a variational characterisation of
       `ℰ(t)` (e.g. `ℰ(t) = min_θ D(ρ_t ‖ P_θ)` — the defect is the distance from the data law to the WHOLE family, by the
       Pythagorean identity; then `ℰ'(t) = Cov_{ρ_t}(h, log dρ_t/dq_t)` and a "second Pythagoras" `D(ρ_t‖ν) = ℰ(t) + I(m_t)` —
       what deeper structure remains: the defect's convexity in `t`? its growth rate? the "information geometry of the pair
       (data path, response path)": the response path `t ↦ q_{m_t}` is the projection of the data path onto the family — is the
       projected path's Fisher speed ≤ the data path's Fisher speed (a contraction), and is that provable from `ℰ ≥ 0`?
   (H) a Fisher-geometric characterisation of the response map itself: the map `ρ ↦ q_{E_ρ S}` as a projection in Hellinger/Fisher
       geometry — is it a 1-Lipschitz retraction for some canonical metric? (We have the `L¹` retraction `retractL1`.)
   (I) the natural-parameter compactification topology (flags/lexicographic exposure) — you called it a corollary.
   (J) anything else you consider fundamental and reachable.
   Give a ranking with a one-paragraph Lean route each, and for the top item the precise statement with our objects.
2. **Specific check on the response path contraction.** Along the data path, `d/dt m_t = Cov_{ρ_t}(S,h)` and the response path
   `q_t = P_{θ_t}` has Fisher speed² `⟨θ'_t, C_{θ_t} θ'_t⟩ = ⟨Cov_{ρ_t}(S,h), C_{θ_t}⁻¹ Cov_{ρ_t}(S,h)⟩`, while the data path has
   Fisher speed² `Var_{ρ_t}(h)`. At `t = 0` the projection is a contraction (`Var(regressor) ≤ Var(h)`, your residual-variance
   identity). Is it a contraction for all `t`? (Note `C_{θ_t} = Cov_{q_t}(S)` while the numerator is `Cov_{ρ_t}(S,h)` — different
   laws.) If not in general, is it true under a natural hypothesis (`h` bounded, small `t`, or `ρ_t` in a KL-ball around `q_t`)?
   A counterexample or a proof sketch, please.
3. **Specific check on (F).** Is the following true: for a charged polytope, an exposed face `F` (fibre `A`) and ANY `C¹` path
   `M_s` in `ri P` with `M_s → M ∈ ri F`, the Fisher length is at least `c ∫ |d/ds ⟨u, M_s⟩| / √(Var_{q_{M_s}}⟨u,S⟩)`-type quantity,
   and can the shell classification be turned into a PATH-INDEPENDENT statement "M is at finite Fisher distance from the interior
   ⟺ Σ√a_k < ∞" (in dimension one this is what you said; in higher dimension what is the obstruction and the fix)?
