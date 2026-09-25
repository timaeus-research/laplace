# Consult: germbij analytic layer, fifteenth research round (after research_round14)

Same setting (Lean 4 + Mathlib, laplace `Laplace.Multi`, mirrored on the local hironaka branch `wall-atlas`). Every item of your round-14 ranking is closed, sorry-free, standard axioms:

1. **General-truth consumer interface.** The whole term layer is now stated for `TruthChartsData m T L'` (`WallChartsData m ℓ L' := TruthChartsData m (fun z ↦ z ℓ) L'` is an abbreviation; namespaces `TruthChartsData`, `TruthChartsData.Phase`; `bridgePt`, `modelKernelOf`, `termKernel`, `TermData.vertex/tied/partial/activeTruth/activeTruthDegenerate`, `TermMeasureCertificate`, `fibreRatio`, the expectation and distinguishability theorems all over an arbitrary `T`). Nothing changed for coordinate truths. On hironaka: `WallAtlasT.toPhase` and `exists_truthChartsData_withPhase : ∃ ε > 0, ∃ D : TruthChartsData m T (L ∩ {|T| ≤ ε}), Nonempty (D.Phase F)` for `F, T` analytic near `0`, `T 0 = 0`, `F·T ≢ 0`, `L ⊆ W` compact, `W` connected open.
2. **Exported `xy` regression** (`MixedTruthExport.lean`, hironaka `TruthMixedRegression.lean`): `exported_mix_tendsto_totalKernel`: ANY `D : TruthChartsData 1 (z₀z₁) (closedBall 0 (1/2) ∩ {|z₀z₁| ≤ ε})` has `(D.totalKernel (e^{-t z₀z₁ a} ψ) (σ/t)).toReal / log t → e^{-σ a(0)} ψ(0)` (`a` continuous, `ψ ≥ 0` continuous supported in the closed square `[0,1/2]²`); `exists_mixed_export_regression`: for `a` analytic on `univ` with `a 0 ≠ 0`, the resolution of `z₀z₁ a · z₀z₁` produces such `D` with a phase record, and the limit holds for it. Route: cutoff in the truth variable, a.e. equality of kernels across regions for an observable supported in both, continuity of both kernels at `s ≠ 0`, pointwise identification, cutoff factor `= 1` at `σ/t`.
3. **Limit identification lemmas**: `TruthChartsData.totalKernel_ae_eq_of_support`, `totalKernel_mul_comp_truth` (`D.totalKernel (θ · η∘T) s = η s · D.totalKernel θ s`: the kernel at `s` sees only the fibre `T = s`), `eq_of_ae_eq_of_continuousAt`.
4. **Profile integrability ⇔ strict optimum** (`ProfileIntegrability.lean`), for the anchored unquotiented profile with one scaled coordinate `j` (the only integrable configuration under a strict truth constraint, by `not_integrable_envelope_of_two_scaled`):
```lean
theorem integrable_singleScaleProfile_iff {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) {j : Fin (m + 1)}
    {r κ : Fin (m + 1) → ℝ} (hκj : 0 < κ j) :
    Integrable (singleScaleProfile ρ c j r κ) ↔
      -1 < r j ∧ ∀ i, i ≠ j → -1 < r i - κ i * (r j + 1) / κ j
-- singleScaleProfile ρ c j r κ u = 1_{u_j > 0, 0 < u_i < ρ (i ≠ j)} ∏ u^r · exp(-c ∏ u^κ)
```
(sufficiency by Fubini and the Gamma integral; necessity by the recession directions `−e_j` and `κ_i e_j − κ_j e_i` through the existing `not_integrable_of_recession_direction`). The general polyhedral criterion (all coordinates, tied truth constraint) is not formalised.
5. **Exact log-face constants — inventory.** On checking, the exact constants the note uses are already theorems: `tendsto_modelKernel_tied` (fully tied face, `Q = 0`, moving unit/weight continuous at the face point: `A W(0,0) (B a(0,0))^{-λ} δ^k Γ(λ)/k! ∏ 1/κ_i`), `tendsto_modelKernel_partial_var` (tied block `T` ⊕ strictly worse block `N`, moving units: `A δ^k Γ(λ)/k! ∏_T κ^{-1} ∫_{(0,ρ)^N} W (B a)^{-λ} ∏_N z^{r−λκ} dz` at the face point), their chart wrappers `TermData.tied`, `TermData.partial`, and — with a tied truth constraint — the active-truth family (`vol(F')/|det M|` times the transverse integral; all free coordinates tied by the certificate, spectators strictly worse in `tendsto_modelKernel_general_spectator`, degenerate second constraint in `tendsto_modelKernel_general_degenerate`). Your round-14 formula `vol_d(F) ∫_N 1_{z_j ≥ 0, j ∈ J₀} e^{-c·z} exp(-∑_{A₀} a_i e^{-α_i·z}) dz` is, in this single-phase-monomial setting, the simplex volume `∏ 1/κ_i` (one constraint) or `vol(F')/|det M|` (two constraints). So I regard item 5 as closed unless you see a regime the inventory misses.

The note itself (`germbij.tex`, the object of the formalisation; `germbij_slop.tex` is the running commentary with the LEAN paragraphs) has sections: The question; Setup; The nondegenerate case; Why analyticity matters; The singular case; Identifiability at singular minima (a pencil identity; the theorem; the normalized formulation; constructive recovery; what remains); Summary; Asymptotic notation and the scale.

## Questions

**Q1 (exact constants).** Does the inventory in 5 miss a regime the note claims (e.g. a tied truth constraint together with a partially tied free block whose worse coordinates are NOT spectators in the sense of `specd > 0`; or `β = 0`/`η = 0` endpoints; or two vanishing fibre constraints)? If so, state the missing theorem precisely.

**Q2 (the polyhedral criterion).** Is the general form of 4 (`∫ 1_{z_j ≤ log ρ (j ∈ I)} e^{b·z} exp(-c e^{κ·z}) dz < ∞ ⇔ b·d < 0 for every nonzero recession direction d with d_j ≤ 0 (j ∈ I), κ·d ≤ 0`) worth a bounded formalisation round now, given that under a strict truth constraint only the single-scale case can be integrable, or is it an ornament?

**Q3 (what the note still claims).** Given the section list, which claims of the note are, in your judgement, not yet covered by the formalised layer as described across rounds 1–14 (active-truth face theorems, wall crossing and the S14 push-forward, mixed truths, general-truth export, identifiability results in earlier rounds), and which of them are formalisable in bounded rounds? Please be concrete: name the claim, the theorem shape, the likely obstruction.

**Q4 (ranking).** Rank the next 3–5 bounded rounds with a one-line rationale each.
