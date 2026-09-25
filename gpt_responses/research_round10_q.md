# Consult: germbij analytic layer, tenth research round (after research_round9)

Same setting (Lean 4 + Mathlib, laplace `Laplace.Multi`, mirrored on hironaka `wall-atlas`). All four items of your round-9 order are landed, sorry-free:

1. **Exact trace model** `W = w(u)`, `a = a(u)` (`ActiveTruthTraceTheorem.lean`, `tendsto_modelKernel_trace`), with the `h ↔ u` identity `∫_{h>h₀} e^{-ηh} f(u(h)) dh = q C^{-qη} ∫_0^ρ u^{qη−1} f(u) du` isolated (`integral_Ioi_truthOf`, no integrability hypothesis).
2. **Weighted fibre limit** (`ActiveTruthFibreWeighted.lean`, `tendsto_lintegral_fibre_weighted`): `L^{-k}∫_{fibreSet_L(v)} Φ(ρe^{-z(z')}) dz' → Φ₀ vol(F')` for bounded measurable `Φ` with `Tendsto Φ (𝓝[(0,ρ)^n] 0) (𝓝 Φ₀)`. The a.e. positivity of the reconstructed coordinates you asked for turned out to be exactly the existing nondegeneracy `(c_j, a_j) ≠ (0,0)` (null hyperplanes `{c_j·w = a_j}`, `{w_i = 0}`).
3. **General trace replacement** (`ActiveTruthGeneral.lean`, `tendsto_modelKernel_general`): jointly measurable `W(x,u)`, `a(x,u)`, `0 ≤ W ≤ W_*`, `a ≥ a_- > 0`, traces `W_tr, a_tr` (measurable, same bounds on `(0,ρ)`) as `x → 0` inside the box for each `u ∈ (0,ρ)`; limit `A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ∫_0^ρ u^{qη−1} W_tr a_tr^{-β}`.
4. **The chart wrapper** (`ActiveTruthChart.lean`):

```lean
/-- The density of the active-truth measure on the truth segment, before the cut. -/
noncomputable def activeTruthDensityFn (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) (u : ℝ) : ℝ :=
  P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
    D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConst i γ e *
    (u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
      ((P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)|) *
        |P.a i (D.bridgePt i ε b 0 u)| ^ (-β)))
-- faceConst i γ e = vol(facePolytope (kappa i ∘ e) (Qexp i ∘ e) δ γ).toReal / |det (transMat (kappa i ∘ e) (Qexp i ∘ e))|
-- activeTruthDensity = (Ioo 0 ρ).indicator activeTruthDensityFn
noncomputable def activeTruthMeasure … : Measure (Fin (m + 1) → ℝ) :=
  (volume.withDensity fun u ↦ ENNReal.ofReal (P.activeTruthDensity i ε b σ γ β η e u)).map
    (fun u ↦ D.rep i (D.bridgePt i ε b 0 u))

theorem tendsto_modelKernelOf_activeTruth (e : Fin k ⊕ Fin 2 ≃ Fin m) (hσ : σ ≠ 0)
    (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ P.phaseExp i γ) (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0)
    (hc₀ : fibreCoef (P.kappa i ∘ e) (D.Qexp i ∘ e) 0 ≠ 0 ∨ fibreA (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ 0 ≠ 0)
    (hc₁ : … 1 …)
    (hr : ∀ j, P.rExp i (e j) + 1 = β * P.kappa i (e j) - η * D.Qexp i (e j))
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + (β * P.phaseExp i γ - η * γ)) / log t ^ k *
        P.modelKernelOf i φ ε b t γ σ) atTop (𝓝 (∫ x, φ x ∂(P.activeTruthMeasure i ε b σ γ β η e)))

noncomputable def TermData.activeTruth … : P.TermData σ γ p   -- (γp + βδ − ηγ, k, activeTruthMeasure)
```
(`bridgePt i ε b x v = insertNth (k i) (±v) (ε·x)` is the chart point; the `k i`-th chart coordinate is the truth coordinate. `TermData` is the seabed's per-term certificate: a power, a log order and a finite measure with the limit against every continuous nonnegative bounded observable supported in `L'`.) **So the leading measure of an active-truth chart lives on the truth segment `u ↦ rep(0,…,±u,…,0)`, not at `rep 0`** — your round-8 statement; my round-9 framing ("observables of the active coordinates only") was wrong because the chart coordinate `u_{k}` IS the truth coordinate. The units were extended off the model domain by `max(|a|, m_a)` (the kernel cannot see it) to meet the global lower bound.

## Questions

1. **Audit** `tendsto_modelKernelOf_activeTruth` / `TermData.activeTruth` as stated: the power `γp + βδ − ηγ` with `δ = phaseExp i γ = 1 − γν`, the log order `k`, the density (in particular `A = constA = |σ|^p/q_k`, `B = constB = |σ|^ν`, `D = constD = |σ|^{1/q_k}`, the factor `q = q_k` and `D^{-qη}`), and the support. Is the measure the one your (LM) predicts for `I = ∅` (the "`v^{qη−1} dv` on `0 < v < ρ`" pushed through the chart trace), and is the dependence on `σ` right (`|σ|^{p − νβ − η}`-type scaling)? Anything missing for the certificate interface (positivity is automatic here since `A ≥ 0`)?

2. **Nonemptiness / nonvanishing.** The theorem is stated without assuming the face has a positive point, so the limit may be `0` (`vol(F') = 0`) — then the certified `(lam, k)` is not the true order. For the interface (`TermMeasureCertificate.ofTerms` takes the minimum `lam` and the max `k` at that `lam`), is a zero measure at a wrong `(lam, k)` harmful? (I believe the certificate's `lam₀/k₀` bookkeeping only needs the limits to hold, and a zero-measure term at a lower `lam` would wrongly lower `lam₀`.) So I plan a lemma `0 < vol(F') ↔ ∃ w > 0, c_j·w < a_j` under nondegeneracy, and to require the positive point in the chart wrapper. Agree? Is the right hypothesis "the face `{α ≥ 0 : κ·α = δ, Q·α = γ}` has a point with all `α_j > 0`" (stated on the original coordinates, then transported through `e`)?

3. **Ranking for the next rounds.** Candidates: (a) spectators with traces + the chart wrapper for charts with spectator coordinates (`Fin m' ⊕ (Fin k ⊕ Fin 2) ≃ Fin m`), reusing the outer DCT of `ActiveTruthSpectator` — the units then depend on `(y, x_J, u)` and the trace is `W(y, 0, u)`; (b) the LP interface: from `lpOptimal_activeTruth_iff` and the certificate `(β, η)`, derive the chart hypotheses (`hr`, nondegeneracy) from the phase data — i.e. a theorem "if the LP of the chart has a dual certificate with positive multipliers and a nondegenerate optimal face, then `TermData.activeTruth` applies"; (c) coordinate independence of `faceConst` (change of solved pair); (d) the example identification `modelKernel(example) = (degI t).toReal`; (e) the `c_j = a_j = 0` case (face in a coordinate hyperplane; keep the transverse half-plane indicator); (f) a "moving parameter" version (σ → σ₀) as for the tied term (`tendsto_termKernel_tied_param`), needed by the note's parameter-stability results; (g) the general-truth Hironaka export. Please rank with one-line rationales and, for the top item, the statement you would write.

4. **One technical question for (a).** With spectators `y ∈ (0,ρ)^{m'}` and general units `W(y, x_J, u)`, the frozen-`y` kernel has units `W_y(x_J, u) := W(y, x_J, u)` and the inner theorem applies pointwise in `y` with traces `W(y, 0, u)`; the outer DCT needs the uniform bound of `ActiveTruthUniform` (`normalised_lintegral_le`) generalised from constant units to general units — it holds with `W_*` in place of `w₀` (the same proof: `ampG ≤ W_* e^{-c₀ a_- e^{-s}}`). Is there any obstacle to also letting the spectator density be general (units depending on `y` through `wt |b|` and `|a|` at `(y, 0, u)`), i.e. is the limit `∫_{(0,ρ)^{m'}} ∏ y^{d−1} ∫_0^ρ u^{qη−1} W_tr(y,u) a_tr(y,u)^{-β} du dy` with `W_tr(y,u) = φ(rep(y,0,±u)) (wt|b|)(y,0,±u)` correct as stated, with no extra continuity in `y`?

Please be specific and concise.
