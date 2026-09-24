# Consult: germbij analytic layer, seventh research round (after research_round6)

Same setting (Lean 4 + Mathlib, laplace `Laplace.Multi`, mirrored on hironaka `wall-atlas`). Landed since round 6:

1. **What the leading expectations know** (`ExpectationValuesKnow.lean`): `TermMeasureCertificate.normalise_restrict_eq_iff_forall_tendsto` — for two certified phases and a reference observable `χ` vanishing off the open region `L'` with positive leading integrals, the leading fibre expectations of every observable vanishing off `L'` agree **iff** the normalised leading measures restricted to `L'` agree (the converse direction via `∫ψ dμ = ∫ψ d(μ|L')` for such ψ and `ratio_eq_of_normalise_eq` on the restrictions).

2. **The degenerate face, complete** (`DegenerateFace.lean`): `tendsto_degI : Tendsto (fun t ↦ t^4/log t * (degI t).toReal) atTop (𝓝 1)` for `degI t = ∫⁻_{(0,1)³} 1_{xyz > t^{-2}} z² e^{-t³xyz²}` (iterated `lintegral`). Route exactly as you proposed: `xy` collapse with density `−log s` (Tonelli on the triangle); scaling `u = ts, v = tz` (`I = t^{-4} J`, `J = ∫_{(0,t)²} (log t − log u) 1_{uv>1} v² e^{-uv²}`); `w = uv²` (inner integrand `1_{w>v} e^{-w}` on `0 < w < v²t`, log weight `log t − log w + 2 log v`); divide by `log t`; dominated convergence on the plane with the bound `1_{0<v<w}(1 + 3w + 2w^{-1/2} + 4v^{-1/2}) e^{-w}` (from `|log v| ≤ v + 2/√v` and `v < w`), whose integral is finite by three Gamma integrals (the inner `v`-integral is `(w + 3w² + 10√w) e^{-w}` exactly); limit `∫_0^∞∫_v^∞ e^{-w} = 1`. Numerics: 0.70, 0.78, 0.83, 0.86 at `t = 10², …, 10⁵` (≈ `1 − 1.56/log t`).

## Statements (Lean, verbatim)

```lean
noncomputable def degIntegrand (t x y z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ioi (t ^ (-2 : ℝ))).indicator (fun _ ↦ (1 : ℝ)) (x * y * z) *
    (z ^ 2 * exp (-(t ^ 3 * (x * y * z ^ 2)))))


noncomputable def degI (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1, degIntegrand t x y z


theorem tendsto_degI : Tendsto (fun t ↦ t ^ 4 / log t * (degI t).toReal) atTop (𝓝 1) := by
  have h := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp tendsto_degN

theorem lintegral_unitSquare_mul {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1, G (x * y) =
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (-log s) * G s := by
  have h1 : ∀ y ∈ Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1, G (x * y) =
-
theorem degJ_eq_subst (t : ℝ) :
    degJ t = ∫⁻ v in Ioo (0 : ℝ) t, ∫⁻ w in Ioo (0 : ℝ) (v ^ 2 * t),
      ENNReal.ofReal (log t - log w + 2 * log v) * degM v w := by
  unfold degJ
-
theorem degΦ_le_degΨ {t : ℝ} (ht : exp 1 ≤ t) (p : ℝ × ℝ) : degΦ t p ≤ degΨ p := by
  have hlt : 1 ≤ log t := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (exp_pos 1) ht
-
theorem lintegral_degΨ_inner {w : ℝ} (hw : 0 < w) :
    ∫⁻ v, degΨ (v, w) = ENNReal.ofReal ((w + 3 * w ^ 2 + 10 * √w) * exp (-w)) := by
  have e : ∀ v, degΨ (v, w) = (Ioo (0 : ℝ) w).indicator (fun v ↦ ENNReal.ofReal
      ((1 + 3 * w + 2 * w ^ (-(1 / 2 : ℝ)) + 4 * v ^ (-(1 / 2 : ℝ))) * exp (-w))) v := by

theorem normalise_restrict_eq_iff_forall_tendsto (hL' : IsOpen L')
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁) (hσ₁ : σ₁ ≠ 0)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂) (hσ₂ : σ₂ ≠ 0)
    {χ : (Fin (m + 1) → ℝ) → ℝ} (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ}
    (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hpos₁ : 0 < ∫ z, χ z ∂C₁.leadingMeasure) (hpos₂ : 0 < ∫ z, χ z ∂C₂.leadingMeasure) :
    normaliseMeasure (C₁.leadingMeasure.restrict L') =
        normaliseMeasure (C₂.leadingMeasure.restrict L') ↔
      ∀ ψ : (Fin (m + 1) → ℝ) → ℝ, Continuous ψ → (∀ z, 0 ≤ ψ z) → (∃ M, ∀ z, ψ z ≤ M) →
        (∀ z, ψ z ≠ 0 → z ∈ L') →
        Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
          (𝓝 0) := by
  constructor
  · intro hnorm ψ hψc hψ ⟨M, hM⟩ hψL
```

## Questions

1. **Audit** the two results above (the example's chain of identities and the bound, and the iff).

2. **The general theorem behind the example.** The example's logarithm comes from the product-fibre factor `−log s` of a coordinate pair `(x, y)` on which the optimal face is a segment, with the truth constraint active. Give the exact general statement to formalise next, in the model-kernel conventions of the seabed: model kernel `K(t) = A t^{-γp} ∫_{box} W(x, v_t) ∏ x^r e^{-B t^δ a(x, v_t) ∏ x^κ} dx` on the domain `D t^{-γ/q} ∏ x^{-Q/q} < ρ` (cutoff variable `v_t = D t^{-γ/q} ∏ x^{-Q/q}`, truth constraint `Q·α ≤ γ`, loss constraint `κ·α ≥ δ`, objective `(r+1)·α`). What is the right hypothesis package — "the LP optimal set is a face of dimension `k` on which both constraints are active, with the active constraints' normals independent" — and what is the normalisation `t^{λ}/(log t)^{k}` and the limiting measure (which coordinates are integrated, which are scaled, what density on the face)? Is the `k` for the general case `dim(Opt)` (affine dimension of the optimal set) or is there a subtlety with the truth truncation (the domain is `Q·α < γ` strictly, and the face may lie on the boundary of the truncation)? Is there a reduction of the general active-truth case to the `Q = 0` partially tied theorem by a substitution (the example's `u = ts, v = tz` then `w = uv²` looks like a change of the scaled coordinates that moves the truth constraint into the exponential) — if so, state the substitution generally, since then the theorem would follow from `tendsto_modelKernel_partial` plus an exact fibre-factor identity rather than a new dominated-convergence argument. Please give the answer as a theorem statement (hypotheses, normalisation, limit), plus the two-line reason for each piece.

3. **Ranking** of what remains: (a) the general active-truth theorem of Q2; (b) general-truth hironaka export (resolve `F·T`); (c) variable-unit partial faces with moving parameters (you suggested a frozen-unit perturbation squeeze; the existing hypotheses give only pointwise face continuity, so it needs a localisation step — is it still worth it?); (d) compact-uniform packaging; (e) anything new. Say what to skip.
