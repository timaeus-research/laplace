# Tide `ambient-moments` (seabed: laplace, off main after tide gibbs-rotation) — candidates v1

Context. Tide `gibbs-rotation` proved the frame-independence of Gibbs moments for `A w = Qᵀ(w − c)` and transported E2's per-direction results
to the note's `w`-frame *along the columns of `Q`* (observables `(Aw)ᵢ`). What the note reports besides those projections: "the relative
Frobenius error of the whole covariance", "the posterior mean shift", and E2's first panel "relative error of the four Laplace predictions
(eq:cov)…(eq:covK) against exact quadrature … for the covariance at `a = 0.5`, `2.7×10⁻²` at `t = 10`". These are statements about the
*ambient* mean vector `⟨w⟩` and covariance matrix `Cov_w[wⱼ, wₖ]`, which are linear combinations of the projected moments:
`w − c = Q A(w)`, so `⟨w⟩ − c = Q⟨u⟩` and `Cov_w = Q diag(Var_uᵢ) Qᵀ` (the `u`-covariance is diagonal by separability).

Seabed (Lean 4 / Mathlib, all proved). `Laplace.Multi.gibbsExpectation L t φ = (∫ φ e^{−tL})/Z`, `gibbsCov L t φ ψ = ⟨φψ⟩ − ⟨φ⟩⟨ψ⟩` (totalised
Bochner integrals). `affineFrame Q c w = Qᵀ *ᵥ (w − c)`, `rotated Q c L = L ∘ affineFrame`, `gibbsExpectation_rotated`/`gibbsCov_rotated`
(frame independence), `integral_comp_affineFrame` (change of variables, from `integral_comp_mulVec` and translation invariance),
`integrable_comp_mulVec_iff (M) (hM : det ≠ 0) (g) (hg : AEStronglyMeasurable g) : Integrable (g ∘ (M *ᵥ ·)) ↔ Integrable g`.
`gibbsCov_separableAnharmonic : Cov_u[uᵢ, uⱼ] = δᵢⱼ Var_{ℓᵢ}`, `separableAnharmonic_var_relative_rate_note : t(λᵢ t Var − 1) → a² − ½`,
`separableAnharmonic_mean_asymptotic : t⟨uᵢ⟩ → −αᵢ/(2λᵢ²)`, `integrable_pow_mul_exp_neg_t_anharmonic`, `Integrable.fintype_prod`,
`sum_sq_conj : ∑ᵢⱼ (UᵀAU)ᵢⱼ² = ∑ᵢⱼ Aᵢⱼ²`, `sum_sq_diagonal`, `frobenius_inv`.

Candidates.

A. **Bilinearity of the Gibbs moments under integrability** (`gibbsExpectation_sum`, `gibbsExpectation_const_mul`, `gibbsCov_sum_left`,
   `gibbsCov_smul_left`, symmetric versions): `⟨∑ᵢ aᵢ φᵢ⟩ = ∑ᵢ aᵢ⟨φᵢ⟩` and `Cov[∑ᵢ aᵢφᵢ, ψ] = ∑ᵢ aᵢ Cov[φᵢ, ψ]` whenever `φᵢ e^{−tL}`, `φᵢ ψ e^{−tL}`
   are integrable (linearity of the Bochner integral; `Z` cancels).
B. **Integrability transport for the rotated oscillator** (`integrable_rotated_coord`, `integrable_rotated_coord_mul`): the coordinates `(Aw)ᵢ`
   and their products `(Aw)ᵢ(Aw)ⱼ`, times `e^{−t L(Aw)}`, are integrable on `ι → ℝ` — from the separable integrability
   (`∏ₖ (xₖ^{eₖ} e^{−tℓₖ(xₖ)})` via `Integrable.fintype_prod`) through the change of variables (`integrable_comp_mulVec_iff` with `M = Qᵀ` plus
   translation, or directly `MeasurePreserving`).
C. **Ambient mean and covariance of the note's `anharm` potential** (`gibbsExpectation_coord_rotatedAnharmonic`,
   `gibbsCov_coord_rotatedAnharmonic`): `⟨wⱼ⟩ − cⱼ = ∑ᵢ Qⱼᵢ ⟨uᵢ⟩_{ℓᵢ}` and `Cov_w[wⱼ, wₖ] = ∑ᵢ Qⱼᵢ Qₖᵢ Var_{ℓᵢ}`, i.e. `Cov_w = Q diag(Var) Qᵀ` as a
   matrix; asymptotics `t(⟨wⱼ⟩ − cⱼ) → −∑ᵢ Qⱼᵢ αᵢ/(2λᵢ²)` (`rotatedAnharmonic_ambient_mean_asymptotic`).
D. **E2's first panel in Frobenius form** (`frobenius_rel_laplace_separable`, `frobenius_rel_laplace_rotated`): with `S = diag(1/(λᵢt))` (the
   Laplace covariance `P⁻¹`, `P = t diag(λ)`) and `S_w = Q S Qᵀ`, `t² ∑ⱼₖ (Cov_w − S_w)ⱼₖ² / ∑ⱼₖ (S_w)ⱼₖ² = ∑ᵢ (λᵢ t Varᵢ − 1)²/λᵢ² / ∑ᵢ 1/λᵢ² · …`
   hmm — precisely: `∑ᵢⱼ (Cov_w − S_w)² = ∑ᵢ (Varᵢ − 1/(λᵢt))²` and `∑(S_w)² = ∑ᵢ 1/(λᵢt)²`, so the ratio is
   `∑ᵢ (λᵢtVarᵢ − 1)²/λᵢ² / ∑ᵢ 1/λᵢ²`, and since every `t(λᵢtVarᵢ − 1) → a² − ½`, `t² · ratio → (a² − ½)²`: **the relative Frobenius error of the
   Laplace covariance prediction is `|a² − ½|/t + o(1/t)`, independent of the spectrum** — E2's `2.7×10⁻²` at `t = 10` against `0.025`.

Numerical check done (`numcheck46.py`, `d = 4`, `λ = (1, 2, 5, 10)`, `a = ½`): `t · ‖Cov − S‖_F/‖S‖_F = 0.2655, 0.2526, 0.2503` at
`t = 10, 100, 1000` (→ 0.25); in a random frame `Q`, `t‖Cov_w − S_w‖_F/‖S_w‖_F` identical; `t(⟨w⟩ − c) = Q(t⟨u⟩)` to 1e-14 and close to
`−Q(αᵢ/(2λᵢ²))`.

Questions. (1) Is A–D correct, in particular D's claim that the relative Frobenius error's leading term is spectrum-independent because every
direction has the same relative error (a weighted mean of identical limits)? (2) For B, which route is least painful in Lean: (i) push the
separable integrability through `integrable_comp_mulVec_iff` with `M = Qᵀ` and a translation (`Integrable.comp_sub_right`), or (ii) prove
`MeasurePreserving (affineFrame Q c) volume volume` once and use `MeasurePreserving.integrable_comp` — and does the latter need the map to be
a `MeasurableEquiv`? (3) Is there a cleaner formulation of D — e.g. as a Tendsto of `t² · (∑(Cov_w − S_w)²)/(∑ S_w²)` to `(a² − ½)²`, or via the
weighted-mean lemma `weighted_mean_le_of_monovary`-style bounds — and should D also be stated against `Σ_ULA` (no: E2 compares the *Laplace*
prediction to exact quadrature)? Please end with a vote on the subset A–D.
