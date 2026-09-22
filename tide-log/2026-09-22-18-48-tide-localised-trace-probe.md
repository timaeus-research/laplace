# Tide: localised-trace-probe

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); GPT's next target after tide 80: the invariant centred quadratic-probe theorem
`−∂ₜ tr(B C(t)) = tr(BH⁻¹)/t² + 2tr(BV)/t³ + O(t⁻⁴)` with the exact bridge to `Cov_loc(L, (w − m(t))ᵀB(w − m(t)))`.
**Seabed:** laplace, commit ff25c69 (worktree `laplace-tide-localised-trace-probe`, branch `tide/localised-trace-probe` off `main`)
**Started:** 2026-09-22T18:50Z

## Candidates v1 (Claude)

Setting (E2, as in tides 68–80): the rotated separable anharmonic family `L∘A` (`A(w) = Qᵀ(w − c)`, `QᵀQ = 1`, `H = Q diag(λ) Qᵀ`,
`αᵢ² < 3λᵢγᵢ`), the isotropic localiser `g ≥ 0` with anchor `w₀`, all parameters fixed, `t → ∞`. Frame coordinates `uᵢ = (Qᵀ(w − c))ᵢ`,
`μᵢ(t) = ⟨uᵢ⟩_loc`, `m(t) = ⟨w⟩_loc = c + Qμ(t)`, `C(t)ⱼₖ = Cov_loc(wⱼ, wₖ)` the centred covariance. `B` any real `d × d` matrix,
`B̃ = QᵀBQ`. Tide 80 gave `Dᵢ(t) := Cov_loc[L∘A, uᵢ²] − 2μᵢ Cov_loc[L∘A, uᵢ] = −∂ₜ Var_loc(uᵢ)` exactly, `Cov_loc(uᵢ, uⱼ) = 0` (`i ≠ j`),
and `t² Dᵢ = 1/λᵢ + 2vᵢ/t + O(t⁻²)` with `vᵢ = varLocCoeff2ᵢ = c₂',ᵢ − cᵢ²`; `V := Q diag(vᵢ) Qᵀ`.

**A. The trace probe's exact derivative.** For every `B`, `s ↦ ∑ⱼₖ Bⱼₖ Cov_loc,s(wⱼ, wₖ)` (`= tr(B C(s))`, `C` symmetric) is differentiable
on `(0, ∞)` with
`−d/dt ∑ⱼₖ Bⱼₖ Cov_loc(wⱼ, wₖ) = ∑ᵢ B̃ᵢᵢ Dᵢ(t)`, `B̃ᵢᵢ = ∑ⱼₖ Qⱼᵢ Bⱼₖ Qₖᵢ`.
Lean: `hasDerivAt_localised_trace_cov` (from tide 80's `hasDerivAt_localised_cov_coord` by `HasDerivAt.fun_sum` twice, then the double
sum swap) and `trace_cov_eq : ∑ⱼₖ Bⱼₖ Cov(wⱼ, wₖ) = Matrix.trace (B * Matrix.of (fun j k => Cov(wⱼ, wₖ)))` (via `gibbsCov_comm`).

**B. The exact bridge to the centred quadratic probe.** With `m = m(t)` frozen,
`Cov_loc,t(L∘A, w ↦ ∑ⱼₖ Bⱼₖ (wⱼ − mⱼ)(wₖ − mₖ)) = ∑ᵢ B̃ᵢᵢ Dᵢ(t) = −∂ₜ tr(B C(t))`.
Route: `mⱼ = cⱼ + ∑ᵢ Qⱼᵢ μᵢ` (new `localised_mean_coord`, from `coord_eq_sum_affineFrame` + expectation linearity), so pointwise
`w − m = Q(u − μ)` and the probe is `∑ᵢᵢ' B̃ᵢᵢ' (uᵢ − μᵢ)(uᵢ' − μᵢ')` (matrix algebra: `(Q y) ⬝ (B (Q y)) = y ⬝ (QᵀBQ y)`); bilinearity of
`gibbsCov` in the probe (`gibbsCov_finsetSum_left` + `gibbsCov_comm`, `gibbsCov_const_mul_left`, `gibbsCov_const_add_left`) reduces to
`Cov(L∘A, uᵢuᵢ') − μᵢ' Cov(L∘A, uᵢ) − μᵢ Cov(L∘A, uᵢ')`, which is `0` for `i ≠ i'` (tide 80's `centred_pair_offdiag_zero`) and `Dᵢ` on the
diagonal. Statement on the rotated measure; integrability of `L∘A × frame polynomials` from tides 76–80's `locFamily` lemmas.

**C. Second order (the invariant statement).** For every `B`:
`|t² (−∂ₜ tr(B C(t))) − tr(B H⁻¹) − 2 tr(B V)/t| ≤ K/t²` eventually, `tr(B H⁻¹) = ∑ᵢ B̃ᵢᵢ/λᵢ`, `tr(B V) = ∑ᵢ B̃ᵢᵢ vᵢ`,
i.e. `−∂ₜ tr(B C(t)) = tr(BH⁻¹)/t² + 2 tr(BV)/t³ + O(t⁻⁴)` — and by B the same expansion for `Cov_loc(L∘A, (w − m)ᵀB(w − m))`.
Lean: tide 80's `localisedVar_neg_deriv_order2_rate` + `sum_rate_div_sq` with weights `B̃ᵢᵢ`, plus `trace_mul_conj_diagonal :
tr(B (Q diag(a) Qᵀ)) = ∑ᵢ (QᵀBQ)ᵢᵢ aᵢ`. Corollaries: `B = 1`: `−∂ₜ tr C(t) = tr H⁻¹/t² + 2 tr V/t³ + O(t⁻⁴)`; `B = H`:
`−∂ₜ tr(H C(t)) = d/t² + 2(∑ᵢ λᵢvᵢ)/t³ + O(t⁻⁴)` (the Gaussian quadratic energy `½(w − m)ᵀH(w − m)` has `Cov_loc(L∘A, ·) = d/(2t²) +
(∑λᵢvᵢ)/t³ + O(t⁻⁴)`).

(Not proposed: the relative form `2tr(BV)/(t·tr(BH⁻¹))` needs `tr(BH⁻¹) ≠ 0`; record as a remark for `B` PSD nonzero.)

Sizing: A ~120 lines, B ~250 (mean transport + probe algebra + bilinearity), C ~120 with corollaries. Target A + B + C.

## Numerical check

`numcheck_localised_trace_probe.py` (2D, rotation `θ = 0.6`, `B = [[1, .4], [.4, 2]]`, anchor off the minimum): (a) at `t = 40`,
`−d/dt tr(BC)` by central differences, `Cov_loc(L, (w − m)ᵀB(w − m))` by 2D quadrature, and the frame reduction `∑ᵢ B̃ᵢᵢDᵢ` all equal
`0.0016345576`; (b) `tr(BH⁻¹) = 2.75499598`, `2tr(BV) = −5.78970515`; `t·(t²(−∂ₜ tr BC) − tr BH⁻¹) = −5.690, −5.740, −5.765, −5.777` at
`t = 80, 160, 320, 640`, and `t²·(… − 2tr(BV)/t) ≈ 7.99, 7.94, 7.91, 7.89` (bounded).

## GPT-6 Astra v1

Verbatim in `gpt_localised_trace_probe_v1.md` (prompt: `gpt_localised_trace_probe_prompt_v1.md`). Summary: **A, B, C correct; no
mathematical error.** No symmetry assumption on `B` (everything depends on `sym B`; `C`, `H⁻¹`, `V` symmetric); the trace
identification `tr(BC) = ∑ⱼₖ BⱼₖCⱼₖ` and `(QᵀBQ)ᵢᵢ = ∑ⱼₖ QⱼᵢBⱼₖQₖᵢ` are right; keep `B, Q, c, g, w₀` fixed in `t` (a `t`-dependent
localiser would add a score term); constants may depend on `B`. Route for B: **the frame route** given the landed API — prove
`localised_mean_coord`, the pointwise centred-coordinate transport, a **centred-frame-pair lemma**
`Cov_t(L, (uᵢ − μᵢ)(uⱼ − μⱼ)) = Dᵢ (i = j), 0 (i ≠ j)`, then expand the quadratic into finite scalar sums; isolate
`trace_mul_conj_diagonal` as reusable algebra. The frozen-probe route is mathematically fine (extra term
`(m(s) − m)ᵀB(m(s) − m)` has zero derivative at `s = t`, also for nonsymmetric `B`) but needs derivative support for a moving
probe — do not apply the fixed-observable derivative theorem to `ψ_{m(s)}`. Wording: say "**B-weighted centred covariance trace**",
not "centred second moment"; for `B = H` state both `−∂ₜ tr(HC) = d/t² + 2∑λᵢvᵢ/t³ + O(t⁻⁴)` and, for the frozen centred Gaussian
quadratic energy `Eₜ = ½(w − m)ᵀH(w − m)`, `Cov_t(L∘A, Eₜ) = d/(2t²) + ∑λᵢvᵢ/t³ + O(t⁻⁴)`; the expansion follows from the derivative
estimates, not from differentiating `C = S + O(S²)`. **Next target**: the Frobenius discrepancy from the Gaussian-prior covariance:
`C(t) − S(t) = (V + gH⁻²)/t² + O(t⁻³)` gives `| ‖C(t) − S(t)‖_F² − ‖V + gH⁻²‖_F²/t⁴ | ≤ K/t⁵`, coefficient `∑ᵢ (vᵢ + g/λᵢ²)²`.
Raw second moments are less invariant (mean-drift terms); third-cumulant derivatives need new moment machinery.

## Vote
- Claude: A + B + C (corollaries `B = 1`, `B = H`, and the centred quadratic Cov form)
- GPT-6 Astra: "**Vote: A+B+C.** … Commit A+B+C; if time tightens, cut specialised corollaries before cutting B."

## Result

Commit `dbefb28` on `tide/localised-trace-probe`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/LocalisedTraceProbe.lean` (     616 lines).
A + B + C as voted (GPT: "Commit A+B+C; if time tightens, cut specialised corollaries before cutting B"); all corollaries kept.
Algebra: `sumsum_conj` (`∑ⱼₖ Bⱼₖ(Qy)ⱼ(Qy)ₖ = ∑ᵢᵢ' (QᵀBQ)ᵢᵢ' yᵢyᵢ'` via the `dotProduct`/`mulVec` API), `sum_sum_eq_trace`,
`conj_diagonal_entry`, `conj_diagonal_transpose`, `trace_mul_conj_diagonal`, `sum_sum_conj_diag`, `conj_conj`,
`sum_sum_cov_eq_trace`. Defs `locFrameMean`, `locCentredD`.
A: `hasDerivAt_localised_trace_cov`. B: `localised_mean_coord`, `coord_sub_mean_eq`, `gibbsCov_energy_centred_pair_locFamily`,
`localisedCovK_centred_pair` (the centred frame pair covariance: `Dᵢ` on the diagonal, `0` off it),
`localisedCovK_centred_quadratic_eq` (the bridge). C: `localised_centredD_weighted_order2_rate`,
`localisedTraceCov_neg_deriv_order2_rate`, `localisedCovK_centred_quadratic_order2_rate`,
`localisedTotalVar_neg_deriv_order2_rate` (`B = 1`), `localisedTraceCov_hessian_neg_deriv_order2_rate` and
`localisedCovK_hessian_centred_quadratic_order2_rate` (`B = H`, leading coefficient `d`).

Surprises: the trace algebra is cleanest through `Matrix.trace_mul_comm` on the conjugated diagonal rather than nested
`Finset.sum_comm`; the quadratic-form conjugation is five named `dotProduct`/`mulVec` rewrites. The frame family's partition
function is nonzero as a product of the 1D ones (`partitionFunction_separable` + `partitionFunction_locFamily_ne`).
