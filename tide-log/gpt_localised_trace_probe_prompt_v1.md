You are consulted (one round) on tide 81 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders `≤ K/t^n` for `t ≥ T ≥ 1`.

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

## Seabed facts available (names of Lean theorems, all landed)
- tide 80 (`Laplace/Multi/LocalisedCentredDerivative.lean`): `hasDerivAt_localised_frame_pow` (d/ds ⟨uᵢ^m⟩_loc(s) = −Cov_loc,t[L∘A, uᵢ^m]),
  `hasDerivAt_localised_frame_var`, `localisedVar_frame_eq_neg_deriv`, `centred_pair_offdiag_zero` (Cov[L∘A,uᵢuⱼ] − μⱼCov[L∘A,uᵢ] −
  μᵢCov[L∘A,uⱼ] = 0, i ≠ j), `hasDerivAt_localised_cov_coord` (d/ds Cov_loc(wⱼ,wₖ) = −∑ᵢ QⱼᵢQₖᵢ Dᵢ), `localisedVar_neg_deriv_order2_rate`
  (|t² Dᵢ − 1/λᵢ − 2vᵢ/t| ≤ K/t²), `localisedCov_neg_deriv_order2_rate` (entrywise second order in physical coordinates).
- tides 68/76/79: `localisedRotatedAnharmonic_cov_frame` (Cov_loc(uᵢ,uᵢ') = if i = i' then Var_loc,ᵢ else 0), `_cov_coord`,
  `localisedCovK_frame_coord/pair` (Cov_loc[L∘A, uᵢ^m] in the 1D family; Cov_loc[L∘A,uᵢuⱼ] = μⱼCov[L∘A,uᵢ] + μᵢCov[L∘A,uⱼ]),
  `localised_frame_coord_expectation`, `localisedRotated_gibbsCov_eq`/`_gibbsExpectation_eq` (rotation transport with pinned probe),
  `coord_eq_sum_affineFrame` (wⱼ = cⱼ + ∑ᵢ Qⱼᵢ uᵢ(w)), `gibbsCov_comm`, `gibbsCov_finsetSum_left`, `gibbsCov_const_mul_left`,
  `gibbsCov_const_add_left`, `gibbsCov_linear_combination`, `gibbsExpectation_finsetSum_of_integrable`, `gibbsExpectation_const_mul`,
  `gibbsExpectation_const_of_ne_zero`, `conj_diagonal_inv_apply` ((Q diag(1/λ) Qᵀ)ⱼₖ = ∑ᵢ QⱼᵢQₖᵢ/λᵢ), `sum_rate_div_sq` (finite weighted
  sums of `≤ K/t²` rates), tide 74's `varLocCoeff2` (= c₂' − c² with closed form α²/λ⁴ − gx₀α/λ³ − g/λ² − γ/(2λ³)).

## Numerical check (done; 2D, rotation θ = 0.6, B = [[1, .4],[.4, 2]], λ = (1.3, .9), α = (.7, −.4), γ = (1.1, .8), g = .8, anchor off-minimum)
(a) t = 40: −d/dt tr(BC) by central differences = 0.0016345576; Cov_loc(L, (w−m)ᵀB(w−m)) by 2D quadrature = 0.0016345576; the frame
reduction ∑ B̃ᵢᵢDᵢ = 0.0016345576.
(b) tr(BH⁻¹) = 2.75499598, 2tr(BV) = −5.78970515; t·(t²(−∂ₜtr BC) − tr BH⁻¹) = −5.690, −5.740, −5.765, −5.777 at t = 80, 160, 320, 640;
t²·(… − 2tr(BV)/t) ≈ 7.99, 7.94, 7.91, 7.89 (bounded).

## Questions
1. Are A, B, C correct as stated for a general (not necessarily symmetric) matrix B? Any hidden hypothesis (e.g. on the anchor, on B)?
   Is identifying ∑ⱼₖ Bⱼₖ Cov(wⱼ,wₖ) with tr(B C) fine given C symmetric (tr(BC) = tr(BᵀC))?
2. For the bridge B: is the frame-reduction route (pointwise w − m = Q(u − μ), bilinearity, tide 80's off-diagonal vanishing) the cleanest
   Lean route, or is the "frozen probe" route (−∂ₛ⟨ψ_m⟩ₛ|ₛ₌ₜ = Cov_t(L, ψ_m) with ⟨ψ_m⟩ₛ = tr(BC(s)) + (m(s) − m)ᵀB(m(s) − m), whose extra term has
   zero derivative at s = t) better? Any pitfall in either?
3. Wording against the note (its eq:cov is the centred covariance C = S + O(S²), S = (tH + gI)⁻¹; E3 reads the localiser as a Gaussian
   prior): is "for every probe matrix B the negative time-derivative of the B-weighted centred second moment tr(BC(t)) equals the energy
   covariance of the centred quadratic (w − m)ᵀB(w − m) and expands as tr(BH⁻¹)/t² + 2tr(BV)/t³ + O(t⁻⁴); for B = H this is d/t² +
   2∑λᵢvᵢ/t³" the right invariant statement? Is the B = H corollary worth stating as the 'Gaussian quadratic energy' reading?
4. Better or additional candidates close to this seabed, and the best next target after this tide (e.g. the same for the raw second
   moment ⟨wwᵀ⟩, the Frobenius discrepancy ‖C(t) − S(t)‖_F² to leading order, or the third cumulant's derivative)?
Vote: which bundle (A, A+B, A+B+C) should this tide commit to? Be concrete and terse; flag any error explicitly.
