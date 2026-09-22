You are consulted (one round) on tide 82 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders `≤ K/t^n` for `t ≥ T ≥ 1`. Your previous consult (tide 81) named this as the best next target:
"quantify the discrepancy from the Gaussian-prior covariance: `| ‖C(t) − S(t)‖_F² − ‖V + gH⁻²‖_F²/t⁴ | ≤ K/t⁵`, coefficient
`∑ᵢ (vᵢ + g/λᵢ²)²`".

## Candidates v1 (Claude)

Setting (E2, as in tides 68–81): the rotated separable anharmonic family with the isotropic localiser `g ≥ 0`, anchor `w₀`, fixed
parameters, `t → ∞`. `C(t)` the exact localised centred covariance, `S(t) = (tH + gI)⁻¹ = Q diag(1/(tλᵢ + g)) Qᵀ` the note's
Gaussian-prior resolvent, `H⁻¹ = Q diag(1/λᵢ) Qᵀ`, `vᵢ = varLocCoeff2ᵢ` (tide 74), `wᵢ = vᵢ + g/λᵢ² = covLocCoeff2ᵢ`,
`W = Q diag(wᵢ) Qᵀ = V + gH⁻²`. Tide 74 gives entrywise `|C(t)ⱼₖ − S(t)ⱼₖ − Wⱼₖ/t²| ≤ K/t³` (`localisedRotatedAnharmonic_cov_order2_rate`).
`‖X‖_F² := ∑ⱼₖ Xⱼₖ²`.

**A. The Frobenius discrepancy from the Gaussian-prior covariance.**
`|t⁴ ‖C(t) − S(t)‖_F² − ‖W‖_F²| ≤ K/t` eventually, with the invariant closed form `‖W‖_F² = ∑ᵢ (vᵢ + g/λᵢ²)²`
(`‖Q diag(a) Qᵀ‖_F² = ∑ᵢ aᵢ²` for orthogonal `Q`). Equivalently `‖C − S‖_F² = ‖V + gH⁻²‖_F²/t⁴ + O(t⁻⁵)`: the note's `O(S²)` remainder in
(eq:cov) has Frobenius norm `‖W‖_F/t² + O(t⁻³)`, i.e. `‖C − S‖_F = ‖W‖_F ‖S‖_F²·(1 + o(1))·(∑λᵢ⁻²)⁻¹`… stated as the squared form only.
Lean: entrywise square rate `sq_rate : |t²x − w| ≤ K/t ⟹ |t⁴x² − w²| ≤ (2|w|K + K²)/t` (for `t ≥ 1`), summed over `j, k`
(`sum_rate_div` finite-sum transport), plus `frobenius_conj_diagonal` (via `sum_sum_eq_trace`, `trace_mul_comm`, `QᵀQ = 1`).

**B. The discrepancy from the unlocalised Laplace covariance `H⁻¹/t`: the localiser drops out.**
`|t⁴ ‖C(t) − H⁻¹/t‖_F² − ‖V‖_F²| ≤ K/t`, `‖V‖_F² = ∑ᵢ vᵢ²`. Entrywise, `S − H⁻¹/t = −gH⁻²/t² + O(t⁻³)` exactly
(`1/(tλ + g) − 1/(tλ) = −g/(tλ(tλ + g))`, with `|t²(…) + g/λ²| = g²/(λ²(tλ + g)) ≤ g²/(λ³t)`), so `C − H⁻¹/t = V/t² + O(t⁻³)`: the
pure Gaussian-localiser term `gH⁻²` cancels between `C − S` and `S − H⁻¹/t`. Contrast with A: the discrepancy from the *resolvent* is
governed by `V + gH⁻²`, from the *unlocalised* Laplace covariance by `V` alone.

**C. The relative discrepancy (the note's `O(S²)` made quantitative).**
`‖S(t)‖_F² = ∑ᵢ 1/(tλᵢ + g)²` exactly (`locS_rot_apply` + `frobenius_conj_diagonal`), so `t²‖S‖_F² = ∑ᵢ λᵢ⁻² + O(1/t)` and
`|t² ‖C − S‖_F²/‖S‖_F² − ‖W‖_F²/‖H⁻¹‖_F²| ≤ K/t`, `‖H⁻¹‖_F² = ∑ᵢ λᵢ⁻²`: the relative Frobenius error of the note's (eq:cov) is
`(‖W‖_F/‖H⁻¹‖_F)/t + O(t⁻²)` (in the squared form). Lean: ratio bookkeeping with the positive limit `∑ λᵢ⁻² > 0` (needs `d ≥ 1`, i.e.
`Nonempty (Fin d)`; for `d = 0` both sides are `0`… state with `[Nonempty (Fin d)]` or `0 < d`).

Not proposed: operator-norm versions (Frobenius is the invariant sum-of-squares the seabed's entrywise rates reach directly); the
Frobenius *norm* (square root) — the squared form is the clean statement.

Sizing: A ~150 lines (square rate, finite sums, Frobenius of a conjugated diagonal), B ~120 (resolvent-minus-inverse entrywise rate,
combination), C ~100 (exact `‖S‖_F²`, ratio). Target A + B + C.

## Seabed facts available (names of Lean theorems, all landed)
- tide 74 (`LocalisedOrder2Multi`): `localisedRotatedAnharmonic_cov_order2_rate` (|Cⱼₖ − (locS g H t)ⱼₖ − (∑ᵢ QⱼᵢQₖᵢ covLocCoeff2ᵢ)/t²| ≤
  K/t³), `covLocCoeff2 = varLocCoeff2 + g/λ²`, `varLocCoeff2_eq` (closed form α²/λ⁴ − gx₀α/λ³ − g/λ² − γ/(2λ³)); anchor corollaries.
- `locS_rot_apply` ((locS g H t)ⱼₖ = ∑ᵢ QⱼᵢQₖᵢ/(tλᵢ + g)), `conj_diagonal_inv_apply`; tide 81's algebra: `sum_sum_eq_trace`
  (∑ⱼₖ BⱼₖXⱼₖ = tr(BXᵀ)), `conj_diagonal_entry`, `conj_diagonal_transpose`, `trace_mul_conj_diagonal` (tr(B Q diag(a) Qᵀ) = ∑ᵢ (QᵀBQ)ᵢᵢaᵢ),
  `conj_conj` (Qᵀ(Q D Qᵀ)Q = D), `sum_rate_div_sq` / `sum_rate_div_cube` (finite weighted sums of rates), `prod_rate`, `order2_to_order1`.
- Mathlib: `Matrix.trace_mul_comm`, `Matrix.diagonal_mul_diagonal`, `Matrix.trace_diagonal`.

## Numerical check (done; 2D, rotation θ = 0.6, λ = (1.3, .9), α = (.7, −.4), γ = (1.1, .8), g = .8, anchor off the minimum)
  the requested tolerance from being achieved.  The error may be 
  underestimated.
sum (v_i + g/lam_i^2)^2 = 0.14066548   sum v_i^2 = 2.08256044   ratio limit = 0.07702279
t=    80: t^4|C-S|^2 = 0.136262 (t*resid -0.3523)   t^4|C-Hinv/t|^2 = 2.037943 (t*resid -3.5694)   ratio = 0.076111 (t*resid -0.0729)
t=   160: t^4|C-S|^2 = 0.138502 (t*resid -0.3462)   t^4|C-Hinv/t|^2 = 2.060393 (t*resid -3.5468)   ratio = 0.076598 (t*resid -0.0679)
t=   320: t^4|C-S|^2 = 0.139594 (t*resid -0.3429)   t^4|C-Hinv/t|^2 = 2.071517 (t*resid -3.5338)   ratio = 0.076819 (t*resid -0.0653)
t=   640: t^4|C-S|^2 = 0.140132 (t*resid -0.3411)   t^4|C-Hinv/t|^2 = 2.077050 (t*resid -3.5269)   ratio = 0.076923 (t*resid -0.0639)
t=  1280: t^4|C-S|^2 = 0.140400 (t*resid -0.3402)   t^4|C-Hinv/t|^2 = 2.079808 (t*resid -3.5233)   ratio = 0.076973 (t*resid -0.0632)
(Residuals scaled by t are bounded, so the O(1/t) claims hold numerically.)

## Questions
1. Are A, B, C correct as stated? In particular: the invariance `‖Q diag(a) Qᵀ‖_F² = ∑ aᵢ²`; the exact resolvent-minus-inverse
   identity in B and its rate; the positivity/nonemptiness needed in C. Any hidden hypothesis?
2. Is the squared Frobenius form the right invariant statement against the note's "C = S + O(S²)" (and E3's Gaussian-prior reading of
   the localiser)? Would you phrase the note's remark as "the O(S²) remainder has Frobenius norm ‖V + gH⁻²‖_F/t² + O(t⁻³), relative size
   (‖V + gH⁻²‖_F/‖H⁻¹‖_F)/t"? Is B's contrast (localiser term cancels against the unlocalised Laplace covariance) worth stating, and how
   would you word it?
3. Cleanest Lean route for the square-of-rate step (entrywise `|t²x − w| ≤ K/t ⟹ |t⁴x² − w²| ≤ (2|w|K + K²)/t`) and for the ratio in C
   (denominator `t²‖S‖_F² → ∑λᵢ⁻² > 0`)? Any pitfalls (e.g. d = 0)?
4. Better or additional candidates close to this seabed, and the best next target after this tide (e.g. the Frobenius discrepancy of the
   *derivative* −∂ₜC from H⁻¹/t² using tide 80/81, the mean's discrepancy ‖m(t) − m_S(t)‖² with tide 74's meanLocResidual2, or the
   trace-form `tr(H(C − S))` with its sign)?
Vote: which bundle (A, A+B, A+B+C) should this tide commit to? Be concrete and terse; flag any error explicitly.
