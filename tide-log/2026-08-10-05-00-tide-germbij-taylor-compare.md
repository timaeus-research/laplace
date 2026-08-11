# Tide: germbij-taylor-compare (smooth-germ programme, stage C3)

**Direction (user):** the normalized local Taylor comparison (auto
mode, standing delegation) — the programme's designated hardest
stage: for admissible potentials with K₁ − K₂ = o(|x|^D) at 0, the
moment differences obey A_s: o(q^{s+D−1}) and F_s: o(q^{s+D−2}),
via the exponential secant bound, the √q moving split, C2's tail
estimate, and the quotient decomposition.

**Seabed:** laplace, stacked on tide/germbij-taylor-package (PR #61,
merged f1f8f64 at tide start — base branch already on main).
**Worktree/branch:** laplace-tide-germbij-taylor-compare /
tide/germbij-taylor-compare
**Started:** 2026-08-10T05:00Z

## Deliberation

Shape consult saved verbatim: `tide-log/gpt56_c3_shape_v1.md`.
Confirms the exponent bookkeeping (A_s at o(q^{s+D−1}); quotient at
o(q^{s+D−2}) via (A₁−A₂)/Z₁ + A₂(Z₂−Z₁)/(Z₁Z₂) with Z ≥ C₀q and
|A_s| ≤ Cq^{s+1}). Three adopted refinements: (1) moving radius
r(q) = √q instead of q^{4/5} — outer exponent r²/q² = 1/q gives
e^{-c/q} tails with NO rpow anywhere, and √q ≤ δ is easy; (2) Nat
subtraction defused by the global side condition 2 ≤ D (covers both
s+D−1 and s+D−2 for every s); (3) the ending is a direct
Metric.tendsto_nhds epsilon-of-room proof — given η, set
εj = η/(4·max(C,1)), pull δj from the jet hypothesis, then eventually
in q: inner ≤ η/4, outer < η/2 — matching the quantifier order being
proved (NOT squeeze_zero_norm', whose majorant would be ε-dependent).
Also: epsilon-radius jet form as the working hypothesis (an IsLittleO
wrapper can come with C4, whose Peano remainder produces it);
separate (ρᵢ, κᵢ, δᵢ) per potential with ρ := min at the shared
envelope; signed A_s fine (estimates through |x|^s only).

## Vote

- Claude: the consult's plan as refined (√q split, 2 ≤ D, tendsto_nhds
  ending), staged as: admissibility layer (C3.0 partition lower bound
  + moment upper bound) checkpoint first, then the main comparison.
- GPT-5.6 Sol: same ("the C3 estimates are correctly scaled").

Agreed.

## Numerical check

The exponent claims were checked numerically in the jet-difference
tide (covariance limit ratios 0.9999) and stage-1/2 checks; C3's new
content over those is the smooth-vs-polynomial split bookkeeping,
whose only closed forms (scaling constants, e^{-c/q} tails) are
inherited from checked lemmas. One new check executed below at the
statement level.

Executed (values quoted from output): K₁ = x² + 0.3x⁵e^{-x²},
K₂ = x², D = 4 (difference is 0.3x⁵ + O(x⁷) = o(|x|⁴)); the scaled
difference (A₂(K₁) − A₂(K₂))/q⁵ at q = 0.2, 0.1, 0.05:
0.012645 → 0.001139 → 0.000078, decaying roughly like q² (the actual
next order is x⁵ i.e. one extra q) — confirming o(q^{s+D−1}) with
margin.

## Result

- Theorems (Laplace/OneD/TaylorCompare.lean, ~700 lines, zero
  sorries, zero warnings; gate verified via import + .olean):
  AdmissiblePotential (+ integrable_pow, partition_lower with the
  explicit constant 2δe^{-κδ²}, moment_upper via envelope + exact
  scaling), exp_neg_div_tendsto_zero (e^{-c/q}/q^n → 0 by u = 1/q),
  admissible_moment_difference_littleO (C3 main: the √q split with
  the secant bound and the Taylor power kept inside the Gaussian,
  assembled by the Metric.tendsto_nhds epsilon-of-room skeleton), and
  admissible_normalized_difference_littleO (C3 quotient: F_s
  difference at o(q^{s+D-2}) by squeeze against the two unnormalized
  limits with Z ≥ C₀q and |A| ≤ Cq^{s+1} — NOT the generic 3D
  quotient lemma, which needs nonvanishing limits and does not apply
  in x-space where Z → 0).
- Surprises: (1) a new instance of the cascading-rewrite class:
  `show s + D = (s+D-2)+2` rewrote the s + D INSIDE s + D - 2,
  leaving unprovable residues — nth_rewrite on a named equation is
  the fix (exponent-arithmetic analogue of the radical-atom rule);
  (2) gcongr discharges monotone-denominator side goals from ambient
  hypotheses entirely (a trailing exact is "No goals" even for the
  substantive inequality); (3) positivity cannot use context
  hypotheses like 0 ≤ C₂ — nonnegativity of set constants must be
  passed explicitly; (4) the epsilon-of-room skeleton from the shape
  consult worked as written, with the only structural addition being
  the |·|-composed limits for the squeeze form of the quotient step.
