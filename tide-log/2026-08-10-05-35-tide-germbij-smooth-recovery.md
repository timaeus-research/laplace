# Tide: germbij-smooth-recovery (smooth-germ programme, stages C4-C5)

**Direction (user):** the programme's closing tide (auto mode,
standing delegation): the Taylor/stabilizer adapter and the
finite-order smooth recovery — two smooth admissible losses whose
normalized moment data vanishes at the coefficient-sensitive rates
have equal Taylor coefficients through degree D = R + 2.

**Seabed:** laplace, stacked on tide/germbij-taylor-compare (PR #62
in CI at tide start). Linear-chain worktree.
**Worktree/branch:** laplace-tide-germbij-smooth-recovery /
tide/germbij-smooth-recovery
**Started:** 2026-08-10T05:35Z

## Deliberation

Stages C4-C5 specified in the smooth-germ scoping consult (archived
two tides back: tide-log/gpt56_smooth_germ_scoping_v1.md) and refined
by the C3 shape consult. Seabed survey for the one genuinely new
ingredient: Mathlib's `taylor_isLittleO` supplies the Peano remainder
`(f x − taylorWithinEval f n s x₀ x) =o[𝓝[s] x₀] (x − x₀)^n` — so C4
is composition: (1) IsLittleO → the comparison's epsilon-radius jet
form; (2) taylorWithinEval at 0 in jet-coefficient shape
(c_i = iteratedDeriv(3+i) f 0/(3+i)!); (3) the stabilized Taylor
polynomial is admissible AND has a positive jet profile (from the C2
stabilizer envelope through the profile factorization); (4) the
L-vs-P comparison via C3 with the M > D stabilizer invisible; (5)
triangle transfer of the data hypothesis from (L₁,L₂) to (P₁,P₂) and
jet_recovery_stable, concluding equal coefficients hence equal
iterated derivatives through D. Documented prior-deliberation path.

## Vote

- Claude: C4-C5 as one closing tide.
- GPT-5.6 Sol (scoping consult): C4 then C5, with C5 "interface
  adaptation" once C3 exists.

Agreed (carried over).

## Numerical check

The composition introduces no new closed form beyond what C3's and
the weighted-jet programme's executed checks cover; the one new
identity class (Taylor coefficients c_i = iteratedDeriv/(factorial))
is definitional. Noted per protocol; the C3 statement-level check
(previous tide log) covers the analytic content end to end.

## C5 composition plan (checkpoint 4, recorded before writing)

Target theorem `smooth_jet_recovery`: L₁ L₂ admissible + ContDiff D
(D := R+2, hR via hD : 2 ≤ D), data hypotheses in x-space q-form:
∀ r ≤ R: Tendsto ((⟨x^{2+r}⟩^{L₁}_{t(q)} − ⟨x^{2+r}⟩^{L₂}_{t(q)}) /
q^{2+2r}) (𝓝[>]0) (𝓝 0) where t(q) = (q²)⁻¹ and ⟨⟩ is the x-space
normalized moment (∫x^s e^{-tL}/∫e^{-tL}). Conclusion:
taylorBase L₁ = taylorBase L₂ ∧ taylorCoeff L₁ D = taylorCoeff L₂ D,
plus corollary iteratedDeriv k L₁ 0 = iteratedDeriv k L₂ 0 for
2 ≤ k ≤ D.

Steps: (1) M := 2*(D/2+1) (even, > D, omega); d_ν + admissibility +
profile from stabilized_admissible with (R', a, c) :=
(D−2, taylorBase L_ν, taylorCoeff L_ν D) — note a_ν > 0 from
taylorBase_ge + rho_pos. (2) hjet(L_ν, P_ν) at order D in
epsilon-radius form: given ε, Peano δ'₁ at ε/2 (taylor_jet_epsilon +
taylorWithinEval_eq_jet + stabilized_jet_eq to identify P = T + d x^M),
δ'₂ := min 1 (ε/(2(d+1))) absorbs d|x|^M ≤ (ε/2)|x|^D via
|x|^{M−D} ≤ |x| ≤ ε/(2(d+1)). (3) C3 quotient instances
admissible_normalized_difference_littleO for (L_ν, P_ν) at every
s ≤ 2+R. (4) scaling bridge: normalizedJetMoment 1 (M−2) a_ν q ext_ν
= q^{-s}·⟨x^s⟩^{P_ν} via normalized_polynomialJet_scale (P_ν =
polynomialJet 1 (M−2) a_ν ext_ν definitionally). (5) per-rung
assembly: (F-jet diff)/q^r = q^{-s-r}(x-diff) decomposed into three
pieces via triangle; outer pieces = (C3-limit)·q^{D−2−r} → 0·(0 or 1);
middle = data. Both jet_recovery_stable data shapes (s = 2 unscaled;
per-rung scaled) produced this way. (6) jet_recovery_stable (k := 1)
gives a₁ = a₂ ∧ ext₁ = ext₂; project to taylorBase/taylorCoeff
(stabilizedCoeff agrees with c below R'); iteratedDeriv corollary by
cases k = 2 / k ≥ 3 (i := k−3).
