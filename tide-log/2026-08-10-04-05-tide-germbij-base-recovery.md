# Tide: germbij-base-recovery (programme B′, stages B1-B2)

**Direction (user):** programme B′ opening tide (auto mode, standing
delegation): the leading second-moment asymptotic of the jet Gibbs
measure (normalizedJetMoment 2 → M₂(a) as q → 0⁺), its Gamma closed
form via the t = a·(2k)! bridge, strict monotonicity in the base
coefficient, and base-coefficient recovery: two enveloped jets with
eventually-equal second moments have a₁ = a₂.

**Seabed:** laplace, main at b631345 (weighted-jet programme +
synthesis complete).
**Worktree/branch:** laplace-tide-germbij-base-recovery /
tide/germbij-base-recovery
**Started:** 2026-08-10T04:05Z

## Programme scoping

Consult saved verbatim: `tide-log/gpt56_general_order_scoping_v1.md`
(will be copied at commit). It splits the remaining nondegenerate
work into programme B′ (unequal-base polynomial recovery, stages
B1-B5, low risk, endpoint: finite polynomial jets with possibly
different positive quadratic coefficients are identified by
normalized moment data) and a separate programme C (smooth-germ
transfer: an asymptotically-STABLE recovery theorem replacing exact
eventual equality, then localisation/Taylor-remainder analysis — the
note's "Justification" paragraph). Named trap: treating the Taylor
replacement as producing exact polynomial data; it produces
order-controlled errors, so C needs the stability interface (B2's
limit-based form is the designed bridge). Key simplifications
endorsed: recover a from the SECOND moment (M₂(a) = C_k·a^{-1/k}
strictly decreasing, all k); do NOT extend the pairwise machinery to
unequal bases (at a₁ ≠ a₂ the difference has a q⁰ term — wrong scale
by design); B3 is then verbatim composition.

## Vote

- Claude: B′ next, this tide = B1+B2 with both the eventual-equality
  and limit-based (C-bridge) interfaces.
- GPT-5.6 Sol: B′ ("small, low-risk, and now clearly justified by
  the completed weighted-jet machinery").

Agreed.

## Numerical check

Executed before formalisation. Gamma form
M₂ = ((2k)!/t)^{1/k}·Γ(3/(2k))/Γ(1/(2k)) at t = a(2k)! vs quadrature:
k=1, a=0.7: 0.71428571 both (= 1/(2a) ✓); k=2, a=1.3: 0.29643607
both. Jet moment at q = 0.004 within 1.2e-5 of the limit. Strict
monotonicity: M₂ at a = 0.5, 1, 2 strictly decreasing for k = 1
(1.0 > 0.5 > 0.25) and k = 2 (0.478 > 0.338 > 0.239).

## Result

- Theorems (Laplace/OneD/BaseRecovery.lean, ~200 lines, zero sorries,
  zero warnings; gate verified via import line + fresh .olean):
  HasPositiveJetProfile.base_pos (the envelope itself forces
  0 < a, since the profile at y = 0 is a — so no separate positivity
  hypothesis is ever needed), jet_secondMoment_tendsto,
  reference_secondMoment_gamma ((1/a)^{1/k}·Γ(3/(2k))/Γ(1/(2k)) via
  the t = a(2k)! bridge), reference_secondMoment_injective (rpow base
  monotonicity + Gamma-ratio cancellation),
  base_recovery_of_tendsto (the limit-based C-bridge interface), and
  base_recovery.
- Surprises: (1) 0 < a is derivable from the envelope (profile at 0),
  killing a hypothesis; (2) `rw` cannot unfold a def under a Tendsto
  binder but `Tendsto.congr fun q ↦ rfl` closes it by defeq; (3) the
  lambda-level exponent rewrite failed as usual — the integral-level
  congr (integral_congr_ae + norm_num) is the reliable form; (4) the
  Γ-ratio cancellation is cleanest as mul_right_cancel₀ around a
  three-step ring calc, avoiding field_simp shape uncertainty.
