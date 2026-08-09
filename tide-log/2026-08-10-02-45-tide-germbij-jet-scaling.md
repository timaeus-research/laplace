# Tide: germbij-jet-scaling (weighted-jet programme, stage 2)

**Direction (user):** stage 2 of the weighted-jet programme (germbij
§7.4 inductive recovery, auto mode, standing delegation): the jet
potential and its uniformly-positive-profile envelope, q-uniform
integrability, and the exact scaling identity
t^{s/(2k)}⟨x^s⟩_t = normalized reference-jet moment at q = t^{-1/(2k)}.

**Seabed:** laplace, main at be28cf4 (stage 1 merged).
**Worktree/branch:** laplace-tide-germbij-jet-scaling /
tide/germbij-jet-scaling
**Started:** 2026-08-10T02:45Z

## Envelope deliberation

Consult saved verbatim: `tide-log/gpt56_jet_scaling_envelope_v1.md`.
Three candidate envelopes were sent (E1 even-positive top, E2
smallness window with two-region bound, E3 cutoff observables). GPT
REJECTED E1 alone with a decisive counterexample: the factorization
L_q(u) = u^{2k}·P(qu) with profile P(y) = a + Σ c_r y^r means qu
ranges over all of ℝ regardless of q; for P(y) = 1 − 3y + y²
(positive even top!) P(1) = −1, so L_q(1/q) = −q^{-2k} and the Gibbs
weight has a remote peak e^{+q^{-2k}} — integrable at each q but not
converging to the reference measure. The recommended envelope is the
uniformly positive profile:

  HasPositiveJetProfile R a ρ c := 0 < ρ ∧ ∀ y, ρ ≤ P(y)

giving the clean global inequality L_q(u) ≥ ρ u^{2k} for EVERY real
q, hence a q-independent dominating function |u|^n e^{-ρu^{2k}}
(existing kth_integrable_pow family) and later dominated
differentiation at q = 0. Arbitrary target jets are handled by an
even stabilizer d y^M, M > R, which does not disturb extraction
through order R. Generic R immediately (stages 6-7 need generic
coefficient indexing); R = 2 as the first certificate via the
discriminant condition c₂ > 0, c₁² < 4ac₂, ρ = a − c₁²/(4c₂) — the
quadratic-profile analogue of the anharmonic discriminant.

## Vote

- Claude: the consult's plan as stated (profile envelope, generic R,
  ratio-form scaling theorem as the foundational result,
  gibbsExpectation corollary, R = 2 certificate).
- GPT-5.6 Sol: same (its own recommendation).

Agreed.

## Numerical check

Executed before formalisation. (1) The counterexample: P(1) = −1 for
(1, −3, 1), confirming E1's failure. (2) The R = 2 certificate at
(a, c₁, c₂) = (1, −1, 1): grid min of P = 0.75 = ρ exactly. (3) The
exact scaling identity at k = 1: t^{s/2}⟨x^s⟩_t vs the normalized
jet moment at q = t^{-1/2}, for t ∈ {5, 40}, s ∈ {1, 2, 3}:
agreement to machine precision (max |diff| 1.4e-15), as befits an
exact identity.

## Planned declarations (from the consult, Lean-shaped)

jetProfile, jetPotential, polynomialJet (defs);
jetPotential_eq_pow_mul_profile; HasPositiveJetProfile (def);
jetPotential_lower_bound; norm_pow_mul_exp_neg_jetPotential_le;
integrable_pow_mul_exp_neg_jetPotential (+ _exp_ specialization,
+ integral positivity); normalizedJetMoment (def);
integral_polynomialJet_scale (+ partition version; substitution
x = qu with t·q^{2k} = 1); normalized_polynomialJet_scale;
gibbsExpectation_polynomialJet_scale; hasPositiveJetProfile_two.

## Result

- Declarations (Laplace/OneD/JetScaling.lean, ~290 lines, zero
  sorries, zero warnings): jetProfile / jetPotential / polynomialJet /
  normalizedJetMoment (defs), jetPotential_eq_pow_mul_profile,
  HasPositiveJetProfile, jetPotential_lower_bound,
  jetPotential_continuous, norm_pow_mul_exp_neg_jetPotential_le,
  integrable_pow_mul_exp_neg_jetPotential (+ exp specialization +
  partition positivity), mul_polynomialJet_comp_mul (the pointwise
  substitution identity from t·q^{2k} = 1),
  integral_polynomialJet_scale, normalized_polynomialJet_scale,
  gibbsExpectation_polynomialJet_scale, hasPositiveJetProfile_two.
- Design choice: the core theorems take the algebraic hypothesis
  (hq : 0 < q) (hqt : t * q^(2k) = 1) instead of a let-bound rpow,
  keeping rpow plumbing out of the analytic layer entirely; the
  t^{-1/(2k)} instantiation can be a later one-line corollary when a
  stage needs it.
- Surprises: (1) congr-lambda goals from Integrable.congr can arrive
  beta-unreduced, so rw [pow_zero] finds no pattern where simp (which
  betas) closes it — new catalogue entry. (2) After simp-normalizing
  the s = 0 instance of the scale identity, the planned h0' bridge
  was already identical to it (the "unsolved goals + no goals" error
  pair signals a redundant have whose rw closed everything). (3)
  linear_combination with coefficient c_i·u^m·q^{i+1} against
  t·q^{2k} = 1 cleanly discharges the per-term substitution algebra
  inside Finset.sum_congr.
