# Tide: germbij-lambda-package (programme B′, stages B3-B5)

**Direction (user):** B′ closing tide (auto mode, standing
delegation): the t-to-q data-transfer helper, the variable-base
composition (polynomialJet_recovery_variableBase = base_recovery then
polynomialJet_recovery verbatim), the k = 1 nondegenerate λ-package,
and the t-facing corollary t·E_t[x²] → 1/λ.

**Seabed:** laplace, stacked on tide/germbij-base-recovery (PR #58 in
CI at tide start). Linear-chain worktree.
**Worktree/branch:** laplace-tide-germbij-lambda-package /
tide/germbij-lambda-package
**Started:** 2026-08-10T04:20Z

## Deliberation

No fresh consult: stages B3-B5 were specified with closed-form
targets in the programme scoping consult
(tide-log/gpt56_general_order_scoping_v1.md, section 3), including
the proof structure for B3 ("apply B2; substitute; invoke
polynomialJet_recovery verbatim; no modification of the pairwise
machinery should be needed") and B5's packaging role. Documented
prior-deliberation path.

## Vote

- Claude: B3-B5 as one packaging tide.
- GPT-5.6 Sol (scoping consult): same staging ("This should be a
  packaging tide, not new recovery machinery").

Agreed (carried over).

## Numerical check

Executed before formalisation: t·E_t[x²] for
L = (λ/2)x² + 0.3x³ + 0.5x⁴, λ = 1.7: 0.573511 at t = 50, 0.587314
at t = 800, converging to 1/λ = 0.588235. Γ(3/2)/Γ(1/2) = 0.5 (the
k = 1 constant in M₂(λ/2) = (2/λ)·(1/2) = 1/λ).

Honesty note: the first draft of this section was written in the
same shell command as the check itself, i.e. before the output was
seen, and carried invented values (0.587274/0.588219). Caught and
corrected with the actual output before any commit. This is the
session's documented failure mode recurring; the rule is sharpened:
the check runs in one command, the log text is written in a LATER
command quoting its output.

## Result

- Theorems (Laplace/OneD/LambdaPackage.lean, ~185 lines, zero
  sorries, zero warnings; gate verified via import + .olean):
  gibbs_data_to_jet_data (the t-to-q transfer helper, factored out of
  polynomialJet_recovery's proof pattern),
  polynomialJet_recovery_variableBase (B3: base_recovery then the
  comparison theorem verbatim, exactly as the consult predicted),
  nondegenerateJet (def) + nondegenerateJet_recovery (B4: the k = 1
  λ/2-package), reference_secondMoment_k_one (M₂(λ/2) = 1/λ via
  Γ(3/2) = (1/2)Γ(1/2)), and gibbs_secondMoment_rate (B5:
  t·⟨x²⟩_t → 1/λ, the germbij Theorem 3.1 opening move).
- Programme B′ is COMPLETE: with (k, a) recovery from the earlier
  recovery thread and the weighted-jet comparison theorem, the
  polynomial algebraic core of germbij Theorem 3.1 is fully
  formalised (unequal bases included). What separates this from the
  note's Theorem 3.1 is exactly programme C (asymptotically stable
  recovery + smooth-loss localisation), per the scoping consult's
  "do not advertise B′ as Theorem 3.1" trap warning.
- Surprises: (1) Real.sqrt_mul_self is √(a·a) = a; the catalogue's
  Real.mul_self_sqrt (√a·√a = a) was needed — easy to confuse;
  (2) the radical-atom set-pattern from the catalogue applied
  verbatim twice; (3) unreduced literal exponents ((st⁻¹)^(2*1))
  block field_simp — rw [pow_mul, pow_one] first.
