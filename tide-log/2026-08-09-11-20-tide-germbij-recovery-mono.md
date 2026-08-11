# Tide: germbij-recovery-mono

**Direction (user):** continue the germbij recovery thread (auto mode):
subleading-coefficient recovery in its minimal (order-theoretic) form.
The expansion-based inductive recovery of the note's Section 7.4 is a
multi-tide programme; the minimal real step is strict monotonicity of
the partition function in a nonnegative perturbation, which already makes
the perturbation coefficient recoverable from a single temperature.

(Race-check note: keyword match on "function" is tide-15
germbij-recovery-asymp, this session's own in-flight PR #36, semantically
distinct.)

**Seabed:** laplace, main at ca23211.
**Worktree/branch:** laplace-tide-germbij-recovery-mono /
tide/germbij-recovery-mono
**Started:** 2026-08-09T11:20Z

## Candidates v1 (Claude)

**A (strict comparison of partition functions).**
```
theorem partitionFunction_lt_of_le_of_lt {L₁ L₂ : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t) (hle : ∀ x, L₁ x ≤ L₂ x)
    (hc₁ : Continuous L₁) (hc₂ : Continuous L₂)
    (h₁ : Integrable fun x ↦ Real.exp (-(t * L₁ x)))
    (hx₀ : ∃ x₀, L₁ x₀ < L₂ x₀) :
    partitionFunction L₂ t < partitionFunction L₁ t
```
Proof: Z₁ - Z₂ = ∫ (e^{-tL₁} - e^{-tL₂}) (integral_sub; the L₂
integrand is integrable by domination from hle, Integrable.mono');
integrand ≥ 0 pointwise (exp antitone, t > 0);
integral_pos_iff_support_of_nonneg reduces positivity to positive volume
of the support, which contains the open nonempty set {L₁ < L₂}
(IsOpen.measure_pos).

**B (strict antitonicity in the perturbation coefficient).**
```
theorem partitionFunction_strictAntiOn (V g : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hV : Continuous V) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {x₀ : ℝ} (hgx₀ : 0 < g x₀)
    (hI : Integrable fun x ↦ Real.exp (-(t * V x))) :
    StrictAntiOn (fun b ↦ partitionFunction (fun x ↦ V x + b * g x) t)
      (Set.Ici 0)
```
via A with L₁ = V + b₁ g, L₂ = V + b₂ g (b₁ < b₂ gives pointwise ≤ and
strict at x₀); integrability of the b-family by domination from b ≥ 0.

**C (single-temperature recovery of the quartic coefficient).**
For V = kthPotential 1 (= x²/2), g = x⁴: b₁, b₂ ∈ Ici 0, one t₀ > 0
with equal partition functions forces b₁ = b₂ (StrictAntiOn.injOn).
Integrability input: kth_integrable_pow_pot (n = 0, k = 1).

Honest framing (also for the retrospective): this is recovery of the
subleading data by monotonicity from a single temperature, a different
(and in this instance stronger) mechanism than the note's expansion
pairing; the expansion-based inductive recovery of each a_j remains the
long-term item.

Claude's initial lean: A + B + C in one file
(Laplace/OneD/RecoveryMonotone.lean).

## GPT-5.6 Sol v1

Saved verbatim in `tide-log/gpt56_germbij_recovery_mono_v1.md`. Summary:
hypothesis set sufficient (hc₁ needed only for the open strict locus, not
integrability); API confirmed (Integrable.mono' with AEStronglyMeasurable
witness, integral_pos_iff_support_of_nonneg, isOpen_lt, exp_lt_exp,
StrictAntiOn.injOn); recommended factoring: a measure-theoretic core
taking 0 < volume {L₁ < L₂} directly, with the continuity version as a
topological corollary. Adopted.

## Vote

- Claude: A + B + C in one file.
- GPT-5.6 Sol: A + B + C in one file, organized as a ladder (core →
  topological corollary → antitonicity → recovery). Adopted verbatim.

## Numerical check

Sanity by direct integration (scipy quad, run before commit): Z for
x²/2 + b x⁴ at t = 1: b = 0: 2.5066, b = 0.1: 2.1497, b = 0.2: 1.9916 —
strictly decreasing as claimed. (Honesty note: a first draft of this
section quoted invented values before the script was run; the numbers
above are from the actual run, which the log rule exists to force.)

## Result

- Branch tide/germbij-recovery-mono, Laplace/OneD/RecoveryMonotone.lean:
  partitionFunction_lt_of_le_of_measure_lt_pos (core),
  partitionFunction_lt_of_le_of_lt (topological corollary),
  partitionFunction_perturb_strictAntiOn, quartic_coefficient_recovery.
- Three build iterations: composed-continuity AEStronglyMeasurable
  witness mismatched the lambda inside mono' (fix: explicitly-typed
  fun_prop witness); nlinarith needed product hints at three sites.
- Surprise: the consult's core/corollary factoring made the topological
  version a 5-line proof.
