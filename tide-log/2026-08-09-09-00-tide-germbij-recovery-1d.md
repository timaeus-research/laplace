# Tide: germbij-recovery-1d

**Direction (user):** continue formalising the germbij note (auto mode):
section 7.4's dimension-one constructive recovery, minimal form. The
leading exponent of the partition function recovers k and the coefficient
recovers the scale a, for pure even-monomial potentials.

**Seabed:** laplace, main at cb64915 (Theorem 7.3 program complete;
closed form partitionFunction_kthPotential available:
Z_{L_k}(t) = (1/k)((2k)!/t)^{1/(2k)} Gamma(1/(2k)) = alpha_k t^{-1/(2k)}).
**Started:** 2026-08-09T09:00Z
**Worktree/branch:** laplace-tide-germbij-recovery-1d /
tide/germbij-recovery-1d

## Candidates v1 (Claude)

**Candidate A (power-function rigidity, general).**
```
theorem eventual_power_eq {α₁ α₂ β₁ β₂ T : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (h : ∀ t : ℝ, T ≤ t → α₁ * t ^ β₁ = α₂ * t ^ β₂) :
    β₁ = β₂ ∧ α₁ = α₂
```
(rpow). Proof: evaluate at t₀ := max T 2 and t₀²; divide to get
t₀^(β₁-β₂) = t₀^(2(β₁-β₂)); injectivity of the exponent for base > 1
forces β₁ = β₂; then cancel t₀^β > 0.

**Candidate B (scale glue).**
```
lemma partitionFunction_smul (L : ℝ → ℝ) (a t : ℝ) :
    partitionFunction (fun x ↦ a * L x) t = partitionFunction L (a * t)
```
definitional (rewrite t * (a * L x) = (a * t) * L x under the integral).

**Candidate C (recovery corollary).** For k₁, k₂ ≥ 1, a₁, a₂ > 0: if
partitionFunction (fun x ↦ a₁ * kthPotential k₁ x) t
= partitionFunction (fun x ↦ a₂ * kthPotential k₂ x) t for all t ≥ T
(T > 0), then k₁ = k₂ and a₁ = a₂. Via B the closed form is
alpha_k (a t)^{-1/(2k)} = (alpha_k a^{-1/(2k)}) t^{-1/(2k)}; A gives
equal exponents (so 1/(2k₁) = 1/(2k₂), hence k₁ = k₂ by injectivity of
k ↦ 1/(2k) on k ≥ 1) and equal coefficients (so a₁^{-1/(2k)} =
a₂^{-1/(2k)}, hence a₁ = a₂ again by rpow injectivity in the base).

This is the note's "the leading exponent recovers k, the moments recover
a" specialised to the partition function (zeroth moment), the smallest
real instance of section 7.4's constructive recovery.

Claude's initial lean: A + B + C in one file (Laplace/OneD/Recovery.lean).

## GPT-5.6 Sol v1

Saved verbatim in `tide-log/gpt56_germbij_recovery_1d_v1.md`. Summary: A
correct as stated, no degeneracy from arbitrary T; confirmed the API set
(rpow_lt_rpow_left_iff for exponent injectivity, rpow_left_injOn for base
injectivity, mul_rpow/inv_rpow/rpow_neg for the splitting); main advice
for C: keep ((2k)!/a)^q as a single base (do not split off a^-q), which
minimizes rpow algebra and makes the a-recovery a positive-exponent base
injectivity step; T > 0 convenient but not necessary.

## Vote

- Claude: A + B + C in one file (Laplace/OneD/Recovery.lean).
- GPT-5.6 Sol: A + B + C, same organization.

## Numerical check

Closed form is already numerically verified in the seabed
(partitionFunction_kthPotential landed with the kth_moment_even family);
the new content is algebraic rigidity (injectivity), for which a check is
a tautology (alpha t^beta determines (alpha, beta): sampling t = 2, 4 for
alpha=3, beta=-1/4 vs any other pair differs). Not separately scripted.

## Result

- Branch tide/germbij-recovery-1d, file Laplace/OneD/Recovery.lean:
  eventual_power_eq, partitionFunction_smul,
  kth_partitionFunction_recovery.
- Three build iterations. Fixes: omega for the doubled nat equation;
  replacing field_simp+rcases by deterministic mul_left/right_cancel₀
  (field_simp mangled an rpow into a subtype projection); and, most
  instructive, dropping the unused hα₂ hypothesis from eventual_power_eq
  made α₂/β₂ unconstrained at the call site and the elaborator collapsed
  them onto the left-hand values — fixed by passing (α₂ := ...)
  (β₁ := ...) (β₂ := ...) explicitly.
- Surprise: the two-sample-point trick (t₀ and t₀·t₀) reduces the
  rigidity to linear_combination + one strict-mono lemma, with no
  logarithms anywhere.
