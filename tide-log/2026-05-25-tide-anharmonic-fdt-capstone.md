# Tide: anharmonic-fdt-capstone

**Direction (user):** instantiate the FDT and cross-susceptibility
derivative theorems on the anharmonic-plus-linear-perturbation
`GibbsRegularity` instance (now sorry-free as of `b38b09e`); write
out the headline first-moment FDT and `Cov(x², x)` identities.

**Seabed:** `lean/laplace`, commit `b38b09e` (post-merge of
`tide/anharmonic-partition-hasDerivAt`).

**Started:** 2026-05-25T03:05:00Z

## Seabed snapshot

The `Threepoint` package (a Mathlib-style dependency vendored into
the laplace `.lake/packages/Threepoint`) provides the abstract FDT
machinery:

- `Threepoint.GibbsRegularity μ L A t` — the three-field hypothesis
  bundle: `partition_pos`, `partition_h_zero`, `partition_hasDerivAt`.
- `Threepoint.GibbsObservable μ L A t φ` — per-observable
  differentiation-under-the-integral-sign witness for `φ`.
- `Threepoint.gibbsExp_deriv_eq_neg_t_cov` — the **first-cumulant
  FDT**: `∂_h ⟨φ⟩_h |_{h=0} = -t · Cov(φ, A)`. Conditional on
  `GibbsRegularity` + two `GibbsObservable` instances (for `φ` and
  `φ·A`).
- `Threepoint.gibbsCov_deriv_eq_neg_t_kappa3` — the **cross-
  susceptibility / three-point identity**: `∂_h Cov_h(φ, B) |_{h=0}
  = -t · κ₃(φ, A, B)`. Conditional on `GibbsRegularity` + six
  `GibbsObservable` instances (for `φ, B, φ·B, φ·A, B·A, φ·B·A`).

The laplace seabed already supplies, for the anharmonic potential
`L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` with `λ, γ > 0` and `α² < 3λγ`:

- `Threepoint.anharmonic_id_gibbsRegularity` (line 298 of
  `AnharmonicGibbsRegularity.lean`) — the now-sorry-free
  `GibbsRegularity` instance with `L := anharmonicPotential lam alpha
  gamma`, `A := id`, for any `t > 0`. This is the load-bearing
  yesterday-tide closure.
- `kappa3_anharmonic_id_id_id_asymptotic` (line 222 of
  `AnharmonicKappa3.lean`) — the asymptotic
  `t² · κ₃(x, x, x) → -α/λ³` as `t → ∞`.
- `cov_self_anharmonic_asymptotic` (in `IntegralRemainder.lean`) —
  `t · Var(x) → 1/λ` as `t → ∞`.
- `kappa3_anharmonic_shifted_affine_asymptotic` (line 352 of
  `AnharmonicKappa3Affine.lean`) — the affine multilinear
  generalisation already exists.

The harmonic-case mirror is in `HarmonicCrossSuscDeriv.lean`:

- `cov_h_id_id_deriv_harmonic_eq_zero` — *conditional* form, takes
  `GibbsObservable` for `x`, `x*x`, `x*x*x`. Concludes
  `HasDerivAt (h ↦ Cov_h(x,x)) 0 0` because `κ₃ = 0` by parity
  (Tide 5).
- `cov_h_id_id_deriv_harmonic_eq_zero_unconditional` —
  unconditional form, discharges the GibbsObservable hypotheses via
  `Threepoint.harmonic_id_gibbsObservable_{id, mul_self, mul_mul_self}`
  (which were Tide G4 / formalised in
  `HarmonicGibbsObservableMonomials.lean`, 441 lines).

**Anharmonic GibbsObservable lemmas are NOT yet formalised**
(`grep -rn 'anharmonic.*GibbsObservable'` returns nothing). The
yesterday-retro's follow-up #4 ("Anharmonic observable hypothesis")
is a separate multi-tide undertaking that mirrors the 441-line
harmonic monomial observable file.

So this tide is the *conditional* mirror: instantiate the FDT and
cross-susceptibility identities on the anharmonic `GibbsRegularity`
instance, leaving the `GibbsObservable` hypotheses as inputs. The
unconditional form waits for follow-up #4.

## Candidates v1 (Claude)

### Candidate A — Cross-susceptibility derivative for the anharmonic case (conditional)

The literal mirror of `cov_h_id_id_deriv_harmonic_eq_zero`:

```lean
theorem cov_h_id_id_deriv_anharmonic_id_id_eq
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t)
    (hx : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x))
    (hx2 : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x * x))
    (hx3 : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x * x * x)) :
    HasDerivAt
        (fun h : ℝ => Threepoint.gibbsCov (volume : Measure ℝ)
                        (anharmonicPotential lam alpha gamma)
                        (fun x : ℝ => x) t h
                        (fun x : ℝ => x) (fun x : ℝ => x))
        (-t * Threepoint.kappa3 (volume : Measure ℝ)
                (anharmonicPotential lam alpha gamma)
                (fun x : ℝ => x) t (fun x : ℝ => x) (fun x : ℝ => x))
        0
```

**Rationale.** This is the minimal step outward from the
`anharmonic_id_gibbsRegularity` instance: just feed it into the
abstract `gibbsCov_deriv_eq_neg_t_kappa3` and don't simplify
further. The harmonic mirror does the same shape and then
specialises to 0 via Tide 5; here the κ₃ does *not* vanish (the
anharmonic cubic term breaks parity), so the conclusion stays as
`-t · κ₃`. ~30 lines, exactly mirroring `HarmonicCrossSuscDeriv.lean`.

**Closed-form value.** Not a literal closed form, but the asymptotic
`-t · κ₃ ~ α/(λ³ t)` as `t → ∞` is computable from the existing
`kappa3_anharmonic_id_id_id_asymptotic`.

### Candidate B — Asymptotic capstone for the cross-susceptibility derivative

```lean
theorem cov_h_id_id_deriv_anharmonic_id_id_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma)
    (hx hx2 hx3 : ∀ t, 0 < t → Threepoint.GibbsObservable …) :
    Filter.Tendsto
      (fun t : ℝ => t * deriv (fun h : ℝ => …) 0)
      Filter.atTop
      (nhds (α / lam ^ 3))
```

Composes Candidate A with `kappa3_anharmonic_id_id_id_asymptotic` to
get the asymptotic `t · ∂_h Cov_h(x,x)|_{h=0} → α/λ³`.

**Rationale.** A natural "headline" companion to the conditional
identity. Lets the casual reader see the closed-form scaling.
~30-50 lines.

**Risk.** Asks for a uniform-in-`t` GibbsObservable hypothesis,
which complicates the statement. May want to gate this behind a
single `∀ t, ...` hypothesis bundle.

### Candidate C — First-cumulant FDT for the anharmonic case (conditional)

```lean
theorem first_cum_fdt_anharmonic_id_eq
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t)
    (hx : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x))
    (hx2 : Threepoint.GibbsObservable (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t
            (fun x : ℝ => x * x)) :
    HasDerivAt
        (fun h : ℝ => Threepoint.gibbsExp (volume : Measure ℝ)
                        (anharmonicPotential lam alpha gamma)
                        (fun x : ℝ => x) t h (fun x : ℝ => x))
        (-t * Threepoint.gibbsCov (volume : Measure ℝ)
                (anharmonicPotential lam alpha gamma)
                (fun x : ℝ => x) t 0
                (fun x : ℝ => x) (fun x : ℝ => x))
        0
```

The instantiation of `gibbsExp_deriv_eq_neg_t_cov` for the anharmonic
potential. Conclusion: `∂_h ⟨x⟩_h |_{h=0} = -t · Var(x)`.

**Rationale.** Pairs with Candidate A. The conjunction (A + C) is
the "FDT and cross-susceptibility" pair named in the v52 direction.
Note no harmonic mirror of this exists in the laplace seabed —
the harmonic case was only formalised at the second-cumulant
level. C is therefore a *new* harmonic-anharmonic-symmetric
instantiation, not a strict mirror. ~25 lines.

### Candidate D — Bundle A + C + their asymptotic capstones

A single tide that lands four theorems: A, C, and the two
asymptotics `t · A → α/λ³` and `t · C → -1/λ` (via
`cov_self_anharmonic_asymptotic`). ~100-150 lines.

**Rationale.** Closes out the narrative completely; the
yesterday-retro asked for "FDT and cross-susceptibility" capstones,
and D supplies both at conditional + asymptotic granularity.

**Risk.** Asymptotic forms need uniform-in-`t` hypotheses; the
statement gets ugly. May be cleaner to ship A + C conditional only,
defer asymptotic capstones to a strict-improvement follow-up.

## My vote (pre-GPT)

**Candidate D**, with a fallback to **A + C** if the uniform-in-`t`
hypothesis on the asymptotic side proves awkward.

A + C alone is the strict "consume the instance" capstone the retro
asked for. Adding B and the C-asymptotic is value-add if cheap and
deferrable if not.

## Numerical check

Verified both identities by Gaussian quadrature against finite-difference at
λ=1, α=0.5, γ=1 (admissible: α²=0.25 < 3λγ=3), for t ∈ {1, 5, 20, 100}.

| t   | ∂_h⟨x⟩\|_{h=0} (FD) | -t·Var(x) (FDT) | rel. err |
|-----|---------------------|-----------------|----------|
| 1   | -0.78759            | -0.78759        | 1e-9     |
| 5   | -0.94653            | -0.94653        | 1e-9     |
| 20  | -0.98698            | -0.98698        | 1e-9     |
| 100 | -0.99747            | -0.99747        | 1e-9     |

| t   | ∂_h Cov_h(x,x)\|_{h=0} (FD) | -t·κ₃(x,x,x) (κ₃ id) | rel. err |
|-----|------------------------------|-----------------------|----------|
| 1   | 0.10687                      | 0.10687               | 3e-9     |
| 5   | 0.06378                      | 0.06378               | 8e-9     |
| 20  | 0.02212                      | 0.02212               | 1e-8     |
| 100 | 0.00488                      | 0.00488               | 1e-8     |

Both abstract identities are confirmed to ~1e-8 relative accuracy.

Asymptotic capstones (at λ=1, α=0.5):

| t   | ∂_h⟨x⟩\|_{h=0} | predicted -1/λ | t · ∂_h Cov\|_{h=0} | predicted α/λ³ |
|-----|----------------|-----------------|----------------------|-----------------|
| 1   | -0.78759       | -1.0            | 0.10687              | 0.5             |
| 5   | -0.94653       | -1.0            | 0.31889              | 0.5             |
| 20  | -0.98698       | -1.0            | 0.44235              | 0.5             |
| 100 | -0.99747       | -1.0            | 0.48769              | 0.5             |

Convergence to the predicted asymptotes is clean. The first-cumulant FDT
asymptotic is `∂_h⟨x⟩|_{h=0} → -1/λ` (no `t` factor; -t·Var ~ -1/λ since
t·Var → 1/λ). The cross-susceptibility asymptotic is
`t · ∂_h Cov_h(x,x)|_{h=0} → α/λ³` (with `t` factor; -t·κ₃ ~ α/(λ³t) so
t·(-t·κ₃) → α/λ³).

Script: `/tmp/anharmonic_fdt_check.py`. Both identities and both asymptotes
hold; ready for Step 3.

---

## Resume (2026-05-30)

Resumed by a tide-pick auto-loop session. The 2026-05-25 WIP left the two
identities proven *conditionally* on `GibbsObservable` witnesses for
`x, x², x³`; the v2 docstring estimated discharging them as a "441-line"
multi-tide undertaking. In fact the harmonic side already solved exactly
this shape in `HarmonicGibbsObservableMonomials.lean`, and the anharmonic
`partition_hasDerivAt` field already built the coercivity-domination
machinery. The remaining work was a faithful mirror, ~210 lines.

**Proceed-without-GPT.** This is a mirror-shaped resume: the candidate was
already deliberated (the WIP), the target mirrors an already-merged proof
(`HarmonicGibbsObservableMonomials`), and the underlying identities are
numerically validated above (~1e-8) and in the FDT experiment-log. No fresh
GPT consult was run; correctness is machine-checked by `lake build`.

## Step 3 hand-off / Result

New file `Laplace/OneD/AnharmonicGibbsObservableMonomials.lean`:

- `integrable_abs_pow_mul_exp_neg_t_anharmonic (m : ℕ)` — general
  integrability of `|x|^m · exp(-t·L_anh)`, generalising the `m=0,1`
  witnesses already in `AnharmonicGibbsRegularity`.
- `Threepoint.anharmonic_id_gibbsObservable_pow (k : ℕ)` — the
  `GibbsObservable` instance for `x^k`, via
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with dominator
  `t·exp(t/(2c))·|x|^(k+1)·exp(-(t/2)·L_anh)`.
- Three multiplicative wrappers: `_id`, `_mul_self`, `_mul_mul_self`.

Two helpers in `AnharmonicGibbsRegularity.lean` un-privated for reuse:
`anharmonic_perturbed_pointwise_hasDerivAt`,
`anharmonic_perturbed_pointwise_bound`.

`AnharmonicFDT.lean`: both `gibbsExp_deriv_anharmonic_id_id_eq` and
`gibbsCov_deriv_anharmonic_id_id_id_eq` are now **unconditional** (the
`GibbsObservable` hypotheses removed, discharged via the wrappers).

**Commit:** `c331ac2` on `tide/anharmonic-fdt-capstone`.
Full library builds (8304 jobs), no sorries, no lint warnings.

**Deferred follow-up:** the asymptotic capstones (`∂_h⟨x⟩|_{h=0} → -1/λ`
and `t·∂_h Cov|_{h=0} → α/λ³`) — numerically confirmed above — still need
the `∀ t`-quantified observable witnesses composed with the moment
asymptotics. A clean next tide.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-fdt-capstone.tex`
