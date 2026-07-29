# Tide-distill: main theorems + comparator machinery (2026-07-28)

## Goal

Pin the seabed's main theorems in a self-contained `Statements.lean`
(human-auditable, deliberately sorried), prove them by delegation in
`Solutions.lean`, and wire up [leanprover/comparator](https://github.com/leanprover/comparator)
verification (config + CI workflow), per the `tide-distill` skill.
Reference implementation: `rlct_markov`.

## Theorem selection (Step 2)

Judged on source-material salience (Susceptibility Primer §4.1 + the
Clusters-to-Circuits three-point paper) and measured transitive import-closure
coverage (`closure_report.py`):

| pinned statement | delegated library theorem | closure |
|---|---|---|
| `cov_anharmonic_asymptotic` | `Laplace.OneD.cov_anharmonic_asymptotic` (primer eq. 4.10) | 7 files, 9.2% of lines |
| `kappa3_anharmonic_asymptotic` | `Laplace.OneD.kappa3_anharmonic_id_id_id_asymptotic` | ⊂ FDT closure |
| `gibbsCov_deriv_anharmonic_asymptotic` | `Laplace.OneD.gibbsCov_deriv_anharmonic_asymptotic` (FDT capstone) | 13 files, 12.9% |
| `gibbsCov_first_order_rate_sharp` | `Laplace.Multi.gibbsCov_first_order_rate_sharp` (primer `lem:laplace_cov`) | 7 files, 23.5% |
| `gibbsExpectation_first_order_rate_explicit` | `Laplace.Multi.gibbsExpectation_first_order_rate_explicit` (primer `lem:laplace_exp`) | ⊂ explicit closure |
| `gibbsCov_first_order_rate_explicit` | `Laplace.Multi.gibbsCov_first_order_rate_explicit` (primer `lem:laplace_cov2`) | 9 files, **67.2%** |
| `gibbsExpectation_kthKth_isEquivalent_rpow` | `Laplace.TwoD.gibbsExpectation_kthKth_pow_pow_isEquivalent_rpow` (2D degenerate family) | 8 files, 4.4% |

**Union: 26 of 68 files, 37,939 of 46,367 lines = 82% of the library.**
Main unrepresented areas: the harmonic track (`OneD/Harmonic*`), the 1D
cumulant/log-partition ladder (`AnharmonicCumulants*`, `AnharmonicPartition*`,
`AnharmonicSusceptibilityGeneralH`), the bounded-prior track
(`QuarticBoundedPrior*`), and the fixed-instance 2D quartic–sextic files
(subsumed by the generic kth–kth family).

The two README/PROGRESS headliners (1D eq. 4.10 + multi sharp) were the
starting point; reading the primer's `\leanref` annotations surfaced that the
EXPLICIT-coefficient theorems (`lem:laplace_exp`, `lem:laplace_cov2`) had
landed in `Multi/CovarianceExplicit.lean` (19.6k lines, 67% of the library on
its own) after PROGRESS.md was last updated — they, not the sharp track, are
the coverage backbone.

## Design decisions (Steps 1 + 3)

* **Defs extraction** (`Laplace/Multi/Defs.lean`, Mathlib-only import
  closure): the multivariate theorems' hypothesis packages are nominal
  `structure`s (`PotentialApprox ⊂ PotentialJetApprox ⊂ PotentialTensorApprox
  ⊂ PotentialQuinticApprox`, the observable mirrors, and the
  `LaplaceCovHypotheses ⊂ 4Moment ⊂ 6Moment` Gaussian packages) — the kernel
  distinguishes duplicated copies, so they were MOVED (names/namespaces
  unchanged) together with the plain defs they reference (`partitionFunction`
  / `gibbsExpectation` / `gibbsCov` (multi), `quadForm`, `gaussianWeight`,
  `gaussianZ`, `dot`, `HasPolyGrowth`, `FubiniIBPHypothesis{,Cubic,Quintic}`,
  `tensorContractMatrix`, `trASig`). Source files import Defs via
  `Multi/Basic.lean`.
* **In-file duplication** for everything transparently duplicable: the 1D and
  2D Gibbs vocabulary, `anharmonicPotential`, `kthPotential`, `addSeparable`,
  `kthKthMomentConst`, and the Threepoint field-perturbed vocabulary
  (`perturbedExpectation`/`perturbedCov`/`thirdCumulant` — external-package
  defs specialised to `W = ℝ`, `μ = volume`, so `Statements.lean` needs no
  Threepoint import).
* `cov2Coefficient` is `private` in `CovarianceExplicit.lean`; the pinned
  statement instead uses an in-file `cov2Coeff` as an explicit function of the
  jet data `(A, Φ, B, T, Σ, b)` — definitionally equal, so delegation closes
  by `exact`.
* Statement names follow the library except `kappa3_anharmonic_asymptotic`
  (dropping the `_id_id_id_` observable marker) and
  `gibbsExpectation_kthKth_isEquivalent_rpow` (dropping `_pow_pow_`).

## Findings / gotchas

* **The root import shim was stale**: `Laplace.lean` was missing 16 modules —
  including `Multi/CovarianceSharp.lean`, `Multi/CovarianceExplicit.lean` (the
  two multivariate headline files!) and the whole FDT/cumulant ladder — so
  `lake build` (and hence CI) had NOT been building them; no oleans existed.
  Fixed the shim; all 16 orphans compile (two pre-existing latent breaks in
  `CovarianceExplicit.lean` surfaced only because of the Defs move — see
  next).
* **Cross-module matcher constants are defeq, not syntactic**: two proofs in
  `CovarianceExplicit.lean` unfolded `tensorContractMatrix` and then `rw`-ed
  with locally-stated `match`-lambdas. Same-file, the match auxiliaries
  coincide; once the def moved to `Defs.lean` the goal's matcher constant
  differs from the proof's local one (defeq but not syntactically equal), so
  `rw` stops firing. Fixes: close by `exact h.trans …` / trailing `rfl`
  (defeq-tolerant) instead of `rw`'s reducible-transparency auto-`rfl`.
* CI note: the `lean-common` dependency is a private repo; the comparator
  workflow authenticates the lake fetch by rewriting the URL with the
  `LEAN_COMMON_READ_TOKEN` action secret (added by Billy this session).

## Faithfulness (Step 4)

Adversarial subagent pass (fresh context, templates/faithfulness-brief.md)
against the primer .tex + the ThreePointFunctions .tex. Verdicts:

* `cov_anharmonic_asymptotic` — **DEVIATES (MAJOR, adjudicated real)**: the
  primer's `eq:cov_anharmonic_1d` asserts `-2α/(λ³t²) + O(t⁻³)`; the library
  theorem (and hence the pin) proves only the limit (`o(t⁻²)`). No rate form
  of `Cov_t[x², x]` exists in the library (only `Cov_t[x,x]` and `⟨x⟩_t` have
  `O2_rate` forms), so this is a genuine gap → **disclosure added** to the
  docstring + README rather than a fix. A rate-strengthening tide is the
  natural follow-up.
* `kappa3_anharmonic_asymptotic`, `gibbsCov_deriv_anharmonic_asymptotic` —
  FAITHFUL; beyond-source framing verified honest (neither paper displays the
  ±α/λ³ values). Adjudicated MINORs fixed: the ThreePoint prior-specialised-
  to-Lebesgue note added to the perturbed-vocabulary section docstring;
  "fluctuation–dissipation identity" renamed to the paper's
  "cross-susceptibility identity".
* `gibbsCov_first_order_rate_sharp`, `gibbsExpectation_first_order_rate_explicit`,
  `gibbsCov_first_order_rate_explicit` — FAITHFUL; the hypothesis-package
  reshaping disclosures judged complete; all constants/signs/rates match the
  source displays term-by-term.
* `gibbsExpectation_kthKth_isEquivalent_rpow` — FAITHFUL as an
  honestly-disclosed beyond-source result.
* Cross-cutting adjudications: (i) `tensorContractMatrix` reads its matrix
  argument transposed vs the primer's `(K:M)ᵢ = ∑ⱼₖ Kᵢⱼₖ Mⱼₖ` — neutralised
  by the symmetry hypotheses in force; a note added to the `cov2Coeff`
  docstring. (ii) The "(4.x)" equation numbers presuppose per-section
  numbering the .tex does not enable (globally it is (12)/(14)/(19)/(20)),
  though the repo's entrenched "(4.10)" suggests the compiled primer numbers
  by section — docstrings switched to label-first citations, keeping "(4.10)
  compiled" only for the entrenched headline anchor.

## Result

* Full build green (8326 jobs): library (incl. the 16 previously-orphaned
  modules) + `Statements` (7 expected `sorry` warnings only) + `Solutions`
  (warning-free). `scripts/sorries`: 0 sorry / 0 #exit / 0 native_decide /
  0 axiom (Statements exempt by design).
* All 7 delegations close by bare `exact` — the pinned statements are
  definitionally the library theorems (including `cov2Coeff` vs the private
  `cov2Coefficient`, and the Threepoint-vocabulary duplicates at
  `W = ℝ`, `μ = volume`).
* `#print axioms` for all 7: `[propext, Classical.choice, Quot.sound]`.
* Coverage: union closure 26/68 files, 82% of lines (recorded in
  `Solutions.lean`'s module docstring).
* **Local comparator pass: PASSED** (`"Your solution is okay!"`, exit 0) —
  reusing the rlct_markov session's builds of `lean4export@v4.29.0` and
  `comparator@master` (toolchain v4.33.0-rc1), invoked as
  `lake env comparator comparator.json` from the repo root with
  `COMPARATOR_LANDRUN=fake-landrun.sh` (dev shim — everything real except the
  sandbox isolation; an adversarial audit is a fresh-host run per comparator's
  README). Pipeline observed: sandboxed lake build of Challenge and Solution
  (full warm replays, green), lean4export of the 7 named statement closures,
  declaration equivalence, axiom check against the permitted triple, kernel
  replay accepted.

## CI addendum (2026-07-29)

Getting the two workflows green surfaced three independent issues, fixed in
fc2242b / 81d5f69 / 8f53846:

* `threepoint` is private too — the `LEAN_COMMON_READ_TOKEN` rewrite worked
  for lean-common on the first CI run, and the next fetch died the same way;
  Billy widened the token's scope to include threepoint, and the same URL
  rewrite now covers both repos in both workflows.
* **`enableArtifactCache = true` breaks comparator's sandboxed replay**: lake
  stores artifacts in `~/.cache/lake`, which the landrun sandbox mounts
  read-only → EACCES on every store → `build failed`. The local
  fake-landrun pass cannot catch this (the shim does not sandbox). Fix: the
  workflow flips the lakefile flag just before the verification step (the
  env override `LAKE_ARTIFACT_CACHE` cannot reach the sandbox — comparator
  forwards only `PATH`/`HOME`).
* `docgen-action` in Lean Action CI exceeds the 6-hour runner limit
  (doc-gen4 renders the whole Mathlib closure) — latent since May, masked by
  the 30-second fetch failure. Split into a manual-only `Docs` workflow;
  Lean Action CI is build-only and now green for the first time.

**CI comparator verdict: PASSED** (run 30416796703, "Your solution is
okay!", kernel replay accepted, 6m17s with the warm lake cache; confirmed
again on the next push). This was a real-landrun run, upgrading the local
dev-shim pass to the genuinely sandboxed check.

## Follow-ups

* A rate-strengthening tide for `Cov_t[x², x]` (`O(t⁻¹)` on `t²·Cov`, closing
  the one disclosed deviation from `eq:cov_anharmonic_1d`).
* Run comparator with real `landrun` on a Landlock-capable host.
* `PROGRESS.md` is stale (predates `CovarianceExplicit.lean`); refresh it or
  fold it into the README.
