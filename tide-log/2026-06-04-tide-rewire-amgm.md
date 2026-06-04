# Tide: rewire amgm to lean-common

**Direction (user):** "Rewire" — wire the consumer repos onto the `lean-common`
modules promoted this session, dropping their local copies. (Choice
"Push lean-common, then git-dep".) This is the laplace pilot consumer.
**Seabed:** laplace, commit 158bb04 at start
**Started:** 2026-06-04

## What this tide is

Not a formalisation step — a *consumer-rewiring* step. This session promoted
four reusable cores into `lean-common` (MoorePenrose, Majorization, AmGm, plus
the existing NatBits/HCR). The promotions were deliberately additive: new files
in `lean-common` that nothing imported yet, so they never disrupted concurrent
work in the consumer repos. This tide closes the loop for the first consumer:
laplace's `amgm_t_abs_x` — the scaled weighted AM–GM bound
`t·|x| ≤ tc/2·x² + t/(2c)` — was transplanted verbatim into
`lean-common`'s `Common/AmGm.lean`. Here we point laplace at it and drop the
local copy, validating the whole git-dependency mechanism end-to-end.

## The rewire

1. **Dependency add.** Appended to `lakefile.toml`:
   ```toml
   [[require]]
   name = "lean-common"
   git = "https://github.com/timaeus-research/lean-common.git"
   rev = "511ee60"
   ```
   `511ee60` is the lean-common tip with the *fixed* manifest (the spurious
   `Threepoint` package entry removed — see "Manifest hygiene" below) and all
   five Common modules. `lake update lean-common` resolved cleanly; the new
   dep's Mathlib pin (`8a178386`, v4.29.0) matches laplace's, so no
   transitive-Mathlib conflict.
2. **Import + drop.** In `Laplace/OneD/AnharmonicGibbsRegularity.lean`: added
   `import Common.AmGm`, deleted the entire local `theorem amgm_t_abs_x`
   (docstring through `exact le_of_mul_le_mul_left h_mul_le h2c_pos`, ~20 lines).
3. **Qualify call sites (2).** Both uses — `AnharmonicGibbsRegularity.lean:229`
   and `AnharmonicPartitionDerivGeneralH.lean:66` — rewritten from the bare
   `amgm_t_abs_x t c ht hc_pos x` to `Common.AmGm.amgm_t_abs_x t c ht hc_pos x`
   (identical signature, so a behaviour-preserving substitution; no `open` added,
   so nothing else in scope shifts). The second call site is in a *different*
   file that had been consuming the local theorem transitively through the
   import chain `AnharmonicPartitionDerivGeneralH → … → AnharmonicGibbsRegularity`;
   that chain now transitively pulls `Common.AmGm`, so no extra import is needed
   there.

## Manifest hygiene (the prerequisite)

The first attempt at this rewire (ledger entry 2026-06-04T18:29:02Z, abandoned)
surfaced that lean-common's `lake-manifest.json` carried a spurious `Threepoint`
package entry — an artifact of an earlier experiment. For a consumer like
modes-lean that does *not* independently depend on Threepoint, that stray entry
would contaminate the dependency closure. Fixed at lean-common commit d6ea20e
(merge 511ee60) by regenerating the manifest via `lake update`; the closure is
now `mathlib + plausible + LeanSearchClient + importGraph + proofwidgets +
aesop + Qq + batteries + Cli`, Mathlib pin preserved. For laplace specifically
the entry was a non-issue (laplace legitimately depends on Threepoint —
`AnharmonicGibbsRegularity.lean` imports `Threepoint.CrossSusceptibility`), but
the fix is correct hygiene for the other consumers and is now on the remote.

## Result

`lake build` clean (8306 jobs, "Build completed successfully"); `scripts/sorries`
→ 0 sorry / 0 #exit / 0 native_decide / 0 axiom. The bare `amgm_t_abs_x` no
longer appears as a local definition anywhere in `Laplace/` — only as
`Common.AmGm.amgm_t_abs_x` call sites. The git-dependency-add + import + drop
pattern is validated; modes-lean (Majorization, MoorePenrose) and threepoint
(MoorePenrose) follow the same recipe.

## Numerical check

Not feasible: this is a refactor with no new mathematical content. The two
theorems are textually identical (one was transplanted from the other); the
`lake build` is the proof of behaviour-preservation.

## Suggested follow-ups

- Rewire modes-lean onto `Common.Majorization` (drop local `weighted_sum_le`)
  and `Common.MoorePenrose` (drop local, bridge the ᵀ↔ᴴ notation).
- Rewire threepoint onto `Common.MoorePenrose` (drop local, ᴴ form).
- Once all three consumers are rewired, the cross-repo Moore–Penrose / AM–GM /
  majorization duplication is fully retired into the shared library.
