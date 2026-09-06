# Tide: separable-potential marginal expectation + free-energy additivity

**Direction (user):** laplace separable-potential free-energy additivity + same-coordinate marginal expectation: log Z_2D = log Z_U + log Z_V, and ⟨f∘fst⟩_{U⊕V} = ⟨f⟩_U (mean-level companion to SeparableSameCoordCov) — clean CGF-level extensions of TwoD/AddSeparable
**Seabed:** laplace, commit f5508fc
**Started:** 2026-09-06T16:00Z

## Candidates v1 (Claude)

Extending `Laplace/TwoD/AddSeparable.lean` (the separable-potential factorisation hub) at the
CGF / marginal level:

1. **Marginal expectation** (`gibbsExpectation_addSeparable_fst/_snd`): for `L(x,y)=U(x)+V(y)`,
   `⟨f∘fst⟩_{2D,t} = ⟨f⟩_{U,t}` (the other coordinate integrates out). This is the mean-level
   companion to the existing covariance-level `SeparableSameCoordCov`, and it is currently *inlined*
   inside `gibbsCov_addSeparable_fst_snd_eq_zero` (steps `hExp_f`/`hExp_g`) rather than exposed —
   exposing it makes it reusable API.
2. **Free-energy additivity** (`logPartition_addSeparable`): `log Z_2D = log Z_U + log Z_V`, the
   CGF-level reading of the partition-function factorisation `Z_2D = Z_U·Z_V`
   (`partitionFunction_addSeparable_factor`). The free energy of a separable system is additive.

Both are minimal steps directly on top of `AddSeparable`, in a NEW LEAF file (AddSeparable is a
hub; adding to it rebuilds all dependents and surfaces their pre-existing header warnings — recorded
gotcha).

## GPT-5.5 Pro
Not consulted — these are clean corollaries of the existing `AddSeparable` factorisation lemmas
(`partitionFunction_addSeparable_factor`, `gibbsExpectation_separable_addSeparable`,
`gibbsExpectation_const`); the marginal-expectation proof already exists inlined in the seabed. A
mirror-shaped, low-risk assembly, matching the "proceed-without-GPT" allowance.

## Vote
- Claude: both (marginal expectation `_fst`/`_snd` + free-energy additivity), one leaf file.
- GPT-5.5 Pro: not consulted (see above).

## Numerical check
Not feasible: structural algebraic identities (log of a product; marginalisation of a product
measure). Correctness rests on the `AddSeparable` factorisation lemmas they compose.

## Result

Landed `Laplace/TwoD/SeparableMarginal.lean` (new leaf), built first try (module + full library,
8887 jobs), wired into `Laplace.lean`.

- `gibbsExpectation_addSeparable_fst` / `_snd` — `⟨f∘fst⟩_{2D,t} = ⟨f⟩_{U,t}` (marginalisation).
- `logPartition_addSeparable` — `log Z_2D = log Z_U + log Z_V` (free-energy additivity).

`scripts/sorries` clean (0/0/0/0); axioms = the 3 standard (`propext, Classical.choice, Quot.sound`).

**What surprised us:** nothing mathematically — both first-try. The value was in exposing the
marginal-expectation collapse (previously inlined inside `gibbsCov_addSeparable_fst_snd_eq_zero`) as
reusable named API, and stating the free-energy additivity that the partition factorisation had left
implicit. A clean consolidation tide chosen after confirming (via a portfolio survey) that the
higher-novelty frontiers are all heavy/consult-scale and deserve fresh context.
