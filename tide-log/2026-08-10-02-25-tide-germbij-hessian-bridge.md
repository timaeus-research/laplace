# Tide: germbij k=2 superPoly covariance bridge (inverse perimeter 1/3)

**Direction (user):** "Fix the docstring overclaim and proceed with the tides
to fix the gaps" — the gaps being the 2026-08-10 fidelity review's findings
(review log `projects/primer/review-log/2026-08-10-01-29-review-germbij-new-content.md`,
retrospective laplace PR #105). This tide is gap 1: the k=2 superPoly
covariance bridge composing `hessian_recovery` into the note's data language.
**Seabed:** laplace, commit b7566bb.
**Started:** 2026-08-10T02:25Z

## Seabed snapshot

- `LocalLaplaceDomain.covariance i j q` (HessianRecovery.lean:28) — built from
  `posteriorIntegral` quotients, definitionally the same quotients as
  `posteriorMoment` (ExpansionBridge.lean:109).
- `hessian_recovery` (HessianRecovery.lean:74): ∀ i j covariance difference
  =o[𝓝[>]0](q²) ⟹ H₁ = H₂. Allows different L₁/L₂/H₁/H₂ packages.
- `tendsto_normalized_first_moment` (HessianMoments.lean:115): m(w_i)(q)/q → 0.
- `isLittleO_pow_of_superPoly` (ExpansionBridge.lean:57): SuperPoly f ⟹
  (fun q ↦ f((q²)⁻¹)/q^m) =o(q^r) for all m r.
- `posteriorMomentT_inv_sq` (ExpansionBridge.lean:119): the t = q⁻²
  substitution identity.

The review finding this closes: the superPoly-language headline assumes
`hbase` at j = 2 and a shared `H`; the note derives the Hessian from the
data. This tide supplies the missing k = 2 bridge at the H-matrix level.

## Candidates v1 (Claude)

**A (minimal, backed).** `hessian_recovery_of_superPoly_moments`:
for `A : LocalLaplaceDomain L₁ H₁`, `B : LocalLaplaceDomain L₂ H₂`,
if for every i the first-moment families and for every i,j the
second-moment families agree beyond all orders in the temperature —
`SuperPoly (fun t ↦ A.posteriorMomentT (fun w ↦ w i) t − B.posteriorMomentT (fun w ↦ w i) t)` and
`SuperPoly (fun t ↦ A.posteriorMomentT (fun w ↦ w i * w j) t − B.posteriorMomentT (fun w ↦ w i * w j) t)` —
then `H₁ = H₂`.
Proof plan: covariance difference = (second-moment difference) −
[mA(i)·(mA(j)−mB(j)) + (mA(i)−mB(i))·mB(j)]; the moment differences
transport to o(q^r) for every r (m = 0 case of the rate-transport lemma +
the t = q⁻² substitution); the bare first moments are o(q) (from
`tendsto_normalized_first_moment`); products give o(q²); feed
`hessian_recovery`. Rationale: smallest infrastructure delta — pure
Asymptotics plumbing over merged components; exactly discharges the
review's F1 at the H-matrix level.

**B (larger).** A + the derivative-level conclusion
`iteratedFDeriv ℝ 2 L₁ 0 = iteratedFDeriv ℝ 2 L₂ 0`, via a
HigherLaplaceDomain-level `taylorHomogeneousTerm 2 = qform H / 2` bridge
(ray expansions + stage-1 coefficient uniqueness, as in GaussAbsorb but
with the O(‖y‖^k) remainder in place of the Peano field) plus order-2
polarization. Rationale: the composed no-hbase headline (tide 2) needs the
j = 2 equality in tensor form eventually.

**C (too big).** The full recomposed headline without hbase — belongs to
tide 2 (shift wrapper) which needs it anyway; folding it here makes this
tide a programme.

Claude's inclination: A; the tensor tie in B is real work with a different
mechanism (ray uniqueness) and composes better in tide 2 where the shift
wrapper also lives.

## GPT-5.6 Sol v1

Verbatim in `tide-log/gpt_tide_hessian_bridge_v1.md`. Key points: candidate A
correct as written, no missing hypotheses (integrability upstream, junk
values irrelevant, `posteriorMomentT_inv_sq` supplies the eventual equality);
prefer H-matrix level (tensor tie belongs to the recomposition tide); and a
strengthening A′ — first-moment agreement is unnecessary, since each
package's first moments are o(q) independently, so each PRODUCT of first
moments is o(q²) on its own. Second-moment superPoly data alone suffices.

## Vote

- Claude: A′ (agreeing with the strengthening — it is strictly less
  hypothesis for the same conclusion, and tide 2's composition only has
  second-moment data to spend anyway).
- GPT-5.6 Sol: A′.

Agreed: **A′ — `hessian_recovery_of_superPoly_moments`: superPoly-matched
second-moment families alone force H₁ = H₂.**

## Numerical check

Not feasible: structural (Asymptotics plumbing over numerically-verified
merged components; no new closed form).

## Step 3 hand-off

New file `Laplace/Multi/HessianBridge.lean`:
- `covariance_eq_posteriorMoment` (rfl bridge to the ExpansionBridge
  vocabulary),
- `posteriorMoment_coord_isLittleO` (first moments o(q), from
  `tendsto_normalized_first_moment` via `isLittleO_iff_tendsto'`),
- `posteriorMoment_sub_isLittleO` (superPoly transport at m = 0),
- `hessian_recovery_of_superPoly_moments` (headline).

## Result

Committed on tide/germbij-hessian-bridge (1882c1f):
`Laplace/Multi/HessianBridge.lean` — `covariance_eq_posteriorMoment`,
`posteriorMoment_coord_isLittleO`, `posteriorMoment_sub_isLittleO`,
`posteriorMoment_coord_mul_isLittleO`, and the headline
`hessian_recovery_of_superPoly_moments`. Zero sorries, compiled on the
first build. Surprise: none — the m = 0 transport + per-package o(q)
first moments made this pure plumbing, as deliberated.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-10-02-25-tide-germbij-hessian-bridge.tex
