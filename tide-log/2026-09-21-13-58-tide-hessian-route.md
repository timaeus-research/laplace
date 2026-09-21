# Tide: the Hessian route with only positive definiteness

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." (auto run on the Sanity on Sampling mathematics; this tide turns the note's four Hessian-route equations `eq:cov`, `eq:llc`, `eq:mean`, `eq:covK` into theorems whose only Gaussian input is `P.PosDef`, and adds the LLC `→ d/2` and the exactness of `eq:mean` on quadratic valleys.)
**Seabed:** laplace, `main` at c430f7a; worktree `laplace-tide-hessian-route`, branch `tide/hessian-route`
**Started:** 2026-09-21 (UTC, see file name)

## Context

The note tags `eq:cov`, `eq:llc`/`eq:mean` and `eq:covK` with the seabed's `gibbsCov_first_order_rate_sharp`,
`gibbsExpectation_first_order_rate_explicit` and `gibbsCov_first_order_rate_explicit`. Each of those takes a Gaussian hypothesis
package (`LaplaceCovHypotheses`, `LaplaceCov4MomentHypotheses`, `LaplaceCov6MomentHypotheses`) on the pair `(H, Hinv)`, which the
tides `gaussian-moments-posdef` and `gaussian-moments-high` discharged for `H = matCLM P`, `Hinv = matCLM P⁻¹`, `P.PosDef`
(`laplaceCovHypotheses_matCLM`, `laplaceCov4MomentHypotheses_matCLM`, `laplaceCov6MomentHypotheses_matCLM`). The note's `eq:llc`
claims `t⟨K⟩ → d/2` at `γ = 0` and `eq:mean`'s cubic term is `−½ S (tT:S)`; the seabed's explicit theorem gives
`2t⟨φ⟩ → trASig A Hinv − ⟨Hinv a, T:Hinv⟩` for an observable with tensor package `(a, A, Φ)`.

## Candidates v1 (Claude)

**A. Turnkey Hessian route.**

1. `gibbsCov_first_order_rate_sharp_posDef`, `gibbsExpectation_first_order_rate_explicit_posDef`, `gibbsCov_first_order_rate_explicit_posDef`:
   the three tagged theorems with `(H, Hinv) := (matCLM P, matCLM P⁻¹)`, `P.PosDef`, and no `hGauss` (the only remaining hypotheses are the
   potential/observable approximation packages and `[Nonempty ι]`).
2. `quadObservable P : ObservableTensorApprox (fun w => ½ quadForm (matCLM P) w) 0` — the exact quadratic `K = ½ wᵀPw` as an observable with
   gradient `0`, Hessian `A = matCLM P`, `Φ = 0`, all remainders `0` (needs the sup-norm bound `|½ wᵀPw| ≤ ½ (∑ᵢⱼ |Pᵢⱼ|) ‖w‖²`).
3. `trASig_matCLM_inv : trASig (matCLM P) (matCLM P⁻¹) = card ι`, and hence **`eq:llc` for any regular potential**:
   `llc_first_order_rate_posDef : ∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀, |2 t ⟨½ wᵀPw⟩_{V,t} − card ι| ≤ K/t` for every `V` with
   `PotentialQuinticApprox V (matCLM P)` — the note's "`t⟨K⟩ → d/2` when `γ = 0`" as a theorem, with an `O(1/t)` rate.
4. `meanShift t H T := −½ (tH)⁻¹ *ᵥ (t • contractT T (tH)⁻¹)` (the functional of `eq:mean`'s cubic term, in the notation of `OneLoop.lean`), and
   `meanShift_quadValley`: for the quadratic valley of `ValleyQuadratic.lean`, `meanShift t H T = ![0, b/t]`, which is exactly the Gibbs mean
   minus the minimiser (`gibbsExpectation_quadValley_fst`, `_snd`): `eq:mean`'s first-order term is exact on quadratic valleys, like `eq:oneloop`.

Rationale: the four equations the note actually tags get hypothesis-light targets; the two new theorems (3, 4) are the note's two remaining
Hessian-route claims. Closed forms: `card ι` and `(0, b/t)` (numerical check below).

**B. Also the `γ > 0` version of `eq:llc` for regular potentials** (`½ tr(tH P⁻¹)` with `P = tH + γ`): needs the seabed's expansion for the
localised potential `tL + (γ/2)|w − w₀|²`, whose Hessian package is `t`-dependent; not a one-tide item. Skip.

**C. Only 1** — too thin.

Claude's preference: A.

## Numerical check

`scratchpad/numcheck17.py`. Mean shift `−½ S (tT:S)` on the quadratic valley tensors at `(μ, b, c, a, t) = (0.3, 1.5, −0.7, 0.8, 4)` gives
`(0, 0.375) = (0, b/t)`, and at `(−1.2, 0.4, 2, 3, 7)` gives `(1e-16, 0.0571…) = (0, b/t)`. LLC: for the non-Gaussian regular potential
`V = ½wᵀPw + 0.3x³ + 0.2xy² + ½(x⁴ + y⁴)` in `d = 2`, `2t⟨½wᵀPw⟩ = 1.7475, 1.9147, 1.9760` at `t = 20, 80, 320`, with `t(2t⟨K⟩ − 2) = −5.05, −6.83, −7.67`
(converging: the `O(1/t)` rate).

## GPT-6 Astra v1

Saved verbatim in `gpt_hessian_route_v1.md`. Summary: (a) confirmed: for the quadratic observable `K = ½wᵀPw` with `a = 0` the cubic
correction vanishes and `trASig(P, P⁻¹) = d`, so `|2t⟨K⟩ − d| ≤ C/t`; GPT stresses distinguishing this `K` from the loss `V` itself, so the
tide also packages `V` as an observable (`potentialObservable`, gradient `0`, Hessian `P`, tensor `T`) and proves `2t⟨V⟩ → d` too — the
note's LLC is `t⟨L⟩`; (b) confirmed the `eq:mean` normalisation (`−½ S (tT:S) = −(1/2t) H⁻¹(T:H⁻¹)`) and the valley value `(0, b/t)`.
Lean: a sup-norm proof of `|wᵀPw| ≤ (∑|Pᵢⱼ|)‖w‖²` via `norm_le_pi_norm`, `Finset.abs_sum_le_sum_abs`, `mul_le_mul`; `Φ_symm` for the zero
tensor by `simp`; the `poly_growth` field with witnesses `(C, 2)`. Cheap extras adopted: the quintic package for `K` (odd part zero), so
`eq:covK` specialises to `φ = K` (`covK_first_order_rate_posDef`); GPT notes the closed form `t² Cov(K, ψ) → ½ tr(A_ψ Σ) − ⟨Σ a_ψ, T:Σ⟩`
(cubic term with *twice* the coefficient of `t⟨ψ⟩`) and `t² Var(K) → d/2`, but says proving the `cov2Coefficient` simplification is a
separate algebraic task — left as a follow-up. Votes **A** plus the quintic package.

## Vote
- Claude: candidate A (plus `potentialObservable` and the quintic package for `K`)
- GPT-6 Astra: candidate A (same)

Agreed. Note: `cov2Coefficient` was `private` in `CovarianceExplicit.lean`, which made the tagged theorem's statement unnameable from outside;
this tide makes it (and `cov2Coefficient_full`) public.
