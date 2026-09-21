# Tide: quadratic curved valleys, exact covariance and one-loop exactness

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." (auto run on the Sanity on Sampling mathematics; this tide generalises the Rosenbrock results of tides `sanity-closed-forms` and `oneloop-rosenbrock` to every quadratic curved valley, which is the note's mechanism for finding (4): the leading Laplace error is the cubic coupling of the flat direction into the stiff one.)
**Seabed:** laplace, `tide/oneloop-rosenbrock` at 467f77c (chained; `main` at c923e85); worktree `laplace-tide-valley-quadratic`, branch `tide/valley-quadratic`
**Started:** 2026-09-21 (UTC, see file name)

## Candidates v1 (Claude)

**A. Quadratic valleys `valley μ g a` with `g x = b x² + c x + e` (any minimiser `μ`), `p := g'(μ) = 2bμ + c`.**

1. Exact Gibbs moments from the seabed's shear machinery (`gibbsExpectation_valley_poly`, `harmonicMoment_vec`): `⟨x⟩ = μ`, `⟨x²⟩ = μ² + 1/t`, `⟨y⟩ = g(μ) + b/t` (the valley curvature shifts the mean of `y` off the minimiser by `b/t`), `⟨xy⟩ = μ g(μ) + (μb + p)/t`, `⟨y²⟩ = g(μ)² + (p² + 2g(μ)b)/t + 3b²/t² + 1/(at)`, `⟨L⟩ = 1/t` (so `t⟨L⟩ = 1 = d/2` exactly); covariances `Var x = 1/t`, `Cov(x,y) = p/t`, `Var y = p²/t + 2b²/t² + 1/(at)`.
2. Hessian at the minimiser `H = !![1 + ap², −ap; −ap, a]`, `(tH)⁻¹ = (1/t) !![1, p; p, p² + 1/a]`, and
   `quadValleyCov_eq_laplace_add : Cov = (tH)⁻¹ + (2b²/t²) e_y e_yᵀ`: the whole Laplace error is `2b²/t²` in the `yy` entry, i.e. the cubic coupling of the flat direction (`b = g''/2`), for every quadratic valley. For every direction `v`: `vᵀ Cov v = vᵀ(tH)⁻¹v + (2b²/t²) v_y²`.
3. Taylor tensors at the minimiser: `T_zzz = 6abp`, `T_zzw = T_zwz = T_wzz = −2ab`, `Q_zzzz = 12ab²` (certified by the exact polynomial identity `quadValley_taylor`), and
   `oneLoopPi_quadValley : Π = 2a²b² (p, −1)(p, −1)ᵀ`, `oneLoopCov_quadValley : oneLoopCov t H T Q = Cov`: the one-loop formula is exact for every quadratic valley.
4. Rosenbrock is the case `μ = 1, b = 1, c = e = 0` (`p = 2`): `quadValleyHess 1 1 0 a = rosenHess a`.

Rationale: one coherent generalisation of two landed tides, using only existing machinery; it turns the note's finding (4) from a Rosenbrock observation into a theorem about the family. Closed forms as stated (numerical check below).

**B. Arbitrary polynomial valley floors `g`** (degree ≤ 2 in the moments up to order 4 is what `Fin 5` coefficient matrices allow for `g²`; cubic `g` needs degree 6): out of reach of the seabed's `Fin 5` coefficient interface without extending it. Skip.

**C. Only item 2** (exact covariance) — too small on its own now that the one-loop functional exists.

Claude's preference: A.

## Numerical check

`scratchpad/numcheck13.py` (scipy `dblquad` for the exact moments, numpy `einsum` for the one-loop functional, Taylor identity at random points):

| `(μ, b, c, e, a, t)` | `⟨y⟩ − g(μ) − b/t` | max entry `Cov − ((tH)⁻¹ + (2b²/t²) e_y e_yᵀ)` | max entry `oneLoop − Cov` | Taylor error | `Π/(2a²b²)` |
| --- | --- | --- | --- | --- | --- |
| (0.3, 1.5, −0.7, 2, 0.8, 4) | 2e-16 | 2e-16 | 2e-16 | 3e-18 | `[[0.04, −0.2], [−0.2, 1]]` = `[[p², −p], [−p, 1]]`, `p = 0.2` |
| (−1.2, 0.4, 2, 0, 3, 7) | 1e-17 | 4e-16 | 2e-16 | 6e-17 | `[[1.0816, −1.04], [−1.04, 1]]`, `p = 1.04` |

## GPT-6 Astra v1

Saved verbatim in `gpt_valley_quadratic_v1.md`. Summary: all closed forms in A.1–A.3 confirmed (the Taylor identity
`L(μ+z, q+w) = ½[z² + a(w − pz)²] − ab(w − pz)z² + ½ab²z⁴`; the contractions `Q:S = (12ab²/t) e_z e_zᵀ`,
`T:S = (2ab/t)(p, −1)`, the bubble and tadpole-line matrices as stated; the `zz` terms cancel `−6ab² + 4ab² + 2ab² = 0`).
Lean advice: keep `quadFn`/`valleySlope` named and unfold locally; `field_simp [ha.ne', ht.ne']` when cancelling; a generic
`gibbsExpectation_valley_of_poly` wrapper. Cheap strengthening adopted: `⟨L⟩ = 1/t`, `⟨L²⟩ = 2/t²`, `Var L = 1/t²` for
**every** continuous valley floor `g` (the `Fin 5` interface suffices); the directional identity. Correction to my aside:
`κ₃(y) = 6bp²/t² + 8b³/t³` (not `8b³/t³`), needing degree-six shear moments, not formalised. Votes **A** plus the general-floor
LLC statements.

## Vote
- Claude: candidate A (plus the general-floor `⟨L⟩`, `⟨L²⟩`, `Var L`)
- GPT-6 Astra: candidate A (same additions)

Agreed.

## Result

Committed as `Laplace/TwoD/ValleyQuadratic.lean` (74db0e8), 336 lines, 0 sorries, `lean-state check` clean.

Theorems: `quadFn`, `valleySlope`, `rosenbrock_eq_quadValley`; for every continuous floor `g`:
`gibbsExpectation_valley_of_poly`, `gibbsExpectation_valley_self` (`⟨L⟩ = 1/t`), `gibbsExpectation_valley_self_sq`
(`2/t²`), `gibbsCov_valley_self` (`1/t²`); quadratic floors: `gibbsExpectation_quadValley_{fst, fst_sq, snd, fst_mul_snd,
snd_sq, self}`, `gibbsCov_quadValley_{fst_fst, fst_snd, snd_snd}`; `quadValleyHess`, `quadValleySigma`,
`quadValleyHess_rosenbrock`, `quadValleyHess_smul_inv`, `quadValleyCov`, `quadValleyCov_eq_laplace_add`
(`Cov = (tH)⁻¹ + (2b²/t²) e_y e_yᵀ`), `quadValleyCov_quadForm`; `quadValleyT`, `quadValleyQ`, `quadValley_taylor`,
`contractQ_quadValley`, `contractT_quadValley`, `bubble_quadValley`, `tadpoleLine_quadValley`,
`oneLoopPi_quadValley` (`Π = 2a²b²(p,−1)(p,−1)ᵀ`), `oneLoopCov_quadValley` (exact).

Surprises: none; the Rosenbrock proofs generalised line for line with symbolic coefficient matrices. GPT corrected an
aside of mine (`κ₃(y) = 6bp²/t² + 8b³/t³`, not `8b³/t³`), which is why no third cumulant is claimed here.
