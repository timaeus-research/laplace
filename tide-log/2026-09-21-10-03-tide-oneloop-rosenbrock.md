# Tide: the one-loop covariance formula, exact for Rosenbrock

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." (auto run on the Sanity on Sampling mathematics; this tide formalises the note's second-order/one-loop covariance formula, E7.)
**Seabed:** laplace, `main` at c923e85; worktree `laplace-tide-oneloop-rosenbrock`, branch `tide/oneloop-rosenbrock`
**Started:** 2026-09-21 (UTC, see file name)

## Context

The note's E7 section states, for `V = ½xᵀPx + (t/6)Tx³ + (t/24)Qx⁴` (so `P = tH`, `T = D³L(w*)`, `Q = D⁴L(w*)`), the connected two-point function to one loop (`eq:oneloop`):

  `Cov[x] = S + S Π S`,  `Π = -(t/2)(Q:S) + (t²/2) TSST + (t²/2) T·S·(T:S)`,  `S = P⁻¹`,

with `(TSST)ᵢⱼ = Tᵢₖₗ Sₖₖ' Sₗₗ' Tⱼₖ'ₗ'` and `(T·S·(T:S))ᵢⱼ = Tᵢⱼₖ Sₖₗ (T:S)ₗ`; in one dimension `Var = 1/(λt) + (α²/λ⁴ − g/(2λ³))/t²`; and its Findings record that for Rosenbrock `d = 2` the second-order prediction equals the exact variance (the series terminates). The seabed has the exact Rosenbrock covariance (`TwoD/Rosenbrock.lean`: `rosenCov_eq_laplace_add : rosenCov a t = (t • rosenHess a)⁻¹ + (2/t²) • !![0,0;0,1]`) and, in one dimension, the second-order second-moment rate `secondMoment_anharmonic_order2_rate` (`|t⟨x²⟩ − 1/λ − (45A² − 12B)/(λt)| ≤ K/(t√t)`, `A = cubicScale`, `B = quarticScale`) and `mean_anharmonic_asymptotic`.

## Candidates v1 (Claude)

**A. The one-loop functional, its 1D value, and its exactness for Rosenbrock.**

1. `oneLoopCov t H T Q : Matrix (Fin d) (Fin d) ℝ := S + S * oneLoopPi t T Q S * S` with `S = (t • H)⁻¹` and `oneLoopPi t T Q S = -(t/2) • contractQ Q S + (t²/2) • bubble T S + (t²/2) • tadpoleLine T S`, the three contractions written out as finite sums over `Fin d` (`T : Fin d → Fin d → Fin d → ℝ`, `Q : Fin d → Fin d → Fin d → Fin d → ℝ`).
2. `oneLoopCov_oneDim`: for `d = 1`, `H = !![λ]`, `T ≡ α`, `Q ≡ γ`, `λ ≠ 0`, `t ≠ 0`: `oneLoopCov = !![1/(λt) + (α²/λ⁴ − γ/(2λ³))/t²]` (the note's 1D formula, algebra).
3. `var_anharmonic_second_order` (the 1D formula as a theorem about the true variance): for `λ > 0`, `γ > 0`, `α² < 3λγ`,
   `Tendsto (fun t => t² * (Var_t[x] − 1/(λt))) atTop (nhds (α²/λ⁴ − γ/(2λ³)))` under `e^{-t(λx²/2 + αx³/6 + γx⁴/24)}`, from the seabed's `secondMoment_anharmonic_order2_rate` and `mean_anharmonic_asymptotic` via `Var = ⟨x²⟩ − ⟨x⟩²`: `t(t⟨x²⟩ − 1/λ) → (45A² − 12B)/λ = 5α²/(4λ⁴) − γ/(2λ³)` and `(t⟨x⟩)² → α²/(4λ⁴)`.
4. Rosenbrock `d = 2`: `rosenT a`, `rosenQ a` (the cubic and quartic Taylor tensors at `(1,1)`: `T_zzz = 12a`, `T_zzw = T_zwz = T_wzz = −2a`, `Q_zzzz = 12a`, all else `0`), certified by the exact polynomial identity `rosenbrock a (1+z, 1+w) = ½ vᵀHv + (1/6) Σ T v³ + (1/24) Σ Q v⁴`; then
   `oneLoopCov_rosenbrock : oneLoopCov t (rosenHess a) (rosenT a) (rosenQ a) = rosenCov a t` for `0 < a`, `0 < t`.
   Hand computation: `Σ = tS = !![1,2;2,4+1/a]`, `(Q:S)_zz = 12a/t`, `(T:S) = (4a, −2a)/t`, `S(T:S) = (0, −2)/t²`, `TSST = (1/t²)!![16a²+8a, −8a²; −8a², 4a²]`, so `Π = a² !![8, −4; −4, 2] = 2a² vvᵀ` with `v = (2, −1)`, `Σv = (0, −1/a)`, and `SΠS = (2/t²) e_y e_yᵀ`: exactly the correction in `rosenCov_eq_laplace_add`.

Rationale: this is the note's E7 formula and its two checkable instances; every ingredient is in the seabed, so the work is definitions plus finite algebra over `Fin 2` plus one squeeze argument. Closed forms: as stated (numerical check below).

**B. The general second-order coordinate covariance** (`t² (Cov_t[xᵢ, xⱼ] − Sᵢⱼ) → (SΠS)ᵢⱼ` for a smooth potential in `d` dimensions) from the seabed's `CovarianceExplicit` machinery. Blocked: `gibbsCov_first_order_rate_explicit` requires the first observable to have vanishing gradient (`a = 0`), and coordinates do not. Out of scope for one tide.

**C. Only the 1D asymptotic theorem (A.3)** — too small on its own.

Claude's preference: A.

## Numerical check

`scratchpad/numcheck12.py` (numpy/scipy). The functional `S + SΠS` evaluated with `einsum` on the Rosenbrock Taylor tensors
(`T_zzz = 12a`, `T_zzw = T_zwz = T_wzz = −2a`, `Q_zzzz = 12a`, checked against `rosenbrock a (1+z, 1+w)` at random points to 1e-14):

| `a`, `t` | max entry of `oneLoop − ((tH)⁻¹ + (2/t²) e_y e_yᵀ)` | `Π / a²` |
| --- | --- | --- |
| 0.7, 3 | 3.6e-15 | `[[8, −4], [−4, 2]]` |
| 5, 11 | 7.0e-15 | `[[8, −4], [−4, 2]]` |
| 100, 2.5 | 2.7e-11 | `[[8, −4], [−4, 2]]` |

One dimension, `λ = 1.3`, `α = 0.8`, `γ = 2`, `Var_t[x]` by quadrature versus `1/(λt) + (α²/λ⁴ − γ/(2λ³))/t²` (coefficient −0.231084):

| `t` | `Var_t[x]` | formula | `t²(Var − 1/(λt))` |
| --- | --- | --- | --- |
| 30 | 0.0253759617 | 0.0253842653 | −0.238558 |
| 100 | 0.0076689359 | 0.0076691993 | −0.233718 |
| 300 | 0.0025615247 | 0.0025615350 | −0.232004 |

The 1D functional `oneLoopCov t !![λ] α γ` returns the formula value exactly (same table, third column).

## GPT-6 Astra v1

Saved verbatim in `gpt_oneloop_rosenbrock_v1.md`. Summary: the transcription of `eq:oneloop` is the standard one-loop connected two-point function (one quartic vertex contributes `−t`, two cubic vertices `t²`; the tadpole-line term survives after subtracting the mean product); the Rosenbrock hand computation is confirmed term by term (`−6a`, `8a² + 4a`, `2a` for `Π₁₁`); the 1D bookkeeping is confirmed with `cubicScale = α/(6λ^{3/2})`, `quarticScale = γ/(24λ²)`. Lean advice: prove `Π` through staged contraction lemmas rather than one expansion inside the matrix product; nested vectors for `T`; `squeeze_zero'` + `tendsto_iff_norm_sub_tendsto_zero` for the 1D limit, then `hsecond.sub (hmean.pow 2)` and `Tendsto.congr'`. Optional extension: every quadratic curved valley `valley μ g a`, `g = bx² + cx + d`, has exact covariance `[[1/t, p/t], [p/t, p²/t + 1/(at) + 2b²/t²]]` (`p = g'(μ)`) and one-loop correction exactly `2b²t⁻² e_y e_yᵀ`; do not generalise exactness to arbitrary quartic potentials. Votes **A** with staged contraction lemmas.

## Vote
- Claude: candidate A
- GPT-6 Astra: candidate A (staged contraction lemmas; quadratic-valley exactness optional)

Agreed. The quadratic-valley generalisation is noted as a follow-up.
