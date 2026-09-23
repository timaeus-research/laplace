# Tide: fulllaw-llc

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: the exactness gap flagged in tide 101 — the LLC mean under the seabed's *full* (state-dependent) minibatch covariance law `Σ = AΣAᵀ + N + c∑ᵢDᵢΣDᵢᵀ` (`fullFixed`, `Dᵢ = Hᵢ − H` the per-sample Hessian deviations, `c = minibatchCoeff`): trace monotonicity for PSD-ordered covariances in the frame, hence `(t/2)tr(HΣ_full) ≥ (t/2)tr(HΣ^{mb}) + (t/2)c·tr(H∑ᵢDᵢΣ^{mb}Dᵢᵀ) ≥ (t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) ≥ (t/2)∑λᵢ/(pᵢκᵢ)`, with the first-order Hessian-fluctuation term in frame coordinates.
**Seabed:** laplace, commit 8e723d2 (tide 106 `minibatch-scaled` landed)
**Started:** 2026-09-23T08:37Z

## Candidates v1 (Claude)

Frame `U` diagonalising `P` (`p`) and `H` (`λ ≥ 0`); `A = ulaStep P h`, `N = minibatchNoise h t C`, `Σ^{mb} = lyapunovVia U ρ N` (the additive-law fixed point), `Σ_full = fullFixed A N D hc hK` under the seabed's contraction hypothesis `fullLipschitz A D c < 1`; `stateTerm D X = ∑ᵢDᵢXDᵢᵀ`.
- **A** (frame trace order): `trace_mul_nonneg_frame`: `X ⪰ 0 ⇒ 0 ≤ tr(HX)` (`tr(HX) = ∑λᵢ(UᵀXU)ᵢᵢ`, PSD diagonal); `trace_mul_le_frame`: `Y − X ⪰ 0 ⇒ tr(HX) ≤ tr(HY)`.
- **B** (E8 full law): `fullFixed_trace_ge`: **`tr(HΣ^{mb}) + c·tr(H·stateTerm D Σ^{mb}) ≤ tr(HΣ_full)`** (from the seabed's first-order domination `Σ_full − Σ^{mb} − c·stateTerm D Σ^{mb} ⪰ 0`), `stateTerm_trace_nonneg`: `0 ≤ tr(H·stateTerm D Σ^{mb})`, hence `tr(HΣ^{mb}) ≤ tr(HΣ_full)`; the LLC chain `fullLaw_llc_ge`: **`(t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) + (t/2)c·tr(H·stateTerm D Σ^{mb}) ≤ (t/2)tr(HΣ_full)`** and `ula_llc_le_minibatch_llc_frame`: `(t/2)∑λᵢ/(pᵢκᵢ) ≤ (t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ)` (`Ĉᵢᵢ ≥ 0`).
- **C** (the first-order term in the frame): `trace_stateTerm_frame`: `tr(H∑ᵢDᵢSDᵢᵀ) = ∑ᵢ∑ⱼλⱼ∑ₖₗ(UᵀDᵢU)ⱼₖ(UᵀSU)ₖₗ(UᵀDᵢU)ⱼₗ` — the Hessian fluctuations enter through their frame entries against the full `Ŝ`.
- **D** (optional): the mean of the energy needs only the covariance — `E[½uᵀHu] = ½tr(HΣ) + ½mᵀHm` for any law with covariance `Σ` — the seabed's Gaussian formulas already give this; a non-Gaussian version would need a general second-moment formalism (deferred).

## Numerical check

`numcheck107.py` (3D, 5 random PSD per-sample Hessians, `m = 2`, `t = 20`, `g = 0.7`, `h = 0.1/t`, random PSD `C_g`): the Lipschitz constant is below 1; the additive and full fixed points converge; `Σ_full − Σ^{mb} ⪰ 0` and `Σ_full − Σ^{mb} − c·stateTerm ⪰ 0`; the trace chain holds; tide 101's closed form matches `tr(HΣ^{mb})`; the frame formula for the first-order term matches.
```
Lipschitz constant 0.9555375255042474 (need < 1)
fixed point residuals 0.0 0.0
eigmin(Sf - Smb) 0.000543471855280542  eigmin(Sf - Smb - first) 0.00043190053140401507
tr(H Sf)=0.181582 >= tr(H Smb)+c tr(H stateTerm)=0.177847 >= tr(H Smb)=0.176772 >= tr(H Sula)=0.151427
tide101 closed form tr(H Smb) = 0.1767722109670613
first-order trace tr(H sum D Smb D^T) = 1.433138484763425  frame formula 1.4331384847634276
```

## GPT-6 Astra v1

Verbatim in `gpt_fulllaw_llc_v1.md` (prompt in `gpt_fulllaw_llc_v1_prompt.md`). Summary:
- **A–C correct**; B is a valid lower-bound chain (`t ≥ 0`, `Ĉ ⪰ 0`, `pᵢκᵢ > 0`). **But `c·B(S)` is a one-step lower correction, not the exact
  first-order correction in `c`**: with `T(X) = AXAᵀ`, `B(X) = ∑DᵢXDᵢᵀ`, `R = (1 − T)⁻¹ = ∑ᵣTʳ`, `F = S + cRB(S) + O(c²)`, so the genuine leading LLC
  correction is `(t/2)c·tr(HRB(S)) ≥ (t/2)c·tr(HB(S))` (scalar example: `F = N/(1−a²−cd²)`, `S = N/(1−a²)`, first-order increment `cd²S/(1−a²)`).
  Cheap upper bound `‖F − S‖ ≤ c‖B(S)‖/(1 − q)`, `q = ‖A‖‖Aᵀ‖ + c∑‖Dᵢ‖‖Dᵢᵀ‖`, hence `0 ≤ tr(HF) − tr(HS) ≤ d‖H‖c‖B(S)‖/(1−q)`; a relative bound needs
  `K(S) ⪯ βS`. C is right; no simultaneous diagonalisation of the `Dᵢ` is needed.
- **Scaling**: the one-step term is `O(1)` in `t` at `h = η/t` (`(η²f/2)tr(HB(S̄))`, `f = (1−m/n)/(m(n−1))`), but the true leading correction includes
  the resolvent, `R = O(η⁻¹)` for small `η`, so it is typically `O(η)` where the one-step term is `O(η²)`; the sample sum cancels the apparent
  `1/n` (scaling is fluctuation size over `m`, not `mn`); the constant-`C` bias is `O(ηt·tr Ĉ)` with the batch factor already inside `Ĉ`. Suggested
  prose: "the additive-law formula captures the constant-covariance minibatch bias; the full law adds a nonnegative Hessian-fluctuation correction
  whose one-step contribution is an explicit lower bound and whose leading perturbative contribution includes propagation through the additive
  Lyapunov resolvent; at fixed `ht = η` it is `O(1)` in temperature whereas the constant-covariance bias can grow linearly in temperature."
  The LLC-mean bridge `E[(t/2)uᵀHu] = (t/2)tr(HΣ) + (t/2)μᵀHμ` needs only a centred stationary law with finite second moments (no Gaussianity);
  the covariance fixed-point theorem alone does not prove existence of that law.
- **Lean**: prove A as two reusable lemmas; keep B abstract in `S` and instantiate `lyapunovVia` last; apply monotonicity to `F − (S + cB(S)) ⪰ 0`;
  for C prove `UᵀB(S)U = ∑D̂ᵢŜD̂ᵢᵀ` first; explicit associativity and `Finset.sum_comm`.
- **Cheap additions**: (1) monotone finite-iterate lower bounds `S = X₀ ⪯ X₁ ⪯ … ⪯ F`, `X_k = S + c∑_{j<k}LʲB(S)`, hence monotone LLC lower bounds
  converging to `F`; (2) `D = 0` and `c = 0` recover equality (uniqueness corollaries); (3) strictness: `tr(HB(S)) > 0` when `S ≻ 0` and some row
  `j` of some `D̂ᵢ` is nonzero with `λⱼ > 0`.
- **Vote: ship A–C, call B a one-step lower bound rather than the exact first-order correction, add monotone iterates and zero-noise equality,
  and explain the resolvent-leading correction and scaling in prose.**

Adopted: A–C with the "one-step lower bound" wording; the monotone iterate bounds (`fullStep_iterate_trace_mono`, `fullStep_iterate_trace_le`) and the
zero-noise equalities (`fullFixed_eq_of_c_zero`, `fullFixed_eq_of_D_zero`). Deferred: the resolvent expansion and the explicit upper bounds,
strictness.

## Vote
- Claude: A–C (+ iterate bounds, zero-noise equality)
- GPT-6 Astra: A–C as one-step lower bounds (+ monotone iterates, zero-noise equality)

## Result

Commit `eef6960` on `tide/fulllaw-llc`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/FullLawLLC.lean` (     247 lines).
A–C as voted (B relabelled a one-step lower bound per GPT), plus the monotone iterate bounds and zero-noise equalities.
Lemmas: `posSemidef_transpose_mul_mul`, `trace_mul_nonneg_frame`, `trace_mul_le_frame`, `fullFixed_trace_ge`, `stateTerm_trace_nonneg`,
`fullFixed_trace_ge'`, `ula_llc_le_minibatch_llc_frame`, `fullLaw_llc_ge`, `trace_mul_conj_apply`, `trace_stateTerm_frame`,
`fullStep_iterate_trace_mono`, `fullStep_iterate_trace_le`, `fullFixed_eq_of_c_zero`, `fullFixed_eq_of_D_zero`.

Surprises: the core compiled on the third round (omit bookkeeping, a swapped summation order fixed by `Finset.sum_comm`, and a `rw` that
already closed the goal). Mathematically GPT corrected the framing: `c∑DᵢSDᵢᵀ` is the one-step lower correction, not the first-order
correction in `c` — the latter is propagated through the additive Lyapunov resolvent `R = (1−T)⁻¹`, `F = S + cRB(S) + O(c²)`, and is `O(η)`
rather than `O(η²)` at small step; the seabed's finite iterates `fullStep^k(S)` make the missing propagation visible as monotone lower bounds.
