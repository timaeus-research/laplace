# Tide: fulllaw-frame

**Direction (user):** auto run on the Sanity-on-Sampling mathematics; this tide: E8 in the commuting eigenframe — the exact closed-form full law when the `Dᵢ` share the Hessian eigenframe, its LLC, the exact anchored-scaling slope `∑ⱼwⱼ/(1−qⱼ)`, and the first-order diagnostic understating it.
**Seabed:** laplace, commit d4f3d62 (tide 116 `FullLawScaled`; tide 115 `FullLawResolvent`; `FullStep`, `Lyapunov`, `MinibatchBudget`)
**Started:** 2026-09-23 (UTC)

## Candidates v1 (Claude)

Setting: `A = U diag(a) Uᵀ` (`a = 1 − hp`), `Dᵢ = U diag(dᵢ) Uᵀ` (the noise-Jacobians share the eigenframe), `B(X) = ∑ᵢDᵢXDᵢᵀ`,
`N̂ = UᵀNU`, `vⱼ = ∑ᵢdᵢⱼ²`. In the frame `(Uᵀ(AXAᵀ)U)ₖₗ = aₖaₗX̂ₖₗ` and `(UᵀB(X)U)ₖₗ = (∑ᵢdᵢₖdᵢₗ)X̂ₖₗ`, so the full law `X = AXAᵀ + N + cB(X)`
is *entrywise* in the frame.

- **A (exact full law in the frame).** `frameFullFixed U a c d N := U · [N̂ₖₗ/(1 − aₖaₗ − c∑ᵢdᵢₖdᵢₗ)] · Uᵀ` is a fixed point of `fullStep (ulaStep P h) N D c`
  whenever every denominator is nonzero (`stateTerm_frame_apply`, `fullStep_frameFullFixed`); under the contraction hypothesis `hK` it *is*
  `fullFixed` (`frameFullFixed_eq_fullFixed`, by `eq_fullFixed_of_fixed`). Rationale: the first exact closed form for the full law (tides
  107/114/115/116 only bound or expand it); the natural test case for the E8 story.
- **B (its LLC).** `tr(H·frameFullFixed) = ∑ⱼλⱼN̂ⱼⱼ/(1 − aⱼ² − cvⱼ)`; with minibatch noise `N̂ⱼⱼ = 2h + h²t²Ĉⱼⱼ`:
  `(t/2)tr(HΣ_full) = (t/2)∑ⱼλⱼ(2h + h²t²Ĉⱼⱼ)/(1 − (1−hpⱼ)² − cvⱼ)` (`trace_frameFullFixed`, `frame_llc_minibatch`).
- **C (exact slope at the anchored scaling).** `h = η/t`, `pⱼ = tλⱼ + g`, fixed `C, dᵢ, c` with `qⱼ := cvⱼ/sⱼ < 1`, `sⱼ = 1 − αⱼ² = ηλⱼ(2−ηλⱼ)`:
  `(LLC_full − LLC^{ULA})/t → σ_full = ½∑ⱼλⱼη²Ĉⱼⱼ/(sⱼ − cvⱼ) = ∑ⱼwⱼ/(1−qⱼ)`, `wⱼ = ½λⱼη²Ĉⱼⱼ/sⱼ = ηĈⱼⱼ/(2(2−ηλⱼ))` (`frame_slope_tendsto`,
  `frame_slope_eq_sum_weight`). Per mode `(t/2)λⱼ[(2h + η²Ĉⱼⱼ)/(1−ρⱼ²−cvⱼ) − 2h/(1−ρⱼ²)]`: the `2h` pieces contribute `O(1)`, the `η²Ĉⱼⱼ` piece `Θ(t)`.
- **D (the first-order diagnostic understates).** In the frame `(UᵀB(Σ∞)U)ⱼⱼ = vⱼŜ∞ⱼⱼ`, so tide 116's `σ₁ = ½c∑ⱼλⱼvⱼη²Ĉⱼⱼ/sⱼ² = ∑ⱼwⱼqⱼ` and
  `σ_mb = ∑ⱼwⱼ`; hence `σ_mb + σ₁ = ∑ⱼwⱼ(1+qⱼ) ≤ ∑ⱼwⱼ/(1−qⱼ) = σ_full` with exact deficit `∑ⱼwⱼqⱼ²/(1−qⱼ)` (`sigma1_frame_eq`,
  `firstOrder_slope_eq_sum_weight`, `frame_slope_sub_firstOrder_eq`, `firstOrder_le_frame_slope`). Rationale: quantifies GPT's tide-116 remark that
  the first-order diagnostic `R₁` understates the effect near `qⱼ = 1`.

## Numerical check

`numcheck117.py` (`d = 3`, `n = 2`, `η = 0.3`, `g = 0.5`, `c = 0.05`, random `Q`, `C`, `dᵢ`): the closed form has fixed-point residual `1e−16` and
agrees with the iterated full step to `2e−16`; `fullLipschitz = 0.925 < 1` at `t = 10³`; `σ_full = ∑wⱼ/(1−qⱼ) = 0.536421`,
`σ_mb + σ₁ = ∑wⱼ(1+qⱼ) = 0.532009`, deficit `∑wⱼqⱼ²/(1−qⱼ) = 0.004412` (exact match); `(LLC_full − LLC^{ULA})/t = 0.534731, 0.536393, 0.536420,
0.536421` at `t = 10, 10², 10³, 10⁴`. `q = (0.101, 0.032, 0.182)`.

## GPT-6 Astra v1

Full response in `gpt_fulllaw-frame_v1.md`. Vote: "formalise A–D, including direct uniqueness and the `aⱼ² + cvⱼ < 1` denominator lemma; add the
ratio if cheap, and defer noncommuting extensions."

## Status

Paused 2026-09-25 before Step 3 (the user stopped the auto loop; the SRU packaging of tides 21/115/116 took priority). Candidates, numerical
check and consult are recorded above; no Lean was written. Resume from `## Candidates v1` with the generator plan: `frameFullFixed`,
`stateTerm_frame_apply`, `fullStep_frameFullFixed`, `frameFullFixed_eq_fullFixed`, `trace_frameFullFixed`, `frame_llc_minibatch`,
`frame_slope_tendsto`, `sigma1_frame_eq`, `firstOrder_le_frame_slope`.
