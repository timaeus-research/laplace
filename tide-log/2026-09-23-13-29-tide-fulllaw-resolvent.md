# Tide: fulllaw-resolvent

**Direction (user):** auto mode — E8, full law: the exact resolvent identity `Δ = c·R(B(Σ_full))`, the sharper lower bound `Δ ⪰ cR(B(Σ^{mb})) ⪰ cB(Σ^{mb})`, the Neumann bound `‖R(Y)‖ ≤ ‖Y‖/(1−a)`, and the `O(c²)` remainder (GPT's suggested refinement from tides 107/114).
**Seabed:** laplace, commit 80143fe (tide 114 `FullLawUpper`, tide 107 `FullLawLLC`, `Sampler/Lyapunov` (`lyapunovVia_fixed_iff`), tide 104 (`lyapunovVia_posSemidef`, `lyapunovVia_add`, `diagLyapunov_sub_posSemidef`))
**Started:** 2026-09-23-13-29 UTC

## Candidates v1 (Claude)

Setting: `A = I − hP`, `T(X) = AXAᵀ`, `R = (1−T)⁻¹` the Lyapunov resolvent (`lyapunovVia U ρ`, entrywise `Ŷᵢⱼ/(1−ρᵢρⱼ)` in the frame), `B(X) = ∑ᵢDᵢXDᵢᵀ`,
`Σ^{mb} = R(N)`, `Σ_full` the full-law fixed point, `Δ = Σ_full − Σ^{mb}`, `a = ‖A‖‖Aᵀ‖`, `b = ∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖`, `L = a + cb < 1`.

- **A** (`lyapunovVia_smul`, `lyapunovVia_sub`, `fullFixed_sub_eq_resolvent`): `Δ = AΔAᵀ + cB(Σ_full)`, so by uniqueness of the Lyapunov solution
  **`Δ = c·R(B(Σ_full))`** (exact).
- **B** (`lyapunovVia_sub_self_posSemidef`, `fullFixed_sub_sub_resolvent_posSemidef`, `resolvent_stateTerm_sub_posSemidef`): `Δ − cR(B(Σ^{mb})) = cR(B(Δ)) ⪰ 0`
  and `R(Y) − Y ⪰ 0` for `Y ⪰ 0`: **`Δ ⪰ cR(B(Σ^{mb})) ⪰ cB(Σ^{mb})`**, sharpening tide 107's one-step lower bound to the exact first-order term.
- **C** (`norm_lyapunovVia_le`): the Neumann bound **`‖R(Y)‖ ≤ ‖Y‖/(1−a)`** from Banach's estimate at `0` for the additive contraction (`c = 0`).
- **D** (`fullFixed_sub_resolvent_norm_le`): **`‖Δ − cR(B(Σ^{mb}))‖ ≤ c²b‖B(Σ^{mb})‖/((1−a)(1−L))`**: the full law is `Σ^{mb} + cR(B(Σ^{mb})) + O(c²)`.
- **E** (`trace_resolvent_frame`, `fullLaw_llc_first_order`, `fullLaw_llc_ge'`): `tr(H·R(Y)) = ∑ᵢλᵢŶᵢᵢ/(1−ρᵢ²)`, `1−ρᵢ² = hpᵢ(2−hpᵢ)`; the exact
  `(t/2)tr(HΔ) = (t/2)c∑ᵢλᵢ(B̂(Σ_full))ᵢᵢ/(hpᵢ(2−hpᵢ))` and the sharper LLC lower bound `LLC^{mb} + (t/2)c∑ᵢλᵢ(B̂(Σ^{mb}))ᵢᵢ/(hpᵢ(2−hpᵢ)) ≤ (t/2)tr(HΣ_full)`:
  the first-order correction is the one-step term divided by `1−ρᵢ² = O(h)` per mode.

## Numerical check

`numcheck115.py` (tide 114's instance, `a = 0.858`, `L = 0.863`):
```
a=0.8584 b=5.7992 L=0.8628
exact identity  ‖Δ − c R(B(F))‖ = 2.67e-16
eigs(Δ − cR(B(S))) = [7.60e-07 3.23e-06 7.99e-06]  eigs(cR(B(S)) − cB(S)) = [0.00012144 0.00038314 0.00111093]
Neumann: ‖R(Y)‖ = 19.9385 ≤ ‖Y‖/(1−a) = 54.8071
remainder ‖Δ − cR(B(S))‖ = 8.980e-06 ≤ c²b‖B(S)‖/((1−a)(1−L)) = 9.761e-05   (first-order term c‖R(B(S))‖ = 1.654e-03)
LLC: tr(HΔ) = 3.05497e-03  ≥ c tr(H R(B(S))) = 3.03905e-03  ≥ c tr(H B(S)) = 1.02616e-03
```

## GPT-6 Astra v1

Full response in `gpt_fulllaw-resolvent_v1.md`. Summary: **adopt A–D and E** (`c ≥ 0`, `N ⪰ 0`, `L < 1`; for the LLC bounds `t ≥ 0`, `H ⪰ 0`).
`R(Y) − Y = ∑_{k≥1}A^kY(Aᵀ)^k ⪰ 0` is exactly the positivity-preserving series; the frame formula for `tr(HR(Y))` is right because the frame
diagonalises both `P` and `H` (only the diagonal of `Ŷ` enters). Rejected: a scalar-multiple PSD *upper* bound `Δ ⪯ cR(B(Σ^{mb}))/(1−c‖RB‖)`
(fails in 2D: `A = 0`, `B(X) = SXSᵀ` with the swap `S`, `N = diag(1,0)` gives `Q₁ = diag(0,c)` while `Δ = diag(c²/(1−c²), c/(1−c²))`, not dominated
by any multiple of `Q₁`); a valid version needs an order-domination assumption `K(Q₁) ⪯ κQ₁`. Adopted: the second-order hierarchy with `K = R∘B`,
`Δ = ∑_{j≥1}c^jK^j(Σ^{mb})`, `Δ − Q₁ − Q₂ = c²K²(Δ) ⪰ 0` and `‖Δ − Q₁ − Q₂‖ ≤ θ²‖Q₁‖/(1−θ)`, `θ = c‖K‖ ≤ cb/(1−a)` (PSD hierarchy formalised; the norm
version deferred). Anchored scaling: with `c = η²α`, `α = (1−m/n)/(m(n−1))`, the first-order LLC correction is exactly
`(ηt²α/2)∑ᵢλᵢB̂ᵢᵢ/(pᵢ(2−ηpᵢ/t))`, i.e. `(ηtα/2)∑ᵢB̂ᵢᵢ/(2−ηλᵢ)` at `pᵢ = tλᵢ` — no extra `1/λᵢ`; it is `O(η)` (and linear in `t` only if `B̂(Σ^{mb})` is
`t`-independent). Wording: call `1/(1−ρᵢ²) = ∑_k ρᵢ^{2k}` the *geometric accumulation factor*, not the integrated autocorrelation time (which is
`(1+r)/(1−r)`).

## Candidates v2 (Claude, adopting the addition)

- **F** (`stateTerm_add`, `stateTerm_smul`, `fullFixed_sub_second_order_eq`, `fullFixed_sub_second_order_posSemidef`):
  `Δ − cK(Σ^{mb}) − c²K²(Σ^{mb}) = c²K²(Δ) ⪰ 0`, the next rung of the monotone PSD hierarchy.

## Vote
- Claude: A + B + C + D + E + F
- GPT-6 Astra: "prioritize A → B → E, retain C–D for quantitative control, add (ii) if cheap, reject unqualified (i)"
