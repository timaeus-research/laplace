# Context: laplace seabed, tide 115 (E8 full law, resolvent refinement)

Following your tide-114 advice. `A = I − hP`, `T(X) = AXAᵀ`, `R = (1−T)⁻¹` (Lyapunov resolvent; in the eigenframe of `P`, `R(Y)ᵢⱼ = Ŷᵢⱼ/(1−ρᵢρⱼ)`,
`ρᵢ = 1−hpᵢ`), `B(X) = ∑ᵢDᵢXDᵢᵀ`, `Σ^{mb} = R(N)`, `Σ_full` the fixed point of `X ↦ T(X) + N + cB(X)`, `Δ = Σ_full − Σ^{mb}`, `a = ‖A‖‖Aᵀ‖`,
`b = ∑‖Dᵢ‖‖Dᵢᵀ‖`, `L = a + cb < 1` (ℓ∞ operator norm). Formalised: existence/uniqueness/PSD of `Σ_full`, `Δ ⪰ cB(Σ^{mb}) ⪰ 0`, the Banach bound
`‖Δ‖ ≤ c‖B(Σ^{mb})‖/(1−L)`, and `Σ^{mb}` as the unique Lyapunov solution.

# Candidates
A. `Δ = T(Δ) + cB(Σ_full)`, hence by Lyapunov uniqueness `Δ = c·R(B(Σ_full))` (exact).
B. `Δ − cR(B(Σ^{mb})) = cR(B(Δ)) ⪰ 0`, and `R(Y) − Y = ∑_{k≥1}T^k(Y) ⪰ 0` for `Y ⪰ 0`: `Δ ⪰ cR(B(Σ^{mb})) ⪰ cB(Σ^{mb})`.
C. Neumann: `‖R(Y)‖ ≤ ‖Y‖/(1−a)` (Banach's estimate at `0` for `X ↦ T(X) + Y`).
D. `‖Δ − cR(B(Σ^{mb}))‖ ≤ c‖B(Δ)‖/(1−a) ≤ cb‖Δ‖/(1−a) ≤ c²b‖B(Σ^{mb})‖/((1−a)(1−L))`.
E. In the frame, `tr(H R(Y)) = ∑ᵢλᵢŶᵢᵢ/(1−ρᵢ²)` with `1−ρᵢ² = hpᵢ(2−hpᵢ)`; so `(t/2)tr(HΔ) = (t/2)c∑ᵢλᵢ(B̂(Σ_full))ᵢᵢ/(hpᵢ(2−hpᵢ))` exactly and
   `LLC_full ≥ LLC^{mb} + (t/2)c∑ᵢλᵢ(B̂(Σ^{mb}))ᵢᵢ/(hpᵢ(2−hpᵢ))`: the first-order correction is the one-step term divided by `1−ρᵢ² = O(h)`, so it is
   `O(η)` at the anchored scaling where the one-step term is `O(η²)` (your remark in tide 107).

Numerical check (3D, a = 0.858, L = 0.863): `‖Δ − cR(B(Σ_full))‖ = 3e-16`; `Δ − cR(B(Σ^{mb}))` has eigenvalues `(8e-7, 3e-6, 8e-6) ≥ 0`;
`cR(B(Σ^{mb})) − cB(Σ^{mb})` eigenvalues `(1.2e-4, 3.8e-4, 1.1e-3) ≥ 0`; Neumann `19.9 ≤ 54.8`; remainder `9.0e-6 ≤ 9.8e-5`; `tr(HΔ) = 3.055e-3 ≥ 3.039e-3
(first order) ≥ 1.026e-3 (one-step)`.

# Questions
1. Are A–E correct? In particular is the frame formula for `tr(H R(Y))` right when `Y` is not diagonal in the frame (only the diagonal entries of
   `Ŷ` enter because `H` is diagonal there), and is `R(Y) − Y ⪰ 0` for PSD `Y` exactly the statement that `∑_{k≥1}A^kY(Aᵀ)^k ⪰ 0`?
2. Cheap additions: (i) the upper bound `Δ ⪯ cR(B(Σ^{mb}))/(1 − c‖R∘B‖)`-type PSD statement? (ii) the second-order term `c²R(B(R(B(Σ^{mb}))))` with an
   `O(c³)` remainder (Neumann series in `cRB`)? (iii) at the anchored scaling, the explicit limit of the first-order LLC correction
   `(t/2)c∑λᵢB̂ᵢᵢ/(hpᵢ(2−hpᵢ))` with `c = h²t²(1−m/n)/(m(n−1))`, `h = η/t` — does it reduce to `(η t/(4m'))∑B̂ᵢᵢ/(λᵢ(2−ηλᵢ))·(…)`, i.e. linear in `t`
   like the constant-noise bias?
3. Wording for E8: "the Hessian-fluctuation correction to the LLC is, to first order in `c`, `(t/2)c∑ᵢλᵢ(B̂(Σ^{mb}))ᵢᵢ/(hpᵢ(2−hpᵢ))`, i.e. the one-step
   term amplified by the mode's integrated autocorrelation time `1/(1−ρᵢ²)`"?
Vote please.
