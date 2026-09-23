# Tide 108 consult: logarithmic burn-in at the anchored scaling (laplace seabed, Lean 4 + Mathlib; E4)

Seabed (tides 98–100): ULA from a start `x₀` on the anchored Gaussian `N(m, P⁻¹)`, `P = tH + g·1`, step `h`; the `k`-step energy `⟨½uᵀHu⟩_k = ½∑λᵢσᵢ²(1−ρᵢ^{2k}) + ½∑λᵢ(m̂ᵢ + ρᵢ^k(x̂₀ᵢ − m̂ᵢ))²`, `ρᵢ = 1 − hpᵢ`, and the E2–E4 budget `|t⟨L⟩_loc − t⟨½uᵀHu⟩_k − C₁′/t + (th/4)∑λᵢ/κᵢ − Burn(t,k)| ≤ K/t²` (for `t ≥ T`, `h > 0`, stability) with `Burn(t,k) = (t/2)∑λᵢρᵢ^{2k}σᵢ² − (t/2)∑λᵢ[(m̂ᵢ + ρᵢ^k(x̂₀ᵢ − m̂ᵢ))² − m̂ᵢ²]`; at `h = η/t`: `(th/4)∑λᵢ/κᵢ → (η/4)∑λᵢ/(1−ηλᵢ/2)`, `ρᵢ → 1 − ηλᵢ`, `tσᵢ² → 1/(λᵢ(1−ηλᵢ/2))`, `t m̂ᵢ → gŵᵢ/λᵢ`. Tide 102's consult remarked that burn-in "grows only logarithmically in t from a fixed displacement".

Candidates v1 (Claude):
A. General criterion: if `k(t) → ∞` and `t·r^{2k(t)} → 0` for some `r ∈ (r∞, 1)`, `r∞ = maxᵢ|1−ηλᵢ|`, then `Burn(t, k(t)) → 0` (three pieces: `λ(tσ²)ρ^{2k}`, `(t/2)λρ^{2k}d²`, `tλρ^k m̂ d`, `d = x̂₀ − m̂`).
B. Log schedule: `k(t) = ⌈κ log t⌉₊` with `κ > 1/(2 log(1/r))` gives `t r^{2k(t)} ≤ t^{1 + 2κ log r} → 0` and `k → ∞`.
C. Hence `Burn(t, ⌈κ log t⌉₊) → 0`: burn-in of order `log t` suffices for the scaled statistic.
D. With tide 99's budget and the bias limit: `t⟨½uᵀHu⟩_{k(t)} − t⟨L⟩_loc → −(η/4)∑λᵢ/(1−ηλᵢ/2)` along the schedule — the sampled scaled statistic converges to the localised energy minus the step-size bias.
E (optional). Necessity: for `κ < 1/(2 log(1/r∞))` and `x̂₀ ≠ 0` the burn-in does not vanish.

Numerical check (`λ = (1, 2.5, 0.7)`, `η = 0.3`): `r∞ = 0.79`, `κ_crit = 2.12`; `κ = 1.5κ_crit`: Burn `−6.3e-2 → −5.8e-5` over `t = 10…10⁶` (`t r^{2k} → 1e-3`); `κ = 0.7κ_crit`: Burn `−0.6 → −3.2`, not vanishing.

Questions:
1. Are A–D correct? In A, is the uniform bound `|ρᵢ(t)| ≤ r` eventually (for every `r > r∞`) the right device, and is the sign/definition of `Burn` consistent with the budget (Burn is the *negative* of the excess `t⟨·⟩_k − t·stationary`)? Is `k(t) → ∞` needed separately or implied by `t r^{2k} → 0`?
2. E4 reading: "at the β-scaled step the burn-in needed for a fixed absolute precision of the scaled statistic grows like `log t/(2 log(1/r∞))`; the constant in front is the slowest mode's contraction `r∞ = max|1−ηλᵢ|`" — correct? Should the note present the threshold `κ_crit = 1/(2 log(1/r∞))` as sharp (E), and how does this interact with the E5 result (stationary steps `t`-independent) and the minibatch results (batch ∝ t)? Total cost `≈ κ log t + n` iterations per LLC estimate.
3. Lean route: A via `squeeze_zero`/`Tendsto` products with `|ρᵢ(t)|^k ≤ r^k` from eventual `|ρᵢ(t)| ≤ r` (`pow_le_pow_left₀`) and `tendsto_pow_atTop_nhds_zero_of_lt_one` composed with `k`; B via `Real.rpow` (`rpow_le_rpow_of_exponent_ge` for base `< 1`, `rpow_natCast`, `rpow_def_of_pos`) and `tendsto_rpow_neg_atTop`, `tendsto_natCeil_atTop ∘ Real.tendsto_log_atTop`; D by squeezing the budget's `K/t²`. Pitfalls with `Nat.ceil` and the real power of a natural exponent?
4. Cheap additions (the total-iteration statement `⌈κ log t⌉ + n` for precision `ε`; E; the burn-in of the *unscaled* statistic needing only `r^{2k} → 0`, i.e. `k → ∞` with no `t`-dependence)? Vote.
