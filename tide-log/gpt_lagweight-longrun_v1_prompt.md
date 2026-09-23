# Context: laplace seabed, tide 112 (small closing tide)

Tide 111 formalised, for the average of `n` consecutive post-burn-in ULA draws of `q = ½uᵀHu` at the anchored scaling `h = η/t`, the limiting
scaled variance `W_{η,n} = ½∑ᵢaᵢ⁻²F_n(αᵢ²)` with `αᵢ = 1−ηλᵢ`, `aᵢ = 1−ηλᵢ/2`, `F_n(z) = (n + 2∑_{j<n}(n−(j+1))z^{j+1})/n²`, and the bounds
`1/n ≤ F_n ≤ 1`, `F_n(z) ≤ (1+z)/(n(1−z))`. Tide 103 has the stationary long-run variance limit `L_η = ∑ᵢ(1+αᵢ²)/(4ηλᵢaᵢ³)`.

# Candidates
A. `∑_{j<n}(n−(j+1))z^{j+1} = nz/(1−z) − z(1−z^n)/(1−z)²` (z ≠ 1), hence `F_n(z) = (1+z)/(n(1−z)) − 2z(1−z^n)/(n²(1−z)²)` (n ≥ 1).
B. `n·F_n(z) → (1+z)/(1−z)` for `0 ≤ z < 1`.
C. `½∑ᵢaᵢ⁻²(1+αᵢ²)/(1−αᵢ²) = L_η` and `n·W_{η,n} → L_η`.

Numerical check: identity to 1e-13; `n·W_n → L_η = 6.1694` (6.1686 at n = 10⁴).

# Questions
1. Are A–C correct (including the `z ≠ 1` / `n ≥ 1` side conditions and the identification with tide 103's `L_η` via `1−αᵢ² = 2ηλᵢaᵢ`)?
2. Is there a cheap strengthening worth adding — e.g. the rate `n·F_n(z) − (1+z)/(1−z) = −2z(1−z^n)/(n(1−z)²) = O(1/n)`, monotonicity of `n ↦ n·F_n(z)`,
   or the bound `n·W_{η,n} ≤ L_η` (so the fixed-`n` average never beats the long-run rate)?
3. One-line wording for the note connecting the fixed-`n` average to the long-run variance, with caveats.
Vote please.
