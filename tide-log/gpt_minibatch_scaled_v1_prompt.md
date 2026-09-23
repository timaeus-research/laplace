# Tide 106 consult: β-scaled limits of the minibatch long-run variance (laplace seabed, Lean 4 + Mathlib; E8 + E5 at the anchored scaling)

Landed (tide 105): for the constant-noise SGLD chain, `τ²_{mb} = ½∑ᵢⱼλᵢλⱼŜᵢⱼ²(1+ρⱼ²)/(1−ρⱼ²) + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼ(1+ρⱼ)/(1−ρⱼ)` with `Ŝᵢⱼ = (2h[i=j] + h²t²Ĉᵢⱼ)/(1−ρᵢρⱼ)`, and `τ²_{ULA} ≤ τ²_{mb}`. Tide 103: anchored model `P_t = tH + g·1`, `pᵢ = tλᵢ + g`, `m̂ᵢ = gŵᵢ/pᵢ`, step `h = η/t`, `0 < ηλᵢ < 2`; limit toolkit (`ρᵢ(t) → 1 − ηλᵢ`, IATs, eventual stability, `Tendsto.congr'` from eventual equality with the closed form); `t²τ²_{ULA} → L_η = ∑ᵢ(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)`. Your tide-105 consult predicted `τ²_{mb} = Θ(1)`, `t²τ²_{mb} = Θ(t²)` for fixed `C` and bounded scaled fluctuations for `C = O(1/t)`.

Candidates v1 (Claude):
A. `mbAnchored_longRunVar`: tide 105's formula on the anchored model with explicit entries and `m̂ᵢ = gŵᵢ/(tλᵢ+g)`.
B (fixed `C`). `(2(η/t)δᵢⱼ + (η/t)²t²Ĉᵢⱼ)/(1 − ρᵢ(t)ρⱼ(t)) → η²Ĉᵢⱼ/(1 − (1−ηλᵢ)(1−ηλⱼ)) = ηĈᵢⱼ/(λᵢ+λⱼ−ηλᵢλⱼ)`; the mean part `→ 0`; `τ²_{mb}(t) → L_∞ := ½∑ᵢⱼλᵢλⱼ(η²Ĉᵢⱼ/(1−(1−ηλᵢ)(1−ηλⱼ)))²·(1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))` as an unconditional `Tendsto`; and `t²τ²_{mb}(t) → +∞` when `L_∞ > 0` (`L_∞ > 0 ⟺ Ĉ ≠ 0`).
C (linear batch growth `C_t = C₀/t`). `t·Ŝᵢⱼ(t) → (2ηδᵢⱼ + η²Ĉ₀ᵢⱼ)/(1−(1−ηλᵢ)(1−ηλⱼ))`, `tm̂ᵢ → gŵᵢ/λᵢ`, `Ŝᵢⱼ → 0`; `t²τ²_{mb}(t) → L_lin := ½∑ᵢⱼλᵢλⱼ((2ηδᵢⱼ + η²Ĉ₀ᵢⱼ)/(1−(1−ηλᵢ)(1−ηλⱼ)))²·(1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))`.
D. `L_lin(C₀ = 0) = L_η` (diagonal collapse), and `L_η ≤ L_lin` for `Ĉ₀ ⪰ 0`.

Numerical check (3D random frame, `η = 0.3`, `g = 0.7`, random PSD `C₀`): fixed `C`: `τ²_{mb}(t)` → 0.007755 at `t = 10240` vs `L_∞ = 0.007724`, `t²τ²` → 8·10⁵; `C₀/t`: `t²τ²_{mb}` → 6.5139 vs `L_lin = 6.5142`; `L_lin(0) = L_η = 6.1694`.

Questions:
1. Are A–D correct, including the `1/(1−(1−ηλᵢ)(1−ηλⱼ))` denominators (`= 1/(η(λᵢ+λⱼ−ηλᵢλⱼ))`) and the claim that the mean part vanishes in both regimes (`m̂ = O(1/t)`: fixed `C` gives `O(t⁻²)·O(1)` per term, scaled by `t²` in C gives `O(1)·O(1)·Ŝ = O(1/t) → 0`)?
2. How should the note phrase the E8+E5 batch-size result: "with a fixed gradient-noise covariance the stationary Monte Carlo variance of the scaled LLC statistic's chain average is `Θ(t²)/n`, so `n ∝ t²`; with batch size growing linearly in `t` it is `L_lin/n` with `L_lin ≥ L_η`, recovering the exact-gradient budget only as `C₀ → 0`"? Is `L_∞` (the limiting *unscaled* long-run variance) meaningful on its own — e.g. as `η·` a Lyapunov-type functional of `C`?
3. Lean route: A by transcription (tide 103 pattern + tide 101's entry simp set); B/C via `Tendsto.div` with the denominator limit `1 − ρᵢρⱼ → 1 − (1−ηλᵢ)(1−ηλⱼ) ≠ 0`, `tendsto_finsetSum` twice, mean part via products of limits (`gŵᵢ/(tλᵢ+g) → 0`, `t·gŵᵢ/(tλᵢ+g) → gŵᵢ/λᵢ`, `Ŝ = (tŜ)/t → 0`), then `Tendsto.congr'` with eventual admissibility; `t²τ² → ∞` via `Tendsto.atTop_mul`-type lemma with `t² → ∞` and `τ² → L_∞ > 0`. Pitfalls?
4. Cheap additions (e.g. `L_∞ > 0 ⟺ Ĉ ≠ 0`; `L_∞ = (η/2)∑ᵢⱼλᵢλⱼ Ĉᵢⱼ² w/(λᵢ+λⱼ−ηλᵢλⱼ)²`; the superlinear regime `C = C₀/t^{1+ε}` giving `L_η` exactly — maybe just `C_t = C₀/t²` as a third regime)? Vote.
