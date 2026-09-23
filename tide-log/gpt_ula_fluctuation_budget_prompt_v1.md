# Tide 100 consult: the fluctuation side of the ULA anchored LLC estimate and the stationary budget (laplace seabed, Lean 4 + Mathlib)

Landed (tides 92–99): ULA on the anchored Gaussian `N(m, P⁻¹)`, `P = tH + gI`, from `x₀` has the k-step law `N(m_k, Σ_k)`, `m_k = m + (1 − hP)^k(x₀ − m)`, `Σ_k = U diag(vᵢ) Uᵀ`, `vᵢ = fᵢ/(pᵢκᵢ)`, `fᵢ = 1 − ρᵢ^{2k}`, `ρᵢ = 1 − hpᵢ`, `κᵢ = 1 − hpᵢ/2` (tide 99, any orthogonal frame); `⟨½uᵀHu⟩_k = ½∑λᵢvᵢ + ½∑λᵢμᵢ²`, `μᵢ = (Uᵀm)ᵢ + ρᵢ^k(Uᵀ(x₀ − m))ᵢ`; the E2–E4 expectation-bias budget `t⟨L∘A⟩_loc − t⟨½uᵀHu⟩_k = C₁′/t − (th/4)∑λᵢ/κᵢ + Burn_k + O(t⁻²)`; tide 96's tilted variance `Var_{P,v}(uᵀHu) = 2tr(HΣHΣ) + 4(Hm)ᵀΣ(Hm)`.

Candidates v1 (Claude):
A (Sampler, frame). `burnInAnch_var_frame`: `Var_k(½uᵀHu) = ½∑ᵢ(λᵢvᵢ)² + ∑ᵢvᵢ(λᵢμᵢ)²` (so the scaled statistic has `Var_k(t·½uᵀHu) = (t²/2)∑(λᵢvᵢ)² + t²∑vᵢ(λᵢμᵢ)²`), from `tiltedVar_quadForm` with `tr((HΣ_k)²) = ∑(λᵢvᵢ)²` and `(Hm_k)ᵀΣ_k(Hm_k) = ∑vᵢ(λᵢμᵢ)²`.
B (Multi, E2 frame). The instantiation with `U = Q`, `bᵢ = aᵢ/pᵢ`, `zᵢ = (Qᵀx₀)ᵢ`: `Var_k(t·½uᵀHu) = (t²/2)∑(λᵢvᵢ)² + t²∑vᵢ(λᵢ(bᵢ + ρᵢ^k(zᵢ − bᵢ)))²`.
C (Multi, stationary limits, fixed t, h). `t⟨½uᵀHu⟩_k → (t/2)∑λᵢ/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²`, `Burn_k → 0`, `Var_k → (t²/2)∑(λᵢ/(pᵢκᵢ))² + t²∑λᵢ²bᵢ²/(pᵢκᵢ)` as `k → ∞` (from `|ρᵢ| < 1`).
D (Multi, stationary budget). `|t⟨L∘A⟩_loc − ((t/2)∑λᵢ/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²) − C₁′/t + (th/4)∑λᵢ/κᵢ| ≤ K/t²` (tide 95's constants), i.e. the k → ∞ form of the budget: at stationarity the ULA anchored estimate exceeds the exact localised LLC by `(th/4)∑λᵢ/κᵢ − C₁′/t + O(t⁻²)`.

Numerical check (E2 frame 2D as before, t = 40, h = 0.3/t, x₀ = (0.9, −0.6), k = 3, 4·10⁵ chains): MC variance 4.6 vs formula (see log); along k the variance rises from the start's value to the stationary `(t²/2)∑(λ/(pκ))² + t²∑λ²b²/(pκ)`; `Burn_k → 0` geometrically.

Questions:
1. Are A–D correct? In particular the variance formula (the cross term `(Hm_k)ᵀΣ_k(Hm_k) = ∑vᵢλᵢ²μᵢ²` uses that `H` and `Σ_k` share the frame) and the stationary variance.
2. E5 reading: with `h = η/t`, `vᵢ → 1/(pᵢκᵢ) ≈ 1/(tλᵢ(1 − ηλᵢ/2))`, so the stationary variance of the scaled statistic is `(1/2)∑1/(1 − ηλᵢ/2)² + O(1/t)` — i.e. `Var(tX) ≈ d/2` inflated by the ULA factor `1/κᵢ²`, plus a start-dependent piece `t²∑λᵢ²bᵢ²/(pᵢκᵢ) → ∑λᵢaᵢ²/(λᵢ²…)`… please give the clean `t → ∞` limits of both pieces at fixed η and state what a single-chain single-time sample tells us about the LLC (standard error `√(d/2)`-ish, independent of t) vs the biases `C₁′/t` and `(η/4)∑λ/κ`. What should the note say about "how many samples/steps to resolve the anharmonic correction"?
3. Lean route: A via `tiltedVar_quadForm hQ v hH`, `tr((HΣ)²)` by conjugation (`frame_eq_conj`, `conj_mul_conj_frame`, `trace_mul_cycle`), the cross term by `dotProduct_conj_diagonal_mulVec` with `Uᵀ(Hm_k) = diag(λ)Uᵀm_k`; C via `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`; D via tide 95 + the per-mode identity `½tλ/p − (t/2)λ/(pκ) = −(th/4)λ/κ`. Pitfalls?
4. Cheap additions (e.g. the variance's `h = η/t` limit, a Chebyshev-type statement `P(|X̄_M − E| ≥ ε) ≤ Var/(Mε²)` for M independent chains — but Mathlib probability infrastructure may be heavy)?
5. Vote.
