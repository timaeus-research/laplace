# Tide 99 consult: the E2–E4 error budget for the ULA-sampled anchored LLC estimate (laplace seabed, Lean 4 + Mathlib)

Landed: E2 exact localised law in the eigenframe (`ℓᵢ = λᵢx²/2 + αᵢx³/6 + γᵢx⁴/24`, localiser `(g/2)|u − u₀|²`, `aᵢ = g u₀ᵢ`) with the second-order LLC
`t⟨L∘A⟩_loc = d/2 + ∑e₁ᵢ/t + O(t⁻²)`; E3 anchored Gaussian `N(m, P⁻¹)`, `P = tH + gI`, `m = P⁻¹ g u₀`, with `𝓔^{anch} = ½∑tλᵢ/pᵢ + (t/2)∑λᵢ(aᵢ/pᵢ)²`, `pᵢ = tλᵢ + g`,
and the gap `t⟨L∘A⟩_loc − 𝓔^{anch} = C₁′/t + O(t⁻²)`, `C₁′ = ∑(e₀ᵢ − aᵢαᵢ/(2λᵢ²))` (tide 95); E4 ULA burn-in on a Gaussian target with precision `P` from the mode
(tide 92) and from any start (tide 98): k-step law `N(m_k, Σ_k)`, `Σ_k = U diag((1 − ρᵢ^{2k})/(pᵢκᵢ)) Uᵀ`, `ρᵢ = 1 − hpᵢ`, `κᵢ = 1 − hpᵢ/2`, stability `hpᵢ < 2`.
All eigen statements for E4 are currently in the `orthoOf` frame of `P`; tide 97 provides frame-general lemmas (`UᵀU = 1`, `UᵀHU = diag λ`).

Candidates v1 (Claude):
A (Sampler, frame-general ULA). Restate tide 92's burn-in algebra for an arbitrary orthogonal frame `U` diagonalising `P` (`UᵀPU = diag p`): `ulaStep = U diag(1 − hp) Uᵀ`,
  `ulaCov = U diag(1/(pκ)) Uᵀ`, `Σ_k = U diag(f/(pκ)) Uᵀ`, `Σ_k⁻¹ ≻ 0` (k ≥ 1).
B (Sampler, ULA on the anchored Gaussian). Target `N(m, P⁻¹)`; ULA `x_{k+1} = x_k − hP(x_k − m) + √(2h)ξ` from `x₀` has the k-step law `N(m_k, Σ_k)`,
  `m_k = m + (1 − hP)^k(x₀ − m)`, formalised as `tiltedExpectation Σ_k⁻¹ (Σ_k⁻¹ m_k)`. For a second matrix `H` in the same frame (`UᵀHU = diag λ`):
  `⟨½uᵀHu⟩_k = ½∑λᵢfᵢ/(pᵢκᵢ) + ½∑λᵢ((Uᵀm_k)ᵢ)²`, `(Uᵀm_k)ᵢ = (Uᵀm)ᵢ + ρᵢ^k((Uᵀx₀)ᵢ − (Uᵀm)ᵢ)`.
C (Multi, the budget). In the E2 frame (`H = Q diag(λ) Qᵀ`, `P = tH + gI`, `(Qᵀm)ᵢ = aᵢ/pᵢ`), for `t ≥ T`, any `h > 0` with `h pᵢ < 2`, `k ≥ 1`, start `x₀`:
  `t⟨L∘A⟩_loc − t⟨½uᵀHu⟩_k = C₁′/t − (th/4)∑ᵢλᵢ/κᵢ + Burn_k + O(t⁻²)`,
  `Burn_k = (t/2)∑ᵢλᵢρᵢ^{2k}/(pᵢκᵢ) − (t/2)∑ᵢλᵢ[((Qᵀm_k)ᵢ)² − (aᵢ/pᵢ)²]`,
  from tide 95 plus the *exact* identity `𝓔^{anch} − t⟨½uᵀHu⟩_k = −(th/4)∑λᵢ/κᵢ + Burn_k` (per mode: `½tλ/p − (t/2)λf/(pκ) = −(th/4)λ/κ + (t/2)λρ^{2k}/(pκ)`).
  Reading: three error sources for the ULA-based anchored LLC estimate — anharmonicity `C₁′/t`, the ULA step-size bias `−(th/4)∑λᵢ/κᵢ` (the estimate sits *above*
  the Gaussian prediction by `(th/4)∑λ/κ`), and the burn-in transient.

Numerical check (E2 frame 2D, λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35), start x₀ = (0.9, −0.6), k = 3, β-scaled step `h = η/t`, η = 0.3):
the identity `𝓔^{anch} − t⟨½uᵀHu⟩_k = disc + burn` holds to 1e-6; Monte Carlo of the ULA chain (4·10⁵ chains) gives `t⟨½uᵀHu⟩_k = 3.130` vs formula 3.133 (t = 40);
`t·(t⟨L⟩ − t⟨½uᵀHu⟩_k − disc − burn)` → −0.2716 (t = 640) vs `C₁′ = −0.2729`. With `h = η/t` the step-size bias tends to `(η/4)∑λᵢ/(1 − ηλᵢ/2) = 0.199` (does not
vanish as t → ∞), and the burn-in term from a *fixed ambient start* grows like `t·ρ^{2k}` (−1.95 at t = 40, −32.9 at t = 640 for k = 3): a fixed number of steps
is not a fixed fraction of burn-in when t grows.

Questions:
1. Are A–C correct, including the per-mode identity and the sign convention (`t⟨L⟩ − estimate`)? Any hidden assumption (e.g. `H` and `P` sharing the frame is automatic for `P = tH + gI`)?
2. E4/E5 reading for the note: with the β-scaled step `h = η/t` the discretisation bias of the LLC estimate is O(1) in t, `(η/4)∑λᵢ/(1 − ηλᵢ/2) ≈ (η/4)tr H`, while the anharmonic
   gap is `C₁′/t`; and the burn-in transient from a fixed start scales like `t·ρ^{2k}`, so the number of burn-in steps must grow like `log t/(2|log ρ_min|)`. Fair? How should the note phrase the
   comparison "anharmonic error vs sampler error"? Is `(η/4)∑λᵢ/κᵢ` the standard first-order ULA bias for the quadratic-form statistic (it equals `(h/4)tr(P·H·ulaCov)`-type expressions)?
3. Lean route: prove A by mirroring tide 92 with tide 97's `frame_eq_conj`, `posDef_conj_diagonal`, general `conj_mul_conj`/`conj_pow`/`inv_conj_diagonal`; B via `tiltedExpectation_quadForm`
   with the trace `∑∑ H Σ_k = tr(HΣ_k) = ∑λᵢσᵢ` (needs the symmetry of `Σ_k` entries) and `xᵀ(U diag λ Uᵀ)x = ∑λᵢ(Uᵀx)ᵢ²`; C by combining `localisedEnergy_anchoredGap` with the exact identity
   proved termwise (`field_simp; ring` with `p ≠ 0`, `κ ≠ 0`). Pitfalls?
4. Cheap additions worth making (e.g. the `h = η/t` corollary with the limit `(η/4)∑λᵢ/(1 − ηλᵢ/2)`; the k → ∞ stationary budget `C₁′/t − (th/4)∑λ/κ`; the variance budget)?
5. Vote.
