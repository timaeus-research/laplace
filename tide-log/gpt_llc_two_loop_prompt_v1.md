# Tide `llc-two-loop` (laplace seabed, main fb41117): candidates for GPT-6 Astra

## Context

The note gives eq:llc only at leading order (`⟨K⟩ = ½ tr(HS) + O(S²)`, `t⟨K⟩ → d/2`) and reports in E2 that "at `t = 3` the exact LLC is
`4.76`, not `5`" (`d = 10`, `a = ½`). The seabed has the scalar version of the next term (`energy_anharmonic_order1_rate_sharp`,
`|t⟨ℓ⟩ − ½ − (5α²/(24λ³) − γ/(8λ²))/t| ≤ K/t²`, with separable / rotated forms in the note's parametrisation) and, since this morning,
the one-loop covariance and eq:mean / eq:covK evaluated on E2's tensors in matrix form (`oneLoopCov_rot`, `meanShift_rot`,
`covKFormula_rot`) with the contractions `contractQ (Q4:S)`, `bubble (TSST)`, `tadpoleLine`, `contractT (T:S)` (`Laplace/Multi/OneLoop.lean`)
and their closed forms on the rotated tensors `H = Q diag λ Qᵀ`, `T = rotT`, `Q4 = rotQ`, `S = Q diag(1/(λt)) Qᵀ`:
`contractQ = Q diag(γ/(λt)) Qᵀ`, `bubble = tadpoleLine = Q diag(α²/(λt)²) Qᵀ`, `contractT = Q (α/(λt))`.

## Candidates

**A. The energy to two loops in tensor notation.** Define, with `S = (tH)⁻¹`,
`twoLoopEnergy t H T Q4 := ½ tr(H S) + (t/12) θ + (t/8) δ − (1/8) q`, where
`θ = ∑ᵢⱼₖₗₘₙ Tᵢⱼₖ Tₗₘₙ Sᵢₗ Sⱼₘ Sₖₙ = ∑ᵢₗ Sᵢₗ (TSST)ᵢₗ` (the theta vacuum diagram, `= ∑ᵢⱼ Sᵢⱼ bubbleᵢⱼ` in the seabed's terms),
`δ = (T:S)ᵀ S (T:S)` (the dumbbell), `q = ∑ᵢⱼₖₗ Q4ᵢⱼₖₗ Sᵢⱼ Sₖₗ = ∑ᵢⱼ (Q4:S)ᵢⱼ Sᵢⱼ` (the figure-eight).
This is `−∂ₜ log Z` from the two-loop free energy `log Z = −tV* − ½ log det(tH/2π) + (t²/12)θ + (t²/8)δ − (t/8)q + …` (symmetry factors
`3!/(2!·3!²) = 1/12`, `9/(2!·3!²) = 1/8`, `3/4! = 1/8`). Claim: on the rotated tensors
`twoLoopEnergy = d/(2t) + (∑ᵢ (5αᵢ²/(24λᵢ³) − γᵢ/(8λᵢ²)))/t²` (`twoLoopEnergy_rot`), and in the note's parametrisation
`= d/(2t) + d(5a²/24 − 1/8)/t²`.

**B. The rate.** `|⟨L∘A⟩ − twoLoopEnergy t H T Q4| ≤ K/t³` for `t ≥ T` (equivalently `|t⟨K⟩ − t·twoLoopEnergy| ≤ K/t²`), from the
scalar `energy_anharmonic_order1_rate_sharp` summed over coordinates (`⟨L⟩ = ∑ᵢ⟨ℓᵢ⟩`) and `⟨L∘A⟩ = ⟨L⟩`. So E2's `4.76` is the two-loop
formula (`4.757`) with an `O(t⁻²)` remainder in `t⟨K⟩`.

## Numerical check (`numcheck_llc_two_loop.py`, `d = 3`, `λ = (1, 2, 5)`, `a = ½`, random `Q`)

`twoLoopEnergy(t)` equals `d/(2t) + c/t²` to 10 digits at `t = 5, 50`; `t²·(t⟨L⟩ − t·twoLoopEnergy) = −0.115, −0.143, −0.153, −0.159,
−0.161` at `t = 20 … 400` (bounded); E2: `10(½ + (5/96 − 1/8)/3) = 4.757`.

## Questions

1. Are the coefficients `1/12`, `1/8`, `−1/8` and the identification `θ = ∑ᵢⱼ Sᵢⱼ (TSST)ᵢⱼ` right, given the seabed's
   `bubble T S i j = ∑ₖₗₘₙ Tᵢₖₗ Sₖₘ Sₗₙ Tⱼₘₙ`? (Is `∑ᵢⱼ Sᵢⱼ bubbleᵢⱼ` exactly the theta diagram `Tᵢⱼₖ Tₗₘₙ Sᵢₗ Sⱼₘ Sₖₙ`?) Note the
   separable family cannot distinguish the `θ` and `δ` weights (both equal `∑ αᵢ² sᵢ³`); the split is fixed by the symmetry factors.
2. Since the note does not state this formula, how should the staging note present it — as a suggested addition to E2/E7 ("the LLC's
   next term, `E2`'s `4.76`") rather than a `\leanref` on an existing sentence? Any risk that `twoLoopEnergy` disagrees with the standard
   two-loop expansion of `⟨V⟩` for a general (non-separable) potential, given that only the separable case is verified?
3. Lean: `∑ᵢⱼ (Q diag a Qᵀ)ᵢⱼ (Q diag b Qᵀ)ᵢⱼ = ∑ₚ aₚbₚ` via `tr(Aᵀ B)` and `conj_mul_conj`, or entrywise? Any pitfalls with
   `Matrix.trace` of `Q * (diagonal a * diagonal b) * Qᵀ` (`trace_mul_cycle` + `Qᵀ Q = 1`)?
4. Scope and vote (A+B)?
