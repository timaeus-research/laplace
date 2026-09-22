# Tide: llc-two-loop

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: the LLC's next term in the note's tensor notation, E2's `4.76`.)
**Seabed:** laplace, main fb41117
**Started:** 2026-09-22T08:23Z

## Candidates v1 (Claude)

See `gpt_llc_two_loop_prompt_v1.md` (A–B verbatim).

- A: `twoLoopEnergy t H T Q4 := ½ tr(HS) + (t/12)θ + (t/8)δ − (1/8)q` (theta, dumbbell, figure-eight); on the rotated tensors
  `= d/(2t) + ∑ᵢ (5αᵢ²/(24λᵢ³) − γᵢ/(8λᵢ²))/t²`.
- B: `|⟨L∘A⟩ − twoLoopEnergy| ≤ K/t³` (E2's LLC to two loops with an `O(t⁻²)` remainder in `t⟨K⟩`).

## Numerical check

`numcheck_llc_two_loop.py` (`d = 3`, `λ = (1, 2, 5)`, `a = ½`, random `Q`): `twoLoopEnergy(t) = d/(2t) + c/t²` to 10 digits at
`t = 5, 50`; `t²·(t⟨L⟩ − t·twoLoopEnergy) = −0.115, −0.143, −0.153, −0.159, −0.161` at `t = 20 … 400`; E2: `4.757`.

## GPT-6 Astra v1

Verbatim in `gpt_llc_two_loop_v1.md`. Summary: the Wick count confirms the coefficients (`3` quartic pairings → `−tq/8`; `3! = 6`
three-cross-edge pairings → `t²θ/12`; `3·3 = 9` one-cross-edge pairings → `t²δ/8`; `3 + 6 + 9 = 15` pairings of six legs) and the
identification `∑ᵢⱼ Sᵢⱼ bubbleᵢⱼ = θ` is a dummy-index renaming (no symmetry needed). `−∂ₜ` of the two-loop `log Z` gives exactly
`twoLoopEnergy`, which approximates `⟨V − V*⟩` (the note's `⟨K⟩`). Three claims to keep distinct in the staging note: the general tensor
*definition* (motivated by the standard expansion), the exact rotated-family *evaluation*, and the rotated-separable *rate* transferred
from the scalar theorem; the Lean does not establish a general non-separable rate theorem. Suggested regression test outside the separable
family: `H = I₂`, `T₁₁₂ = T₁₂₁ = T₂₁₁ = 1` gives `θ = 3/t³`, `δ = 1/t³` (distinguishes the two contractions). Warns not to identify the
two-loop `4.75694…` with E2's exact value at `t = 3` (an `O(t⁻²)` theorem gives neither applicability nor a numerical error there): say
"numerically matching the reported `4.76` at the displayed precision". Lean: prove the Frobenius-conjugation lemma once via
`tr(AᵀB) = tr(Q Dₐ D_b Qᵀ) = tr(Dₐ D_b)`; for `δ` use orthogonal invariance of the vector quadratic form with `contractT_rot`.

## Vote
- Claude: A+B
- GPT-6 Astra: A+B ("YES on A+B … exclude a general non-separable rate theorem and any certification of the exact `t = 3` value")

Adopted: add the `T₁₁₂`-type regression test (`theta`/`dumbbell` at `d = 2`) to the numerical check; phrase E2's `4.76` as "matching at
the displayed precision"; distinguish definition / evaluation / rate in the staging note.
