# Tide `tensor-identification` (laplace seabed): candidates for GPT-6 Astra

## Context

The E2/E7 matrix-form theorems of the last tides (`oneLoopCov_rot`, `covKFormula_rot`, `meanShift_rot`, `frobenius_rel_oneLoop_rotatedAnharmonic`,
`covKFormula_rot_rate`) take the tensors of E2's rotated oscillator as *data*:

```lean
-- Laplace/Multi/OneLoopRotated.lean, indices Fin d, Q orthogonal (Qᵀ * Q = 1)
noncomputable def rotT (Q : Matrix (Fin d) (Fin d) ℝ) (alpha : Fin d → ℝ) : Fin d → Fin d → Fin d → ℝ := fun i j k => ∑ l, alpha l * Q i l * Q j l * Q k l
noncomputable def rotQ (Q) (gamma) : Fin d → Fin d → Fin d → Fin d → ℝ := fun i j k m => ∑ l, gamma l * Q i l * Q j l * Q k l * Q m l
-- and H = Q * diagonal lam * Qᵀ
-- the potential (Laplace/Multi/GibbsRotation.lean, SeparableExact.lean, OneD/Anharmonic.lean)
def anharmonicPotential (lam alpha gamma : ℝ) : ℝ → ℝ := fun x => lam / 2 * x ^ 2 + alpha / 6 * x ^ 3 + gamma / 24 * x ^ 4
def separablePotential (ℓ : ι → ℝ → ℝ) : (ι → ℝ) → ℝ := fun w => ∑ i, ℓ i (w i)
def separableAnharmonic (lam alpha gamma : ι → ℝ) := separablePotential fun i => anharmonicPotential (lam i) (alpha i) (gamma i)
def affineFrame (Q : Matrix ι ι ℝ) (c w : ι → ℝ) : ι → ℝ := Qᵀ *ᵥ (w - c)
def rotated (Q c) (L : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ := fun w => L (affineFrame Q c w)
def rotatedAnharmonic Q c lam alpha gamma := rotated Q c (separableAnharmonic lam alpha gamma)
```
The staging notes say "the identification of `rotT`, `rotQ` with E2's derivative tensors at `c` is stated, not proved". The seabed's
precedent for certifying tensors is the Rosenbrock **Taylor identity** (`rosenbrock_taylor_full`: the potential equals its quadratic +
cubic + quartic Taylor terms at `(1, 1)` with `rosenT`, `rosenQ`), not a derivative computation.

## Candidates

**A. Taylor identity for the rotated oscillator.** For all `v : Fin d → ℝ`,
`rotatedAnharmonic Q c lam alpha gamma (c + v) = ½ (v ⬝ᵥ ((Q * diagonal lam * Qᵀ) *ᵥ v)) + (1/6) ∑ᵢⱼₖ rotT Q alpha i j k * vᵢvⱼvₖ + (1/24) ∑ᵢⱼₖₘ rotQ Q gamma i j k m * vᵢvⱼvₖvₘ`,
together with `rotatedAnharmonic … c = 0`. Proof: `affineFrame Q c (c + v) = Qᵀv =: u`, `separableAnharmonic u = ∑ₗ (λₗuₗ²/2 + αₗuₗ³/6 + γₗuₗ⁴/24)`,
and `∑ᵢⱼₖ (∑ₗ αₗ QᵢₗQⱼₗQₖₗ) vᵢvⱼvₖ = ∑ₗ αₗ (∑ᵢ Qᵢₗvᵢ)³ = ∑ₗ αₗ uₗ³` (`Finset.sum_mul_sum` twice and sum reordering), likewise for the quadratic
(`v ⬝ (Q diag λ Qᵀ v) = ∑ₗ λₗ uₗ²`) and quartic terms. This certifies `H, rotT, rotQ` as the note's `D²L, D³L, D⁴L` at `w* = c` in the same
sense as the Rosenbrock tensors: the potential is exactly a polynomial with these coefficient tensors.

**B (stretch). Derivative characterisation.** With `partialD i f w := deriv (fun s : ℝ => f (w + s • Pi.single i 1)) 0`,
`partialD i (partialD j (partialD k (rotatedAnharmonic Q c lam alpha gamma))) c = rotT Q alpha i j k`, and the analogous Hessian
(`= (Q diag λ Qᵀ) i j`) and fourth-order (`= rotQ`) statements, plus `partialD i (rotatedAnharmonic …) c = 0`. Route: the general lemma
`partialD k (fun w => ∑ₗ gₗ ((Qᵀ *ᵥ (w − c)) l)) w = ∑ₗ deriv gₗ ((Qᵀ *ᵥ (w − c)) l) * Q k l` (chain rule along a coordinate line,
`Qᵀ *ᵥ Pi.single k 1 = fun l => Q k l`), applied three times with `g = ℓ, ℓ', ℓ''`, and the explicit derivatives of the anharmonic
polynomial (`ℓ' = λx + αx²/2 + γx³/6`, `ℓ'' = λ + αx + γx²/2`, `ℓ''' = α + γx`, `ℓ'''' = γ`).

**C.** Alternatively/additionally, the `iteratedFDeriv ℝ 3 (rotatedAnharmonic …) c` characterisation: is there a Mathlib route through
`iteratedFDeriv` of a composition with an affine map and of a finite sum of `ℓₗ ∘ projₗ` that is not a multi-day detour?

## Numerical check (`numcheck_tensor_identification.py`, `d = 3`, random `Q, c`, central finite differences `h = 0.01`)

`F(c) = 0`, gradient `O(h²) ≈ 3e-5`; `max |FD − H| = 2.7e-4`, `max |FD − rotT| = 2.7e-14`, `max |FD − rotQ| = 7.6e-12`.

## Questions

1. Is A the right (and sufficient) formal sense of "these are E2's derivative tensors" for the staging notes, given the seabed's Rosenbrock
   precedent? Any missing factor (the `1/6`, `1/24` and the symmetry of `rotT`/`rotQ` in their indices)?
2. For A's sum manipulations, is `Finset.sum_mul_sum` + reordering the cleanest, or is there a slicker path (e.g. `Finset.sum_pow`-style
   lemma, or `Matrix.dotProduct_mulVec` for the quadratic term and induction-free handling of the cubic/quartic via `Fintype.sum_prod_type`)?
3. For B, is `deriv` along coordinate lines the right formulation in Lean 4 Mathlib (vs `fderiv`/`iteratedFDeriv`), and which lemmas give
   `deriv (fun s => ∑ l, g l (a l + s * b l)) 0 = ∑ l, deriv (g l) (a l) * b l` (differentiability of the polynomial `g l` via `fun_prop`?)
   and `deriv` of `anharmonicPotential`? Any pitfall with nested `partialD` (differentiability of the inner `deriv` as a function of `w`)?
4. Scope and vote (A alone, A+B, or A+B+C)?
