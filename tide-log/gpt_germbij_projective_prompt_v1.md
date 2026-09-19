# Consult: closing the projective (normalized) singular identifiability story (germbij / laplace Lean)

## Context
Lean 4 + Mathlib seabed `laplace` (Timaeus), germbij note "What expectation values know about the loss landscape".
Notation: losses `L₁ L₂ : ℝ^d → ℝ` nonnegative; `I_i(φ, t) = ∫ φ(w) e^{-t L_i(w)} dw`; `SuperPoly f` := `∀ N, f = o(t^{-N})` as `t → ∞`.
"Projective agreement": for some scalar function `C : ℝ → ℝ` (NO assumptions on `C`) and every `φ ∈ C_c^∞`, `SuperPoly (I₂(φ) − C·I₁(φ))`.
With `C = Z₂/Z₁` (`Z_i = ∫ χ e^{-tL_i}` for a fixed window χ), projective agreement is exactly equality of the normalized expansions `Φ_{L₁} = Φ_{L₂}`.

Already formalised (merged today): **if `L₁, L₂` are `C^∞`, nonnegative, analytic at a common zero `p`, and projectively agree, then `L₁ = L₂` on a neighbourhood of `p`** (`normalized_families_force_germ_eq_at`; locus form; 1/Z form). Mechanism: IBP cancels `C`, sector lower bound kills the germ of `∂(L₂−L₁)`.
Seabed tools: `sector_lower_bound_multi` (∫_{t^{-1/2}S} a² e^{-tK} ≥ vol(S) c² e^{-4C₀} t^{-m-d/2} given `K ≤ C₀‖w‖²` near 0 and `|a(t^{-1/2}x)| ≥ c t^{-m/2}` on S), `quadratic_upper_bound_of_nonneg` (C², K(0)=0, K≥0 ⇒ K ≤ C₀‖w‖² on a ball), `laplace_moment_bounded` (|I(φ,t)| ≤ ∫|φ| for t ≥ 0), `anchor_moment_eq` (I₁(φ₀) = I₂(φ₀) when L₁ = L₂ on supp φ₀), and the scalar-gauge algebra `superPoly_of_mul_anchor` ((C−1)·A SuperPoly and A ≥ κ t^{-n} ⇒ C−1 SuperPoly), `superPoly_sub_of_scalar_gauge` (C−1 SuperPoly, J bounded, B − C·J SuperPoly ⇒ B − J SuperPoly) — all conditional on a polynomial lower bound `hanchor_low` that the seabed has never discharged.

## Candidates
(G) Standalone Gaussian-type lower bound: `K` continuous, ≥ 0, `K(p) = 0`, `C²` at `p`; `ψ` continuous compactly supported, ≥ 0, `= 1` on `ball(p, R)`. Then ∃ κ > 0, T₀: ∀ t ≥ T₀, `κ t^{-d/2} ≤ ∫ ψ e^{-tK}`. (The `a ≡ 1`, `m = 0` case of the sector bound.)
(E) `L` continuous, `L ≥ δ > 0` on `supp ψ` ⇒ `|∫ψ e^{-tL}| ≤ (∫|ψ|) e^{-tδ}` for `t ≥ 0`; hence SuperPoly, and `p(t)·∫ψ e^{-tL}` SuperPoly for polynomially bounded `p`.
(Z) Equal zero loci: `L₁, L₂` `C²` (globally, for convenience), ≥ 0, projectively agreeing over `C_c^∞`, BOTH zero sets nonempty ⇒ `{L₁ = 0} = {L₂ = 0}`. Proof: (⊆) at `p ∈ Z(L₁)∖Z(L₂)`, a bump `ψ` where `L₂ ≥ δ`: `I₂(ψ)` exponentially small, `I₁(ψ) ≳ t^{-d/2}` ⇒ `C` SuperPoly ⇒ every `I₂(φ)` SuperPoly (since `I₁(φ)` bounded) — contradicts (G) at a zero of `L₂`. (⊇) a bump at `p ∈ Z(L₁)` gives `|C(t)| = O(t^{d/2})`; at `q ∈ Z(L₂)∖Z(L₁)`: `I₁(ψ_q)` exponentially small so `C·I₁(ψ_q)` SuperPoly, hence `I₂(ψ_q)` SuperPoly — contradicts (G) at `q`.
(R) Scalar rigidity + transfer: if moreover `L₁ = L₂` near some zero `p` (e.g. from the merged theorem), then `SuperPoly (C − 1)` (bump `ψ₀` in the agreement region: `I₁(ψ₀) = I₂(ψ₀)`, so `(C−1) I₁(ψ₀) = −R_{ψ₀}`; divide by (G)), and consequently `SuperPoly (I₂(φ) − I₁(φ))` for EVERY continuous compactly supported `φ` (gauge removal against bounded `I₁(φ)`). I.e. projective agreement + one common analytic zero ⇒ exact unnormalized agreement beyond all orders.
(N) The 1/Z headline: `Φ_{L₁} = Φ_{L₂}` (normalized by a common window), `L_i` smooth, ≥ 0, analytic at their zeros, both zero sets nonempty ⇒ zero sets equal, `L₁ = L₂` on an open neighbourhood of the common zero set, `Z₂/Z₁ = 1 + o(t^{-∞})`, and `I₂(φ) − I₁(φ) = o(t^{-∞})` for all `φ`.

## Questions
1. Are G, E, Z, R, N correct as stated? Specifically: (i) in Z, is global `C²` (or just `C²` at the zeros) the right regularity, and is "both zero sets nonempty" exactly the needed nondegeneracy (`L₂ = L₁ + c` shows it cannot be dropped)? (ii) In Z(⊇), the polynomial bound `|C(t)| = O(t^{d/2})` uses `I₂(ψ_p) ≤ ∫ψ_p` and `I₁(ψ_p) ≥ κ t^{-d/2}` — is there any issue with `C` possibly negative or non-measurable? (iii) In R, does the transfer really give exact agreement for all `φ`, including `φ` supported far from the zero set (where both `I_i(φ)` are themselves SuperPoly)? (iv) In N, `Z₂/Z₁ − 1` SuperPoly: is positivity of `Z_i` (assumed) enough?
2. Does anything here need analyticity beyond what the merged theorem uses (only R/N inherit it through `hEq`)?
3. Is the "projective ⇒ exact" transfer (R) the right headline for the paper — does it make the note's normalized/unnormalized distinction collapse entirely in the presence of one common analytic zero? Any subtlety with the note's `o(t^{-∞})` conventions (functions vs formal series)?
4. Better or additional nearby targets? E.g. (a) a version of Z with `C_c^0` observables only; (b) the polynomial growth `|C(t)| = O(t^{d/2})` as a standalone statement with a matching lower bound `|C| ≳ t^{-d/2}` (so `C` is "polynomially tame" whenever both zero sets are nonempty); (c) dropping the common-window assumption in N (two different windows χ₁, χ₂).
5. Vote: G+E+Z+R+N as one tide (~450 Lean lines), or a subset?
Answer in numbered form, concrete about statement shapes; end with a one-line vote.
