1. **Tail estimate:** correct in substance.

   - **Support/rate splitting:** On the nonzero part, `q • x ∈ U` and `q • x ∉ ball 0 r`, hence
     \[
     G := \frac{L(qx)-L(0)}{q^2}\ge c\|x\|^2,\qquad
     G\ge \frac{cr^2}{q^2}.
     \]
     Therefore
     \[
     G\ge \tfrac12 c\|x\|^2+\tfrac12 cr^2/q^2,
     \]
     so the claimed exponential split is valid. In Lean, case-split first on the indicator and then on membership in the cutoff ball.

   - **Polynomial growth:** For `0 < q ≤ 1`,
     `‖q • x‖ = q‖x‖ ≤ ‖x‖`, hence
     `1 + ‖q • x‖^n ≤ 1 + ‖x‖^n`. Together with `0 ≤ χ ≤ 1`, this gives
     `|P(q • x) * (1 - χ(q • x))| ≤ C(1 + ‖x‖^n)`.

   - **Denominator:** If
     `D q = ∫ x, A.integrand 1 q x → Z_H` with `Z_H > 0`, then eventually
     `D q ≥ Z_H / 2 > 0`. Thus both the rescaled denominator and, after restoring the positive dilation prefactor, the original posterior denominator are nonzero. The junk quotient values never occur eventually.

   - **Linearity:** Work directly after `posteriorIntegral_eq`. Cancel the common positive prefactor, then combine the two rescaled numerator integrals using `integral_sub`. This still requires integrability, but `integrable_integrand` applies to the continuous polynomial-growth functions
     `x ↦ P(q • x)` and `x ↦ P(q • x) * χ(q • x)`. This is cleaner than transporting unrescaled integrability. Some integrability argument is unavoidable because the cutoff cancellation must happen inside the integral.

   - The resulting bound is
     `|tail q| ≤ K exp (-(c*r^2/2) / q^2)` eventually. Under
     `q = (sqrt t)⁻¹`, this becomes `K exp (-δ*t)` eventually. The proposed exponential-to-`SuperPoly` lemma completes the proof.

2. **CC-data premise:** The proposed pairwise shape is mathematically adequate:
   it means test functions compactly supported in the common region
   `A.U ∩ B.U`. Because both domains contain a ball around zero, there is enough room for the common bump.

   Do not describe it literally as `C_c^∞(U)` unless the two package domains are identified. Say “smooth compactly supported tests in the common localization region.” For exact note-level fidelity, an even cleaner interface introduces a set `V` with
   `Metric.ball 0 r ⊆ V`, `V ⊆ A.U`, and `V ⊆ B.U`, and quantifies over tests with `tsupport φ ⊆ V`. The intersection formulation is simpler and sufficient here.

3. **Smoothness:** No conceptual pitfall. Coordinate evaluation on `EuclidD d` is a continuous linear map, hence smooth; binary products and finite products preserve `ContDiff ℝ ⊤`. Polynomial-growth certificates follow from
   `|x i| ≤ ‖x‖`:
   - `|x i * x j| ≤ ‖x‖²`;
   - `|monomialTest m x| ≤ ‖x‖^k`.

   The main cost is Lean API plumbing around `PiLp` coordinate maps and `Finset.prod`, not mathematics. The `d = 0` case is harmless.

4. **Target:** A is the minimal complete target. B leaves the note-literal implication unexposed; C mixes in the distinct located-moment interface and should be a follow-up. Ensure the corollary docstrings say common compactly supported test data, not bare monomial data and not a single shared `U` unless one is explicitly supplied.

**Vote: A.**