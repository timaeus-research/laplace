1. **A1:** Mathematically correct, including the sign and factor \(t\). No regularity assumptions on `L1` or `L2` are needed because the differentiation is only in `s` at fixed `w`.

2. **A2:** Mathematically correct under explicit Fubini/integrability assumptions. Continuity of `L1`, `L2`, and continuous compact support of `phi` are sufficient: the joint integrand is continuous and supported in a compact set in the `w` variable. Lean bookkeeping may still be substantial.

3. **B:** The constant and scaling are correct:
   \[
   c^2 e^{-4C_0}t^{-m-1/2}.
   \]
   The condition \(4\le r_0^2t\) ensures the integration interval lies in \([0,r_0]\) and implies \(t>0\). However, as stated it lacks measurability/integrability assumptions on `a` and `K`; arbitrary functions satisfying the pointwise bounds need not yield the claimed Lebesgue-integral inequality. Add measurability, or simply continuity on `Icc 0 r0`. Lean should also express \(t^{-1/2}\) explicitly using `Real.sqrt` or `Real.rpow`.

**Minimal good tide target:** A1. It is exact, foundational, low-risk, and directly formalises the core pencil identity before introducing Fubini infrastructure.

**Nearby improvements:**
- Prove A1 first with scalar parameters `x y : ℝ`, then derive the `L1 L2 w` formulation as a one-line corollary.
- After A1, prove A2 under a single explicit hypothesis that the joint integrand is integrable on `Icc 0 1 × ℝ`; later derive a compact-support continuity corollary.

VOTE: A1