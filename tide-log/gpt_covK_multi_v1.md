1. **DCT is sound; check the integrability API.** Since \(L\ge0\), \(s>t/2\) indeed implies
   \[
   e^{-sL(u)}\le e^{-(t/2)L(u)},
   \]
   giving the proposed derivative bound. Use the open neighborhood `Ioi (t/2)`, continuity for measurability, and `Integrable.norm` for the majorant. There is no new issue from `volume` on `Fin d → ℝ`. Besides the bound, supply integrability at the base point and the pointwise parameter derivative. **For A, the listed coordinate-piece lemmas do not immediately cover arbitrary mixed monomials:** you need integrability of
   \(\ell_k(u_k)\prod_n u_n^{e_n}e^{-aL(u)}\).
   This follows by separability and the one-dimensional energy-weighted moment bounds, but may require a new helper. For the quotient rule, partition-function positivity at \(t\) gives the required nonzero denominator.

2. **Direct B is cleaner.** The stated seabed already supplies precisely the probe and energy-weighted probe integrability needed. This avoids exponent bookkeeping for \(u_i u_j\), including \(i=j\), and eventual linearity rewrites. Ideally prove one reusable Gibbs differentiation lemma for a fixed observable, then instantiate it with \(1\) and the quadratic probe. If its hypotheses concern domination at \(t/2\), retain base-point integrability and the relevant measurability hypotheses explicitly.

3. **Transport is straightforward provided the frame is fixed in \(s\).** Rewrite the entire expectation function using the all-\(s\) transport equality, apply B to the transported probe, and rewrite the covariance at \(t\). `probe_affineFrame` is a pointwise observable identity, so introduces no derivative term. Check only that B receives the **transformed coefficients** prescribed by that identity. If transport actually requires \(s>0\), local eventual equality near \(t>0\) suffices instead of global `funext`.

4. **Scope:** direct B+C gives the desired oscillator result with the least additional infrastructure. A is worthwhile as a subsequent generalization, particularly if the differentiation argument has been factored into a reusable lemma.

**Vote: direct-B+C, with a reusable dominated-differentiation helper; defer A.**