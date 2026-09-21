### 1. Mathematics

**A–C are correct**, under the standing measurability and measure-class assumptions:

- **A:** The accepted part becomes \(Z^{-1}\int_A\int_B\mathrm{flux}(x,y)\,d\mu(y)d\mu(x)\). The rejection part is exactly \(\int_{A\cap B}\pi(x)(1-a(x))\,d\mu(x)\).
- **B:** Tonelli plus flux symmetry swaps the accepted term; intersection symmetry handles rejection. **No integrability assumption is needed**, but Tonelli’s measure-class assumptions still are: ensure the seabed supplies `SFinite μ` (or `SigmaFinite μ`). Positivity and proposal normalisation alone should not be treated as supplying that Lean instance.
- **C:** Yes, provided \(0<T<\infty\) and the target law has density \(T^{-1}\pi\). For the probability interpretation, also require \(T=\int\pi\,d\mu\).
- **Terminology:** “Reversibility” is standard for the rectangle identity. It is equivalent to D for finite joint measures: measurable rectangles form a generating π-system, so agreement there determines the measure. No standard-Borel assumption is needed for this uniqueness argument.

### 2. Lean

- **Restricted Tonelli:** Yes. Instantiate the measures as `μ.restrict A` and `μ.restrict B`; restrictions inherit `SFinite`. Use joint **measurability** of the flux to obtain `AEMeasurable` for this particular product measure. An `AEMeasurable` fact already specialised to `μ.prod μ` may not elaborate directly.
- **Rejection term:** Yes, `Measure.restrict_restrict hB` has the indicated orientation:
  ```lean
  (μ.restrict A).restrict B = μ.restrict (B ∩ A)
  ```
  Apply `lintegral_indicator hB` against `μ.restrict A`, then simplify using this identity and intersection commutativity.
- **Law version:** Moving restriction through `withDensity`, then applying the density integral formula, is the right route. Watch both rewrite orientation and multiplication order. Supply explicit typed facts such as
  ```lean
  have hK : Measurable (fun x => mhKernelSet … x B) := …
  ```
  and similarly for the density. Lambda/`∘` presentation differences are elaboration issues, not mathematical obstacles; `change` or `simpa only [Function.comp_def]` usually resolves them.
- **D:** The general generating-π-system extensionality machinery, together with `generateFrom_prod`, suffices; the finite case can use `univ` as the covering set. Check the pinned Mathlib for a rectangle-specific helper before building this manually—I would not promise a particular `ext_prod`/`prod_eq` signature without inspecting it. You also need the rectangle formula for the kernel joint measure and the swap-preimage calculation.

### 3. Scope

**A+B+C is a sensible tide; roughly 200 lines is plausible**, given the existing measurability and MALA/pMALA wrappers. Make A a reusable lemma.

D is worth a short exploratory attempt: perhaps **20–50 lines with convenient joint-measure and rectangle-extensionality APIs**, substantially more otherwise.

The invariance corollary is cheap. Defer self-adjointness: after D, bounded real-valued measurable functions can be handled directly by joint-law symmetry and Fubini, without a fresh monotone-class proof. A genuine operator statement on all of \(L^2(\nu)\) additionally needs well-definedness and contraction infrastructure.

Vote: A+B+C — This completes reversibility at the existing kernel interface while keeping joint-measure and operator API work optional.