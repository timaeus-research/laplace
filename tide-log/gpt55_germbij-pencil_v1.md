Response received in 19928.9s
## 1. Correctness of the candidates

### A1: pointwise pencil identity

The identity is correct. Put
\[
g(w)=L_2(w)-L_1(w),\qquad
F(s)=\exp\!\bigl(-t(L_1(w)+s\,g(w))\bigr).
\]
Then
\[
F'(s)=-(t\,g(w))\exp\!\bigl(-t(L_1(w)+s\,g(w))\bigr).
\]
Hence
\[
F(1)-F(0)
=-t\int_0^1 g(w)e^{-t(L_1(w)+s g(w))}\,ds,
\]
which rearranges to the proposed formula. Also
\[
L_1(w)+g(w)=L_2(w),
\]
so the endpoints are exactly the two exponentials in the statement. No sign or positivity hypotheses are needed.

For Lean, it would be cleaner first to prove the scalar theorem

```lean
theorem exp_sub_exp_eq_pencil
    (x y t : ℝ) :
    Real.exp (-t * x) - Real.exp (-t * y)
      =
    t * ∫ s in (0 : ℝ)..1,
      (y - x) * Real.exp (-t * (x + s * (y - x))) := by
  ...
```

and then obtain the `L1 L2 w` version by specialization.

Likely ingredients:

- `HasDerivAt.exp`
- derivative rules such as `.const_mul`, `.mul_const`, `.add_const`
- `intervalIntegral.integral_deriv_eq_sub_of_hasDerivAt`, or the corresponding current variant of `intervalIntegral.integral_deriv_eq_sub`
- `ring_nf` or `ring` for the final rearrangement.

The derivative should preferably be arranged as

```lean
-(t * (y - x)) * Real.exp (...)
```

and then normalized against

```lean
-t * ((y - x) * Real.exp (...))
```

by `ring`.

### A2: integrated pencil identity

Mathematically the formula is correct, but “with suitable hypotheses” needs to be made precise. Continuity of `L1`, `L2`, and `phi`, together with `HasCompactSupport phi`, is sufficient: on `[0,1] × supp phi`, the joint integrand is continuous and compactly supported.

For a reusable theorem, however, it is better not to bake compact-support topology into the first statement. State a direct joint-integrability hypothesis for

```lean
fun p : ℝ × ℝ =>
  (L2 p.2 - L1 p.2) * phi p.2 *
    Real.exp (-t * (L1 p.2 + p.1 * (L2 p.2 - L1 p.2)))
```

over the `s ∈ (0,1]` restriction and Lebesgue measure in `w`. Then prove a compact-support corollary later.

Lean-wise, the main bookkeeping is:

1. rewrite the interval integral using `intervalIntegral.integral_of_le zero_le_one`;
2. use a product measure with `volume.restrict (Set.Ioc 0 1)`;
3. apply `MeasureTheory.integral_integral_swap`, or the relevant consequences of an `Integrable` hypothesis such as `Integrable.integral_prod_left/right`;
4. normalize multiplication order using `ring`.

Thus A2 is not wrong, but its current hypothesis set is informal rather than theorem-ready. In particular, merely assuming the iterated inner integrals exist pointwise is generally not enough for Fubini; absolute/product integrability is the clean condition.

### B: sector lower bound

The constant is correct. On
\[
I_t=[t^{-1/2},2t^{-1/2}],
\]
one has:

- \(w^{2m}\ge t^{-m}\);
- \(tK(w)\le tC_0w^2\le 4C_0\);
- therefore
  \[
  a(w)^2e^{-tK(w)}
  \ge c^2t^{-m}e^{-4C_0};
  \]
- and the interval has length \(t^{-1/2}\).

Consequently,
\[
\int_{I_t}a(w)^2e^{-tK(w)}\,dw
\ge c^2e^{-4C_0}t^{-m-1/2}.
\]

The side condition
\[
4\le r_0^2t
\]
together with \(r_0>0\) implies \(t>0\) and
\[
2t^{-1/2}\le r_0.
\]
So the window is contained in `[0,r0]`. Mathematically the condition is sufficient.

Several formal details should be added:

1. The pointwise hypotheses should explicitly read

   ```lean
   ∀ w ∈ Set.Icc (0 : ℝ) r0, 0 ≤ K w ∧ K w ≤ C0 * w^2
   ```

   and

   ```lean
   ∀ w ∈ Set.Icc (0 : ℝ) r0, c * w^m ≤ |a w|
   ```

2. An integrability or regularity hypothesis is necessary. Pointwise bounds alone do not ensure that the real-valued Bochner integral behaves as intended. Add either

   ```lean
   IntegrableOn
     (fun w => (a w)^2 * Real.exp (-t * K w))
     (Set.Icc ...)
   ```

   or continuity of `a` and `K` on the containing compact interval.

3. Although `0 < t` follows mathematically from the existing assumptions, adding it explicitly will substantially simplify Lean’s square-root or `Real.rpow` reasoning.

4. Use explicit real powers. The notation should be unambiguous, for example

   ```lean
   t ^ (-(m : ℝ) - (1 / 2 : ℝ))
   ```

   if the local `HPow ℝ ℝ ℝ` notation is available, or `Real.rpow` explicitly.

5. The condition `0 ≤ C0` is useful for the monotonicity steps. The lower bound `0 ≤ K` is natural and later proves that the pencil potential is nonnegative, although only the upper bound on `K` is needed for this particular exponential lower bound.

Likely tools include:

- `MeasureTheory.integral_mono_set` or `MeasureTheory.integral_mono_ae`;
- `MeasureTheory.Integrable.integral_mono` / `integral_mono_on`;
- `Real.exp_le_exp` applied after reversing the negative exponents;
- `Real.volume_Icc`;
- `Set.Icc_subset_Icc`;
- substantial `Real.sqrt` or `Real.rpow` normalization.

A cleaner Lean statement would avoid deriving the window inclusion from `4 ≤ r0^2 * t` inside the core theorem. Assume directly

```lean
0 < t
2 * t ^ (-(1 / 2 : ℝ)) ≤ r0
```

and prove the quadratic-condition version as a corollary.

An even cleaner generic form introduces a scale `u > 0`:

```lean
2 * u ≤ r0
```

and integrates over `Icc u (2 * u)`, obtaining

\[
c^2 e^{-4C_0}u^{2m+1}
\]

under a normalized bound such as `t * u^2 = 1`. This separates the elementary interval estimate from real-power algebra.

### C: composite lower bound

The exponent
\[
t^{1-m-1/2}
\]
is correct: A2 contributes a factor `t`, while B contributes `t^{-m-1/2}`.

The proposed sketch still omits theorem-level hypotheses:

- `0 ≤ psi` globally;
- `psi = 1` on the sector;
- compact support or sufficient global integrability;
- `0 ≤ L1`, `0 ≤ L2`;
- continuity/measurability;
- the large-`t` side condition;
- the Fubini hypothesis needed for A2.

The global nonnegativity of `psi` matters because, after taking `phi = g * psi`, the pencil integrand is

\[
g^2\psi e^{-tL_s}\ge0.
\]

That permits restricting the full integral to the favorable sector without losing a lower bound. C is mathematically sound after these additions, but it is not yet a clean one-step target.

## 2. Minimal good target for one tide

The best one-tide target is A1 only, preferably in scalar form.

Reasons:

- no measure-theoretic Fubini infrastructure;
- no compact-support or integrability API;
- no square-root or real-power normalization;
- no set-integral monotonicity;
- exact closed form;
- directly foundational for every later result;
- likely a short proof using existing interval-integral FTC machinery.

A1 plus A2 is no longer a minimal step: A2 introduces product measures, restrictions to `Ioc 0 1`, and joint-integrability bookkeeping. B is elementary on paper but likely larger in Lean because of interval containment, powers, exponent monotonicity, and real-valued integral monotonicity.

## 3. Better nearby decomposition

A good chain toward Theorem 7.3 would be:

1. **Scalar pencil identity**  
   Prove A1 for `x y t : ℝ`.

2. **Pointwise functional corollary**  
   Specialize with `x = L1 w`, `y = L2 w`.

3. **Integrated pencil theorem under direct product integrability**  
   Keep Fubini assumptions explicit. Add a separate compact-support corollary only if needed.

4. **Convex-pencil comparison lemma**  
   For `0 ≤ t`, `s ∈ Set.Icc 0 1`, and `0 ≤ x`, `0 ≤ y`:

   ```lean
   Real.exp (-t * ((1 - s) * x + s * y))
     ≥ Real.exp (-t * (x + y))
   ```

   The key algebraic fact is

   ```lean
   (1 - s) * x + s * y ≤ x + y
   ```

   under those hypotheses. Also record nonnegativity of the convex combination. Likely tools are `Real.exp_le_exp`, `mul_le_mul_of_nonneg_left`, and `linarith`/`nlinarith`.

5. **Scale-window sector lemma**  
   First prove it on `[u,2u]`, with direct inclusion `2*u ≤ r0`. This isolates set-integral monotonicity from `t^{-1/2}` algebra.

6. **Laplace-scale corollary**  
   Substitute `u = t^{-1/2}` and derive the displayed power of `t`.

7. **Composite identifiability lower bound**  
   Apply the integrated pencil identity with `phi = g * psi`, use nonnegativity to restrict to the good sector, then use the pencil comparison and sector lemma.

The comparison lemma is an excellent small auxiliary result, but by itself it is less central and less self-contained than the exact pencil identity.

## Vote

**Candidate A1 only, stated first as the scalar pencil identity and followed by the immediate pointwise functional corollary.**Response saved to sri/learning-theory/lean/laplace-tide-germbij-pencil/tide-log/gpt55_germbij-pencil_v1.md

