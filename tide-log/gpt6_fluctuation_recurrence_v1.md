The mathematical argument is correct, including the \(\lambda=0\) case. There is one exponent typo in question 4:
\[
t^\lambda t^{-1/2}=t^{\lambda-1/2},
\]
whereas \(t^{\lambda-1}t^{-1/2}=t^{\lambda-3/2}\).

**Version-checking limitation:** I cannot inspect the v4.33.0 sources in this environment, so I cannot honestly certify the exact improper-FTC declaration or its argument order. In particular, I would not present your proposed name with a guessed signature as compiling code. Below I give the assembly, distinguish the library-dependent step, and explain how to extract the exact declarations from your installation.

## 1. The improper FTC: distinguish two possible interfaces

The interface you want is mathematically:

```lean
-- Desired interface, NOT a claimed Mathlib declaration.
{g g' : ℝ → ℝ} {L₀ L∞ : ℝ}
(hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt g (g' t) t)
(hint : IntegrableOn g' (Set.Ioi (0 : ℝ)))
(hzero : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 L₀))
(htop : Tendsto g atTop (𝓝 L∞)) :
    (∫ t in Set.Ioi (0 : ℝ), g' t) = L∞ - L₀
```

Do not confuse this with a theorem concluding

```lean
(∫ t in Set.Ioi c, g' t) = L∞ - g c
```

which may instead require continuity at the finite endpoint, or differentiability on `Ici c`.

That distinction matters here:

* Your `g` is continuous at zero for `0 < lam`.
* It need **not** be differentiable at zero. For example, when `0 < lam < 1`, the power factor already causes trouble.
* Thus a theorem requiring `HasDerivAt` on `Ici 0` cannot be applied directly.
* A theorem requiring continuity on `Ici 0` and derivatives on `Ioi 0` is suitable.
* `Ioi` versus `Ici` in the **integral** is harmless for Lebesgue measure; the distinction in the **derivative hypotheses** is not.

To obtain the actual v4.33 declarations, run:

```sh
rg -n -A 28 'integral_Ioi_of_hasDeriv' \
  .lake/packages/mathlib/Mathlib
```

Then inspect the relevant declaration with `#check` under:

```lean
import Mathlib
open Set Filter MeasureTheory
open scoped Topology
```

If the available theorem only takes a boundary value `g 0`, you do not need a sophisticated extension argument: for your chosen definitions,
\[
g(0)=0\quad(\lambda>0), \qquad g_0(0)=1.
\]
Prove continuity there and use those values.

If its derivative hypothesis includes the endpoint, apply it at a positive cutoff `ε`, then let `ε → 0⁺`; integrability of `g'` supplies convergence of the truncated integrals. That works, though it is less convenient than an open-endpoint FTC.

## 2. Define the derivative using the shifted integrands

This is the most useful implementation choice: **make integrability and integral expansion definitional**, and put all power algebra in the derivative proof.

For example:

```lean
let F : ℝ → ℝ → ℝ :=
  fun p t =>
    t ^ (p - 1) *
      Real.exp (-β * t + β * a * Real.sqrt t)

let D : ℝ → ℝ :=
  fun t =>
    lam * F lam t
      - β * F (lam + 1) t
      + (β * a / 2) * F (lam + (1 : ℝ) / 2) t
```

Then the integrability assembly is exactly the one you suggest:

```lean
have hI₀ : IntegrableOn (F lam) (Ioi (0 : ℝ)) := by
  simpa only [F] using
    fluctuation_integrableOn β lam hβ hlam a

have hI₁ : IntegrableOn (F (lam + 1)) (Ioi (0 : ℝ)) := by
  simpa only [F] using
    fluctuation_integrableOn β (lam + 1) hβ (by linarith) a

have hIhalf :
    IntegrableOn (F (lam + (1 : ℝ) / 2)) (Ioi (0 : ℝ)) := by
  simpa only [F] using
    fluctuation_integrableOn β (lam + (1 : ℝ) / 2)
      hβ (by linarith) a

have hD : IntegrableOn D (Ioi (0 : ℝ)) := by
  exact
    ((hI₀.const_mul lam).sub (hI₁.const_mul β)).add
      (hIhalf.const_mul (β * a / 2))
```

Here `IntegrableOn` is integrability for the restricted measure, so the ordinary `Integrable.const_mul`, `Integrable.sub`, and `Integrable.add` operations apply.

No positivity of the coefficients is needed.

## 3. Boundary limits

### At zero

Prove continuity of

```lean
fun t : ℝ =>
  t ^ lam * Real.exp (-β * t + β * a * Real.sqrt t)
```

at zero, using `0 < lam`. Then restrict its ordinary neighborhood limit to `𝓝[>] 0`.

The steps are:

1. `t ^ lam → 0`, since `lam > 0`;
2. `Real.sqrt t → 0`;
3. the exponent tends to zero;
4. the exponential tends to one;
5. multiply.

In particular, proving ordinary continuity at zero is enough; you do not need a special one-sided `rpow` argument.

The useful elementary declarations to inspect are:

```lean
#check Real.continuousAt_rpow_const
#check Real.zero_rpow
#check Real.continuous_sqrt
#check Real.continuous_exp
```

A schematic assembly is:

```lean
have hg_cont :
    ContinuousAt
      (fun t : ℝ =>
        t ^ lam * Real.exp (-β * t + β * a * Real.sqrt t))
      0 := by
  -- rpow continuity using hlam; all other operations are continuous.
  ...

have hg_zero :
    Tendsto
      (fun t : ℝ =>
        t ^ lam * Real.exp (-β * t + β * a * Real.sqrt t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Restrict hg_cont.tendsto to nhdsWithin, then simplify the value at 0.
  ...
```

### At infinity

Your proposed bound is particularly convenient because it works for **every real `a`**, without splitting on its sign.

For `0 ≤ t`,
\[
a\sqrt t\le \frac{t+a^2}{2}
\]
follows from \((\sqrt t-a)^2\ge0\). Consequently,
\[
-\beta t+\beta a\sqrt t
\le \frac{\beta a^2}{2}-\frac{\beta t}{2},
\]
and therefore
\[
0\le g(t)
\le e^{\beta a^2/2}\,t^\lambda e^{-(\beta/2)t}.
\]

The algebraic part can be organized as:

```lean
have hquad (t : ℝ) (ht : 0 ≤ t) :
    a * Real.sqrt t ≤ (t + a ^ 2) / 2 := by
  nlinarith [sq_nonneg (Real.sqrt t - a), Real.sq_sqrt ht]
```

Multiply that inequality by the positive `β`, then use `Real.exp_le_exp` and `Real.exp_add`. Multiplication by `t ^ lam` preserves the bound on the positive tail.

It remains to establish
\[
t^\lambda e^{-(\beta/2)t}\longrightarrow0.
\]

To locate the actual exponential-domination theorem rather than guessing its spelling:

```sh
rg -n 'tendsto_.*rpow.*exp|tendsto_.*exp.*rpow|isLittleO.*exp' \
  .lake/packages/mathlib/Mathlib/Analysis
```

If the available theorem only handles `x ^ lam * exp (-x)`, compose with `x = (β / 2) * t`. On the positive tail, use `Real.mul_rpow` to extract the constant \((\beta/2)^\lambda\). Finally squeeze `g` between zero and the displayed upper bound.

## 4. Derivative assembly

I recommend replacing `sqrt` by `rpow` **inside the derivative calculation**, using:

```lean
#check Real.sqrt_eq_rpow
#check Real.hasDerivAt_rpow_const
#check Real.rpow_add
```

This avoids proving identities involving `1 / Real.sqrt t`.

For `ht : 0 < t`, differentiate

\[
t^\lambda\exp\bigl(-\beta t+\beta a\,t^{1/2}\bigr)
\]

using:

* `Real.hasDerivAt_rpow_const` for both powers;
* `HasDerivAt.const_mul`, `.add`, `.sub`;
* `HasDerivAt.exp`;
* `HasDerivAt.mul`.

The rpow derivative theorem’s condition is worth inspecting: in Mathlib interfaces it can be phrased as a disjunction allowing differentiability at zero for suitable exponents, rather than merely `t ≠ 0`. Here the nonzero branch follows from `ht`.

The raw derivative is
\[
\lambda t^{\lambda-1}e^u
+t^\lambda e^u\left(-\beta+\beta a\left(\frac12t^{1/2-1}\right)\right).
\]

First establish the power identity:

```lean
have hpow :
    t ^ lam * t ^ ((1 : ℝ) / 2 - 1)
      = t ^ (lam - (1 : ℝ) / 2) := by
  rw [← Real.rpow_add ht]
  congr 1
  ring
```

Also normalize the shifted exponents:

```lean
have hexp₁ : (lam + 1) - 1 = lam := by ring
have hexphalf :
    (lam + (1 : ℝ) / 2) - 1 = lam - (1 : ℝ) / 2 := by
  ring
```

Then use `convert` on the product-rule result, normalize with these identities and `Real.sqrt_eq_rpow`, and finish the scalar algebra with `ring`.

**Do not expect `ring` to prove rpow identities.** Rewrite the rpow products first; `ring` then treats the remaining powers and exponential as atoms.

The target should be:

```lean
have hg_deriv :
    ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt
        (fun t : ℝ =>
          t ^ lam * Real.exp (-β * t + β * a * Real.sqrt t))
        (D t) t := by
  ...
```

## 5. Expanding the integral and finishing the algebra

After the FTC, you have:

```lean
have hFTC : (∫ t in Ioi (0 : ℝ), D t) = 0 := by
  -- Apply the verified improper-FTC theorem.
  -- Boundary calculation: 0 - 0 = 0.
  ...
```

Expand using the same integrability proofs as above:

```lean
integral_add
integral_sub
integral_const_mul
```

Specifically, the integrability arguments for the outer addition are

```lean
(hI₀.const_mul lam).sub (hI₁.const_mul β)
hIhalf.const_mul (β * a / 2)
```

and for the subtraction they are

```lean
hI₀.const_mul lam
hI₁.const_mul β
```

Since `D` was defined using `F` at shifted parameters, unfolding `F` and `fluctuation` now identifies the integrals directly. No almost-everywhere exponent rewriting is necessary here.

Obtain:

```lean
have hlin :
    lam * fluctuation β lam a
      - β * fluctuation β (lam + 1) a
      + (β * a / 2) *
          fluctuation β (lam + (1 : ℝ) / 2) a = 0 := by
  ...
```

The final algebra is of the form:

```lean
have hβne : β ≠ 0 := ne_of_gt hβ
field_simp [hβne]
nlinarith [hlin]
```

An explicit intermediate rearrangement can make this more predictable:

```lean
have hbalance :
    β * fluctuation β (lam + 1) a =
      lam * fluctuation β lam a
        + (β * a / 2) *
            fluctuation β (lam + (1 : ℝ) / 2) a := by
  linarith [hlin]
```

Then clear denominators in the recurrence and use `hbalance`.

## 6. The \(\lambda=0\) case

Yes, but it is a **separate application of the FTC**, not an application of the recurrence theorem whose hypothesis is `0 < lam`.

Use the simpler primitive

```lean
g₀ t := Real.exp (-β * t + β * a * Real.sqrt t)
```

and define only the two surviving derivative terms:

```lean
D₀ t :=
  -β * F 1 t
    + (β * a / 2) * F ((1 : ℝ) / 2) t
```

Then:

* integrability uses only exponents `1` and `1 / 2`;
* `g₀ → 1` at zero;
* `g₀ → 0` at infinity;
* the FTC gives
  \[
  -\beta S_1+\frac{\beta a}{2}S_{1/2}=-1.
  \]

Hence
\[
S_1=\frac a2S_{1/2}+\frac1\beta.
\]

There is **no need to establish integrability at exponent zero**. In particular, do not first demand integrability of `F 0` and then multiply its proof by zero. Remove the zero term before assembling integrability—or use the integrability of the identically zero function. The separate two-term definition is cleaner.