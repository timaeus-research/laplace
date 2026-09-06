Assume throughout that **\(β>0\), \(b>0\)**, with \(a\in\mathbb R\) arbitrary and \(n\to+\infty\) through positive reals.

The exact leading coefficient is
\[
\boxed{C=\frac14\,\mathrm{fluctuation}\;β\;\frac12\;a.}
\]
There is **no additional factor \(1/2\)**. The leading coefficient is independent of \(b\); \(b\) first appears in the next-order term.

My recommendation is to prove the leading equivalence through a **uniform bounded-error estimate for a one-dimensional primitive**. This avoids both logarithmic integrability at zero and triangular-domain Fubini.

## 1. Reduction and exact expansion

Write
\[
f(s)=e^{-βs^2+βas},\qquad
F(x)=\int_0^x f(s)\,ds,\qquad
A=\int_0^\infty f(s)\,ds.
\]
Your existing 1D substitution theorem, with \(n=1,h=0,k=1\), gives
\[
A=\frac12 S_{1/2}(a).
\]

Set
\[
L=b^2\sqrt n.
\]

For \(u>0\), the substitution \(s=\sqrt n\,u\,v\) gives
\[
\int_0^b f(\sqrt n\,u\,v)\,dv
=\frac{F(b\sqrt n\,u)}{\sqrt n\,u}.
\]
A second one-dimensional substitution, \(x=b\sqrt n\,u\), gives
\[
\boxed{
Z_2(n)=\frac1{\sqrt n}H(L),\qquad
H(L):=\int_0^L\frac{F(x)}x\,dx.
}
\]
The value assigned to \(F(x)/x\) at \(x=0\) is immaterial.

### Where the logarithm comes from

Once \(x\) is large, \(F(x)\approx A\). Thus
\[
H(L)\approx A\int_1^L\frac{dx}{x}=A\log L.
\]
Since
\[
\log L=2\log b+\frac12\log n,
\]
we obtain
\[
Z_2(n)\sim \frac A2 n^{-1/2}\log n
=\frac14S_{1/2}(a)n^{-1/2}\log n.
\]

In the original outer variable, the transition is around
\[
u=\frac1{b\sqrt n}.
\]
Above this scale, the inner integral is saturated and the outer integrand is approximately \(A/(\sqrt n\,u)\).

### Exact next-order term

Define the absolutely convergent logarithmic moment
\[
B=\int_0^\infty f(s)\log s\,ds.
\]
Swapping the integrals in \(H\) gives
\[
H(L)=\int_0^L f(s)\log(L/s)\,ds.
\]
Consequently,
\[
H(L)=A\log L-B+R(L),
\qquad
R(L)=\int_L^\infty f(s)\log(s/L)\,ds.
\]

Let
\[
E=e^{βa^2/2}.
\]
Gaussian domination gives
\[
0<f(s)\le E e^{-βs^2/2}\qquad(s\ge0).
\]
For \(L\ge1\), use \(0\le\log(s/L)\le s\) on \(s\ge L\):
\[
0\le R(L)
\le E\int_L^\infty s e^{-βs^2/2}\,ds
=\frac Eβe^{-βL^2/2}.
\]

Therefore
\[
\boxed{
Z_2(n)
=\frac14S_{1/2}(a)n^{-1/2}\log n
+\bigl(S_{1/2}(a)\log b-B\bigr)n^{-1/2}
+\frac{R(b^2\sqrt n)}{\sqrt n}.
}
\]
Eventually,
\[
0\le \frac{R(b^2\sqrt n)}{\sqrt n}
\le \frac Eβ n^{-1/2}e^{-(βb^4/2)n}.
\]

Equivalently, if
\[
J=\int_0^\infty t^{-1/2}\log t\,
             e^{-βt+βa\sqrt t}\,dt,
\]
then \(B=J/4\), so the constant-order coefficient is
\[
\boxed{D=S_{1/2}(a)\log b-\frac14J.}
\]

For comparison, the state-density computation gives directly
\[
Z_2(n)=\frac1{4\sqrt n}
\int_0^{nb^4}t^{-1/2}
 \bigl(\log n+4\log b-\log t\bigr)
 e^{-βt+βa\sqrt t}\,dt,
\]
which confirms the coefficient \(S_{1/2}(a)/4\).

---

## 2. Recommended leading-term proof: bounded error, no logarithmic moment

Introduce the first moment
\[
M=\int_0^\infty s f(s)\,ds.
\]
It is finite, and
\[
M\le \frac Eβ.
\]

Two elementary bounds suffice:

1. For \(x\ge0\),
   \[
   0\le F(x)\le Ex.
   \]

2. For \(x>0\),
   \[
   0\le A-F(x)=\int_x^\infty f(s)\,ds\le \frac Mx.
   \]
   The last inequality follows from \(x f(s)\le s f(s)\) for \(s>x\).

For \(L\ge1\), split at \(1\):
\[
H(L)-A\log L
=
\int_0^1\frac{F(x)}x\,dx
-\int_1^L\frac{A-F(x)}x\,dx.
\]
Now
\[
0\le\int_0^1\frac{F(x)}x\,dx\le E,
\]
and
\[
0\le\int_1^L\frac{A-F(x)}x\,dx
\le M\int_1^L x^{-2}\,dx
=M(1-L^{-1})\le M.
\]
Hence the particularly useful estimate
\[
\boxed{
A\log L-M\le H(L)\le A\log L+E
\qquad(L\ge1).
}
\]

This immediately gives
\[
Z_2(n)
=\frac14S_{1/2}(a)n^{-1/2}\log n+O(n^{-1/2}),
\]
and thus the requested equivalence.

### Boundary regimes, explicitly

- **Small \(u\):** on \(0<u\le1/(b\sqrt n)\),
  \[
  \frac{F(b\sqrt n\,u)}{\sqrt n\,u}\le Eb.
  \]
  The contribution is at most \(E/\sqrt n\).

- **Saturated region:** the integrated error in replacing \(F\) by \(A\) is at most \(M/\sqrt n\).

- **Near \(u=b\):** there is no extra singular boundary layer. Any fixed band \([\theta b,b]\), \(0<\theta<1\), contributes at most
  \[
  \frac A{\sqrt n}\log(1/\theta)=O(n^{-1/2}).
  \]
  The logarithm comes from the growing ratio between the lower saturation scale and the fixed chart endpoint.

---

## 3. Lean-sized lemma plan

Below are mathematical specifications for Lean lemmas, not purportedly compiling code. I would use `Ioc` for chart/set integrals and an **interval integral for the primitive**, because its continuity is then easy to obtain.

For example:
```lean
def quadraticKernel (β a s : ℝ) : ℝ :=
  Real.exp (-β * s ^ 2 + β * a * s)

def quadraticPrimitive (β a x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, quadraticKernel β a s

def quadraticMass (β a : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), quadraticKernel β a s

def quadraticMoment (β a : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), s * quadraticKernel β a s

def logarithmicPrimitive (β a L : ℝ) : ℝ :=
  ∫ x in Set.Ioc (0 : ℝ) L, quadraticPrimitive β a x / x
```

For positive endpoints, bridge interval integrals to `Ioc` using
`intervalIntegral.integral_of_le`.

Each item below is intended as a small lemma, splitting off routine algebra if it approaches your line budget.

### A. Kernel domination

**Statement:** for `hβ : 0 < β` and `hs : 0 ≤ s`,
```lean
0 ≤ quadraticKernel β a s ∧
quadraticKernel β a s ≤
  Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * s ^ 2)
```

**Proof:** from
\[
-βs^2+βas\le -(β/2)s^2+βa^2/2.
\]

Use `sq_nonneg (s - a)`, `nlinarith`, `Real.exp_le_exp`, and `Real.exp_add`.

Alternatively specialize your fluctuation domination at \(t=s^2\), simplifying \(\sqrt{s^2}=s\).

**Pitfall:** direct quadratic algebra is probably shorter than managing `sqrt (s ^ 2)`.

### B. Integrability of the mass and first moment

Two statements:
```lean
IntegrableOn (quadraticKernel β a) (Set.Ioi 0)
IntegrableOn (fun s => s * quadraticKernel β a s) (Set.Ioi 0)
```

**Preferred proof:** reuse the integrability facts underlying your standard 1D theorem, with \(h=0\) and \(h=1\), \(k=1,n=1\).

**Useful fallback:** your existing integral identities and `fluctuation_pos` show that both integrals are nonzero. Nonintegrability would make the Bochner integral zero, by `integral_undef`. Thus the identities themselves can recover integrability.

That fallback is logically valid, although a direct integrability wrapper is cleaner.

### C. Mass identification and positivity

**Statements:**
```lean
quadraticMass β a = (1 / 2 : ℝ) * fluctuation β (1 / 2) a
0 < quadraticMass β a
```

Use `standardIntegral1D_eq_fluctuation` at \(n=1,h=0,k=1\), then `fluctuation_pos`.

For the moment, the analogous identity is
\[
M=\frac12 S_1(a).
\]
Your `fluctuation_le_gaussian` then gives \(M\le E/β\).

**Pitfall:** annotate every half intended as real, especially exponents.

### D. Primitive continuity and linear bound

Separate statements:

```lean
Continuous (quadraticPrimitive β a)
```

and, for `hx : 0 ≤ x`,
```lean
0 ≤ quadraticPrimitive β a x ∧
quadraticPrimitive β a x ≤ Real.exp (β * a ^ 2 / 2) * x
```

Continuity uses the Mathlib theorem saying that the interval-integral primitive of a continuous function is continuous. If necessary, obtain it from the corresponding `HasDerivAt` primitive theorem.

For the bounds, use `intervalIntegral.integral_of_le`, `setIntegral_mono_on`, and the integral of a constant.

### E. Integrability of \(F(x)/x\) on bounded positive intervals

For `hL : 0 ≤ L`:
```lean
IntegrableOn
  (fun x => quadraticPrimitive β a x / x)
  (Set.Ioc 0 L)
```

On `Ioc 0 L`,
\[
0\le F(x)/x\le E.
\]

Use continuity/measurability of the primitive and division, followed by integrability by domination on the finite-measure interval.

**Pitfall:** do not ask Lean for continuity of `F x / x` at zero. It is unnecessary, and the literal Lean function has value zero there rather than the continuous-extension value \(f(0)=1\).

### F. Tail splitting and moment bound

First prove, for `hx : 0 ≤ x`,
```lean
quadraticMass β a - quadraticPrimitive β a x =
  ∫ s in Set.Ioi x, quadraticKernel β a s
```

Use the disjoint decomposition
\[
(0,\infty)=(0,x]\;\dot\cup\;(x,\infty),
\]
with `integral_union` and integrability restrictions.

Then prove, for `hx : 0 < x`,
```lean
0 ≤ quadraticMass β a - quadraticPrimitive β a x ∧
quadraticMass β a - quadraticPrimitive β a x
  ≤ quadraticMoment β a / x
```

Use `setIntegral_mono_on` for \(x f(s)\le s f(s)\), and monotonicity when restricting the nonnegative moment integrand.

**Pitfall:** prove
\[
x(A-F(x))\le M
\]
first, then divide by positive \(x\).

### G. Two elementary interval integrals

For `hL : 1 ≤ L`:
```lean
(∫ x in Set.Ioc (1 : ℝ) L, (1 : ℝ) / x) = Real.log L
```
and
```lean
(∫ x in Set.Ioc (1 : ℝ) L, (1 : ℝ) / x ^ 2) = 1 - 1 / L
```

Use `intervalIntegral.integral_of_le` and the library formulas for inverse and real powers. I would check the installed names rather than assume a particular `integral_one_div` spelling.

A stable fallback is the fundamental theorem with primitives `Real.log` and `fun x => -(1 / x)`, respectively. Everything is bounded away from zero.

### H. Uniform logarithmic-primitive bounds

For `hL : 1 ≤ L`:
```lean
quadraticMass β a * Real.log L - quadraticMoment β a
  ≤ logarithmicPrimitive β a L
```
and
```lean
logarithmicPrimitive β a L
  ≤ quadraticMass β a * Real.log L
      + Real.exp (β * a ^ 2 / 2)
```

Split `Ioc 0 L` at `1`, use E–G, and integrate the pointwise bounds.

I would make the split identity its own lemma:
\[
H(L)-A\log L
=\int_{(0,1]}F(x)/x
-\int_{(1,L]}(A-F(x))/x.
\]

This keeps the two inequality proofs short.

### I. Inner chart substitution

For `hn : 0 < n`, `hu : 0 < u`, `hb : 0 < b`:
\[
\int_{(0,b]} f(\sqrt n\,u\,v)\,dv
=(\sqrt n\,u)^{-1}F(b\sqrt n\,u).
\]

Use `intervalIntegral.integral_comp_mul_left`, after converting the bounded set integral to an interval integral.

**Pitfalls:**

- The scaling factor is positive.
- Depending on the theorem’s orientation, some algebraic rearrangement is needed.
- Normalize the original exponent to \(f(\sqrt n\,u\,v)\) separately, using `Real.sq_sqrt hn.le` and `ring`.

### J. Outer chart substitution

For positive \(n,b\):
\[
Z_2(n)=\frac1{\sqrt n}H(b^2\sqrt n).
\]

After I, factor out \(1/\sqrt n\), then substitute \(x=b\sqrt n\,u\).

The identity to normalize is
\[
\frac{F(cu)}u=c\,\frac{F(cu)}{cu},\qquad c=b\sqrt n>0.
\]

Use the same interval substitution theorem and E for integrability.

**Important:** this route requires **no two-dimensional Fubini theorem at all**.

### K. Explicit eventual error bound

For positive \(n\) satisfying \(1\le b^2\sqrt n\):
\[
\left|Z_2(n)-\frac A2\frac{\log n}{\sqrt n}\right|
\le
\frac{2A|\log b|+E+M}{\sqrt n}.
\]

Use H, J, and
\[
\log(b^2\sqrt n)=2\log b+\tfrac12\log n.
\]

`Real.log_mul`, `Real.log_pow`, and the square-root logarithm identity handle the latter; positivity hypotheses should be explicit.

### L. Final asymptotic

A natural target is
```lean
(fun n : ℝ => Z₂ β a b n) ~[atTop]
  (fun n : ℝ =>
    (fluctuation β (1 / 2) a / 4) *
      n ^ (-(1 / 2 : ℝ)) * Real.log n)
```

From K:
\[
Z_2-Cn^{-1/2}\log n=O(n^{-1/2}).
\]
Then
\[
n^{-1/2}=o(n^{-1/2}\log n)
\]
because \(1/\log n\to0\).

Use `tendsto_log_atTop`, reciprocal convergence, and your preferred quotient characterization of `IsLittleO`/`IsEquivalent`. `isLittleO_of_tendsto'` is suitable after establishing eventual nonvanishing.

**Recommendation:** retain `1 / Real.sqrt n` until this last lemma. Convert to `n ^ (-(1 / 2 : ℝ))` only once.

---

## 4. Optional exact-expansion add-on

After the leading theorem, the expansion needs three additional components.

1. **Logarithmic-moment integrability**
   \[
   \mathrm{IntegrableOn}\;(s\mapsto f(s)\log s)\;(0,\infty).
   \]
   Split at \(1\):
   - near zero, use \(f\le E\) and integrability of \(|\log s|\);
   - above \(1\), use \(|\log s|=\log s\le s\) and first-moment integrability.

2. **Triangular swap**
   \[
   H(L)=\int_{(0,L]}f(s)\log(L/s)\,ds.
   \]
   Swap the kernel \(f(s)/x\) on \(0<s\le x\le L\). Nonnegativity allows Tonelli first; finiteness follows from E. Alternatively establish absolute integrability and use `MeasureTheory.integral_integral_swap`.

3. **Gaussian remainder bound**
   \[
   0\le R(L)\le(E/β)e^{-βL^2/2}\quad(L\ge1).
   \]
   The Gaussian first-moment tail is an elementary antiderivative calculation.

These are worthwhile if you want the next coefficient, but unnecessary infrastructure for the first `log n` theorem.

---

## 5. Numerical sanity check

Completing the square gives
\[
A=\frac{\sqrt\pi}{2\sqrt β}
e^{βa^2/4}
\left(1+\operatorname{erf}\!\left(\frac{a\sqrt β}{2}\right)\right).
\]
Thus
\[
\boxed{
C=\frac{\sqrt\pi}{4\sqrt β}
e^{βa^2/4}
\left(1+\operatorname{erf}\!\left(\frac{a\sqrt β}{2}\right)\right).
}
\]

For \(β=1.3,\ a=0.4,\ b=1\),
\[
\boxed{C\approx 0.5129.}
\]

```python
import numpy as np
from scipy.special import erf

beta, a = 1.3, 0.4
C = (
    np.sqrt(np.pi) / (4 * np.sqrt(beta))
    * np.exp(beta * a*a / 4)
    * (1 + erf(a * np.sqrt(beta) / 2))
)
print(C)
```

Check that
\[
\frac{\sqrt n\,Z_2(n)}{\log n}\longrightarrow C.
\]
For \(b=1\), the more sensitive next-order check is
\[
\sqrt n\,Z_2(n)-C\log n\longrightarrow-B.
\]
The first ratio generally converges only at rate \(1/\log n\), despite the exponentially small remainder after including the constant term.
