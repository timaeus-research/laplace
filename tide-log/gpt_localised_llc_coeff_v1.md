## 1. Correctness of A, B, C and the rate bookkeeping

**The conclusions of A, B, and C are correct for fixed parameters, with eventual bounds \(t\ge T\ge1\). There is one important missing term in A’s cubic expansion.** C also needs the sharper unlocalised remainder you identified—or an equivalent specialisation of A.

### Independent coefficient check

First,
\[
\begin{aligned}
c_2'
&=B_2+ac_3+\frac{3p_3}{\lambda^2}-\frac{d_1}{\lambda}\\
&=\frac{5\alpha^2}{4\lambda^4}-\frac{\gamma}{2\lambda^3}
-\frac{2a\alpha}{\lambda^3}+\frac{a^2-g}{\lambda^2}.
\end{aligned}
\]
Consequently,
\[
\begin{aligned}
\frac{\lambda}{2}c_2'
&=\frac{5\alpha^2}{8\lambda^3}-\frac{\gamma}{4\lambda^2}
-\frac{a\alpha}{\lambda^2}+\frac{a^2-g}{2\lambda},\\
\frac{\alpha}{6}\left(c_3+\frac{3a}{\lambda^2}\right)
&=-\frac{5\alpha^2}{12\lambda^3}+\frac{a\alpha}{2\lambda^2},\\
\frac{\gamma}{24}\frac{3}{\lambda^2}
&=\frac{\gamma}{8\lambda^2}.
\end{aligned}
\]
Adding gives exactly
\[
\boxed{
e_1=\frac{a^2-g}{2\lambda}
-\frac{a\alpha}{2\lambda^2}
-\frac{\gamma}{8\lambda^2}
+\frac{5\alpha^2}{24\lambda^3}.
}
\]

There is also a useful conceptual check:
\[
\boxed{e_1=e_0+d_1.}
\]
The localiser changes the partition function’s first correction by \(d_1\), and the energy is its negative logarithmic \(t\)-derivative. This checks the coefficient independently, but **does not itself prove the remainder**: differentiating an \(O(t^{-2})\) remainder without derivative control is invalid.

### Correction to the cubic expansion

Writing \(b=g/2\), \(y=ax-bx^2\), the displayed equality in A.2 should be
\[
x^3\phi
=x^3+ax^4-\boxed{bx^5}+\frac{x^3y^2}{2}+x^3R_3.
\]
Equivalently,
\[
x^3\phi
=x^3+ax^4+p_3x^5-abx^6+\frac{b^2}{2}x^7+x^3R_3.
\]
The omitted term is harmless for the claimed rate, because it is a **signed** fifth moment of order \(t^{-3}\), but it must appear in the pointwise identity.

### Are the moment inputs sufficient?

Yes. The crucial consequences, for \(t\ge1\), are
\[
|\langle x^5\rangle|\le C t^{-3},
\qquad
\langle x^{2k}\rangle\le C_k t^{-k}.
\]
The first follows immediately from `fifthMoment_lead`; its explicit coefficient \(c_5\) is not needed here.

The bookkeeping is:

| Expansion | Required unscaled error | Inputs controlling it |
|---|---:|---|
| \( \langle x^2\phi\rangle \) through \(t^{-2}\) | \(O(t^{-3})\) | second-moment sharp rate; third/fourth leading rates; signed fifth moment; even moments \(6,8,10\) |
| \( \langle x^3\phi\rangle \) through \(t^{-2}\) | \(O(t^{-3})\) | third/fourth leading rates; signed fifth moment; indicated even-moment envelopes |
| \( \langle x^4\phi\rangle \) through \(t^{-2}\) | \(O(t^{-3})\) | fourth leading rate; signed fifth moment; even moments \(6,8\) |

In particular:

- Replacing the signed fifth moment by an absolute fifth moment generally gives only \(O(t^{-5/2})\), which is insufficient. Retaining its sign is essential.
- The inequality
  \[
  |x|^7\le \frac{x^6+x^8}{2}
  \]
  gives \(O(t^{-3})\), exactly what these proofs need. It loses sharpness compared with the natural absolute seventh-moment scale, but **loses nothing relevant to the target rates**.
- Similarly, \(|x|^9\le(x^8+x^{10})/2\) gives more than enough decay for the cubic remainder.

For division, explicitly retain or prove \(D\ge1/2\) eventually. The denominator expansion supplies this; \(D=1+O(t^{-1})\) alone suffices for the cubic and quartic ratios, while the second-moment correction uses the sharper expansion and `ratio_key`.

A bounded-above exponent is available because \(a=gx_0\): for \(g>0\), \(y\le a^2/(2g)\); for \(g=0\), necessarily \(a=0\). An auxiliary theorem allowing arbitrary \(a\) with \(g=0\) would not have this global upper bound.

### B and C

**B follows** from finite summation and the exact scalar trace remainder
\[
\frac12\frac{t\lambda}{t\lambda+g}
-\frac12+\frac{g}{2\lambda t}
=\frac{g^2}{2\lambda t(t\lambda+g)}.
\]
This directly supplies the \(O(t^{-2})\) trace error.

**C follows after sharpening the unlocalised energy remainder.** Your proposed three-moment assembly suffices. Alternatively, specialise A to \(g=0\), hence \(a=0\), and simplify the localised expectation to the unlocalised one. That can avoid duplicating the analytic proof.

## 2. Strongest reachable bundle and a cleaner proof route

**I would target A+B+C.** The analytic risk is concentrated in A; B and C are comparatively cheap once A exists. The 700–800-line estimate is plausible with the stated infrastructure, though the actual Lean APIs—not the mathematics—will determine it.

### Recommended simplification: reuse the second-moment pointwise expansion

You do **not** need three independent exponential expansions.

Prove A.1’s single pointwise identity and envelope:
\[
x^2\phi=x^2+ax^3+p_3x^4+p_4x^5+R,
\qquad
|R|\le E_6x^6+E_8x^8+E_{10}x^{10}.
\]

Then multiply it by \(x\):
\[
x^3\phi=x^3+ax^4+p_3x^5+p_4x^6+xR.
\]
Use
\[
|xR|
\le \frac{E_6}{2}(x^6+x^8)
+\frac{E_8}{2}(x^8+x^{10})
+\frac{E_{10}}2(x^{10}+x^{12}).
\]
Every resulting remainder term has expectation \(O(t^{-3})\) or better.

Likewise, multiply by \(x^2\):
\[
x^4\phi=x^4+ax^5+p_3x^6+p_4x^7+x^2R,
\]
where
\[
|x^2R|\le E_6x^8+E_8x^{10}+E_{10}x^{12}.
\]
The fifth moment stays signed, and the seventh moment is bounded by \((x^6+x^8)/2\).

**Trade-off:** this uses even moments through degree \(12\), rather than \(10\), but `evenMoment_bound k` already provides them. In exchange, there is only **one substantial exponential-remainder proof**, plus polynomial multiplication and routine envelopes. This is the cleanest route suggested by the listed seabed.

### Stein/IBP alternative

For the localised measure, integration by parts gives
\[
1=t\lambda\langle x^2\rangle_{\rm loc}
+\frac{t\alpha}{2}\langle x^3\rangle_{\rm loc}
+\frac{t\gamma}{6}\langle x^4\rangle_{\rm loc}
+g\langle x^2\rangle_{\rm loc}
-a\langle x\rangle_{\rm loc}.
\]
Thus
\[
t\langle\ell\rangle_{\rm loc}
=\frac12+\frac a2\langle x\rangle_{\rm loc}
-\frac g2\langle x^2\rangle_{\rm loc}
-\frac{\alpha}{12}t\langle x^3\rangle_{\rm loc}
-\frac{\gamma}{24}t\langle x^4\rangle_{\rm loc}.
\]

This avoids the sharp localised second-moment expansion, using instead
\[
\langle x\rangle_{\rm loc}
=\left(\frac a\lambda-\frac{\alpha}{2\lambda^2}\right)t^{-1}
+O(t^{-2})
\]
and the leading second moment. But it still needs the sharp cubic and quartic estimates.

**Use this only if a suitable IBP theorem is already available.** Building the boundary-decay and integration machinery solely for this tide is probably less predictable than the single-envelope route.

Mean and variance alone do not determine quartic energy; an additional identity or higher-moment control remains necessary.

## 3. Wording against E3

Your proposed reading is fair **as a statement about the fixed-localiser \(1/t\) coefficient**. I would phrase it as:

> For fixed localisation strength and anchor, the trace expression reproduces the universal covariance-shrinkage contribution \(-g/(2\lambda)\) to the first energy correction. The residual coefficient consists of the unlocalised anharmonic correction and the anchor-dependent correction \(a^2/(2\lambda)-a\alpha/(2\lambda^2)\).

Three qualifications matter.

1. **The trace is not the whole Gaussian anchored energy.**  
   For a purely quadratic loss, the exact answer is
   \[
   t\langle\ell\rangle_{\rm Gaussian,loc}
   =\frac12\frac{t\lambda}{t\lambda+g}
   +\frac{t\lambda a^2}{2(t\lambda+g)^2}.
   \]
   The second term is the squared-mean contribution. Thus \(a^2/(2\lambda)\) is already present in the full anchored Gaussian approximation; it is not an anharmonic discrepancy.

2. **The anchor-dependent correction need not be positive.**
   \[
   \frac{a^2}{2\lambda}-\frac{a\alpha}{2\lambda^2}
   =\frac{a}{2\lambda}\left(a-\frac{\alpha}{\lambda}\right)
   \]
   can have either sign. Only its purely Gaussian part is nonnegative.

3. **The expansion is not asserted uniformly in \(g,x_0\), or the oscillator parameters.**  
   In particular, \(g\) growing with \(t\) is a different regime.

At the minimum anchor, the clean statement is
\[
t\langle\ell\rangle_{\rm loc}
-\frac12\frac{t\lambda}{t\lambda+g}
=\frac{e_0}{t}+O(t^{-2}).
\]
This residual is not necessarily positive: \(e_0=(5\alpha^2-3\lambda\gamma)/(24\lambda^3)\) can have either sign under the stated assumptions.

## 4. Recommended scope

Package the tide around:

1. one reusable \(x^2\phi\) expansion and envelope;
2. sharp localised second, third, and fourth moment rates;
3. A and its coefficient identity;
4. B and the trace-residual theorem;
5. C, with the sharp unlocalised bound obtained by specialisation or short assembly.

**Vote: A+B+C, using one shared pointwise expansion and correcting the missing \(-\tfrac g2x^5\) term in the cubic route.**